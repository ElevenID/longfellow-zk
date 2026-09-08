// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use core_algebra::ElementOf;
use runtime_algebra::{poly::InterpolationField, SupportsSampling};
use runtime_random::Transcript;
use zeroize::{Zeroize, Zeroizing};

use crate::{
    hquad::HQuad,
    poly::Poly,
    proof::{LayerProof, SumcheckProof, MAX_LOGW},
    transcript::TranscriptSumcheck,
    IntoWitnessLayers, SumcheckProofAux, ZeroizingVec,
};

struct Bindings<const W: usize, F: InterpolationField<W>> {
    logv: usize,
    nv: usize,
    challenges: [Vec<ElementOf<F>>; 2],
}

struct SecretPoly<const N: usize, const W: usize, F>
where
    F: InterpolationField<W>,
    ElementOf<F>: Zeroize,
{
    value: Poly<N, W, F>,
}

impl<const N: usize, const W: usize, F> SecretPoly<N, W, F>
where
    F: InterpolationField<W>,
    ElementOf<F>: Zeroize,
{
    fn new(value: Poly<N, W, F>) -> Self {
        Self { value }
    }
}

impl<const N: usize, const W: usize, F> std::ops::Deref for SecretPoly<N, W, F>
where
    F: InterpolationField<W>,
    ElementOf<F>: Zeroize,
{
    type Target = Poly<N, W, F>;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<const N: usize, const W: usize, F> std::ops::DerefMut for SecretPoly<N, W, F>
where
    F: InterpolationField<W>,
    ElementOf<F>: Zeroize,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

impl<const N: usize, const W: usize, F> Drop for SecretPoly<N, W, F>
where
    F: InterpolationField<W>,
    ElementOf<F>: Zeroize,
{
    fn drop(&mut self) {
        self.value.evaluations.zeroize();
    }
}

pub fn prove<const W: usize, F: InterpolationField<W> + SupportsSampling<W>>(
    in_layers: impl IntoWitnessLayers<ElementOf<F>>,
    pad: &SumcheckProof<W, F>,
    circuit: &core_proto::circuit::Circuit<F>,
    transcript: &mut Transcript,
    f: &F,
) -> (SumcheckProof<W, F>, SumcheckProofAux<W, F>)
where
    ElementOf<F>: Zeroize,
{
    prove_guarded(in_layers.into_witness_layers(), pad, circuit, transcript, f)
}

pub fn prove_guarded<const W: usize, F>(
    in_layers: Zeroizing<Vec<Vec<ElementOf<F>>>>,
    pad: &SumcheckProof<W, F>,
    circuit: &core_proto::circuit::Circuit<F>,
    transcript: &mut Transcript,
    f: &F,
) -> (SumcheckProof<W, F>, SumcheckProofAux<W, F>)
where
    F: InterpolationField<W> + SupportsSampling<W>,
    ElementOf<F>: Zeroize,
{
    assert!(
        circuit.raw.ninput >= circuit.raw.npublic_input,
        "npublic_input ({}) exceeds ninput ({})",
        circuit.raw.npublic_input,
        circuit.raw.ninput
    );

    let inputs = &in_layers[circuit.raw.layers.len() - 1];
    assert!(
        inputs.len() >= circuit.raw.npublic_input,
        "input vector too short: expected at least npublic_input ({}) entries, got {}",
        circuit.raw.npublic_input,
        inputs.len()
    );
    let public_inputs = &inputs[..circuit.raw.npublic_input];
    transcript.write_sumcheck_statement(circuit, public_inputs, f);
    prove_core_guarded(in_layers, pad, circuit, transcript, f)
}

pub fn prove_core<const W: usize, F: InterpolationField<W> + SupportsSampling<W>>(
    in_layers: impl IntoWitnessLayers<ElementOf<F>>,
    pad: &SumcheckProof<W, F>,
    circuit: &core_proto::circuit::Circuit<F>,
    transcript: &mut Transcript,
    f: &F,
) -> (SumcheckProof<W, F>, SumcheckProofAux<W, F>)
where
    ElementOf<F>: Zeroize,
{
    prove_core_guarded(in_layers.into_witness_layers(), pad, circuit, transcript, f)
}

pub fn prove_core_guarded<const W: usize, F>(
    mut in_layers: Zeroizing<Vec<Vec<ElementOf<F>>>>,
    pad: &SumcheckProof<W, F>,
    circuit: &core_proto::circuit::Circuit<F>,
    transcript: &mut Transcript,
    f: &F,
) -> (SumcheckProof<W, F>, SumcheckProofAux<W, F>)
where
    F: InterpolationField<W> + SupportsSampling<W>,
    ElementOf<F>: Zeroize,
{
    // The wire array is conceptually infinite (padded with zeros), but we normalize
    // each layer's wire vector to contain at least one 0 to simplify the implementation
    // and avoid handling the empty vec case in downstream binding functions.
    for wires in in_layers.iter_mut() {
        if wires.is_empty() {
            wires.push(f.zero());
        }
    }
    let (_copy_challenges, challenges_0) = transcript.begin_circuit(f);
    let mut bindings = Bindings {
        logv: circuit.raw.logv,
        nv: circuit.raw.noutput,
        challenges: [
            challenges_0[..circuit.raw.logv].to_vec(),
            challenges_0[..circuit.raw.logv].to_vec(),
        ],
    };

    let num_layers = circuit.raw.layers.len();
    assert!(in_layers.len() >= num_layers && pad.layers.len() >= num_layers);
    let layers_slice = &circuit.raw.layers[..num_layers];
    let in_layers_slice = &mut in_layers[..num_layers];
    let pad_layers_slice = &pad.layers[..num_layers];

    let mut claims = Zeroizing::new([f.zero(), f.zero()]);
    let mut layers = Vec::with_capacity(num_layers);
    let mut bound_quad = ZeroizingVec::new(Vec::with_capacity(num_layers));

    for i in 0..num_layers {
        let clr = &layers_slice[i];
        let (alpha, beta) = transcript.begin_layer(f);
        let wires = Zeroizing::new(std::mem::take(&mut in_layers_slice[i]));
        let hquad = HQuad::bind_g(
            clr,
            &circuit.raw.constants,
            bindings.logv,
            bindings.nv,
            &bindings.challenges[0],
            &bindings.challenges[1],
            &alpha,
            &beta,
            f,
        );
        let (layer_proof, new_bindings, new_claims, hquad_scalar) = layer_guarded(
            clr.logw(),
            clr.nw(),
            wires,
            &pad_layers_slice[i],
            transcript,
            hquad,
            &alpha,
            claims,
            f,
        );
        bindings = new_bindings;
        claims = new_claims;

        bound_quad.push(hquad_scalar);
        layers.push(layer_proof);
    }

    (SumcheckProof { layers }, SumcheckProofAux { bound_quad })
}

#[allow(clippy::too_many_arguments)]
fn layer_guarded<const W: usize, F>(
    logw: usize,
    nw: usize,
    wires: Zeroizing<Vec<ElementOf<F>>>,
    pad: &LayerProof<W, F>,
    transcript: &mut Transcript,
    mut hquad: HQuad<W, F>,
    alpha: &ElementOf<F>,
    claims: Zeroizing<[ElementOf<F>; 2]>,
    f: &F,
) -> (
    LayerProof<W, F>,
    Bindings<W, F>,
    Zeroizing<[ElementOf<F>; 2]>,
    ElementOf<F>,
)
where
    F: InterpolationField<W> + SupportsSampling<W>,
    ElementOf<F>: Zeroize,
{
    assert!(crate::sane_logw(logw), "logw must be sane");
    assert!(
        wires.len() as u64 <= (1u64 << logw),
        "size of wires {} exceeds 2^logw {}",
        wires.len(),
        1u64 << logw
    );
    let mut challenges = [Vec::with_capacity(logw), Vec::with_capacity(logw)];
    let mut round_polys = [Vec::with_capacity(logw), Vec::with_capacity(logw)];
    let mut sum = Zeroizing::new(claims[0].clone());
    let mut alpha_claim = Zeroizing::new(alpha.clone());
    f.mul(&mut alpha_claim, &claims[1]);
    f.add(&mut sum, &alpha_claim);

    // Wrap the initial wire vector in an Rc to avoid cloning the massive input slice.
    // At round 0, both right hand (w[0]) and left hand (w[1]) point to the same shared buffer.
    let wires_rc = std::rc::Rc::new(wires);
    let mut w = [wires_rc.clone(), wires_rc];
    let mut qw = Zeroizing::new(vec![f.zero(); w[0].len()]);

    for round in 0..logw {
        for hand in 0..2 {
            let other_hand = 1 - hand;
            let wh_hand = &w[hand];
            let wh_other_hand = &w[other_hand];

            let wh_size = wh_hand.len();
            runtime_algebra::blas::clear(&mut qw[..wh_size], f);

            if hand == 0 {
                for i in 0..hquad.hc.len() {
                    let p0 = hquad.hc[i].h[0] as usize;
                    let p1 = hquad.hc[i].h[1] as usize;
                    let dst = &mut qw[p0];
                    let witness_other_hand_val = &wh_other_hand[p1];
                    f.fma(dst, &hquad.vc[i], witness_other_hand_val);
                }
            } else {
                for i in 0..hquad.hc.len() {
                    let p0 = hquad.hc[i].h[1] as usize;
                    let p1 = hquad.hc[i].h[0] as usize;
                    let dst = &mut qw[p0];
                    let witness_other_hand_val = &wh_other_hand[p1];
                    f.fma(dst, &hquad.vc[i], witness_other_hand_val);
                }
            }

            let evaluations = quad_round_poly(wh_size, &qw[..wh_size], wh_hand, &*sum, f);

            assert!(round < MAX_LOGW);
            let round_challenge = sample_round_challenge(
                transcript,
                &evaluations,
                &pad.hp[hand][round],
                &mut round_polys[hand],
                &mut challenges[hand],
                f,
            );
            let next_sum = eval_lagrange_zeroizing(&evaluations, &round_challenge, f);
            sum.zeroize();
            *sum = next_sum;

            // In-place vs out-of-place binding optimization:
            // When w[hand] has strong count 1 (sole owner), get_mut returns Some(v) and we bind
            // in-place, reusing the allocated buffer without heap allocations.
            // In round 0 for hand=0, w[0] and w[1] share the Rc (strong count 2), so get_mut
            // returns None. We bind out-of-place to allocate a new halved buffer for
            // w[0], leaving w[1] as the sole owner of the original buffer. All
            // subsequent halvings across both hands then happen in-place!
            if let Some(v) = std::rc::Rc::get_mut(&mut w[hand]) {
                crate::dense::bind_zeroizing(v, &round_challenge, f);
            } else {
                let bound_v =
                    crate::dense::bind_out_of_place_zeroizing(&w[hand], &round_challenge, f);
                w[hand] = std::rc::Rc::new(bound_v);
            }
            hquad.bind_h(&round_challenge, hand, f);
        }
    }

    let next_claim_0 = Zeroizing::new(crate::dense::as_scalar::<W, F>(&w[0]));
    let next_claim_1 = Zeroizing::new(crate::dense::as_scalar::<W, F>(&w[1]));
    let next_claims = Zeroizing::new([(*next_claim_0).clone(), (*next_claim_1).clone()]);

    let hquad_scalar = hquad.scalar();
    let mut expected_sum = Zeroizing::new(next_claims[0].clone());
    f.mul(&mut expected_sum, &next_claims[1]);
    f.mul(&mut expected_sum, &hquad_scalar);
    assert_eq!(
        sum, expected_sum,
        "reconstructed sum does not match expected"
    );

    let mut proof_claims = Zeroizing::new([next_claims[0].clone(), next_claims[1].clone()]);
    f.sub(&mut proof_claims[0], &pad.claims[0]);
    f.sub(&mut proof_claims[1], &pad.claims[1]);
    transcript.end_layer(&proof_claims, f);
    let public_proof_claims = [proof_claims[0].clone(), proof_claims[1].clone()];

    let bindings = Bindings {
        logv: logw,
        nv: nw,
        challenges,
    };

    (
        LayerProof {
            hp: round_polys,
            claims: public_proof_claims, // padded and public
        },
        bindings,
        next_claims,
        hquad_scalar,
    )
}

/// Absorbs the unpadded round polynomial into the transcript after applying ZK padding,
/// samples the round challenge, and records the padded polynomial and challenge.
#[inline]
fn sample_round_challenge<const W: usize, F: InterpolationField<W> + SupportsSampling<W>>(
    transcript: &mut Transcript,
    unpadded_poly: &SecretPoly<3, W, F>,
    pad_poly: &crate::proof::RoundPoly<W, F>,
    round_polys: &mut Vec<crate::proof::RoundPoly<W, F>>,
    challenges: &mut Vec<ElementOf<F>>,
    f: &F,
) -> ElementOf<F>
where
    ElementOf<F>: Zeroize,
{
    let mut unmasked_wire = Zeroizing::new([
        unpadded_poly.evaluations[0].clone(),
        unpadded_poly.evaluations[2].clone(),
    ]);
    f.sub(&mut unmasked_wire[0], &pad_poly.evaluations[0]);
    f.sub(&mut unmasked_wire[1], &pad_poly.evaluations[1]);
    let poly_padded = crate::proof::RoundPoly {
        evaluations: [unmasked_wire[0].clone(), unmasked_wire[1].clone()],
    };
    let round_challenge = transcript.round(&poly_padded, f);
    round_polys.push(poly_padded);
    challenges.push(round_challenge.clone());
    round_challenge
}

/// Evaluates the quad round polynomial of degree 2 (represented
/// by 3 evaluation points) for the current sumcheck prover round.
///
/// Directly computes the evaluations [g(0), g(1), g(2)] without intermediate
/// monomial or Newton conversions.
#[inline]
fn quad_round_poly<const W: usize, F: InterpolationField<W>>(
    num_variables: usize,
    qw: &[ElementOf<F>],
    witness_values: &[ElementOf<F>],
    sum: &ElementOf<F>,
    f: &F,
) -> SecretPoly<3, W, F>
where
    ElementOf<F>: Zeroize,
{
    let num_pairs = num_variables / 2;
    let mut accum_a0 = Zeroizing::new(f.zero_accum());
    let mut accum_a2 = Zeroizing::new(f.zero_accum());

    for i in 0..num_pairs {
        let idx = 2 * i;
        f.mac(&mut accum_a0, &qw[idx], &witness_values[idx]);
        let mut dqw = Zeroizing::new(qw[idx + 1].clone());
        f.sub(&mut dqw, &qw[idx]);
        let mut dw = Zeroizing::new(witness_values[idx + 1].clone());
        f.sub(&mut dw, &witness_values[idx]);
        f.mac(&mut accum_a2, &dqw, &dw);
    }

    if !num_variables.is_multiple_of(2) {
        let last = num_variables - 1;
        f.mac(&mut accum_a0, &qw[last], &witness_values[last]);
        f.mac(&mut accum_a2, &qw[last], &witness_values[last]);
    }

    let a0 = Zeroizing::new(f.accum_reduce(&accum_a0));
    let a2 = Zeroizing::new(f.accum_reduce(&accum_a2));

    // g(0) = a0
    // g(1) = sum - a0
    let mut g1 = Zeroizing::new((*sum).clone());
    f.sub(&mut g1, &a0);

    // c1 = g(1) - a0 - a2 = sum - 2*a0 - a2
    let mut c1 = Zeroizing::new((*g1).clone());
    f.sub(&mut c1, &a0);
    f.sub(&mut c1, &a2);

    // Evaluate g(2) = a2*pt(2)^2 + c1*pt(2) + a0 using Horner's method for binary field
    // compatibility:
    let pt2 = f.poly_evaluation_point(2);
    let mut g2 = Zeroizing::new((*a2).clone());
    f.mul(&mut g2, &pt2);
    f.add(&mut g2, &c1);
    f.mul(&mut g2, &pt2);
    f.add(&mut g2, &a0);

    SecretPoly::new(Poly {
        evaluations: [(*a0).clone(), (*g1).clone(), (*g2).clone()],
    })
}

fn eval_lagrange_zeroizing<const N: usize, const W: usize, F>(
    polynomial: &SecretPoly<N, W, F>,
    x: &ElementOf<F>,
    f: &F,
) -> ElementOf<F>
where
    F: InterpolationField<W>,
    ElementOf<F>: Zeroize,
{
    assert!(N > 0, "polynomial must contain at least one evaluation");
    let mut coefficients = SecretPoly::new(polynomial.value.clone());
    for i in 1..N {
        for k in (i..N).rev() {
            let previous = Zeroizing::new(coefficients.evaluations[k - 1].clone());
            f.sub(&mut coefficients.evaluations[k], &previous);
            let denominator = Zeroizing::new(f.newton_denominator(k, i));
            f.mul(&mut coefficients.evaluations[k], &denominator);
        }
    }

    let mut result = Zeroizing::new(coefficients.evaluations[N - 1].clone());
    for i in (0..(N - 1)).rev() {
        let mut delta = Zeroizing::new(x.clone());
        let evaluation_point = Zeroizing::new(f.poly_evaluation_point(i));
        f.sub(&mut delta, &evaluation_point);
        f.mul(&mut result, &delta);
        f.add(&mut result, &coefficients.evaluations[i]);
    }
    (*result).clone()
}

#[cfg(test)]
mod secure_default_tests {
    use std::{
        panic::{catch_unwind, AssertUnwindSafe},
        sync::{
            atomic::{AtomicUsize, Ordering},
            Arc,
        },
    };

    use core_algebra::AlgebraicField;
    use core_proto::circuit::{Circuit, Layer, RawCircuit, TermDelta};
    use runtime_random::Transcript;

    use super::{prove, prove_core, quad_round_poly};
    use crate::{
        proof::{LayerProof, RoundPoly},
        test_field::{TrackedElement, TrackedField},
        SumcheckProof,
    };

    fn circuit(layers: Vec<Layer<TrackedField>>) -> Circuit<TrackedField> {
        Circuit {
            raw: RawCircuit {
                ninput: 0,
                npublic_input: 0,
                noutput: 0,
                logv: 0,
                subfield_boundary: 0,
                constants: Vec::new(),
                layers,
            },
            id: [0u8; 32],
        }
    }

    fn two_round_circuit(field: &TrackedField) -> Circuit<TrackedField> {
        let layer = Layer::new(
            4,
            2,
            vec![TermDelta {
                g: 0,
                h: [0, 0],
                k_index: 0,
            }],
            vec![vec![0]],
            vec![0],
        );
        let mut circuit = circuit(vec![layer]);
        circuit.raw.ninput = 4;
        circuit.raw.noutput = 1;
        circuit.raw.constants.push(field.one());
        circuit
    }

    fn zero_pad(field: &TrackedField, rounds: usize) -> SumcheckProof<1, TrackedField> {
        let round = || RoundPoly {
            evaluations: [field.zero(), field.zero()],
        };
        SumcheckProof {
            layers: vec![LayerProof {
                hp: [
                    (0..rounds).map(|_| round()).collect(),
                    (0..rounds).map(|_| round()).collect(),
                ],
                claims: [field.zero(), field.zero()],
            }],
        }
    }

    #[test]
    fn ordinary_prover_wipes_layers_on_success_and_unwind() {
        let field = TrackedField;
        let empty_circuit = circuit(Vec::new());
        let empty_pad: SumcheckProof<1, TrackedField> = SumcheckProof { layers: Vec::new() };

        let success_wipes = Arc::new(AtomicUsize::new(0));
        let success = prove_core::<1, _>(
            vec![vec![TrackedElement::secret(1, &success_wipes)]],
            &empty_pad,
            &empty_circuit,
            &mut Transcript::new(b"sumcheck-cleanup-success"),
            &field,
        );
        assert!(success.0.layers.is_empty());
        assert_eq!(success_wipes.load(Ordering::SeqCst), 1);

        let prove_unwind_wipes = Arc::new(AtomicUsize::new(0));
        let prove_unwind = catch_unwind(AssertUnwindSafe(|| {
            let _ = prove::<1, _>(
                vec![vec![TrackedElement::secret(1, &prove_unwind_wipes)]],
                &empty_pad,
                &empty_circuit,
                &mut Transcript::new(b"sumcheck-cleanup-prove-unwind"),
                &field,
            );
        }));
        assert!(prove_unwind.is_err());
        assert_eq!(prove_unwind_wipes.load(Ordering::SeqCst), 1);

        let invalid_circuit = circuit(vec![Layer::new(1, 0, Vec::new(), Vec::new(), Vec::new())]);
        let core_unwind_wipes = Arc::new(AtomicUsize::new(0));
        let core_unwind = catch_unwind(AssertUnwindSafe(|| {
            let _ = prove_core::<1, _>(
                vec![vec![TrackedElement::secret(1, &core_unwind_wipes)]],
                &empty_pad,
                &invalid_circuit,
                &mut Transcript::new(b"sumcheck-cleanup-core-unwind"),
                &field,
            );
        }));
        assert!(core_unwind.is_err());
        assert_eq!(core_unwind_wipes.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn unmasked_round_polynomial_wipes_derived_evaluations_on_drop() {
        let field = TrackedField;
        let inputs = Arc::new(AtomicUsize::new(0));
        let derived = Arc::new(AtomicUsize::new(0));
        let qw = vec![
            TrackedElement::secret_with_derived_wipes(1, &inputs, &derived),
            TrackedElement::secret_with_derived_wipes(0, &inputs, &derived),
        ];
        let witness = vec![
            TrackedElement::secret_with_derived_wipes(1, &inputs, &derived),
            TrackedElement::secret_with_derived_wipes(0, &inputs, &derived),
        ];
        let sum = TrackedElement::secret_with_derived_wipes(1, &inputs, &derived);

        let polynomial = quad_round_poly::<1, _>(2, &qw, &witness, &sum, &field);
        let before_drop = derived.load(Ordering::SeqCst);
        drop(polynomial);
        assert_eq!(
            derived.load(Ordering::SeqCst) - before_drop,
            3,
            "all three unmasked evaluations must be wiped by their guard"
        );
    }

    #[test]
    fn multi_round_prover_wipes_derived_state_on_success_and_unwind() {
        let field = TrackedField;
        let circuit = two_round_circuit(&field);

        let success_inputs = Arc::new(AtomicUsize::new(0));
        let success_derived = Arc::new(AtomicUsize::new(0));
        let success_witness = vec![(0..4)
            .map(|_| {
                TrackedElement::secret_with_derived_wipes(0, &success_inputs, &success_derived)
            })
            .collect()];
        let success = prove_core::<1, _>(
            success_witness,
            &zero_pad(&field, 2),
            &circuit,
            &mut Transcript::new(b"sumcheck-derived-success"),
            &field,
        );
        assert_eq!(success.0.layers.len(), 1);
        assert_eq!(success_inputs.load(Ordering::SeqCst), 4);
        assert!(
            success_derived.load(Ordering::SeqCst) > 0,
            "multi-round success must wipe witness-derived scratch values"
        );

        let unwind_inputs = Arc::new(AtomicUsize::new(0));
        let unwind_derived = Arc::new(AtomicUsize::new(0));
        let unwind_witness = vec![(0..4)
            .map(|_| TrackedElement::secret_with_derived_wipes(0, &unwind_inputs, &unwind_derived))
            .collect()];
        let unwind = catch_unwind(AssertUnwindSafe(|| {
            let _ = prove_core::<1, _>(
                unwind_witness,
                &zero_pad(&field, 1),
                &circuit,
                &mut Transcript::new(b"sumcheck-derived-unwind"),
                &field,
            );
        }));
        assert!(unwind.is_err());
        assert_eq!(unwind_inputs.load(Ordering::SeqCst), 4);
        assert!(
            unwind_derived.load(Ordering::SeqCst) > 0,
            "multi-round unwind must wipe witness-derived scratch values"
        );
    }
}
