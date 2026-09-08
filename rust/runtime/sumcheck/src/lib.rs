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

pub mod dense;
pub mod eq;
#[cfg(feature = "prover")]
pub mod eval;
pub mod hquad;
#[cfg(feature = "prover")]
pub mod pad;
pub mod poly;
pub use runtime_proto::sumcheck as proof;
#[cfg(feature = "prover")]
pub mod prover;
pub mod transcript;
pub mod verifier;

#[cfg(feature = "prover")]
pub use dense::{as_scalar, bind, bind_all, normalize};
pub use eq::eval as eq;
pub use hquad::HQuad;
pub use poly::{LagrangeBasis, Poly, QuadRoundPoly, QuadWirePoly};
pub use proof::{sane_logw, LayerProof, RoundPoly, SumcheckProof, MAX_LOGW};
#[cfg(feature = "prover")]
pub use prover::{prove, prove_core, prove_core_guarded, prove_guarded};
pub use runtime_random::{RandomEngine, Transcript};
pub use transcript::TranscriptSumcheck;
pub use verifier::{verify, Claims};

#[cfg(feature = "prover")]
pub use crate::eval::{
    eval_circuit, eval_circuit_guarded, eval_quad, eval_quad_guarded, WitnessLayers,
};

use core_algebra::ElementOf;
use runtime_algebra::poly::InterpolationField;
use zeroize::Zeroize;

#[cfg(feature = "prover")]
pub trait IntoWitnessLayers<E: Zeroize> {
    fn into_witness_layers(self) -> WitnessLayers<E>;
}

#[cfg(feature = "prover")]
impl<E: Zeroize> IntoWitnessLayers<E> for Vec<Vec<E>> {
    fn into_witness_layers(self) -> WitnessLayers<E> {
        zeroize::Zeroizing::new(self)
    }
}

#[cfg(feature = "prover")]
impl<E: Zeroize> IntoWitnessLayers<E> for WitnessLayers<E> {
    fn into_witness_layers(self) -> WitnessLayers<E> {
        self
    }
}

/// A vector that wipes every element before releasing its allocation.
pub struct ZeroizingVec<T> {
    values: Vec<T>,
    wipe: fn(&mut [T]),
}

impl<T: Zeroize> ZeroizingVec<T> {
    pub fn new(values: Vec<T>) -> Self {
        fn wipe<T: Zeroize>(values: &mut [T]) {
            for value in values {
                value.zeroize();
            }
        }

        Self {
            values,
            wipe: wipe::<T>,
        }
    }
}

impl<T> std::ops::Deref for ZeroizingVec<T> {
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

impl<T> std::ops::DerefMut for ZeroizingVec<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.values
    }
}

impl<T> Zeroize for ZeroizingVec<T> {
    fn zeroize(&mut self) {
        (self.wipe)(&mut self.values);
    }
}

impl<T> Drop for ZeroizingVec<T> {
    fn drop(&mut self) {
        self.zeroize();
    }
}

/// Auxiliary sumcheck values consumed by symbolic verification.
pub struct SumcheckProofAux<const W: usize, F: InterpolationField<W>> {
    pub bound_quad: ZeroizingVec<ElementOf<F>>,
}

impl<const W: usize, F: InterpolationField<W>> SumcheckProofAux<W, F>
where
    ElementOf<F>: Zeroize,
{
    pub fn new(num_layers: usize, f: &F) -> Self {
        Self {
            bound_quad: ZeroizingVec::new(vec![f.zero(); num_layers]),
        }
    }
}

impl<const W: usize, F: InterpolationField<W>> Zeroize for SumcheckProofAux<W, F>
where
    ElementOf<F>: Zeroize,
{
    fn zeroize(&mut self) {
        self.bound_quad.zeroize();
    }
}

#[cfg(all(test, feature = "prover"))]
pub(crate) mod test_field {
    use std::{
        hash::{Hash, Hasher},
        sync::{
            atomic::{AtomicUsize, Ordering},
            Arc,
        },
    };

    use core_algebra::{AlgebraicField, BareField, SerializableField};
    use runtime_algebra::{poly::InterpolationField, RuntimeField, SupportsSampling};
    use zeroize::Zeroize;

    #[derive(Debug)]
    pub(crate) struct TrackedElement {
        value: u8,
        wipes: Option<Arc<AtomicUsize>>,
        clone_wipes: Option<Arc<AtomicUsize>>,
    }

    impl TrackedElement {
        pub(crate) fn secret(value: u8, wipes: &Arc<AtomicUsize>) -> Self {
            Self {
                value: value & 1,
                wipes: Some(Arc::clone(wipes)),
                clone_wipes: None,
            }
        }

        pub(crate) fn secret_with_derived_wipes(
            value: u8,
            input_wipes: &Arc<AtomicUsize>,
            derived_wipes: &Arc<AtomicUsize>,
        ) -> Self {
            Self {
                value: value & 1,
                wipes: Some(Arc::clone(input_wipes)),
                clone_wipes: Some(Arc::clone(derived_wipes)),
            }
        }

        fn plain(value: u8) -> Self {
            Self {
                value: value & 1,
                wipes: None,
                clone_wipes: None,
            }
        }

        fn derived(value: u8, wipes: Option<Arc<AtomicUsize>>) -> Self {
            Self {
                value: value & 1,
                wipes: wipes.clone(),
                clone_wipes: wipes,
            }
        }

        fn lineage(&self) -> Option<&Arc<AtomicUsize>> {
            self.clone_wipes.as_ref().or(self.wipes.as_ref())
        }

        fn inherit_lineage(&mut self, other: &Self) {
            let Some(wipes) = other.lineage() else {
                return;
            };
            if self.wipes.is_none() {
                self.wipes = Some(Arc::clone(wipes));
            }
            if self.clone_wipes.is_none() {
                self.clone_wipes = Some(Arc::clone(wipes));
            }
        }
    }

    impl Clone for TrackedElement {
        fn clone(&self) -> Self {
            Self::derived(self.value, self.clone_wipes.clone())
        }
    }

    impl PartialEq for TrackedElement {
        fn eq(&self, other: &Self) -> bool {
            self.value == other.value
        }
    }

    impl Eq for TrackedElement {}

    impl Hash for TrackedElement {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.value.hash(state);
        }
    }

    impl Zeroize for TrackedElement {
        fn zeroize(&mut self) {
            self.value = 0;
            if let Some(wipes) = self.wipes.take() {
                wipes.fetch_add(1, Ordering::SeqCst);
            }
            self.clone_wipes = None;
        }
    }

    #[derive(Debug)]
    pub(crate) struct TrackedField;

    impl BareField for TrackedField {
        type E = TrackedElement;
    }

    impl AlgebraicField for TrackedField {
        fn zero(&self) -> Self::E {
            TrackedElement::plain(0)
        }

        fn one(&self) -> Self::E {
            TrackedElement::plain(1)
        }

        fn add(&self, a: &mut Self::E, b: &Self::E) {
            a.inherit_lineage(b);
            a.value ^= b.value;
        }

        fn sub(&self, a: &mut Self::E, b: &Self::E) {
            a.inherit_lineage(b);
            a.value ^= b.value;
        }

        fn mul(&self, a: &mut Self::E, b: &Self::E) {
            a.inherit_lineage(b);
            a.value &= b.value;
        }

        fn invert(&self, a: &Self::E) -> Self::E {
            assert_eq!(a.value, 1, "zero has no inverse");
            let mut inverse = self.one();
            inverse.inherit_lineage(a);
            inverse
        }
    }

    impl SerializableField for TrackedField {
        fn is_binary(&self) -> bool {
            true
        }

        fn serialized_size_bytes(&self) -> usize {
            1
        }

        fn to_bytes_into(&self, element: &Self::E, destination: &mut [u8]) {
            destination[0] = element.value;
        }

        fn bytes_to_element(&self, bytes: &[u8]) -> Result<Self::E, String> {
            match bytes {
                [value] if *value <= 1 => Ok(TrackedElement::plain(*value)),
                _ => Err("tracked test field expects one canonical bit".to_owned()),
            }
        }

        fn serialized_mone(&self) -> Vec<u8> {
            vec![1]
        }
    }

    impl RuntimeField<1> for TrackedField {
        type Accum = TrackedAccum;

        fn zero_accum(&self) -> Self::Accum {
            TrackedAccum {
                value: 0,
                wipes: None,
            }
        }

        fn mac(&self, accumulator: &mut Self::Accum, x: &Self::E, y: &Self::E) {
            accumulator.value ^= x.value & y.value;
            if accumulator.wipes.is_none() {
                accumulator.wipes = x.lineage().or_else(|| y.lineage()).map(Arc::clone);
            }
        }

        fn accum_reduce(&self, accumulator: &Self::Accum) -> Self::E {
            TrackedElement::derived(accumulator.value, accumulator.wipes.clone())
        }
    }

    #[derive(Clone, Debug)]
    pub(crate) struct TrackedAccum {
        value: u8,
        wipes: Option<Arc<AtomicUsize>>,
    }

    impl Zeroize for TrackedAccum {
        fn zeroize(&mut self) {
            self.value = 0;
            if let Some(wipes) = self.wipes.take() {
                wipes.fetch_add(1, Ordering::SeqCst);
            }
        }
    }

    impl SupportsSampling<1> for TrackedField {
        fn sample<R: FnMut(usize) -> Vec<u8>>(&self, mut rng: R) -> Self::E {
            TrackedElement::plain(rng(1).first().copied().unwrap_or_default())
        }
    }

    impl InterpolationField<1> for TrackedField {
        fn poly_evaluation_point(&self, i: usize) -> Self::E {
            TrackedElement::plain(i as u8)
        }

        fn newton_denominator(&self, _k: usize, _i: usize) -> Self::E {
            self.one()
        }
    }
}

#[cfg(all(test, feature = "prover"))]
mod api_compatibility_tests {
    use core_algebra::{ElementOf, SerializableField};
    use runtime_algebra::{poly::InterpolationField, RuntimeField, SupportsSampling};
    use runtime_random::Transcript;
    use zeroize::Zeroize;

    #[allow(dead_code)]
    fn legacy_eval_wrapper<const W: usize, F>(
        witness: Vec<F::E>,
        circuit: &core_proto::circuit::Circuit<F>,
        field: &F,
    ) where
        F: RuntimeField<W> + SerializableField,
        F::E: Zeroize,
    {
        let _ = crate::eval_circuit(witness, circuit, field);
    }

    #[allow(dead_code)]
    fn legacy_prove_wrapper<const W: usize, F>(
        layers: Vec<Vec<ElementOf<F>>>,
        pad: &crate::SumcheckProof<W, F>,
        circuit: &core_proto::circuit::Circuit<F>,
        transcript: &mut Transcript,
        field: &F,
    ) where
        F: InterpolationField<W> + SupportsSampling<W>,
        ElementOf<F>: Zeroize,
    {
        let _ = crate::prove(layers.clone(), pad, circuit, transcript, field);
        let _ = crate::prove_core(layers, pad, circuit, transcript, field);
        let _ = crate::SumcheckProofAux::new(circuit.raw.layers.len(), field);
    }
}

#[cfg(test)]
mod zeroizing_aux_tests {
    use std::sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    };

    use zeroize::Zeroize;

    use super::ZeroizingVec;

    #[derive(Clone)]
    struct Tracked(Arc<AtomicUsize>);

    impl Zeroize for Tracked {
        fn zeroize(&mut self) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }

    #[test]
    fn auxiliary_vector_wipes_every_value_on_drop() {
        let wiped = Arc::new(AtomicUsize::new(0));
        {
            let _values = ZeroizingVec::new(vec![Tracked(Arc::clone(&wiped)); 4]);
        }
        assert_eq!(wiped.load(Ordering::SeqCst), 4);
    }
}
