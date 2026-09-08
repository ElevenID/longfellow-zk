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

use core_algebra::SerializableField;
use runtime_algebra::field::RuntimeField;
use zeroize::{Zeroize, Zeroizing};

pub type WitnessLayers<E> = Zeroizing<Vec<Vec<E>>>;

pub fn eval_circuit<const W: usize, F: RuntimeField<W> + SerializableField>(
    w: Vec<F::E>,
    circuit: &core_proto::circuit::Circuit<F>,
    f: &F,
) -> Result<WitnessLayers<F::E>, String>
where
    F::E: Zeroize,
{
    #[cfg(test)]
    let _cleanup = CleanupObserver(&EVAL_INPUT_CLEANUPS);
    eval_circuit_guarded(Zeroizing::new(w), circuit, f)
}

pub fn eval_circuit_guarded<const W: usize, F>(
    mut w: Zeroizing<Vec<F::E>>,
    circuit: &core_proto::circuit::Circuit<F>,
    f: &F,
) -> Result<WitnessLayers<F::E>, String>
where
    F: RuntimeField<W> + SerializableField,
    F::E: Zeroize,
{
    let nl = circuit.raw.layers.len();
    let mut in_layers = Zeroizing::new(vec![Vec::new(); nl]);

    for l in (0..nl).rev() {
        let nv = if l > 0 {
            circuit.raw.layers[l - 1].nw()
        } else {
            circuit.raw.noutput
        };

        let v = eval_quad_guarded(nv, &w, &circuit.raw.layers[l], &circuit.raw.constants, f)
            .map_err(|e| {
                format!("Witness does not satisfy circuit constraints at layer {l}: {e}")
            })?;

        in_layers[l] = std::mem::take(&mut *w);
        w = v;
    }

    for (i, val) in w.iter().enumerate() {
        if !f.is_zero(val) {
            return Err(format!("Circuit output at index {i} is not zero"));
        }
    }

    Ok(in_layers)
}

pub fn eval_quad<const W: usize, F: RuntimeField<W> + SerializableField>(
    nv: usize,
    w: &[F::E],
    layer: &core_proto::circuit::Layer<F>,
    constants: &[F::E],
    f: &F,
) -> Result<Zeroizing<Vec<F::E>>, String>
where
    F::E: Zeroize,
{
    eval_quad_guarded(nv, w, layer, constants, f)
}

#[cfg(test)]
struct CleanupObserver(&'static std::sync::atomic::AtomicUsize);

#[cfg(test)]
impl Drop for CleanupObserver {
    fn drop(&mut self) {
        self.0.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    }
}

#[cfg(test)]
static EVAL_INPUT_CLEANUPS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

pub fn eval_quad_guarded<const W: usize, F>(
    nv: usize,
    w: &[F::E],
    layer: &core_proto::circuit::Layer<F>,
    constants: &[F::E],
    f: &F,
) -> Result<Zeroizing<Vec<F::E>>, String>
where
    F: RuntimeField<W> + SerializableField,
    F::E: Zeroize,
{
    let mut v = Zeroizing::new(vec![f.zero(); nv]);

    layer.try_for_each_term(
        constants,
        #[inline(always)]
        |term| {
            let g = term.g as usize;
            let r = term.h0 as usize;
            let l = term.h1 as usize;

            let wl = &w[l];
            let wr = &w[r];

            if f.is_zero(&term.k) {
                let mut y = Zeroizing::new(wl.clone());
                f.mul(&mut y, wr);
                if !f.is_zero(&y) {
                    return Err(format!(
                    "gate multiplication constraint not satisfied: left_wire={l}, right_wire={r}"
                ));
                }
            } else {
                let mut x = Zeroizing::new(term.k);
                f.mul(&mut x, wl);
                f.mul(&mut x, wr);
                f.add(&mut v[g], &x);
            }
            Ok(())
        },
    )?;
    Ok(v)
}

#[cfg(test)]
mod secure_default_tests {
    use std::{
        panic::{catch_unwind, AssertUnwindSafe},
        sync::{atomic::Ordering, Mutex},
    };

    use core_proto::circuit::{Circuit, Layer, RawCircuit, TermDelta};
    use runtime_algebra::{gf2_128::Gf2_128Field, AlgebraicField};

    use super::{eval_circuit, eval_quad, EVAL_INPUT_CLEANUPS};

    static TEST_LOCK: Mutex<()> = Mutex::new(());

    fn circuit(
        layers: Vec<Layer<Gf2_128Field>>,
        ninput: usize,
        noutput: usize,
    ) -> Circuit<Gf2_128Field> {
        Circuit {
            raw: RawCircuit {
                ninput,
                npublic_input: 0,
                noutput,
                logv: 0,
                subfield_boundary: 0,
                constants: Vec::new(),
                layers,
            },
            id: [0u8; 32],
        }
    }

    #[test]
    fn ordinary_evaluation_wipes_input_on_success_error_and_unwind() {
        let _lock = TEST_LOCK.lock().expect("test lock poisoned");
        EVAL_INPUT_CLEANUPS.store(0, Ordering::SeqCst);
        let field = Gf2_128Field::new();

        let success = eval_circuit(Vec::new(), &circuit(Vec::new(), 0, 0), &field);
        assert!(success.is_ok());
        assert_eq!(EVAL_INPUT_CLEANUPS.load(Ordering::SeqCst), 1);

        let error = eval_circuit(vec![field.one()], &circuit(Vec::new(), 1, 1), &field)
            .expect_err("nonzero circuit output must fail");
        assert_eq!(error, "Circuit output at index 0 is not zero");
        assert_eq!(EVAL_INPUT_CLEANUPS.load(Ordering::SeqCst), 2);

        let invalid_layer = Layer::new(
            1,
            0,
            vec![TermDelta {
                g: 0,
                h: [0, 0],
                k_index: 0,
            }],
            vec![vec![0]],
            vec![0],
        );
        let mut invalid = circuit(vec![invalid_layer], 0, 1);
        invalid.raw.constants.push(field.zero());
        let unwind = catch_unwind(AssertUnwindSafe(|| {
            let _ = eval_circuit(Vec::new(), &invalid, &field);
        }));
        assert!(unwind.is_err());
        assert_eq!(EVAL_INPUT_CLEANUPS.load(Ordering::SeqCst), 3);
    }

    #[test]
    fn ordinary_quad_error_redacts_witness_values() {
        let field = Gf2_128Field::new();
        let layer = Layer::new(
            1,
            0,
            vec![TermDelta {
                g: 0,
                h: [0, 0],
                k_index: 0,
            }],
            vec![vec![0]],
            vec![0],
        );
        let error = eval_quad(1, &[field.one()], &layer, &[field.zero()], &field)
            .expect_err("nonzero multiplication constraint must fail");
        assert_eq!(
            error,
            "gate multiplication constraint not satisfied: left_wire=0, right_wire=0"
        );
        assert!(!error.contains("_val="));
    }
}
