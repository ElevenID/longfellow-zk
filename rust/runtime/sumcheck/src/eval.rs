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

pub fn eval_circuit<const W: usize, F>(
    w: Vec<F::E>,
    circuit: &core_proto::circuit::Circuit<F>,
    f: &F,
) -> Result<WitnessLayers<F::E>, String>
where
    F: RuntimeField<W> + SerializableField,
    F::E: Zeroize,
{
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

        let v =
            eval_quad(nv, &w, &circuit.raw.layers[l], &circuit.raw.constants, f).map_err(|e| {
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

pub fn eval_quad<const W: usize, F>(
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
