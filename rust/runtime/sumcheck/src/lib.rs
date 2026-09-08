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
