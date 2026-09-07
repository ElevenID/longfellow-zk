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

use runtime_algebra::{Subfield, SupportsSampling};
use std::ops::{Deref, DerefMut};
use zeroize::Zeroize;

struct ZeroizeOnDropRef<'a, T: Zeroize>(&'a mut T);

impl<T: Zeroize> Deref for ZeroizeOnDropRef<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl<T: Zeroize> DerefMut for ZeroizeOnDropRef<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0
    }
}

impl<T: Zeroize> Drop for ZeroizeOnDropRef<'_, T> {
    fn drop(&mut self) {
        self.0.zeroize();
    }
}

pub mod transcript;
pub use transcript::Transcript;
mod secure_hash;
#[cfg(any(test, feature = "hash-test-observer"))]
#[doc(hidden)]
pub use secure_hash::HashCleanupObserver;
pub use secure_hash::SecureSha256;

/// Trait defining operations for seedable/pseudorandom challenge engines.
pub trait RandomEngine {
    /// Generates raw pseudorandom bytes of the specified length.
    fn bytes(&mut self, len: usize) -> Vec<u8>;

    /// Generates a random field element.
    fn elt_field<const W: usize, F: SupportsSampling<W>>(&mut self, f: &F) -> F::E {
        f.sample(|len| self.bytes(len))
    }

    /// Generates a random subfield element.
    fn elt_subfield<SF: Subfield>(&mut self, sf: &SF) -> SF::E {
        sf.sample(|len| self.bytes(len))
    }

    /// Generates a slice of field elements with random values.
    fn elt_field_slice<const W: usize, F: SupportsSampling<W>>(
        &mut self,
        len: usize,
        f: &F,
    ) -> Vec<F::E> {
        let mut v = Vec::with_capacity(len);
        for _ in 0..len {
            v.push(self.elt_field(f));
        }
        v
    }

    /// Generates a random u128.
    fn u128(&mut self) -> u128 {
        let mut bytes = Vec::new();
        let mut value = 0u128;
        u128_with_scratch(self, &mut bytes, &mut value, || {})
    }

    /// Generates a random integer in `[0, n)`.
    fn nat(&mut self, n: usize) -> usize {
        let mut bytes = Vec::new();
        let mut candidate = 0usize;
        nat_with_scratch(self, n, &mut bytes, &mut candidate, || {})
    }

    /// Chooses `k` unique indices from `[0, n)` randomly.
    fn choose(&mut self, res: &mut [usize], n: usize, k: usize) {
        if n == 0 || k == 0 {
            return;
        }
        assert!(n >= k && res.len() >= k);
        let mut a: Vec<usize> = (0..n).collect();
        let res_slice = &mut res[..k];
        let a_slice = &mut a[..n];
        for i in 0..k {
            let j = (i + self.nat(n - i)) % n;
            a_slice.swap(i, j);
            res_slice[i] = a_slice[i];
        }
    }

    /// Computes the bit mask for a value `n`.
    fn mask(&self, n: usize) -> usize {
        let mut msk = 0usize;
        while (n & msk) != n {
            msk = (msk << 1) | 1;
        }
        msk
    }
}

fn u128_with_scratch<E, H>(
    engine: &mut E,
    bytes: &mut Vec<u8>,
    value: &mut u128,
    after_decode: H,
) -> u128
where
    E: RandomEngine + ?Sized,
    H: FnOnce(),
{
    use zeroize::Zeroizing;

    let mut guarded_bytes = ZeroizeOnDropRef(bytes);
    let mut guarded_value = ZeroizeOnDropRef(value);
    guarded_bytes.zeroize();
    guarded_bytes.clear();
    guarded_bytes.reserve_exact(16);
    guarded_value.zeroize();
    let random = Zeroizing::new(engine.bytes(16));
    assert_eq!(
        random.len(),
        16,
        "random engine returned an unexpected byte count"
    );
    guarded_bytes.extend_from_slice(&random);
    for (i, byte) in guarded_bytes.iter().enumerate() {
        *guarded_value |= u128::from(*byte) << (i * 8);
    }
    after_decode();
    *guarded_value
}

fn nat_with_scratch<E, H>(
    engine: &mut E,
    n: usize,
    bytes: &mut Vec<u8>,
    candidate: &mut usize,
    mut after_decode: H,
) -> usize
where
    E: RandomEngine + ?Sized,
    H: FnMut(),
{
    use zeroize::Zeroizing;

    assert!(n > 0, "nat(0) is undefined");
    let mut nn = n;
    let mut len = 0;
    while nn != 0 {
        nn >>= 8;
        len += 1;
    }
    assert!(len <= std::mem::size_of::<usize>());
    let mask = engine.mask(n);

    let mut guarded_bytes = ZeroizeOnDropRef(bytes);
    let mut guarded_candidate = ZeroizeOnDropRef(candidate);
    guarded_bytes.zeroize();
    guarded_bytes.clear();
    guarded_bytes.reserve_exact(len);
    loop {
        guarded_bytes.zeroize();
        guarded_bytes.clear();
        guarded_candidate.zeroize();
        let random = Zeroizing::new(engine.bytes(len));
        assert_eq!(
            random.len(),
            len,
            "random engine returned an unexpected byte count"
        );
        guarded_bytes.extend_from_slice(&random);
        for i in (0..len).rev() {
            *guarded_candidate = (*guarded_candidate << 8) | usize::from(guarded_bytes[i]);
        }
        *guarded_candidate &= mask;
        after_decode();
        if *guarded_candidate < n {
            return *guarded_candidate;
        }
    }
}

#[cfg(test)]
mod sampling_zeroization_tests {
    use super::{nat_with_scratch, u128_with_scratch, RandomEngine};

    struct ScriptedEngine {
        outputs: std::collections::VecDeque<Vec<u8>>,
    }

    impl ScriptedEngine {
        fn new(outputs: impl IntoIterator<Item = Vec<u8>>) -> Self {
            Self {
                outputs: outputs.into_iter().collect(),
            }
        }
    }

    impl RandomEngine for ScriptedEngine {
        fn bytes(&mut self, len: usize) -> Vec<u8> {
            let output = self.outputs.pop_front().expect("script exhausted");
            assert_eq!(output.len(), len);
            output
        }
    }

    #[test]
    fn integer_sampling_scratch_is_wiped_after_acceptance_rejection_and_unwind() {
        let mut bytes = vec![0xa5; 1];
        let mut candidate = usize::MAX;
        let mut accepting_engine = ScriptedEngine::new([vec![0x07], vec![0x03]]);
        let mut attempts = 0;
        assert_eq!(
            nat_with_scratch(&mut accepting_engine, 5, &mut bytes, &mut candidate, || {
                attempts += 1;
            },),
            3
        );
        assert_eq!(attempts, 2);
        assert!(bytes.iter().all(|byte| *byte == 0));
        assert_eq!(candidate, 0);

        bytes.fill(0xa5);
        candidate = usize::MAX;
        let mut unwind_engine = ScriptedEngine::new([vec![0x03]]);
        let unwind = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            nat_with_scratch(&mut unwind_engine, 5, &mut bytes, &mut candidate, || {
                panic!("injected integer-sampling unwind");
            });
        }));
        assert!(unwind.is_err());
        assert!(bytes.iter().all(|byte| *byte == 0));
        assert_eq!(candidate, 0);
    }

    #[test]
    fn u128_sampling_scratch_is_wiped_on_return_and_unwind() {
        let expected = 0x0011_2233_4455_6677_8899_aabb_ccdd_eeffu128;
        let mut bytes = vec![0xa5; 16];
        let mut value = u128::MAX;
        let mut accepting_engine = ScriptedEngine::new([expected.to_le_bytes().to_vec()]);
        assert_eq!(
            u128_with_scratch(&mut accepting_engine, &mut bytes, &mut value, || {}),
            expected
        );
        assert!(bytes.iter().all(|byte| *byte == 0));
        assert_eq!(value, 0);

        bytes.fill(0xa5);
        value = u128::MAX;
        let mut unwind_engine = ScriptedEngine::new([expected.to_le_bytes().to_vec()]);
        let unwind = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            u128_with_scratch(&mut unwind_engine, &mut bytes, &mut value, || {
                panic!("injected u128-sampling unwind");
            });
        }));
        assert!(unwind.is_err());
        assert!(bytes.iter().all(|byte| *byte == 0));
        assert_eq!(value, 0);
    }
}

#[cfg(feature = "secure-random")]
pub mod secure;
#[cfg(feature = "secure-random")]
pub use secure::SecureRandomEngine;

#[cfg(feature = "testonly")]
pub mod deterministic;
#[cfg(feature = "testonly")]
pub use deterministic::DeterministicRng;
