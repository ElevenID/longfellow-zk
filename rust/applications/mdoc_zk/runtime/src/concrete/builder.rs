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

#[cfg(feature = "prover")]
use core_algebra::AlgebraicField;
use core_algebra::{Nat, SerializableField, SupportsU128Conversions};
use runtime_algebra::{gf2_128::Gf2_128Field, p256::P256Field};
use zeroize::{Zeroize, Zeroizing};

#[cfg(feature = "prover")]
use crate::config::{K_HASH_V256_BIT_PLUCKER, K_SHA_BIT_PLUCKER};
use crate::config::{K_HASH_V8_BIT_PLUCKER, K_SIG_MAC_BIT_PLUCKER};

pub struct AssignmentBuilder<'a, F>
where
    F: core_algebra::BareField + core_algebra::AlgebraicField,
    F::E: Zeroize,
{
    pub field: &'a F,
    pub(crate) buffer: Zeroizing<Vec<F::E>>,
}

impl<'a, F> AssignmentBuilder<'a, F>
where
    F: core_algebra::BareField + core_algebra::AlgebraicField,
    F::E: Zeroize,
{
    pub fn new(field: &'a F) -> Self {
        Self {
            field,
            buffer: Zeroizing::new(Vec::new()),
        }
    }

    pub fn push_elt(&mut self, elt: &F::E) {
        self.buffer.push(elt.clone());
    }

    pub fn into_inner(mut self) -> Vec<F::E> {
        std::mem::take(&mut *self.buffer)
    }

    #[inline(always)]
    fn push_bit(&mut self, bit: bool) {
        self.buffer.push(if bit {
            self.field.one()
        } else {
            self.field.zero()
        });
    }

    pub fn push_bits_len(&mut self, val: u64, nbits: usize) {
        let mut cur_val = val;
        for _ in 0..nbits {
            self.push_bit((cur_val & 1) != 0);
            cur_val >>= 1;
        }
    }

    pub fn push_raw_bytes(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.push_bits_len(u64::from(b), 8);
        }
    }

    pub fn push_pad(&mut self, pad_elt: F::E, count: usize) {
        self.buffer.extend(std::iter::repeat_n(pad_elt, count));
    }

    #[cfg(feature = "prover")]
    pub fn push_ecdsa_given(&mut self, given: &circuits_ecdsa2::concrete::ConcreteGiven<F>) {
        given.push_elements(|elt| self.push_elt(elt));
    }

    #[cfg(feature = "prover")]
    pub fn push_ecdsa_derived(&mut self, derived: &circuits_ecdsa2::concrete::ConcreteDerived<F>) {
        derived.push_elements(|elt| self.push_elt(elt));
    }
}

impl<F: core_algebra::BareField + core_algebra::AlgebraicField + core_algebra::HasLookupPoints>
    AssignmentBuilder<'_, F>
where
    F::E: Zeroize,
{
    fn pack_bits_to_elements<const PLUCKER_WIDTH: usize>(
        &self,
        bits: &[bool],
    ) -> Zeroizing<Vec<F::E>> {
        let num_chunks = bits.len().div_ceil(PLUCKER_WIDTH);
        let mut elts = Zeroizing::new(Vec::with_capacity(num_chunks));
        for i in 0..num_chunks {
            let mut v = 0usize;
            for j in 0..PLUCKER_WIDTH {
                let idx = i * PLUCKER_WIDTH + j;
                if idx < bits.len() && bits[idx] {
                    v |= 1 << j;
                }
            }
            elts.push(self.field.lookup_point((1 << PLUCKER_WIDTH) + 1, v));
        }
        elts
    }

    fn push_value_plucked<const PLUCKER_WIDTH: usize, const BIT_LEN: usize>(&mut self, val: u128) {
        let mut bits = Zeroizing::new([false; BIT_LEN]);
        let mut cur_val = val;
        for item in bits.iter_mut() {
            *item = (cur_val & 1) != 0;
            cur_val >>= 1;
        }
        let elts = self.pack_bits_to_elements::<PLUCKER_WIDTH>(&bits[..]);
        self.buffer.extend(elts.iter().cloned());
    }

    #[cfg(feature = "prover")]
    fn push_nat_plucked<const PLUCKER_WIDTH: usize, const W: usize, N: Nat<W>>(&mut self, nat: &N) {
        let mut bytes = Zeroizing::new(nat.to_bytes_le());
        bytes.resize(W * 8, 0);

        let mut bits = Zeroizing::new(vec![false; W * 64]);
        for (i, &byte) in bytes.iter().enumerate() {
            let mut cur_byte = byte;
            for k in 0..8 {
                bits[i * 8 + k] = (cur_byte & 1) != 0;
                cur_byte >>= 1;
            }
        }

        let elts = self.pack_bits_to_elements::<PLUCKER_WIDTH>(&bits);
        self.buffer.extend(elts.iter().cloned());
    }
    #[cfg(feature = "prover")]
    fn pack_bits_to_elements_legacy<const PLUCKER_WIDTH: usize>(
        &self,
        bits: &[bool],
    ) -> Zeroizing<Vec<F::E>> {
        let num_chunks = bits.len().div_ceil(PLUCKER_WIDTH);
        let mut elts = Zeroizing::new(Vec::with_capacity(num_chunks));
        for i in 0..num_chunks {
            let mut v = 0usize;
            for j in 0..PLUCKER_WIDTH {
                let idx = i * PLUCKER_WIDTH + j;
                if idx < bits.len() && bits[idx] {
                    v |= 1 << j;
                }
            }
            elts.push(self.field.lookup_point(1 << PLUCKER_WIDTH, v));
        }
        elts
    }

    #[cfg(feature = "prover")]
    fn push_value_plucked_legacy<const PLUCKER_WIDTH: usize, const BIT_LEN: usize>(
        &mut self,
        val: u128,
    ) {
        let mut bits = Zeroizing::new([false; BIT_LEN]);
        let mut cur_val = val;
        for item in bits.iter_mut() {
            *item = (cur_val & 1) != 0;
            cur_val >>= 1;
        }
        let elts = self.pack_bits_to_elements_legacy::<PLUCKER_WIDTH>(&bits[..]);
        self.buffer.extend(elts.iter().cloned());
    }
}

impl AssignmentBuilder<'_, Gf2_128Field> {
    pub fn push_v8(&mut self, byte: u8) {
        self.push_value_plucked::<{ K_HASH_V8_BIT_PLUCKER }, 8>(u128::from(byte));
    }

    #[cfg(feature = "prover")]
    pub fn push_v32(&mut self, val: u32) {
        self.push_value_plucked::<{ K_SHA_BIT_PLUCKER }, 32>(u128::from(val));
    }

    #[cfg(feature = "prover")]
    pub fn push_v32_legacy(&mut self, val: u32) {
        let mut cur_val = val;
        for _ in 0..8 {
            let val_chunk = (cur_val & 0xf) as usize;
            let plucked = (val_chunk << 1) ^ 15;
            let mut pt = self.field.u128_to_element(0u128);
            for (j, &basis_val) in core_algebra::GF2_16_BASIS_V1.iter().enumerate() {
                if (plucked & (1 << j)) != 0 {
                    pt = self.field.addf(&pt, &self.field.u128_to_element(basis_val));
                }
            }
            self.buffer.push(pt);
            cur_val >>= 4;
        }
    }

    #[cfg(feature = "prover")]
    pub fn push_nat256<N: Nat<4>>(&mut self, nat: &N) {
        self.push_nat_plucked::<{ K_HASH_V256_BIT_PLUCKER }, 4, N>(nat);
    }

    pub fn push_u128(&mut self, val: u128) {
        self.buffer.push(self.field.u128_to_element(val));
    }

    #[cfg(feature = "prover")]
    pub fn push_sha256_derived(&mut self, derived: &circuits_sha256::concrete::ConcreteDerived) {
        for val in derived.modern_elements() {
            self.push_v32(val);
        }
    }

    #[cfg(feature = "prover")]
    pub fn push_sha256msg_derived(
        &mut self,
        derived: &circuits_sha256msg::concrete::ConcreteDerived,
    ) {
        for sha in &derived.sha_derived {
            self.push_sha256_derived(sha);
        }
    }
}

impl AssignmentBuilder<'_, P256Field> {
    pub fn push_nat_256_bits<N: Nat<4>>(&mut self, nat: &N) {
        let mut bytes = Zeroizing::new(nat.to_bytes_le());
        bytes.resize(32, 0);
        for &b in bytes.iter() {
            self.push_bits_len(u64::from(b), 8);
        }
    }

    pub fn push_plucked_128(&mut self, val: u128) {
        self.push_value_plucked::<{ K_SIG_MAC_BIT_PLUCKER }, 128>(val);
    }

    #[cfg(feature = "prover")]
    pub fn push_plucked_128_legacy(&mut self, val: u128) {
        self.push_value_plucked_legacy::<{ K_SIG_MAC_BIT_PLUCKER }, 128>(val);
    }

    pub fn push_nat_elt<const W_NAT: usize, N: Nat<W_NAT>>(&mut self, val: &N) {
        let mut bytes = Zeroizing::new(val.to_bytes_le());
        bytes.resize(32, 0);
        let el = self.field.bytes_to_element(&bytes).unwrap();
        self.buffer.push(el);
    }
}
