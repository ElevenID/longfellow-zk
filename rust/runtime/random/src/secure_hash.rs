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

use sha2::{compress256, digest::generic_array::GenericArray};
use zeroize::{Zeroize, Zeroizing};

const BLOCK_BYTES: usize = 64;
const INITIAL_STATE: [u32; 8] = [
    0x6a09_e667,
    0xbb67_ae85,
    0x3c6e_f372,
    0xa54f_f53a,
    0x510e_527f,
    0x9b05_688c,
    0x1f83_d9ab,
    0x5be0_cd19,
];

/// SHA-256 state whose chaining words and partial-block buffer are securely
/// erased on finalization, unwind, replacement, and drop.
pub struct SecureSha256 {
    state: [u32; 8],
    buffer: [u8; BLOCK_BYTES],
    buffer_len: usize,
    message_len: u64,
    #[cfg(any(test, feature = "hash-test-observer"))]
    cleanup_observer: Option<HashCleanupObserver>,
}

#[cfg(any(test, feature = "hash-test-observer"))]
#[derive(Clone, Default)]
pub struct HashCleanupObserver(std::sync::Arc<std::sync::atomic::AtomicUsize>);

#[cfg(any(test, feature = "hash-test-observer"))]
impl HashCleanupObserver {
    #[must_use]
    pub fn cleanup_count(&self) -> usize {
        self.0.load(std::sync::atomic::Ordering::SeqCst)
    }
}

impl SecureSha256 {
    #[must_use]
    pub fn new() -> Self {
        Self {
            state: INITIAL_STATE,
            buffer: [0u8; BLOCK_BYTES],
            buffer_len: 0,
            message_len: 0,
            #[cfg(any(test, feature = "hash-test-observer"))]
            cleanup_observer: None,
        }
    }

    #[cfg(any(test, feature = "hash-test-observer"))]
    #[doc(hidden)]
    #[must_use]
    pub fn new_with_cleanup_observer(observer: HashCleanupObserver) -> Self {
        Self {
            cleanup_observer: Some(observer),
            ..Self::new()
        }
    }

    pub fn update(&mut self, mut data: &[u8]) {
        self.message_len = self
            .message_len
            .checked_add(u64::try_from(data.len()).expect("SHA-256 input length exceeds u64"))
            .expect("SHA-256 input length overflow");

        if self.buffer_len != 0 {
            let copied = (BLOCK_BYTES - self.buffer_len).min(data.len());
            self.buffer[self.buffer_len..self.buffer_len + copied].copy_from_slice(&data[..copied]);
            self.buffer_len += copied;
            data = &data[copied..];
            if self.buffer_len == BLOCK_BYTES {
                self.compress_buffer();
            }
        }

        while data.len() >= BLOCK_BYTES {
            let (block, remaining) = data.split_at(BLOCK_BYTES);
            compress256(
                &mut self.state,
                core::slice::from_ref(GenericArray::from_slice(block)),
            );
            data = remaining;
        }

        if !data.is_empty() {
            self.buffer[..data.len()].copy_from_slice(data);
            self.buffer_len = data.len();
        }
    }

    #[must_use]
    pub fn finish(mut self) -> Zeroizing<[u8; 32]> {
        let bit_len = self
            .message_len
            .checked_mul(8)
            .expect("SHA-256 bit length overflow");
        self.buffer[self.buffer_len] = 0x80;
        self.buffer_len += 1;
        if self.buffer_len > 56 {
            self.buffer[self.buffer_len..].fill(0);
            self.compress_buffer();
        }
        self.buffer[self.buffer_len..56].fill(0);
        self.buffer[56..].copy_from_slice(&bit_len.to_be_bytes());
        self.buffer_len = BLOCK_BYTES;
        self.compress_buffer();

        let mut digest = Zeroizing::new([0u8; 32]);
        for (chunk, word) in digest.chunks_exact_mut(4).zip(self.state) {
            chunk.copy_from_slice(&word.to_be_bytes());
        }
        self.clear_sensitive_state();
        digest
    }

    fn compress_buffer(&mut self) {
        compress256(
            &mut self.state,
            core::slice::from_ref(GenericArray::from_slice(&self.buffer)),
        );
        self.buffer.zeroize();
        self.buffer_len.zeroize();
    }

    fn clear_sensitive_state(&mut self) {
        self.state.zeroize();
        self.buffer.zeroize();
        self.buffer_len.zeroize();
        self.message_len.zeroize();
    }
}

impl Default for SecureSha256 {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for SecureSha256 {
    fn clone(&self) -> Self {
        Self {
            state: self.state,
            buffer: self.buffer,
            buffer_len: self.buffer_len,
            message_len: self.message_len,
            #[cfg(any(test, feature = "hash-test-observer"))]
            cleanup_observer: self.cleanup_observer.clone(),
        }
    }
}

impl Drop for SecureSha256 {
    fn drop(&mut self) {
        self.clear_sensitive_state();
        #[cfg(any(test, feature = "hash-test-observer"))]
        if let Some(observer) = &self.cleanup_observer {
            debug_assert!(self.state.iter().all(|word| *word == 0));
            debug_assert!(self.buffer.iter().all(|byte| *byte == 0));
            debug_assert_eq!(self.buffer_len, 0);
            debug_assert_eq!(self.message_len, 0);
            observer.0.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{HashCleanupObserver, SecureSha256};
    use sha2::{Digest, Sha256};

    #[test]
    fn sha256_matches_reference_across_padding_and_block_boundaries() {
        for len in [0, 1, 55, 56, 63, 64, 65, 127, 128, 129, 1_048_576] {
            let input: Vec<u8> = (0..len)
                .map(|index| (index as u8).wrapping_mul(37).wrapping_add(11))
                .collect();
            let expected = Sha256::digest(&input);
            let observer = HashCleanupObserver::default();
            let mut actual = SecureSha256::new_with_cleanup_observer(observer.clone());
            for chunk in input.chunks(23) {
                actual.update(chunk);
            }
            assert_eq!(&*actual.finish(), expected.as_slice(), "length {len}");
            assert_eq!(observer.cleanup_count(), 1, "length {len}");
        }
    }

    #[test]
    fn sha256_matches_known_vector_and_wipes_on_finish_and_unwind() {
        let finish_observer = HashCleanupObserver::default();
        let mut finishing_hash = SecureSha256::new_with_cleanup_observer(finish_observer.clone());
        finishing_hash.update(b"abc");
        let digest = finishing_hash.finish();
        assert_eq!(
            &*digest,
            &[
                0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae,
                0x22, 0x23, 0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61,
                0xf2, 0x00, 0x15, 0xad,
            ]
        );
        assert_eq!(finish_observer.cleanup_count(), 1);

        let unwind_observer = HashCleanupObserver::default();
        let unwind = std::panic::catch_unwind({
            let observer = unwind_observer.clone();
            move || {
                let mut unwinding_hash = SecureSha256::new_with_cleanup_observer(observer);
                unwinding_hash.update(&[0xa5; 31]);
                panic!("injected hash unwind");
            }
        });
        assert!(unwind.is_err());
        assert_eq!(unwind_observer.cleanup_count(), 1);
    }
}
