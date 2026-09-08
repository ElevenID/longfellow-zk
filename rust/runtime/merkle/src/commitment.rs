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
use runtime_proto::MerkleNonce;
use runtime_proto::MerkleProof;
#[cfg(feature = "prover")]
use runtime_random::{RandomEngine, SecureSha256};
use sha2::{Digest as ShaDigest, Sha256};
#[cfg(feature = "prover")]
use zeroize::Zeroize;

#[cfg(feature = "prover")]
use super::heap::MerkleHeap;
use super::{heap::verify_proof, Digest, MerkleError};

/// Pure data structure representing the full Merkle commitment state.
/// It holds:
/// - `num_leaves`: The total number of leaves (columns) committed to.
/// - `mh`: The fully built `MerkleHeap` containing leaf and internal node digests.
/// - `nonce`: The generated `MerkleNonce` salts for all columns/leaves.
#[cfg(feature = "prover")]
pub struct MerkleCommitment {
    pub num_leaves: usize,
    pub mh: MerkleHeap,
    pub nonce: Vec<MerkleNonce>,
}

#[cfg(feature = "prover")]
impl MerkleCommitment {
    /// Erases all prover-only leaf salts. Call this after the final opening if
    /// the commitment object must remain allocated.
    pub fn clear_sensitive_nonces(&mut self) {
        for nonce in &mut self.nonce {
            nonce.bytes.zeroize();
        }
    }
}

#[cfg(feature = "prover")]
impl Drop for MerkleCommitment {
    fn drop(&mut self) {
        self.clear_sensitive_nonces();
    }
}

#[cfg(feature = "prover")]
fn wipe_nonce_vec(nonces: &mut [MerkleNonce]) {
    for nonce in nonces {
        nonce.bytes.zeroize();
    }
}

#[cfg(feature = "prover")]
struct NonceWipeGuard<'a> {
    nonces: &'a mut Vec<MerkleNonce>,
    armed: bool,
}

#[cfg(feature = "prover")]
impl NonceWipeGuard<'_> {
    fn push(&mut self, nonce: MerkleNonce) {
        self.nonces.push(nonce);
    }

    fn disarm(&mut self) {
        self.armed = false;
    }
}

#[cfg(feature = "prover")]
impl Drop for NonceWipeGuard<'_> {
    fn drop(&mut self) {
        if self.armed {
            wipe_nonce_vec(self.nonces);
        }
    }
}

#[cfg(feature = "prover")]
struct RandomBytesWipeGuard<'a> {
    bytes: &'a mut Vec<u8>,
}

#[cfg(feature = "prover")]
impl Drop for RandomBytesWipeGuard<'_> {
    fn drop(&mut self) {
        self.bytes.zeroize();
    }
}

#[cfg(feature = "prover")]
struct NonceScratchWipeGuard<'a> {
    bytes: &'a mut [u8; 32],
}

#[cfg(feature = "prover")]
impl Drop for NonceScratchWipeGuard<'_> {
    fn drop(&mut self) {
        self.bytes.zeroize();
    }
}

#[cfg(feature = "prover")]
fn with_nonce_scratch<T, F, U>(
    bytes: &mut Vec<u8>,
    nonce_scratch: &mut [u8; 32],
    after_copy: F,
    use_nonce: U,
) -> T
where
    F: FnOnce(),
    U: FnOnce(&[u8; 32]) -> T,
{
    let guarded_source = RandomBytesWipeGuard { bytes };
    let guarded_nonce = NonceScratchWipeGuard {
        bytes: nonce_scratch,
    };
    assert_eq!(
        guarded_source.bytes.len(),
        32,
        "random engine returned an unexpected nonce length"
    );
    guarded_nonce.bytes.copy_from_slice(guarded_source.bytes);
    after_copy();
    use_nonce(guarded_nonce.bytes)
}

/// Commits to a set of `num_leaves` leaves/columns.
///
/// For each leaf:
/// 1. Generates a random `MerkleNonce` using the random engine `rng`.
/// 2. Salts the leaf hash by feeding the nonce first into a SHA256 hasher.
/// 3. Computes the leaf data hash by passing the hasher to the closure `update_leaf_hash`.
/// 4. Inserts the computed leaf digest into the `MerkleHeap`.
///
/// Returns the constructed `MerkleCommitment` and the root `Digest`.
#[cfg(feature = "prover")]
pub fn commit<F, R>(
    num_leaves: usize,
    rng: &mut R,
    update_leaf_hash: F,
) -> (MerkleCommitment, Digest)
where
    F: FnMut(usize, &mut SecureSha256),
    R: RandomEngine,
{
    commit_with_hash_factory(num_leaves, rng, update_leaf_hash, SecureSha256::new)
}

#[cfg(feature = "prover")]
fn commit_with_hash_factory<F, R, H>(
    num_leaves: usize,
    rng: &mut R,
    mut update_leaf_hash: F,
    mut new_hash: H,
) -> (MerkleCommitment, Digest)
where
    F: FnMut(usize, &mut SecureSha256),
    R: RandomEngine,
    H: FnMut() -> SecureSha256,
{
    let mut nonce = Vec::with_capacity(num_leaves);
    let mut nonce_guard = NonceWipeGuard {
        nonces: &mut nonce,
        armed: true,
    };
    let mut leaves = Vec::with_capacity(num_leaves);
    for i in 0..num_leaves {
        let mut random_nonce_bytes = rng.bytes(32);
        let mut nonce_scratch = [0u8; 32];
        with_nonce_scratch(
            &mut random_nonce_bytes,
            &mut nonce_scratch,
            || {},
            |nonce_value| {
                let mut sha = new_hash();
                sha.update(nonce_value);
                update_leaf_hash(i, &mut sha);

                let hash = sha.finish();
                let mut digest = Digest::default();
                digest.data.copy_from_slice(&*hash);
                leaves.push(digest);
                nonce_guard.push(MerkleNonce {
                    bytes: *nonce_value,
                });
            },
        );
    }

    let mh = MerkleHeap::new(&leaves);
    let root = mh.root();
    nonce_guard.disarm();
    drop(nonce_guard);
    (
        MerkleCommitment {
            num_leaves,
            mh,
            nonce,
        },
        root,
    )
}

#[cfg(all(test, feature = "prover"))]
mod zeroization_tests {
    use super::{commit_with_hash_factory, with_nonce_scratch, MerkleCommitment, NonceWipeGuard};
    use crate::heap::MerkleHeap;
    use runtime_random::{HashCleanupObserver, RandomEngine, SecureSha256};

    struct RecognizableRandom;

    impl RandomEngine for RecognizableRandom {
        fn bytes(&mut self, len: usize) -> Vec<u8> {
            vec![0xa5; len]
        }
    }

    #[test]
    fn nonce_source_is_wiped_on_return_and_unwind() {
        let mut normal = vec![0xa5; 32];
        let mut normal_scratch = [0x5a; 32];
        let nonce = with_nonce_scratch(&mut normal, &mut normal_scratch, || {}, |bytes| *bytes);
        assert_eq!(nonce, [0xa5; 32]);
        assert!(normal.iter().all(|byte| *byte == 0));
        assert_eq!(normal_scratch, [0; 32]);

        let mut unwinding = vec![0x5a; 32];
        let mut unwind_scratch = [0xa5; 32];
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            with_nonce_scratch(
                &mut unwinding,
                &mut unwind_scratch,
                || panic!("injected unwind"),
                |_| (),
            );
        }));
        assert!(result.is_err());
        assert!(unwinding.iter().all(|byte| *byte == 0));
        assert_eq!(unwind_scratch, [0; 32]);
    }

    #[test]
    fn commitment_explicitly_clears_opened_and_unopened_nonces() {
        let leaves = [crate::Digest::default(); 2];
        let mut commitment = MerkleCommitment {
            num_leaves: 2,
            mh: MerkleHeap::new(&leaves),
            nonce: vec![
                runtime_proto::MerkleNonce { bytes: [0xa5; 32] },
                runtime_proto::MerkleNonce { bytes: [0x5a; 32] },
            ],
        };
        let proof = super::open(&commitment, &[0]);
        assert_eq!(proof.nonce[0].bytes, [0xa5; 32]);
        commitment.clear_sensitive_nonces();
        assert!(commitment
            .nonce
            .iter()
            .all(|nonce| nonce.bytes.iter().all(|byte| *byte == 0)));
    }

    #[test]
    fn partial_nonce_storage_is_wiped_on_unwind() {
        let mut nonces = Vec::new();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut guard = NonceWipeGuard {
                nonces: &mut nonces,
                armed: true,
            };
            guard.push(runtime_proto::MerkleNonce { bytes: [0xa5; 32] });
            panic!("injected commitment failure");
        }));
        assert!(result.is_err());
        assert_eq!(nonces.len(), 1);
        assert!(nonces[0].bytes.iter().all(|byte| *byte == 0));
    }

    #[test]
    fn merkle_hash_state_is_wiped_after_finalize_and_unwind() {
        let finalize_observer = HashCleanupObserver::default();
        let mut finishing_rng = RecognizableRandom;
        let (commitment, _) =
            commit_with_hash_factory(1, &mut finishing_rng, |_, hash| hash.update(&[0x5a; 31]), {
                let observer = finalize_observer.clone();
                move || SecureSha256::new_with_cleanup_observer(observer.clone())
            });
        assert_eq!(finalize_observer.cleanup_count(), 1);
        drop(commitment);

        let unwind_observer = HashCleanupObserver::default();
        let mut unwinding_rng = RecognizableRandom;
        let unwind = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            commit_with_hash_factory(
                1,
                &mut unwinding_rng,
                |_, hash| {
                    hash.update(&[0x5a; 31]);
                    panic!("injected Merkle hash unwind");
                },
                {
                    let observer = unwind_observer.clone();
                    move || SecureSha256::new_with_cleanup_observer(observer.clone())
                },
            );
        }));
        assert!(unwind.is_err());
        assert_eq!(unwind_observer.cleanup_count(), 1);
    }
}

/// Opens the commitment at the queried leaf positions `opened_indices`.
///
/// # Safety Note
/// `open` is called by the Prover during Fiat-Shamir proof generation using transcript-derived
/// query indices. An assertion checks that all queried leaf indices fall strictly within
/// `0..commitment.num_leaves`.
///
/// Returns a `MerkleProof` containing:
/// - The nonces at the queried positions.
/// - The sibling digests path needed to reconstruct the path to the root.
#[must_use]
#[cfg(feature = "prover")]
pub fn open(commitment: &MerkleCommitment, opened_indices: &[usize]) -> MerkleProof {
    let np = opened_indices.len();
    let mut nonce = Vec::with_capacity(np);
    for &idx in opened_indices {
        assert!(
            idx < commitment.num_leaves,
            "leaf index {} out of bounds (num_leaves = {})",
            idx,
            commitment.num_leaves
        );
        nonce.push(commitment.nonce[idx]);
    }
    let path = commitment.mh.generate_proof(opened_indices);
    MerkleProof { nonce, path }
}

/// Verifies that the opened column data (hashed via `update_leaf_hash`) matches
/// the commitment root at the queried leaf positions `opened_indices`.
///
/// 1. Reconstructs each leaf digest by hashing the provided nonce (from the proof) along with the
///    leaf data (supplied by the caller via `update_leaf_hash`). The callback receives both the
///    local query index (`0..num_queries`) and the global leaf index (`opened_indices[r]`).
/// 2. Performs Merkle path verification using `verify_proof`.
pub fn verify<F>(
    num_leaves: usize,
    root: &Digest,
    opened_indices: &[usize],
    proof: &MerkleProof,
    mut update_leaf_hash: F,
) -> Result<(), MerkleError>
where
    F: FnMut(usize, usize, &mut Sha256),
{
    let num_queries = opened_indices.len();
    if proof.nonce.len() != num_queries {
        return Err(MerkleError::InvalidNonceLength {
            expected: num_queries,
            found: proof.nonce.len(),
        });
    }
    let mut leaves = vec![Digest::default(); num_queries];
    for r in 0..num_queries {
        let mut sha = Sha256::new();
        sha.update(proof.nonce[r].bytes);
        update_leaf_hash(r, opened_indices[r], &mut sha);
        leaves[r].data.copy_from_slice(&sha.finalize());
    }

    let leaves_pairs: Vec<(usize, Digest)> = opened_indices.iter().copied().zip(leaves).collect();

    verify_proof(num_leaves, root, &proof.path, &leaves_pairs)
}
