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

use crate::RandomEngine;
use rand_chacha::ChaCha20Rng;
use rand_core::{RngCore, SeedableRng};

/// A cryptographically secure random engine seeded once from the operating
/// system CSPRNG. Construction is fallible so entropy failure can be handled
/// before proof generation begins; byte generation cannot abort the process.
pub struct SecureRandomEngine(ChaCha20Rng);

impl SecureRandomEngine {
    pub fn try_new() -> Result<Self, getrandom::Error> {
        Self::try_from_seed_source(getrandom::fill)
    }

    fn try_from_seed_source<E>(
        seed_source: impl FnOnce(&mut [u8]) -> Result<(), E>,
    ) -> Result<Self, E> {
        let mut seed = <ChaCha20Rng as SeedableRng>::Seed::default();
        seed_source(&mut seed)?;
        Ok(Self(ChaCha20Rng::from_seed(seed)))
    }
}

impl std::fmt::Debug for SecureRandomEngine {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_tuple("SecureRandomEngine")
            .field(&"[REDACTED]")
            .finish()
    }
}

impl RandomEngine for SecureRandomEngine {
    fn bytes(&mut self, len: usize) -> Vec<u8> {
        let mut buf = vec![0u8; len];
        self.0.fill_bytes(&mut buf);
        buf
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn seed_failure_is_returned_to_the_caller() {
        let result = SecureRandomEngine::try_from_seed_source(|_| Err("entropy unavailable"));

        assert_eq!(result.unwrap_err(), "entropy unavailable");
    }

    #[test]
    fn seeded_engine_advances_between_requests() {
        let mut engine = SecureRandomEngine::try_from_seed_source(|seed| {
            seed.copy_from_slice(&[7_u8; 32]);
            Ok::<_, ()>(())
        })
        .unwrap();

        assert_ne!(engine.bytes(64), engine.bytes(64));
    }
}
