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

#ifndef PRIVACY_PROOFS_ZK_LIB_CIRCUITS_TESTS_SHA3_SHA3_WITNESS_H_
#define PRIVACY_PROOFS_ZK_LIB_CIRCUITS_TESTS_SHA3_SHA3_WITNESS_H_

#include <cstddef>
#include <cstdint>
#include <vector>

#include "arrays/dense.h"

namespace proofs {

struct Sha3Witness {
  // We record the intermediate state of A every 4 rounds.
  // Keccak-f[1600] has 24 rounds, so there are 6 intermediate states recorded
  // (after round 3, 7, 11, 15, 19, 23).
  struct BlockWitness {
    uint64_t a_intermediate[6][5][5];
  };

  // Runs one block of the keccak permutation on state A, recording
  // intermediates into bw. Note: state A is updated in-place to the new state.
  static void compute_witness_block(uint64_t A[5][5], BlockWitness& bw);

  // Generate BlockWitnesses for a shake256 computation.
  static void compute_witness_shake256(const std::vector<uint8_t>& seed,
                                       size_t outlen,
                                       std::vector<BlockWitness>& witnesses);

  // Fills a Dense array mapping with exactly the bit outputs of the block
  // witnesses.
  template <class Field>
  static void fill_witness(DenseFiller<Field>& filler,
                           const std::vector<BlockWitness>& bws,
                           const Field& f) {
    for (const auto& w : bws) {
      for (size_t i = 0; i < 6; ++i) {
        for (size_t x = 0; x < 5; ++x) {
          for (size_t y = 0; y < 5; ++y) {
            uint64_t val = w.a_intermediate[i][x][y];
            filler.push_back(val, 64, f);
          }
        }
      }
    }
  }
};

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_CIRCUITS_TESTS_SHA3_SHA3_WITNESS_H_
