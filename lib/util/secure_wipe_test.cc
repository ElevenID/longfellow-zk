// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "util/secure_wipe.h"

#include <cstdint>
#include <vector>

#include "gtest/gtest.h"

namespace proofs {
namespace {

TEST(SecureWipeTest, ClearsObjectAndVectorStorage) {
  uint64_t value = 0xffffffffffffffffULL;
  secure_wipe_object(value);
  EXPECT_EQ(value, 0u);

  std::vector<uint8_t> bytes(32, 0xa5);
  secure_wipe_vector(bytes);
  for (uint8_t byte : bytes) {
    EXPECT_EQ(byte, 0u);
  }
}

TEST(SecureWipeTest, GuardClearsStorageAtScopeExit) {
  std::vector<uint32_t> words(8, 0xa5a5a5a5u);
  {
    SecureWipeGuard<uint32_t> wipe(words);
  }
  for (uint32_t word : words) {
    EXPECT_EQ(word, 0u);
  }
}

TEST(SecureWipeTest, ObjectGuardClearsStorageAtScopeExit) {
  uint64_t words[2] = {0xffffffffffffffffULL, 0xa5a5a5a5a5a5a5a5ULL};
  {
    SecureObjectWipeGuard<uint64_t[2]> wipe(words);
  }
  EXPECT_EQ(words[0], 0u);
  EXPECT_EQ(words[1], 0u);
}

}  // namespace
}  // namespace proofs
