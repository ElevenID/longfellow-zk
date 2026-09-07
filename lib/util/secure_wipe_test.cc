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
#include <stdexcept>
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

TEST(SecureWipeTest, VectorResetGuardWipesAndRestoresLengthOnUnwind) {
  std::vector<uint32_t> words(1, 0xa5a5a5a5u);
  words.reserve(2);
  EXPECT_THROW(
      {
        SecureVectorResetGuard<uint32_t> wipe(words, 1);
        words.push_back(0x5a5a5a5au);
        throw std::runtime_error("test unwind");
      },
      std::runtime_error);
  ASSERT_EQ(words.size(), 1u);
  EXPECT_EQ(words[0], 0u);
}

TEST(SecureWipeTest, ObjectGuardClearsStorageAtScopeExit) {
  uint64_t words[2] = {0xffffffffffffffffULL, 0xa5a5a5a5a5a5a5a5ULL};
  {
    SecureObjectWipeGuard<uint64_t[2]> wipe(words);
  }
  EXPECT_EQ(words[0], 0u);
  EXPECT_EQ(words[1], 0u);
}

TEST(SecureWipeTest, ScratchClearsAfterNormalReturnAndExceptionUnwind) {
  uint8_t scratch[16];
  with_secure_scratch(scratch, [](auto& bytes) {
    for (auto& byte : bytes) byte = 0xa5;
  });
  for (uint8_t byte : scratch) EXPECT_EQ(byte, 0u);

  EXPECT_THROW(
      with_secure_scratch(scratch, [](auto& bytes) {
        for (auto& byte : bytes) byte = 0x5a;
        throw std::runtime_error("test unwind");
      }),
      std::runtime_error);
  for (uint8_t byte : scratch) EXPECT_EQ(byte, 0u);
}

TEST(SecureWipeTest, FixedCapacityGuardClearsWithoutReallocation) {
  std::vector<uint8_t> bytes;
  bytes.reserve(32);
  auto* allocation = bytes.data();
  {
    FixedCapacitySecureWipeGuard<uint8_t> wipe(bytes);
    uint8_t payload[32];
    for (auto& byte : payload) byte = 0xa5;
    wipe.append(payload, sizeof(payload));
    EXPECT_EQ(bytes.data(), allocation);
  }
  for (uint8_t byte : bytes) EXPECT_EQ(byte, 0u);
}

TEST(SecureWipeTest, FixedCapacityGuardRejectsGrowthBeforeMutation) {
  std::vector<uint8_t> bytes;
  bytes.reserve(1);
  FixedCapacitySecureWipeGuard<uint8_t> wipe(bytes);
  wipe.push_back(0xa5);
  auto* allocation = bytes.data();
  const size_t capacity = bytes.capacity();
  const size_t length = bytes.size();

  EXPECT_FALSE(wipe.can_append(1));
  EXPECT_DEATH(wipe.push_back(0x5a), "");
  EXPECT_EQ(bytes.data(), allocation);
  EXPECT_EQ(bytes.capacity(), capacity);
  EXPECT_EQ(bytes.size(), length);
}

}  // namespace
}  // namespace proofs
