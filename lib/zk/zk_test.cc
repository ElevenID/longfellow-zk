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

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <memory>
#include <stdexcept>
#include <vector>

#include "algebra/convolution.h"
#include "algebra/fp_p128.h"
#include "algebra/reed_solomon.h"
#include "arrays/dense.h"
#include "circuits/compiler/circuit_dump.h"
#include "circuits/compiler/compiler.h"
#include "circuits/ecdsa/verify_circuit.h"
#include "circuits/ecdsa/verify_witness.h"
#include "circuits/logic/compiler_backend.h"
#include "circuits/logic/logic.h"
#include "ec/p256.h"
#include "proto/circuit_io.h"
#include "proto/circuit_writer.h"
#include "random/random.h"
#include "random/secure_random_engine.h"
#include "random/transcript.h"
#include "sumcheck/circuit.h"
#include "sumcheck/prover.h"
#include "util/log.h"
#include "util/readbuffer.h"
#include "zk/zk_common.h"
#include "zk/zk_proof.h"
#include "zk/zk_prover.h"
#include "zk/zk_testing.h"
#include "gtest/gtest.h"

namespace proofs {
namespace {

// Test fixture for ZK.
// This class produces static versions of a test circuit that can be used for
// many tests.
class ZKTest : public testing::Test {
  using Nat = Fp256Base::N;
  using Elt = Fp256Base::Elt;
  using Verw = VerifyWitness3<P256, Fp256Scalar>;

 protected:
  ZKTest()
      : pkx_(p256_base.of_string("0x88903e4e1339bde78dd5b3d7baf3efdd72eb5bf5aaa"
                                 "f686c8f9ff5e7c6368d9c")),
        pky_(p256_base.of_string("0xeb8341fc38bb802138498d5f4c03733f457ebbafd0b"
                                 "2fe38e6f58626767f9e75")),
        omega_x_(p256_base.of_string("0xf90d338ebd84f5665cfc85c67990e3379fc9563"
                                     "b382a4a4c985a65324b242562")),
        omega_y_(p256_base.of_string("0xb9e81e42bc97cc4da04fc2e20106e34084738a6"
                                     "474d232c6dbf4174f60a43eac")),
        e_("0x2c26b46b68ffc68ff99b453c1d30413413422d706483bfa0f98a5e886266e7a"
           "e"),
        r_("0xc71bcbfb28bbe06299a225f057797aaf5f22669e90475de5f64176b2612671"),
        s_("0x42ad2f2ec7b6e91360b53427690dddfe578c10d8cf480a66a6c2410ff4f6dd4"
           "0") {
    set_log_level(INFO);
    w_ = std::make_unique<Dense<Fp256Base>>(1, circuit1_->ninputs);
    DenseFiller<Fp256Base> filler(*w_);

    Verw vw(p256_scalar, p256);
    vw.compute_witness(pkx_, pky_, e_, r_, s_);
    filler.push_back(p256_base.one());
    filler.push_back(pkx_);
    filler.push_back(pky_);
    filler.push_back(p256_base.to_montgomery(e_));
    vw.fill_witness(filler);

    // public input
    pub_ = std::make_unique<Dense<Fp256Base>>(1, circuit1_->ninputs);
    DenseFiller<Fp256Base> pubfill(*pub_);
    pubfill.push_back(p256_base.one());
    pubfill.push_back(pkx_);
    pubfill.push_back(pky_);
    pubfill.push_back(p256_base.to_montgomery(e_));
  }

  static void SetUpTestCase() {
    if (circuit1_ == nullptr) {
      using CompilerBackend = CompilerBackend<Fp256Base>;
      using LogicCircuit = Logic<Fp256Base, CompilerBackend>;
      using EltW = typename LogicCircuit::EltW;
      using Verc = VerifyCircuit<LogicCircuit, Fp256Base, P256>;
      QuadCircuit<Fp256Base> Q(p256_base);
      const CompilerBackend cbk(&Q);
      const LogicCircuit lc(&cbk, p256_base);

      Verc verc(lc, p256, n256_order);

      EltW pkx = lc.eltw_input(), pky = lc.eltw_input(), e = lc.eltw_input();
      Q.private_input();
      Verc::Witness vwc;
      vwc.input(lc);
      verc.verify_signature3(pkx, pky, e, vwc);
      circuit1_ = Q.mkcircuit(1).release();
    }
  }

  static void TearDownTestCase() {
    if (circuit1_ != nullptr) {
      delete circuit1_;
      circuit1_ = nullptr;
    }
  }

  static Circuit<Fp256Base>* circuit1_;
  std::unique_ptr<Dense<Fp256Base>> w_;
  std::unique_ptr<Dense<Fp256Base>> pub_;
  const Elt pkx_, pky_, omega_x_, omega_y_;
  const Nat e_, r_, s_;
};

Circuit<Fp256Base>* ZKTest::circuit1_ = nullptr;

TEST_F(ZKTest, prover_verifier) {
  run2_test_zk(*circuit1_, *w_, *pub_, p256_base, omega_x_, omega_y_,
               1ull << 31);
}

TEST_F(ZKTest, failing_test) {
  auto W_fail = Dense<Fp256Base>(1, circuit1_->ninputs);
  DenseFiller<Fp256Base> wf(W_fail);
  wf.push_back(p256_base.one());
  wf.push_back(pkx_);
  wf.push_back(pky_);
  wf.push_back(p256_base.to_montgomery(e_));
  run_failing_test_zk2(*circuit1_, W_fail, *pub_, p256_base, omega_x_, omega_y_,
                       1ull << 31);
}

TEST_F(ZKTest, short_proofs_fail) {
  ZkProof<Fp256Base> zkpv(*circuit1_, 4, 189);
  std::vector<uint8_t> buf(213348, 1u);
  // Check that short proofs fail.
  for (size_t i = 1; i < buf.size(); ++i) {
    ReadBuffer rb(buf.data(), buf.size() - i);
    EXPECT_FALSE(zkpv.read(rb, p256_base));
  }
}

TEST_F(ZKTest, random_proofs_fail) {
  ZkProof<Fp256Base> zkpv(*circuit1_, 4, 189);
  std::vector<uint8_t> buf(213348, 1u);
  for (size_t i = 0; i < buf.size(); ++i) {
    buf[i] = random() & 0xff;
  }
  ReadBuffer rb(buf);
  EXPECT_FALSE(zkpv.read(rb, p256_base));
}

TEST_F(ZKTest, elt_out_of_range) {
  ZkProof<Fp256Base> zkpv(*circuit1_, 4, 189);
  // Initialize the proof so that all of the elt are in range.
  std::vector<uint8_t> buf(213348, 0u);

  // Set the first two run lengths to be 1.
  buf[(3366 + 189) * 32] = 1;
  buf[(3366 + 189 + 1) * 32 + 4] = 1;

  // Selectively create bad elts at these indices and assert the parse fails.
  size_t bad_elts[] = {
      1 * 32,
      13 * 32, /* bad elts in sumcheck transcript */
      451 * 32,
      456 * 32, /* bad elts in com proof, block */
      1133 * 32,
      1134 * 32, /* bad elts in com proof, dblock */
      2496 * 32,
      2497 * 32, /* bad elts in com proof, r */
      2685 * 32,
      2686 * 32,                 /* bad elts in com proof, d-b */
      (3366 + 189) * 32 + 4,     /* bad elt in first run */
      (3366 + 189 + 1) * 32 + 8, /* bad elt in second run */
  };
  for (size_t bi = 0; bi < sizeof(bad_elts) / sizeof(size_t); ++bi) {
    for (size_t i = 0; i < 32; ++i) {
      buf[bad_elts[bi] + i] = 0xff;
    }
    ReadBuffer rb(buf);
    EXPECT_FALSE(zkpv.read(rb, p256_base));
    for (size_t i = 0; i < 32; ++i) {
      buf[bad_elts[bi] + i] = 0x00;
    }
  }
}

TEST(ZK, test_circuit_io) {
  auto c = Circuit<Fp256Base>{
      .nv = 2,
      .logv = 1,
      .nc = 1,
      .logc = 0,
      .nl = 1,
      .ninputs = 4,
      .npub_in = 4,
  };
  c.l.push_back(Layer<Fp256Base>{.nw = 7, .logw = 3, .quad = nullptr});
  ZkProof<Fp256Base> zkpv(c, 4, 16);
  std::vector<uint8_t> buf(213348, 0x02u);
  ReadBuffer rb(buf);
  EXPECT_FALSE(zkpv.read(rb, p256_base));
}

void dump(const char* msg, const std::vector<uint8_t> bytes) {
  size_t sz = bytes.size();
  log(INFO, "%s size: %zu", msg, sz);

  for (size_t i = 0; i < sz; ++i) {
    printf("%02x", bytes[i]);
  }
  printf("\n");
}

// This mock random engine returns a fixed sequence of random bytes in order
// to create "simple" examples for the RFC.
class TestRandomEngine : public RandomEngine {
 public:
  TestRandomEngine() = default;
  void bytes(uint8_t* buf, size_t n) override {
    memset(buf, 0, n);
    buf[0] = 2;
  }
};

class ThrowAfterRandomEngine : public TestRandomEngine {
 public:
  explicit ThrowAfterRandomEngine(size_t successful_calls)
      : successful_calls_(successful_calls) {}

  void bytes(uint8_t* buf, size_t n) override {
    if (successful_calls_ == 0) {
      throw std::runtime_error("injected RNG failure");
    }
    --successful_calls_;
    TestRandomEngine::bytes(buf, n);
  }

 private:
  size_t successful_calls_;
};

template <typename T>
bool vector_storage_is_zero(const std::vector<T>& values) {
  const auto* bytes = reinterpret_cast<const uint8_t*>(values.data());
  for (size_t i = 0; i < values.size() * sizeof(T); ++i) {
    if (bytes[i] != 0) return false;
  }
  return true;
}

TEST(ZK, CommitRetryKeepsWitnessAllocationStable) {
  using TestField = Fp128<>;
  using CompilerBackend = CompilerBackend<TestField>;
  using LogicCircuit = Logic<TestField, CompilerBackend>;
  using EltW = LogicCircuit::EltW;
  const TestField field;
  std::unique_ptr<Circuit<TestField>> circuit;
  {
    QuadCircuit<TestField> compiler(field);
    CompilerBackend backend(&compiler);
    const LogicCircuit logic(&backend, field);
    EltW n = logic.eltw_input();
    compiler.private_input();
    EltW m = logic.eltw_input();
    EltW s = logic.eltw_input();
    logic.assert_eq(
        logic.sub(logic.mul(logic.sub(s, logic.konst(2)), logic.mul(m, m)),
                  logic.mul(logic.sub(s, logic.konst(4)), m)),
        logic.mul(n, logic.konst(2)));
    circuit = compiler.mkcircuit(1);
  }

  Dense<TestField> witness(1, circuit->ninputs);
  DenseFiller<TestField> filler(witness);
  filler.push_back(field.one());
  filler.push_back(field.of_scalar(45));
  filler.push_back(field.of_scalar(5));
  filler.push_back(field.of_scalar(6));
  Dense<TestField> public_inputs(1, circuit->npub_in);
  DenseFiller<TestField> public_filler(public_inputs);
  public_filler.push_back(field.one());

  using FftFactory = FFTConvolutionFactory<TestField>;
  const auto omega =
      field.of_string("164956748514267535023998284330560247862");
  FftFactory fft(field, omega, 1ull << 32);
  using RSFactory = ReedSolomonFactory<TestField, FftFactory>;
  const RSFactory rsf(fft, field);
  ZkProver<TestField, RSFactory> prover(*circuit, field, rsf);
  auto* allocation = prover.witness_.data();
  const size_t capacity = prover.witness_.capacity();

  SecureRandomEngine rng;
  ZkProof<TestField> prior_proof(*circuit, 4, 6);
  Transcript prior_transcript((uint8_t*)"prior", 5);
  prover.commit(prior_proof, witness, prior_transcript, rng);
  ASSERT_NE(prover.lp_.get(), nullptr);
  ASSERT_FALSE(vector_storage_is_zero(prover.pad_.l));
  ASSERT_EQ(prover.witness_.data(), allocation);
  ASSERT_EQ(prover.witness_.capacity(), capacity);
  ASSERT_EQ(prover.witness_.size(), prover.n_witness_);

  ZkProof<TestField> failed_proof(*circuit, 4, 6);
  Transcript failed_transcript((uint8_t*)"retry", 5);
  ThrowAfterRandomEngine throwing_rng(1);
  EXPECT_THROW(
      prover.commit(failed_proof, witness, failed_transcript, throwing_rng),
      std::runtime_error);
  ASSERT_EQ(prover.witness_.data(), allocation);
  ASSERT_EQ(prover.witness_.capacity(), capacity);
  ASSERT_EQ(prover.witness_.size(), prover.n_witness_);
  for (const auto& value : prover.witness_) {
    EXPECT_EQ(value, field.zero());
  }
  EXPECT_TRUE(vector_storage_is_zero(prover.pad_.l));
  EXPECT_TRUE(vector_storage_is_zero(prover.lqc_));
  EXPECT_EQ(prover.lp_.get(), nullptr);

  ZkProof<TestField> fresh_proof(*circuit, 4, 6);
  Transcript fresh_transcript((uint8_t*)"fresh", 5);
  prover.commit(fresh_proof, witness, fresh_transcript, rng);
  EXPECT_EQ(prover.witness_.data(), allocation);
  EXPECT_EQ(prover.witness_.capacity(), capacity);
  EXPECT_EQ(prover.witness_.size(), prover.n_witness_);
  EXPECT_TRUE(prover.prove(fresh_proof, witness, fresh_transcript));

  ZkVerifier<TestField, RSFactory> verifier(*circuit, rsf, 4, 6, field);
  Transcript verifier_transcript((uint8_t*)"fresh", 5);
  verifier.recv_commitment(fresh_proof, verifier_transcript);
  EXPECT_TRUE(
      verifier.verify(fresh_proof, public_inputs, verifier_transcript));
}

// This Test method generates the examples used in our RFC for a circuit,
// for a sumcheck run, and a Ligero run.
// First, it defines a small test circuit:
//     C(n, m, s) = 0 if and only if n is the m-th s-gonal number.
// i.e., verifies that 2n = (s-2)m^2 - (s - 4)*m
// For example, C(45, 5, 6) = 0.
// This relationship was chosen so that it has depth > 2 but not too many
// wires or terms.
TEST(ZK, Rfc_testvector1) {
  set_log_level(INFO);

  using Fp128 = Fp128<>;
  using CompilerBackend = CompilerBackend<Fp128>;
  using LogicCircuit = Logic<Fp128, CompilerBackend>;
  using EltW = LogicCircuit::EltW;
  const Fp128 Fg;
  std::unique_ptr<Circuit<Fp128>> circuit;

  /*scope to delimit compile-time*/ {
    QuadCircuit<Fp128> Q(Fg);
    CompilerBackend cbk(&Q);
    const LogicCircuit LC(&cbk, Fg);
    EltW n = LC.eltw_input();
    Q.private_input();
    EltW m = LC.eltw_input();
    EltW s = LC.eltw_input();
    LC.assert_eq(LC.sub(LC.mul(LC.sub(s, LC.konst(2)), LC.mul(m, m)),
                        LC.mul(LC.sub(s, LC.konst(4)), m)),
                 LC.mul(n, LC.konst(2)));
    circuit = Q.mkcircuit(1);
    dump_info("rfc_sgonal", 1, Q);
  }

  // Serialize the circuit.
  std::vector<uint8_t> bytes;
  CircuitWriter<Fp128> cr(Fg, FP128_ID);
  cr.to_bytes(*circuit, bytes);
  dump("circuit", bytes);

  // Sample input.
  auto W = Dense<Fp128>(1, circuit->ninputs);
  DenseFiller<Fp128> filler(W);

  filler.push_back(Fg.one());
  filler.push_back(Fg.of_scalar(45));
  filler.push_back(Fg.of_scalar(5));
  filler.push_back(Fg.of_scalar(6));

  Transcript tp((uint8_t*)"test", 4);

  // Sumcheck on the circuit.
  ZkCommon<Fp128>::initialize_sumcheck_fiat_shamir(tp, *circuit, W, Fg);

  ZkProof<Fp128> zkpr(*circuit, 4, 6);
  Prover<Fp128>::inputs in;
  Prover<Fp128> sc_prover(Fg);
  auto V = sc_prover.eval_circuit(&in, circuit.get(), W.clone(), Fg);
  EXPECT_TRUE(V != nullptr);
  for (size_t i = 0; i < V->n1_; ++i) {
    EXPECT_EQ(V->v_[i], Fg.zero());
  }
  sc_prover.prove(&zkpr.proof, nullptr, circuit.get(), in, tp);
  std::vector<uint8_t> sc_bytes;
  zkpr.write_sc_proof(zkpr.proof, sc_bytes, Fg);
  dump("sc_proof", sc_bytes);

  // Ligero proof.
  using FftConvolutionFactory = FFTConvolutionFactory<Fp128>;
  auto omega = Fg.of_string("164956748514267535023998284330560247862");
  uint64_t omega_order = 1ull << 32;
  FftConvolutionFactory fft(Fg, omega, omega_order);
  using RSFactory = ReedSolomonFactory<Fp128, FftConvolutionFactory>;
  const RSFactory rsf(fft, Fg);
  auto zkp = ZkProver<Fp128, RSFactory>(*circuit, Fg, rsf);
  TestRandomEngine rng;
  Transcript tlp((uint8_t*)"test", 4);
  zkp.commit(zkpr, W, tlp, rng);

  log(INFO, "params: b:%zu be:%zu nrow:%zu w:%zu r: %zu nq:%zu qr:%zu wit:%zu",
      zkpr.param.block, zkpr.param.block_enc, zkpr.param.nrow, zkpr.param.w,
      zkpr.param.r, zkpr.param.nqtriples, zkpr.param.nq, zkp.witness_.size());

  // Print the tableau.
  std::vector<uint8_t> buf(16, 0);
  for (size_t i = 0; i < zkp.witness_.size(); ++i) {
    Fg.to_bytes_field(&buf[0], zkp.witness_[i]);
    dump("block", buf);
  }

  std::vector<uint8_t> com_bytes;
  zkpr.write_com(zkpr.com, com_bytes, Fg);
  dump("commit", com_bytes);

  EXPECT_TRUE(zkp.prove(zkpr, W, tp));
  std::vector<uint8_t> ligero_bytes;
  zkpr.write_com_proof(zkpr.com_proof, ligero_bytes, Fg);
  dump("ligero_proof", ligero_bytes);
}

}  // namespace
}  // namespace proofs
