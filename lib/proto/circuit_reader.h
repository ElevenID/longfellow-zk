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

#ifndef PRIVACY_PROOFS_ZK_LIB_PROTO_CIRCUIT_READER_H_
#define PRIVACY_PROOFS_ZK_LIB_PROTO_CIRCUIT_READER_H_

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <memory>
#include <vector>

#include "proto/circuit_io.h"
#include "sumcheck/circuit.h"
#include "sumcheck/circuit_id.h"
#include "sumcheck/quad.h"
#include "sumcheck/quad_builder.h"
#include "util/ceildiv.h"
#include "util/panic.h"
#include "util/readbuffer.h"

namespace proofs {
// Circuit reader.
//
// We expect circuits to be created and stored locally by the prover
// and verifier respectively. The byte representations are thus
// assumed to be trusted. As a result, the parser below performs only
// basic sanity checking.

template <class Field>
class CircuitReader {
  using Elt = typename Field::Elt;
  using QuadCorner = typename Quad<Field>::quad_corner_t;

 public:
  explicit CircuitReader(const Field& f, FieldID field_id)
      : f_(f), field_id_(field_id) {}

  // Returns a unique_ptr<Circuit> or nullptr if there is an error in
  // deserializing the circuit.
  //
  // If ENFORCE_CIRCUIT_ID is TRUE, check that the circuit id in
  // the serialization matches the id stored in the circuit.
  std::unique_ptr<Circuit<Field>> from_bytes(ReadBuffer& buf,
                                             bool enforce_circuit_id) {
    std::unique_ptr<Circuit<Field>> c;
    std::shared_ptr<std::vector<Elt>> constants;
    if (!read_header(buf, c, constants)) {
      return nullptr;
    }

    if (!read_layers(buf, c->nl, c->nv, constants->size(), constants, *c)) {
      return nullptr;
    }
    // Read the circuit name from the serialization.
    if (!buf.have(CircuitIO::kIdSize)) {
      return nullptr;
    }
    buf.next(CircuitIO::kIdSize, c->id);

    if (enforce_circuit_id) {
      uint8_t idtmp[CircuitIO::kIdSize];
      circuit_id(idtmp, *c, f_);
      if (memcmp(idtmp, c->id, CircuitIO::kIdSize) != 0) {
        return nullptr;
      }
    }
    return c;
  }

 private:
  bool read_header(ReadBuffer& buf, std::unique_ptr<Circuit<Field>>& c,
                   std::shared_ptr<std::vector<Elt>>& constants) {
    if (!buf.have(8 * CircuitIO::kBytesPerSizeT + 1)) {
      return false;
    }

    uint8_t version = *buf.next(1);
    if (version != 1) {
      return false;
    }

    size_t fid_as_size_t = read_field_id(buf);
    size_t nv = read_size(buf);
    size_t nc = read_size(buf);
    size_t npub_in = read_size(buf);
    size_t subfield_boundary = read_size(buf);
    size_t ninputs = read_size(buf);
    size_t nl = read_size(buf);
    size_t numconst = read_size(buf);

    // Basic sanity checks.
    if (nv == 0 || nv > kMaxValidWireId || nc == 0 || nl == 0 ||
        nl > CircuitIO::kMaxLayers ||
        fid_as_size_t != static_cast<size_t>(field_id_) ||
        ninputs > kMaxValidWireId || npub_in > ninputs ||
        subfield_boundary > ninputs || numconst > kMaxValidIndex) {
      return false;
    }

    // Ensure there are enough input bytes for the quad constants.
    auto need = CircuitIO::checked_mul(numconst, Field::kBytes);
    if (!need || !buf.have(need.value())) {
      return false;
    }

    constants = std::make_shared<std::vector<Elt>>(numconst);
    for (size_t i = 0; i < numconst; ++i) {
      auto vv = f_.of_bytes_field(buf.next(Field::kBytes));
      if (!vv.has_value()) {
        return false;
      }
      (*constants)[i] = vv.value();
    }

    c = std::make_unique<Circuit<Field>>();
    *c = Circuit<Field>{
        .nv = nv,
        .logv = lg(nv),
        .nc = nc,
        .logc = lg(nc),
        .nl = nl,
        .ninputs = ninputs,
        .npub_in = npub_in,
        .subfield_boundary = subfield_boundary,
    };
    c->l.reserve(nl);
    return true;
  }
  static constexpr size_t kMaxValidWireId = 0xFFFFFFFEull;
  static constexpr size_t kMaxValidIndex = 0xFFFFFFFFull;

  bool read_layers(ReadBuffer& buf, size_t nl, size_t nv, size_t numconst,
                   const std::shared_ptr<std::vector<Elt>>& constants,
                   Circuit<Field>& c) {
    // a starting bound on quad number
    size_t max_g = nv;

    // Use an approximate delta table builder, preferring quick lookup at the
    // cost of missing some deduplications.
    ApproximateDeltaTableBuilder<Field> db(/*prime*/ 8209);

    for (size_t ly = 0; ly < nl; ++ly) {
      // Ensure there are enough input bytes for the layer, 3 values.
      if (!buf.have(3 * CircuitIO::kBytesPerSizeT)) {
        return false;
      }

      size_t lw = read_size(buf);
      if (lw > LayerProof<Field>::kMaxBindings || !(lw > 0)) return false;

      size_t nw = read_size(buf);
      if (!(nw > 0) || nw < lw || nw > kMaxValidWireId || nw > (1ull << lw))
        return false;

      size_t nq = read_size(buf);
      if (!(nq > 0) || nq > kMaxValidIndex) return false;

      // Each quad takes 4 values, check for overflow.
      auto need = CircuitIO::checked_mul(4 * CircuitIO::kBytesPerSizeT, nq);
      if (!need || !buf.have(need.value())) {
        return false;
      }

      auto qq = std::make_unique<Quad<Field>>(nq, constants, db.delta_table());
      if (!read_quads(buf, nq, max_g, nw, numconst, *qq, db)) {
        return false;
      }
      c.l.push_back(Layer<Field>{
          .nw = nw,
          .logw = lw,
          .quad = std::unique_ptr<const Quad<Field>>(std::move(qq))});
      // The outputs of layer ly become the inputs for layer ly+1.
      // Thus, the new maximum value for g in the next layer is the number of
      // wires in this layer.
      max_g = nw;
    }
    return true;
  }

  bool read_quads(ReadBuffer& buf, size_t nq, size_t max_g, size_t nw,
                  size_t numconst, Quad<Field>& qq,
                  ApproximateDeltaTableBuilder<Field>& db) {
    size_t prevg = 0, prevhl = 0, prevhr = 0;
    for (size_t i = 0; i < nq; ++i) {
      size_t g = read_index(buf, prevg);
      if (g >= max_g) {  // index of quad must be < wires in the layer
        return false;
      }
      size_t hl = read_index(buf, prevhl);
      size_t hr = read_index(buf, prevhr);
      if (hl >= nw || hr >= nw) {
        return false;
      }
      size_t vi = read_num(buf);
      if (vi >= numconst) {
        return false;
      }

      qq.assign(i,
                db.dedup(QuadCorner(g - prevg), QuadCorner(hl - prevhl),
                         QuadCorner(hr - prevhr), static_cast<uint32_t>(vi)));
      prevg = g;
      prevhl = hl;
      prevhr = hr;
    }
    return true;
  }
  // Do not cast to FieldID, since the input is untrusted and the
  // cast may fail.
  static size_t read_field_id(ReadBuffer& buf) { return read_num(buf); }

  static size_t read_size(ReadBuffer& buf) { return read_num(buf); }

  static size_t read_index(ReadBuffer& buf, size_t prev_ind) {
    size_t delta = read_num(buf);
    if (delta & 1) {
      return prev_ind - (delta >> 1);
    } else {
      return prev_ind + (delta >> 1);
    }
  }

  // This routine reads bytes written by serialize_* methods, and thus
  // only needs to handle values expressed in kBytesPerSizeT.
  // On 32b platforms, some large circuits may fail; this method
  // causes a failure in that case.
  static size_t read_num(ReadBuffer& buf) {
    uint64_t r = 0;
    const uint8_t* p = buf.next(CircuitIO::kBytesPerSizeT);
    for (size_t i = 0; i < CircuitIO::kBytesPerSizeT; ++i) {
      r |= (static_cast<uint64_t>(p[i]) << (i * 8));
    }

    // SIZE_MAX is system defined as max value for size_t.
    // This check fails if a large circuit is loaded on a 32b machine.
    check(r < SIZE_MAX, "Violating small wire-label assumption");
    return static_cast<size_t>(r);
  }

  const Field& f_;
  FieldID field_id_;
};

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_PROTO_CIRCUIT_READER_H_
