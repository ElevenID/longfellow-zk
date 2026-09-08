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

#[cfg(feature = "verifier")]
pub mod attribute;
#[cfg(feature = "verifier")]
pub(crate) mod concrete;
#[cfg(feature = "verifier")]
pub mod error;
#[cfg(feature = "prover")]
pub(crate) mod mac;
#[cfg(feature = "verifier")]
pub mod proto;
#[cfg(feature = "prover")]
pub mod prover;
#[cfg(feature = "circuit-provider")]
pub mod provider;
#[cfg(feature = "verifier")]
pub(crate) mod utils;
#[cfg(feature = "verifier")]
pub mod verifier;
#[cfg(feature = "verifier")]
pub mod zk_spec;

#[cfg(feature = "verifier")]
pub use attribute::RequestedAttribute;
#[cfg(feature = "verifier")]
pub use concrete::{push_input_hash, push_input_sig};
#[cfg(feature = "prover")]
pub(crate) use concrete::{push_witness_hash, push_witness_sig};
#[cfg(feature = "prover")]
pub use error::MdocProverErrorCode;
#[cfg(feature = "verifier")]
pub use error::MdocVerifierErrorCode;
#[cfg(feature = "prover")]
pub(crate) use mac::generate_mac_ap;
#[cfg(feature = "prover")]
pub use mac::push_macs;
#[cfg(feature = "verifier")]
pub use mdoc_zk_circuits as circuits;
#[cfg(feature = "circuit-provider")]
pub use mdoc_zk_compile as generate;
#[cfg(feature = "circuit-provider")]
pub use mdoc_zk_compile::*;
#[cfg(feature = "verifier")]
pub use mdoc_zk_proto::{config, *};
#[cfg(feature = "verifier")]
pub use proto::*;
#[cfg(feature = "prover")]
pub use prover::*;
#[cfg(feature = "circuit-provider")]
pub use provider::*;
#[cfg(feature = "verifier")]
pub use utils::{circuit_supports, parse_hex_nat, parse_pk_coordinate, req_attr, same_namespace};
#[cfg(feature = "verifier")]
pub use verifier::*;
#[cfg(feature = "verifier")]
pub use zk_spec::*;

/// Compile-time boundary: raw prover keys and witness vectors are internal.
///
/// ```compile_fail
/// use mdoc_zk_runtime::generate_mac_ap;
/// ```
///
/// ```compile_fail
/// use mdoc_zk_runtime::push_witness_hash;
/// ```
///
/// ```compile_fail
/// use mdoc_zk_runtime::push_witness_sig;
/// ```
#[cfg(feature = "prover")]
pub struct SecretProducerApiBoundary;
