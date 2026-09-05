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

use sha2::Digest;

use super::{
    append_bytes_len, append_text_len,
    constants::{K_COSE_SIGN1_SIGNING_HEADER, K_DEVICE_AUTHENTICATION_HEADER, K_TAG24},
};

#[must_use]
pub fn compute_transcript_hash(transcript: &[u8], doc_type: &str) -> Vec<u8> {
    let mut doc_type_bytes = Vec::new();
    append_text_len(&mut doc_type_bytes, doc_type.len());
    doc_type_bytes.extend_from_slice(doc_type.as_bytes());

    let mut device_authentication_cbor = K_DEVICE_AUTHENTICATION_HEADER.to_vec();
    device_authentication_cbor.extend_from_slice(transcript);
    device_authentication_cbor.extend_from_slice(&doc_type_bytes);
    device_authentication_cbor.extend_from_slice(&[0xD8, 0x18, 0x41, 0xA0]);

    let mut cose_sign1_bytes = K_COSE_SIGN1_SIGNING_HEADER.to_vec();
    let mut payload = K_TAG24.to_vec();
    append_bytes_len(&mut payload, device_authentication_cbor.len());
    payload.extend_from_slice(&device_authentication_cbor);
    append_bytes_len(&mut cose_sign1_bytes, payload.len());
    cose_sign1_bytes.extend_from_slice(&payload);

    let mut hasher = sha2::Sha256::new();
    hasher.update(&cose_sign1_bytes);
    hasher.finalize().to_vec()
}
