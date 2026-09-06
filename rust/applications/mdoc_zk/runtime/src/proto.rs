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

use core_proto::SerializableField;
use runtime_algebra::{ElementOf, RuntimeField, Subfield};
use runtime_proto::{ZkProof, ZkProofGeometry};
use sha2::{Digest, Sha256};

/// Maximum bytes produced while decompressing a circuit bundle.
///
/// Legacy concatenated circuit bundles can exceed the stricter LFA2 archive
/// limit. LFA2 parsing still enforces `core_proto::archive::MAX_ARCHIVE_BYTES`
/// and the per-entry limits after decompression.
const MAX_DECOMPRESSED_CIRCUIT_BYTES: usize = 128 * 1024 * 1024;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MdocProofGeometry {
    pub geom_hash: ZkProofGeometry,
    pub geom_sig: ZkProofGeometry,
}

#[cfg(test)]
mod decompression_limits_tests {
    use super::*;

    #[test]
    fn compressed_limit_covers_zstd_worst_case_overhead() {
        assert!(
            core_proto::archive::MAX_COMPRESSED_ARCHIVE_BYTES
                >= zstd::zstd_safe::compress_bound(core_proto::archive::MAX_ARCHIVE_BYTES)
        );
    }

    #[test]
    fn streams_zstd_bombs_through_decompression_limit() {
        let mut encoder = zstd::stream::write::Encoder::new(Vec::new(), 1).unwrap();
        std::io::copy(
            &mut std::io::repeat(0).take((MAX_DECOMPRESSED_CIRCUIT_BYTES + 1) as u64),
            &mut encoder,
        )
        .unwrap();
        let compressed = encoder.finish().unwrap();
        let p256 = runtime_algebra::p256::P256Field::new();
        let gf2 = runtime_algebra::gf2_128::Gf2_128Field::new();

        let parse_error = decompress_circuits(&compressed, &[0; 32], &p256, &gf2).unwrap_err();
        assert!(
            parse_error.contains("Unsupported format header"),
            "{parse_error}"
        );

        let decoder = zstd::stream::read::Decoder::new(compressed.as_slice()).unwrap();
        let mut limited =
            DecompressionLimitReader::new(decoder, MAX_DECOMPRESSED_CIRCUIT_BYTES);
        let limit_error = std::io::copy(&mut limited, &mut std::io::sink()).unwrap_err();
        assert!(
            limit_error
                .to_string()
                .contains("Decompressed circuit archive exceeds")
        );
    }

    #[cfg(feature = "circuit-provider")]
    #[test]
    fn official_legacy_circuits_fit_decompression_limit() {
        let mut largest = 0;
        for hash in mdoc_zk_artifacts::all_circuit_hashes() {
            let compressed = mdoc_zk_artifacts::load_circuit_v1(hash);
            let decompressed = zstd::decode_all(compressed.as_slice()).unwrap();
            largest = largest.max(decompressed.len());
            assert!(
                decompressed.len() <= MAX_DECOMPRESSED_CIRCUIT_BYTES,
                "official circuit {hash} expands to {} bytes",
                decompressed.len()
            );
        }
        println!("largest official legacy circuit bundle: {largest} bytes");
    }

    #[test]
    fn rejects_compressed_archive_over_limit_before_decoding() {
        let compressed = vec![0u8; core_proto::archive::MAX_COMPRESSED_ARCHIVE_BYTES + 1];
        let p256 = runtime_algebra::p256::P256Field::new();
        let gf2 = runtime_algebra::gf2_128::Gf2_128Field::new();

        let error = decompress_circuits(&compressed, &[0; 32], &p256, &gf2).unwrap_err();
        assert!(error.contains("Compressed circuit archive exceeds"));
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MdocProof<F1: SerializableField, F2: SerializableField> {
    pub macs: [u128; 6],
    pub proof_hash: ZkProof<2, F1>,
    pub proof_sig: ZkProof<4, F2>,
}

impl<F1: RuntimeField<2> + SerializableField, F2: RuntimeField<4> + SerializableField>
    MdocProof<F1, F2>
{
    #[cfg(feature = "prover")]
    pub fn write<SF1: Subfield<E = ElementOf<F1>>, SF2: Subfield<E = ElementOf<F2>>>(
        &self,
        geom: &MdocProofGeometry,
        f1: &F1,
        sf1: &SF1,
        f2: &F2,
        sf2: &SF2,
    ) -> Result<Vec<u8>, String> {
        let mut proof_bytes = Vec::with_capacity(360_276);
        for m in &self.macs {
            proof_bytes.extend_from_slice(&m.to_le_bytes());
        }
        self.proof_hash
            .write_to_buf(&mut proof_bytes, &geom.geom_hash, f1, sf1)
            .map_err(|e| e.to_string())?;

        self.proof_sig
            .write_to_buf(&mut proof_bytes, &geom.geom_sig, f2, sf2)
            .map_err(|e| e.to_string())?;

        Ok(proof_bytes)
    }

    pub fn read<'a, SF1: Subfield<E = ElementOf<F1>>, SF2: Subfield<E = ElementOf<F2>>>(
        bytes: &'a [u8],
        geom: &MdocProofGeometry,
        f1: &F1,
        sf1: &SF1,
        f2: &F2,
        sf2: &SF2,
    ) -> Result<(&'a [u8], Self), String> {
        let mut remaining = bytes;
        if remaining.len() < 6 * 16 {
            return Err("Proof size too small for MACs".to_string());
        }
        let mut macs = [0u128; 6];
        for val in &mut macs {
            let chunk = &remaining[..16];
            *val = u128::from_le_bytes(chunk.try_into().unwrap());
            remaining = &remaining[16..];
        }

        let proof_hash = ZkProof::read(&mut remaining, &geom.geom_hash, f1, sf1)
            .map_err(|e| format!("Failed to read hash proof: {e:?}"))?;

        let proof_sig = ZkProof::read(&mut remaining, &geom.geom_sig, f2, sf2)
            .map_err(|e| format!("Failed to read signature proof: {e:?}"))?;

        Ok((
            remaining,
            Self {
                macs,
                proof_hash,
                proof_sig,
            },
        ))
    }
}

use std::io::{self, BufRead, Read};

struct DecompressionLimitReader<R> {
    inner: R,
    remaining: usize,
}

impl<R> DecompressionLimitReader<R> {
    fn new(inner: R, limit: usize) -> Self {
        Self {
            inner,
            remaining: limit,
        }
    }
}

impl<R: Read> Read for DecompressionLimitReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if buf.is_empty() {
            return Ok(0);
        }
        if self.remaining == 0 {
            let mut overflow = [0u8; 1];
            return match self.inner.read(&mut overflow)? {
                0 => Ok(0),
                _ => Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "Decompressed circuit archive exceeds {MAX_DECOMPRESSED_CIRCUIT_BYTES} byte limit"
                    ),
                )),
            };
        }

        let allowed = self.remaining.min(buf.len());
        let read = self.inner.read(&mut buf[..allowed])?;
        self.remaining -= read;
        Ok(read)
    }
}

pub fn decompress_circuits(
    compressed: &[u8],
    expected_combined_id: &[u8; 32],
    p256: &runtime_algebra::p256::P256Field,
    gf2: &runtime_algebra::gf2_128::Gf2_128Field,
) -> Result<
    (
        core_proto::circuit::Circuit<runtime_algebra::p256::P256Field>,
        core_proto::circuit::Circuit<runtime_algebra::gf2_128::Gf2_128Field>,
    ),
    String,
> {
    if compressed.len() > core_proto::archive::MAX_COMPRESSED_ARCHIVE_BYTES {
        return Err(format!(
            "Compressed circuit archive exceeds {} byte limit",
            core_proto::archive::MAX_COMPRESSED_ARCHIVE_BYTES
        ));
    }
    let zstd_decoder = zstd::stream::read::Decoder::new(compressed)
        .map_err(|e| format!("Failed to initialize zstd decoder: {e}"))?;
    let limited_decoder =
        DecompressionLimitReader::new(zstd_decoder, MAX_DECOMPRESSED_CIRCUIT_BYTES);
    let mut buf_stream = std::io::BufReader::new(limited_decoder);

    let is_lfa2 = {
        let peek = buf_stream
            .fill_buf()
            .map_err(|e| format!("Failed to read circuit header: {e}"))?;
        peek.starts_with(core_proto::archive::LFA2_MAGIC)
    };

    if is_lfa2 {
        let archive = core_proto::archive::CircuitArchive::from_stream(&mut buf_stream)?;
        if !buf_stream
            .fill_buf()
            .map_err(|e| format!("Failed to check circuit archive boundary: {e}"))?
            .is_empty()
        {
            return Err("Trailing data after circuit archive".to_string());
        }
        if &archive.combined_id != expected_combined_id {
            return Err(
                "Circuit archive ID does not match the selected ZK specification".to_string(),
            );
        }

        let sig_entry = archive
            .get("sig")
            .ok_or_else(|| "Missing 'sig' entry in circuit archive".to_string())?;
        let reader_sig = core_proto::reader::CircuitReader::new(p256, core_proto::FieldID::P256);
        let (c_sig, sig_remaining) = reader_sig.from_bytes(&sig_entry.payload, true)?;
        if !sig_remaining.is_empty() || c_sig.id != sig_entry.circuit_id {
            return Err("Signature circuit payload does not match its archive entry".to_string());
        }

        let hash_entry = archive
            .get("hash")
            .ok_or_else(|| "Missing 'hash' entry in circuit archive".to_string())?;
        let reader_hash = core_proto::reader::CircuitReader::new(gf2, core_proto::FieldID::Gf2_128);
        let (c_hash, hash_remaining) = reader_hash.from_bytes(&hash_entry.payload, true)?;
        if !hash_remaining.is_empty() || c_hash.id != hash_entry.circuit_id {
            return Err("Hash circuit payload does not match its archive entry".to_string());
        }

        Ok((c_sig, c_hash))
    } else {
        let reader1 = core_proto::reader::CircuitReader::new(p256, core_proto::FieldID::P256);
        let c_sig = reader1.from_stream(&mut buf_stream, true)?;

        let reader2 = core_proto::reader::CircuitReader::new(gf2, core_proto::FieldID::Gf2_128);
        let c_hash = reader2.from_stream(&mut buf_stream, true)?;
        if !buf_stream
            .fill_buf()
            .map_err(|e| format!("Failed to check circuit archive boundary: {e}"))?
            .is_empty()
        {
            return Err("Trailing data after legacy circuit archive".to_string());
        }

        let mut hasher = Sha256::new();
        hasher.update(c_sig.id);
        hasher.update(c_hash.id);
        let combined_id: [u8; 32] = hasher.finalize().into();
        if &combined_id != expected_combined_id {
            return Err(
                "Circuit archive ID does not match the selected ZK specification".to_string(),
            );
        }

        Ok((c_sig, c_hash))
    }
}
