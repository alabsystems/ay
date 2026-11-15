// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Accounted chunked artifact transport, never a new request allowance.
//!
//! Logical bytes are cumulative allocation debits, not live RSS. Serde leaves,
//! arithmetic and individual allocator/destructor calls remain opaque.

use super::verification_error;
use crate::ChcProofArtifactDigest;
use crate::ChcResult;
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::io::{self, Write};

const CHUNK: usize = 4096;

#[cfg(test)]
mod tests;

pub(super) fn artifact(
    role: &str,
    bytes: &[u8],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> ChcResult<ChcProofArtifactDigest> {
    admit(progress, role.len(), role.len())?;
    Ok(ChcProofArtifactDigest {
        schema: crate::CHC_PROOF_ARTIFACT_DIGEST_SCHEMA,
        role: role.to_owned(),
        sha256: hash(bytes, progress)?,
        bytes: u64::try_from(bytes.len())
            .map_err(|_| verification_error("checked replay artifact length overflow"))?,
        path: None,
    })
}

pub(super) fn vector<T>(
    count: usize,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> ChcResult<Vec<T>> {
    let bytes = count
        .checked_mul(std::mem::size_of::<T>())
        .ok_or_else(|| verification_error("checked replay row reservation overflow"))?;
    admit(progress, count, bytes)?;
    let mut output = Vec::new();
    output
        .try_reserve_exact(count)
        .map_err(|_| verification_error("checked replay row allocation refused"))?;
    let actual = output
        .capacity()
        .checked_mul(std::mem::size_of::<T>())
        .ok_or_else(|| verification_error("checked replay row capacity overflow"))?;
    admit(progress, 0, actual.saturating_sub(bytes))?;
    Ok(output)
}

pub(super) fn admit(
    progress: &mut dyn FnMut(usize, usize) -> bool,
    work: usize,
    bytes: usize,
) -> ChcResult<()> {
    if progress(work, bytes) {
        Ok(())
    } else {
        Err(verification_error(
            "checked replay retained resource allowance exhausted or interrupted",
        ))
    }
}

pub(super) fn hash(
    bytes: &[u8],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> ChcResult<String> {
    admit(progress, 1, std::mem::size_of::<Sha256>())?;
    let mut digest = Sha256::new();
    for chunk in bytes.chunks(CHUNK) {
        admit(progress, chunk.len(), 0)?;
        digest.update(chunk);
    }
    admit(progress, 64, 64)?;
    let digest = digest.finalize();
    let mut output = String::new();
    output
        .try_reserve_exact(64)
        .map_err(|_| verification_error("checked replay digest allocation refused"))?;
    const HEX: &[u8; 16] = b"0123456789abcdef";
    for byte in digest {
        output.push(HEX[(byte >> 4) as usize] as char);
        output.push(HEX[(byte & 15) as usize] as char);
    }
    admit(progress, 0, 0)?;
    Ok(output)
}

struct ControlledWriter<'a> {
    bytes: Vec<u8>,
    progress: &'a mut dyn FnMut(usize, usize) -> bool,
}

impl Write for ControlledWriter<'_> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        for chunk in bytes.chunks(CHUNK) {
            // Charge a conservative complete replacement reservation before
            // growing the backing owner. Never refund its old capacity.
            let needed = self
                .bytes
                .len()
                .checked_add(chunk.len())
                .ok_or_else(|| io::Error::other("checked replay artifact length overflow"))?;
            let allocation = if needed > self.bytes.capacity() {
                self.bytes
                    .capacity()
                    .checked_mul(2)
                    .ok_or_else(|| io::Error::other("checked replay capacity overflow"))?
                    .max(CHUNK)
                    .max(needed)
            } else {
                0
            };
            if !(self.progress)(chunk.len(), allocation) {
                return Err(io::Error::other("checked replay artifact resource refusal"));
            }
            if allocation != 0 {
                self.bytes
                    .try_reserve_exact(allocation - self.bytes.len())
                    .map_err(|_| io::Error::other("checked replay artifact allocation refused"))?;
                if self.bytes.capacity() > allocation {
                    let extra = self.bytes.capacity() - allocation;
                    if !(self.progress)(0, extra) {
                        return Err(io::Error::other("checked replay artifact capacity refusal"));
                    }
                }
            }
            self.bytes.extend_from_slice(chunk);
        }
        if !(self.progress)(0, 0) {
            return Err(io::Error::other(
                "checked replay artifact post-write refusal",
            ));
        }
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        if (self.progress)(0, 0) {
            Ok(())
        } else {
            Err(io::Error::other("checked replay artifact flush refusal"))
        }
    }
}

pub(super) fn encode(
    value: &impl Serialize,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> ChcResult<Vec<u8>> {
    admit(progress, 1, std::mem::size_of::<Vec<u8>>())?;
    let mut writer = ControlledWriter {
        bytes: Vec::new(),
        progress,
    };
    let result = serde_json::to_writer(&mut writer, value);
    if let Err(error) = result {
        // Drop any partially encoded owner before the terminal sticky poll.
        drop(writer);
        admit(progress, 0, 0)?;
        return Err(verification_error(format!(
            "checked replay controlled artifact serialization: {error}"
        )));
    }
    let bytes = writer.bytes;
    admit(progress, 0, 0)?;
    Ok(bytes)
}
