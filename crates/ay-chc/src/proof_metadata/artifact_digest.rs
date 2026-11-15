// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private artifact construction hashes the actual owned bytes under control.

use super::{normalization, ChcProofArtifactDigest, ChcProofRunArtifact, IdentityHashInterrupted};

impl ChcProofRunArtifact {
    pub(crate) fn new_with_progress(
        schema: &'static str,
        role: &'static str,
        bytes: Vec<u8>,
        progress: &mut dyn FnMut() -> bool,
    ) -> Result<Self, IdentityHashInterrupted> {
        let sha256 = normalization::bytes_hash_with_progress(&bytes, progress)?;
        let artifact = Self {
            schema,
            role,
            digest: ChcProofArtifactDigest::from_sha256(role, sha256, bytes.len() as u64),
            bytes,
        };
        if !progress() {
            return Err(IdentityHashInterrupted);
        }
        Ok(artifact)
    }
}

#[cfg(test)]
mod tests;
