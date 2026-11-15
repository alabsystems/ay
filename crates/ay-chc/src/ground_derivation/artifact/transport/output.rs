// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Chunk-polled output with a bound checked before retaining each byte chunk.
//!
//! The cap applies to serialized bytes, not the already-built typed envelope,
//! serde's internal work, allocator overhead, or process RSS. Oversize output
//! stops immediately, so diagnostics cannot report its uncomputed full length.

use super::{error, interruption_error, io_poll, ArtifactResult, GroundValidationControl, Reason};
use crate::ground_derivation::artifact::CHC_GROUND_DERIVATION_ARTIFACT_MAX_BYTES;
use serde::Serialize;
use std::io::{self, Write};

struct BoundedOutput<'c, 'p> {
    bytes: Vec<u8>,
    limit: usize,
    failure: Option<Reason>,
    control: &'c mut GroundValidationControl<'p>,
}

impl BoundedOutput<'_, '_> {
    fn reserve_chunk(&mut self, additional: usize) -> io::Result<()> {
        let Some(required) = self.bytes.len().checked_add(additional) else {
            self.failure = Some(Reason::ArtifactTooLarge);
            return Err(io::Error::other("ground evidence size overflow"));
        };
        if required > self.limit {
            self.failure = Some(Reason::ArtifactTooLarge);
            return Err(io::Error::other(
                "ground evidence output exceeds byte limit",
            ));
        }
        if required > self.bytes.capacity() {
            // Geometric growth avoids a reallocation for each serde token;
            // requested capacity never exceeds the serialized-byte ceiling.
            let target = self
                .bytes
                .capacity()
                .saturating_mul(2)
                .max(required)
                .min(self.limit);
            if self
                .bytes
                .try_reserve_exact(target - self.bytes.len())
                .is_err()
            {
                self.failure = Some(Reason::SerializationFailed);
                return Err(io::Error::other("cannot reserve ground evidence output"));
            }
        }
        Ok(())
    }
}

impl Write for BoundedOutput<'_, '_> {
    fn write(&mut self, input: &[u8]) -> io::Result<usize> {
        if self.failure.is_some() {
            return Err(io::Error::other("ground evidence output already refused"));
        }
        for chunk in input.chunks(super::POLL_BYTES) {
            io_poll(self.control)?;
            self.reserve_chunk(chunk.len())?;
            self.bytes.extend_from_slice(chunk);
        }
        Ok(input.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        io_poll(self.control)
    }
}

pub(in crate::ground_derivation::artifact) fn serialize_envelope<T: Serialize>(
    value: &T,
    control: &mut GroundValidationControl<'_>,
) -> ArtifactResult<Vec<u8>> {
    serialize_with_limit(value, CHC_GROUND_DERIVATION_ARTIFACT_MAX_BYTES, control)
}

fn serialize_with_limit<T: Serialize>(
    value: &T,
    limit: usize,
    control: &mut GroundValidationControl<'_>,
) -> ArtifactResult<Vec<u8>> {
    control.poll().map_err(interruption_error)?;
    let mut writer = BoundedOutput {
        bytes: Vec::new(),
        limit,
        failure: None,
        control,
    };
    let serialized = serde_json::to_writer(&mut writer, value);
    // Preserve sticky interruption even when serde wrapped the writer failure,
    // or when cancellation arrives just after an opaque serialization failure.
    writer.control.poll().map_err(interruption_error)?;
    if let Some(reason) = writer.failure {
        let detail = match reason {
            Reason::ArtifactTooLarge => format!("artifact exceeds maximum of {limit} bytes"),
            _ => "cannot reserve ground evidence output".to_string(),
        };
        return Err(error(reason, detail));
    }
    serialized.map_err(|failure| error(Reason::SerializationFailed, failure.to_string()))?;
    Ok(writer.bytes)
}

#[cfg(test)]
mod tests;
