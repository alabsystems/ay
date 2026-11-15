// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Cooperative byte transport for canonical ground evidence.
//!
//! These adapters poll at byte chunks and phase boundaries, not inside every
//! serde operation. In particular serde can scan an entire string for escapes
//! before writing it, and internally tagged values can perform buffered work
//! between reads. Allocation, destruction and numeric decoding also remain
//! outside this transport contract. No wall-clock bound is asserted.

use std::io::{self, Read, Write};

use serde::{de::DeserializeOwned, Serialize};
use sha2::{Digest, Sha256};

use super::{
    error, interruption_error, ChcGroundDerivationArtifactError,
    ChcGroundDerivationArtifactErrorReason as Reason, GroundValidationControl,
    CHC_GROUND_DERIVATION_ARTIFACT_MAX_NESTING_DEPTH,
    CHC_GROUND_DERIVATION_ARTIFACT_MAX_STRING_OR_TOKEN_BYTES,
};

mod output;
pub(super) use output::serialize_envelope;

#[cfg(test)]
mod tests;

const POLL_BYTES: usize = 4096;

type ArtifactResult<T> = Result<T, ChcGroundDerivationArtifactError>;

pub(super) fn validate_json_surface(
    bytes: &[u8],
    control: &mut GroundValidationControl<'_>,
) -> ArtifactResult<()> {
    control.poll().map_err(interruption_error)?;
    let mut depth = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    let mut string_bytes = 0usize;
    let mut token_bytes = 0usize;
    for chunk in bytes.chunks(POLL_BYTES) {
        control.poll().map_err(interruption_error)?;
        for &byte in chunk {
            if in_string {
                string_bytes = string_bytes.checked_add(1).ok_or_else(|| {
                    error(
                        Reason::StringOrTokenTooLarge,
                        "JSON string length overflowed usize",
                    )
                })?;
                if string_bytes > CHC_GROUND_DERIVATION_ARTIFACT_MAX_STRING_OR_TOKEN_BYTES {
                    return Err(error(
                        Reason::StringOrTokenTooLarge,
                        format!(
                            "JSON string exceeds {} encoded bytes",
                            CHC_GROUND_DERIVATION_ARTIFACT_MAX_STRING_OR_TOKEN_BYTES
                        ),
                    ));
                }
                if escaped {
                    escaped = false;
                } else if byte == b'\\' {
                    escaped = true;
                } else if byte == b'"' {
                    in_string = false;
                    string_bytes = 0;
                }
                continue;
            }
            match byte {
                b'"' => {
                    in_string = true;
                    string_bytes = 0;
                    token_bytes = 0;
                }
                b'{' | b'[' => {
                    depth = depth.checked_add(1).ok_or_else(|| {
                        error(
                            Reason::NestingTooDeep,
                            "JSON nesting depth overflowed usize",
                        )
                    })?;
                    if depth > CHC_GROUND_DERIVATION_ARTIFACT_MAX_NESTING_DEPTH {
                        return Err(error(
                            Reason::NestingTooDeep,
                            format!(
                                "JSON nesting exceeds {}",
                                CHC_GROUND_DERIVATION_ARTIFACT_MAX_NESTING_DEPTH
                            ),
                        ));
                    }
                    token_bytes = 0;
                }
                b'}' | b']' | b',' | b':' | b' ' | b'\t' | b'\r' | b'\n' => {
                    if matches!(byte, b'}' | b']') {
                        depth = depth.saturating_sub(1);
                    }
                    token_bytes = 0;
                }
                _ => {
                    token_bytes = token_bytes.checked_add(1).ok_or_else(|| {
                        error(
                            Reason::StringOrTokenTooLarge,
                            "JSON scalar token length overflowed usize",
                        )
                    })?;
                    if token_bytes > CHC_GROUND_DERIVATION_ARTIFACT_MAX_STRING_OR_TOKEN_BYTES {
                        return Err(error(
                            Reason::StringOrTokenTooLarge,
                            format!(
                                "JSON scalar token exceeds {} bytes",
                                CHC_GROUND_DERIVATION_ARTIFACT_MAX_STRING_OR_TOKEN_BYTES
                            ),
                        ));
                    }
                }
            }
        }
    }
    control.poll().map_err(interruption_error)
}

fn io_poll(control: &mut GroundValidationControl<'_>) -> io::Result<()> {
    control.poll().map_err(|_| {
        // `io::Bytes` and `write_all` may retry ErrorKind::Interrupted. A
        // sticky refusal must instead unwind serde through a non-retryable
        // error; the owner maps the control state to our typed interruption.
        io::Error::other("ground evidence transport cancelled")
    })
}

struct ProgressReader<'b, 'c, 'p> {
    bytes: &'b [u8],
    position: usize,
    until_poll: usize,
    control: &'c mut GroundValidationControl<'p>,
}

impl Read for ProgressReader<'_, '_, '_> {
    fn read(&mut self, output: &mut [u8]) -> io::Result<usize> {
        if self.control.is_stopped() {
            return io_poll(self.control).map(|()| 0);
        }
        if output.is_empty() {
            return Ok(0);
        }
        if self.position == self.bytes.len() {
            io_poll(self.control)?;
            return Ok(0);
        }
        if self.until_poll == 0 {
            io_poll(self.control)?;
            self.until_poll = POLL_BYTES;
        }
        let count = output
            .len()
            .min(self.bytes.len() - self.position)
            .min(self.until_poll);
        output[..count].copy_from_slice(&self.bytes[self.position..self.position + count]);
        self.position += count;
        self.until_poll -= count;
        Ok(count)
    }
}

pub(super) fn parse_envelope<T: DeserializeOwned>(
    bytes: &[u8],
    control: &mut GroundValidationControl<'_>,
) -> ArtifactResult<T> {
    control.poll().map_err(interruption_error)?;
    let parsed = serde_json::from_reader(ProgressReader {
        bytes,
        position: 0,
        until_poll: 0,
        control,
    });
    // This also maps our non-retryable serde I/O error to Interrupted before
    // it could be mistaken for malformed input. `from_reader` checks EOF.
    control.poll().map_err(interruption_error)?;
    parsed.map_err(|parse_error| error(Reason::MalformedEnvelope, parse_error.to_string()))
}

struct CanonicalComparisonWriter<'b, 'c, 'p> {
    expected: &'b [u8],
    position: usize,
    mismatch: bool,
    control: &'c mut GroundValidationControl<'p>,
}

impl Write for CanonicalComparisonWriter<'_, '_, '_> {
    fn write(&mut self, input: &[u8]) -> io::Result<usize> {
        for chunk in input.chunks(POLL_BYTES) {
            io_poll(self.control)?;
            let end = self.position.checked_add(chunk.len());
            if end.and_then(|end| self.expected.get(self.position..end)) != Some(chunk) {
                self.mismatch = true;
                return Err(io::Error::other("ground evidence canonical bytes differ"));
            }
            // A successful slice lookup above bounds this addition by the
            // expected input length.
            self.position += chunk.len();
        }
        Ok(input.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        io_poll(self.control)
    }
}

pub(super) fn check_canonical_json<T: Serialize>(
    value: &T,
    expected: &[u8],
    mismatch_detail: &'static str,
    control: &mut GroundValidationControl<'_>,
) -> ArtifactResult<()> {
    control.poll().map_err(interruption_error)?;
    let (serialized, mismatch, complete) = {
        let mut writer = CanonicalComparisonWriter {
            expected,
            position: 0,
            mismatch: false,
            control,
        };
        let serialized = serde_json::to_writer(&mut writer, value);
        (
            serialized,
            writer.mismatch,
            writer.position == expected.len(),
        )
    };
    control.poll().map_err(interruption_error)?;
    if mismatch {
        return Err(error(Reason::NonCanonicalEnvelope, mismatch_detail));
    }
    serialized.map_err(|serialization_error| {
        error(Reason::SerializationFailed, serialization_error.to_string())
    })?;
    if !complete {
        return Err(error(Reason::NonCanonicalEnvelope, mismatch_detail));
    }
    Ok(())
}

pub(super) fn sha256_hex(
    bytes: &[u8],
    control: &mut GroundValidationControl<'_>,
) -> ArtifactResult<String> {
    control.poll().map_err(interruption_error)?;
    let mut digest = Sha256::new();
    for chunk in bytes.chunks(POLL_BYTES) {
        control.poll().map_err(interruption_error)?;
        digest.update(chunk);
    }
    let digest = digest.finalize();
    let mut output = String::with_capacity(64);
    for byte in digest {
        use std::fmt::Write as _;
        let _ = write!(output, "{byte:02x}");
    }
    control.poll().map_err(interruption_error)?;
    Ok(output)
}
