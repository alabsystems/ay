// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Schema-specific admission, not a substitute JSON parser. All valid field
//! names fit even when every ASCII character uses a six-byte Unicode escape.
//! Serde subsequently checks escaping, delimiters, field types and all values.

use super::*;

pub(super) const MAX_KEY_BYTES: usize = 15 * 6; // empty_clause_id
pub(super) const MAX_DEPTH: usize = 4;
// Audited against serde_json 1.0.150's IoRead and fixed schema visitors: one
// reused <=90-byte decoded string scratch, bounded stack/container state, and
// one primary plus one transient error. Expected/custom text stays <128 bytes;
// even Debug-escaped string diagnostics fit a 1KiB logical text allowance.
// This deliberately larger reserve is NOT proof of opaque Vec/String capacity
// or allocator RSS. Re-audit if the parser/features or visitor text change.
pub(super) const OPAQUE_BYTES: usize = 16 * 1024;
pub(super) const WINDOW: usize = 256;
// Stream parsing, scratch copies/UTF-8 and bounded diagnostic rendering. This
// is a conservative logical reservation, not a count of CPU instructions.
pub(super) const PARSER_PASSES: usize = 16;

#[derive(Default)]
enum Token {
    #[default]
    Outside,
    String {
        bytes: usize,
        escaped: bool,
    },
    Integer {
        value: u64,
        digits: usize,
    },
}

pub(super) fn admit(bytes: &[u8], control: &mut Control<'_>) -> Result<(), WireError> {
    control.cap(
        "JSON bytes",
        bytes.len() as u128,
        control.limits.max_json_bytes as u128,
    )?;
    // Only the supplied slice is included, not hidden capacity in its caller's
    // backing allocation. No input copy is made by this API.
    control.retain(bytes.len())?;
    let mut token = Token::Outside;
    let mut depth = 0_usize;
    for chunk in bytes.chunks(WINDOW) {
        control.charge(chunk.len())?;
        for &byte in chunk {
            step(byte, &mut token, &mut depth, control)?;
        }
    }
    if depth != 0 || matches!(token, Token::String { .. }) {
        return control.fail(WireError::InvalidJson);
    }
    control.retain(OPAQUE_BYTES)?;
    // Fixed error formatting/unwinding allowance, in addition to the stream's
    // per-byte grants. Never format the serde error in our refusal path.
    control.charge(OPAQUE_BYTES)
}

fn step(
    byte: u8,
    token: &mut Token,
    depth: &mut usize,
    control: &mut Control<'_>,
) -> Result<(), WireError> {
    match token {
        Token::String { bytes, escaped } => {
            if byte == b'"' && !*escaped {
                *token = Token::Outside;
            } else {
                *bytes += 1; // Refuses at 91, so this addition cannot overflow.
                if *bytes > MAX_KEY_BYTES {
                    return control.fail(WireError::InvalidJson);
                }
                *escaped = byte == b'\\' && !*escaped;
            }
            return Ok(());
        }
        Token::Integer { value, digits } if byte.is_ascii_digit() => {
            *digits += 1;
            let next = value
                .checked_mul(10)
                .and_then(|v| v.checked_add(u64::from(byte - b'0')));
            if *digits > 20 || next.is_none() {
                return control.fail(WireError::InvalidJson);
            }
            *value = next.ok_or(WireError::InvalidJson)?;
            return Ok(());
        }
        _ => *token = Token::Outside,
    }
    match byte {
        b'0'..=b'9' => {
            *token = Token::Integer {
                value: u64::from(byte - b'0'),
                digits: 1,
            }
        }
        b'"' => {
            *token = Token::String {
                bytes: 0,
                escaped: false,
            }
        }
        b'{' | b'[' => {
            *depth += 1;
            if *depth > MAX_DEPTH {
                return control.fail(WireError::InvalidJson);
            }
        }
        b'}' | b']' if *depth > 0 => *depth -= 1,
        b' ' | b'\n' | b'\r' | b'\t' | b':' | b',' => {}
        _ => return control.fail(WireError::InvalidJson),
    }
    Ok(())
}
