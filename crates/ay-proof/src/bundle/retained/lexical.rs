// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Admission adapted from bv_blast_solver/retained/wire/lexical.rs. That module
//! is private to the already frozen wire codec; this adds envelope depth only.
//! Serde still validates syntax. No owning parser runs before this census.

use super::*;

pub(super) const WINDOW: usize = 256;
pub(super) const OPAQUE_BYTES: usize = 16 * 1024;
const PARSER_PASSES: usize = 16;
const MAX_KEY_BYTES: usize = 15 * 6; // Includes fully escaped empty_clause_id.
                                     // serde_json 1.0.150 starts at 128 and refuses when the decremented depth is 0.
pub(super) const OUTER_DEPTH: usize = 127;

pub(super) enum Container {
    Inventory,
    Payload,
}

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

pub(super) fn inventory_cap(
    wire: &WireLimits,
    control: &mut Control<'_>,
) -> Result<usize, TransportError> {
    // Canonical {"step":u32,"payload":<raw>} plus one separator; bounds come
    // from the existing per-payload wire limit and eight-entry structural cap.
    // Noncanonical whitespace is allowed only while fitting this same bound.
    let framing = b"{\"step\":".len() + 10 + b",\"payload\":".len() + 2;
    let entry = control.add(wire.max_json_bytes, framing)?;
    let entries = control.product(entry, MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF)?;
    control.add(entries, 2)
}

pub(super) fn admit(
    bytes: &[u8],
    wire: &WireLimits,
    container: Container,
    control: &mut Control<'_>,
) -> Result<(), TransportError> {
    let (limit, maximum_depth) = match container {
        // An ordered conditional frame adds its array and role object around
        // the unchanged inner refutation's depth-four bound. Inventory adds
        // one array and one entry object; this remains a closed small ceiling.
        Container::Inventory => (inventory_cap(wire, control)?, 8),
        Container::Payload => (wire.max_json_bytes, 6),
    };
    control.cap("JSON bytes", bytes.len(), limit)?;
    let mut token = Token::Outside;
    let mut depth = 0;
    for chunk in bytes.chunks(WINDOW) {
        // One scan, then a prepaid opaque borrowed serde parse including UTF-8,
        // error positioning and bounded diagnostics. Not instruction counting.
        let work = control.product(chunk.len(), PARSER_PASSES + 1)?;
        control.charge(work, 0)?;
        for &byte in chunk {
            step(byte, &mut token, &mut depth, maximum_depth, control)?;
        }
    }
    if depth != 0 || matches!(token, Token::String { .. }) {
        return control.fail(TransportError::InvalidJson);
    }
    Ok(())
}

pub(super) fn parser_reservation(control: &mut Control<'_>) -> Result<(), TransportError> {
    // Same deliberately conservative logical reserve as the inner codec.
    // New strings are <=90 encoded bytes, new depth <=8, all custom errors are
    // fixed short text. RawValue copies no payload bytes from a slice reader.
    // Opaque allocator capacity and RSS are NOT certified by this reservation.
    control.charge(OPAQUE_BYTES, OPAQUE_BYTES)
}

fn step(
    byte: u8,
    token: &mut Token,
    depth: &mut usize,
    maximum_depth: usize,
    control: &mut Control<'_>,
) -> Result<(), TransportError> {
    match token {
        Token::String { bytes, escaped } => {
            if byte == b'"' && !*escaped {
                *token = Token::Outside;
            } else {
                *bytes += 1;
                if *bytes > MAX_KEY_BYTES {
                    return control.fail(TransportError::InvalidJson);
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
                return control.fail(TransportError::InvalidJson);
            }
            *value = next.ok_or(TransportError::InvalidJson)?;
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
            if *depth > maximum_depth {
                return control.fail(TransportError::InvalidJson);
            }
        }
        b'}' | b']' if *depth > 0 => *depth -= 1,
        b' ' | b'\n' | b'\r' | b'\t' | b':' | b',' => {}
        _ => return control.fail(TransportError::InvalidJson),
    }
    Ok(())
}

/// Allocation-free prerequisite for borrowing RawValue in the eventual outer
/// DTO. It bounds ignore_value's scratch stack but deliberately does not bound
/// legacy field strings/numbers or establish full JSON correctness.
pub(super) fn outer(bytes: &[u8], control: &mut Control<'_>) -> Result<(), TransportError> {
    let (mut quoted, mut escaped, mut depth) = (false, false, 0_usize);
    for chunk in bytes.chunks(WINDOW) {
        control.charge(chunk.len(), 0)?;
        for &byte in chunk {
            if quoted {
                if byte == b'"' && !escaped {
                    quoted = false;
                }
                escaped = byte == b'\\' && !escaped;
            } else {
                match byte {
                    b'"' => {
                        quoted = true;
                        escaped = false;
                    }
                    b'{' | b'[' => {
                        depth += 1;
                        if depth > OUTER_DEPTH {
                            return control.fail(TransportError::InvalidJson);
                        }
                    }
                    b'}' | b']' if depth > 0 => depth -= 1,
                    b'}' | b']' => return control.fail(TransportError::InvalidJson),
                    _ => {}
                }
            }
        }
    }
    if quoted || depth != 0 {
        return control.fail(TransportError::InvalidJson);
    }
    parser_reservation(control)
}
