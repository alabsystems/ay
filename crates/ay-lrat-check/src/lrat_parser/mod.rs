// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LRAT proof parser supporting both text and binary formats.
//!
//! ## Text format
//!
//! ```text
//! <id> <lit1> <lit2> ... 0 <hint1> <hint2> ... 0   # addition
//! <id> d <id1> <id2> ... 0                          # deletion
//! ```
//!
//! ## Binary format
//!
//! Addition: `a` byte, LEB128 id, LEB128 lits..., 0, LEB128 hints..., 0
//! Deletion: `d` byte, LEB128 ids..., 0
//!
//! Literals use the mapping: positive var v -> 2*v, negative var v -> 2*v + 1.

pub mod error;

pub use error::LratParseError;

use crate::dimacs::Literal;

/// Maximum variable index accepted in a proof literal.
///
/// The checker sizes dense per-literal arrays (assignments, marks, occurrence
/// lists) from the largest variable a proof mentions, so an unbounded index
/// in a malformed ~20-byte proof would trigger a ~100GB allocation and abort
/// the process. This matches the checker's dense allocation envelope, not the
/// syntax-only DIMACS limit.
const MAX_LRAT_VAR: u64 = crate::checker::MAX_DENSE_VARS as u64;

/// A single step in an LRAT proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LratStep {
    /// Add a derived clause: (clause_id, literals, hint_clause_ids).
    ///
    /// Hints are signed: positive IDs reference clauses for RUP propagation,
    /// negative IDs mark RAT witness boundaries. In the LRAT format, a
    /// negative hint `-C` means "clause C contains `~pivot`; the following
    /// positive hints prove the resolvent yields a conflict."
    ///
    /// Reference: drat-trim `lrat-check.c:getRATs()` (line 70) and
    /// `checkClause()` (lines 135-191).
    Add {
        id: u64,
        clause: Vec<Literal>,
        hints: Vec<i64>,
    },
    /// Delete clauses: (step_id, clause_ids_to_delete).
    Delete { ids: Vec<u64> },
}

/// Detect whether an LRAT proof is in binary format.
///
/// Binary LRAT starts with 'a' (0x61) or 'd' (0x64) byte.
/// Text LRAT starts with a digit (clause ID).
pub fn is_binary_lrat(data: &[u8]) -> bool {
    // Skip any leading whitespace
    for &b in data {
        if b == b' ' || b == b'\n' || b == b'\r' || b == b'\t' {
            continue;
        }
        return b == b'a' || b == b'd';
    }
    false
}

/// Parse a text-format LRAT proof.
pub fn parse_text_lrat(input: &str) -> Result<Vec<LratStep>, LratParseError> {
    let mut steps = Vec::new();
    let mut previous_step_id = 0;

    for line in input.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }

        let tokens: Vec<&str> = line.split_whitespace().collect();
        if tokens.is_empty() {
            continue;
        }

        // First token is always the step ID
        let step_id: u64 = tokens[0].parse().map_err(|_| LratParseError::InvalidStep {
            detail: format!("invalid step ID: {}", tokens[0]),
        })?;
        if step_id == 0 {
            return Err(LratParseError::InvalidStep {
                detail: "step ID 0 is reserved".into(),
            });
        }
        if step_id <= previous_step_id {
            return Err(LratParseError::InvalidStep {
                detail: format!("non-monotonic step ID {step_id} after {previous_step_id}"),
            });
        }
        previous_step_id = step_id;

        if tokens.len() > 1 && tokens[1] == "d" {
            // Deletion step: <id> d <id1> <id2> ... 0
            let mut ids = Vec::new();
            let mut terminated = false;
            for (index, &token) in tokens[2..].iter().enumerate() {
                let id: u64 = token.parse().map_err(|_| LratParseError::InvalidStep {
                    detail: format!("invalid deletion ID: {token}"),
                })?;
                if id == 0 {
                    terminated = true;
                    if index + 1 != tokens[2..].len() {
                        return Err(LratParseError::InvalidStep {
                            detail: "tokens after deletion terminator".into(),
                        });
                    }
                    break;
                }
                ids.push(id);
            }
            if !terminated {
                return Err(LratParseError::InvalidStep {
                    detail: "deletion step is missing its terminating 0".into(),
                });
            }
            let _ = step_id; // deletion step ID is informational
            steps.push(LratStep::Delete { ids });
        } else {
            // Addition step: <id> <lit1> ... 0 <hint1> ... 0
            let mut clause = Vec::new();
            let mut hints = Vec::new();
            let mut in_hints = false;
            let mut hints_terminated = false;

            for (index, &token) in tokens[1..].iter().enumerate() {
                if in_hints {
                    let hint: i64 = token.parse().map_err(|_| LratParseError::InvalidStep {
                        detail: format!("invalid hint ID: {token}"),
                    })?;
                    if hint == 0 {
                        hints_terminated = true;
                        if index + 1 != tokens[1..].len() {
                            return Err(LratParseError::InvalidStep {
                                detail: "tokens after hint terminator".into(),
                            });
                        }
                        break;
                    }
                    hints.push(hint);
                } else {
                    let lit: i64 = token.parse().map_err(|_| LratParseError::InvalidStep {
                        detail: format!("invalid literal: {token}"),
                    })?;
                    if lit == 0 {
                        in_hints = true;
                    } else {
                        if lit.unsigned_abs() > MAX_LRAT_VAR {
                            return Err(LratParseError::InvalidStep {
                                detail: format!(
                                    "literal {lit} exceeds the supported maximum variable \
                                     index {MAX_LRAT_VAR}; refusing to allocate"
                                ),
                            });
                        }
                        let lit32 =
                            i32::try_from(lit).map_err(|_| LratParseError::InvalidStep {
                                detail: format!("literal {lit} exceeds i32 range"),
                            })?;
                        clause.push(Literal::from_dimacs(lit32));
                    }
                }
            }
            if !in_hints {
                return Err(LratParseError::InvalidStep {
                    detail: "addition step is missing its clause terminator".into(),
                });
            }
            if !hints_terminated {
                return Err(LratParseError::InvalidStep {
                    detail: "addition step is missing its hint terminator".into(),
                });
            }

            steps.push(LratStep::Add {
                id: step_id,
                clause,
                hints,
            });
        }
    }

    Ok(steps)
}

/// Read a LEB128-style unsigned integer from the byte stream.
/// Delegates to ay-proof-common.
fn read_leb128(data: &[u8], pos: usize) -> Result<(u64, usize), LratParseError> {
    ay_proof_common::leb128::read_u64(data, pos).map_err(LratParseError::from)
}

/// Decode a binary LRAT value to its raw unsigned integer.
///
/// Binary LRAT encodes all values (literals, clause IDs, hint IDs) as
/// `2 * abs(value) + sign_bit` using LEB128. This function strips the
/// encoding to recover the unsigned value: `encoded >> 1`.
///
/// Reference: CaDiCaL `lrattracer.cpp:put_binary_id`, drat-trim `decompress.c:read_lit`.
fn decode_binary_id(encoded: u64) -> u64 {
    encoded >> 1
}

/// Decode a binary LRAT hint ID to a signed `i64`.
///
/// Binary LRAT encodes hint IDs as `2 * abs(value) + sign_bit` where
/// `sign_bit = 1` for negative (RAT witness marker). Positive hints are
/// RUP chain references; negative hints mark RAT witness clause boundaries.
///
/// Reference: drat-trim `compress.c` and `lrat-check.c:getRATs()`.
fn decode_binary_hint(encoded: u64) -> i64 {
    let magnitude = (encoded >> 1) as i64;
    if encoded & 1 == 0 {
        magnitude
    } else {
        -magnitude
    }
}

/// Decode a binary LRAT literal to a [`Literal`].
///
/// Binary encoding: positive var v -> 2*v, negative var v -> 2*v + 1.
/// Returns `Err` if the variable index exceeds i32 range.
fn decode_binary_lit(encoded: u64) -> Result<Literal, LratParseError> {
    let var_u64 = encoded >> 1;
    if var_u64 == 0 {
        return Err(LratParseError::InvalidBinary {
            position: 0,
            detail: format!(
                "invalid binary LRAT literal encoding: value {encoded} maps to variable 0"
            ),
        });
    }
    if var_u64 > MAX_LRAT_VAR {
        return Err(LratParseError::InvalidBinary {
            position: 0,
            detail: format!(
                "binary LRAT literal var {var_u64} exceeds the supported maximum \
                 variable index {MAX_LRAT_VAR}; refusing to allocate"
            ),
        });
    }
    let var = i32::try_from(var_u64).map_err(|_| LratParseError::InvalidBinary {
        position: 0,
        detail: format!("binary LRAT literal var {var_u64} exceeds i32 range"),
    })?;
    let dimacs = if encoded & 1 == 0 { var } else { -var };
    Ok(Literal::from_dimacs(dimacs))
}

/// Parse a binary-format LRAT proof.
pub fn parse_binary_lrat(data: &[u8]) -> Result<Vec<LratStep>, LratParseError> {
    let mut steps = Vec::new();
    let mut previous_addition_id = 0;
    // Match `is_binary_lrat`: a binary stream may have leading ASCII
    // whitespace before its first record marker.
    let mut pos = data
        .iter()
        .position(|byte| !byte.is_ascii_whitespace())
        .unwrap_or(data.len());

    while pos < data.len() {
        let marker = data[pos];
        pos += 1;

        match marker {
            b'a' => {
                // Addition: id, lits..., 0, hints..., 0
                let (raw_id, new_pos) = read_leb128(data, pos)?;
                pos = new_pos;
                if raw_id == 0 || raw_id & 1 != 0 {
                    return Err(LratParseError::InvalidBinary {
                        position: pos,
                        detail: format!("invalid encoded addition ID {raw_id}"),
                    });
                }
                let id = decode_binary_id(raw_id);
                if id <= previous_addition_id {
                    return Err(LratParseError::InvalidBinary {
                        position: pos,
                        detail: format!(
                            "non-monotonic addition ID {id} after {previous_addition_id}"
                        ),
                    });
                }
                previous_addition_id = id;

                let mut clause = Vec::new();
                loop {
                    let (val, new_pos) = read_leb128(data, pos)?;
                    pos = new_pos;
                    if val == 0 {
                        break;
                    }
                    clause.push(decode_binary_lit(val)?);
                }

                let mut hints = Vec::new();
                loop {
                    let (val, new_pos) = read_leb128(data, pos)?;
                    pos = new_pos;
                    if val == 0 {
                        break;
                    }
                    let hint = decode_binary_hint(val);
                    if hint == 0 {
                        return Err(LratParseError::InvalidBinary {
                            position: pos,
                            detail: format!("invalid encoded hint ID {val}"),
                        });
                    }
                    hints.push(hint);
                }

                steps.push(LratStep::Add { id, clause, hints });
            }
            b'd' => {
                // Deletion: ids..., 0
                let mut ids = Vec::new();
                loop {
                    let (val, new_pos) = read_leb128(data, pos)?;
                    pos = new_pos;
                    if val == 0 {
                        break;
                    }
                    if val & 1 != 0 {
                        return Err(LratParseError::InvalidBinary {
                            position: pos,
                            detail: format!("invalid encoded deletion ID {val}"),
                        });
                    }
                    let id = decode_binary_id(val);
                    if id == 0 {
                        return Err(LratParseError::InvalidBinary {
                            position: pos,
                            detail: "deletion ID 0 is reserved".into(),
                        });
                    }
                    ids.push(id);
                }
                steps.push(LratStep::Delete { ids });
            }
            _ => {
                return Err(LratParseError::InvalidBinary {
                    position: pos - 1,
                    detail: format!("invalid binary LRAT marker byte: 0x{marker:02x}"),
                });
            }
        }
    }

    Ok(steps)
}

/// Helper to build a literal from DIMACS notation (for tests).
#[cfg(test)]
fn lit(dimacs: i32) -> Literal {
    Literal::from_dimacs(dimacs)
}

#[cfg(test)]
mod tests;
