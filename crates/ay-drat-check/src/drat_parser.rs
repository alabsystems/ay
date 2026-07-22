// Copyright 2026 Andrew Yates
// DRAT proof parser supporting both text and binary formats.

use crate::error::DratParseError;
use crate::literal::Literal;

/// Maximum DIMACS variable accepted in a proof literal.
///
/// `DratChecker::ensure_capacity` resizes dense watch/assignment arrays to
/// the largest variable a proof mentions, so an unbounded index in a one-line
/// malformed proof (e.g. `2147483647 0`) would trigger a ~100GB allocation
/// and abort the process. The cap matches the dense checker envelope rather
/// than the much larger syntax-only DIMACS limit.
const MAX_DRAT_VAR: u32 = crate::checker::MAX_DENSE_VARS as u32;

/// A single proof step: addition or deletion of a clause.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProofStep {
    /// A RUP/RAT clause addition (plain DRAT `a`-line).
    Add(Vec<Literal>),
    /// A clause deletion (`d`-line).
    Delete(Vec<Literal>),
    /// A PR (propagation-redundant) clause addition in DPR format: the `a`-line
    /// carried a witness section (the witness begins by repeating the clause's
    /// first literal). `witness` includes that repeated pivot. The RUP/RAT DRAT
    /// checker cannot verify these — they are intended for a verified LPR checker.
    AddPr {
        clause: Vec<Literal>,
        witness: Vec<Literal>,
    },
}

/// Apply the DPR addition split rule to the literals of an `a`-record.
///
/// In DPR format the witness section begins at the SECOND occurrence of the
/// line's first literal (the pivot). If such a repeat exists the record is a PR
/// addition `AddPr { clause, witness }`; otherwise it is a plain `Add`.
fn classify_addition(lits: Vec<Literal>) -> ProofStep {
    if let Some(pivot) = lits.first().copied() {
        if let Some(rel) = lits[1..].iter().position(|&l| l == pivot) {
            let split = rel + 1;
            let witness = lits[split..].to_vec();
            let clause = lits[..split].to_vec();
            return ProofStep::AddPr { clause, witness };
        }
    }
    ProofStep::Add(lits)
}

/// Detect whether proof data is in binary or text DRAT format.
///
/// Binary DRAT uses 'a' (0x61) for additions and 'd' (0x64) for deletions,
/// followed by LEB128-encoded literals. Text DRAT uses decimal integers.
///
/// Heuristic: 'a' as first non-whitespace byte is unambiguously binary (text
/// never starts with 'a'). 'd' is ambiguous — text deletions also start with
/// 'd'. Disambiguate by checking the next byte: text has whitespace after
/// 'd', while binary normally has LEB128 data. [`parse_drat`] retries the
/// other parser for LEB128 bytes that are also ASCII whitespace.
pub fn is_binary_drat(data: &[u8]) -> bool {
    let mut i = 0;
    // Skip leading whitespace
    while i < data.len() {
        if data[i] == b' ' || data[i] == b'\n' || data[i] == b'\r' || data[i] == b'\t' {
            i += 1;
            continue;
        }
        break;
    }
    if i >= data.len() {
        return false;
    }
    // 'a' (0x61) is unambiguously binary — text never starts with 'a'
    if data[i] == 0x61 {
        return true;
    }
    // 'd' (0x64) is ambiguous. In text format, 'd' is followed by whitespace
    // (e.g., "d 1 -2 0" or "d\t1 -2 0"). In binary format, 'd' is followed
    // by LEB128 data. The auto-parser handles byte-level ambiguity by retrying.
    if data[i] == 0x64 {
        if i + 1 < data.len() {
            return !data[i + 1].is_ascii_whitespace();
        }
        // 'd' alone at end of file — treat as text (empty deletion line)
        return false;
    }
    false
}

/// Parse a text-format DRAT proof.
///
/// Format:
/// - `lit1 lit2 ... 0` — addition (RUP)
/// - `d lit1 lit2 ... 0` — deletion
pub fn parse_text_drat(data: &[u8]) -> Result<Vec<ProofStep>, DratParseError> {
    let text = std::str::from_utf8(data).map_err(|e| DratParseError::InvalidUtf8 {
        detail: e.to_string(),
    })?;
    let mut steps = Vec::new();

    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('c') {
            continue;
        }
        let (is_delete, tokens_str) = if let Some(rest) = trimmed.strip_prefix('d') {
            (true, rest.trim_start())
        } else {
            (false, trimmed)
        };
        let mut lits = Vec::new();
        let mut tokens = tokens_str.split_whitespace();
        let mut terminated = false;
        while let Some(token) = tokens.next() {
            let val: i32 = token.parse().map_err(|e| DratParseError::InvalidLiteral {
                detail: format!("bad literal '{token}': {e}"),
            })?;
            if val == 0 {
                terminated = true;
                if tokens.next().is_some() {
                    return Err(DratParseError::InvalidText {
                        detail: "tokens after clause terminator".into(),
                    });
                }
                break;
            }
            if val.unsigned_abs() > MAX_DRAT_VAR {
                return Err(DratParseError::InvalidLiteral {
                    detail: format!(
                        "literal {val} exceeds the supported maximum variable \
                         index {MAX_DRAT_VAR}; refusing to allocate"
                    ),
                });
            }
            lits.push(Literal::from_dimacs(val));
        }
        if !terminated {
            return Err(DratParseError::InvalidText {
                detail: "proof step is missing its terminating 0".into(),
            });
        }
        if is_delete {
            steps.push(ProofStep::Delete(lits));
        } else {
            steps.push(classify_addition(lits));
        }
    }
    Ok(steps)
}

/// Parse a binary-format DRAT proof.
///
/// Binary format:
/// - Byte 'a' (0x61): addition, followed by LEB128 literals, terminated by 0
/// - Byte 'd' (0x64): deletion, followed by LEB128 literals, terminated by 0
///
/// Literal encoding: positive var v → 2*(v+1), negative → 2*(v+1)+1,
/// then LEB128 variable-length encoding.
pub fn parse_binary_drat(data: &[u8]) -> Result<Vec<ProofStep>, DratParseError> {
    let mut steps = Vec::new();
    // Match `is_binary_drat`: allow leading ASCII whitespace before the first
    // binary record marker.
    let mut pos = data
        .iter()
        .position(|byte| !byte.is_ascii_whitespace())
        .unwrap_or(data.len());

    while pos < data.len() {
        let marker = data[pos];
        pos += 1;
        let is_delete = match marker {
            0x61 => false, // 'a'
            0x64 => true,  // 'd'
            _ => {
                return Err(DratParseError::InvalidBinary {
                    offset: pos - 1,
                    detail: format!("unexpected marker byte 0x{marker:02x}"),
                })
            }
        };

        let mut lits = Vec::new();
        loop {
            let (val, new_pos) = read_leb128(data, pos)?;
            pos = new_pos;
            if val == 0 {
                break;
            }
            // Decode: val = 2*(var+1) + sign, where sign=0 means positive, 1 means negative
            let var_plus_one = val >> 1;
            if var_plus_one == 0 {
                return Err(DratParseError::InvalidLiteral {
                    detail: format!("invalid literal encoding: value {val}"),
                });
            }
            let var_idx = var_plus_one - 1;
            // DIMACS variable is var_idx + 1; reject anything above MAX_DRAT_VAR.
            if var_idx >= MAX_DRAT_VAR {
                return Err(DratParseError::InvalidLiteral {
                    detail: format!(
                        "binary DRAT variable {var_idx} exceeds the supported maximum \
                         variable index {MAX_DRAT_VAR}; refusing to allocate"
                    ),
                });
            }
            let var_i32 = i32::try_from(var_idx).map_err(|_| DratParseError::InvalidLiteral {
                detail: format!("binary DRAT variable {var_idx} exceeds i32 range"),
            })?;
            let dimacs = if val & 1 == 0 {
                var_i32 + 1
            } else {
                -(var_i32 + 1)
            };
            lits.push(Literal::from_dimacs(dimacs));
        }

        if is_delete {
            steps.push(ProofStep::Delete(lits));
        } else {
            steps.push(classify_addition(lits));
        }
    }
    Ok(steps)
}

/// Read a LEB128 unsigned integer from `data` starting at `pos`.
/// Delegates to ay-proof-common.
fn read_leb128(data: &[u8], pos: usize) -> Result<(u32, usize), DratParseError> {
    ay_proof_common::leb128::read_u32(data, pos).map_err(DratParseError::from)
}

/// Parse a DRAT proof, auto-detecting text vs binary format.
pub fn parse_drat(data: &[u8]) -> Result<Vec<ProofStep>, DratParseError> {
    if is_binary_drat(data) {
        match parse_binary_drat(data) {
            Ok(steps) => Ok(steps),
            Err(binary_error) => parse_text_drat(data).or(Err(binary_error)),
        }
    } else {
        match parse_text_drat(data) {
            Ok(steps) => Ok(steps),
            // A deletion-first binary stream is ambiguous when its first
            // LEB128 byte happens to be ASCII whitespace. Retry binary before
            // reporting the text parse error.
            Err(text_error) => parse_binary_drat(data).or(Err(text_error)),
        }
    }
}

#[cfg(test)]
#[path = "drat_parser_tests.rs"]
mod tests;
