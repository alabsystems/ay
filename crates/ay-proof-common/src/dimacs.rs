// Copyright 2026 Andrew Yates
// DIMACS CNF parser shared by ay-drat-check and ay-lrat-check.

use crate::error::ParseError;
use crate::literal::Literal;
use std::io::{BufRead, BufReader, Read};

/// Parsed CNF formula.
#[derive(Debug)]
pub struct CnfFormula {
    pub num_vars: usize,
    pub clauses: Vec<Vec<Literal>>,
}

/// Parsed CNF formula with sequential 1-indexed clause IDs.
///
/// LRAT proof checking requires clause IDs to map proof hints back to specific
/// clauses. IDs are auto-generated (1-indexed, sequential).
#[derive(Debug)]
pub struct CnfFormulaWithIds {
    pub num_vars: usize,
    pub clauses: Vec<(u64, Vec<Literal>)>,
}

/// Shared DIMACS CNF parsing core.
///
/// Parses the standard DIMACS CNF format and calls `emit_clause` for each
/// complete clause. Returns the declared variable count.
/// Backstop on the *actual* number of distinct variables (the highest variable
/// index that appears). The proof checkers size dense per-variable arrays from
/// the returned count, and dense numbering makes those arrays O(max index), so a
/// pathological explicitly-referenced index is refused rather than allocating
/// hundreds of GB. The declared `p cnf` count is NOT trusted for sizing.
/// Mirrors `ay_sat::dimacs_core::MAX_DIMACS_VARS`.
const MAX_CNF_VARS: usize = 1 << 28;

/// Returns the *content-driven* variable count: one past the maximum variable
/// index that actually appears, independent of the declared header.
fn parse_cnf_core(
    reader: impl Read,
    mut emit_clause: impl FnMut(Vec<Literal>),
) -> Result<usize, ParseError> {
    let reader = BufReader::new(reader);
    let mut declared_num_vars = 0;
    let mut actual_num_vars = 0;
    let mut header_seen = false;
    let mut current_clause: Vec<Literal> = Vec::new();

    for line in reader.lines() {
        let line = line.map_err(ParseError::from)?;
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('c') {
            continue;
        }
        if trimmed.starts_with("p ") {
            if header_seen {
                return Err(ParseError::InvalidHeader {
                    detail: "duplicate problem line".into(),
                });
            }
            let parts: Vec<&str> = trimmed.split_whitespace().collect();
            if parts.len() < 4 || parts[1] != "cnf" {
                return Err(ParseError::InvalidHeader {
                    detail: format!("invalid problem line: {trimmed}"),
                });
            }
            // Parsed for validity only; never used to size an allocation.
            declared_num_vars =
                parts[2]
                    .parse::<usize>()
                    .map_err(|e| ParseError::InvalidHeader {
                        detail: format!("bad variable count: {e}"),
                    })?;
            // Validate clause count is a number but don't enforce it — many
            // DIMACS files in the wild have inaccurate headers.
            let _expected_clauses: usize =
                parts[3].parse().map_err(|e| ParseError::InvalidHeader {
                    detail: format!("bad clause count: {e}"),
                })?;
            header_seen = true;
            continue;
        }
        if !header_seen {
            return Err(ParseError::InvalidHeader {
                detail: "clause data before problem line".into(),
            });
        }
        for token in trimmed.split_whitespace() {
            let val: i32 = token.parse().map_err(|e| ParseError::InvalidLiteral {
                detail: format!("bad literal '{token}': {e}"),
            })?;
            if val == 0 {
                emit_clause(std::mem::take(&mut current_clause));
            } else {
                let var = val.unsigned_abs() as usize;
                if var > declared_num_vars {
                    return Err(ParseError::InvalidLiteral {
                        detail: format!(
                            "literal {val} exceeds declared variable count {declared_num_vars}"
                        ),
                    });
                }
                // Content-driven: size by the variables that actually appear.
                actual_num_vars = actual_num_vars.max(var);
                if actual_num_vars > MAX_CNF_VARS {
                    return Err(ParseError::InvalidLiteral {
                        detail: format!(
                            "variable {actual_num_vars} exceeds the maximum supported \
                             {MAX_CNF_VARS}; refusing to allocate"
                        ),
                    });
                }
                current_clause.push(Literal::from_dimacs(val));
            }
        }
    }
    // Handle trailing clause without terminating 0.
    if !current_clause.is_empty() {
        emit_clause(current_clause);
    }
    Ok(actual_num_vars)
}

/// Parse a DIMACS CNF file from a reader.
///
/// Supports standard DIMACS format:
/// - Lines starting with `c` are comments
/// - `p cnf <vars> <clauses>` declares the problem
/// - Clause lines are space-separated signed integers terminated by 0
pub fn parse_cnf(reader: impl Read) -> Result<CnfFormula, ParseError> {
    let mut clauses = Vec::new();
    let num_vars = parse_cnf_core(reader, |clause| clauses.push(clause))?;
    Ok(CnfFormula { num_vars, clauses })
}

/// Parse a DIMACS CNF file, returning clauses with sequential 1-indexed IDs.
///
/// Same format as [`parse_cnf`] but each clause is tagged with an auto-generated
/// clause ID (1, 2, 3, ...). Required by LRAT proof checkers which map proof
/// hint IDs back to specific original clauses.
pub fn parse_cnf_with_ids(reader: impl Read) -> Result<CnfFormulaWithIds, ParseError> {
    let mut clauses = Vec::new();
    let mut clause_id: u64 = 1;
    let num_vars = parse_cnf_core(reader, |clause| {
        clauses.push((clause_id, clause));
        clause_id += 1;
    })?;
    Ok(CnfFormulaWithIds { num_vars, clauses })
}

#[cfg(test)]
#[path = "dimacs_tests.rs"]
mod tests;
