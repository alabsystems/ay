// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QDIMACS parser
//!
//! Parses QBF formulas in QDIMACS format (standard format for QBF benchmarks).
//! Delegates tokenization to [`ay_sat::dimacs_core`] and handles quantifier
//! blocks (`e`/`a`) locally.
//!
//! ## Format
//! ```text
//! c comment line
//! p cnf <num_vars> <num_clauses>
//! e <var1> <var2> ... 0    // existential block
//! a <var1> <var2> ... 0    // universal block
//! <lit1> <lit2> ... 0      // clause
//! ...
//! ```
//!
//! Variables are 1-indexed positive integers.
//! Literals are signed integers (positive = true, negative = false).
//! Each line ends with 0.

use std::collections::HashSet;

use crate::formula::{QbfFormula, Quantifier, QuantifierBlock, MAX_QBF_VARS};
use ay_sat::dimacs_core::{self, DimacsCoreError, DimacsRecord};
use ay_sat::{Literal, Variable};

/// Error type for QDIMACS parsing
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QdimacsError {
    /// Missing problem line (p cnf ...)
    MissingProblemLine,
    /// Invalid problem line format
    InvalidProblemLine(String),
    /// Invalid quantifier line
    InvalidQuantifierLine(String),
    /// Invalid clause format
    InvalidClause(String),
    /// Variable out of range
    VariableOutOfRange(u32, usize),
}

impl std::fmt::Display for QdimacsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingProblemLine => write!(f, "missing problem line"),
            Self::InvalidProblemLine(s) => write!(f, "invalid problem line: {s}"),
            Self::InvalidQuantifierLine(s) => write!(f, "invalid quantifier line: {s}"),
            Self::InvalidClause(s) => write!(f, "invalid clause: {s}"),
            Self::VariableOutOfRange(v, n) => {
                write!(f, "variable {v} out of range (max {n})")
            }
        }
    }
}

impl std::error::Error for QdimacsError {}

impl From<DimacsCoreError> for QdimacsError {
    fn from(e: DimacsCoreError) -> Self {
        match e {
            DimacsCoreError::MissingHeader => Self::MissingProblemLine,
            DimacsCoreError::InvalidHeader { line_content, .. } => {
                Self::InvalidProblemLine(line_content)
            }
            DimacsCoreError::InvalidLiteral { token, .. } => Self::InvalidClause(token),
            DimacsCoreError::IoError(s) => Self::InvalidClause(format!("I/O error: {s}")),
            DimacsCoreError::VariableOutOfRange { var, max, .. } => {
                Self::VariableOutOfRange(var, max as usize)
            }
            _ => Self::InvalidClause(format!("{e}")),
        }
    }
}

/// Parse a QDIMACS string into a QBF formula
pub fn parse_qdimacs(input: &str) -> Result<QbfFormula, QdimacsError> {
    let (header, records) = dimacs_core::parse_dimacs_records_str(input)?;
    // Declared count: used only for the quantifier-prefix validity check below,
    // never to size an allocation.
    let num_vars = header.num_vars;

    let mut prefix = Vec::new();
    let mut quantified_variables = HashSet::new();
    let mut matrix_started = false;
    // Cap the speculative clause pre-allocation from the untrusted declared count
    // (the vector grows to fit real clauses anyway).
    let mut clauses = Vec::with_capacity(header.num_clauses.min(1 << 20));
    // Content-driven variable count: the highest 1-indexed variable that actually
    // appears in the prefix or matrix. The QBF solver's per-variable arrays are
    // sized by this, not by the (untrusted) declared header.
    let mut actual_num_vars: u32 = 0;
    for record in records {
        match record {
            DimacsRecord::Tagged {
                tag: tag @ ('e' | 'a'),
                values,
            } => {
                if matrix_started {
                    return Err(QdimacsError::InvalidQuantifierLine(
                        "quantifier block appears after the matrix has started".to_string(),
                    ));
                }
                let quantifier = if tag == 'e' {
                    Quantifier::Exists
                } else {
                    Quantifier::Forall
                };

                let mut variables = Vec::new();
                for &val in &values {
                    if val <= 0 {
                        return Err(QdimacsError::InvalidQuantifierLine(format!(
                            "non-positive variable {val} in quantifier block"
                        )));
                    }
                    let var = val as u32;
                    if var as usize > num_vars {
                        return Err(QdimacsError::VariableOutOfRange(var, num_vars));
                    }
                    if !quantified_variables.insert(var) {
                        return Err(QdimacsError::InvalidQuantifierLine(format!(
                            "variable {var} occurs in more than one quantifier block"
                        )));
                    }
                    actual_num_vars = actual_num_vars.max(var);
                    variables.push(var);
                }

                if !variables.is_empty() {
                    prefix.push(QuantifierBlock::new(quantifier, variables));
                }
            }
            DimacsRecord::Clause(raw) => {
                matrix_started = true;
                // Validate the actual dense variable range before constructing
                // `ay_sat::Literal`s. In particular, `i32::MIN.unsigned_abs()`
                // is 2^31; using that as QBF's 1-based internal variable would
                // otherwise trip Literal's encoding assertion before the
                // post-parse allocation backstop could return a typed error.
                for &literal in &raw {
                    let variable = literal.unsigned_abs();
                    if variable as usize > MAX_QBF_VARS {
                        return Err(QdimacsError::InvalidClause(format!(
                            "variable {variable} exceeds the maximum supported {MAX_QBF_VARS}; refusing to allocate"
                        )));
                    }
                    actual_num_vars = actual_num_vars.max(variable);
                }
                // QBF uses 1-indexed variables directly (no -1 adjustment)
                let clause: Vec<Literal> = raw
                    .iter()
                    .map(|&l| {
                        let var = l.unsigned_abs();
                        if l > 0 {
                            Literal::positive(Variable::new(var))
                        } else {
                            Literal::negative(Variable::new(var))
                        }
                    })
                    .collect();
                // Preserve the empty clause: in CNF it is an immediate
                // contradiction, not an ignorable blank record. Dropping it
                // turns `p cnf 0 1; 0` from UNSAT into SAT.
                clauses.push(clause);
            }
            DimacsRecord::Tagged { tag, .. } => {
                return Err(QdimacsError::InvalidQuantifierLine(format!(
                    "unexpected tagged line '{tag}' in QDIMACS input"
                )));
            }
            _ => {
                return Err(QdimacsError::InvalidClause(
                    "unexpected record type in QDIMACS input".to_string(),
                ));
            }
        }
    }

    // Backstop on the *actual* variable count (dense numbering => O(max index)
    // per-variable arrays): refuse a pathological explicit index rather than
    // allocating hundreds of GB.
    if actual_num_vars as usize > MAX_QBF_VARS {
        return Err(QdimacsError::InvalidClause(format!(
            "variable {actual_num_vars} exceeds the maximum supported {MAX_QBF_VARS}; \
             refusing to allocate"
        )));
    }
    Ok(QbfFormula::new(actual_num_vars as usize, prefix, clauses))
}

#[cfg(test)]
#[path = "parser_tests.rs"]
mod tests;
