// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! MPS format parser.
//!
//! Reference: <https://en.wikipedia.org/wiki/MPS_(format)>
//!
//! This parser accepts the free-form MPS dialect (whitespace separated,
//! ignoring the strict fixed-column layout). Sections: `NAME`, `ROWS`,
//! `COLUMNS`, `RHS`, `RANGES`, `BOUNDS`, `ENDATA`.
//!
//! Supported bound markers: `UP`, `LO`, `FX`, `FR`, `MI`, `PL`, `BV`, `LI`,
//! `UI`. Supported row kinds: `N` (objective), `L` (<=), `G` (>=), `E` (=).
//! `MARKER` lines toggle integer sections inside `COLUMNS`.

use std::collections::BTreeMap;

use crate::error::LpError;
use crate::model::{Constraint, Problem, RowKind, Sense, VarKind, Variable};

/// Parses an MPS file into a [`Problem`].
///
/// # Errors
///
/// Returns [`LpError::Parse`], [`LpError::InvalidNumber`],
/// [`LpError::UnknownIdent`], or [`LpError::InvalidInstance`] on malformed
/// input.
pub fn parse_mps(input: &str) -> Result<Problem, LpError> {
    let mut state = ParserState::default();
    let mut section = Section::None;
    let mut in_integer = false;
    let mut sense = Sense::Min;

    for (idx, raw) in input.lines().enumerate() {
        let line_no = idx + 1;
        let line = strip_comment(raw);
        if line.trim().is_empty() {
            continue;
        }

        // Section headers start at column 0 (i.e., are not indented).
        if !raw.starts_with(|c: char| c.is_whitespace()) {
            let header = line.split_whitespace().next().unwrap_or("");
            section = match header {
                "NAME" => {
                    if let Some(name) = line.split_whitespace().nth(1) {
                        state.problem.name = name.to_string();
                    }
                    Section::None
                }
                "ROWS" => Section::Rows,
                "COLUMNS" => Section::Columns,
                "RHS" => Section::Rhs,
                "RANGES" => Section::Ranges,
                "BOUNDS" => Section::Bounds,
                "OBJSENSE" => Section::ObjSense,
                "ENDATA" => break,
                other => {
                    return Err(LpError::Parse {
                        line: line_no,
                        msg: format!("unknown section header '{other}'"),
                    });
                }
            };
            continue;
        }

        let tokens: Vec<&str> = line.split_whitespace().collect();
        if tokens.is_empty() {
            continue;
        }

        match section {
            Section::None => {}
            Section::ObjSense => {
                sense = match tokens[0].to_ascii_uppercase().as_str() {
                    "MAX" | "MAXIMIZE" => Sense::Max,
                    "MIN" | "MINIMIZE" => Sense::Min,
                    other => {
                        return Err(LpError::Parse {
                            line: line_no,
                            msg: format!("invalid OBJSENSE '{other}'"),
                        });
                    }
                };
            }
            Section::Rows => parse_rows_line(&tokens, line_no, &mut state)?,
            Section::Columns => {
                parse_columns_line(&tokens, line_no, &mut state, &mut in_integer)?;
            }
            Section::Rhs => parse_rhs_line(&tokens, line_no, &mut state)?,
            Section::Ranges => parse_ranges_line(&tokens, line_no, &mut state)?,
            Section::Bounds => parse_bounds_line(&tokens, line_no, &mut state)?,
        }
    }

    state.problem.sense = sense;
    state.finalize()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Section {
    None,
    ObjSense,
    Rows,
    Columns,
    Rhs,
    Ranges,
    Bounds,
}

#[derive(Default)]
struct ParserState {
    problem: Problem,
    /// Name of the `N` objective row (first declared wins).
    obj_row: Option<String>,
    /// Row names -> index into `problem.constraints`. The objective has no entry.
    row_index: BTreeMap<String, usize>,
    /// Column names -> index into `problem.variables`.
    col_index: BTreeMap<String, usize>,
    /// RANGES values keyed by row name, applied in `finalize`.
    ranges: BTreeMap<String, f64>,
}

impl ParserState {
    fn finalize(mut self) -> Result<Problem, LpError> {
        // Apply RANGES semantics per the MPS specification. A range value `r`
        // on row `i` with rhs `b` defines the extra interval:
        //   L rows: b - |r| <= lhs <= b
        //   G rows: b <= lhs <= b + |r|
        //   E rows: b <= lhs <= b + r   (if r >= 0)
        //          b + r <= lhs <= b    (if r <  0)
        // We encode the pair as two constraints keeping the original row and
        // appending a companion. Phase 1 handles the common case where
        // downstream solvers only read `<=`/`>=`; equality rows with ranges
        // become a pair (>=, <=).
        let mut new_constraints: Vec<Constraint> = Vec::new();
        let mut replacements: Vec<(usize, Constraint)> = Vec::new();
        for (name, r) in &self.ranges {
            let idx = self
                .row_index
                .get(name)
                .copied()
                .ok_or_else(|| LpError::UnknownIdent {
                    line: 0,
                    name: name.clone(),
                })?;
            // Snapshot the fields we need so we can mutate the vector below.
            let base_name = self.problem.constraints[idx].name.clone();
            let base_kind = self.problem.constraints[idx].kind;
            let base_rhs = self.problem.constraints[idx].rhs;
            let base_coeffs = self.problem.constraints[idx].coeffs.clone();
            match base_kind {
                RowKind::Le => {
                    let lower = base_rhs - r.abs();
                    new_constraints.push(Constraint {
                        name: format!("{base_name}_rng"),
                        kind: RowKind::Ge,
                        coeffs: base_coeffs,
                        rhs: lower,
                    });
                }
                RowKind::Ge => {
                    let upper = base_rhs + r.abs();
                    new_constraints.push(Constraint {
                        name: format!("{base_name}_rng"),
                        kind: RowKind::Le,
                        coeffs: base_coeffs,
                        rhs: upper,
                    });
                }
                RowKind::Eq => {
                    let (lo, hi) = if *r >= 0.0 {
                        (base_rhs, base_rhs + r)
                    } else {
                        (base_rhs + r, base_rhs)
                    };
                    replacements.push((
                        idx,
                        Constraint {
                            name: base_name.clone(),
                            kind: RowKind::Ge,
                            coeffs: base_coeffs.clone(),
                            rhs: lo,
                        },
                    ));
                    new_constraints.push(Constraint {
                        name: format!("{base_name}_rng"),
                        kind: RowKind::Le,
                        coeffs: base_coeffs,
                        rhs: hi,
                    });
                }
            }
        }
        for (idx, c) in replacements {
            self.problem.constraints[idx] = c;
        }
        self.problem.constraints.extend(new_constraints);
        Ok(self.problem)
    }

    fn intern_var(&mut self, name: &str) -> usize {
        if let Some(&idx) = self.col_index.get(name) {
            return idx;
        }
        let idx = self.problem.variables.len();
        self.problem.variables.push(Variable::new(name));
        self.col_index.insert(name.to_string(), idx);
        idx
    }
}

fn parse_rows_line(tokens: &[&str], line: usize, state: &mut ParserState) -> Result<(), LpError> {
    if tokens.len() < 2 {
        return Err(LpError::Parse {
            line,
            msg: "expected '<kind> <name>' in ROWS".to_string(),
        });
    }
    let kind = tokens[0];
    let name = tokens[1];
    match kind {
        "N" => {
            if state.obj_row.is_none() {
                state.obj_row = Some(name.to_string());
            }
            // Additional N rows are ignored per MPS convention.
        }
        "L" | "G" | "E" => {
            if state.row_index.contains_key(name) {
                return Err(LpError::InvalidInstance(format!("duplicate row '{name}'")));
            }
            let row_kind = match kind {
                "L" => RowKind::Le,
                "G" => RowKind::Ge,
                _ => RowKind::Eq,
            };
            let idx = state.problem.constraints.len();
            state.problem.constraints.push(Constraint {
                name: name.to_string(),
                kind: row_kind,
                coeffs: Vec::new(),
                rhs: 0.0,
            });
            state.row_index.insert(name.to_string(), idx);
        }
        other => {
            return Err(LpError::Parse {
                line,
                msg: format!("unknown row kind '{other}'"),
            });
        }
    }
    Ok(())
}

fn parse_columns_line(
    tokens: &[&str],
    line: usize,
    state: &mut ParserState,
    in_integer: &mut bool,
) -> Result<(), LpError> {
    // MARKER lines are 5-token `<name> 'MARKER' 'INTORG'/'INTEND'` — the quoted
    // strings survive whitespace splitting because we don't strip quotes.
    if tokens.iter().any(|t| t.contains("MARKER")) {
        if tokens.iter().any(|t| t.contains("INTORG")) {
            *in_integer = true;
        } else if tokens.iter().any(|t| t.contains("INTEND")) {
            *in_integer = false;
        }
        return Ok(());
    }

    if tokens.len() < 3 {
        return Err(LpError::Parse {
            line,
            msg: "expected '<col> <row> <value> [<row2> <value2>]' in COLUMNS".to_string(),
        });
    }

    let col_name = tokens[0];
    let col_idx = state.intern_var(col_name);
    if *in_integer {
        state.problem.variables[col_idx].kind = VarKind::Integer;
    }

    let mut i = 1;
    while i < tokens.len() {
        if i + 1 >= tokens.len() {
            return Err(LpError::Parse {
                line,
                msg: "odd number of row/value pairs in COLUMNS".to_string(),
            });
        }
        let row = tokens[i];
        let value = parse_float(tokens[i + 1], line)?;
        if state.obj_row.as_deref() == Some(row) {
            state.problem.variables[col_idx].obj_coeff = value;
        } else {
            let row_idx = *state
                .row_index
                .get(row)
                .ok_or_else(|| LpError::UnknownIdent {
                    line,
                    name: row.to_string(),
                })?;
            state.problem.constraints[row_idx]
                .coeffs
                .push((col_idx, value));
        }
        i += 2;
    }
    Ok(())
}

fn parse_rhs_line(tokens: &[&str], line: usize, state: &mut ParserState) -> Result<(), LpError> {
    if tokens.len() < 3 {
        return Err(LpError::Parse {
            line,
            msg: "expected '<name> <row> <value>' in RHS".to_string(),
        });
    }
    // Token 0 is an unused RHS "set name"; real data starts at index 1.
    let mut i = 1;
    while i < tokens.len() {
        if i + 1 >= tokens.len() {
            return Err(LpError::Parse {
                line,
                msg: "odd number of row/value pairs in RHS".to_string(),
            });
        }
        let row = tokens[i];
        let value = parse_float(tokens[i + 1], line)?;
        if state.obj_row.as_deref() == Some(row) {
            // MPS objective RHS is negated into an additive constant.
            state.problem.obj_constant = -value;
        } else {
            let row_idx = *state
                .row_index
                .get(row)
                .ok_or_else(|| LpError::UnknownIdent {
                    line,
                    name: row.to_string(),
                })?;
            state.problem.constraints[row_idx].rhs = value;
        }
        i += 2;
    }
    Ok(())
}

fn parse_ranges_line(tokens: &[&str], line: usize, state: &mut ParserState) -> Result<(), LpError> {
    if tokens.len() < 3 {
        return Err(LpError::Parse {
            line,
            msg: "expected '<name> <row> <value>' in RANGES".to_string(),
        });
    }
    let mut i = 1;
    while i < tokens.len() {
        if i + 1 >= tokens.len() {
            return Err(LpError::Parse {
                line,
                msg: "odd number of row/value pairs in RANGES".to_string(),
            });
        }
        let row = tokens[i];
        let value = parse_float(tokens[i + 1], line)?;
        if !state.row_index.contains_key(row) {
            return Err(LpError::UnknownIdent {
                line,
                name: row.to_string(),
            });
        }
        state.ranges.insert(row.to_string(), value);
        i += 2;
    }
    Ok(())
}

fn parse_bounds_line(tokens: &[&str], line: usize, state: &mut ParserState) -> Result<(), LpError> {
    if tokens.len() < 3 {
        return Err(LpError::Parse {
            line,
            msg: "expected '<kind> <name> <col> [<value>]' in BOUNDS".to_string(),
        });
    }
    let kind = tokens[0].to_ascii_uppercase();
    // tokens[1] is the bound set name (ignored).
    let col_name = tokens[2];
    let col_idx = state
        .col_index
        .get(col_name)
        .copied()
        .ok_or_else(|| LpError::UnknownIdent {
            line,
            name: col_name.to_string(),
        })?;
    let value_token = tokens.get(3);

    let var = &mut state.problem.variables[col_idx];
    match kind.as_str() {
        "UP" => var.upper = required_value(value_token, line)?,
        "LO" => var.lower = required_value(value_token, line)?,
        "FX" => {
            let v = required_value(value_token, line)?;
            var.lower = v;
            var.upper = v;
        }
        "FR" => {
            var.lower = f64::NEG_INFINITY;
            var.upper = f64::INFINITY;
        }
        "MI" => var.lower = f64::NEG_INFINITY,
        "PL" => var.upper = f64::INFINITY,
        "BV" => {
            var.kind = VarKind::Binary;
            var.lower = 0.0;
            var.upper = 1.0;
        }
        "LI" => {
            var.kind = VarKind::Integer;
            var.lower = required_value(value_token, line)?;
        }
        "UI" => {
            var.kind = VarKind::Integer;
            var.upper = required_value(value_token, line)?;
        }
        other => {
            return Err(LpError::Parse {
                line,
                msg: format!("unknown bound kind '{other}'"),
            });
        }
    }
    Ok(())
}

fn required_value(tok: Option<&&str>, line: usize) -> Result<f64, LpError> {
    let raw = tok.ok_or_else(|| LpError::Parse {
        line,
        msg: "bound kind requires a numeric value".to_string(),
    })?;
    parse_float(raw, line)
}

fn parse_float(raw: &str, line: usize) -> Result<f64, LpError> {
    raw.parse::<f64>().map_err(|_| LpError::InvalidNumber {
        line,
        raw: raw.to_string(),
    })
}

fn strip_comment(line: &str) -> &str {
    // MPS comments are entire lines that start with `*` in column 1. A `*` in
    // the middle of a line is not a comment. The caller handles indentation
    // to distinguish headers from content.
    if line.starts_with('*') {
        ""
    } else {
        line
    }
}
