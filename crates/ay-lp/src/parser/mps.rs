// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The MPS reader: one exact reading, the one the MIP competitions' referee
//! makes, or a refusal.
//!
//! Every number is kept as the rational its decimal text denotes
//! ([`crate::exact::decimal`]); nothing passes through `f64`. The referee is
//! the organizers' MIPLIB 2017 solution checker (`miplib2017-checker`,
//! `mpsinput.cpp`), which reads the file exactly with GMP rationals. Where
//! readers in common use (CPLEX, Gurobi, SCIP, HiGHS) and the checker give a
//! file different models, the file is refused with a line-numbered error:
//! no verdict is ever printed from a guessed reading.
//!
//! # The reading
//!
//! - Lines: `*` in column 1 is a comment; a line starting with a blank or tab
//!   is a data line, any other a section header. Fields are separated by
//!   blanks, tabs and `\r` (free format). A data line on which the checker's
//!   fixed-column layout, `$` comment or five-field limit would read other
//!   fields is refused ([`fields`]); so is a line longer than 1022 bytes, a
//!   name longer than 255 bytes and a NUL byte (the checker's buffers).
//! - Sections, in this order: `NAME` (first), `OBJSENSE` (`MIN`, `MAX`,
//!   `MINIMIZE` or `MAXIMIZE`, on the header line or the next data line),
//!   `OBJNAME`, `ROWS`, `COLUMNS`, `RHS`, `RANGES`, `BOUNDS`, `ENDATA`. Each
//!   at most once, `ROWS` and `ENDATA` required (a file without `ENDATA`
//!   may be cut off). `USERCUTS`, `LAZYCONS`, `SOS`, `INDICATORS`, quadratic
//!   and other sections are refused: they would have to be modelled.
//! - `ROWS`: `<N|L|G|E> <name>`, names unique among all rows. The objective is
//!   the `N` row `OBJNAME` names, else the first `N` row; other `N` rows are
//!   free rows whose `COLUMNS` entries are ignored.
//! - `COLUMNS`: `<column> <row> <value> [<row> <value>]`, or exactly
//!   `<name> 'MARKER' 'INTORG'` / `'INTEND'`. A column's records are
//!   contiguous. Repeated `(column, constraint row)` entries are summed (the
//!   checker adds both terms to the activity); a repeated objective entry is
//!   refused (the checker keeps the last, others sum). An integer column of a
//!   marker section starts as the checker's binary: bounds `[0, 1]`.
//! - `RHS` and `RANGES`: `[<set>] <row> <value> [<row> <value>]` (an odd
//!   field count names the set). One set name per section (the checker reads
//!   only the first set). An `RHS` entry of the objective row is the negated
//!   objective constant; `RHS` or `RANGES` of a free row, `RANGES` of the
//!   objective and a second entry for the same row are refused. With `R` the
//!   range of a row with right-hand side `b` (default 0): `G` is
//!   `[b, b + |R|]`, `L` is `[b - |R|, b]`, `E` is `[b, b + R]` for `R > 0`
//!   and `[b + R, b]` otherwise.
//! - `BOUNDS`: `<UP|LO|FX|LI|UI> [<set>] <column> <value>` and
//!   `<FR|MI|PL|BV> [<set>] <column> [<value>]` (the value is ignored), one
//!   set name, applied in file order exactly as the checker does: on a column
//!   whose type is binary, any entry but `UP 1` first makes it a general
//!   integer with upper bound `+inf`; then `LO`/`LI` set the lower bound,
//!   `UP`/`UI` the upper, `FX` both, `FR` frees both, `MI` the lower, `PL` the
//!   upper; `LI`/`UI` make the column integer; `BV` makes it binary and
//!   intersects its bounds with `[0, 1]`. Refused: `SC`, an unknown kind, and
//!   an `UP`/`UI` below 0 on a column whose final lower bound is 0 (the
//!   checker keeps 0, CPLEX, SCIP and HiGHS take `-inf`).
//! - Every number, and every sum or range side derived from them, must be in
//!   the range an `f64` can approximate ([`crate::exact::decimal`]).

mod fields;

use std::collections::HashMap;

use num_rational::BigRational;
use num_traits::{Signed, Zero};

use crate::error::LpError;
use crate::exact::decimal::{in_f64_range, parse_decimal};
use crate::exact::{ExactColumn, ExactProblem, ExactRow};
use crate::model::{Problem, Sense, VarKind};
use fields::CheckerFields;

/// The longest line the checker's 1024-byte `fgets` buffer reads whole.
const MAX_LINE_LEN: usize = 1022;
/// The longest name the checker's 256-byte name buffers hold.
const MAX_NAME_LEN: usize = 255;

/// Parses an MPS file into a floating-point [`Problem`]: the
/// [`ExactProblem::to_problem`] copy of [`parse_mps_exact`]'s reading.
///
/// # Errors
///
/// As [`parse_mps_exact`].
pub fn parse_mps(input: &str) -> Result<Problem, LpError> {
    Ok(parse_mps_exact(input)?.to_problem())
}

/// Reads an MPS file exactly (module docs).
///
/// # Errors
///
/// [`LpError::Parse`] with the line of the first malformed or refused
/// construct.
pub fn parse_mps_exact(input: &str) -> Result<ExactProblem, LpError> {
    let mut reader = Reader::default();
    let mut pieces = input.split('\n').peekable();
    let mut line = 0;
    while let Some(raw) = pieces.next() {
        let terminated = pieces.peek().is_some();
        if !terminated && raw.is_empty() {
            break;
        }
        line += 1;
        if reader.section == Section::End {
            break;
        }
        reader.line(raw, terminated, line)?;
    }
    reader.finish(line)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
enum Section {
    #[default]
    Start,
    Name,
    ObjSense,
    ObjName,
    Rows,
    Columns,
    Rhs,
    Ranges,
    Bounds,
    End,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RowType {
    N,
    L,
    G,
    E,
}

struct RowDecl {
    name: String,
    kind: RowType,
    coeffs: Vec<(usize, BigRational)>,
    rhs: Option<BigRational>,
    range: Option<(BigRational, usize)>,
}

struct ColBuild {
    name: String,
    kind: VarKind,
    lower: Option<BigRational>,
    upper: Option<BigRational>,
    objective: Option<BigRational>,
    negative_up_line: Option<usize>,
}

#[derive(Default)]
struct Reader {
    section: Section,
    fields: CheckerFields,
    name: String,
    sense: Option<Sense>,
    objname: Option<String>,
    rows: Vec<RowDecl>,
    row_of: HashMap<String, usize>,
    objective: Option<usize>,
    columns: Vec<ColBuild>,
    col_of: HashMap<String, usize>,
    current_col: Option<usize>,
    in_integer: bool,
    offset: Option<BigRational>,
    rhs_set: Option<String>,
    ranges_set: Option<String>,
    bounds_set: Option<String>,
    /// Parsed numbers by their text: MPS files repeat a few values.
    numbers: HashMap<String, BigRational>,
}

fn refuse(line: usize, msg: impl Into<String>) -> LpError {
    LpError::Parse {
        line,
        msg: msg.into(),
    }
}

fn number(text: &str, line: usize) -> Result<BigRational, LpError> {
    parse_decimal(text).ok_or_else(|| LpError::InvalidNumber {
        line,
        raw: text.to_string(),
    })
}

/// Most distinct number texts [`Reader::number`] remembers.
const NUMBER_CACHE_LIMIT: usize = 1 << 16;

/// Splits an `RHS`/`RANGES` line into its set name and `(row, value)` pairs.
fn set_and_pairs<'t>(
    tokens: &[&'t str],
    unnamed: &'t str,
    section: &str,
    line: usize,
) -> Result<(&'t str, Vec<(&'t str, &'t str)>), LpError> {
    let (set, body) = match tokens.len() {
        2 | 4 => (unnamed, tokens),
        3 | 5 => (tokens[0], &tokens[1..]),
        _ => {
            return Err(refuse(
                line,
                format!("a {section} line is '[<set>] <row> <value> [<row> <value>]'"),
            ))
        }
    };
    Ok((set, body.chunks(2).map(|p| (p[0], p[1])).collect()))
}

/// Records the section's set name, refusing a second one.
fn one_set(
    slot: &mut Option<String>,
    set: &str,
    section: &str,
    line: usize,
) -> Result<(), LpError> {
    match slot {
        None => {
            *slot = Some(set.to_string());
            Ok(())
        }
        Some(first) if first == set => Ok(()),
        Some(first) => Err(refuse(
            line,
            format!(
                "second {section} set '{set}' after '{first}': the checker reads only the first, \
                 other readers all"
            ),
        )),
    }
}

fn parse_sense(word: &str, line: usize) -> Result<Sense, LpError> {
    match word {
        "MIN" | "MINIMIZE" => Ok(Sense::Min),
        "MAX" | "MAXIMIZE" => Ok(Sense::Max),
        other => Err(refuse(line, format!("invalid OBJSENSE '{other}'"))),
    }
}

impl Reader {
    /// [`number`], remembering up to [`NUMBER_CACHE_LIMIT`] texts.
    fn number(&mut self, text: &str, line: usize) -> Result<BigRational, LpError> {
        if let Some(value) = self.numbers.get(text) {
            return Ok(value.clone());
        }
        let value = number(text, line)?;
        if self.numbers.len() < NUMBER_CACHE_LIMIT {
            self.numbers.insert(text.to_string(), value.clone());
        }
        Ok(value)
    }

    fn line(&mut self, raw: &str, terminated: bool, line: usize) -> Result<(), LpError> {
        let bytes = raw.as_bytes();
        if bytes.contains(&0) {
            return Err(refuse(line, "NUL byte"));
        }
        if bytes.len() > MAX_LINE_LEN {
            return Err(refuse(
                line,
                format!("line longer than {MAX_LINE_LEN} bytes (the checker splits it)"),
            ));
        }
        if bytes.first() == Some(&b'*') {
            return Ok(());
        }
        let tokens: Vec<&str> = raw
            .split([' ', '\t', '\r'])
            .filter(|t| !t.is_empty())
            .collect();
        if bytes
            .first()
            .is_some_and(|b| !matches!(b, b' ' | b'\t' | b'\r'))
        {
            return self.header(&tokens, line);
        }
        let data_section = matches!(
            self.section,
            Section::Columns | Section::Rhs | Section::Ranges | Section::Bounds
        );
        let checker = if self.fields.settled() && !bytes.contains(&b'$') {
            None
        } else {
            Some(self.fields.read(bytes, terminated, data_section))
        };
        if tokens.is_empty() {
            return Ok(());
        }
        if tokens.len() > 5 {
            return Err(refuse(
                line,
                "more than five fields (the checker reads five)",
            ));
        }
        let differs = checker.is_some_and(|checker| {
            checker.len() != tokens.len()
                || checker.iter().zip(&tokens).any(|(c, t)| c != t.as_bytes())
        });
        if differs {
            return Err(refuse(
                line,
                "the MIPLIB checker reads this line's fields differently (a name with blanks \
                 in the fixed-column layout, or a '$' comment)",
            ));
        }
        if let Some(long) = tokens.iter().find(|t| t.len() > MAX_NAME_LEN) {
            return Err(refuse(
                line,
                format!("field of {} bytes (the checker holds 255)", long.len()),
            ));
        }
        match self.section {
            Section::Start => Err(refuse(line, "an MPS file begins with a NAME line")),
            Section::Name => Err(refuse(line, "data line before the first section")),
            Section::ObjSense => {
                if self.sense.is_some() || tokens.len() != 1 {
                    return Err(refuse(line, "OBJSENSE takes one direction"));
                }
                self.sense = Some(parse_sense(tokens[0], line)?);
                Ok(())
            }
            Section::ObjName => {
                if self.objname.is_some() || tokens.len() != 1 {
                    return Err(refuse(line, "OBJNAME takes one row name"));
                }
                self.objname = Some(tokens[0].to_string());
                Ok(())
            }
            Section::Rows => self.row(&tokens, line),
            Section::Columns => self.column(&tokens, line),
            Section::Rhs => self.rhs(&tokens, line),
            Section::Ranges => self.range(&tokens, line),
            Section::Bounds => self.bound(&tokens, line),
            Section::End => Ok(()),
        }
    }

    fn header(&mut self, tokens: &[&str], line: usize) -> Result<(), LpError> {
        let word = tokens.first().copied().unwrap_or("");
        let next = match word {
            "NAME" => {
                if self.section != Section::Start {
                    return Err(refuse(line, "a second NAME line"));
                }
                self.name = tokens.get(1).map_or_else(String::new, ToString::to_string);
                self.section = Section::Name;
                return Ok(());
            }
            "OBJSENSE" => Section::ObjSense,
            "OBJNAME" => Section::ObjName,
            "ROWS" => Section::Rows,
            "COLUMNS" => Section::Columns,
            "RHS" => Section::Rhs,
            "RANGES" => Section::Ranges,
            "BOUNDS" => Section::Bounds,
            "ENDATA" => Section::End,
            "USERCUTS" | "LAZYCONS" | "SOS" | "INDICATORS" | "QUADOBJ" | "QMATRIX" | "QSECTION"
            | "QCMATRIX" | "CSECTION" | "GENCONS" | "PWLOBJ" => {
                return Err(refuse(
                    line,
                    format!("section {word} is not read by ay: it would have to be modelled"),
                ));
            }
            other => return Err(refuse(line, format!("unknown section header '{other}'"))),
        };
        if self.section == Section::Start {
            return Err(refuse(line, "an MPS file begins with a NAME line"));
        }
        if next <= self.section {
            return Err(refuse(
                line,
                format!("section {word} out of order or repeated"),
            ));
        }
        if self.section == Section::ObjSense && self.sense.is_none() {
            return Err(refuse(line, "OBJSENSE without a direction"));
        }
        if self.section == Section::ObjName && self.objname.is_none() {
            return Err(refuse(line, "OBJNAME without a row name"));
        }
        match (next, tokens.len()) {
            (_, 1) => {}
            (Section::ObjSense, 2) => self.sense = Some(parse_sense(tokens[1], line)?),
            (Section::ObjName, 2) => self.objname = Some(tokens[1].to_string()),
            _ => return Err(refuse(line, format!("unexpected field after {word}"))),
        }
        if next > Section::Rows && self.section <= Section::Rows {
            self.choose_objective(line)?;
        }
        self.section = next;
        Ok(())
    }

    fn choose_objective(&mut self, line: usize) -> Result<(), LpError> {
        if self.section != Section::Rows {
            return Err(refuse(line, "no ROWS section"));
        }
        self.objective = match &self.objname {
            Some(name) => match self.row_of.get(name) {
                Some(&r) if self.rows[r].kind == RowType::N => Some(r),
                _ => return Err(refuse(line, format!("OBJNAME '{name}' names no N row"))),
            },
            None => self.rows.iter().position(|r| r.kind == RowType::N),
        };
        Ok(())
    }

    fn row(&mut self, tokens: &[&str], line: usize) -> Result<(), LpError> {
        let [kind, name] = tokens else {
            return Err(refuse(line, "a ROWS line is '<N|L|G|E> <name>'"));
        };
        let kind = match *kind {
            "N" => RowType::N,
            "L" => RowType::L,
            "G" => RowType::G,
            "E" => RowType::E,
            other => return Err(refuse(line, format!("unknown row type '{other}'"))),
        };
        if self.row_of.contains_key(*name) {
            return Err(refuse(
                line,
                format!(
                    "duplicate row name '{name}': readers differ on which row its entries reach"
                ),
            ));
        }
        self.row_of.insert((*name).to_string(), self.rows.len());
        self.rows.push(RowDecl {
            name: (*name).to_string(),
            kind,
            coeffs: Vec::new(),
            rhs: None,
            range: None,
        });
        Ok(())
    }

    fn column(&mut self, tokens: &[&str], line: usize) -> Result<(), LpError> {
        if tokens.iter().any(|t| t.eq_ignore_ascii_case("'MARKER'")) {
            self.in_integer =
                match tokens {
                    [_, "'MARKER'", "'INTORG'"] => true,
                    [_, "'MARKER'", "'INTEND'"] => false,
                    _ => return Err(refuse(
                        line,
                        "a MARKER line is exactly `<name> 'MARKER' 'INTORG'` or `... 'INTEND'` \
                         (readers differ on any other)",
                    )),
                };
            self.current_col = None;
            return Ok(());
        }
        if tokens.len() != 3 && tokens.len() != 5 {
            return Err(refuse(
                line,
                "a COLUMNS line is '<column> <row> <value> [<row> <value>]'",
            ));
        }
        let name = tokens[0];
        let col = match self.col_of.get(name).copied() {
            Some(j) if self.current_col == Some(j) => j,
            Some(_) => {
                return Err(refuse(
                    line,
                    format!("the records of column '{name}' are not contiguous: readers differ"),
                ))
            }
            None => {
                let j = self.columns.len();
                self.col_of.insert(name.to_string(), j);
                let zero = BigRational::zero();
                self.columns.push(ColBuild {
                    name: name.to_string(),
                    kind: if self.in_integer {
                        VarKind::Binary
                    } else {
                        VarKind::Continuous
                    },
                    lower: Some(zero),
                    upper: self.in_integer.then(|| BigRational::from_integer(1.into())),
                    objective: None,
                    negative_up_line: None,
                });
                j
            }
        };
        self.current_col = Some(col);
        for pair in tokens[1..].chunks(2) {
            let (row, value) = (pair[0], self.number(pair[1], line)?);
            let r = *self
                .row_of
                .get(row)
                .ok_or_else(|| refuse(line, format!("unknown row '{row}'")))?;
            if Some(r) == self.objective {
                if self.columns[col].objective.is_some() {
                    return Err(refuse(
                        line,
                        format!(
                            "second objective entry of column '{name}': the checker keeps the \
                             last, others sum"
                        ),
                    ));
                }
                self.columns[col].objective = Some(value);
            } else if self.rows[r].kind != RowType::N {
                let coeffs = &mut self.rows[r].coeffs;
                match coeffs.last_mut() {
                    Some((j, sum)) if *j == col => {
                        *sum += value;
                        if !in_f64_range(sum) {
                            return Err(refuse(line, "summed coefficient out of range"));
                        }
                    }
                    _ => coeffs.push((col, value)),
                }
            }
        }
        Ok(())
    }

    fn rhs(&mut self, tokens: &[&str], line: usize) -> Result<(), LpError> {
        let (set, pairs) = set_and_pairs(tokens, "_RHS_", "RHS", line)?;
        one_set(&mut self.rhs_set, set, "RHS", line)?;
        for (row, text) in pairs {
            let value = self.number(text, line)?;
            let r = *self
                .row_of
                .get(row)
                .ok_or_else(|| refuse(line, format!("unknown row '{row}'")))?;
            if Some(r) == self.objective {
                if self.offset.is_some() {
                    return Err(refuse(line, "second RHS entry of the objective row"));
                }
                self.offset = Some(-value);
            } else if self.rows[r].kind == RowType::N {
                return Err(refuse(line, format!("RHS of the free row '{row}'")));
            } else if self.rows[r].rhs.is_some() {
                return Err(refuse(line, format!("second RHS entry of row '{row}'")));
            } else {
                self.rows[r].rhs = Some(value);
            }
        }
        Ok(())
    }

    fn range(&mut self, tokens: &[&str], line: usize) -> Result<(), LpError> {
        let (set, pairs) = set_and_pairs(tokens, "_RNG_", "RANGES", line)?;
        one_set(&mut self.ranges_set, set, "RANGES", line)?;
        for (row, text) in pairs {
            let value = self.number(text, line)?;
            let r = *self
                .row_of
                .get(row)
                .ok_or_else(|| refuse(line, format!("unknown row '{row}'")))?;
            if self.rows[r].kind == RowType::N {
                return Err(refuse(line, format!("RANGES of the N row '{row}'")));
            }
            if self.rows[r].range.is_some() {
                return Err(refuse(line, format!("second RANGES entry of row '{row}'")));
            }
            self.rows[r].range = Some((value, line));
        }
        Ok(())
    }

    fn bound(&mut self, tokens: &[&str], line: usize) -> Result<(), LpError> {
        let kind = tokens[0];
        let takes_value = match kind {
            "UP" | "LO" | "FX" | "LI" | "UI" => true,
            "FR" | "MI" | "PL" | "BV" => false,
            "SC" => return Err(refuse(line, "semi-continuous bound SC is not read by ay")),
            other => return Err(refuse(line, format!("unknown bound type '{other}'"))),
        };
        let (set, col_name, text) = match (takes_value, tokens.len()) {
            (true, 3) => ("_BND_", tokens[1], Some(tokens[2])),
            (true, 4) | (false, 4) => (tokens[1], tokens[2], Some(tokens[3])),
            (false, 2) => ("_BND_", tokens[1], None),
            (false, 3) => (tokens[1], tokens[2], None),
            _ => {
                return Err(refuse(
                    line,
                    format!(
                        "a {kind} line is '{kind} [<set>] <column>{}'",
                        if takes_value { " <value>" } else { "" }
                    ),
                ))
            }
        };
        one_set(&mut self.bounds_set, set, "BOUNDS", line)?;
        let j = *self
            .col_of
            .get(col_name)
            .ok_or_else(|| refuse(line, format!("unknown column '{col_name}'")))?;
        let value = text
            .map(|t| self.number(t, line))
            .transpose()?
            .unwrap_or_else(BigRational::zero);
        apply_bound(&mut self.columns[j], kind, value, line);
        Ok(())
    }

    fn finish(self, last_line: usize) -> Result<ExactProblem, LpError> {
        if self.section != Section::End {
            return Err(refuse(last_line, "no ENDATA line: the file may be cut off"));
        }
        let zero = BigRational::zero();
        let mut columns = Vec::with_capacity(self.columns.len());
        for c in self.columns {
            if let Some(line) = c.negative_up_line {
                if c.lower.as_ref() == Some(&zero) {
                    return Err(refuse(
                        line,
                        format!(
                            "column '{}' has an upper bound below 0 and lower bound 0: the \
                             checker keeps 0, CPLEX, SCIP and HiGHS take -inf",
                            c.name
                        ),
                    ));
                }
            }
            columns.push(ExactColumn {
                name: c.name,
                kind: c.kind,
                lower: c.lower,
                upper: c.upper,
                objective: c.objective.unwrap_or_else(BigRational::zero),
            });
        }
        let mut rows = Vec::new();
        for decl in self.rows {
            if decl.kind == RowType::N {
                continue;
            }
            let b = decl.rhs.unwrap_or_else(BigRational::zero);
            let (lower, upper) = match (&decl.range, decl.kind) {
                (None, RowType::L) => (None, Some(b)),
                (None, RowType::G) => (Some(b), None),
                (None, _) => (Some(b.clone()), Some(b)),
                (Some((r, _)), RowType::L) => (Some(&b - r.abs()), Some(b)),
                (Some((r, _)), RowType::G) => (Some(b.clone()), Some(&b + r.abs())),
                (Some((r, _)), _) if r.is_positive() => (Some(b.clone()), Some(&b + r)),
                (Some((r, _)), _) => (Some(&b + r), Some(b)),
            };
            if let Some((_, line)) = decl.range {
                if !lower.iter().chain(upper.iter()).all(in_f64_range) {
                    return Err(refuse(
                        line,
                        format!("a side of ranged row '{}' is out of range", decl.name),
                    ));
                }
            }
            rows.push(ExactRow {
                name: decl.name,
                coeffs: decl
                    .coeffs
                    .into_iter()
                    .filter(|(_, a)| !a.is_zero())
                    .collect(),
                lower,
                upper,
            });
        }
        Ok(ExactProblem {
            name: self.name,
            sense: self.sense.unwrap_or_default(),
            offset: self.offset.unwrap_or_else(BigRational::zero),
            columns,
            rows,
        })
    }
}

/// One `BOUNDS` entry, as the checker applies it (module docs).
fn apply_bound(col: &mut ColBuild, kind: &str, value: BigRational, line: usize) {
    let one = BigRational::from_integer(1.into());
    let zero = BigRational::zero();
    if col.kind == VarKind::Binary
        && (kind == "LI" || kind == "UI" || !(kind == "UP" && value == one))
    {
        col.kind = VarKind::Integer;
        col.upper = None;
    }
    match kind {
        "LO" | "LI" => col.lower = Some(value),
        "UP" | "UI" => {
            if value.is_negative() && col.negative_up_line.is_none() {
                col.negative_up_line = Some(line);
            }
            col.upper = Some(value);
        }
        "FX" => {
            col.lower = Some(value.clone());
            col.upper = Some(value);
        }
        "FR" => {
            col.lower = None;
            col.upper = None;
        }
        "MI" => col.lower = None,
        "PL" => col.upper = None,
        _ => {
            // BV
            col.kind = VarKind::Binary;
            col.lower = Some(col.lower.take().map_or(zero.clone(), |lo| lo.max(zero)));
            col.upper = Some(col.upper.take().map_or(one.clone(), |up| up.min(one)));
            return;
        }
    }
    if kind == "LI" || kind == "UI" {
        col.kind = VarKind::Integer;
    }
}
