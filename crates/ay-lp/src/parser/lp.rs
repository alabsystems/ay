// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The CPLEX LP format reader: one exact reading, or a refusal.
//!
//! Every number is kept as the rational its decimal text denotes
//! ([`crate::exact::decimal`]); nothing passes through `f64`. Where CPLEX,
//! Gurobi and SCIP give a construct different meanings, or where a line
//! reader could take a construct for another, the file is refused with a
//! line-numbered error: no verdict is ever printed from a guessed reading.
//!
//! # The reading
//!
//! - Comments: `\` to the end of the line; a `\*` comment must close on its
//!   line. Keywords are case-insensitive; a section keyword stands alone on
//!   its line.
//! - Sections, in this order: the objective (`Minimize`, `Minimise`,
//!   `Minimum`, `Min`, or the `Max` forms; required, first), `Subject To`
//!   (`such that`, `st`, `s.t.`), `Bounds`, then `General` (`Generals`,
//!   `Gen`, `Integer`, `Integers`) and `Binary` (`Binaries`, `Bin`) in either
//!   order, each section at most once, and `End` (required; nothing may
//!   follow it). Semi-continuous, semi-integer, SOS, lazy-constraint,
//!   user-cut, piecewise-linear and general-constraint sections, quadratic
//!   terms (`[`, `]`, `^`) and indicator constraints (`->`) are refused.
//! - Expressions: terms `[+|-] [number] name`; the first term may omit its
//!   sign, every later one has exactly one `+` or `-`. A number directly
//!   before a name is its coefficient. Repeated names are summed. Names
//!   `free`, `inf` and `infinity` (any case) are refused as variables.
//! - Objective: an optional `name:`, then an expression in which a number
//!   standing alone is a constant (summed into the offset).
//! - Constraints: `[name:] expression <op> [+|-] number`, `<op>` one of
//!   `<`, `<=`, `=<`, `>`, `>=`, `=>`, `=` (`<` means `<=`). The right-hand
//!   side ends the constraint and the line: a constant on the left, a
//!   variable on the right, a number-first or double-sided (ranged) form
//!   and a second constraint on the same line are refused. Unnamed rows are
//!   called `c<k>`; a repeated explicit name is refused. A right-hand side of
//!   magnitude `1e20` or more is refused (CPLEX and SCIP read it as
//!   infinite, Gurobi as finite).
//! - Bounds, one statement per line: `x free`, `x <op> v`, `v <op> x`,
//!   `v1 <= x <= v2`, `v1 >= x >= v2`, with `<`/`>` as above and `=` fixing
//!   `x`. `v` is a number or `inf`/`infinity` with an optional sign; a
//!   number of magnitude `1e30` or more is that infinity (all three readers
//!   agree from `1e30`), one in `[1e20, 1e30)` is refused (CPLEX and SCIP
//!   read it as infinite, Gurobi as finite). A lower bound `+inf`, an upper
//!   bound `-inf`, a fix at an infinity and a second statement setting the
//!   same side of the same variable are refused. Defaults: `[0, +inf)`. An
//!   upper bound below 0 on a variable whose lower bound was not given is
//!   refused (readers differ on whether the default 0 stays).
//! - `General`: the listed variables are integer, with their bounds.
//!   `Binary`: integer in `[0, 1]`; refused unless the Bounds section left
//!   the variable's lower bound at 0 and its upper bound unset or 1 (CPLEX
//!   replaces other bounds by `[0, 1]`, other readers intersect them). A
//!   variable in both sections is refused.
//! - Every number, sum and constant must be in the range an `f64` can
//!   approximate ([`crate::exact::decimal`]).

use std::collections::{BTreeMap, HashMap, HashSet};

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::error::LpError;
use crate::exact::decimal::in_f64_range;
use crate::exact::{ExactColumn, ExactProblem, ExactRow};
use crate::model::{Problem, Sense, VarKind};
use crate::parser::lp_tok::{tokenize, Section, SpannedTok, Tok};

/// Parses a CPLEX LP file into a floating-point [`Problem`]: the
/// [`ExactProblem::to_problem`] copy of [`parse_lp_exact`]'s reading.
///
/// # Errors
///
/// As [`parse_lp_exact`].
pub fn parse_lp(input: &str) -> Result<Problem, LpError> {
    Ok(parse_lp_exact(input)?.to_problem())
}

/// Reads a CPLEX LP file exactly (module docs).
///
/// # Errors
///
/// [`LpError::Parse`] or [`LpError::InvalidNumber`] with the line of the
/// first malformed or refused construct.
pub fn parse_lp_exact(input: &str) -> Result<ExactProblem, LpError> {
    let mut reader = Reader {
        tokens: tokenize(input)?,
        ..Reader::default()
    };
    reader.read()?;
    reader.finish()
}

fn refuse(line: usize, msg: impl Into<String>) -> LpError {
    LpError::Parse {
        line,
        msg: msg.into(),
    }
}

fn pow10(e: u32) -> BigRational {
    BigRational::from_integer(BigInt::from(10u8).pow(e))
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Op {
    Le,
    Ge,
    Eq,
}

/// A bound value as written: finite, or an infinity of a sign.
enum BoundValue {
    Finite(BigRational),
    Infinite { positive: bool },
}

struct ColBuild {
    name: String,
    objective: BigRational,
    lower: Option<BigRational>,
    upper: Option<BigRational>,
    lower_line: Option<usize>,
    upper_line: Option<usize>,
    kind: VarKind,
    kind_line: usize,
}

#[derive(Default)]
struct Reader {
    tokens: Vec<SpannedTok>,
    pos: usize,
    name: String,
    sense: Sense,
    offset: BigRational,
    columns: Vec<ColBuild>,
    col_index: HashMap<String, usize>,
    rows: Vec<ExactRow>,
    row_names: HashSet<String>,
}

impl Reader {
    fn peek(&self) -> Option<&Tok> {
        self.tokens.get(self.pos).map(|t| &t.tok)
    }

    fn line(&self) -> usize {
        self.tokens
            .get(self.pos)
            .or_else(|| self.tokens.last())
            .map_or(0, |t| t.line)
    }

    fn at_section_end(&self) -> bool {
        matches!(self.peek(), None | Some(Tok::Header(_) | Tok::End))
    }

    fn read(&mut self) -> Result<(), LpError> {
        let Some(Tok::Header(Section::Objective(sense))) = self.peek().cloned() else {
            return Err(refuse(
                self.line(),
                "an LP file starts with Minimize or Maximize",
            ));
        };
        self.sense = sense;
        self.pos += 1;
        if let (Some(Tok::Word(name)), Some(Tok::Colon)) = (
            self.peek().cloned(),
            self.tokens.get(self.pos + 1).map(|t| &t.tok),
        ) {
            self.name = name;
            self.pos += 2;
        }
        let (terms, constant) = self.expression(true)?;
        for (j, a) in terms {
            let sum = &self.columns[j].objective + a;
            self.columns[j].objective = self.in_range(sum, "objective coefficient sum")?;
        }
        self.offset = self.in_range(constant, "objective constant")?;
        // Sections after the objective, by rank: each at most once, in order.
        let mut done: Vec<u8> = Vec::new();
        loop {
            let line = self.line();
            let Some(tok) = self.peek().cloned() else {
                return Err(refuse(line, "no End line: the file may be cut off"));
            };
            self.pos += 1;
            let rank = match tok {
                Tok::Header(Section::Subject) => 1,
                Tok::Header(Section::Bounds) => 2,
                Tok::Header(Section::General) => 3,
                Tok::Header(Section::Binary) => 4,
                Tok::End => {
                    if self.pos < self.tokens.len() {
                        return Err(refuse(self.line(), "content after End"));
                    }
                    return Ok(());
                }
                Tok::Header(Section::Objective(_)) => {
                    return Err(refuse(line, "a second objective section"))
                }
                other => return Err(refuse(line, format!("unexpected {other:?}"))),
            };
            // General and Binary share the last rank: either order.
            let level = |r: u8| r.min(3);
            let out_of_order = done.contains(&rank) || done.iter().any(|&d| level(d) > level(rank));
            if out_of_order {
                return Err(refuse(line, "section repeated or out of order"));
            }
            done.push(rank);
            match rank {
                1 => {
                    while !self.at_section_end() {
                        self.constraint()?;
                    }
                }
                2 => {
                    while !self.at_section_end() {
                        self.bound()?;
                    }
                }
                _ => self.kind_list(if rank == 3 {
                    VarKind::Integer
                } else {
                    VarKind::Binary
                })?,
            }
        }
    }

    fn in_range(&self, value: BigRational, what: &str) -> Result<BigRational, LpError> {
        if in_f64_range(&value) {
            Ok(value)
        } else {
            Err(refuse(
                self.line(),
                format!("{what} {value} is out of range"),
            ))
        }
    }

    fn column(&mut self, name: &str, line: usize) -> Result<usize, LpError> {
        if ["free", "inf", "infinity"]
            .iter()
            .any(|r| name.eq_ignore_ascii_case(r))
        {
            return Err(refuse(
                line,
                format!("'{name}' is not accepted as a variable name"),
            ));
        }
        if let Some(&j) = self.col_index.get(name) {
            return Ok(j);
        }
        let j = self.columns.len();
        self.columns.push(ColBuild {
            name: name.to_string(),
            objective: BigRational::zero(),
            lower: Some(BigRational::zero()),
            upper: None,
            lower_line: None,
            upper_line: None,
            kind: VarKind::Continuous,
            kind_line: 0,
        });
        self.col_index.insert(name.to_string(), j);
        Ok(j)
    }

    /// Terms up to a comparator, a header or `End`: the summed coefficients
    /// by column and the summed constants (refused unless `constants`).
    fn expression(
        &mut self,
        constants: bool,
    ) -> Result<(BTreeMap<usize, BigRational>, BigRational), LpError> {
        let mut terms: BTreeMap<usize, BigRational> = BTreeMap::new();
        let mut constant = BigRational::zero();
        let mut first = true;
        loop {
            if self.at_section_end() || matches!(self.peek(), Some(Tok::Le | Tok::Ge | Tok::Eq)) {
                return Ok((terms, constant));
            }
            let line = self.line();
            let sign = match self.peek() {
                Some(Tok::Plus) => Some(BigRational::one()),
                Some(Tok::Minus) => Some(-BigRational::one()),
                _ => None,
            };
            let sign = match (sign, first) {
                (Some(s), _) => {
                    self.pos += 1;
                    s
                }
                (None, true) => BigRational::one(),
                (None, false) => {
                    return Err(refuse(line, "expected '+' or '-' between two terms"));
                }
            };
            first = false;
            match self.peek().cloned() {
                Some(Tok::Num(value)) => {
                    self.pos += 1;
                    if let Some(Tok::Word(name)) = self.peek().cloned() {
                        self.pos += 1;
                        let j = self.column(&name, line)?;
                        let sum = terms.remove(&j).unwrap_or_default() + sign * value;
                        terms.insert(j, self.in_range(sum, "coefficient sum")?);
                    } else if constants {
                        constant = self.in_range(constant + sign * value, "constant")?;
                    } else {
                        return Err(refuse(
                            line,
                            "a constant on the left of a constraint (or a number-first or \
                             double-sided constraint) is not supported",
                        ));
                    }
                }
                Some(Tok::Word(name)) => {
                    self.pos += 1;
                    let j = self.column(&name, line)?;
                    let sum = terms.remove(&j).unwrap_or_default() + sign;
                    terms.insert(j, self.in_range(sum, "coefficient sum")?);
                }
                other => return Err(refuse(line, format!("expected a term, found {other:?}"))),
            }
        }
    }

    fn constraint(&mut self) -> Result<(), LpError> {
        let line = self.line();
        let name = if let (Some(Tok::Word(name)), Some(Tok::Colon)) = (
            self.peek().cloned(),
            self.tokens.get(self.pos + 1).map(|t| &t.tok),
        ) {
            self.pos += 2;
            if !self.row_names.insert(name.clone()) {
                return Err(refuse(line, format!("a second constraint named '{name}'")));
            }
            name
        } else {
            format!("c{}", self.rows.len() + 1)
        };
        let (terms, _) = self.expression(false)?;
        let op = match self.peek() {
            Some(Tok::Le) => Op::Le,
            Some(Tok::Ge) => Op::Ge,
            Some(Tok::Eq) => Op::Eq,
            _ => return Err(refuse(self.line(), "constraint without a comparator")),
        };
        self.pos += 1;
        if terms.is_empty() {
            return Err(refuse(line, "constraint without a variable on its left"));
        }
        let negative = match self.peek() {
            Some(Tok::Plus) => {
                self.pos += 1;
                false
            }
            Some(Tok::Minus) => {
                self.pos += 1;
                true
            }
            _ => false,
        };
        let rhs_line = self.line();
        let Some(Tok::Num(value)) = self.peek().cloned() else {
            return Err(refuse(
                rhs_line,
                "the right-hand side of a constraint is one number",
            ));
        };
        self.pos += 1;
        let rhs = if negative { -value } else { value };
        if rhs.abs() >= pow10(20) {
            return Err(refuse(
                rhs_line,
                "a right-hand side of magnitude 1e20 or more is infinite to some readers",
            ));
        }
        if self
            .tokens
            .get(self.pos)
            .is_some_and(|t| t.line == rhs_line)
        {
            return Err(refuse(
                rhs_line,
                "a constraint ends its line at its right-hand side (ranged constraints and \
                 variables on the right are not supported)",
            ));
        }
        let (lower, upper) = match op {
            Op::Le => (None, Some(rhs)),
            Op::Ge => (Some(rhs), None),
            Op::Eq => (Some(rhs.clone()), Some(rhs)),
        };
        self.rows.push(ExactRow {
            name,
            coeffs: terms.into_iter().filter(|(_, a)| !a.is_zero()).collect(),
            lower,
            upper,
        });
        Ok(())
    }

    /// One `Bounds` statement: the tokens of one line.
    fn bound(&mut self) -> Result<(), LpError> {
        let line = self.line();
        let end = self.tokens[self.pos..]
            .iter()
            .position(|t| t.line != line)
            .map_or(self.tokens.len(), |k| self.pos + k);
        let stmt: Vec<Tok> = self.tokens[self.pos..end]
            .iter()
            .map(|t| t.tok.clone())
            .collect();
        self.pos = end;
        let mut at = 0;
        if let [Tok::Word(name), Tok::Word(free)] = stmt.as_slice() {
            if free.eq_ignore_ascii_case("free") {
                let j = self.column(name, line)?;
                set_side(&mut self.columns[j], false, None, line)?;
                return set_side(&mut self.columns[j], true, None, line);
            }
        }
        let first = if let Some(Tok::Word(name)) = stmt.first() {
            at = 1;
            Err(name.clone())
        } else {
            Ok(bound_value(&stmt, &mut at, line)?)
        };
        let op1 = bound_op(&stmt, &mut at, line)?;
        let (j, value, op) = match first {
            // `x <op> v`: the side the comparator names.
            Err(name) => {
                let v = bound_value(&stmt, &mut at, line)?;
                (self.column(&name, line)?, v, op1)
            }
            // `v <op> x [<op> v2]`: the comparator read from the variable.
            Ok(v) => {
                let Some(Tok::Word(name)) = stmt.get(at) else {
                    return Err(refuse(line, "a bound names one variable"));
                };
                at += 1;
                let j = self.column(name, line)?;
                let flipped = match op1 {
                    Op::Le => Op::Ge,
                    Op::Ge => Op::Le,
                    Op::Eq => Op::Eq,
                };
                if at < stmt.len() {
                    let op2 = bound_op(&stmt, &mut at, line)?;
                    let v2 = bound_value(&stmt, &mut at, line)?;
                    if op1 != op2 || op1 == Op::Eq {
                        return Err(refuse(line, "a double bound uses two '<=' or two '>='"));
                    }
                    self.apply(j, flipped, v, line)?;
                    (j, v2, op2)
                } else {
                    (j, v, flipped)
                }
            }
        };
        if at != stmt.len() {
            return Err(refuse(line, "one bound statement per line"));
        }
        self.apply(j, op, value, line)
    }

    /// `x <op> value`.
    fn apply(&mut self, j: usize, op: Op, value: BoundValue, line: usize) -> Result<(), LpError> {
        let column = &mut self.columns[j];
        let finite = |positive_ok: bool| match &value {
            BoundValue::Finite(v) => Ok(Some(v.clone())),
            BoundValue::Infinite { positive } if *positive == positive_ok => Ok(None),
            BoundValue::Infinite { .. } => Err(refuse(line, "a bound at the wrong infinity")),
        };
        match op {
            Op::Le => set_side(column, true, finite(true)?, line),
            Op::Ge => set_side(column, false, finite(false)?, line),
            Op::Eq => {
                let BoundValue::Finite(v) = &value else {
                    return Err(refuse(line, "a variable fixed at an infinity"));
                };
                set_side(column, false, Some(v.clone()), line)?;
                set_side(column, true, Some(v.clone()), line)
            }
        }
    }

    fn kind_list(&mut self, kind: VarKind) -> Result<(), LpError> {
        while !self.at_section_end() {
            let line = self.line();
            let Some(Tok::Word(name)) = self.peek().cloned() else {
                return Err(refuse(line, "a variable name is expected here"));
            };
            self.pos += 1;
            let j = self.column(&name, line)?;
            let column = &mut self.columns[j];
            if column.kind != VarKind::Continuous && column.kind != kind {
                return Err(refuse(
                    line,
                    format!("'{name}' is declared both General and Binary"),
                ));
            }
            column.kind = kind;
            column.kind_line = line;
        }
        Ok(())
    }

    fn finish(self) -> Result<ExactProblem, LpError> {
        let zero = BigRational::zero();
        let one = BigRational::one();
        let mut columns = Vec::with_capacity(self.columns.len());
        for mut c in self.columns {
            if c.kind == VarKind::Binary {
                let upper_ok = match &c.upper {
                    None => c.upper_line.is_none(),
                    Some(u) => *u == one,
                };
                if c.lower.as_ref() != Some(&zero) || !upper_ok {
                    return Err(refuse(
                        c.kind_line,
                        format!(
                            "binary '{}' has bounds other than [0, 1]: CPLEX replaces them, \
                             other readers intersect them",
                            c.name
                        ),
                    ));
                }
                c.upper = Some(one.clone());
            }
            if let (Some(u), None, Some(line)) = (&c.upper, c.lower_line, c.upper_line) {
                if u.is_negative() {
                    return Err(refuse(
                        line,
                        format!(
                            "'{}' has an upper bound below 0 and no lower bound: readers \
                             differ on whether the default 0 stays",
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
                objective: c.objective,
            });
        }
        Ok(ExactProblem {
            name: self.name,
            sense: self.sense,
            offset: self.offset,
            columns,
            rows: self.rows,
        })
    }
}

/// Sets the lower (`upper == false`) or upper side of `column`, refusing a
/// second statement for the same side.
fn set_side(
    column: &mut ColBuild,
    upper: bool,
    value: Option<BigRational>,
    line: usize,
) -> Result<(), LpError> {
    let (slot, seen) = if upper {
        (&mut column.upper, &mut column.upper_line)
    } else {
        (&mut column.lower, &mut column.lower_line)
    };
    if let Some(first) = *seen {
        return Err(refuse(
            line,
            format!(
                "a second {} bound for '{}' (first on line {first})",
                if upper { "upper" } else { "lower" },
                column.name
            ),
        ));
    }
    *seen = Some(line);
    *slot = value;
    Ok(())
}

fn bound_op(stmt: &[Tok], at: &mut usize, line: usize) -> Result<Op, LpError> {
    let op = match stmt.get(*at) {
        Some(Tok::Le) => Op::Le,
        Some(Tok::Ge) => Op::Ge,
        Some(Tok::Eq) => Op::Eq,
        _ => return Err(refuse(line, "a bound needs '<=', '>=' or '='")),
    };
    *at += 1;
    Ok(op)
}

/// `[+|-] (number | inf | infinity)`; magnitudes from `1e30` are infinite,
/// those in `[1e20, 1e30)` refused (module docs).
fn bound_value(stmt: &[Tok], at: &mut usize, line: usize) -> Result<BoundValue, LpError> {
    let negative = match stmt.get(*at) {
        Some(Tok::Plus) => {
            *at += 1;
            false
        }
        Some(Tok::Minus) => {
            *at += 1;
            true
        }
        _ => false,
    };
    let value = match stmt.get(*at) {
        Some(Tok::Num(v)) if v.abs() >= pow10(30) => BoundValue::Infinite {
            positive: !negative,
        },
        Some(Tok::Num(v)) if v.abs() >= pow10(20) => {
            return Err(refuse(
                line,
                "a bound of magnitude in [1e20, 1e30) is infinite to CPLEX and SCIP, finite \
                 to Gurobi",
            ))
        }
        Some(Tok::Num(v)) => BoundValue::Finite(if negative { -v.clone() } else { v.clone() }),
        Some(Tok::Word(w))
            if w.eq_ignore_ascii_case("inf") || w.eq_ignore_ascii_case("infinity") =>
        {
            BoundValue::Infinite {
                positive: !negative,
            }
        }
        _ => return Err(refuse(line, "a bound value is a number or 'inf'")),
    };
    *at += 1;
    Ok(value)
}

// Unit tests live in `tests/parser_lp.rs` (module budget).
