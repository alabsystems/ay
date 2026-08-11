// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! CPLEX LP format parser. Supports `Minimize`/`Maximize`, `Subject To`,
//! `Bounds`, `General`/`Integer`/`Binary`, `End`. Case-insensitive, tolerant
//! of common aliases (`st`, `s.t.`). Bounds forms: `0 <= x <= 5`, `x >= 0`,
//! `x free`, `-inf <= x`.

use std::collections::BTreeMap;

use crate::error::LpError;
use crate::model::{Constraint, Problem, RowKind, VarKind, Variable};
use crate::parser::checked_finite_add;
use crate::parser::lp_tok::{tokenize, Section, SpannedTok, Tok};

/// Parses a CPLEX LP file into a [`Problem`].
///
/// # Errors
///
/// Returns an [`LpError`] for unterminated expressions or unknown sections.
pub fn parse_lp(input: &str) -> Result<Problem, LpError> {
    let tokens = tokenize(input)?;
    let parser = LpParser::new(tokens);
    parser.parse()
}

struct LpParser {
    tokens: Vec<SpannedTok>,
    pos: usize,
    problem: Problem,
    col_index: BTreeMap<String, usize>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Comparator {
    Le,
    Ge,
    Eq,
}

impl LpParser {
    fn new(tokens: Vec<SpannedTok>) -> Self {
        Self {
            tokens,
            pos: 0,
            problem: Problem::new(),
            col_index: BTreeMap::new(),
        }
    }

    fn parse(mut self) -> Result<Problem, LpError> {
        // Expect an objective header first.
        let Some(SpannedTok {
            tok: Tok::Header(Section::Objective(sense)),
            line,
        }) = self.tokens.get(self.pos).cloned()
        else {
            return Err(LpError::Parse {
                line: 0,
                msg: "LP file must start with Minimize or Maximize".to_string(),
            });
        };
        self.problem.sense = sense;
        self.pos += 1;

        // Parse objective (optional name, then a linear expression until next header).
        self.parse_objective(line)?;

        while self.pos < self.tokens.len() {
            let Some(tok) = self.tokens.get(self.pos) else {
                break;
            };
            match &tok.tok {
                Tok::Header(Section::Subject) => {
                    self.pos += 1;
                    self.parse_subject_to()?;
                }
                Tok::Header(Section::Bounds) => {
                    self.pos += 1;
                    self.parse_bounds()?;
                }
                Tok::Header(Section::General) | Tok::Header(Section::Integer) => {
                    self.pos += 1;
                    self.parse_var_list(VarKind::Integer)?;
                }
                Tok::Header(Section::Binary) => {
                    self.pos += 1;
                    self.parse_var_list(VarKind::Binary)?;
                }
                Tok::End => break,
                Tok::Header(Section::Objective(_)) => {
                    return Err(LpError::Parse {
                        line: tok.line,
                        msg: "duplicate objective section".to_string(),
                    });
                }
                other => {
                    return Err(LpError::Parse {
                        line: tok.line,
                        msg: format!("unexpected token {other:?}"),
                    });
                }
            }
        }

        Ok(self.problem)
    }

    fn parse_objective(&mut self, hdr_line: usize) -> Result<(), LpError> {
        // Optional "name:".
        if let (Some(a), Some(b)) = (self.tokens.get(self.pos), self.tokens.get(self.pos + 1)) {
            if let (Tok::Word(n), Tok::Colon) = (&a.tok, &b.tok) {
                self.problem.name = n.clone();
                self.pos += 2;
            }
        }
        let terms = self.parse_expression_until_header()?;
        for (var_idx, coeff) in terms {
            let current = self.problem.variables[var_idx].obj_coeff;
            self.problem.variables[var_idx].obj_coeff =
                checked_finite_add(current, coeff, hdr_line, "objective coefficient sum")?;
        }
        Ok(())
    }

    fn parse_subject_to(&mut self) -> Result<(), LpError> {
        while self.pos < self.tokens.len() {
            if self.peek_is_header() {
                return Ok(());
            }
            self.parse_constraint()?;
        }
        Ok(())
    }

    fn parse_constraint(&mut self) -> Result<(), LpError> {
        let constraint_line = self.tokens.get(self.pos).map_or(0, |token| token.line);
        // Optional name:
        let name = if let (Some(a), Some(b)) =
            (self.tokens.get(self.pos), self.tokens.get(self.pos + 1))
        {
            if let (Tok::Word(n), Tok::Colon) = (&a.tok, &b.tok) {
                let n = n.clone();
                self.pos += 2;
                n
            } else {
                format!("c{}", self.problem.constraints.len() + 1)
            }
        } else {
            format!("c{}", self.problem.constraints.len() + 1)
        };

        // Parse LHS expression until a comparator.
        let (lhs, op) = self.parse_lhs_until_op()?;
        let lhs = aggregate_constraint_terms(lhs, constraint_line)?;
        let rhs = self.parse_rhs_number()?;

        let kind = match op {
            Comparator::Le => RowKind::Le,
            Comparator::Ge => RowKind::Ge,
            Comparator::Eq => RowKind::Eq,
        };

        self.problem.constraints.push(Constraint {
            name,
            kind,
            coeffs: lhs,
            rhs,
        });
        Ok(())
    }

    fn parse_bounds(&mut self) -> Result<(), LpError> {
        while self.pos < self.tokens.len() {
            if self.peek_is_header() {
                return Ok(());
            }
            self.parse_bound()?;
        }
        Ok(())
    }

    fn parse_bound(&mut self) -> Result<(), LpError> {
        // Supported patterns:
        //   <name> free
        //   <lo> <= <name> <= <hi>
        //   <name> <= <hi>
        //   <name> >= <lo>
        //   <name> = <val>
        //   <lo> <= <name>
        let start_line = self.tokens[self.pos].line;

        // Try "<name> free".
        if let Some(SpannedTok {
            tok: Tok::Word(n), ..
        }) = self.tokens.get(self.pos).cloned()
        {
            if let Some(SpannedTok {
                tok: Tok::Word(kw), ..
            }) = self.tokens.get(self.pos + 1).cloned()
            {
                if kw.eq_ignore_ascii_case("free") {
                    let idx = self.intern_var(&n);
                    self.problem.variables[idx].lower = f64::NEG_INFINITY;
                    self.problem.variables[idx].upper = f64::INFINITY;
                    self.pos += 2;
                    return Ok(());
                }
            }
        }

        // Either `<num> <op> <name> <op> <num>` or `<name> <op> <num>`.
        // First token is either a number (optionally preceded by +/-) or a name.
        if matches!(
            self.peek().map(|t| &t.tok),
            Some(Tok::Num(_) | Tok::Plus | Tok::Minus)
        ) {
            let first_value = self.consume_signed_number_or_inf(start_line)?;
            let first_op = self.expect_op(start_line)?;
            let name = self.expect_word(start_line)?;
            let idx = self.intern_var(&name);
            if self.peek_is_op() {
                let second_op = self.expect_op(start_line)?;
                let second_value = self.consume_signed_number_or_inf(start_line)?;
                match (first_op, second_op) {
                    // `lo <= x <= hi`.
                    (Comparator::Le, Comparator::Le) => {
                        self.problem.variables[idx].lower = first_value;
                        self.problem.variables[idx].upper = second_value;
                    }
                    // The equivalent reversed spelling: `hi >= x >= lo`.
                    (Comparator::Ge, Comparator::Ge) => {
                        self.problem.variables[idx].upper = first_value;
                        self.problem.variables[idx].lower = second_value;
                    }
                    _ => {
                        return Err(LpError::Parse {
                            line: start_line,
                            msg: "ranged bound comparators must use matching directions"
                                .to_string(),
                        });
                    }
                }
            } else {
                match first_op {
                    // `<lo> <= <name>` implies a lower bound.
                    Comparator::Le => self.problem.variables[idx].lower = first_value,
                    // `<hi> >= <name>` implies an upper bound.
                    Comparator::Ge => self.problem.variables[idx].upper = first_value,
                    Comparator::Eq => {
                        self.problem.variables[idx].lower = first_value;
                        self.problem.variables[idx].upper = first_value;
                    }
                }
            }
            Ok(())
        } else {
            let name = self.expect_word(start_line)?;
            let idx = self.intern_var(&name);
            let op = self.expect_op(start_line)?;
            let value = self.consume_signed_number_or_inf(start_line)?;
            match op {
                Comparator::Le => self.problem.variables[idx].upper = value,
                Comparator::Ge => self.problem.variables[idx].lower = value,
                Comparator::Eq => {
                    self.problem.variables[idx].lower = value;
                    self.problem.variables[idx].upper = value;
                }
            }
            Ok(())
        }
    }

    fn parse_var_list(&mut self, kind: VarKind) -> Result<(), LpError> {
        while self.pos < self.tokens.len() {
            if self.peek_is_header() {
                return Ok(());
            }
            if let Some(SpannedTok {
                tok: Tok::Word(name),
                ..
            }) = self.tokens.get(self.pos).cloned()
            {
                let idx = self.intern_var(&name);
                self.problem.variables[idx].kind = kind;
                if matches!(kind, VarKind::Binary)
                    && self.problem.variables[idx].lower == 0.0
                    && self.problem.variables[idx].upper.is_infinite()
                    && self.problem.variables[idx].upper.is_sign_positive()
                {
                    self.problem.variables[idx].lower = 0.0;
                    self.problem.variables[idx].upper = 1.0;
                }
                self.pos += 1;
            } else {
                return Err(LpError::Parse {
                    line: self.tokens[self.pos].line,
                    msg: format!(
                        "variable name expected, got {:?}",
                        self.tokens[self.pos].tok
                    ),
                });
            }
        }
        Ok(())
    }

    fn parse_expression_until_header(&mut self) -> Result<Vec<(usize, f64)>, LpError> {
        let mut out: Vec<(usize, f64)> = Vec::new();
        let mut sign = 1.0;
        while let Some(tok) = self.tokens.get(self.pos) {
            match &tok.tok {
                Tok::Header(_) | Tok::End => break,
                Tok::Plus => {
                    sign = 1.0;
                    self.pos += 1;
                }
                Tok::Minus => {
                    sign = -sign;
                    self.pos += 1;
                }
                Tok::Num(n) => {
                    let coef = *n * sign;
                    self.pos += 1;
                    if let Some(SpannedTok {
                        tok: Tok::Word(name),
                        ..
                    }) = self.tokens.get(self.pos).cloned()
                    {
                        let idx = self.intern_var(&name);
                        out.push((idx, coef));
                        self.pos += 1;
                    } else {
                        // Standalone numeric term. Fold into objective constant
                        // via an "extra" phantom entry — here we return to the
                        // caller which only uses this for the objective.
                        self.problem.obj_constant = checked_finite_add(
                            self.problem.obj_constant,
                            coef,
                            tok.line,
                            "objective constant sum",
                        )?;
                    }
                    sign = 1.0;
                }
                Tok::Word(name) => {
                    let idx = self.intern_var(&name.clone());
                    out.push((idx, sign));
                    self.pos += 1;
                    sign = 1.0;
                }
                _ => break,
            }
        }
        Ok(out)
    }

    fn parse_lhs_until_op(&mut self) -> Result<(Vec<(usize, f64)>, Comparator), LpError> {
        let mut out: Vec<(usize, f64)> = Vec::new();
        let mut sign = 1.0;
        while let Some(tok) = self.tokens.get(self.pos).cloned() {
            match tok.tok {
                Tok::Le | Tok::Ge | Tok::Eq => {
                    let op = match tok.tok {
                        Tok::Le => Comparator::Le,
                        Tok::Ge => Comparator::Ge,
                        Tok::Eq => Comparator::Eq,
                        _ => {
                            return Err(LpError::Parse {
                                line: tok.line,
                                msg: "constraint requires <=, >=, or =".to_string(),
                            });
                        }
                    };
                    self.pos += 1;
                    return Ok((out, op));
                }
                Tok::Plus => {
                    sign = 1.0;
                    self.pos += 1;
                }
                Tok::Minus => {
                    sign = -sign;
                    self.pos += 1;
                }
                Tok::Num(n) => {
                    let coef = n * sign;
                    self.pos += 1;
                    if let Some(SpannedTok {
                        tok: Tok::Word(name),
                        ..
                    }) = self.tokens.get(self.pos).cloned()
                    {
                        let idx = self.intern_var(&name);
                        out.push((idx, coef));
                        self.pos += 1;
                    } else {
                        return Err(LpError::Parse {
                            line: tok.line,
                            msg: "constant term on LHS not supported".to_string(),
                        });
                    }
                    sign = 1.0;
                }
                Tok::Word(name) => {
                    let idx = self.intern_var(&name);
                    out.push((idx, sign));
                    self.pos += 1;
                    sign = 1.0;
                }
                _ => {
                    return Err(LpError::Parse {
                        line: tok.line,
                        msg: format!("unexpected token in constraint LHS: {:?}", tok.tok),
                    });
                }
            }
        }
        Err(LpError::Parse {
            line: 0,
            msg: "constraint missing comparator".to_string(),
        })
    }

    fn parse_rhs_number(&mut self) -> Result<f64, LpError> {
        let start_line = self.tokens.get(self.pos).map_or(0, |t| t.line);
        let sign = match self.peek().map(|t| &t.tok) {
            Some(Tok::Plus) => {
                self.pos += 1;
                1.0
            }
            Some(Tok::Minus) => {
                self.pos += 1;
                -1.0
            }
            _ => 1.0,
        };
        match self.advance_clone() {
            Some(SpannedTok {
                tok: Tok::Num(n), ..
            }) => Ok(n * sign),
            other => Err(LpError::Parse {
                line: other.as_ref().map_or(start_line, |t| t.line),
                msg: "expected numeric RHS".to_string(),
            }),
        }
    }

    fn consume_signed_number_or_inf(&mut self, default_line: usize) -> Result<f64, LpError> {
        let sign = match self.peek().map(|t| &t.tok) {
            Some(Tok::Plus) => {
                self.pos += 1;
                1.0
            }
            Some(Tok::Minus) => {
                self.pos += 1;
                -1.0
            }
            _ => 1.0,
        };
        match self.advance_clone() {
            Some(SpannedTok {
                tok: Tok::Num(n), ..
            }) => Ok(n * sign),
            Some(SpannedTok {
                tok: Tok::Word(w),
                line,
            }) if w.eq_ignore_ascii_case("inf") || w.eq_ignore_ascii_case("infinity") => {
                let _ = line;
                Ok(f64::INFINITY * sign)
            }
            other => Err(LpError::Parse {
                line: other.as_ref().map_or(default_line, |t| t.line),
                msg: "expected number or 'inf'".to_string(),
            }),
        }
    }

    fn expect_op(&mut self, default_line: usize) -> Result<Comparator, LpError> {
        match self.advance_clone() {
            Some(SpannedTok { tok: Tok::Le, .. }) => Ok(Comparator::Le),
            Some(SpannedTok { tok: Tok::Ge, .. }) => Ok(Comparator::Ge),
            Some(SpannedTok { tok: Tok::Eq, .. }) => Ok(Comparator::Eq),
            other => Err(LpError::Parse {
                line: other.as_ref().map_or(default_line, |t| t.line),
                msg: "expected <=, >=, or =".to_string(),
            }),
        }
    }

    fn expect_word(&mut self, default_line: usize) -> Result<String, LpError> {
        match self.advance_clone() {
            Some(SpannedTok {
                tok: Tok::Word(w), ..
            }) => Ok(w),
            other => Err(LpError::Parse {
                line: other.as_ref().map_or(default_line, |t| t.line),
                msg: "expected identifier".to_string(),
            }),
        }
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

    fn peek(&self) -> Option<&SpannedTok> {
        self.tokens.get(self.pos)
    }

    fn advance_clone(&mut self) -> Option<SpannedTok> {
        let cur = self.tokens.get(self.pos).cloned();
        if cur.is_some() {
            self.pos += 1;
        }
        cur
    }

    fn peek_is_header(&self) -> bool {
        matches!(
            self.tokens.get(self.pos).map(|t| &t.tok),
            Some(Tok::Header(_) | Tok::End)
        )
    }

    fn peek_is_op(&self) -> bool {
        matches!(
            self.tokens.get(self.pos).map(|t| &t.tok),
            Some(Tok::Le | Tok::Ge | Tok::Eq)
        )
    }
}

/// Normalize a row to at most one coefficient per variable. Repeated LP terms
/// are additive, so their sum must remain finite just like an objective
/// coefficient sum.
fn aggregate_constraint_terms(
    terms: Vec<(usize, f64)>,
    line: usize,
) -> Result<Vec<(usize, f64)>, LpError> {
    let mut aggregated = BTreeMap::new();
    for (variable, coefficient) in terms {
        let current = aggregated.get(&variable).copied().unwrap_or(0.0);
        let sum = checked_finite_add(current, coefficient, line, "constraint coefficient sum")?;
        aggregated.insert(variable, sum);
    }
    Ok(aggregated.into_iter().collect())
}

// Unit tests live in `tests/parser_lp.rs` (module budget).
