// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Version-independent oracle for the objectives AY prints.
//!
//! The differential half of this gate trusts z3's OPTIMIZER, and only the
//! releases the deviation classes were measured against deserve that trust.
//! This half trusts nothing but z3's QF_LRA SATISFIABILITY answers, which every
//! z3 release gets right on these tiny instances: each printed optimum is
//! re-derived from its definition.
//!
//! For `maximize v` over the constraints `C` (minimize is the mirror image):
//!
//! * `c` (attained): `C ∧ v = c` is sat and `C ∧ v > c` is unsat.
//! * `c - ε` (supremum `c`, not attained): `C ∧ v ≥ c` is unsat and
//!   `cl(C) ∧ v = c` is sat, where `cl(C)` relaxes every strict bound. For a
//!   nonempty `C` the relaxation IS the topological closure, so a point of
//!   `cl(C)` at `v = c` is a limit of points of `C` and `c` is the supremum.
//! * `oo`: `C ∧ v > 1000` is sat. A generated instance has at most four
//!   constraints over at most three variables with constants in `[-10, 10]`,
//!   so every finite optimum lies within `±40`; exceeding 1000 proves the
//!   objective unbounded.
//!
//! A lexicographic successor is checked under the equalities fixing every
//! predecessor at its attained optimum. After a predecessor with no attained
//! optimum AY must print no successor at all (it refuses that suffix,
//! deviation class 3); a printed one is wrong.

use super::{run_z3, Instance};

/// Why [`check_objectives`] rejected a printed objectives block.
#[derive(Debug)]
pub(super) enum ObjectiveError {
    /// A printed value is not the optimum its definition names, or a
    /// lexicographic successor follows a predecessor with no attained optimum.
    Wrong(String),
    /// The block is missing, has the wrong number of lines, or a line does
    /// not parse.
    Malformed(String),
    /// z3's satisfiability check answered neither `sat` nor `unsat`.
    Undecided(String),
}

/// Checks every objective a solver printed for a `sat` instance. Returns how
/// many objectives were checked, or why the block is rejected.
pub(super) fn check_objectives(
    instance: &Instance,
    out: &[String],
) -> Result<usize, ObjectiveError> {
    let lines: Vec<&str> = out
        .iter()
        .map(String::as_str)
        .skip_while(|line| *line != "(objectives")
        .skip(1)
        .take_while(|line| *line != ")")
        .collect();
    if lines.len() != instance.objectives.len() {
        return Err(ObjectiveError::Malformed(format!(
            "{} objective(s) printed for {} declared",
            lines.len(),
            instance.objectives.len()
        )));
    }
    let mut fixed = Vec::new();
    let mut checked = 0;
    for (line, (maximize, var)) in lines.iter().zip(&instance.objectives) {
        let value = parse_objective_line(line, var).ok_or_else(|| {
            ObjectiveError::Malformed(format!("unparseable objective line {line:?}"))
        })?;
        check_one(instance, &fixed, *maximize, var, &value).map_err(|error| match error {
            ObjectiveError::Wrong(why) => {
                ObjectiveError::Wrong(format!("{line:?} is not the optimum: {why}"))
            }
            other => other,
        })?;
        checked += 1;
        if instance.box_mode {
            continue;
        }
        if !(value.eps.is_zero() && value.inf.is_zero()) {
            if checked < lines.len() {
                return Err(ObjectiveError::Wrong(format!(
                    "{line:?} is unattained, yet a lexicographic successor was \
                     printed: the contract (deviation class 3) is to refuse that suffix"
                )));
            }
            break;
        }
        fixed.push(format!("(= {var} {})", value.finite.smt()));
    }
    Ok(checked)
}

fn check_one(
    instance: &Instance,
    fixed: &[String],
    maximize: bool,
    var: &str,
    value: &ObjValue,
) -> Result<(), ObjectiveError> {
    let beyond = if maximize { ">" } else { "<" };
    let decide = |relaxed: bool, extra: String| {
        let mut asserted = fixed.to_vec();
        asserted.push(extra.clone());
        decide_sat(instance, relaxed, &asserted)
            .ok_or_else(|| ObjectiveError::Undecided(format!("z3 did not decide {extra}")))
    };
    let expect = |relaxed: bool, extra: String, sat: bool| -> Result<(), ObjectiveError> {
        if decide(relaxed, extra.clone())? == sat {
            Ok(())
        } else {
            let closure = if relaxed { " (closure)" } else { "" };
            let answer = if sat { "unsat" } else { "sat" };
            Err(ObjectiveError::Wrong(format!(
                "{extra}{closure} is {answer}"
            )))
        }
    };
    if !value.inf.is_zero() {
        let toward = if maximize {
            value.inf.num > 0
        } else {
            value.inf.num < 0
        };
        if !toward || !value.finite.is_zero() || !value.eps.is_zero() {
            return Err(ObjectiveError::Wrong(
                "an infinite optimum on the wrong side".to_string(),
            ));
        }
        let far = if maximize { "1000.0" } else { "(- 1000.0)" };
        return expect(false, format!("({beyond} {var} {far})"), true);
    }
    let bound = value.finite.smt();
    if value.eps.is_zero() {
        expect(false, format!("(= {var} {bound})"), true)?;
        return expect(false, format!("({beyond} {var} {bound})"), false);
    }
    let toward = if maximize {
        value.eps.num < 0
    } else {
        value.eps.num > 0
    };
    if !toward {
        return Err(ObjectiveError::Wrong(
            "an epsilon offset pointing out of the feasible region".to_string(),
        ));
    }
    expect(false, format!("({beyond}= {var} {bound})"), false)?;
    expect(true, format!("(= {var} {bound})"), true)
}

/// `Some(true)` for sat, `Some(false)` for unsat, from z3's satisfiability
/// check alone (never its optimizer).
fn decide_sat(instance: &Instance, relaxed: bool, extra: &[String]) -> Option<bool> {
    let mut script = instance.declarations.clone();
    for constraint in &instance.constraints {
        script.push_str(&format!("(assert {})\n", constraint.render(relaxed)));
    }
    for assertion in extra {
        script.push_str(&format!("(assert {assertion})\n"));
    }
    script.push_str("(check-sat)\n");
    match run_z3(&script)
        .lines()
        .map(str::trim)
        .find(|l| !l.is_empty())
    {
        Some("sat") => Some(true),
        Some("unsat") => Some(false),
        _ => None,
    }
}

/// An exact rational, always reduced with a positive denominator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Rational {
    num: i128,
    den: i128,
}

impl Rational {
    const ZERO: Self = Self { num: 0, den: 1 };
    const ONE: Self = Self { num: 1, den: 1 };

    fn new(num: i128, den: i128) -> Option<Self> {
        if den == 0 {
            return None;
        }
        let mut gcd = (num.unsigned_abs(), den.unsigned_abs());
        while gcd.1 != 0 {
            gcd = (gcd.1, gcd.0 % gcd.1);
        }
        let divisor = i128::try_from(gcd.0.max(1)).ok()? * den.signum();
        Some(Self {
            num: num / divisor,
            den: den / divisor,
        })
    }

    fn add(self, other: Self) -> Option<Self> {
        let num = self
            .num
            .checked_mul(other.den)?
            .checked_add(other.num.checked_mul(self.den)?)?;
        Self::new(num, self.den.checked_mul(other.den)?)
    }

    fn mul(self, other: Self) -> Option<Self> {
        Self::new(
            self.num.checked_mul(other.num)?,
            self.den.checked_mul(other.den)?,
        )
    }

    fn neg(self) -> Self {
        Self {
            num: -self.num,
            den: self.den,
        }
    }

    fn is_zero(self) -> bool {
        self.num == 0
    }

    /// An SMT-LIB `Real` term denoting this value.
    fn smt(self) -> String {
        let magnitude = format!("(/ {}.0 {}.0)", self.num.unsigned_abs(), self.den);
        if self.num < 0 {
            format!("(- {magnitude})")
        } else {
            magnitude
        }
    }
}

/// `finite + eps·ε + inf·oo`, the shape of every printed objective value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ObjValue {
    finite: Rational,
    eps: Rational,
    inf: Rational,
}

impl ObjValue {
    fn constant(finite: Rational) -> Self {
        Self {
            finite,
            eps: Rational::ZERO,
            inf: Rational::ZERO,
        }
    }

    fn is_constant(&self) -> bool {
        self.eps.is_zero() && self.inf.is_zero()
    }

    fn add(self, other: Self) -> Option<Self> {
        Some(Self {
            finite: self.finite.add(other.finite)?,
            eps: self.eps.add(other.eps)?,
            inf: self.inf.add(other.inf)?,
        })
    }

    fn scale(self, factor: Rational) -> Option<Self> {
        Some(Self {
            finite: self.finite.mul(factor)?,
            eps: self.eps.mul(factor)?,
            inf: self.inf.mul(factor)?,
        })
    }
}

enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

/// ` (x1 (+ 2 (* (- 1) epsilon)))` naming `var` -> its value.
fn parse_objective_line(line: &str, var: &str) -> Option<ObjValue> {
    let mut tokens = line
        .replace('(', " ( ")
        .replace(')', " ) ")
        .split_whitespace()
        .map(str::to_string)
        .collect::<Vec<_>>()
        .into_iter()
        .peekable();
    let Sexp::List(items) = parse_sexp(&mut tokens)? else {
        return None;
    };
    if tokens.next().is_some() {
        return None;
    }
    match items.as_slice() {
        [Sexp::Atom(name), value] if name == var => eval(value),
        _ => None,
    }
}

fn parse_sexp(tokens: &mut std::iter::Peekable<std::vec::IntoIter<String>>) -> Option<Sexp> {
    let token = tokens.next()?;
    match token.as_str() {
        "(" => {
            let mut items = Vec::new();
            while tokens.peek()? != ")" {
                items.push(parse_sexp(tokens)?);
            }
            tokens.next();
            Some(Sexp::List(items))
        }
        ")" => None,
        _ => Some(Sexp::Atom(token)),
    }
}

fn eval(sexp: &Sexp) -> Option<ObjValue> {
    match sexp {
        Sexp::Atom(atom) => match atom.as_str() {
            "epsilon" => Some(ObjValue {
                eps: Rational::ONE,
                ..ObjValue::constant(Rational::ZERO)
            }),
            "oo" => Some(ObjValue {
                inf: Rational::ONE,
                ..ObjValue::constant(Rational::ZERO)
            }),
            numeral => parse_numeral(numeral).map(ObjValue::constant),
        },
        Sexp::List(items) => match items.as_slice() {
            [Sexp::Atom(op), operand] if op == "-" => eval(operand)?.scale(Rational::ONE.neg()),
            [Sexp::Atom(op), lhs, rhs] if op == "-" => {
                eval(lhs)?.add(eval(rhs)?.scale(Rational::ONE.neg())?)
            }
            [Sexp::Atom(op), operands @ ..] if op == "+" && !operands.is_empty() => operands
                .iter()
                .try_fold(ObjValue::constant(Rational::ZERO), |sum, operand| {
                    sum.add(eval(operand)?)
                }),
            [Sexp::Atom(op), lhs, rhs] if op == "*" => {
                let (lhs, rhs) = (eval(lhs)?, eval(rhs)?);
                if lhs.is_constant() {
                    rhs.scale(lhs.finite)
                } else if rhs.is_constant() {
                    lhs.scale(rhs.finite)
                } else {
                    None
                }
            }
            [Sexp::Atom(op), lhs, rhs] if op == "/" => {
                let (lhs, rhs) = (eval(lhs)?, eval(rhs)?);
                if !lhs.is_constant() || !rhs.is_constant() || rhs.finite.is_zero() {
                    return None;
                }
                let inverse = Rational::new(rhs.finite.den, rhs.finite.num)?;
                Some(ObjValue::constant(lhs.finite.mul(inverse)?))
            }
            _ => None,
        },
    }
}

/// `12` or `1.25` (the normalized output drops a bare `.0`).
fn parse_numeral(text: &str) -> Option<Rational> {
    let (whole, fraction) = text.split_once('.').unwrap_or((text, ""));
    if whole.is_empty() || !(whole.bytes().chain(fraction.bytes())).all(|b| b.is_ascii_digit()) {
        return None;
    }
    let digits: i128 = format!("{whole}{fraction}").parse().ok()?;
    let scale = 10i128.checked_pow(u32::try_from(fraction.len()).ok()?)?;
    Rational::new(digits, scale)
}

#[test]
fn objective_values_parse_into_exact_linear_forms() {
    let value = |line: &str| parse_objective_line(line, "x").expect(line);
    let q = |num, den| Rational::new(num, den).unwrap();
    let eps = |finite, eps| ObjValue {
        eps,
        ..ObjValue::constant(finite)
    };
    assert_eq!(value(" (x 9)"), ObjValue::constant(q(9, 1)));
    assert_eq!(value(" (x (- (/ 3 2)))"), ObjValue::constant(q(-3, 2)));
    assert_eq!(value(" (x 1.25)"), ObjValue::constant(q(5, 4)));
    assert_eq!(
        value(" (x (+ 2 (* (- 1) epsilon)))"),
        eps(q(2, 1), q(-1, 1))
    );
    assert_eq!(
        value(" (x (+ (- (/ 3 2)) epsilon))"),
        eps(q(-3, 2), q(1, 1))
    );
    assert_eq!(value(" (x epsilon)"), eps(Rational::ZERO, q(1, 1)));
    assert_eq!(value(" (x (* (- 1) oo))").inf, q(-1, 1));
    assert!(parse_objective_line(" (y 1)", "x").is_none());
    assert!(parse_objective_line(" (x (* epsilon oo))", "x").is_none());
}
