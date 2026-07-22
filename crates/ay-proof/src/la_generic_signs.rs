// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Carcara-faithful signing of Alethe `la_generic` coefficients, computed over
//! the **printed** atom strings (exactly what an external checker parses).
//!
//! The internal certificate keeps non-negative Farkas magnitudes and lets the
//! validator search either orientation of each equality. Alethe's `la_generic`
//! has no such search: the printed equality coefficient is signed, and the
//! checker forms the single linear combination the args dictate, reading atoms
//! from the printed proof. AY's printer applies surface-syntax overrides that
//! may reorient an equality (e.g. `(= (* 2 r2) -7)` is printed
//! `(= (- (* 2 r2)) 7)`), so resolving signs from the INTERNAL term orientation
//! can disagree with the printed orientation the checker actually sees.
//!
//! This module parses the linear form out of the printed strings and searches
//! the equality signs against a SOUND reconstruction of Carcara's acceptance
//! test:
//!   - each hypothesis `¬(clause literal)` normalizes to `e >= 0` / `e > 0`
//!     (inequality) or `e = 0` (equality), `e` in the `lhs - rhs` orientation;
//!   - inequality coefficients are applied in magnitude (Carcara fixes the
//!     inequality orientation, ignoring the printed sign), equalities signed;
//!   - the step is accepted iff the weighted sum eliminates every variable and
//!     leaves a STRICTLY NEGATIVE constant — a contradiction under both `>= 0`
//!     and `> 0`, and one that survives integer strengthening, so the check
//!     never false-accepts (a `= 0`-constant strict combination is soundly but
//!     conservatively rejected).
//!
//! Emission-only: this changes only the printed coefficients of an
//! already-decided UNSAT proof; it never affects a verdict, and it substitutes
//! a repaired vector only when the sound check accepts it.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_rational::{BigRational, Rational64};
use num_traits::{One, Signed, Zero};

/// A linear form over printed variable names plus a rational constant.
#[derive(Clone, Debug, Default)]
struct Lin {
    coeffs: BTreeMap<String, BigRational>,
    constant: BigRational,
}

impl Lin {
    fn constant(c: BigRational) -> Self {
        Self {
            coeffs: BTreeMap::new(),
            constant: c,
        }
    }

    fn var(name: String) -> Self {
        let mut coeffs = BTreeMap::new();
        coeffs.insert(name, BigRational::one());
        Self {
            coeffs,
            constant: BigRational::zero(),
        }
    }

    fn is_constant(&self) -> bool {
        self.coeffs.is_empty()
    }

    fn add_scaled(&mut self, other: &Lin, scale: &BigRational) {
        if scale.is_zero() {
            return;
        }
        self.constant += scale * &other.constant;
        for (v, c) in &other.coeffs {
            let entry = self
                .coeffs
                .entry(v.clone())
                .or_insert_with(BigRational::zero);
            *entry += scale * c;
            if entry.is_zero() {
                self.coeffs.remove(v);
            }
        }
    }

    fn scale(&mut self, s: &BigRational) {
        if s.is_one() {
            return;
        }
        self.constant *= s;
        if s.is_zero() {
            self.coeffs.clear();
            return;
        }
        for c in self.coeffs.values_mut() {
            *c *= s;
        }
    }

    fn negate(&mut self) {
        self.constant = -std::mem::take(&mut self.constant);
        for c in self.coeffs.values_mut() {
            *c = -std::mem::take(c);
        }
    }
}

/// Split the top-level whitespace-separated s-expression tokens/subforms of
/// `s` (an already-trimmed expression). `(f a b)` yields `["f", "a", "b"]`,
/// respecting nested parentheses; a bare atom yields the atom itself.
fn split_sexpr(s: &str) -> Option<Vec<String>> {
    let s = s.trim();
    if !s.starts_with('(') {
        return Some(vec![s.to_string()]);
    }
    if !s.ends_with(')') {
        return None;
    }
    let inner = &s[1..s.len() - 1];
    let mut parts = Vec::new();
    let mut depth = 0i32;
    let mut cur = String::new();
    for ch in inner.chars() {
        match ch {
            '(' => {
                depth += 1;
                cur.push(ch);
            }
            ')' => {
                depth -= 1;
                if depth < 0 {
                    return None;
                }
                cur.push(ch);
            }
            c if c.is_whitespace() && depth == 0 => {
                if !cur.is_empty() {
                    parts.push(std::mem::take(&mut cur));
                }
            }
            c => cur.push(c),
        }
    }
    if depth != 0 {
        return None;
    }
    if !cur.is_empty() {
        parts.push(cur);
    }
    Some(parts)
}

/// Parse a decimal / integer numeral token (`7.0`, `-5`, `45.0`) into a
/// rational, or `None` if it is not a numeral (i.e. a variable name).
fn parse_numeral(tok: &str) -> Option<BigRational> {
    let (neg, body) = match tok.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, tok),
    };
    if body.is_empty() {
        return None;
    }
    let val = if let Some(dot) = body.find('.') {
        let int_part = &body[..dot];
        let frac_part = &body[dot + 1..];
        if !int_part.chars().all(|c| c.is_ascii_digit())
            || !frac_part.chars().all(|c| c.is_ascii_digit())
        {
            return None;
        }
        let combined = format!("{int_part}{frac_part}");
        let numer: BigInt = combined.parse().ok()?;
        let denom = BigInt::from(10u32).pow(frac_part.len() as u32);
        BigRational::new(numer, denom)
    } else {
        if !body.chars().all(|c| c.is_ascii_digit()) {
            return None;
        }
        BigRational::from(body.parse::<BigInt>().ok()?)
    };
    Some(if neg { -val } else { val })
}

/// Parse a printed arithmetic term string into a linear form. Any subterm the
/// grammar does not linearize (an uninterpreted application, `mod`, `select`,
/// …) becomes an opaque variable keyed by its exact printed string — matching
/// how an external checker treats it as an atom.
fn parse_lin(s: &str) -> Option<Lin> {
    let s = s.trim();
    if !s.starts_with('(') {
        return Some(match parse_numeral(s) {
            Some(r) => Lin::constant(r),
            None => Lin::var(s.to_string()),
        });
    }
    let parts = split_sexpr(s)?;
    if parts.is_empty() {
        return None;
    }
    let op = parts[0].as_str();
    let args = &parts[1..];
    match op {
        "+" => {
            let mut acc = Lin::default();
            for a in args {
                acc.add_scaled(&parse_lin(a)?, &BigRational::one());
            }
            Some(acc)
        }
        "-" if args.len() == 1 => {
            let mut e = parse_lin(&args[0])?;
            e.negate();
            Some(e)
        }
        "-" if args.len() >= 2 => {
            let mut acc = parse_lin(&args[0])?;
            for a in &args[1..] {
                let mut sub = parse_lin(a)?;
                sub.negate();
                acc.add_scaled(&sub, &BigRational::one());
            }
            Some(acc)
        }
        "*" => {
            let mut const_part = BigRational::one();
            let mut non_const: Option<Lin> = None;
            for a in args {
                let sub = parse_lin(a)?;
                if sub.is_constant() {
                    const_part *= sub.constant;
                } else if non_const.is_none() {
                    non_const = Some(sub);
                } else {
                    // Non-linear product: treat the whole term as opaque.
                    return Some(Lin::var(s.to_string()));
                }
            }
            Some(match non_const {
                Some(mut e) => {
                    e.scale(&const_part);
                    e
                }
                None => Lin::constant(const_part),
            })
        }
        "/" if args.len() == 2 => {
            let mut num = parse_lin(&args[0])?;
            let den = parse_lin(&args[1])?;
            if den.is_constant() && !den.constant.is_zero() {
                let inv = BigRational::one() / den.constant;
                num.scale(&inv);
                Some(num)
            } else {
                Some(Lin::var(s.to_string()))
            }
        }
        _ => Some(Lin::var(s.to_string())),
    }
}

/// The normalized hypothesis for one conflict literal (`printed` atom asserted
/// with truth value `value`): `(e, strict, is_equality)` with the hypothesis
/// equivalent to `e >= 0` / `e > 0` / `e = 0`, `e` in `lhs - rhs` orientation.
/// `None` for a disequality or a non-arithmetic / unparseable atom.
fn hypothesis(printed: &str, value: bool) -> Option<(Lin, bool, bool)> {
    let mut s = printed.trim().to_string();
    let mut value = value;
    // Strip leading `(not ...)`, flipping polarity.
    loop {
        let parts = split_sexpr(&s)?;
        if parts.len() == 2 && parts[0] == "not" {
            s = parts[1].clone();
            value = !value;
        } else {
            break;
        }
    }
    let parts = split_sexpr(&s)?;
    if parts.len() != 3 {
        return None;
    }
    let pred = parts[0].as_str();
    let lhs = parse_lin(&parts[1])?;
    let rhs = parse_lin(&parts[2])?;
    let l_minus_r = {
        let mut e = lhs.clone();
        e.add_scaled(&rhs, &BigRational::from(BigInt::from(-1)));
        e
    };
    let r_minus_l = {
        let mut e = rhs;
        e.add_scaled(&lhs, &BigRational::from(BigInt::from(-1)));
        e
    };
    match (pred, value) {
        ("=", true) => Some((l_minus_r, false, true)),
        ("<=", true) | (">", false) => Some((r_minus_l, false, false)),
        ("<", true) | (">=", false) => Some((r_minus_l, true, false)),
        (">=", true) | ("<", false) => Some((l_minus_r, false, false)),
        (">", true) | ("<=", false) => Some((l_minus_r, true, false)),
        _ => None,
    }
}

fn to_big(r: &Rational64) -> BigRational {
    BigRational::new(BigInt::from(*r.numer()), BigInt::from(*r.denom()))
}

/// SOUND reconstruction of Carcara's `la_generic` acceptance test over the
/// printed hypotheses for the given signed coefficient vector.
fn coeffs_valid(hyps: &[(Lin, bool, bool)], coeffs: &[Rational64]) -> bool {
    if hyps.len() != coeffs.len() {
        return false;
    }
    let mut sum = Lin::default();
    for ((expr, _strict, is_eq), &c) in hyps.iter().zip(coeffs.iter()) {
        let scale = if *is_eq { c } else { c.abs() };
        if scale.is_zero() {
            continue;
        }
        sum.add_scaled(expr, &to_big(&scale));
    }
    sum.coeffs.is_empty() && sum.constant < BigRational::zero()
}

/// Choose the coefficient vector to PRINT for an Alethe `la_generic` step whose
/// clause literals print as `printed_atoms` (`(printed_atom, truth_value)`,
/// matching how the printer reconstructs the conflict). `existing` is the
/// signs-from-internal-orientation candidate; it is kept byte-identical when an
/// external checker already accepts it. Otherwise the equality signs are
/// repaired (inequalities emitted in magnitude) so the checker accepts, using
/// `magnitudes` (the non-negative Farkas coefficients). Falls back to
/// `existing` when the atoms cannot be parsed, there are too many equalities to
/// enumerate, or no sign choice validates — so the result never regresses a
/// currently-valid certificate and never fabricates a "fixed" invalid one.
#[must_use]
pub(crate) fn resolve_printed_la_generic_coefficients(
    printed_atoms: &[(String, bool)],
    existing: &[Rational64],
    magnitudes: &[Rational64],
) -> Vec<Rational64> {
    let existing = existing.to_vec();
    if printed_atoms.len() != existing.len() || magnitudes.len() != existing.len() {
        return existing;
    }
    let mut hyps: Vec<(Lin, bool, bool)> = Vec::with_capacity(printed_atoms.len());
    for (atom, value) in printed_atoms {
        match hypothesis(atom, *value) {
            Some(h) => hyps.push(h),
            None => return existing, // unparseable / disequality: keep current behavior
        }
    }
    if coeffs_valid(&hyps, &existing) {
        return existing;
    }
    let eq_indices: Vec<usize> = hyps
        .iter()
        .enumerate()
        .filter_map(|(i, (_e, _s, is_eq))| if *is_eq { Some(i) } else { None })
        .collect();
    if eq_indices.len() > 16 {
        return existing;
    }
    let base: Vec<Rational64> = magnitudes.iter().map(|c| c.abs()).collect();
    for mask in 0u32..(1u32 << eq_indices.len()) {
        let mut candidate = base.clone();
        for (bit, &ei) in eq_indices.iter().enumerate() {
            if mask & (1u32 << bit) != 0 {
                candidate[ei] = -candidate[ei];
            }
        }
        if coeffs_valid(&hyps, &candidate) {
            return candidate;
        }
    }
    existing
}

#[cfg(test)]
#[path = "la_generic_signs_tests.rs"]
mod la_generic_signs_tests;
