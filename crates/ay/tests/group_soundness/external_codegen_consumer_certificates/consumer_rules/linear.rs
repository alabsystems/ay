// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The consumer's `la_generic` (Clean's Carcara `linear_arithmetic.rs`):
//! negate each literal, move it to `s >= d` / `s > d` / `s = d` form,
//! strengthen it when every atom is `Int` (scaled by the lcm of the
//! denominators and rounded to the gcd lattice, Clean's fix), multiply by the
//! literal's `:args` coefficient (skipped when 0, Clean's fix), sum, and
//! require `0 op d` to be false with no atom left. An atom whose sort the
//! reader does not know makes the strengthening, and so the step,
//! `Undetermined`.

use std::collections::hash_map::{Entry, HashMap};

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use super::document::Document;
use super::{negation, refuse, require, undecided, Checked, StepInput, Verdict};

#[derive(Default)]
struct LinearComb {
    terms: HashMap<u32, BigRational>,
    constant: BigRational,
}

impl LinearComb {
    fn insert(&mut self, key: u32, value: BigRational) {
        if value.is_zero() {
            return;
        }
        match self.terms.entry(key) {
            Entry::Occupied(mut entry) => {
                *entry.get_mut() += value;
                if entry.get().is_zero() {
                    entry.remove();
                }
            }
            Entry::Vacant(entry) => {
                entry.insert(value);
            }
        }
    }

    fn add_term(&mut self, document: &Document, term: u32, coeff: &BigRational) {
        let args = document.args(term);
        match document.head(term) {
            Some("+") => args
                .iter()
                .for_each(|&arg| self.add_term(document, arg, coeff)),
            Some("-") if args.len() == 1 => self.add_term(document, args[0], &-coeff),
            Some("-") if !args.is_empty() => {
                self.add_term(document, args[0], coeff);
                args[1..]
                    .iter()
                    .for_each(|&arg| self.add_term(document, arg, &-coeff));
            }
            Some("*") if args.len() == 2 => {
                match (fraction(document, args[0]), fraction(document, args[1])) {
                    (None, Some(inner)) => self.add_term(document, args[0], &(inner * coeff)),
                    (Some(inner), _) => self.add_term(document, args[1], &(inner * coeff)),
                    (None, None) => self.insert(term, coeff.clone()),
                }
            }
            _ => match fraction(document, term) {
                Some(value) => self.constant += value * coeff,
                None => self.insert(term, coeff.clone()),
            },
        }
    }

    fn from_term(document: &Document, term: u32) -> Self {
        let mut result = Self::default();
        result.add_term(document, term, &BigRational::one());
        result
    }

    fn add(&mut self, other: Self) {
        for (key, value) in other.terms {
            self.insert(key, value);
        }
        self.constant += other.constant;
    }

    fn scale(&mut self, scalar: &BigRational) {
        if scalar.is_zero() {
            *self = Self::default();
        } else if !scalar.is_one() {
            self.terms.values_mut().for_each(|c| *c *= scalar);
            self.constant *= scalar;
        }
    }
}

/// `as_number`: an integer or decimal constant.
fn number(document: &Document, id: u32) -> Option<BigRational> {
    let text = document.atom_text(id)?;
    let (whole, fraction) = text.split_once('.').unwrap_or((text, ""));
    let digits = |s: &str| s.bytes().all(|b| b.is_ascii_digit());
    if whole.is_empty() || !digits(whole) || !digits(fraction) {
        return None;
    }
    let numerator: BigInt = format!("{whole}{fraction}").parse().ok()?;
    let denominator = num_traits::pow(BigInt::from(10), fraction.len());
    Some(BigRational::new(numerator, denominator))
}

/// `as_signed_number`.
fn signed_number(document: &Document, id: u32) -> Option<BigRational> {
    match document.op(id, "-").as_deref() {
        Some([inner]) => number(document, *inner).map(|r| -r),
        _ => number(document, id),
    }
}

/// `as_fraction`: a signed number, `(/ a b)`, or Euclidean `(div a b)`.
fn fraction(document: &Document, id: u32) -> Option<BigRational> {
    let unsigned = |id: u32| -> Option<BigRational> {
        if let Some([a, b]) = document.op(id, "/").as_deref() {
            let denominator = signed_number(document, *b).filter(|d| !d.is_zero())?;
            return Some(signed_number(document, *a)? / denominator);
        }
        if let Some([a, b]) = document.op(id, "div").as_deref() {
            let (a, b) = (signed_number(document, *a)?, signed_number(document, *b)?);
            if b.is_zero() || !a.is_integer() || !b.is_integer() {
                return None;
            }
            // Euclidean: the remainder is never negative.
            let (a, b) = (a.to_integer(), b.to_integer());
            let floor = BigRational::new(a, b.abs()).floor().to_integer();
            return Some(BigRational::from_integer(floor * b.signum()));
        }
        number(document, id)
    };
    match document.op(id, "-").as_deref() {
        Some([inner]) => unsigned(*inner).map(|r| -r),
        _ => unsigned(id),
    }
}

/// The non-negative greatest common divisor.
fn gcd(a: &BigInt, b: &BigInt) -> BigInt {
    let (mut a, mut b) = (a.abs(), b.abs());
    while !b.is_zero() {
        let r = &a % &b;
        a = b;
        b = r;
    }
    a
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Op {
    Gt,
    Ge,
    Eq,
}

/// Whether `atom` is `Int`: `None` where the reader does not know its sort.
fn is_int(document: &Document, atom: u32) -> Option<bool> {
    let head = document.node(atom);
    if let super::document::Node::List(children) = head {
        if let Some((name, _)) = children.first().and_then(|&h| document.indexed_name(h)) {
            return (name == "@int_of").then_some(true);
        }
    }
    document.declared_sort_is_int(atom)
}

/// One literal's negation in `s op d` form, strengthened, times its argument.
fn literal(
    document: &Document,
    term: u32,
    arg: &BigRational,
) -> Result<Option<(Op, LinearComb)>, Verdict> {
    let negated = negation(document, term).ok();
    let (head, args) = match negated {
        Some(inner) => (
            document.head(inner).map(str::to_string),
            document.args(inner),
        ),
        None => (document.head(term).map(str::to_string), document.args(term)),
    };
    let op = match (negated.is_some(), head.as_deref()) {
        (true, Some(op @ (">=" | "<=" | ">" | "<" | "="))) => op.to_string(),
        (false, Some("<")) => ">=".to_string(),
        (false, Some(">")) => "<=".to_string(),
        (false, Some("<=")) => ">".to_string(),
        (false, Some(">=")) => "<".to_string(),
        _ => return refuse("not a disequality"),
    };
    let [s1, s2] = args[..] else {
        return refuse("not a binary disequality");
    };
    let mut combination = LinearComb::from_term(document, s1);
    let mut right = LinearComb::from_term(document, s2);
    right.scale(&-BigRational::one());
    combination.add(right);
    combination.constant = -combination.constant.clone();
    let mut op = match op.as_str() {
        ">" => Op::Gt,
        ">=" => Op::Ge,
        "<" => {
            combination.scale(&-BigRational::one());
            Op::Gt
        }
        "<=" => {
            combination.scale(&-BigRational::one());
            Op::Ge
        }
        _ => Op::Eq,
    };
    if arg.is_zero() {
        return Ok(None);
    }
    if op != Op::Eq {
        let ints: Option<Vec<bool>> = combination
            .terms
            .keys()
            .map(|&atom| is_int(document, atom))
            .collect();
        let Some(ints) = ints else {
            return undecided("an atom's sort is not inferred");
        };
        if ints.iter().all(|&int| int) {
            let lcm = combination.terms.values().fold(BigInt::one(), |acc, c| {
                let g = gcd(&acc, c.denom());
                &acc * c.denom() / g
            });
            let lcm = BigRational::from_integer(lcm);
            let gcd = combination
                .terms
                .values()
                .fold(BigInt::zero(), |acc, c| gcd(&acc, (c * &lcm).numer()));
            let gcd = BigRational::from_integer(if gcd.is_zero() { BigInt::one() } else { gcd });
            let quotient = &combination.constant * &lcm / &gcd;
            let rounded = if op == Op::Gt {
                quotient.floor() + BigRational::one()
            } else {
                quotient.ceil()
            };
            combination.constant = rounded * gcd / lcm;
            op = Op::Ge;
        }
    }
    combination.scale(&if op == Op::Eq { arg.clone() } else { arg.abs() });
    Ok(Some((op, combination)))
}

pub(super) fn la_generic(document: &mut Document, input: &StepInput) -> Checked {
    require(input.args.len() == input.conclusion.len(), || {
        "not one argument per literal".to_string()
    })?;
    let mut sum = LinearComb::default();
    let mut op = Op::Eq;
    for (&term, &arg) in input.conclusion.iter().zip(&input.args) {
        let Some(arg) = fraction(document, arg) else {
            return refuse("an argument is not a number");
        };
        if let Some((literal_op, combination)) = literal(document, term, &arg)? {
            sum.add(combination);
            op = match (op, literal_op) {
                (Op::Gt, _) | (_, Op::Gt) => Op::Gt,
                (Op::Ge, _) | (_, Op::Ge) => Op::Ge,
                _ => Op::Eq,
            };
        }
    }
    // Whether `0 op d` holds, as the consumer reads it.
    let zero = BigRational::zero();
    let holds = match zero.cmp(&sum.constant) {
        std::cmp::Ordering::Less => false,
        std::cmp::Ordering::Equal => matches!(op, Op::Ge | Op::Eq),
        std::cmp::Ordering::Greater => matches!(op, Op::Gt | Op::Ge),
    };
    require(sum.terms.is_empty() && !holds, || {
        "the combination is not a contradiction".to_string()
    })
}
