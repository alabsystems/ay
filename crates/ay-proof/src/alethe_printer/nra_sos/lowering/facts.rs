// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The nonnegative products and squares of an SOS certificate as checked
//! Alethe clauses. Pinned carcara multiplies a comparison only by a STRICTLY
//! signed term (`la_mult_pos` needs `(> m 0)`, `la_mult_neg` `(< m 0)`), so a
//! factor that may be zero is split on its sign: in the zero case the product
//! is bounded through the shifted multiplier `B + 1 > 0`, whose product with
//! `A >= 0` is `A·B + A >= 0`, and `A <= 0` then gives `A·B >= 0`.

use super::emit::{negated, Emitter, Multiplier};
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

/// One inequality source as an oriented factor: `oriented >= 0`, or `> 0`
/// when `strict`, with `fact` its printed comparison.
pub(super) struct Factor {
    pub(super) oriented: String,
    pub(super) strict: bool,
    pub(super) fact: String,
}

/// A derived nonnegativity literal and the step whose clause concludes it
/// from the factors' facts.
pub(super) struct Derived {
    pub(super) literal: String,
    pub(super) step: String,
}

/// `(cl (not Ga) (not Gb) P)` with `P` the product of the two factors
/// compared against zero: `(> ..)` when both are strict, `(>= ..)` otherwise.
pub(super) fn product(emitter: &mut Emitter, left: &Factor, right: &Factor) -> Option<Derived> {
    let zero = emitter.zero();
    // A strict factor is itself the positive multiplier the rule needs.
    let (multiplier, scaled) = match (left.strict, right.strict) {
        (true, _) => (left, right),
        (false, true) => (right, left),
        (false, false) => return nonstrict_product(emitter, left, right),
    };
    let relation = if scaled.strict { ">" } else { ">=" };
    let (m, s) = (&multiplier.oriented, &scaled.oriented);
    let literal = format!("({relation} (* {m} {s}) (* {m} {zero}))");
    let step = emitter.multiply(
        Multiplier::Positive,
        &multiplier.fact,
        &scaled.fact,
        &literal,
    )?;
    Some(Derived { literal, step })
}

/// Both factors may be zero: split on `A > 0`.
fn nonstrict_product(emitter: &mut Emitter, left: &Factor, right: &Factor) -> Option<Derived> {
    let (zero, one) = (emitter.zero(), emitter.one());
    let (a, b) = (&left.oriented, &right.oriented);
    let positive = format!("(> {a} {zero})");
    let literal = format!("(>= (* {a} {b}) (* {a} {zero}))");
    let when_positive = emitter.multiply(Multiplier::Positive, &positive, &right.fact, &literal)?;
    let shifted = format!("(+ {b} {one})");
    let shifted_positive = format!("(> {shifted} {zero})");
    let shifted_product = format!("(>= (* {shifted} {a}) (* {shifted} {zero}))");
    let shifted_step = emitter.multiply(
        Multiplier::Positive,
        &shifted_positive,
        &left.fact,
        &shifted_product,
    )?;
    let shift = emitter.la_generic(vec![
        (negated(&right.fact), BigRational::one()),
        (shifted_positive, BigRational::one()),
    ])?;
    let otherwise = emitter.la_generic(vec![
        (positive, BigRational::one()),
        (negated(&shifted_product), BigRational::one()),
        (literal.clone(), BigRational::one()),
    ])?;
    let mut premises = vec![otherwise.name, when_positive, shifted_step, shift.name];
    premises.extend(otherwise.equalities);
    let step = emitter.resolution(
        &[negated(&left.fact), negated(&right.fact), literal.clone()],
        &premises,
    )?;
    Some(Derived { literal, step })
}

/// `(cl P)` for `P = (>= (* L L) (* L 0))`: split on the sign of `L`.
pub(super) fn square(emitter: &mut Emitter, form: &str) -> Option<Derived> {
    let (zero, one) = (emitter.zero(), emitter.one());
    let positive = format!("(> {form} {zero})");
    let negative = format!("(< {form} {zero})");
    let nonnegative = format!("(>= {form} {zero})");
    let strict = format!("(> (* {form} {form}) (* {form} {zero}))");
    let literal = format!("(>= (* {form} {form}) (* {form} {zero}))");
    let when_positive = emitter.multiply(Multiplier::Positive, &positive, &positive, &strict)?;
    let when_negative = emitter.multiply(Multiplier::Negative, &negative, &negative, &strict)?;
    let shifted = format!("(+ {form} {one})");
    let shifted_positive = format!("(> {shifted} {zero})");
    let shifted_product = format!("(>= (* {shifted} {form}) (* {shifted} {zero}))");
    let shifted_step = emitter.multiply(
        Multiplier::Positive,
        &shifted_positive,
        &nonnegative,
        &shifted_product,
    )?;
    let shift = emitter.la_generic(vec![
        (negative.clone(), BigRational::one()),
        (shifted_positive, BigRational::one()),
    ])?;
    let split = emitter.la_generic(vec![
        (negative.clone(), BigRational::one()),
        (nonnegative, BigRational::one()),
    ])?;
    let when_nonnegative = emitter.resolution(
        &[negative, shifted_product.clone()],
        &[shifted_step, shift.name, split.name],
    )?;
    let weaken = emitter.la_generic(vec![
        (negated(&strict), BigRational::one()),
        (literal.clone(), BigRational::one()),
    ])?;
    let otherwise = emitter.la_generic(vec![
        (positive, BigRational::one()),
        (negated(&shifted_product), BigRational::one()),
        (literal.clone(), BigRational::one()),
    ])?;
    let mut premises = vec![
        otherwise.name,
        when_nonnegative,
        when_negative,
        when_positive,
        weaken.name,
    ];
    premises.extend(otherwise.equalities);
    let step = emitter.resolution(std::slice::from_ref(&literal), &premises)?;
    Some(Derived { literal, step })
}

/// The Gram matrix as `Σ weight·(Σ form_j·basis_j)²`: the exact Schur
/// elimination the strict checker's PSD test performs, read as `L·D·Lᵀ`.
/// `None` where that test refuses (a negative pivot, a zero pivot with a
/// nonzero tail).
pub(super) fn gram_squares(
    gram: &[Vec<BigRational>],
) -> Option<Vec<(BigRational, Vec<BigRational>)>> {
    let mut work = gram.to_vec();
    let mut squares = Vec::new();
    for pivot_index in 0..work.len() {
        let (done, rest) = work.split_at_mut(pivot_index + 1);
        let pivot_row = done.last()?;
        let pivot = pivot_row.get(pivot_index)?.clone();
        if pivot.is_negative() {
            return None;
        }
        let tail = pivot_row.get(pivot_index + 1..)?;
        if pivot.is_zero() {
            let column_is_zero = rest
                .iter()
                .all(|row| row.get(pivot_index).is_some_and(Zero::is_zero));
            if !column_is_zero || tail.iter().any(|value| !value.is_zero()) {
                return None;
            }
            continue;
        }
        let mut form = vec![BigRational::zero(); pivot_index];
        form.push(BigRational::one());
        form.extend(tail.iter().map(|value| value / &pivot));
        for row in rest.iter_mut() {
            let factor = row.get(pivot_index)? / &pivot;
            if factor.is_zero() {
                continue;
            }
            for (target, source) in row.iter_mut().zip(pivot_row).skip(pivot_index + 1) {
                *target -= &factor * source;
            }
        }
        squares.push((pivot, form));
    }
    Some(squares)
}

/// Scale a square's form to integer coefficients: `w·f² = (w/s²)·(s·f)²`.
pub(super) fn integral(
    weight: BigRational,
    form: Vec<BigRational>,
) -> (BigRational, Vec<BigRational>) {
    let scale = form.iter().fold(num_bigint::BigInt::one(), |acc, value| {
        acc.lcm(value.denom())
    });
    let scale = BigRational::from_integer(scale);
    let weight = weight / (&scale * &scale);
    (
        weight,
        form.into_iter().map(|value| value * &scale).collect(),
    )
}
