// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `evaluate` as pinned Carcara reads the PRINTED step.
//!
//! [`validate_ground_evaluate`] compares values over the term store, where
//! `-4` and `(- 4)` are one constant. Pinned Carcara 1.1.0 (git 9a352ee)
//! evaluates the left side and compares it with the printed right side
//! SYNTACTICALLY, so the value must be spelled as a literal it reads: `4`,
//! `-4`, `4.0`, `-2.5`. MEASURED: `(= (+ (- 2) (- 2)) (- 4)) :rule evaluate`
//! fails ("expected terms to be equal: '-4' and '(- 4)'"), and a value with no
//! finite decimal has no literal at all ("'-1/3' and '(- (/ 1.0 3.0))'").
//! The printer-facing validator therefore also asks that the value HAVE a
//! literal; the printer spells it (`alethe_printer::evaluate_literal`), so a
//! step this accepts is one Carcara checks, and one it refuses is never
//! printed as `evaluate`.

use super::ground_evaluate::validate_ground_evaluate;
use super::ProofCheckError;
use ay_core::{Constant, ProofId, Symbol, TermData, TermId, TermStore};
use num_bigint::{BigInt, Sign};
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

/// Past this many decimal digits the literal is not worth its bytes.
const MAX_DECIMAL_DIGITS: u32 = 64;

/// The literal Carcara's lexer reads as `value` of sort Int (`integral`) or
/// Real, or `None` when the value has no finite decimal expansion.
pub(crate) fn carcara_numeric_literal(value: &BigRational, integral: bool) -> Option<String> {
    let sign = if value.numer().sign() == Sign::Minus {
        "-"
    } else {
        ""
    };
    let magnitude = value.abs();
    if integral {
        return magnitude
            .is_integer()
            .then(|| format!("{sign}{}", magnitude.numer()));
    }
    let denominator = magnitude.denom().clone();
    let mut rest = denominator.clone();
    let (mut twos, mut fives) = (0u32, 0u32);
    let two = BigInt::from(2u8);
    let five = BigInt::from(5u8);
    while rest.is_even() {
        rest /= &two;
        twos += 1;
    }
    while (&rest % &five).is_zero() {
        rest /= &five;
        fives += 1;
    }
    if !rest.is_one() {
        return None;
    }
    let digits = twos.max(fives).max(1);
    if digits > MAX_DECIMAL_DIGITS {
        return None;
    }
    let scale = BigInt::from(10u8).pow(digits);
    let scaled = magnitude.numer() * &scale / &denominator;
    let (whole, fraction) = scaled.div_rem(&scale);
    Some(format!(
        "{sign}{whole}.{fraction:0>width$}",
        width = digits as usize
    ))
}

/// [`validate_ground_evaluate`], and the value side of the equality has a
/// literal Carcara reads ([`carcara_numeric_literal`]).
pub(crate) fn validate_ground_evaluate_for_printer(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    premise_count: usize,
    args: &[TermId],
) -> Result<(), ProofCheckError> {
    validate_ground_evaluate(terms, step_id, clause, premise_count, args)?;
    let refuse = |reason: &str| {
        Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: format!("evaluate: {reason}"),
        })
    };
    if !value_has_literal(terms, clause) {
        return refuse("pinned Carcara reads no literal for the value (no finite decimal)");
    }
    if !integer_division_agrees_with_carcara(terms, clause) {
        return refuse(
            "pinned Carcara evaluates `div`/`mod` by truncation, which differs from SMT-LIB \
             unless the dividend is a non-negative numeral",
        );
    }
    Ok(())
}

/// Whether every `div` / `mod` the evaluated side applies has a NON-NEGATIVE
/// integer constant as its dividend, and no `rem` appears.
///
/// MEASURED on pinned Carcara 1.1.0 (git 9a352ee): its `evaluate` computes
/// `div` and `mod` by truncating division (`ay_core::pinned_carcara::evaluate`
/// lists both), so `(= (div (- 7) 2) -4)` and `(= (mod (- 7) 2) 1)`, true in
/// SMT-LIB and accepted by AY's evaluator, fail ("expected terms to be
/// equal: '-3' and '-4'"), while the FALSE `(= (div (- 7) 2) -3)` would pass.
/// Truncation and SMT-LIB's Euclidean division agree exactly when the
/// dividend is non-negative (`(div 7 (- 2))` is `-3` to both, measured
/// `valid`); `rem` is not SMT-LIB.
fn integer_division_agrees_with_carcara(terms: &TermStore, clause: &[TermId]) -> bool {
    let [literal] = clause else {
        return false;
    };
    let TermData::App(_, operands) = terms.get(*literal) else {
        return true;
    };
    let Some(evaluated) = operands.first() else {
        return true;
    };
    let mut pending = vec![*evaluated];
    let mut seen = ay_core::kani_compat::DetHashSet::default();
    while let Some(term) = pending.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermData::App(Symbol::Named(name), arguments) = terms.get(term) {
            match &**name {
                "rem" => return false,
                "div" | "mod" => {
                    let non_negative_dividend = arguments.first().is_some_and(|dividend| {
                        matches!(
                            terms.get(*dividend),
                            TermData::Const(Constant::Int(value)) if value.sign() != Sign::Minus
                        )
                    });
                    if !non_negative_dividend {
                        return false;
                    }
                }
                _ => {}
            }
        }
        pending.extend(terms.children(term));
    }
    true
}

fn value_has_literal(terms: &TermStore, clause: &[TermId]) -> bool {
    let [literal] = clause else {
        return false;
    };
    let TermData::App(Symbol::Named(_), operands) = terms.get(*literal) else {
        return false;
    };
    let [_, value] = operands.as_slice() else {
        return false;
    };
    match terms.get(*value) {
        TermData::Const(Constant::Rational(rational)) => {
            carcara_numeric_literal(&rational.0, false).is_some()
        }
        _ => true,
    }
}

#[cfg(test)]
#[path = "evaluate_literal_tests.rs"]
mod tests;
