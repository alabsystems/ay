// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A closed arithmetic spelling beside the constant it elaborated to.
//!
//! The problem writes `(abs -3)` or `(- -2 -3)`; AY interns the constant
//! (`3`, `1`), and a congruence position prints one side each way. Pinned
//! Carcara 1.1.0 (git 9a352ee) re-derives the identity with its own
//! `evaluate`: MEASURED valid for `(= (abs -3) 3)`, `(= (- -2 -3) 1)`,
//! `(= (- (- 2)) 2)` and `(= (+ (- 2) (- 2)) -4)`. Its `evaluate` reads only a
//! literal value (`evaluate_literal`), so a printed `(- 4)` is reached from
//! `-4` by `refl` (`refl_spelling`).
//!
//! Only `+`, `-`, `*` and `abs` over numeric literals are read. `div` and `mod`
//! are excluded on purpose: MEASURED, pinned Carcara evaluates
//! `(div (- 7) 2)` to `-3` (truncation) where SMT-LIB's value is `-4`, so the
//! true step `(= (div (- 7) 2) -4)` is refused. The value is recomputed here
//! and must be the position's internal constant.

use super::*;
use crate::checker::carcara_numeric_literal;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Signed;

const MAX_GROUND_BYTES: usize = 4096;
const MAX_GROUND_DEPTH: usize = 32;

/// The exact value of a closed `+`/`-`/`*`/`abs` term over numeric literals.
fn ground_value(text: &str, depth: usize) -> Option<BigRational> {
    if depth > MAX_GROUND_DEPTH {
        return None;
    }
    let Some(inner) = text.strip_prefix('(').and_then(|t| t.strip_suffix(')')) else {
        let (negative, magnitude) = text
            .strip_prefix('-')
            .map_or((false, text), |magnitude| (true, magnitude));
        let digits =
            |part: &str| !part.is_empty() && part.bytes().all(|byte| byte.is_ascii_digit());
        let (whole, fraction) = magnitude.split_once('.').unwrap_or((magnitude, ""));
        if !digits(whole) || !(fraction.is_empty() || digits(fraction)) || magnitude.ends_with('.')
        {
            return None;
        }
        let scale = BigInt::from(10u8).pow(u32::try_from(fraction.len()).ok()?);
        let value = BigRational::new(format!("{whole}{fraction}").parse().ok()?, scale);
        return Some(if negative { -value } else { value });
    };
    let parts = split_smt_terms(inner)?;
    let (head, operands) = parts.split_first()?;
    let values = operands
        .iter()
        .map(|operand| ground_value(operand, depth + 1))
        .collect::<Option<Vec<_>>>()?;
    match (head.as_str(), values.as_slice()) {
        ("-", [single]) => Some(-single.clone()),
        ("-", [first, rest @ ..]) if !rest.is_empty() => {
            Some(rest.iter().fold(first.clone(), |acc, value| acc - value))
        }
        ("+", [_, _, ..]) => Some(values.iter().sum()),
        ("*", [_, _, ..]) => Some(values.iter().product()),
        ("abs", [single]) => Some(single.abs()),
        _ => None,
    }
}

/// `(= left right)` when one side is a closed ground spelling the checker
/// `evaluate`s to the position's internal numeric constant `canonical_term`
/// and the other spells that constant (its literal, or a spelling `refl`
/// equates with it). `None` otherwise.
pub(in crate::alethe_printer) fn ground_value_steps(
    terms: &TermStore,
    id: &str,
    left: &str,
    right: &str,
    canonical_term: TermId,
) -> Option<Vec<String>> {
    if left.len() > MAX_GROUND_BYTES || right.len() > MAX_GROUND_BYTES {
        return None;
    }
    let (constant, integral) = match terms.get(canonical_term) {
        TermData::Const(Constant::Int(value)) => (BigRational::from_integer(value.clone()), true),
        TermData::Const(Constant::Rational(value)) => (value.0.clone(), false),
        _ => return None,
    };
    let literal = carcara_numeric_literal(&constant, integral)?;
    // One side spells the constant (its literal, or a spelling `refl`
    // equates with it); the other is the closed APPLICATION `evaluate` reads.
    let spells_constant =
        |text: &str| text == literal || carcara_refl_steps("t", &literal, text).is_some();
    let evaluates =
        |text: &str| text.starts_with('(') && ground_value(text, 0) == Some(constant.clone());
    let (ground, other, ground_first) = if spells_constant(right) && evaluates(left) {
        (left, right, true)
    } else if spells_constant(left) && evaluates(right) {
        (right, left, false)
    } else {
        return None;
    };
    // `(= ground other)`, named `id` when that is the conclusion itself.
    let derived = if ground_first {
        id.to_string()
    } else {
        format!("{id}.g")
    };
    let mut steps = Vec::new();
    if other == literal {
        steps.push(format!(
            "(step {derived} (cl (= {ground} {literal})) :rule evaluate)"
        ));
    } else {
        steps.push(format!(
            "(step {id}.ev (cl (= {ground} {literal})) :rule evaluate)"
        ));
        steps.extend(carcara_refl_steps(&format!("{id}.sp"), &literal, other)?);
        steps.push(format!(
            "(step {derived} (cl (= {ground} {other})) :rule trans :premises ({id}.ev {id}.sp))"
        ));
    }
    if !ground_first {
        steps.push(format!(
            "(step {id} (cl (= {left} {right})) :rule symm :premises ({derived}))"
        ));
    }
    Some(steps)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_closed_spelling_is_evaluated_to_the_positions_constant() {
        let mut terms = TermStore::new();
        let three = terms.mk_int(BigInt::from(3));
        assert_eq!(
            ground_value_steps(&terms, "t3.ac0", "(abs -3)", "3", three),
            Some(vec![
                "(step t3.ac0 (cl (= (abs -3) 3)) :rule evaluate)".to_string()
            ])
        );
        let minus_four = terms.mk_int(BigInt::from(-4));
        let steps =
            ground_value_steps(&terms, "t", "(- 4)", "(+ (- 2) (- 2))", minus_four).unwrap();
        assert!(
            steps.contains(&"(step t.ev (cl (= (+ (- 2) (- 2)) -4)) :rule evaluate)".to_string())
        );
        assert!(steps.contains(&"(step t.sp (cl (= -4 (- 4))) :rule refl)".to_string()));
        assert_eq!(
            steps.last().map(String::as_str),
            Some("(step t (cl (= (- 4) (+ (- 2) (- 2)))) :rule symm :premises (t.g))")
        );
    }

    #[test]
    fn another_value_an_unread_operator_or_a_symbol_declines() {
        let mut terms = TermStore::new();
        let three = terms.mk_int(BigInt::from(3));
        let minus_four = terms.mk_int(BigInt::from(-4));
        let x = terms.mk_var("x", Sort::Int);
        assert!(ground_value_steps(&terms, "t", "(abs -4)", "3", three).is_none());
        assert!(ground_value_steps(&terms, "t", "(div -7 2)", "(- 4)", minus_four).is_none());
        assert!(ground_value_steps(&terms, "t", "(+ x 0)", "x", x).is_none());
        assert!(ground_value_steps(&terms, "t", "(abs -3)", "(- 3)", three).is_none());
    }
}
