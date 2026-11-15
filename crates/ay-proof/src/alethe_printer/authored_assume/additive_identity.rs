// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked use-site bridges between an authored arithmetic spelling and the
//! term it interns as: the additive identity (`(+ x 0)` and `x`), and the
//! lenient negative literal (`-2` and `(- 2)`).
//!
//! THE SHAPE THIS REPAIRS. The frontend interns the authored `(+ x1 0)` as
//! `x1`, and the surface-override ledger keeps the authored spelling for every
//! term that carried it, so an authored `(= x0 (+ x1 0))` prints that way
//! wherever its `TermId` occurs. A congruence over it then compares the
//! printed `(+ x1 0)` with a premise or a sibling that prints `x1`: internally
//! the same term, printed two ways, and no leaf the bridge knew relates them.
//! Measured on the OR-substitution fuzz (1,200 QF_LIA files): one certified
//! UNSAT in four refused `(get-proof)` with `left="(+ x1 0)"; right="x1"`.
//!
//! WHY THE STEP IS SOUND AS PRINTED. `sum_simplify` is pinned Carcara's own
//! rule (1.1.0, `generic_sum_prod_simplify_rule`): it checks `(= t u)` where
//! `u` is `t` with its numeric constants summed and, when that sum is `0`,
//! dropped. This leaf admits only the sub-case it can compute byte-exactly
//! from the printed text — every constant summand a literal `0`, at least one
//! dropped, at least one non-constant left — and emits the step only when the
//! other spelling IS that result. Any summand that pinned Carcara could read
//! as a number (a numeral, a decimal, `(- ..)`, `(/ ..)`, `(div ..)`) other
//! than a literal zero makes it decline, so the leaf never has to guess how
//! Carcara would fold a constant.

use super::{oriented_equivalence, split_application, EquivalenceDirection};

/// The term pinned Carcara's `sum_simplify` computes for the printed sum
/// `sum` when its only numeric summands are literal zeros, or `None` when
/// `sum` is not such a sum.
pub(in crate::alethe_printer) fn zero_summands_dropped(sum: &str) -> Option<String> {
    let summands = split_application(sum, "+")?;
    if summands.len() < 2 {
        return None;
    }
    let mut kept = Vec::with_capacity(summands.len());
    let mut dropped = false;
    for summand in summands {
        if is_literal_zero(&summand) {
            dropped = true;
        } else if may_read_as_number(&summand) {
            return None;
        } else {
            kept.push(summand);
        }
    }
    if !dropped {
        return None;
    }
    match kept.len() {
        0 => None,
        1 => kept.pop(),
        _ => Some(format!("(+ {})", kept.join(" "))),
    }
}

/// Push `(step {id} (cl (= ..)) :rule sum_simplify)` relating `surface` and
/// `canonical` in `direction` when one is the other with its literal-zero
/// summands dropped.
pub(in crate::alethe_printer) fn additive_identity_step(
    id: &str,
    surface: &str,
    canonical: &str,
    direction: EquivalenceDirection,
    output: &mut Vec<String>,
) -> bool {
    let related = zero_summands_dropped(surface).as_deref() == Some(canonical)
        || zero_summands_dropped(canonical).as_deref() == Some(surface);
    if related {
        let equality = oriented_equivalence(surface, canonical, direction);
        output.push(format!("(step {id} (cl {equality}) :rule sum_simplify)"));
    }
    related
}

/// Push `(step {id} (cl (= ..)) :rule minus_simplify)` when `surface` and
/// `canonical` are the two spellings of one negative number: the lenient
/// literal `-2` some inputs write (and AY reads as a numeral) and the SMT-LIB
/// `(- 2)` AY prints. Pinned Carcara parses the first as a constant and the
/// second as unary minus, so they are different terms to it, and
/// `minus_simplify` is the rule that relates them (`as_signed_number` of both
/// sides agree; measured valid on pinned Carcara 1.1.0 in both orientations).
pub(in crate::alethe_printer) fn negative_literal_respelling_step(
    id: &str,
    surface: &str,
    canonical: &str,
    direction: EquivalenceDirection,
    output: &mut Vec<String>,
) -> bool {
    let related = negative_literal_respelling(surface, canonical);
    if related {
        let equality = oriented_equivalence(surface, canonical, direction);
        output.push(format!("(step {id} (cl {equality}) :rule minus_simplify)"));
    }
    related
}

/// Whether one of `first`/`second` is `-n` and the other `(- n)` for the
/// same unsigned numeral or decimal `n`.
pub(in crate::alethe_printer) fn negative_literal_respelling(first: &str, second: &str) -> bool {
    let pair = |literal: &str, applied: &str| {
        literal.strip_prefix('-').is_some_and(|magnitude| {
            is_unsigned_number(magnitude)
                && applied
                    .strip_prefix("(- ")
                    .and_then(|rest| rest.strip_suffix(')'))
                    == Some(magnitude)
        })
    };
    pair(first, second) || pair(second, first)
}

fn is_unsigned_number(text: &str) -> bool {
    text.starts_with(|c: char| c.is_ascii_digit())
        && text.chars().all(|c| c.is_ascii_digit() || c == '.')
}

fn is_literal_zero(summand: &str) -> bool {
    matches!(summand, "0" | "0.0")
}

/// Whether pinned Carcara's `as_fraction` could read `summand` as a number:
/// numerals and decimals, and the `(- ..)`, `(/ ..)` and `(div ..)` shells it
/// looks through. Over-approximate on purpose (`(- x)` counts): a false
/// positive only makes the leaf decline.
fn may_read_as_number(summand: &str) -> bool {
    summand
        .chars()
        .next()
        .is_some_and(|first| first.is_ascii_digit() || first == '.')
        || ["(- ", "(/ ", "(div "]
            .iter()
            .any(|shell| summand.starts_with(shell))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_trailing_or_leading_zero_summand_drops_to_the_other_summand() {
        assert_eq!(zero_summands_dropped("(+ x1 0)").as_deref(), Some("x1"));
        assert_eq!(zero_summands_dropped("(+ 0 x1)").as_deref(), Some("x1"));
        assert_eq!(zero_summands_dropped("(+ y 0.0)").as_deref(), Some("y"));
    }

    #[test]
    fn several_survivors_stay_a_sum_in_their_printed_order() {
        assert_eq!(
            zero_summands_dropped("(+ b 0 a)").as_deref(),
            Some("(+ b a)")
        );
    }

    #[test]
    fn any_other_constant_declines_rather_than_guess_the_fold() {
        assert_eq!(zero_summands_dropped("(+ x 0 2)"), None);
        assert_eq!(zero_summands_dropped("(+ x (- 2) 0)"), None);
        assert_eq!(zero_summands_dropped("(+ x 0 (/ 1 2))"), None);
        // `(- x)` may be unary minus of a variable; declining is the safe side.
        assert_eq!(zero_summands_dropped("(+ (- x) 0)"), None);
    }

    #[test]
    fn a_sum_with_no_zero_or_only_zeros_is_not_this_shape() {
        assert_eq!(zero_summands_dropped("(+ x y)"), None);
        assert_eq!(zero_summands_dropped("(+ 0 0)"), None);
        assert_eq!(zero_summands_dropped("x"), None);
        assert_eq!(zero_summands_dropped("(* x 0)"), None);
    }

    #[test]
    fn a_lenient_negative_literal_and_its_unary_minus_are_one_number() {
        assert!(negative_literal_respelling("-2", "(- 2)"));
        assert!(negative_literal_respelling("(- 2.5)", "-2.5"));
        assert!(!negative_literal_respelling("-2", "(- 3)"));
        assert!(!negative_literal_respelling("-x", "(- x)"));
        assert!(!negative_literal_respelling("2", "(- 2)"));
        let mut output = Vec::new();
        assert!(negative_literal_respelling_step(
            "t1",
            "-2",
            "(- 2)",
            EquivalenceDirection::SurfaceToCanonical,
            &mut output
        ));
        assert_eq!(
            output,
            vec!["(step t1 (cl (= -2 (- 2))) :rule minus_simplify)".to_string()]
        );
    }

    #[test]
    fn the_step_is_emitted_only_for_the_exact_result_in_either_direction() {
        let mut output = Vec::new();
        assert!(additive_identity_step(
            "t1",
            "(+ x1 0)",
            "x1",
            EquivalenceDirection::SurfaceToCanonical,
            &mut output
        ));
        assert!(additive_identity_step(
            "t2",
            "x1",
            "(+ x1 0)",
            EquivalenceDirection::CanonicalToSurface,
            &mut output
        ));
        assert!(!additive_identity_step(
            "t3",
            "(+ x1 0)",
            "x2",
            EquivalenceDirection::SurfaceToCanonical,
            &mut output
        ));
        assert_eq!(
            output,
            vec![
                "(step t1 (cl (= (+ x1 0) x1)) :rule sum_simplify)".to_string(),
                "(step t2 (cl (= (+ x1 0) x1)) :rule sum_simplify)".to_string(),
            ]
        );
    }
}
