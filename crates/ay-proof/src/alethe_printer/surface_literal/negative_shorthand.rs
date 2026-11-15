// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The negative-literal shorthand `-2` beside the canonical `(- 2)` of the
//! constant it denotes.
//!
//! Benchmarks write `-2` for the number, and z3, cvc5 and pinned Carcara all
//! read an UNQUOTED `-2` as the numeral even where `|-2|` is declared or
//! bound; only the quoted `|-2|` is a symbol. AY's S-expression parser reads
//! it the same way (`ay_frontend::sexp::is_negative_numeric_literal`), so the
//! authored-surface echo prints the shorthand bare as the constant it is, and
//! every symbol named `-2` quoted (`quote_symbol`). A bare `-2` in a printed
//! surface is therefore always the numeral, and `|-2|` never reaches this
//! module as a shorthand.
//!
//! The printer's canonical spelling of the same constant is `(- 2)` (or
//! `(- (/ 5.0 2.0))`, `(- 2.0)`, `0`, `0.0`), so a congruence position whose
//! one side echoes the authored text and the other the canonical rendering
//! differs in bytes over ONE internal term. Pinned Carcara closes that gap
//! with its own `refl`. MEASURED on carcara 1.1.0 (git 9a352ee), each as
//! `(step t1 (cl (= S C)) :rule refl)` over a problem that parses:
//! `-2`/`(- 2)`, `-0`/`0`, `-2.5`/`(- (/ 5.0 2.0))`, `-2.0`/`(- 2.0)` and
//! `-0.0`/`0.0` check `valid`; `-2`/`(- 3)` fails ("reflexivity failed with
//! terms '-2' and '(- 3)'"), `-2.5`/`(- (/ 5.0 3.0))` fails, and `-0`/`(- 0)`
//! fails, so the step states an identity the checker re-derives and never one
//! it cannot see.
//!
//! The identity is grounded in the INTERNAL term, never in the text alone:
//! the two texts are walked along the position's internal term, every leaf
//! where they differ must hold one numeric constant, one side must be that
//! constant's own rendering, and the other must spell the same value in the
//! same sort (digits only for an `Int`, digits `.` digits for a `Real`).
//! MEASURED as well: `(= (< x -3) (< x (- 3)))` and `(= (f -1) (f (- 1)))`
//! by `refl` check `valid`. Anything else declines and leaves the caller's
//! refusal unchanged.

use super::*;
use num_bigint::BigInt;
use num_rational::BigRational;

/// The value a bare negative-literal shorthand spells, with whether it is a
/// decimal: `-` then digits, or `-` then digits `.` digits — exactly the
/// spellings the elaborator turns into a negative constant. A quoted `|-2|`,
/// `-.5`, `-5.`, `--1` or `-1e3` is not a shorthand.
fn shorthand_value(text: &str) -> Option<(BigRational, bool)> {
    let magnitude = text.strip_prefix('-')?;
    let digits = |part: &str| !part.is_empty() && part.bytes().all(|byte| byte.is_ascii_digit());
    let (value, decimal) = match magnitude.split_once('.') {
        None => {
            if !digits(magnitude) {
                return None;
            }
            (
                BigRational::from_integer(magnitude.parse::<BigInt>().ok()?),
                false,
            )
        }
        Some((whole, fraction)) => {
            if !digits(whole) || !digits(fraction) {
                return None;
            }
            let scale = BigInt::from(10u8).pow(u32::try_from(fraction.len()).ok()?);
            let numerator = format!("{whole}{fraction}").parse::<BigInt>().ok()?;
            (BigRational::new(numerator, scale), true)
        }
    };
    Some((-value, decimal))
}

/// Whether the bare shorthand `text` spells `constant`, in its sort.
fn shorthand_spells(text: &str, constant: &Constant) -> bool {
    let Some((value, decimal)) = shorthand_value(text) else {
        return false;
    };
    match constant {
        Constant::Int(integer) => !decimal && value == BigRational::from_integer(integer.clone()),
        Constant::Rational(rational) => decimal && value == rational.0,
        _ => false,
    }
}

const MAX_SHORTHAND_WALK_BYTES: usize = 64 * 1024;
const MAX_SHORTHAND_WALK_DEPTH: usize = 64;
const MAX_SHORTHAND_WALK_NODES: usize = 256;

/// `(step id (cl (= left right)) :rule refl)` when `left` and `right` are two
/// printings of the internal `term` that differ only where one spells a
/// numeric constant of `term` by its negative-literal shorthand and the other
/// by the printer's own rendering of that constant; `None` otherwise.
///
/// The walk follows `term`: below an application both texts must be
/// applications with one head and one printed argument per internal argument,
/// and every differing leaf must sit on an internal numeric constant. A
/// variable, a different head or arity, or a shorthand of another value
/// declines.
pub(in crate::alethe_printer) fn negative_literal_shorthand_steps(
    terms: &TermStore,
    id: &str,
    left: &str,
    right: &str,
    term: TermId,
) -> Option<Vec<String>> {
    if left == right
        || left.len() > MAX_SHORTHAND_WALK_BYTES
        || right.len() > MAX_SHORTHAND_WALK_BYTES
    {
        return None;
    }
    let mut nodes = 0;
    respelled_by_shorthand(terms, term, left, right, 0, &mut nodes)
        .then(|| vec![format!("(step {id} (cl (= {left} {right})) :rule refl)")])
}

fn respelled_by_shorthand(
    terms: &TermStore,
    term: TermId,
    left: &str,
    right: &str,
    depth: usize,
    nodes: &mut usize,
) -> bool {
    if left == right {
        return true;
    }
    if depth > MAX_SHORTHAND_WALK_DEPTH || *nodes >= MAX_SHORTHAND_WALK_NODES {
        return false;
    }
    *nodes += 1;
    match terms.get(term) {
        TermData::Const(constant) => {
            let canonical = AlethePrinter::format_constant(constant);
            (left == canonical && shorthand_spells(right, constant))
                || (right == canonical && shorthand_spells(left, constant))
        }
        TermData::App(_, args) => {
            let (Some(left_parts), Some(right_parts)) =
                (application_parts(left), application_parts(right))
            else {
                return false;
            };
            let [left_head, left_args @ ..] = left_parts.as_slice() else {
                return false;
            };
            let [right_head, right_args @ ..] = right_parts.as_slice() else {
                return false;
            };
            left_head == right_head
                && left_args.len() == args.len()
                && right_args.len() == args.len()
                && args
                    .iter()
                    .zip(left_args.iter().zip(right_args))
                    .all(|(&arg, (left, right))| {
                        respelled_by_shorthand(terms, arg, left, right, depth + 1, nodes)
                    })
        }
        _ => false,
    }
}

fn application_parts(text: &str) -> Option<Vec<String>> {
    split_smt_terms(text.strip_prefix('(')?.strip_suffix(')')?)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int(terms: &mut TermStore, value: i64) -> TermId {
        terms.mk_int(BigInt::from(value))
    }

    fn real(terms: &mut TermStore, numerator: i64, denominator: i64) -> TermId {
        terms.mk_rational(BigRational::new(
            BigInt::from(numerator),
            BigInt::from(denominator),
        ))
    }

    fn steps(terms: &TermStore, left: &str, right: &str, term: TermId) -> Option<Vec<String>> {
        negative_literal_shorthand_steps(terms, "t2.ac0", left, right, term)
    }

    #[test]
    fn the_shorthand_of_the_positions_constant_is_refl_in_both_orientations() {
        let mut terms = TermStore::new();
        let cases = [
            ("-2", int(&mut terms, -2)),
            ("-0", int(&mut terms, 0)),
            ("-2.5", real(&mut terms, -5, 2)),
            ("-2.0", real(&mut terms, -2, 1)),
            ("-2.50", real(&mut terms, -5, 2)),
            ("-0.0", real(&mut terms, 0, 1)),
        ];
        for (text, term) in cases {
            let canonical = crate::render_term_canonical(&terms, term);
            assert_eq!(
                steps(&terms, text, &canonical, term),
                Some(vec![format!(
                    "(step t2.ac0 (cl (= {text} {canonical})) :rule refl)"
                )]),
                "{text}"
            );
            assert!(steps(&terms, &canonical, text, term).is_some(), "{text}");
        }
    }

    #[test]
    fn a_quoted_name_another_value_or_another_sort_declines() {
        let mut terms = TermStore::new();
        let two = int(&mut terms, -2);
        for text in [
            "|-2|", "-3", "-2.0", "-.2", "-2.", "--2", "-2e0", "2", "(- 2)",
        ] {
            assert_eq!(steps(&terms, text, "(- 2)", two), None, "{text}");
        }
        let half = real(&mut terms, -5, 2);
        for text in ["-2", "-2.4", "|-2.5|"] {
            assert_eq!(steps(&terms, text, "(- (/ 5.0 2.0))", half), None, "{text}");
        }
    }

    #[test]
    fn the_other_side_must_be_the_constants_own_rendering() {
        let mut terms = TermStore::new();
        let two = int(&mut terms, -2);
        let zero = int(&mut terms, 0);
        assert_eq!(steps(&terms, "-2", "(- 3)", two), None);
        assert_eq!(steps(&terms, "-2", "x", two), None);
        assert_eq!(
            steps(&terms, "-0", "(- 0)", zero),
            None,
            "pinned carcara does not equate -0 with (- 0)"
        );
        let x = terms.mk_var("x", Sort::Int);
        assert_eq!(
            steps(&terms, "-2", "(- 2)", x),
            None,
            "a variable position is never a constant's spelling"
        );
    }

    #[test]
    fn the_walk_follows_the_internal_application() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let three = int(&mut terms, -3);
        let lt = terms.mk_app(Symbol::named("<"), [x, three], Sort::Bool);
        assert_eq!(
            steps(&terms, "(< x -3)", "(< x (- 3))", lt),
            Some(vec![
                "(step t2.ac0 (cl (= (< x -3) (< x (- 3)))) :rule refl)".to_string()
            ])
        );
        // The shorthand on the variable's position, a changed head, a changed
        // arity or a changed value is not this term's respelling.
        for (left, right) in [
            ("(< -3 x)", "(< (- 3) x)"),
            ("(<= x -3)", "(< x (- 3))"),
            ("(< x -3 x)", "(< x (- 3) x)"),
            ("(< x -4)", "(< x (- 3))"),
            ("(< x |-3|)", "(< x (- 3))"),
        ] {
            assert_eq!(steps(&terms, left, right, lt), None, "{left} / {right}");
        }
    }
}
