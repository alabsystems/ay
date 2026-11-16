// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use num_bigint::BigInt;

fn pair(terms: &TermStore, left: &str, right: &str, canonical_term: TermId) -> Option<Vec<String>> {
    AlethePrinter::new(terms).checker_identity_pair_steps("t", left, right, canonical_term)
}

/// a20 / b01: the authored `(* -1 y)` beside the canonical `(- y)`; pinned
/// Carcara checks `(= (* -1 y) (- y)) :rule poly_simp` valid.
#[test]
fn a_polynomial_respelling_is_poly_simp() {
    let mut terms = TermStore::new();
    let y = terms.mk_var("y", Sort::Int);
    let negated = terms.mk_app(Symbol::named("-"), [y], Sort::Int);
    assert_eq!(
        pair(&terms, "(* -1 y)", "(- y)", negated),
        Some(vec![
            "(step t (cl (= (* -1 y) (- y))) :rule poly_simp)".to_string()
        ])
    );
    assert_eq!(pair(&terms, "(* -2 y)", "(- y)", negated), None);
}

/// d20 / e20: an equality in the other operand order, with the shorthand on
/// one side, is pinned Carcara's own `refl`.
#[test]
fn an_equality_in_the_other_order_is_refl() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let minus_two = terms.mk_int(BigInt::from(-2));
    let equality = terms.mk_app(Symbol::named("="), [x, minus_two], Sort::Bool);
    assert_eq!(
        pair(&terms, "(= -2 x)", "(= x (- 2))", equality),
        Some(vec![
            "(step t (cl (= (= -2 x) (= x (- 2)))) :rule refl)".to_string()
        ])
    );
}

/// f01: `(not (>= x -3))` beside the canonical `(not (<= (- 3) x))`. The
/// literal is respelled by `refl`, the comparison reversed by
/// `comp_simplify`, and `cong` closes the `not`; no step is one pinned
/// Carcara refuses (`(= (not (>= x -3)) (not (<= (- 3) x)))` by `refl` is).
#[test]
fn a_reversed_comparison_with_a_shorthand_under_not_is_bridged() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let minus_three = terms.mk_int(BigInt::from(-3));
    let le = terms.mk_app(Symbol::named("<="), [minus_three, x], Sort::Bool);
    let negated = terms.mk_not(le);
    let steps = pair(&terms, "(not (>= x -3))", "(not (<= (- 3) x))", negated).expect("bridged");
    assert_eq!(
        steps.last().map(String::as_str),
        Some("(step t (cl (= (not (>= x -3)) (not (<= (- 3) x)))) :rule cong :premises (t.n))")
    );
    assert!(steps
        .iter()
        .any(|step| step == "(step t.n.l (cl (= (>= x -3) (>= x (- 3)))) :rule refl)"));
    for step in &steps {
        if step.contains(":rule comp_simplify") {
            let conclusion = step
                .split_once("(cl ")
                .and_then(|(_, rest)| rest.rsplit_once(") :rule"))
                .map(|(conclusion, _)| conclusion)
                .expect("a clause");
            assert!(
                printed_simplify::printed_comp_simplify_holds(
                    &[conclusion],
                    &la_generic_surface::StepDefinitions::NONE
                ),
                "{step}"
            );
        }
    }
}

/// d16: `(abs -3)` beside the constant `3` is pinned Carcara's `evaluate`.
#[test]
fn a_closed_spelling_of_the_constant_is_evaluated() {
    let mut terms = TermStore::new();
    let three = terms.mk_int(BigInt::from(3));
    assert_eq!(
        pair(&terms, "(abs -3)", "3", three),
        Some(vec![
            "(step t (cl (= (abs -3) 3)) :rule evaluate)".to_string()
        ])
    );
}
