// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for `(get-interpolant A B)` / `(compute-interpolant A B)`.

#![allow(clippy::unwrap_used)]

use super::*;
use crate::engine_utils::check_sat_with_timeout;
use crate::interpolant_validation::is_unsat_result;

/// Parse a single SMT-LIB term from text.
fn term(src: &str) -> Term {
    let sexpr = ay_frontend::sexp::parse_sexp(src).expect("parse sexpr");
    Term::from_sexp(&sexpr).expect("parse term")
}

/// All-Int sort resolver (LIA fragment).
fn int_sorts(_: &str) -> Option<ChcSort> {
    Some(ChcSort::Int)
}

/// Verify the two Craig obligations independently via the SMT context.
fn assert_valid_interpolant(a: &ChcExpr, b: &ChcExpr, i: &ChcExpr) {
    let timeout = std::time::Duration::from_secs(5);
    // A => I  <=>  UNSAT(A /\ !I)
    let a_and_not_i = ChcExpr::and(a.clone(), ChcExpr::not(i.clone()));
    assert!(
        is_unsat_result(&check_sat_with_timeout(&a_and_not_i, timeout)),
        "A => I failed: A={a}, I={i}"
    );
    // I /\ B is UNSAT
    let i_and_b = ChcExpr::and(i.clone(), b.clone());
    assert!(
        is_unsat_result(&check_sat_with_timeout(&i_and_b, timeout)),
        "I /\\ B unsat failed: I={i}, B={b}"
    );
}

#[test]
fn lia_simple_bound_conflict() {
    // A = (<= x 0), B = (>= x 1); A /\ B is UNSAT.
    let a = term("(<= x 0)");
    let b = term("(>= x 1)");
    let a_expr = term_to_chc(&a, &int_sorts).unwrap();
    let b_expr = term_to_chc(&b, &int_sorts).unwrap();

    let i = compute_smt_interpolant(&a, &b, &int_sorts).expect("interpolant exists");
    assert_valid_interpolant(&a_expr, &b_expr, &i);

    // The interpolant must only mention the shared variable x.
    let vars: Vec<String> = i.vars().into_iter().map(|v| v.name).collect();
    assert!(vars.iter().all(|v| v == "x"), "interpolant vars: {vars:?}");
}

#[test]
fn lia_conjunctive_a_and_b() {
    // A = (and (<= x 0)), B = (and (>= x 1)) — Z3's `(and ...)` grouping form.
    let a = term("(and (<= x 0))");
    let b = term("(and (>= x 1))");
    let a_expr = term_to_chc(&a, &int_sorts).unwrap();
    let b_expr = term_to_chc(&b, &int_sorts).unwrap();

    let i = compute_smt_interpolant(&a, &b, &int_sorts).expect("interpolant exists");
    assert_valid_interpolant(&a_expr, &b_expr, &i);
}

#[test]
fn lia_shared_variable_relation() {
    // A: y = x + 1 and x >= 0  => y >= 1
    // B: y <= 0
    // shared var: y. Interpolant over y blocks B.
    let a = term("(and (= y (+ x 1)) (>= x 0))");
    let b = term("(<= y 0)");
    let a_expr = term_to_chc(&a, &int_sorts).unwrap();
    let b_expr = term_to_chc(&b, &int_sorts).unwrap();

    let i = compute_smt_interpolant(&a, &b, &int_sorts).expect("interpolant exists");
    assert_valid_interpolant(&a_expr, &b_expr, &i);

    // x is A-local, must not appear in the interpolant.
    let vars: Vec<String> = i.vars().into_iter().map(|v| v.name).collect();
    assert!(
        !vars.contains(&"x".to_string()),
        "interpolant leaked x: {vars:?}"
    );
}

#[test]
fn satisfiable_pair_is_unsupported() {
    // A = (<= x 0), B = (<= x 1); A /\ B is SAT — no interpolant.
    let a = term("(<= x 0)");
    let b = term("(<= x 1)");
    let res = compute_smt_interpolant(&a, &b, &int_sorts);
    assert!(
        matches!(res, Err(InterpolantError::Unsupported(_))),
        "{res:?}"
    );
}

#[test]
fn unsupported_fragment_is_rejected() {
    // Bitvector formula is outside the LIA/LRA fragment.
    let a = term("(bvule x #x00)");
    let b = term("(bvugt x #x00)");
    let res = compute_smt_interpolant(&a, &b, &|_: &str| Some(ChcSort::BitVec(8)));
    assert!(
        matches!(res, Err(InterpolantError::Unsupported(_))),
        "{res:?}"
    );
}

#[test]
fn quantified_formula_is_rejected() {
    let a = term("(forall ((z Int)) (<= z 0))");
    let b = term("(>= x 1)");
    let res = compute_smt_interpolant(&a, &b, &int_sorts);
    assert!(
        matches!(res, Err(InterpolantError::Unsupported(_))),
        "{res:?}"
    );
}

#[test]
fn interpolant_renders_to_smtlib() {
    let a = term("(<= x 0)");
    let b = term("(>= x 1)");
    let i = compute_smt_interpolant(&a, &b, &int_sorts).expect("interpolant exists");
    let rendered = i.to_string();
    // Must be a non-empty S-expression mentioning x.
    assert!(rendered.contains('x'), "rendered: {rendered}");
    assert!(rendered.starts_with('('), "rendered: {rendered}");
}

#[test]
fn lra_real_returns_valid_interpolant() {
    // A = (<= x 0.0), B = (>= x 1.0) over Reals. A /\ B is UNSAT.
    //
    // #chc25-lra-convergence: the Farkas linear parser is now Real-aware, so the
    // `get-interpolant` command SUPPORTS LRA and returns a validated Craig
    // interpolant instead of `unsupported`. (Previously the LIA-only parser
    // rejected Real-sorted variables and this returned Unsupported.) Soundness
    // is unchanged: the returned candidate is Craig-validated + re-validated
    // over the REAL theory before it is handed back.
    let real_sorts = |_: &str| Some(ChcSort::Real);
    let a = term("(<= x 0.0)");
    let b = term("(>= x 1.0)");
    let a_expr = term_to_chc(&a, &real_sorts).unwrap();
    let b_expr = term_to_chc(&b, &real_sorts).unwrap();

    let i = compute_smt_interpolant(&a, &b, &real_sorts)
        .expect("LRA interpolant is now supported and must be produced");
    assert_valid_interpolant(&a_expr, &b_expr, &i);

    // The interpolant must only mention the shared Real variable x.
    for v in i.vars() {
        assert_eq!(v.name, "x", "interpolant var: {}", v.name);
        assert_eq!(
            v.sort,
            ChcSort::Real,
            "interpolant var {} mis-sorted",
            v.name
        );
    }
}

#[test]
fn decimal_literal_is_reduced() {
    // `1.0` must reduce to Real(1, 1), not Real(10, 10).
    assert_eq!(decimal_to_real("1.0"), Some(ChcExpr::Real(1, 1)));
    assert_eq!(decimal_to_real("0.5"), Some(ChcExpr::Real(1, 2)));
    assert_eq!(decimal_to_real("2.50"), Some(ChcExpr::Real(5, 2)));
    assert_eq!(decimal_to_real("3"), Some(ChcExpr::Real(3, 1)));
}
