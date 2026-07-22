// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::pdr::solver::test_helpers::solver_from_str;
use crate::pdr::solver::PdrSolver;
use crate::smt::SmtResult;
use crate::{ChcExpr, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ntest::timeout;

/// Test that discover_difference_invariants finds A - B = 5.
/// init: A=10, B=5; transition: A'=A+3, B'=B+3
/// The difference A-B is preserved at 5.
#[test]
#[timeout(10_000)]
fn discover_diff_invariant_constant_offset() {
    let input = r#"(set-logic HORN)
(declare-fun inv ( Int Int ) Bool)
(assert (forall ( (A Int) (B Int) )
    (=> (and (= A 10) (= B 5)) (inv A B))))
(assert (forall ( (A Int) (B Int) (A1 Int) (B1 Int) )
    (=> (and (inv A B) (= A1 (+ A 3)) (= B1 (+ B 3))) (inv A1 B1))))
(assert (forall ( (A Int) (B Int) )
    (=> (and (inv A B) (< A B)) false)))
(check-sat)
(exit)"#;

    let mut solver = solver_from_str(input);
    solver.discover_difference_invariants();

    let pred = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "inv")
        .expect("inv predicate")
        .id;
    let vars = solver.canonical_vars(pred).expect("canonical vars");
    assert_eq!(vars.len(), 2);

    // Expect A - B = 5
    let expected = ChcExpr::eq(
        ChcExpr::sub(ChcExpr::var(vars[0].clone()), ChcExpr::var(vars[1].clone())),
        ChcExpr::Int(5),
    );
    let lemmas: Vec<_> = solver.frames[1]
        .lemmas
        .iter()
        .filter(|l| l.predicate == pred)
        .collect();
    assert!(
        lemmas.iter().any(|l| l.formula == expected),
        "Expected diff invariant A - B = 5, got: {:?}",
        lemmas.iter().map(|l| &l.formula).collect::<Vec<_>>()
    );
}

/// Test that discover_difference_invariants does NOT produce a diff invariant
/// when the difference is not preserved.
/// init: A=10, B=5; transition: A'=A+1, B'=B+2 (diff changes by -1 each step)
#[test]
#[timeout(10_000)]
fn discover_diff_invariant_not_preserved() {
    let input = r#"(set-logic HORN)
(declare-fun inv ( Int Int ) Bool)
(assert (forall ( (A Int) (B Int) )
    (=> (and (= A 10) (= B 5)) (inv A B))))
(assert (forall ( (A Int) (B Int) (A1 Int) (B1 Int) )
    (=> (and (inv A B) (= A1 (+ A 1)) (= B1 (+ B 2))) (inv A1 B1))))
(assert (forall ( (A Int) (B Int) )
    (=> (and (inv A B) (< A 0)) false)))
(check-sat)
(exit)"#;

    let mut solver = solver_from_str(input);
    solver.discover_difference_invariants();

    let pred = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "inv")
        .expect("inv predicate")
        .id;
    let vars = solver.canonical_vars(pred).expect("canonical vars");

    // Should NOT produce A - B = 5 since difference is not preserved
    let bad_invariant = ChcExpr::eq(
        ChcExpr::sub(ChcExpr::var(vars[0].clone()), ChcExpr::var(vars[1].clone())),
        ChcExpr::Int(5),
    );
    let diff_lemmas: Vec<_> = solver.frames[1]
        .lemmas
        .iter()
        .filter(|l| l.predicate == pred && l.formula == bad_invariant)
        .collect();
    assert!(
        diff_lemmas.is_empty(),
        "Should not discover diff invariant when difference is not preserved"
    );
}

/// Test difference invariant with negative offset.
/// init: A=2, B=8; transition: A'=A+1, B'=B+1
/// Expected: A - B = -6 (and B - A = 6)
#[test]
#[timeout(10_000)]
fn discover_diff_invariant_negative_offset() {
    let input = r#"(set-logic HORN)
(declare-fun inv ( Int Int ) Bool)
(assert (forall ( (A Int) (B Int) )
    (=> (and (= A 2) (= B 8)) (inv A B))))
(assert (forall ( (A Int) (B Int) (A1 Int) (B1 Int) )
    (=> (and (inv A B) (= A1 (+ A 1)) (= B1 (+ B 1))) (inv A1 B1))))
(assert (forall ( (A Int) (B Int) )
    (=> (and (inv A B) (< A 0)) false)))
(check-sat)
(exit)"#;

    let mut solver = solver_from_str(input);
    solver.discover_difference_invariants();

    let pred = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "inv")
        .expect("inv predicate")
        .id;
    let vars = solver.canonical_vars(pred).expect("canonical vars");

    // Expect A - B = -6 or B - A = 6 (both orderings tried)
    let expected_ab = ChcExpr::eq(
        ChcExpr::sub(ChcExpr::var(vars[0].clone()), ChcExpr::var(vars[1].clone())),
        ChcExpr::Int(-6),
    );
    let expected_ba = ChcExpr::eq(
        ChcExpr::sub(ChcExpr::var(vars[1].clone()), ChcExpr::var(vars[0].clone())),
        ChcExpr::Int(6),
    );
    let lemmas: Vec<_> = solver.frames[1]
        .lemmas
        .iter()
        .filter(|l| l.predicate == pred)
        .collect();
    assert!(
        lemmas
            .iter()
            .any(|l| l.formula == expected_ab || l.formula == expected_ba),
        "Expected diff invariant A - B = -6 or B - A = 6, got: {:?}",
        lemmas.iter().map(|l| &l.formula).collect::<Vec<_>>()
    );
}

#[test]
#[timeout(10_000)]
fn entry_value_inference_sat_probe_uses_sat_only_gate() {
    let input = r#"(set-logic HORN)
(declare-fun inv ( Int ) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (and (inv x) (= x 0)) false)))
(check-sat)
(exit)"#;

    let mut solver = solver_from_str(input);
    assert!(
        solver.is_sat_for_entry_value_inference(&ChcExpr::Bool(true)),
        "SAT probes should return true"
    );
    assert!(
        !solver.is_sat_for_entry_value_inference(&ChcExpr::Bool(false)),
        "UNSAT probes should return false"
    );
}

#[test]
fn entry_value_inference_rejects_unknown_and_unsat_results() {
    assert!(PdrSolver::sat_result_allows_entry_value_inference(
        &SmtResult::Sat(FxHashMap::default())
    ));
    assert!(!PdrSolver::sat_result_allows_entry_value_inference(
        &SmtResult::Unsat
    ));
    assert!(!PdrSolver::sat_result_allows_entry_value_inference(
        &SmtResult::Unknown
    ));
}

/// Verify the 100ms timeout in `is_sat_for_entry_value_inference` correctly
/// handles non-trivial satisfiable and unsatisfiable integer constraints.
/// The existing test only uses Bool(true)/Bool(false) literals; this test
/// exercises the SMT solver with actual LIA formulas under the timeout.
#[test]
#[timeout(10_000)]
fn entry_value_inference_timeout_handles_nontrivial_constraints() {
    let input = r#"(set-logic HORN)
(declare-fun inv ( Int Int ) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= y 0)) (inv x y))))
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int))
    (=> (and (inv x y) (= x1 (+ x 1)) (= y1 (+ y 2))) (inv x1 y1))))
(assert (forall ((x Int) (y Int)) (=> (and (inv x y) (< x 0)) false)))
(check-sat)
(exit)"#;

    let mut solver = solver_from_str(input);

    // A satisfiable integer constraint: x >= 0 AND y >= 0
    let x = ChcExpr::var(ChcVar {
        name: "x".into(),
        sort: ChcSort::Int,
    });
    let y = ChcExpr::var(ChcVar {
        name: "y".into(),
        sort: ChcSort::Int,
    });
    let sat_constraint = ChcExpr::and(
        ChcExpr::ge(x.clone(), ChcExpr::int(0)),
        ChcExpr::ge(y.clone(), ChcExpr::int(0)),
    );
    assert!(
        solver.is_sat_for_entry_value_inference(&sat_constraint),
        "satisfiable integer constraint should pass the 100ms SAT gate"
    );

    // An unsatisfiable integer constraint: x > 0 AND x < 0
    let unsat_constraint = ChcExpr::and(
        ChcExpr::gt(x.clone(), ChcExpr::int(0)),
        ChcExpr::lt(x, ChcExpr::int(0)),
    );
    assert!(
        !solver.is_sat_for_entry_value_inference(&unsat_constraint),
        "unsatisfiable integer constraint should be rejected by SAT gate"
    );

    // A conjunction with equality and inequality: x = 5 AND y > x
    let eq_ineq = ChcExpr::and(
        ChcExpr::eq(y.clone(), ChcExpr::int(5)),
        ChcExpr::gt(y, ChcExpr::int(3)),
    );
    assert!(
        solver.is_sat_for_entry_value_inference(&eq_ineq),
        "satisfiable equality+inequality constraint should pass the SAT gate"
    );
}
