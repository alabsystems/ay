// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Initial-only value analysis regressions.

use super::*;

// ============================================================================
// Tests for is_init_only_value
// ============================================================================

#[test]
fn is_init_only_value_monotonic_counter() {
    // A counter that only increments: x' = x + 1 with x=0 at init
    // x=0 should be init-only because from x=0 you transition to x'=1, never back to 0
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (x2 Int)) (=> (and (Inv x) (= x2 (+ x 1))) (Inv x2))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.get_predicate_by_name("Inv").unwrap().id;
    let canon_x = solver.canonical_vars(inv).unwrap()[0].name.clone();

    // x=0 should be init-only because from x=0, the only transition is x'=x+1=1, not x'=0
    let is_init_only = solver.is_init_only_value(inv, &canon_x, 0);
    assert!(
        is_init_only,
        "x=0 should be init-only for monotonic counter"
    );
}

#[test]
fn is_init_only_value_resettable_counter() {
    // A counter that can reset: x' = x + 1 OR x' = 0
    // x=0 should NOT be init-only since you can return to 0 via reset
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (x2 Int)) (=> (and (Inv x) (or (= x2 (+ x 1)) (= x2 0))) (Inv x2))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.get_predicate_by_name("Inv").unwrap().id;
    let canon_x = solver.canonical_vars(inv).unwrap()[0].name.clone();

    // x=0 should NOT be init-only because you can reset back to 0 from any state
    let is_init_only = solver.is_init_only_value(inv, &canon_x, 0);
    assert!(
        !is_init_only,
        "x=0 should NOT be init-only for resettable counter"
    );
}

#[test]
fn is_init_only_value_no_self_loop() {
    // A predicate with only a fact clause (no transitions)
    // Any init value should be init-only since there's no way to transition
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 42) (Inv x))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.get_predicate_by_name("Inv").unwrap().id;
    let canon_x = solver.canonical_vars(inv).unwrap()[0].name.clone();

    // x=42 should be init-only because there's no self-loop to change it
    let is_init_only = solver.is_init_only_value(inv, &canon_x, 42);
    assert!(
        is_init_only,
        "x=42 should be init-only when no self-loop exists"
    );
}

#[test]
fn is_init_only_value_semantic_behavior_for_non_init() {
    // Document the semantic behavior: is_init_only_value checks if a value can RECUR
    // from itself via a self-loop, not whether the value is an actual init value.
    // For x'=x+1: from x=V, we get x'=V+1 ≠ V, so ANY value V returns true (can't self-loop).
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (x2 Int)) (=> (and (Inv x) (= x2 (+ x 1))) (Inv x2))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.get_predicate_by_name("Inv").unwrap().id;
    let canon_x = solver.canonical_vars(inv).unwrap()[0].name.clone();

    // x=5 is not an init value. From x=5, we go to x'=6, not x'=5.
    // The query (x=5 ∧ x'=x+1 ∧ x'=5) is UNSAT, so the code will say it's "init-only".
    // This is technically correct: x=5 cannot recur in a self-loop from x=5.
    // But semantically, x=5 is not init-only because it's not even an init value!
    // Note: The is_init_only_value function checks if a VALUE can recur, not if it's an init value.
    // So for the transition x'=x+1, ANY value V satisfies: (x=V ∧ x'=x+1 ∧ x'=V) is UNSAT.
    let is_init_only = solver.is_init_only_value(inv, &canon_x, 5);
    // Counterintuitive but correct: 5 is "init-only" in the sense that it cannot recur
    assert!(
        is_init_only,
        "x=5 cannot recur via x'=x+1, so is_init_only returns true"
    );
}
