// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #6853 regression: cross-solver Tseitin state isolation.
//!
//! The root cause of #6853 was that `persistent_sat` (propositional) and
//! `lia_persistent_sat` (LIA) shared a single `tseitin_state`. When a
//! benchmark alternates between SAT and LIA check-sats, Tseitin variables
//! cached for one solver could collide with scope selectors allocated by
//! `push()` in the other. This caused false-UNSAT results.
//!
//! These tests exercise cross-solver push/pop patterns that would fail
//! without per-solver Tseitin state.

use ntest::timeout;

fn results(output: &str) -> Vec<&str> {
    output
        .lines()
        .map(str::trim)
        .filter(|l| *l == "sat" || *l == "unsat" || *l == "unknown")
        .collect()
}

/// Alternating SAT-only and LIA check-sats across push/pop boundaries.
/// Before the fix, the shared Tseitin state would cause the LIA solver to
/// see scope selector variables from the SAT solver (or vice versa),
/// producing false-UNSAT on the second or third cycle.
#[test]
#[timeout(10_000)]
fn test_cross_solver_alternating_sat_lia_push_pop() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const p Bool)

        ; Global: x + y = 10
        (assert (= (+ x y) 10))

        ; --- Cycle 1: LIA scope ---
        (push 1)
        (assert (>= x 3))
        (assert (<= x 7))
        (check-sat)  ; SAT (LIA path)
        (pop 1)

        ; --- SAT-only check (propositional) ---
        (push 1)
        (assert (or p (not p)))
        (check-sat)  ; SAT (SAT path, tautology)
        (pop 1)

        ; --- Cycle 2: LIA scope (would fail without isolation) ---
        (push 1)
        (assert (>= x 2))
        (assert (<= x 8))
        (check-sat)  ; SAT (LIA path again, fresh scope)
        (pop 1)

        ; --- Final global check ---
        (check-sat)  ; SAT (only x + y = 10)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat", "sat", "sat", "sat"]);
}

/// Many interleaved push/pop cycles alternating between LIA and
/// propositional check-sats. This exercises Tseitin variable accumulation
/// over many cycles — the #6853 bug manifested after ~42 cycles.
#[test]
#[timeout(30_000)]
fn test_cross_solver_many_cycles_no_false_unsat() {
    let mut smt = String::from(
        "(set-logic QF_LIA)\n\
         (declare-const x Int)\n\
         (declare-const y Int)\n\
         (declare-const p Bool)\n\
         (assert (= (+ x y) 100))\n",
    );

    let cycle_count = 50;
    let mut expected = Vec::new();

    for i in 0..cycle_count {
        if i % 2 == 0 {
            // LIA check
            smt.push_str("(push 1)\n");
            smt.push_str(&format!("(assert (>= x {i}))\n"));
            smt.push_str(&format!("(assert (<= x {}))\n", 100 - i));
            smt.push_str("(check-sat)\n");
            smt.push_str("(pop 1)\n");
            expected.push("sat");
        } else {
            // Propositional check
            smt.push_str("(push 1)\n");
            smt.push_str("(assert (or p (not p)))\n");
            smt.push_str("(check-sat)\n");
            smt.push_str("(pop 1)\n");
            expected.push("sat");
        }
    }

    let output = crate::common::solve(&smt);
    let actual = results(&output);
    assert_eq!(
        actual.len(),
        expected.len(),
        "expected {} results, got {}",
        expected.len(),
        actual.len()
    );
    for (i, (a, e)) in actual.iter().zip(expected.iter()).enumerate() {
        assert_eq!(
            a, e,
            "cycle {i}: expected {e} but got {a} (cross-solver Tseitin isolation failure)"
        );
    }
}

/// LIA and propositional checks sharing the same push scope.
/// Exercises the case where both solvers are used within a single scope
/// level, then popped together.
#[test]
#[timeout(10_000)]
fn test_cross_solver_same_scope_both_theories() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const p Bool)

        (assert (>= x 0))
        (check-sat)  ; SAT, creates LIA solver

        (push 1)
        ; Add both propositional and LIA constraints in same scope
        (assert p)
        (assert (<= x 10))
        (check-sat)  ; SAT (LIA+prop)
        (pop 1)

        ; After pop, only x >= 0 survives
        (push 1)
        (assert (= x 999))
        (check-sat)  ; SAT (x=999 ≥ 0)
        (pop 1)

        (check-sat)  ; SAT (x >= 0)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat", "sat", "sat", "sat"]);
}

/// Nested push/pop with theory switching at each level.
/// Level 0: global LIA constraint.
/// Level 1: propositional constraint.
/// Level 2: LIA constraint.
/// Pop all the way back and verify global constraint is intact.
#[test]
#[timeout(10_000)]
fn test_cross_solver_nested_theory_switching() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const p Bool)
        (declare-const q Bool)

        ; Global LIA
        (assert (= (+ x y) 42))
        (check-sat)  ; SAT

        (push 1)
        ; Level 1: propositional
        (assert (=> p q))
        (assert p)
        (check-sat)  ; SAT (q must be true, x+y=42)

        (push 1)
        ; Level 2: LIA
        (assert (>= x 100))
        (assert (>= y 100))
        (check-sat)  ; UNSAT (x≥100 ∧ y≥100 ∧ x+y=42)
        (pop 1)

        ; Back to level 1: only x+y=42 and p=>q, p
        (check-sat)  ; SAT
        (pop 1)

        ; Back to global: only x+y=42
        (check-sat)  ; SAT
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat", "sat", "unsat", "sat", "sat"]);
}

/// Rapid push/pop with alternating SAT/UNSAT results across theory switches.
/// This stress-tests that activation scope tracking for both solvers stays
/// correct when assertions are repeatedly scoped and retracted.
#[test]
#[timeout(30_000)]
fn test_cross_solver_rapid_push_pop_sat_unsat_alternation() {
    let mut smt = String::from(
        "(set-logic QF_LIA)\n\
         (declare-const x Int)\n\
         (declare-const y Int)\n\
         (declare-const p Bool)\n\
         (assert (= (+ x y) 50))\n",
    );

    let mut expected = Vec::new();

    for i in 0..30 {
        smt.push_str("(push 1)\n");
        if i % 3 == 0 {
            // LIA SAT: x ∈ [0, 50], always satisfiable with x+y=50.
            // Use a fixed wide range to avoid accidentally making it UNSAT.
            smt.push_str(&format!("(assert (>= x {}))\n", i % 10));
            smt.push_str(&format!("(assert (<= x {}))\n", 50 - (i % 10)));
            smt.push_str("(check-sat)\n");
            expected.push("sat");
        } else if i % 3 == 1 {
            // LIA UNSAT: x ≥ 100 ∧ y ≥ 100 ∧ x+y=50
            smt.push_str("(assert (>= x 100))\n");
            smt.push_str("(assert (>= y 100))\n");
            smt.push_str("(check-sat)\n");
            expected.push("unsat");
        } else {
            // Propositional SAT
            smt.push_str("(assert (or p (not p)))\n");
            smt.push_str("(check-sat)\n");
            expected.push("sat");
        }
        smt.push_str("(pop 1)\n");
    }

    let output = crate::common::solve(&smt);
    let actual = results(&output);
    assert_eq!(actual.len(), expected.len());
    for (i, (a, e)) in actual.iter().zip(expected.iter()).enumerate() {
        assert_eq!(a, e, "iteration {i}: expected {e} but got {a}");
    }
}
