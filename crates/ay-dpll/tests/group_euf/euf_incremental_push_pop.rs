// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for EUF incremental push/pop correctness.
//!
//! Mirrors lia_incremental_push_pop.rs pattern for uninterpreted functions.
//! Key invariant: equalities and function applications asserted inside a push
//! scope must not leak after pop.
//!
//! Part of #2812

use ntest::timeout;

fn results(output: &str) -> Vec<&str> {
    output
        .lines()
        .map(str::trim)
        .filter(|l| *l == "sat" || *l == "unsat" || *l == "unknown")
        .collect()
}

/// Basic push/pop: scoped equality must not leak.
#[test]
#[timeout(10_000)]
fn test_euf_incremental_push_pop_no_leak() {
    let smt = r#"
        (set-logic QF_UF)
        (declare-sort S 0)
        (declare-const a S)
        (declare-const b S)

        ; Base: a != b
        (assert (not (= a b)))
        (check-sat)

        ; Push: assert a = b => UNSAT
        (push 1)
        (assert (= a b))
        (check-sat)
        (pop 1)

        ; After pop: only a != b survives => SAT
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat", "unsat", "sat"]);
}

/// Congruence closure across push/pop scopes.
/// Tests that f(a) = f(b) from a pushed a = b doesn't persist after pop.
#[test]
#[timeout(10_000)]
fn test_euf_incremental_congruence_scope() {
    let smt = r#"
        (set-logic QF_UF)
        (declare-sort S 0)
        (declare-fun f (S) S)
        (declare-const a S)
        (declare-const b S)

        ; Base: f(a) != f(b)
        (assert (not (= (f a) (f b))))
        (check-sat)

        ; Push: a = b => f(a) = f(b) by congruence => UNSAT with base
        (push 1)
        (assert (= a b))
        (check-sat)
        (pop 1)

        ; After pop: f(a) != f(b) and no a = b => SAT
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat", "unsat", "sat"]);
}

/// Multiple push/pop cycles with EUF.
#[test]
#[timeout(10_000)]
fn test_euf_incremental_multi_push_pop() {
    let smt = r#"
        (set-logic QF_UF)
        (declare-sort S 0)
        (declare-const a S)
        (declare-const b S)
        (declare-const c S)

        ; Base: a = b
        (assert (= a b))
        (check-sat)

        ; Scope 1: b = c
        (push 1)
        (assert (= b c))
        ; a = b AND b = c => a = c by transitivity => SAT
        (check-sat)
        (pop 1)

        ; Scope 2: a != c (should be SAT since b = c popped)
        (push 1)
        (assert (not (= a c)))
        (check-sat)
        (pop 1)

        ; Global: just a = b => SAT
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat", "sat", "sat", "sat"]);
}

/// Nested push/pop with EUF transitivity chains.
#[test]
#[timeout(10_000)]
fn test_euf_incremental_nested_push_pop() {
    let smt = r#"
        (set-logic QF_UF)
        (declare-sort S 0)
        (declare-const a S)
        (declare-const b S)
        (declare-const c S)
        (declare-const d S)

        ; Base: a != d
        (assert (not (= a d)))
        (check-sat)

        (push 1)
        (assert (= a b))
        ; Level 1: a != d AND a = b => SAT
        (check-sat)

        (push 1)
        (assert (= b c))
        (assert (= c d))
        ; Level 2: a = b, b = c, c = d => a = d. But a != d => UNSAT
        (check-sat)
        (pop 1)

        ; Back to level 1: a != d AND a = b => SAT (b=c, c=d popped)
        (check-sat)
        (pop 1)

        ; Back to level 0: a != d => SAT (a=b popped)
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat", "sat", "unsat", "sat", "sat"]);
}

/// Regression test for #2822: global assertions must survive scope cycling.
///
/// The bug: pre-push EUF assertions were encoded with an activation literal
/// scoped to the push level, then deactivated after pop. This test verifies
/// that global disequalities remain active across push/pop cycles by checking
/// that a scoped equality contradicting a global disequality produces UNSAT.
#[test]
#[timeout(10_000)]
fn test_euf_global_assertion_survives_scope_cycle() {
    let smt = r#"
        (set-logic QF_UF)
        (declare-sort S 0)
        (declare-fun f (S) S)
        (declare-const a S)
        (declare-const b S)
        (declare-const c S)

        ; Global: a != b
        (assert (not (= a b)))
        (check-sat)

        ; First scope: unrelated equality
        (push 1)
        (assert (= b c))
        (check-sat)
        (pop 1)

        ; Second scope: a = b contradicts global a != b
        ; If global (not (= a b)) was lost after first pop, this would be SAT
        (push 1)
        (assert (= a b))
        (check-sat)
        (pop 1)

        ; Global disequality still holds
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat", "sat", "unsat", "sat"]);
}

/// Proof-enabled push/pop must preserve structured EUF congruence proofs (#6716).
#[test]
#[timeout(10_000)]
fn test_euf_incremental_push_pop_proof_uses_eq_congruent_6716() {
    let smt = r#"
        (set-logic QF_UF)
        (set-option :produce-proofs true)
        (declare-sort S 0)
        (declare-fun f (S) S)
        (declare-const a S)
        (declare-const b S)
        (push 1)
        (assert (= a b))
        (assert (not (= (f a) (f b))))
        (check-sat)
        (get-proof)
    "#;
    let output = crate::common::solve_vec(smt);
    assert_eq!(output.len(), 2);
    assert_eq!(output[0].trim(), "unsat");
    assert!(
        output[1].contains(":rule eq_congruent"),
        "expected eq_congruent proof in push/pop EUF path:\n{}",
        output[1]
    );
    assert!(
        !output[1].contains(":rule trust"),
        "push/pop EUF proof must not fall back to trust:\n{}",
        output[1]
    );
}

/// Regression for #6813: popped-scope predicate applications must not shadow
/// live predicate entries during model extraction.
#[test]
#[timeout(10_000)]
fn test_euf_incremental_model_extraction_ignores_popped_predicate_shadow_6813() {
    let smt = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun p (U) Bool)
        (declare-const a U)
        (declare-const b U)

        ; Dead predicate application from the inner scope.
        (push 1)
        (assert (not (p a)))
        (check-sat)
        (pop 1)

        ; After pop, a = b makes the dead (p a) and live (p b) share the same
        ; canonical argument tuple. Model extraction must use only live roots.
        (assert (= a b))
        (assert (p b))
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat", "sat"]);
}
