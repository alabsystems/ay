// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for BV incremental push/pop correctness.
//!
//! Mirrors lia_incremental_push_pop.rs pattern for bitvectors.
//! Key invariant: bitvector constraints asserted inside a push scope must not
//! leak after pop.
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

/// Basic push/pop: scoped bitvector constraint must not leak.
#[test]
#[timeout(10_000)]
fn test_bv_incremental_push_pop_no_leak() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))

        ; Base: x = #x0A (10)
        (assert (= x #x0A))
        (check-sat)

        ; Push: x = #xFF contradicts x = #x0A => UNSAT
        (push 1)
        (assert (= x #xFF))
        (check-sat)
        (pop 1)

        ; After pop: only x = #x0A => SAT
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat", "unsat", "sat"]);
}

/// Multiple push/pop cycles with BV.
#[test]
#[timeout(10_000)]
fn test_bv_incremental_multi_push_pop() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))

        ; Base: x != #x00
        (assert (not (= x #x00)))
        (check-sat)

        ; Scope 1: x = #x01
        (push 1)
        (assert (= x #x01))
        (check-sat)
        (pop 1)

        ; Scope 2: x = #xFF — SAT if scope 1 didn't leak
        (push 1)
        (assert (= x #xFF))
        (check-sat)
        (pop 1)

        ; Global: just x != 0 => SAT
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat", "sat", "sat", "sat"]);
}

/// Nested push/pop with BV.
#[test]
#[timeout(10_000)]
fn test_bv_incremental_nested_push_pop() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))

        ; Base: bvuge x #x10 (x >= 16 unsigned)
        (assert (bvuge x #x10))
        ; Level 0: SAT
        (check-sat)

        (push 1)
        ; Level 1: x <= 32 unsigned
        (assert (bvule x #x20))
        ; 16 <= x <= 32 => SAT
        (check-sat)

        (push 1)
        ; Level 2: x < 16 contradicts x >= 16
        (assert (bvult x #x10))
        (check-sat)
        (pop 1)

        ; Back to level 1: SAT
        (check-sat)
        (pop 1)

        ; Back to level 0: SAT (x >= 16)
        (check-sat)

        ; Verify no leak: x = #xFF should be SAT (no x <= 32 leaked)
        (push 1)
        (assert (= x #xFF))
        (check-sat)
        (pop 1)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(
        results(&output),
        vec!["sat", "sat", "unsat", "sat", "sat", "sat"]
    );
}

/// BV bitwise operations across push/pop.
#[test]
#[timeout(10_000)]
fn test_bv_incremental_bitwise_scope() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))

        ; Base: x AND y = #x0F
        (assert (= (bvand x y) #x0F))
        (check-sat)

        ; Push: x = #x0F AND y = #xFF => bvand = #x0F => SAT
        (push 1)
        (assert (= x #x0F))
        (assert (= y #xFF))
        (check-sat)
        (pop 1)

        ; Push: x AND y = #x0F AND x AND y = #xF0 => UNSAT
        (push 1)
        (assert (= (bvand x y) #xF0))
        (check-sat)
        (pop 1)

        ; Global: still SAT
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat", "sat", "unsat", "sat"]);
}

/// A proof snapshot must not detach the persistent SAT trace between checks.
#[test]
#[timeout(10_000)]
fn test_bv_incremental_repeated_unsat_proof_snapshots() {
    let smt = r#"
        (set-option :produce-proofs true)
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (push 1)
        (assert (= x #x01))
        (assert (= x #x02))
        (check-sat)
        (get-proof)
        (pop 1)
        (push 1)
        (assert (= x #x03))
        (assert (= x #x04))
        (check-sat)
        (get-proof)
        (pop 1)
    "#;
    let output = crate::common::solve_vec(smt);
    assert_eq!(
        output.len(),
        4,
        "expected two verdict/proof pairs: {output:?}"
    );
    assert_eq!(output[0].trim(), "unsat");
    assert_eq!(output[2].trim(), "unsat");
    for proof in [&output[1], &output[3]] {
        assert!(!proof.trim().is_empty(), "proof output must not be empty");
        assert!(!proof.contains("proof is not available"), "{proof}");
        assert!(!proof.trim_start().starts_with("(error"), "{proof}");
    }
}
