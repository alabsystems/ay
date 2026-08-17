// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Prover verification tests for #4665: cross-theory disequality propagation
//! from arithmetic (LIA/LRA) to arrays. Exercises ROW2 axiom firing when
//! index distinctness is established only by arithmetic reasoning.
//!
//! These tests cover QF_AUFLIA, QF_AUFLRA, and QF_AUFLIRA logics.

use ntest::timeout;

// === QF_AUFLIA: Integer Arithmetic + Arrays ===

#[test]
#[timeout(10_000)]
fn qf_auflia_row2_linear_offset_unsat() {
    // j = i + 2 implies i ≠ j. ROW2: select(store(a,i,v),j) = select(a,j).
    // Combined with select(store(a,i,99),j) = 99 and select(a,j) ≠ 99 → unsat.
    let outputs = crate::common::solve_vec(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (assert (= j (+ i 2)))
        (assert (= (select (store a i 99) j) 99))
        (assert (not (= (select a j) 99)))
        (check-sat)
    "#,
    );
    assert_eq!(outputs[0], "unsat", "j=i+2 implies ROW2 applies");
}

#[test]
#[timeout(10_000)]
fn qf_auflia_row2_negative_offset_unsat() {
    // j = i - 3 implies i ≠ j. ROW2 must fire.
    let outputs = crate::common::solve_vec(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (assert (= j (- i 3)))
        (assert (= (select (store a i 7) j) 7))
        (assert (not (= (select a j) 7)))
        (check-sat)
    "#,
    );
    assert_eq!(outputs[0], "unsat", "j=i-3 implies ROW2 applies");
}

#[test]
#[timeout(10_000)]
fn qf_auflia_row2_multiplication_offset_unsat() {
    // j = 2*i + 1 and i >= 0 implies j ≠ i (since j > i for i >= 0).
    // Even simpler: j = 2*i + 1 and i = 0 → j = 1 ≠ 0 = i.
    let outputs = crate::common::solve_vec(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (assert (= i 0))
        (assert (= j (+ (* 2 i) 1)))
        (assert (= (select (store a i 50) j) 50))
        (assert (not (= (select a j) 50)))
        (check-sat)
    "#,
    );
    assert_eq!(outputs[0], "unsat", "i=0, j=1 implies ROW2 applies");
}

#[test]
#[timeout(10_000)]
fn qf_auflia_row1_equal_indices_sat() {
    // i = j → select(store(a,i,42),j) = 42 (ROW1). Should be SAT.
    let outputs = crate::common::solve_vec(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (assert (= i j))
        (assert (= (select (store a i 42) j) 42))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "sat",
        "ROW1: equal indices, so select = stored value"
    );
}

#[test]
#[timeout(10_000)]
fn qf_auflia_row2_distinct_concrete_sat() {
    // i ≠ j with select(store(a,i,42),j) = select(a,j). This is consistent (ROW2).
    let outputs = crate::common::solve_vec(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (assert (not (= i j)))
        (assert (= (select (store a i 42) j) (select a j)))
        (check-sat)
    "#,
    );
    assert_eq!(outputs[0], "sat", "ROW2 applied correctly: consistent");
}

#[test]
#[timeout(10_000)]
fn qf_auflia_two_stores_different_indices() {
    // store(store(a,i,v1),j,v2) where j = i+1.
    // select at index i should give v1 (ROW2 through j, then ROW1 at i).
    let outputs = crate::common::solve_vec(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (declare-const v1 Int)
        (declare-const v2 Int)
        (assert (= j (+ i 1)))
        (assert (not (= (select (store (store a i v1) j v2) i) v1)))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "select through two stores: j≠i from arithmetic, ROW2 skips j, ROW1 reads i"
    );
}

#[test]
#[timeout(10_000)]
fn qf_auflia_three_stores_chain() {
    // Three stores at indices i, i+1, i+2. Reading at i+1 should give v2.
    let outputs = crate::common::solve_vec(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (assert (= (select (store (store (store a i 10) (+ i 1) 20) (+ i 2) 30) (+ i 1)) 20))
        (check-sat)
    "#,
    );
    assert_eq!(outputs[0], "sat", "chain of 3 stores: read at i+1 = 20");
}

#[test]
#[timeout(10_000)]
fn qf_auflia_three_stores_chain_wrong_value() {
    // Three stores at indices i, i+1, i+2. Reading at i+1 must NOT be 10 (that's at i).
    let outputs = crate::common::solve_vec(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (assert (= (select (store (store (store a i 10) (+ i 1) 20) (+ i 2) 30) (+ i 1)) 10))
        (assert (not (= 10 20)))
        (check-sat)
    "#,
    );
    // This should be unsat: select at i+1 through store at i+2 (ROW2: i+2≠i+1),
    // then direct hit at store at i+1 (ROW1), so value = 20, not 10.
    assert_eq!(
        outputs[0], "unsat",
        "chain of 3 stores: read at i+1 gives 20, not 10"
    );
}

include!("array_cross_theory_prover_4665/mixed_arithmetic_and_regressions.rs");

// === AUFLRA push/pop phantom axiom regression (#6733) ===

/// Regression test for #6733: solve_auf_lra must drain generated array axioms
/// instead of leaving them in ctx.assertions. Without the drain, axioms from
/// popped scopes accumulate as phantom assertions across check-sat calls.
#[test]
#[timeout(10_000)]
fn auflra_push_pop_phantom_axiom_regression_6733() {
    let outputs = crate::common::solve_vec(
        r#"
        (set-logic QF_AUFLRA)
        (declare-const a (Array Int Real))
        (check-sat)
        (push 1)
        (assert (= (select (store a 0 1.5) 0) 2.5))
        (check-sat)
        (pop 1)
        (check-sat)
    "#,
    );
    assert_eq!(outputs[0], "sat", "base scope before push");
    assert_eq!(outputs[1], "unsat", "inner scope: 1.5 != 2.5");
    assert_eq!(
        outputs[2], "sat",
        "after pop: must be sat, not unknown from phantom axioms (#6733)"
    );
}
