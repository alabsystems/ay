// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_LIA P0 canaries (#8707, #8709, #8710).
//!
//! These tests lock in working behavior for pairwise-distinct benchmarks
//! where the solver was previously unsound or incomplete. The full
//! n-queens-8 / SEND+MORE=MONEY canaries are tracked separately in #8707
//! because they require porting Z3's `mutate_assignment`
//! (`reference/z3/src/smt/theory_arith_aux.h:2116-2163`) to perturb the LP
//! assignment between disequality rounds, which is a larger change than
//! fits in this commit.
//!
//! Reference: the development design notes

use ntest::timeout;

/// #8710: QF_LIA bounded-domain distinct with a sum constraint.
/// `(distinct x y) AND (x + y = 10)` over x,y in [1,9] must solve fast.
/// Regression guard: this used to return `unknown` or loop until the
/// no-progress cap triggered.
#[test]
#[timeout(5_000)]
fn test_8710_bounded_domain_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (and (>= x 1) (<= x 9)))
        (assert (and (>= y 1) (<= y 9)))
        (assert (distinct x y))
        (assert (= (+ x y) 10))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "#8710: bounded-domain distinct with sum=10 must be SAT"
    );
}

/// #8709: QF_LIA with nested ITE encoding a lookup table plus arithmetic.
/// Lock in the UNSAT result for the no-feasible-profit instance.
///
/// Pre-fix (before #8727 / commit 13f7a15e0): returned `unknown (incomplete)`
/// because the non-incremental QF_LIA eager arm escalated the post-split
/// UNSAT via the #6812 soundness guard. LIA split clauses
/// (NeedSplit / NeedDisequalitySplit / NeedExpressionSplit) are tautological
/// over the integers, so accepting post-split UNSAT is sound and complete.
#[test]
#[timeout(5_000)]
fn test_8709_nested_ite_unsat() {
    let smt = r#"
        (set-logic QF_LIA)
        (define-fun price ((i Int)) Int
          (ite (= i 0) 3 (ite (= i 1) 1 (ite (= i 2) 4 (ite (= i 3) 1
          (ite (= i 4) 5 (ite (= i 5) 9 (ite (= i 6) 2 (ite (= i 7) 6
          (ite (= i 8) 5 (ite (= i 9) 3 (ite (= i 10) 5 8))))))))))))
        (declare-const buy Int)
        (declare-const sell Int)
        (assert (and (>= buy 0) (< buy 12) (>= sell 0) (< sell 12)))
        (assert (> sell buy))
        (assert (> (- (price sell) (price buy)) 8))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "#8709: nested-ITE price gap > 8 must be UNSAT"
    );
}

/// #8709 SAT companion: same nested-ITE lookup with a feasible gap.
/// `price(5) - price(1) = 9 - 1 = 8`, so `gap = 8` is SAT.
/// Locks in that the `accept_unsat_after_splits` relaxation does not flip
/// SAT cases to UNSAT on ITE-heavy formulas.
#[test]
#[timeout(5_000)]
fn test_8709_nested_ite_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (define-fun price ((i Int)) Int
          (ite (= i 0) 3 (ite (= i 1) 1 (ite (= i 2) 4 (ite (= i 3) 1
          (ite (= i 4) 5 (ite (= i 5) 9 (ite (= i 6) 2 (ite (= i 7) 6
          (ite (= i 8) 5 (ite (= i 9) 3 (ite (= i 10) 5 8))))))))))))
        (declare-const buy Int)
        (declare-const sell Int)
        (assert (and (>= buy 0) (< buy 12) (>= sell 0) (< sell 12)))
        (assert (> sell buy))
        (assert (= (- (price sell) (price buy)) 8))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "#8709: nested-ITE price gap = 8 must be SAT (feasible: sell=5, buy=1)"
    );
}

/// #8709 deeper variant: 20-branch nested ITE lookup, UNSAT via unreachable gap.
/// Max gap is `lookup(19) - lookup(0) = 200 - 10 = 190`, asserting `> 190` is UNSAT.
/// Guards against regressions on deeper nesting where expression-split chains
/// are longer and the #6812 guard would previously escalate all post-split UNSATs.
#[test]
#[timeout(10_000)]
fn test_8709_deep_nested_ite_unsat() {
    let smt = r#"
        (set-logic QF_LIA)
        (define-fun lookup ((i Int)) Int
          (ite (= i 0) 10 (ite (= i 1) 20 (ite (= i 2) 30 (ite (= i 3) 40
          (ite (= i 4) 50 (ite (= i 5) 60 (ite (= i 6) 70 (ite (= i 7) 80
          (ite (= i 8) 90 (ite (= i 9) 100 (ite (= i 10) 110 (ite (= i 11) 120
          (ite (= i 12) 130 (ite (= i 13) 140 (ite (= i 14) 150 (ite (= i 15) 160
          (ite (= i 16) 170 (ite (= i 17) 180 (ite (= i 18) 190 200))))))))))))))))))))
        (declare-const a Int)
        (declare-const b Int)
        (assert (and (>= a 0) (<= a 19)))
        (assert (and (>= b 0) (<= b 19)))
        (assert (> a b))
        (assert (> (- (lookup a) (lookup b)) 190))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "#8709: 20-branch nested-ITE gap > 190 must be UNSAT"
    );
}

/// #8707 (small version): 4-queens minimal repro with pairwise distinct
/// and a diagonal constraint. Mirrors the existing test
/// `lia_all_distinct_false_unsat::test_4queens_minimal_sat` but with a
/// tighter timeout so regressions are caught quickly.
#[test]
#[timeout(5_000)]
fn test_8707_4queens_minimal_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const q1 Int)
        (declare-const q2 Int)
        (declare-const q3 Int)
        (declare-const q4 Int)
        (assert (>= q1 1)) (assert (<= q1 4))
        (assert (>= q2 1)) (assert (<= q2 4))
        (assert (>= q3 1)) (assert (<= q3 4))
        (assert (>= q4 1)) (assert (<= q4 4))
        (assert (not (= q1 q2)))
        (assert (not (= q1 q3)))
        (assert (not (= q1 q4)))
        (assert (not (= q2 q3)))
        (assert (not (= q2 q4)))
        (assert (not (= q3 q4)))
        (assert (not (= (+ q1 (- q2)) 1)))
        (assert (not (= (+ q1 (- q2)) (- 1))))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "#8707: 4-queens minimal repro must be SAT (part of the same chain)"
    );
}

/// #8707: 5-queens full row+diag1+diag2 distinct. Locks in that the lazy
/// theory reason pre-materialization / 1UIP interaction does not return
/// false UNSAT on a straightforward SAT instance. Z3 witness: 1 3 0 2 4.
#[test]
#[timeout(10_000)]
fn test_8707_5queens_full_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const q0 Int) (declare-const q1 Int) (declare-const q2 Int)
        (declare-const q3 Int) (declare-const q4 Int)
        (assert (and (>= q0 0) (<= q0 4) (>= q1 0) (<= q1 4) (>= q2 0) (<= q2 4)
                     (>= q3 0) (<= q3 4) (>= q4 0) (<= q4 4)))
        (assert (distinct q0 q1 q2 q3 q4))
        (assert (distinct (- q0 0) (- q1 1) (- q2 2) (- q3 3) (- q4 4)))
        (assert (distinct (+ q0 0) (+ q1 1) (+ q2 2) (+ q3 3) (+ q4 4)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "#8707: 5-queens with 3 pairwise-distinct constraints must be SAT"
    );
}

/// #8707: 6-queens full row+diag1+diag2 distinct. The original bug report:
/// the debug build panicked on the `resolvent_size == counter + learned_count`
/// invariant at `conflict_analysis.rs:544`, release returned `unsat`. Z3
/// witness: 1 3 5 0 2 4.
///
/// Root cause fix: when `materialize_current_level_lazy_reasons` fails on
/// a current-level lazy theory reason, `analyze_conflict` now aborts (via
/// the `cold.lazy_materialization_failed` flag) and the caller backtracks
/// to level 0. This avoids learning a clause derived from fake-decision
/// bookkeeping, which was NOT RUP-derivable and caused false UNSAT.
#[test]
#[timeout(30_000)]
fn test_8707_6queens_full_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const q0 Int) (declare-const q1 Int) (declare-const q2 Int)
        (declare-const q3 Int) (declare-const q4 Int) (declare-const q5 Int)
        (assert (and (>= q0 0) (<= q0 5) (>= q1 0) (<= q1 5) (>= q2 0) (<= q2 5)
                     (>= q3 0) (<= q3 5) (>= q4 0) (<= q4 5) (>= q5 0) (<= q5 5)))
        (assert (distinct q0 q1 q2 q3 q4 q5))
        (assert (distinct (- q0 0) (- q1 1) (- q2 2) (- q3 3) (- q4 4) (- q5 5)))
        (assert (distinct (+ q0 0) (+ q1 1) (+ q2 2) (+ q3 3) (+ q4 4) (+ q5 5)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "#8707: 6-queens must be SAT (was false UNSAT due to fake-decision bookkeeping)"
    );
}
