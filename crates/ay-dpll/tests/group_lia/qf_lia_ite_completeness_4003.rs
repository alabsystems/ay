// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #4003: QF_LIA completeness with nested ITE expressions.
//!
//! AY must return Sat or Unsat (not Unknown) on basic QF_LIA verification
//! conditions involving nested `ite` (if-then-else) expressions. These patterns
//! come from the VerifierConsumer ay backend where postconditions on branching Rust code
//! generate ITE-heavy formulas.
//!
//! All 6 VerifierConsumer test patterns that previously accepted `Proven | Unknown` are
//! exercised here to prevent completeness regressions.

use ntest::timeout;

/// VerifierConsumer pattern: `clamp_positive` postcondition 1 — `result >= 1`.
/// clamp(val, 1, n) >= 1 when n >= 1.
#[test]
#[timeout(30_000)]
fn test_qf_lia_ite_clamp_positive_ge_1() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-fun val () Int)
        (declare-fun n () Int)
        (assert (>= n 1))
        (assert (not (>= (ite (< val 1) 1 (ite (> val n) n val)) 1)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "clamp(val, 1, n) >= 1 should be provable (unsat negation)"
    );
}

/// VerifierConsumer pattern: `clamp_positive` postcondition 2 — `result <= n`.
/// clamp(val, 1, n) <= n when n >= 1.
#[test]
#[timeout(30_000)]
fn test_qf_lia_ite_clamp_positive_le_n() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-fun val () Int)
        (declare-fun n () Int)
        (assert (>= n 1))
        (assert (not (<= (ite (< val 1) 1 (ite (> val n) n val)) n)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "clamp(val, 1, n) <= n should be provable (unsat negation)"
    );
}

/// VerifierConsumer pattern: `abs_non_negative` — `abs(x) >= 0`.
#[test]
#[timeout(30_000)]
fn test_qf_lia_ite_abs_non_negative() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-fun x () Int)
        (assert (not (>= (ite (< x 0) (- x) x) 0)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "abs(x) >= 0 should be provable (unsat negation)"
    );
}

/// VerifierConsumer pattern: `min_le_both` — `min(a, b) <= a && min(a, b) <= b`.
#[test]
#[timeout(30_000)]
fn test_qf_lia_ite_min_le_both() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (not (and (<= (ite (<= a b) a b) a)
                         (<= (ite (<= a b) a b) b))))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "min(a,b) <= a && min(a,b) <= b should be provable (unsat negation)"
    );
}

/// VerifierConsumer pattern: `max_ge_both` — `max(a, b) >= a && max(a, b) >= b`.
#[test]
#[timeout(30_000)]
fn test_qf_lia_ite_max_ge_both() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (not (and (>= (ite (>= a b) a b) a)
                         (>= (ite (>= a b) a b) b))))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "max(a,b) >= a && max(a,b) >= b should be provable (unsat negation)"
    );
}

/// VerifierConsumer pattern: `min_max_relationship` — `min(a, b) <= max(a, b)`.
#[test]
#[timeout(30_000)]
fn test_qf_lia_ite_min_le_max() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (not (<= (ite (<= a b) a b) (ite (>= a b) a b))))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "min(a,b) <= max(a,b) should be provable (unsat negation)"
    );
}

/// Deeper nesting: |x| + |y| + |z| >= 0.
#[test]
#[timeout(30_000)]
fn test_qf_lia_ite_triple_abs_sum_non_negative() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun z () Int)
        (assert (not (>= (+ (ite (< x 0) (- x) x)
                            (ite (< y 0) (- y) y)
                            (ite (< z 0) (- z) z)) 0)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "|x| + |y| + |z| >= 0 should be provable (unsat negation)"
    );
}

/// Nested clamp composition: clamp(clamp(x, 0, 10), 2, 8) is in [2, 8].
#[test]
#[timeout(30_000)]
fn test_qf_lia_ite_nested_clamp_bounds() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-fun x () Int)
        (define-fun clamp ((v Int) (lo Int) (hi Int)) Int
            (ite (< v lo) lo (ite (> v hi) hi v)))
        (assert (not (and (>= (clamp (clamp x 0 10) 2 8) 2)
                         (<= (clamp (clamp x 0 10) 2 8) 8))))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "clamp(clamp(x,0,10),2,8) in [2,8] should be provable (unsat negation)"
    );
}

/// ITE in arithmetic: (ite c a b) + (ite c b a) = a + b.
#[test]
#[timeout(30_000)]
fn test_qf_lia_ite_complementary_sum() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (declare-fun c () Bool)
        (assert (not (= (+ (ite c a b) (ite c b a)) (+ a b))))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "(ite c a b) + (ite c b a) = a + b should be provable (unsat negation)"
    );
}

/// ITE value is always one of its branches.
#[test]
#[timeout(30_000)]
fn test_qf_lia_ite_value_is_branch() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun c () Bool)
        (assert (not (or (= (ite c x y) x) (= (ite c x y) y))))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "(ite c x y) is either x or y should be provable (unsat negation)"
    );
}

/// SSA-form pattern: ITE indirection preserves z > y when z = y + 1.
#[test]
#[timeout(30_000)]
fn test_qf_lia_ite_ssa_increment() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (declare-fun c () Int)
        (declare-fun flag1 () Bool)
        (declare-fun flag2 () Bool)
        (define-fun x () Int (ite flag1 a b))
        (define-fun y () Int (ite flag2 x c))
        (define-fun z () Int (+ y 1))
        (assert (not (> z y)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "z = y + 1 implies z > y should be provable through ITE indirection"
    );
}

/// Array bounds VC: clamped index is within bounds.
#[test]
#[timeout(30_000)]
fn test_qf_lia_ite_array_bounds_vc() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-fun idx () Int)
        (declare-fun len () Int)
        (declare-fun lo () Int)
        (declare-fun hi () Int)
        (assert (> len 0))
        (assert (>= lo 0))
        (assert (< hi len))
        (assert (>= hi lo))
        (define-fun clamped () Int (ite (< idx lo) lo (ite (> idx hi) hi idx)))
        (assert (not (and (>= clamped 0) (< clamped len))))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "clamped index within bounds should be provable (unsat negation)"
    );
}
