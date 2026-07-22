// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for LRA pending_diseq_splits buffer management (#6269).
//!
//! When check() encounters both single-variable disequalities (which get
//! buffered in pending_diseq_splits) AND multi-variable disequalities (which
//! trigger an early NeedExpressionSplit return), the buffered single-var splits
//! must be drained by the NeedExpressionSplit handler. Without the drain,
//! the buffered splits are silently lost and must be re-discovered on the
//! next check() call, causing redundant work.
//!
//! The clear at check() start (#6269 fix in ad407906f) prevents *duplicate*
//! splits, while the drain in the expression split handler (#6269 acceptance
//! criteria 2) prevents *lost* splits.

use ntest::timeout;

/// Mixed single-var + multi-var disequalities, SAT case.
///
/// x != 3 is a single-variable disequality (DisequalitySplit).
/// x - y != 0 (i.e., x != y) is a multi-variable disequality (ExpressionSplit).
/// Both bounds are loose enough that solutions exist:
///   x in [0, 10], y in [0, 10], x != 3, x != y.
///   e.g., x=1, y=2 satisfies all constraints.
#[test]
#[timeout(10_000)]
fn test_mixed_diseq_single_and_multi_var_sat_6269() {
    let smt = r#"
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 0.0))
(assert (<= x 10.0))
(assert (>= y 0.0))
(assert (<= y 10.0))
(assert (not (= x 3.0)))
(assert (not (= x y)))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "Mixed single-var (x!=3) + multi-var (x!=y) should be SAT"
    );
}

/// Mixed disequalities with tight bounds forcing UNSAT.
///
/// x in [3, 3] forces x=3. Combined with x != 3, this is immediately UNSAT.
/// The multi-var disequality x != y is irrelevant here.
#[test]
#[timeout(10_000)]
fn test_mixed_diseq_single_var_forces_unsat_6269() {
    let smt = r#"
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 3.0))
(assert (<= x 3.0))
(assert (not (= x 3.0)))
(assert (not (= x y)))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "x=3 AND x!=3 should be UNSAT regardless of multi-var diseq"
    );
}

/// Multiple single-var disequalities + one multi-var disequality, SAT.
///
/// x != 1, x != 2, x != 3 are three single-var disequalities.
/// x - y != 0 is a multi-var disequality.
/// x in [0, 10], y in [0, 10] has plenty of room.
/// This exercises the batch collection: all three single-var splits
/// should be buffered before the multi-var triggers ExpressionSplit.
#[test]
#[timeout(10_000)]
fn test_mixed_diseq_multiple_single_plus_multi_sat_6269() {
    let smt = r#"
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 0.0))
(assert (<= x 10.0))
(assert (>= y 0.0))
(assert (<= y 10.0))
(assert (not (= x 1.0)))
(assert (not (= x 2.0)))
(assert (not (= x 3.0)))
(assert (not (= x y)))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "Three single-var diseqs + one multi-var diseq should be SAT"
    );
}

/// Multiple multi-var disequalities with single-var, SAT.
///
/// x != y AND x != z are both multi-var disequalities.
/// x != 5 is a single-var disequality.
/// All in the same formula exercises the buffer drain path thoroughly.
#[test]
#[timeout(10_000)]
fn test_mixed_diseq_two_multi_one_single_sat_6269() {
    let smt = r#"
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (>= x 0.0))
(assert (<= x 10.0))
(assert (>= y 0.0))
(assert (<= y 10.0))
(assert (>= z 0.0))
(assert (<= z 10.0))
(assert (not (= x 5.0)))
(assert (not (= x y)))
(assert (not (= x z)))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "One single-var + two multi-var diseqs should be SAT"
    );
}

/// Tight UNSAT: x = y forced, then x != y is contradictory.
///
/// The single-var disequality x != 5 is satisfiable, but the multi-var
/// x != y combined with x = y forces UNSAT.
#[test]
#[timeout(10_000)]
fn test_mixed_diseq_multi_var_forces_unsat_6269() {
    let smt = r#"
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 0.0))
(assert (<= x 10.0))
(assert (= x y))
(assert (not (= x 5.0)))
(assert (not (= x y)))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "x=y AND x!=y should be UNSAT");
}

/// Targeted drain-path regression: single-var disequalities buffered before
/// a multi-var NeedExpressionSplit early return (#6269 acceptance criteria 2).
///
/// This test is designed so that simplex assigns a=3, b=3 (lower bounds of
/// their ranges). The disequalities are asserted in this order:
///   1. a != 3  (single-var, `expr.coeffs.len() == 1`) — violated when a=3,
///      but a has slack [3, 10], so it is **buffered** in `pending_diseq_splits`.
///   2. a != b  (multi-var, `expr.coeffs.len() > 1`) — violated when a=b=3,
///      triggers immediate `NeedExpressionSplit` return from check().
///
/// At the NeedExpressionSplit return, `pending_diseq_splits` contains the
/// buffered `a != 3` split from step 1. The split-loop drain path collects
/// this split alongside the
/// expression split so it is not lost. Without the drain, the solver would
/// need an extra check() cycle to rediscover the `a != 3` split.
///
/// Two additional single-var disequalities (a != 4, a != 5) are included so
/// the drain path processes multiple buffered entries, testing the batch case.
///
/// Expected: SAT (e.g., a=6, b=7 satisfies all constraints).
#[test]
#[timeout(10_000)]
fn test_drain_path_buffered_singles_before_multi_expr_split_6269() {
    let smt = r#"
(set-logic QF_LRA)
(declare-const a Real)
(declare-const b Real)
(assert (>= a 3.0))
(assert (<= a 10.0))
(assert (>= b 3.0))
(assert (<= b 10.0))
; Single-var disequalities — asserted first so they appear earlier in the
; disequality iteration and are buffered before the multi-var split fires.
(assert (not (= a 3.0)))
(assert (not (= a 4.0)))
(assert (not (= a 5.0)))
; Multi-var disequality — asserted last so it is evaluated after the
; single-var disequalities are already buffered in pending_diseq_splits.
(assert (not (= a b)))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "Three single-var (a!=3,4,5) + one multi-var (a!=b) should be SAT"
    );
}

/// Same drain-path scenario as above but with tight constraints forcing UNSAT.
///
/// a in [3, 5], b in [3, 5]:
///   a != 3, a != 4, a != 5 eliminates all integer-like values, but this is
///   QF_LRA so non-integer values (e.g., a=3.5) are allowed.
///   a = b is additionally asserted, then a != b contradicts it → UNSAT.
///
/// The key property: the single-var disequalities are still iterated before
/// the multi-var `a != b`, so any that are violated get buffered before the
/// expression split fires. In this case a is pinned (a=b forced), so the
/// single-var diseqs may trigger the forced-equality UNSAT path instead.
/// This tests that the drain path does not corrupt state on the UNSAT path.
#[test]
#[timeout(10_000)]
fn test_drain_path_unsat_with_forced_equality_6269() {
    let smt = r#"
(set-logic QF_LRA)
(declare-const a Real)
(declare-const b Real)
(assert (>= a 3.0))
(assert (<= a 5.0))
(assert (>= b 3.0))
(assert (<= b 5.0))
(assert (= a b))
(assert (not (= a 3.0)))
(assert (not (= a 4.0)))
(assert (not (= a b)))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "a=b AND a!=b is UNSAT regardless of other disequalities"
    );
}
