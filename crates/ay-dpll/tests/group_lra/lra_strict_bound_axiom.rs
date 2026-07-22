// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Tests for LRA strict bound axiom correctness.
//!
//! The bound ordering axiom system generates SAT-level binary clauses encoding
//! implications between bound atoms on the same variable. When both strict and
//! non-strict bounds exist at the same value k, the axiom must account for
//! strictness:
//!
//!   (x >= k) does NOT imply (x > k)  — counterexample: x = k
//!   (x <= k) does NOT imply (x < k)  — counterexample: x = k
//!
//! An incorrect axiom at the boundary (e.g., ~(x>=3) ∨ (x>3)) eliminates
//! the satisfying assignment x=3, causing false UNSAT.

use ntest::timeout;

/// x = 3 is the only solution. Both (x >= 3) and (x > 3) are theory atoms.
/// Non-incremental mode: equality decomposition prevents the equality axiom
/// bug, but the mk_bound_axiom_terms bug could still fire if same-bound-value
/// same-direction atoms are NOT filtered by the dedup check.
///
/// In current code, the dedup check at generate_bound_axiom_terms line 4452
/// skips pairs with same bound_value AND same is_upper. This test verifies
/// that behavior.
#[test]
#[timeout(10_000)]
fn test_lra_strict_lower_bound_axiom_sat() {
    let smt = r#"
(set-logic QF_LRA)
(declare-const x Real)
(assert (>= x 3.0))
(assert (<= x 3.0))
(assert (not (> x 3.0)))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "x=3 satisfies x>=3, x<=3, not(x>3)");
}

/// Symmetric test for upper bounds: x <= 3 AND x >= 3 AND NOT(x < 3).
#[test]
#[timeout(10_000)]
fn test_lra_strict_upper_bound_axiom_sat() {
    let smt = r#"
(set-logic QF_LRA)
(declare-const x Real)
(assert (<= x 3.0))
(assert (>= x 3.0))
(assert (not (< x 3.0)))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "x=3 satisfies x<=3, x>=3, not(x<3)");
}

/// Mixed lower/upper strict boundary: x >= 3 AND x < 4 AND NOT(x > 3).
#[test]
#[timeout(10_000)]
fn test_lra_mixed_strict_nonstrict_same_var_sat() {
    let smt = r#"
(set-logic QF_LRA)
(declare-const x Real)
(assert (>= x 3.0))
(assert (< x 4.0))
(assert (not (> x 3.0)))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "x=3 satisfies x>=3, x<4, not(x>3)");
}

// ============================================================================
// Incremental mode tests — these use push/pop to trigger the incremental
// path where equality decomposition is skipped, exercising the equality
// axiom code at lib.rs:4484-4521.
// ============================================================================

/// Incremental mode: (= x 3) AND NOT(x > 3) AND (x >= 3).
/// The equality axiom should NOT generate ~eq ∨ (x > 3) because x=3
/// does NOT imply x > 3.
#[test]
#[timeout(10_000)]
fn test_lra_equality_strict_lower_axiom_incremental_sat() {
    let smt = r#"
(set-logic QF_LRA)
(declare-const x Real)
(push 1)
(assert (= x 3.0))
(assert (not (> x 3.0)))
(assert (>= x 3.0))
(check-sat)
(pop 1)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "incremental: x=3 satisfies (= x 3), not(x>3), x>=3"
    );
}

/// Incremental mode: (= x 3) AND NOT(x < 3) AND (x <= 3).
#[test]
#[timeout(10_000)]
fn test_lra_equality_strict_upper_axiom_incremental_sat() {
    let smt = r#"
(set-logic QF_LRA)
(declare-const x Real)
(push 1)
(assert (= x 3.0))
(assert (not (< x 3.0)))
(assert (<= x 3.0))
(check-sat)
(pop 1)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "incremental: x=3 satisfies (= x 3), not(x<3), x<=3"
    );
}

/// Two incremental queries: first x=3, then x=5. Both SAT.
/// Verifies that the equality axiom bug doesn't cause false UNSAT
/// across multiple push/pop cycles.
#[test]
#[timeout(10_000)]
fn test_lra_equality_strict_axiom_multi_query() {
    let smt = r#"
(set-logic QF_LRA)
(declare-const x Real)
(push 1)
(assert (= x 3.0))
(assert (>= x 3.0))
(assert (not (> x 3.0)))
(check-sat)
(pop 1)
(push 1)
(assert (= x 5.0))
(assert (<= x 5.0))
(assert (not (< x 5.0)))
(check-sat)
(pop 1)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat", "sat"],
        "both queries should be SAT: x=3 and x=5 respectively"
    );
}

/// Cross-direction strict bound test: (x >= 3) AND (x < 3).
/// This should be UNSAT — no real x satisfies both x >= 3 and x < 3.
/// The axiom between lower(3, non-strict) and upper(3, strict) should
/// correctly encode their mutual exclusion: ~(x>=3) ∨ ~(x<3).
#[test]
#[timeout(10_000)]
fn test_lra_cross_direction_strict_conflict_unsat() {
    let smt = r#"
(set-logic QF_LRA)
(declare-const x Real)
(assert (>= x 3.0))
(assert (< x 3.0))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "x >= 3 AND x < 3 has no solution");
}
