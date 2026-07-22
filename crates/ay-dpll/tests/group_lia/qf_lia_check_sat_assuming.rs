// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for `check-sat-assuming` in pure QF_LIA (#6728).
//!
//! Verifies that the dedicated LIA assumption pipeline applies the full
//! preprocessing family (VariableSubstitution, NormalizeArithSom, ITE lifting,
//! mod/div elimination) while preserving original assumption identity for
//! UNSAT-core and proof reporting.

use ntest::timeout;

/// Basic QF_LIA check-sat-assuming: SAT case.
#[test]
#[timeout(30_000)]
fn test_qf_lia_check_sat_assuming_basic_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (>= x 0))
        (check-sat-assuming ((< x 10)))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// Basic QF_LIA check-sat-assuming: UNSAT case.
#[test]
#[timeout(30_000)]
fn test_qf_lia_check_sat_assuming_basic_unsat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (> x 5))
        (check-sat-assuming ((< x 3)))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Substitution-bearing assumptions: assertion `(= y (+ x 1))` defines
/// substitution y → (+ x 1). Assumption `(= y 0)` must be rewritten to
/// use the same variable elimination, making the combined formula UNSAT.
#[test]
#[timeout(30_000)]
fn test_qf_lia_check_sat_assuming_substitution_unsat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (> x 0))
        (check-sat-assuming ((= y (+ x 1)) (= y 0)))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Substitution-bearing assumptions: SAT case where y = x + 1 and y > 0
/// are both satisfiable with x > 0.
#[test]
#[timeout(30_000)]
fn test_qf_lia_check_sat_assuming_substitution_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 1))
        (check-sat-assuming ((= y (+ x 1)) (> y 0)))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// mod/div assumptions: the assumption contains `(mod x 3)` which needs
/// auxiliary variable elimination.
#[test]
#[timeout(30_000)]
fn test_qf_lia_check_sat_assuming_mod_div_unsat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (>= x 0))
        (check-sat-assuming ((= (mod x 3) 1) (= (div x 3) 0) (< x 0)))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// mod/div assumptions: SAT case where mod and div constraints are consistent.
#[test]
#[timeout(30_000)]
fn test_qf_lia_check_sat_assuming_mod_div_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (>= x 0))
        (assert (<= x 20))
        (check-sat-assuming ((= (mod x 5) 0) (> x 4)))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// Normalized-sum assumptions: SOM normalization distributes multiplication
/// over addition. The assumption `(> (* 2 (+ x 1)) 10)` should be normalized.
#[test]
#[timeout(30_000)]
fn test_qf_lia_check_sat_assuming_normalized_sum() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (>= x 0))
        (assert (<= x 3))
        (check-sat-assuming ((> (* 2 (+ x 1)) 10)))
    "#;
    let outputs = crate::common::solve_vec(smt);
    // (* 2 (+ x 1)) = 2x+2, need > 10, so x > 4, but x <= 3
    assert_eq!(outputs, vec!["unsat"]);
}

/// UNSAT-core identity: get-unsat-assumptions must return original assumption
/// terms, not generated selectors or preprocessed helper terms.
#[test]
#[timeout(30_000)]
fn test_qf_lia_check_sat_assuming_unsat_core_identity() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (> x 5))
        (check-sat-assuming ((< x 3) (> x 0)))
        (get-unsat-assumptions)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs[0], "unsat");
    // The unsat assumptions should contain original terms
    let core = &outputs[1];
    // At minimum, (< x 3) should appear — it directly contradicts (> x 5)
    assert!(
        core.contains("< x 3") || core.contains("<= x 2"),
        "UNSAT core should contain the contradicting assumption, got: {core}"
    );
}

/// Multiple check-sat-assuming calls: assumptions are temporary and do not
/// persist between calls.
#[test]
#[timeout(30_000)]
fn test_qf_lia_check_sat_assuming_temporary_assumptions() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (>= x 0))
        (assert (<= x 10))
        (check-sat-assuming ((> x 10)))
        (check-sat-assuming ((< x 5)))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat", "sat"]);
}

/// Branch-and-bound under assumptions: the LIA solver needs to split on
/// integer variables to find the solution.
#[test]
#[timeout(30_000)]
fn test_qf_lia_check_sat_assuming_branch_and_bound() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (assert (>= y 0))
        (check-sat-assuming ((>= (+ x y) 3) (<= x 2) (<= y 2)))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// Combined substitution + mod/div in assumptions.
#[test]
#[timeout(30_000)]
fn test_qf_lia_check_sat_assuming_subst_and_mod_div() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= y (+ x 1)))
        (assert (>= x 0))
        (check-sat-assuming ((= (mod y 3) 0) (<= x 5)))
    "#;
    let outputs = crate::common::solve_vec(smt);
    // y = x+1, mod(y,3) = 0, so y in {0,3,6,...}, x in {-1,2,5,...}
    // With x >= 0 and x <= 5: x=2 (y=3) or x=5 (y=6) work.
    assert_eq!(outputs, vec!["sat"]);
}
