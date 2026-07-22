// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for Gap A (#7912): DPLL empty-assertions fast path.
//!
//! The check_sat_assuming() method has a fast path that returns SAT immediately
//! when both base_assertions and assumptions are empty. This bypasses the
//! normal theory-solving pipeline. These tests verify that fast path is correct
//! across different logic declarations.

#![allow(clippy::panic)]

use ntest::timeout;

fn results(output: &str) -> Vec<&str> {
    output
        .lines()
        .map(str::trim)
        .filter(|l| *l == "sat" || *l == "unsat" || *l == "unknown")
        .collect()
}

/// Gap A: Empty formula with no assertions is trivially SAT (QF_LIA).
#[test]
#[timeout(10_000)]
fn test_gap_a_empty_formula_qf_lia() {
    let smt = "(set-logic QF_LIA)\n(check-sat)\n";
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}

/// Gap A: Empty formula with no assertions is trivially SAT (QF_LRA).
#[test]
#[timeout(10_000)]
fn test_gap_a_empty_formula_qf_lra() {
    let smt = "(set-logic QF_LRA)\n(check-sat)\n";
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}

/// Gap A: Empty formula with no assertions is trivially SAT (QF_BV).
#[test]
#[timeout(10_000)]
fn test_gap_a_empty_formula_qf_bv() {
    let smt = "(set-logic QF_BV)\n(check-sat)\n";
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}

/// Gap A: Empty formula with no assertions is trivially SAT (QF_UF).
#[test]
#[timeout(10_000)]
fn test_gap_a_empty_formula_qf_uf() {
    let smt = "(set-logic QF_UF)\n(check-sat)\n";
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}

/// Gap A: Declared variables but no assertions is SAT.
/// This is a slightly different path: variables exist but no constraints.
#[test]
#[timeout(10_000)]
fn test_gap_a_declared_vars_no_assertions() {
    let smt = r#"
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(check-sat)
"#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}

/// Gap A: Multiple check-sats where the first has no assertions.
/// Ensures the fast path doesn't corrupt state for subsequent calls.
#[test]
#[timeout(10_000)]
fn test_gap_a_empty_then_constrained() {
    let smt = r#"
(set-logic QF_LIA)
(check-sat)
(declare-const x Int)
(assert (> x 5))
(assert (< x 3))
(check-sat)
"#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat", "unsat"]);
}

/// Gap A: check-sat-assuming with empty assumptions on empty assertions.
/// This exercises the check_sat_assuming() fast path directly.
#[test]
#[timeout(10_000)]
fn test_gap_a_check_sat_assuming_empty() {
    let smt = r#"
(set-logic QF_LIA)
(check-sat-assuming ())
"#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}
