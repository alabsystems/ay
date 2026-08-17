// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// =============================================================================
// Prover algorithm audit: str.to_int variable soundness (b62349bdc audit)
//
// After reducing false incompleteness in check_extf_int_reductions, positive
// equalities involving str.to_int / str.to_code with unresolved arguments
// no longer force Unknown. These tests verify the solver does NOT return
// false SAT when the str-to-int mapping is unsatisfiable.
// =============================================================================

/// str.to_int(x) = 5 with x completely free.
/// Should return SAT or Unknown (x = "5" is a valid model).
/// Must NOT return UNSAT.
#[test]
#[timeout(10_000)]
fn soundness_str_to_int_variable_positive_equality_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.to_int x) 5))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        r == Some("sat") || r == Some("unknown"),
        "str.to_int(x) = 5 is satisfiable (x=\"5\"), got {r:?}",
    );
}

/// str.to_int(x) = -2 with x free: UNSAT.
/// str.to_int returns -1 for non-numeric strings, so no string maps to -2.
/// The solver should detect this (or return unknown, not false SAT).
///
/// Regression for b62349bdc: reducing incomplete marking in
/// check_extf_int_reductions caused false SAT for out-of-range values.
/// The LIA solver treats str.to_int(x) as uninterpreted and happily
/// assigns -2, but no string actually maps to -2 under SMT-LIB semantics.
#[test]
#[timeout(10_000)]
fn soundness_str_to_int_variable_impossible_value() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.to_int x) (- 2)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        r == Some("unsat") || r == Some("unknown"),
        "str.to_int(x) = -2 is unsatisfiable (range is {{-1}} union Z>=0), got {r:?}",
    );
}

/// str.to_int(x) = 5 AND str.len(x) = 3: UNSAT.
/// "5" has length 1, not 3. No 3-char string has str.to_int = 5
/// (e.g., "005" has str.to_int = 5 — wait, that IS valid).
/// Actually "005" has str.to_int("005") = 5 and len("005") = 3.
/// So this is SAT, not UNSAT.
#[test]
#[timeout(10_000)]
fn soundness_str_to_int_with_length_constraint() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.to_int x) 5))
(assert (= (str.len x) 3))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        r == Some("sat") || r == Some("unknown"),
        "str.to_int(x)=5, len(x)=3 is SAT (x=\"005\"), got {r:?}",
    );
}

/// str.to_code(x) = 65 with x free: SAT (x = "A").
#[test]
#[timeout(10_000)]
fn soundness_str_to_code_variable_positive_equality_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.to_code x) 65))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        r == Some("sat") || r == Some("unknown"),
        "str.to_code(x) = 65 is satisfiable (x=\"A\"), got {r:?}",
    );
}

// =============================================================================
// Prover algorithm audit: inequality range check (#3695)
//
// check_extf_int_reductions only scans equality assertions for range-restricted
// functions. Inequality constraints (e.g., str.to_int(x) < -2) bypass the range
// check entirely. These tests verify the solver does NOT return false SAT.
// =============================================================================

/// str.to_int(x) < -2 with x free: UNSAT.
/// str.to_int range is {-1} ∪ Z≥0, so no value is < -2.
/// Regression test for #3695: inequality constraints must not bypass range check.
#[test]
#[timeout(10_000)]
fn soundness_str_to_int_inequality_below_range() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (< (str.to_int x) (- 2)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        r == Some("unsat") || r == Some("unknown"),
        "str.to_int(x) < -2 is unsatisfiable (range is {{-1}} ∪ Z≥0), got {r:?}",
    );
}

/// str.to_code(x) > 196607 with x free: UNSAT.
/// str.to_code range is {-1} ∪ [0, 196607], so no value exceeds 196607.
/// Regression test for #3695.
#[test]
#[timeout(10_000)]
fn soundness_str_to_code_inequality_above_range() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (> (str.to_code x) 196607))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        r == Some("unsat") || r == Some("unknown"),
        "str.to_code(x) > 196607 is unsatisfiable (range is {{-1}} ∪ [0, 196607]), got {r:?}",
    );
}

/// str.to_int(x) >= 0 with x free: SAT (e.g., x = "0").
/// Positive control: in-range inequality must still be satisfiable.
#[test]
#[timeout(10_000)]
fn soundness_str_to_int_inequality_in_range_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (>= (str.to_int x) 0))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        r == Some("sat") || r == Some("unknown"),
        "str.to_int(x) >= 0 is satisfiable (x=\"0\"), got {r:?}",
    );
}

/// str.to_int(x) < -1 with x free: UNSAT.
/// str.to_int range is {-1} ∪ Z≥0, so the minimum value is -1.
/// Boundary test for #3695: inequality at exact range boundary.
#[test]
#[timeout(10_000)]
fn soundness_str_to_int_inequality_lt_minus_one_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (< (str.to_int x) (- 1)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        r == Some("unsat") || r == Some("unknown"),
        "str.to_int(x) < -1 is unsatisfiable (min is -1), got {r:?}",
    );
}

/// str.to_int(x) <= -1 with x free: SAT (e.g., x = "abc").
/// str.to_int returns -1 for non-numeric strings, so <= -1 is achievable.
/// Boundary test for #3695: exact minimum is in range.
#[test]
#[timeout(10_000)]
fn soundness_str_to_int_inequality_le_minus_one_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (<= (str.to_int x) (- 1)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        r == Some("sat") || r == Some("unknown"),
        "str.to_int(x) <= -1 is satisfiable (x=\"abc\" gives -1), got {r:?}",
    );
}

/// str.to_code(x) < -1 with x free: UNSAT.
/// str.to_code range is {-1} ∪ [0, 196607], so min is -1.
/// Boundary test for #3695.
#[test]
#[timeout(10_000)]
fn soundness_str_to_code_inequality_lt_minus_one_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (< (str.to_code x) (- 1)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        r == Some("unsat") || r == Some("unknown"),
        "str.to_code(x) < -1 is unsatisfiable (min is -1), got {r:?}",
    );
}

/// Combined range contradiction: str.to_int(x) = -1 AND str.to_int(x) >= 0 is UNSAT.
/// Tests that integer solver + range check interact correctly.
/// Regression test for #3695 (combined constraint reasoning).
#[test]
#[timeout(10_000)]
fn soundness_str_to_int_combined_range_contradiction_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.to_int x) (- 1)))
(assert (>= (str.to_int x) 0))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        r == Some("unsat") || r == Some("unknown"),
        "str.to_int(x) = -1 AND str.to_int(x) >= 0 is contradictory, got {r:?}",
    );
}

/// str.to_code(x) <= -2 with x free: UNSAT.
/// str.to_code minimum is -1. No output value can be <= -2.
/// Regression test for #3695 (strict boundary below minimum).
#[test]
#[timeout(10_000)]
fn soundness_str_to_code_inequality_le_minus_two_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (<= (str.to_code x) (- 2)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        r == Some("unsat") || r == Some("unknown"),
        "str.to_code(x) <= -2 is unsatisfiable (min is -1), got {r:?}",
    );
}

/// Negated inequality: NOT(str.to_int(x) >= -1) = str.to_int(x) < -1 is UNSAT.
/// Tests that negation of inequalities is correctly handled by range check.
/// Regression test for #3695 (negated inequality polarity).
#[test]
#[timeout(10_000)]
fn soundness_str_to_int_negated_ge_minus_one_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (not (>= (str.to_int x) (- 1))))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        r == Some("unsat") || r == Some("unknown"),
        "NOT(str.to_int(x) >= -1) is UNSAT (equivalent to str.to_int(x) < -1), got {r:?}",
    );
}

/// str.indexof(x, "a", 0) < -1: UNSAT (min is -1).
/// Tests inequality range check for str.indexof.
/// Regression test for #3695.
#[test]
#[timeout(10_000)]
fn soundness_str_indexof_inequality_below_range_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (< (str.indexof x "a" 0) (- 1)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        r == Some("unsat") || r == Some("unknown"),
        "str.indexof(x, \"a\", 0) < -1 is UNSAT (min is -1), got {r:?}",
    );
}
