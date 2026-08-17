// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Negated-equality soundness regressions for extended string functions.

use super::*;

// ===================================================================
// Negated-equality soundness: extf evaluation vs disequalities
// ===================================================================
// For formulas of the form (not (= f(...) c)) where f(...) is a ground
// string function that evaluates to c, check_extf_string_equalities
// and check_extf_int_reductions scan all assertions (not just EQC members)
// and detect polarity contradictions.

/// str.at("hello", 0) = "h" is a tautology. Negating it should be UNSAT.
/// check_extf_string_equalities detects the polarity contradiction.
#[test]
#[timeout(10_000)]
fn soundness_negated_str_at_ground_equality() {
    let smt = r#"
(set-logic QF_S)
(assert (not (= (str.at "hello" 0) "h")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "NOT(str.at(\"hello\",0) = \"h\") is UNSAT"
    );
}

/// str.substr("hello", 1, 3) = "ell" is a tautology. Negating it should be UNSAT.
#[test]
#[timeout(10_000)]
fn soundness_negated_str_substr_ground_equality() {
    let smt = r#"
(set-logic QF_S)
(assert (not (= (str.substr "hello" 1 3) "ell")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "NOT(str.substr(\"hello\",1,3) = \"ell\") is UNSAT"
    );
}

/// str.replace("hello", "l", "r") = "herlo". Negation should be UNSAT.
#[test]
#[timeout(10_000)]
fn soundness_negated_str_replace_ground_equality() {
    let smt = r#"
(set-logic QF_S)
(assert (not (= (str.replace "hello" "l" "r") "herlo")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "NOT(str.replace(\"hello\",\"l\",\"r\") = \"herlo\") is UNSAT"
    );
}

/// str.replace_all("hello", "x", "y") = "hello" (no match). Negation should be UNSAT.
#[test]
#[timeout(10_000)]
fn soundness_negated_str_replace_all_no_match() {
    let smt = r#"
(set-logic QF_S)
(assert (not (= (str.replace_all "hello" "x" "y") "hello")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "NOT(str.replace_all(\"hello\",\"x\",\"y\") = \"hello\") is UNSAT"
    );
}

/// str.indexof("hello", "ll", 0) = 2. Negation should be UNSAT.
#[test]
#[timeout(10_000)]
fn soundness_negated_str_indexof_ground_equality() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (not (= (str.indexof "hello" "ll" 0) 2)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "NOT(str.indexof(\"hello\",\"ll\",0) = 2): got {ay:?}"
    );
}

/// str.to_int("42") = 42. Negation should be UNSAT.
#[test]
#[timeout(10_000)]
fn soundness_negated_str_to_int_ground_equality() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (not (= (str.to_int "42") 42)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "NOT(str.to_int(\"42\") = 42): got {ay:?}"
    );
}

/// str.from_int(42) = "42". Negation should be UNSAT.
#[test]
#[timeout(10_000)]
fn soundness_negated_str_from_int_ground_equality() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (not (= (str.from_int 42) "42")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "NOT(str.from_int(42) = \"42\") is UNSAT"
    );
}
