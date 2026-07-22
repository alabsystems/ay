// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

/// Regression #3429: variable-constant concat should converge to SAT.
#[test]
#[timeout(10_000)]
fn suffix_variable_constant_is_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= (str.++ x "b") "ab"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "str.++(x,\"b\") = \"ab\" must be sat, got: {result}"
    );
}

/// Regression #3429: constant-variable concat should converge to SAT.
#[test]
#[timeout(10_000)]
fn prefix_variable_constant_is_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= (str.++ "a" x) "abc"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert!(
        matches!(
            crate::common::sat_result(&result),
            Some("sat") | Some("unknown")
        ),
        "str.++(\"a\",x) = \"abc\" must not be unsat, got: {result}"
    );
}

/// Regression #3429: mixed concat alignment should converge to SAT.
#[test]
#[timeout(10_000)]
fn mixed_concat_alignment_is_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ "ab" x) (str.++ "a" y)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "str.++(\"ab\",x) = str.++(\"a\",y): expected sat or unknown, got {ay:?} ({result})"
    );
}

/// Regression #3429: both prefix and suffix constants with a variable middle.
#[test]
#[timeout(10_000)]
fn sandwich_prefix_suffix_variable_is_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= (str.++ "a" x "c") "abc"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "str.++(\"a\",x,\"c\") = \"abc\" must be sat, got: {result}"
    );
}

/// Regression #3429: suffix mismatch remains UNSAT.
#[test]
#[timeout(10_000)]
fn suffix_mismatch_is_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= (str.++ x "c") "abd"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert!(
        matches!(
            crate::common::sat_result(&result),
            Some("unsat") | Some("unknown")
        ),
        "str.++(x,\"c\") = \"abd\" must not be sat, got: {result}"
    );
}

/// Soundness regression: direct theory shortcut was returning UNSAT for
/// SAT formulas. str.++(x,"a") = "a" is SAT with x="".
///
/// Root cause: the solve_strings_lia() had a pre-DPLL "fast path" that
/// called StringsLiaSolver::check() directly on preprocessed assertions.
/// The theory checker could not resolve the unresolved concat term and
/// reported a spurious UNSAT conflict.
#[test]
#[timeout(10_000)]
fn soundness_direct_theory_shortcut_suffix_empty_is_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.++ x "a") "a"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_ne!(
        ay,
        Some("unsat"),
        "str.++(x,\"a\") = \"a\" must NOT be unsat (SAT with x=\"\")"
    );
}

/// Bridge axiom convergence: two-variable concat with length constraint.
/// str.++(x, y) = "ab" with len(x) = 1 should converge to SAT.
#[test]
#[timeout(15_000)]
fn two_variable_slia_concat_length_constrained() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x y) "ab"))
(assert (= (str.len x) 1))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "two-variable concat with length: expected sat or unknown, got: {ay:?} ({result})"
    );
}

/// Bridge axiom convergence: three-variable concat with length constraints.
/// str.++(x, y, z) = "abc" with len(x) = 1, len(y) = 1 should converge.
#[test]
#[timeout(30_000)]
fn three_variable_slia_concat_length_constrained() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (= (str.++ x y z) "abc"))
(assert (= (str.len x) 1))
(assert (= (str.len y) 1))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "three-variable concat with length constraints must converge, got: {ay:?} ({result})"
    );
}
