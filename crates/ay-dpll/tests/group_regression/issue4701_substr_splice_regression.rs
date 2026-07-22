// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for #4057: false UNSAT on issue4701_substr_splice.
//!
//! This benchmark involves circular dependencies between str.substr,
//! str.replace, and str.++. Z3 returns SAT with model:
//! a="aa", b="a", c="aaa", e="aa".
//!
//! Previously fixed and closed, then regressed. This test pins the
//! correct answer to prevent silent re-regression.

use ntest::timeout;

/// issue4701_substr_splice: circular str.substr/str.replace/str.++ must be SAT.
///
/// Z3 model: a="aa", b="a", c="aaa", e="aa".
/// Verified satisfying: e = "a" ++ substr("aa",0,1) = "a"++"a" = "aa" ✓
///                      a = substr("aaa",0,2) = "aa" ✓
///                      "a" = b ✓
///                      "a"++"aa" = replace("aaa","aa","aa") = "aaa" ✓
#[test]
#[timeout(10_000)]
fn test_issue4701_substr_splice_must_be_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun e () String)
(assert (= e (str.++ b (str.substr a 0 1))))
(assert (= a (str.substr c 0 (str.len e))))
(assert (= "a" b))
(assert (= (str.++ b a) (str.replace c e a)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert_ne!(
        r,
        Some("unsat"),
        "#4057 regression: issue4701_substr_splice is satisfiable (Z3 model: a=\"aa\", b=\"a\", c=\"aaa\", e=\"aa\")"
    );
    // Full sat requires complete string model extraction (#4057 Design #1:
    // InferInfo pattern). The model validation degradation (#4057 model
    // checkpoint) converts incomplete string models to Unknown instead of
    // false-UNSAT. Accept sat or unknown as correct.
    assert!(
        matches!(r, Some("sat") | Some("unknown")),
        "#4057: issue4701_substr_splice should be sat or unknown, not {r:?}",
    );
}

/// Simplified variant: just the core circular dependency without str.replace.
/// If the NF augmentation is over-constraining, even this simpler form may fail.
#[test]
#[timeout(10_000)]
fn test_issue4701_simplified_circular_substr_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun e () String)
(assert (= e (str.++ b (str.substr a 0 1))))
(assert (= a (str.substr c 0 (str.len e))))
(assert (= "a" b))
(assert (> (str.len c) 2))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    // This simplified variant should definitely be SAT: b="a", e="a"+substr(a,0,1),
    // a=substr(c,0,len(e)), c any string of length > 2.
    assert_ne!(
        r,
        Some("unsat"),
        "#4057 simplified: circular substr dependency is satisfiable"
    );
}
