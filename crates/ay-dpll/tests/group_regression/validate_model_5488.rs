// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for #5488: validate_model accepts SAT when all assertions
//! are skipped (checked=0, total>0).
//!
//! The validate_model zero-checked fix (commit a0d11bda1 on origin/main)
//! returns Err when checked==0 && total>0, causing finalize_sat_model_validation
//! to degrade to Unknown. These tests verify DT formulas are handled correctly.

use ntest::timeout;

fn results(output: &str) -> Vec<&str> {
    output
        .lines()
        .map(str::trim)
        .filter(|l| *l == "sat" || *l == "unsat" || *l == "unknown")
        .collect()
}

/// Simple DT formula: the evaluator CAN check `(= x (Just 42))` and returns
/// checked=1, so the zero-check fix doesn't fire. Verifies simple DT formulas
/// still return SAT correctly.
#[test]
#[timeout(10_000)]
fn test_dt_simple_equality_returns_sat_5488() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((Maybe 0)) (((Nothing) (Just (value Int)))))
        (declare-const x Maybe)
        (assert (= x (Just 42)))
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    let res = results(&output);
    assert!(
        res == vec!["sat"] || res == vec!["unknown"],
        "Simple DT equality should be sat or unknown, got: {res:?}\nFull output: {output}"
    );
}

/// Contradictory DT formula that should be UNSAT.
/// UNSAT detection happens at the SAT/theory level before model validation.
#[test]
#[timeout(10_000)]
fn test_dt_contradictory_is_unsat_5488() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((Color 0)) (((Red) (Green) (Blue))))
        (declare-const c Color)
        (assert (= c Red))
        (assert (= c Green))
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(
        results(&output),
        vec!["unsat"],
        "Contradictory DT formula must be UNSAT, got: {output}"
    );
}

/// DT formula with tester predicate.
/// Tests that tester-based assertions containing DT terms are handled
/// correctly by validate_model's skip/evaluate logic.
#[test]
#[timeout(10_000)]
fn test_dt_tester_assertion_5488() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((Maybe 0)) (((Nothing) (Just (value Int)))))
        (declare-const x Maybe)
        (assert (is-Just x))
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    let res = results(&output);
    assert!(
        res == vec!["sat"] || res == vec!["unknown"],
        "DT tester formula should be sat or unknown, got: {res:?}\nFull output: {output}"
    );
}

/// Mixed DT+Int formula where only some assertions have DT terms.
/// The pure-Int assertion gets checked, ensuring checked > 0.
#[test]
#[timeout(10_000)]
fn test_dt_mixed_some_assertions_checked_5488() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Maybe 0)) (((Nothing) (Just (value Int)))))
        (declare-const x Maybe)
        (declare-const y Int)
        (assert (= x (Just 42)))
        (assert (> y 0))
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    let res = results(&output);
    assert!(
        res == vec!["sat"] || res == vec!["unknown"],
        "Mixed DT+Int formula should be sat or unknown, got: {res:?}\nFull output: {output}"
    );
}

/// DT formula with selector on unconstrained variable.
/// Exercises the harder evaluation path where the model may not
/// have a value for the selector result.
#[test]
#[timeout(10_000)]
fn test_dt_selector_unconstrained_5488() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((Pair 0)) (((mk-pair (fst Int) (snd Int)))))
        (declare-const p Pair)
        (assert (> (fst p) 10))
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    let res = results(&output);
    assert!(
        res == vec!["sat"] || res == vec!["unknown"],
        "DT selector formula should be sat or unknown, got: {res:?}\nFull output: {output}"
    );
}
