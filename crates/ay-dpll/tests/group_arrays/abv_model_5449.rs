// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for QF_ABV array model extraction (#5449).
//!
//! Before #5449, the BV eager bit-blasting path returned `None` for array
//! models, causing `get-model`/`get-value` to produce `((as const ...) 0)`
//! regardless of constraints. These tests verify that array model output
//! is consistent with assertions.

use ntest::timeout;

fn results(output: &str) -> Vec<&str> {
    output
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .collect()
}

/// Extract a BV hex value from get-value output like `((x #x10))`.
fn get_bv_binding(line: &str, name: &str) -> Option<String> {
    let needle = format!("({name} ");
    let start = line.find(&needle)? + needle.len();
    let rest = &line[start..];
    let end = rest.find(')')?;
    Some(rest[..end].trim().to_string())
}

/// Basic regression: `select a x` must match the asserted value.
///
/// Before #5449, AY returned `#x00` for both `x` and `(select a x)`,
/// violating the assertion `(= (select a x) #x10)`.
#[test]
#[timeout(10_000)]
fn qf_abv_get_value_select_matches_assertion_5449() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-fun x () (_ BitVec 8))
        (assert (= (select a x) #x10))
        (check-sat)
        (get-value (x (select a x)))
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(lines[0], "sat");
    // The select value must be #x10 regardless of what x is assigned.
    let sel_val = get_bv_binding(lines[1], "(select a x)");
    assert_eq!(
        sel_val,
        Some("#x10".to_string()),
        "select a x must be #x10 per assertion, got: {lines:?}"
    );
}

/// Multiple stores: array model must reflect all constrained indices.
#[test]
#[timeout(10_000)]
fn qf_abv_get_value_multiple_indices_5449() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
        (assert (= (select a #x01) #x42))
        (assert (= (select a #x02) #xff))
        (check-sat)
        (get-value ((select a #x01) (select a #x02)))
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(lines[0], "sat");
    assert_eq!(
        get_bv_binding(lines[1], "(select a #x01)"),
        Some("#x42".to_string()),
        "a[#x01] must be #x42"
    );
    assert_eq!(
        get_bv_binding(lines[1], "(select a #x02)"),
        Some("#xff".to_string()),
        "a[#x02] must be #xff"
    );
}

/// Store-then-select: array model through store chain must be consistent.
#[test]
#[timeout(10_000)]
fn qf_abv_store_then_select_model_5449() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-fun b () (Array (_ BitVec 8) (_ BitVec 8)))
        (assert (= b (store a #x01 #x42)))
        (assert (= (select b #x01) #x42))
        (assert (= (select b #x02) #xab))
        (check-sat)
        (get-value ((select b #x01) (select b #x02)))
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(lines[0], "sat");
    assert_eq!(
        get_bv_binding(lines[1], "(select b #x01)"),
        Some("#x42".to_string()),
        "b[#x01] must be #x42 (stored value)"
    );
    assert_eq!(
        get_bv_binding(lines[1], "(select b #x02)"),
        Some("#xab".to_string()),
        "b[#x02] must be #xab per assertion"
    );
}
