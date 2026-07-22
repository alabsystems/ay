// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Tests for UF function model output showing concrete values instead of
//! internal EUF representative names (#5452).
//!
//! When a UF function returns an interpreted sort (Int, Real, BV), the
//! `get-model` output must show the concrete value (e.g., `42`) instead of
//! internal EUF placeholders like `@?3`.

use ntest::timeout;

/// QF_UFLIA: Int-returning UF function model should show concrete value.
///
/// For `(= (f x) 42)`, the model for `f` must show `42`, not `@?N`.
#[test]
#[timeout(10_000)]
fn test_uflia_function_model_shows_concrete_int() {
    let smt = r#"
(set-logic QF_UFLIA)
(set-option :produce-models true)
(declare-fun f (Int) Int)
(declare-fun x () Int)
(assert (= (f x) 42))
(assert (>= x 0))
(check-sat)
(get-model)
"#;
    let output = crate::common::solve(smt);
    assert!(output.starts_with("sat"), "Expected sat, got: {output}");
    // The model must contain a concrete value for f, not @?N placeholders
    assert!(
        !output.contains("@?"),
        "Model contains unresolved @?N placeholder: {output}"
    );
    // The model should contain the value 42 somewhere in f's definition
    assert!(
        output.contains("42"),
        "Model does not contain expected value 42: {output}"
    );
}

/// QF_UFLRA: Real-returning UF function model should show concrete value.
#[test]
#[timeout(10_000)]
fn test_uflra_function_model_shows_concrete_real() {
    let smt = r#"
(set-logic QF_UFLRA)
(set-option :produce-models true)
(declare-fun g (Real) Real)
(declare-fun y () Real)
(assert (= (g y) 3.0))
(assert (>= y 0.0))
(check-sat)
(get-model)
"#;
    let output = crate::common::solve(smt);
    assert!(output.starts_with("sat"), "Expected sat, got: {output}");
    assert!(
        !output.contains("@?"),
        "Model contains unresolved @?N placeholder: {output}"
    );
}

/// QF_AUFLIA: UF + Array combined model should show concrete values.
#[test]
#[timeout(10_000)]
fn test_auflia_function_model_shows_concrete_values() {
    let smt = r#"
(set-logic QF_AUFLIA)
(set-option :produce-models true)
(declare-fun f (Int) Int)
(declare-fun a () (Array Int Int))
(declare-fun x () Int)
(assert (= (select a x) 42))
(assert (= (f (select a x)) 100))
(assert (>= x 0))
(check-sat)
(get-model)
"#;
    let output = crate::common::solve(smt);
    assert!(output.starts_with("sat"), "Expected sat, got: {output}");
    assert!(
        !output.contains("@?"),
        "Model contains unresolved @?N placeholder: {output}"
    );
}

/// Multiple UF applications with different argument values.
#[test]
#[timeout(10_000)]
fn test_uflia_multiple_applications() {
    let smt = r#"
(set-logic QF_UFLIA)
(set-option :produce-models true)
(declare-fun f (Int) Int)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= x 1))
(assert (= y 2))
(assert (= (f x) 10))
(assert (= (f y) 20))
(check-sat)
(get-model)
"#;
    let output = crate::common::solve(smt);
    assert!(output.starts_with("sat"), "Expected sat, got: {output}");
    assert!(
        !output.contains("@?"),
        "Model contains unresolved @?N placeholder: {output}"
    );
    // Should contain both values
    assert!(output.contains("10"), "Model missing value 10: {output}");
    assert!(output.contains("20"), "Model missing value 20: {output}");
}

/// QF_UFBV: BV-returning UF function model should show concrete BV literal.
#[test]
#[timeout(10_000)]
fn test_ufbv_function_model_shows_concrete_bv() {
    let smt = r#"
(set-logic QF_UFBV)
(set-option :produce-models true)
(declare-fun h ((_ BitVec 8)) (_ BitVec 8))
(declare-fun z () (_ BitVec 8))
(assert (= z #xFF))
(assert (= (h z) #x42))
(check-sat)
(get-model)
"#;
    let output = crate::common::solve(smt);
    assert!(output.starts_with("sat"), "Expected sat, got: {output}");
    assert!(
        !output.contains("@?"),
        "Model contains unresolved @?N placeholder: {output}"
    );
}
