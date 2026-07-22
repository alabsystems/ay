// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! Integration tests for model output of FP, String, and Seq sorts.
//!
//! Before this fix, `get-model` emitted default values (zeros, empty strings)
//! for FloatingPoint, String, and Seq variables instead of their actual model
//! values. This caused incorrect counterexamples for consumers.

use ntest::timeout;
use std::io::Write;
use std::process::{Command, Stdio};

/// Run AY with given SMT-LIB input and return stdout.
fn run_ay(input: &str) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");

    let mut child = Command::new(ay_path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to spawn ay");

    {
        let stdin = child.stdin.as_mut().unwrap();
        stdin.write_all(input.as_bytes()).unwrap();
    }

    let output = child.wait_with_output().expect("Failed to wait on ay");
    String::from_utf8_lossy(&output.stdout).to_string()
}

/// FP model output should contain actual FP values, not default zeros.
///
/// Before fix: `(define-fun x () (_ FloatingPoint 8 24) (_ +zero 8 24))`
/// After fix:  `(define-fun x () (_ FloatingPoint 8 24) (fp #b0 #b00111111 ...))`
#[test]
#[timeout(30_000)]
fn fp_model_contains_actual_values_not_defaults() {
    let input = r#"
(set-option :produce-models true)
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp #b0 #x3f #b00000000000000000000000)))
(check-sat)
(get-model)
(exit)
"#;
    let output = run_ay(input);
    assert!(output.contains("sat"), "Expected sat, got: {output}");
    assert!(
        output.contains("(define-fun x ()"),
        "Model should contain definition for x, got: {output}"
    );
    // The value should NOT be the default +zero
    assert!(
        !output.contains("+zero"),
        "FP model value should be actual value, not default +zero. Got: {output}"
    );
    // Should contain an actual (fp ...) value
    assert!(
        output.contains("(fp #b"),
        "FP model should contain (fp #b...) literal. Got: {output}"
    );
}

/// FP model with distinct non-zero values should reflect both correctly.
#[test]
#[timeout(30_000)]
fn fp_model_distinct_values() {
    let input = r#"
(set-option :produce-models true)
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 8 24))
(assert (fp.eq a (fp #b0 #x3f #b00000000000000000000000)))
(assert (fp.eq b (fp #b0 #x40 #b00000000000000000000000)))
(assert (not (fp.eq a b)))
(check-sat)
(get-model)
(exit)
"#;
    let output = run_ay(input);
    assert!(output.contains("sat"), "Expected sat, got: {output}");
    // Both a and b should be present in model
    assert!(
        output.contains("(define-fun a ()"),
        "Model should contain a, got: {output}"
    );
    assert!(
        output.contains("(define-fun b ()"),
        "Model should contain b, got: {output}"
    );
}

/// `get-value` on ground FP special literals should preserve their actual values.
#[test]
#[timeout(30_000)]
fn fp_get_value_ground_special_literals() {
    let input = r#"
(set-option :produce-models true)
(set-logic QF_FP)
(check-sat)
(get-value ((_ -zero 5 11) (_ +oo 5 11) (_ NaN 5 11)))
(exit)
"#;
    let output = run_ay(input);
    assert!(output.contains("sat"), "Expected sat, got: {output}");
    assert!(
        output.contains("((_ -zero 5 11) (_ -zero 5 11))"),
        "Expected negative zero to round-trip through get-value. Got: {output}"
    );
    assert!(
        output.contains("((_ +oo 5 11) (_ +oo 5 11))"),
        "Expected positive infinity to round-trip through get-value. Got: {output}"
    );
    assert!(
        output.contains("((_ NaN 5 11) (_ NaN 5 11))"),
        "Expected NaN to round-trip through get-value. Got: {output}"
    );
}

/// Nested ground FP terms built from special literals should evaluate concretely.
#[test]
#[timeout(30_000)]
fn fp_get_value_nested_ground_special_terms() {
    let input = r#"
(set-option :produce-models true)
(set-logic QF_FP)
(check-sat)
(get-value ((fp.isNaN (_ NaN 5 11)) (fp.to_ieee_bv (_ -zero 5 11))))
(exit)
"#;
    let output = run_ay(input);
    assert!(output.contains("sat"), "Expected sat, got: {output}");
    assert!(
        output.contains("((fp.isNaN (_ NaN 5 11)) true)"),
        "Expected fp.isNaN on NaN to evaluate to true. Got: {output}"
    );
    assert!(
        output.contains("((fp.to_ieee_bv (_ -zero 5 11)) #x8000)"),
        "Expected fp.to_ieee_bv(-zero) to preserve the sign bit. Got: {output}"
    );
}

/// Non-RNE FP arithmetic in get-value should use the actual concrete result,
/// not fall back to the sort default when the evaluator cannot approximate it.
#[test]
#[timeout(30_000)]
fn fp_get_value_non_rne_arithmetic_uses_actual_model_value() {
    let input = r#"
(set-option :produce-models true)
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 5 11))
(assert (= x (fp #b0 #b01111 #b0000000000)))
(check-sat)
(get-value ((fp.add RTZ x x)))
(exit)
"#;
    let output = run_ay(input);
    assert!(output.contains("sat"), "Expected sat, got: {output}");
    assert!(
        output.contains("((fp.add RTZ x x) (fp #b0 #b10000 #b0000000000))"),
        "Expected fp.add RTZ to evaluate to the exact Float16 value 2.0. Got: {output}"
    );
}

/// Wide `to_fp` conversions should not collapse to the default value when the
/// target precision exceeds native Float64.
#[test]
#[timeout(30_000)]
fn fp_get_value_wide_to_fp_integer_preserves_precision() {
    let input = r#"
(set-option :produce-models true)
(set-logic QF_FP)
(check-sat)
(get-value (((_ to_fp 11 54) RNE 9007199254740993)))
(exit)
"#;
    let output = run_ay(input);
    let expected = format!(
        "(((_ to_fp 11 54) RNE 9007199254740993) (fp #b0 #b10000110100 #b{:053b}))",
        1u64
    );
    assert!(output.contains("sat"), "Expected sat, got: {output}");
    assert!(
        output.contains(&expected),
        "Expected 2^53 + 1 to remain exact at 54-bit precision. Got: {output}"
    );
}

/// Seq model with explicit concat value should show actual elements, not seq.empty.
///
/// Before fix: `(define-fun s () (Seq Int) (as seq.empty (Seq Int)))`
/// After fix:  `(define-fun s () (Seq Int) (seq.++ (seq.unit 1) (seq.unit 2)))`
#[test]
#[timeout(30_000)]
fn seq_model_contains_actual_values_not_empty() {
    let input = r#"
(set-logic QF_SEQ)
(declare-const s (Seq Int))
(assert (= s (seq.++ (seq.unit 1) (seq.unit 2))))
(check-sat)
(get-model)
(exit)
"#;
    let output = run_ay(input);
    assert!(output.contains("sat"), "Expected sat, got: {output}");
    assert!(
        output.contains("(define-fun s ()"),
        "Model should contain definition for s, got: {output}"
    );
    // The value should NOT be the default seq.empty
    assert!(
        !output.contains("seq.empty"),
        "Seq model value should be actual value, not default seq.empty. Got: {output}"
    );
    // Should contain seq.unit elements
    assert!(
        output.contains("seq.unit 1"),
        "Seq model should contain (seq.unit 1). Got: {output}"
    );
    assert!(
        output.contains("seq.unit 2"),
        "Seq model should contain (seq.unit 2). Got: {output}"
    );
}

/// Seq model for a single-element sequence should use seq.unit directly.
#[test]
#[timeout(30_000)]
fn seq_model_single_unit() {
    let input = r#"
(set-logic QF_SEQ)
(declare-const s (Seq Int))
(assert (= s (seq.unit 42)))
(check-sat)
(get-model)
(exit)
"#;
    let output = run_ay(input);
    assert!(output.contains("sat"), "Expected sat, got: {output}");
    assert!(
        output.contains("seq.unit 42"),
        "Seq model should contain (seq.unit 42). Got: {output}"
    );
}

/// Regression: a single-`seq.unit` witness must be non-empty and `(get-model)`
/// must agree with `(get-value)` — both must print `(seq.unit 42)` and neither
/// may print the `seq.empty` default. Before the model-witness fix `(get-model)`
/// printed `(as seq.empty (Seq Int))` (an INVALID witness that re-feeds to
/// `unsat`) while `(get-value)` printed the correct value (#model-seq-witness).
#[test]
#[timeout(30_000)]
fn seq_model_single_unit_nonempty_get_value_agrees() {
    let input = r#"
(set-logic QF_SEQ)
(declare-const s (Seq Int))
(assert (= s (seq.unit 42)))
(check-sat)
(get-model)
(get-value (s))
(exit)
"#;
    let output = run_ay(input);
    assert!(output.contains("sat"), "Expected sat, got: {output}");
    // The witness must be the actual value, never the empty default.
    assert!(
        !output.contains("seq.empty"),
        "Non-empty seq witness must not contain seq.empty. Got: {output}"
    );
    // Both `(get-model)` and `(get-value)` must show `(seq.unit 42)`.
    assert_eq!(
        output.matches("(seq.unit 42)").count(),
        2,
        "Both get-model and get-value should print (seq.unit 42). Got: {output}"
    );
}

/// Seq model for an empty sequence should correctly show seq.empty.
#[test]
#[timeout(30_000)]
fn seq_model_empty_sequence() {
    let input = r#"
(set-logic QF_SEQ)
(declare-const s (Seq Int))
(assert (= s (as seq.empty (Seq Int))))
(check-sat)
(get-model)
(exit)
"#;
    let output = run_ay(input);
    assert!(output.contains("sat"), "Expected sat, got: {output}");
    assert!(
        output.contains("seq.empty"),
        "Empty Seq model should contain seq.empty. Got: {output}"
    );
}

/// Seq model for a 3+ element sequence must use binary seq.++ (SMT-LIB 2.6).
///
/// Before fix: `(seq.++ (seq.unit 1) (seq.unit 2) (seq.unit 3))` (n-ary, not parseable)
/// After fix:  `(seq.++ (seq.++ (seq.unit 1) (seq.unit 2)) (seq.unit 3))` (binary, round-trippable)
#[test]
#[timeout(30_000)]
fn seq_model_multi_element_uses_binary_concat() {
    // Use explicit concat assignment so the model reflects 3 concrete elements.
    let input = r#"
(set-logic QF_SEQ)
(declare-const s (Seq Int))
(assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
(check-sat)
(get-model)
(exit)
"#;
    let output = run_ay(input);
    assert!(output.contains("sat"), "Expected sat, got: {output}");
    assert!(
        output.contains("(define-fun s ()"),
        "Model should contain definition for s, got: {output}"
    );
    // The model must use binary seq.++ — i.e., each seq.++ has exactly 2 arguments.
    // With 3 elements, the output should be nested: (seq.++ (seq.++ a b) c)
    // NOT n-ary: (seq.++ a b c)
    //
    // Count occurrences of "seq.++" — for 3 elements we need 2 binary applications.
    let concat_count = output.matches("seq.++").count();
    assert!(
        concat_count >= 2,
        "3-element seq model should have at least 2 seq.++ applications (binary nesting), \
         found {concat_count}. Got: {output}"
    );
    // All 3 elements should be present as seq.unit terms
    assert!(
        output.contains("seq.unit 1")
            && output.contains("seq.unit 2")
            && output.contains("seq.unit 3"),
        "All 3 elements should be present in model. Got: {output}"
    );
}
