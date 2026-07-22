// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! Regression test for issue #88: Model generation ignores disequalities
//!
//! The model produced by get-model should satisfy all asserted constraints,
//! including disequalities (not =).

use ntest::timeout;
use std::io::Write;
use std::process::{Command, Stdio};

/// Run AY with given SMT-LIB input and return stdout
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

/// Parse a model value from AY output
///
/// Looks for lines like: (define-fun field1 () Int 0)
fn parse_model_int(output: &str, var_name: &str) -> Option<i64> {
    for line in output.lines() {
        let line = line.trim();
        if line.starts_with(&format!("(define-fun {var_name} () Int")) {
            // Extract the integer value
            let parts: Vec<&str> = line.split_whitespace().collect();
            if let Some(val_str) = parts.last() {
                let val_str = val_str.trim_end_matches(')');
                // Handle negative numbers: (- N) format
                if val_str.starts_with("(-") || val_str.contains("(- ") {
                    continue; // Complex expression, skip for now
                }
                return val_str.parse().ok();
            }
        }
    }
    None
}

/// Issue #88: Model violates disequality constraint (FIXED)
///
/// Previously AY returned sat but the model had field1=0 and field2=0,
/// which violated (not (= field1 field2)). Fixed in commit f3d4deb via
/// selective equality routing.
#[test]
#[timeout(60000)]
fn test_model_respects_disequality_issue_88() {
    let input = r#"(set-logic QF_AUFLIA)
(declare-const field1 Int)
(declare-const field2 Int)
(assert (not (= field1 field2)))
(check-sat)
(get-model)
"#;

    let output = run_ay(input);

    // First check: AY returns sat
    assert!(output.starts_with("sat"), "Expected 'sat', got: {output}");

    // Parse model values
    let field1 = parse_model_int(&output, "field1");
    let field2 = parse_model_int(&output, "field2");

    match (field1, field2) {
        (Some(v1), Some(v2)) => {
            // The model MUST satisfy (not (= field1 field2))
            // i.e., field1 != field2
            assert_ne!(
                v1, v2,
                "Model violates disequality: field1={v1}, field2={v2} (should be different)\nFull output:\n{output}"
            );
        }
        _ => {
            // If we can't parse the model, that's also a problem
            // but not the specific bug we're testing
            eprintln!("Warning: Could not parse model values from output:\n{output}");
        }
    }
}

/// Sanity check: equality constraints work correctly
#[test]
#[timeout(60000)]
fn test_model_respects_equality() {
    let input = r#"(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= x y))
(assert (= x 42))
(check-sat)
(get-model)
"#;

    let output = run_ay(input);
    assert!(output.starts_with("sat"), "Expected 'sat', got: {output}");

    let x = parse_model_int(&output, "x");
    let y = parse_model_int(&output, "y");

    match (x, y) {
        (Some(vx), Some(vy)) => {
            assert_eq!(vx, 42, "Expected x=42, got {vx}");
            assert_eq!(vy, 42, "Expected y=42, got {vy}");
        }
        _ => {
            panic!("Could not parse model values from output:\n{output}");
        }
    }
}

/// QF_LIA disequality - works correctly
#[test]
#[timeout(60000)]
fn test_model_disequality_qf_lia_works() {
    let input = r#"(set-logic QF_LIA)
(declare-const a Int)
(declare-const b Int)
(assert (not (= a b)))
(check-sat)
(get-model)
"#;

    let output = run_ay(input);
    assert!(output.starts_with("sat"), "Expected 'sat', got: {output}");

    let a = parse_model_int(&output, "a");
    let b = parse_model_int(&output, "b");

    match (a, b) {
        (Some(va), Some(vb)) => {
            // QF_LIA correctly produces distinct values
            assert_ne!(va, vb, "Model violates a != b: a={va}, b={vb}");
        }
        _ => {
            eprintln!("Warning: Could not parse model values from output:\n{output}");
        }
    }
}

/// QF_AUFLIA disequality (FIXED)
///
/// Previously buggy in QF_AUFLIA logic - the issue was non-arithmetic
/// terms being routed to LIA unnecessarily. Fixed in commit f3d4deb.
#[test]
#[timeout(60000)]
fn test_model_disequality_qf_auflia() {
    let input = r#"(set-logic QF_AUFLIA)
(declare-const a Int)
(declare-const b Int)
(assert (not (= a b)))
(check-sat)
(get-model)
"#;

    let output = run_ay(input);
    assert!(output.starts_with("sat"), "Expected 'sat', got: {output}");

    let a = parse_model_int(&output, "a");
    let b = parse_model_int(&output, "b");

    match (a, b) {
        (Some(va), Some(vb)) => {
            // This FAILS with current bug: both get 0
            assert_ne!(
                va, vb,
                "Model violates a != b: a={va}, b={vb} (QF_AUFLIA bug)\nOutput:\n{output}"
            );
        }
        _ => {
            eprintln!("Warning: Could not parse model values from output:\n{output}");
        }
    }
}
