// Copyright (c) 2024-2026 Andrew Yates
//
// Licensed under the Apache License, Version 2.0.
// SPDX-License-Identifier: Apache-2.0
//
// E-matching tests for nested patterns (Issue #230)
//
// These tests verify that E-matching correctly handles nested patterns
// like P(f(x)) where the bound variable x appears inside a function application.

use ntest::timeout;
use std::io::Write;
use std::process::{Command, Stdio};

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

/// Test flat pattern: forall x. (f x) >= 0
/// E-matching instantiates the quantifier and Nelson-Oppen propagates the equality
/// (f 5) = -1 from LIA to EUF to detect the conflict with (f 5) >= 0.
#[test]
#[timeout(60000)]
fn test_flat_pattern_unsat() {
    let input = r#"(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (>= (f x) 0)))
(assert (= (f 5) (- 1)))
(check-sat)
"#;

    let output = run_ay(input);
    assert!(
        output.contains("unsat"),
        "Expected 'unsat' for flat pattern E-matching, got: {output}"
    );
}

/// #230: Nested pattern P(f(x)) - the main bug case
/// Pattern: forall x. P(f(x)) => Q(x)
/// Ground: P(f(a)), not(Q(a))
/// E-matching should find {x -> a} and derive contradiction.
#[test]
#[timeout(60000)]
fn test_nested_pattern_p_f_x() {
    let input = r#"(set-logic QF_AUFLIA)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun P (U) Bool)
(declare-fun Q (U) Bool)
(declare-const a U)
(assert (forall ((x U)) (=> (P (f x)) (Q x))))
(assert (P (f a)))
(assert (not (Q a)))
(check-sat)
"#;

    let output = run_ay(input);
    assert!(
        output.contains("unsat"),
        "Expected 'unsat' for nested pattern P(f(x)), got: {output}"
    );
}

/// Nested pattern with composition: forall x. P(f(g(x)))
/// Tests double nesting.
#[test]
#[timeout(60000)]
fn test_double_nested_pattern() {
    let input = r#"(set-logic QF_AUFLIA)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun g (U) U)
(declare-fun P (U) Bool)
(declare-const a U)
(assert (forall ((x U)) (P (f (g x)))))
(assert (not (P (f (g a)))))
(check-sat)
"#;

    let output = run_ay(input);
    assert!(
        output.contains("unsat"),
        "Expected 'unsat' for double nested pattern P(f(g(x))), got: {output}"
    );
}

/// Multiple variables in nested pattern: forall x y. P(f(x, y))
#[test]
#[timeout(60000)]
fn test_nested_pattern_multiple_vars() {
    let input = r#"(set-logic QF_AUFLIA)
(declare-sort U 0)
(declare-fun f (U U) U)
(declare-fun P (U) Bool)
(declare-const a U)
(declare-const b U)
(assert (forall ((x U) (y U)) (P (f x y))))
(assert (not (P (f a b))))
(check-sat)
"#;

    let output = run_ay(input);
    assert!(
        output.contains("unsat"),
        "Expected 'unsat' for nested pattern with multiple vars, got: {output}"
    );
}

/// Mixed ground and variable in nested pattern: forall x. P(f(x, c))
/// where c is a declared constant.
#[test]
#[timeout(60000)]
fn test_nested_pattern_mixed_ground_var() {
    let input = r#"(set-logic QF_AUFLIA)
(declare-sort U 0)
(declare-fun f (U U) U)
(declare-fun P (U) Bool)
(declare-const a U)
(declare-const c U)
(assert (forall ((x U)) (P (f x c))))
(assert (not (P (f a c))))
(check-sat)
"#;

    let output = run_ay(input);
    assert!(
        output.contains("unsat"),
        "Expected 'unsat' for mixed ground/var nested pattern, got: {output}"
    );
}

/// Same variable appearing twice in nested pattern: forall x. P(f(x, x))
#[test]
#[timeout(60000)]
fn test_nested_pattern_repeated_var() {
    let input = r#"(set-logic QF_AUFLIA)
(declare-sort U 0)
(declare-fun f (U U) U)
(declare-fun P (U) Bool)
(declare-const a U)
(assert (forall ((x U)) (P (f x x))))
(assert (not (P (f a a))))
(check-sat)
"#;

    let output = run_ay(input);
    assert!(
        output.contains("unsat"),
        "Expected 'unsat' for repeated var in nested pattern, got: {output}"
    );
}

/// Repeated var mismatch - should NOT match f(a, b) with pattern f(x, x)
#[test]
#[timeout(60000)]
fn test_nested_pattern_repeated_var_no_match() {
    let input = r#"(set-logic QF_AUFLIA)
(declare-sort U 0)
(declare-fun f (U U) U)
(declare-fun P (U) Bool)
(declare-const a U)
(declare-const b U)
(assert (forall ((x U)) (P (f x x))))
(assert (not (P (f a b))))
(assert (distinct a b))
(check-sat)
"#;

    let output = run_ay(input);
    // Should return sat or unknown - the pattern f(x,x) should NOT match f(a,b)
    // when a != b, so the instantiation shouldn't apply.
    assert!(
        !output.contains("unsat"),
        "Pattern f(x,x) should not match f(a,b) when a!=b, got: {output}"
    );
}
