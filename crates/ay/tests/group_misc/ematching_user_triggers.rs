// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// E-matching tests for user-provided triggers via SMT-LIB :pattern.
//
// These tests verify that AY:
// 1. Parses :pattern annotations on quantifier bodies.
// 2. Uses those user triggers for instantiation (instead of relying on auto-extracted patterns).

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

/// User trigger not present in the body: forall x. x = c with :pattern ((f x)).
///
/// The quantifier body contains only builtin symbols (e.g., "="), so auto-pattern
/// extraction produces no triggers. With the user-provided trigger, E-matching
/// should instantiate at x := d (via the ground term (f d)) and derive a conflict.
#[test]
#[timeout(60000)]
fn test_user_pattern_annotation_drives_instantiation() {
    let input = r#"(set-logic AUFLIA)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-const c U)
(declare-const d U)
(assert (= (f d) d))
(assert (distinct c d))
(assert (forall ((x U)) (! (= x c) :pattern ((f x)) )))
(check-sat)
"#;

    let output = run_ay(input);
    assert!(
        output.contains("unsat"),
        "Expected 'unsat' for user-triggered instantiation, got: {output}"
    );
}
