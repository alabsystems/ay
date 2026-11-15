// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Public explanations must describe observed evidence, including temporary
//! assumptions and independently checked native refutations.

use crate::spawn::OutputTimeout;
use std::process::{Command, Output};
use std::time::Duration;

fn explain(script: &str) -> Output {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("input.smt2");
    std::fs::write(&input, script).unwrap();
    Command::new(env!("CARGO_BIN_EXE_ay"))
        .args([
            "solve",
            "--explain",
            "--explain-format",
            "json",
            "--no-verify-proof",
            "--timeout",
            "5000",
            "--memory",
            "256",
        ])
        .arg(input)
        .output_timeout(Duration::from_secs(10))
        .expect("bounded explanation run")
}

fn reason(output: &Output) -> serde_json::Value {
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8_lossy(&output.stdout);
    assert!(text.lines().any(|line| line.trim() == "unsat"), "{text}");
    text.lines()
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
        .find(|value| value.get("reason").is_some())
        .unwrap_or_else(|| panic!("missing reason evidence: {text}"))
}

#[test]
fn checked_fp_reason_matches_the_actual_refutation() {
    let output = explain(include_str!(
        "../../../ay-model-check/tests/fixtures/wide-fp-remainder-odd-unsat.smt2"
    ));
    let evidence = reason(&output);
    assert_eq!(evidence["reason"], "CheckedRefutation");
    assert_eq!(evidence["theory"], "FP");
}

#[test]
fn temporary_assumptions_are_not_an_empty_query_bug() {
    let output = explain("(set-logic QF_UF)(declare-const a Bool)(check-sat-assuming (a (not a)))");
    assert_eq!(reason(&output)["reason"], "Unknown");
}

#[test]
fn original_false_constraint_is_identified() {
    let output = explain("(set-logic QF_UF)(assert false)(check-sat)");
    assert_eq!(reason(&output)["reason"], "PreprocessingDetected");
}
