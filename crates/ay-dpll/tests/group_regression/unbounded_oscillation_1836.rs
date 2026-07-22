// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #1836: unbounded oscillation termination.
//!
//! These are integration tests to ensure the combined solver entrypoints do not hang on the
//! known loop-preservation pattern.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn assert_unknown_or_unsat(outputs: Vec<String>) {
    assert!(
        outputs == vec!["unknown"] || outputs == vec!["unsat"],
        "Expected unknown or unsat, got {outputs:?}"
    );
}

#[test]
#[timeout(30_000)]
fn test_auf_lia_unbounded_oscillation_terminates_1836() {
    let input = r#"
(set-logic QF_AUFLIA)
(declare-const i Int)
(declare-const n Int)
(declare-const A (Array Int Int))
(assert (= (select A 0) 0))
(assert (>= i 0))
(assert (<= i n))
(assert (< i n))
(assert (not (and (>= (+ i 1) 0) (<= (+ i 1) n))))
(check-sat)
"#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_unknown_or_unsat(outputs);
}

#[test]
#[timeout(30_000)]
fn test_lira_unbounded_oscillation_terminates_1836() {
    let input = r#"
(set-logic QF_LIRA)
(declare-const i Int)
(declare-const n Int)
(declare-const r Real)
(assert (= r 0.0))
(assert (>= i 0))
(assert (<= i n))
(assert (< i n))
(assert (not (and (>= (+ i 1) 0) (<= (+ i 1) n))))
(check-sat)
"#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_unknown_or_unsat(outputs);
}

#[test]
#[timeout(30_000)]
fn test_auf_lira_unbounded_oscillation_terminates_1836() {
    let input = r#"
(set-logic QF_AUFLIRA)
(declare-const i Int)
(declare-const n Int)
(declare-const r Real)
(declare-const A (Array Int Int))
(assert (= r 0.0))
(assert (= (select A 0) 0))
(assert (>= i 0))
(assert (<= i n))
(assert (< i n))
(assert (not (and (>= (+ i 1) 0) (<= (+ i 1) n))))
(check-sat)
"#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_unknown_or_unsat(outputs);
}
