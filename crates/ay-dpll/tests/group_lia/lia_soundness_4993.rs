// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DPLL(T) soundness regression coverage for #4993.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn extract_int_value(output: &str, var: &str) -> i64 {
    let pattern = format!("({var} ");
    let start = output
        .find(&pattern)
        .unwrap_or_else(|| panic!("variable {var} not found in get-value output: {output}"));
    let rest = &output[start + pattern.len()..];
    let (value, _) = crate::common::parse_smt_int(rest, output);
    value
}

#[test]
#[timeout(10_000)]
fn test_qf_lia_even_interval_model_is_sound_4993() {
    let input = r#"
        (set-logic QF_LIA)
        (set-option :produce-models true)
        (declare-const x Int)
        (assert (> x 0))
        (assert (< x 5))
        (assert (= (mod x 2) 0))
        (check-sat)
        (get-value (x))
    "#;

    let commands = parse(input).expect("parse");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all");

    assert_eq!(outputs[0], "sat", "expected SAT, got outputs: {outputs:?}");

    let stats = exec
        .validate_model()
        .expect("validate_model should accept the returned model");
    assert!(
        stats.checked > 0,
        "validate_model should independently check at least one assertion: {stats:?}"
    );

    let x_val = extract_int_value(&outputs[1], "x");
    assert!(x_val > 0, "model x={x_val} must satisfy x > 0");
    assert!(x_val < 5, "model x={x_val} must satisfy x < 5");
    assert_eq!(x_val.rem_euclid(2), 0, "model x={x_val} must be even");
    assert!(
        matches!(x_val, 2 | 4),
        "model x={x_val} must be one of the only satisfying values {{2, 4}}"
    );
}
