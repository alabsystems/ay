// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// Unit tests for the SMT solver driver (parse_get_value, parse_smt_int, etc.)

use super::*;
use std::io;

#[test]
fn test_parse_get_value_simple() {
    let lines = vec!["((x 5) (y 3))".to_string()];
    let values = parse_get_value(&lines).unwrap();
    assert_eq!(values.get("x").unwrap(), "5");
    assert_eq!(values.get("y").unwrap(), "3");
}

#[test]
fn test_parse_get_value_negative() {
    let lines = vec!["((x (- 7)))".to_string()];
    let values = parse_get_value(&lines).unwrap();
    assert_eq!(values.get("x").unwrap(), "(- 7)");
}

#[test]
fn test_parse_get_value_multiline() {
    let lines = vec![
        "((x 1)".to_string(),
        " (y 2)".to_string(),
        " (z (- 3)))".to_string(),
    ];
    let values = parse_get_value(&lines).unwrap();
    assert_eq!(values.get("x").unwrap(), "1");
    assert_eq!(values.get("y").unwrap(), "2");
    assert_eq!(values.get("z").unwrap(), "(- 3)");
}

#[test]
fn test_parse_get_value_bool() {
    let lines = vec!["((b true) (c false))".to_string()];
    let values = parse_get_value(&lines).unwrap();
    assert_eq!(values.get("b").unwrap(), "true");
    assert_eq!(values.get("c").unwrap(), "false");
}

#[test]
fn test_parse_get_value_empty() {
    let lines: Vec<String> = vec![];
    let values = parse_get_value(&lines).unwrap();
    assert!(values.is_empty());
}

#[test]
fn test_parse_smt_int_positive() {
    assert_eq!(parse_smt_int("42").unwrap(), 42);
}

#[test]
fn test_parse_smt_int_negative() {
    assert_eq!(parse_smt_int("(- 7)").unwrap(), -7);
}

#[test]
fn test_parse_smt_int_zero() {
    assert_eq!(parse_smt_int("0").unwrap(), 0);
}

#[test]
fn test_parse_ay_output_sat() {
    let output = "sat\n((x 5))\n";
    let (status, lines) = parse_ay_output(output).unwrap();
    assert_eq!(status, CheckSatResult::Sat);
    assert_eq!(lines, vec!["((x 5))"]);
}

#[test]
fn test_parse_ay_output_unsat() {
    let output = "unsat\n";
    let (status, lines) = parse_ay_output(output).unwrap();
    assert_eq!(status, CheckSatResult::Unsat);
    assert!(lines.is_empty());
}

#[test]
fn test_parse_ay_output_unknown() {
    let output = "unknown\n";
    let (status, _) = parse_ay_output(output).unwrap();
    assert_eq!(status, CheckSatResult::Unknown);
}

#[test]
fn test_parse_get_value_underscore_names() {
    let lines = vec!["((q_1 2) (q_2 4) (q_3 1))".to_string()];
    let values = parse_get_value(&lines).unwrap();
    assert_eq!(values.get("q_1").unwrap(), "2");
    assert_eq!(values.get("q_2").unwrap(), "4");
    assert_eq!(values.get("q_3").unwrap(), "1");
}

#[test]
fn test_parse_get_value_multiple_blocks() {
    // ay returns separate blocks for separate (get-value ...) commands
    let lines = vec!["((x 1) (y 2))".to_string(), "((obj 3))".to_string()];
    let values = parse_get_value(&lines).unwrap();
    assert_eq!(values.get("x").unwrap(), "1");
    assert_eq!(values.get("y").unwrap(), "2");
    assert_eq!(values.get("obj").unwrap(), "3");
}

#[test]
fn test_parse_get_value_multiple_blocks_negative() {
    let lines = vec!["((x 1) (y (- 2)))".to_string(), "((obj (- 5)))".to_string()];
    let values = parse_get_value(&lines).unwrap();
    assert_eq!(values.get("x").unwrap(), "1");
    assert_eq!(values.get("y").unwrap(), "(- 2)");
    assert_eq!(values.get("obj").unwrap(), "(- 5)");
}

#[test]
fn test_parse_smt_int_invalid_string() {
    assert!(parse_smt_int("abc").is_err());
}

#[test]
fn test_parse_smt_int_malformed_negative() {
    assert!(parse_smt_int("(- )").is_err());
    assert!(parse_smt_int("(- abc)").is_err());
}

#[test]
fn test_parse_smt_int_empty() {
    assert!(parse_smt_int("").is_err());
}

// --- Boundary condition tests (algorithm_audit) ---

#[test]
fn test_parse_smt_int_i64_min() {
    // Fixed: parse_smt_int now parses the unsigned part as u64 before negating,
    // correctly handling i64::MIN whose absolute value overflows i64.
    assert_eq!(
        parse_smt_int("(- 9223372036854775808)").expect("should parse i64::MIN"),
        i64::MIN
    );
}

#[test]
fn test_parse_smt_int_overflow() {
    // Values beyond i64 range should error.
    assert!(parse_smt_int("(- 9223372036854775809)").is_err());
    assert!(parse_smt_int("(- 18446744073709551615)").is_err());
}

#[test]
fn test_parse_smt_int_i64_max() {
    assert_eq!(parse_smt_int("9223372036854775807").unwrap(), i64::MAX);
}

#[test]
fn test_parse_smt_int_i64_max_negative() {
    assert_eq!(parse_smt_int("(- 9223372036854775807)").unwrap(), -i64::MAX);
}

#[test]
fn test_parse_smt_int_overflow_u64() {
    // Value exceeding u64 range should produce an error
    assert!(parse_smt_int("(- 99999999999999999999)").is_err());
}

#[test]
fn test_parse_smt_int_overflow_i64_positive() {
    // Value exceeding i64::MAX should produce an error for positive integers
    assert!(parse_smt_int("9223372036854775808").is_err());
}

#[test]
fn test_parse_smt_int_beyond_i64_min() {
    // -(i64::MAX + 2) = -9223372036854775809, which doesn't fit in i64
    assert!(parse_smt_int("(- 9223372036854775809)").is_err());
}

#[test]
fn test_extract_reason_unknown_timeout() {
    let lines = vec![r#"(:reason-unknown "timeout")"#.to_string()];
    assert_eq!(extract_reason_unknown(&lines), Some("timeout".to_string()));
}

#[test]
fn test_extract_reason_unknown_incomplete() {
    let lines = vec![r#"(:reason-unknown "incomplete")"#.to_string()];
    assert_eq!(
        extract_reason_unknown(&lines),
        Some("incomplete".to_string())
    );
}

#[test]
fn test_extract_reason_unknown_absent() {
    let lines = vec!["((x 5))".to_string()];
    assert_eq!(extract_reason_unknown(&lines), None);
}

#[test]
fn test_extract_reason_unknown_with_error_lines() {
    // After unknown, ay may emit an error for get-value before the reason
    let lines = vec![
        r#"(error "model is not available")"#.to_string(),
        r#"(:reason-unknown "timeout")"#.to_string(),
    ];
    assert_eq!(extract_reason_unknown(&lines), Some("timeout".to_string()));
}

#[test]
fn test_parse_ay_output_empty() {
    let output = "";
    assert!(parse_ay_output(output).is_err());
}

#[test]
fn test_parse_ay_output_unexpected() {
    let output = "error\n";
    let result = parse_ay_output(output);
    assert!(result.is_err());
}

// --- build_output_get_value tests (proof coverage: previously untested) ---

#[test]
fn test_build_output_get_value_empty() {
    let result = TranslationResult {
        smtlib: String::new(),
        declarations: String::new(),
        output_vars: vec![],
        objective: None,
        output_smt_names: vec![],
        smt_var_names: vec![],
        search_annotations: vec![],
        var_domains: HashMap::default(),
    };
    assert_eq!(build_output_get_value(&result), "");
}

#[test]
fn test_build_output_get_value_single_var() {
    let result = TranslationResult {
        smtlib: String::new(),
        declarations: String::new(),
        output_vars: vec![],
        objective: None,
        output_smt_names: vec!["x".into()],
        smt_var_names: vec!["x".into()],
        search_annotations: vec![],
        var_domains: HashMap::default(),
    };
    assert_eq!(build_output_get_value(&result), "(get-value (x))\n");
}

#[test]
fn test_build_output_get_value_multiple_vars() {
    let result = TranslationResult {
        smtlib: String::new(),
        declarations: String::new(),
        output_vars: vec![],
        objective: None,
        output_smt_names: vec!["q_1".into(), "q_2".into(), "q_3".into()],
        smt_var_names: vec![],
        search_annotations: vec![],
        var_domains: HashMap::default(),
    };
    assert_eq!(
        build_output_get_value(&result),
        "(get-value (q_1 q_2 q_3))\n"
    );
}

// --- SolverError Display tests (proof coverage: previously untested) ---

#[test]
fn test_solver_error_display_empty_output() {
    let err = SolverError::EmptyOutput;
    assert_eq!(format!("{err}"), "solver produced no output");
}

#[test]
fn test_solver_error_display_unexpected_output() {
    let err = SolverError::UnexpectedOutput("garbage".into());
    assert_eq!(format!("{err}"), "unexpected solver output: garbage");
}

#[test]
fn test_solver_error_display_missing_objective() {
    let err = SolverError::MissingObjective("obj_cost".into());
    assert_eq!(format!("{err}"), "objective 'obj_cost' not in model");
}

#[test]
fn test_solver_error_display_parse_int() {
    let err = SolverError::ParseIntError("abc".into());
    assert_eq!(format!("{err}"), "cannot parse integer: abc");
}

#[test]
fn test_solver_error_source_io() {
    let err = SolverError::IoError(io::Error::new(io::ErrorKind::BrokenPipe, "pipe"));
    assert!(std::error::Error::source(&err).is_some());
}

#[test]
fn test_solver_error_source_none() {
    let err = SolverError::EmptyOutput;
    assert!(std::error::Error::source(&err).is_none());
}

#[test]
fn test_solver_error_display_solver_error() {
    let err = SolverError::SolverError("segfault in ay".into());
    assert_eq!(format!("{err}"), "solver error: segfault in ay");
}

#[test]
fn test_solver_error_display_io_error() {
    let err = SolverError::IoError(io::Error::new(io::ErrorKind::BrokenPipe, "pipe broken"));
    let msg = format!("{err}");
    assert!(msg.contains("I/O error"));
    assert!(msg.contains("pipe broken"));
}

// --- run_ay dispatcher coverage (proof_coverage) ---

#[test]
fn test_run_ay_library_trivial_sat() {
    // run_ay uses the in-process ay library executor.
    let config = SolverConfig {
        timeout_ms: None,
        all_solutions: false,
        global_deadline: None,
    };
    let result = run_ay("(check-sat)\n", &config);
    assert!(result.is_ok(), "run_ay should succeed: {result:?}");
    let output = result.unwrap();
    assert!(
        output.starts_with("sat") || output.starts_with("unsat") || output.starts_with("unknown"),
        "output should contain check-sat result: {output:?}"
    );
}
