// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for solver parsing functions: parse_get_value, parse_smt_int.
//!
//! Covers multi-block parse_get_value regression ([P1]411), error paths in
//! parse_smt_int, and edge cases in SolverConfig.
//!
//! Part of #319 (FlatZinc translation correctness), #273 (MiniZinc entry).

use ay_flatzinc_smt::solver::{parse_get_value, parse_smt_int, CheckSatResult, SolverConfig};

// --- Multi-block parse_get_value tests ---
// Regression test for multi-block parse_get_value bug ([P1]411).
// During optimization, ay returns two get-value responses on separate lines:
//   (get-value (x y))  → ((x 1) (y 2))
//   (get-value (obj))  → ((obj 3))
// The parser must merge all blocks into one map.

#[test]
fn test_parse_get_value_multi_block_merges_all() {
    // Two get-value response blocks on separate lines (optimization case)
    let lines = vec!["((x 1) (y 2))".to_string(), "((obj 3))".to_string()];
    let values = parse_get_value(&lines).unwrap();
    assert_eq!(values.get("x").unwrap(), "1");
    assert_eq!(values.get("y").unwrap(), "2");
    // Fixed: obj is now correctly parsed from the second block.
    assert_eq!(values.get("obj").unwrap(), "3");
    assert_eq!(values.len(), 3);
}

#[test]
fn test_parse_get_value_single_var() {
    let lines = vec!["((x 42))".to_string()];
    let values = parse_get_value(&lines).unwrap();
    assert_eq!(values.len(), 1);
    assert_eq!(values.get("x").unwrap(), "42");
}

#[test]
fn test_parse_get_value_large_negative() {
    let lines = vec!["((x (- 999999)))".to_string()];
    let values = parse_get_value(&lines).unwrap();
    assert_eq!(values.get("x").unwrap(), "(- 999999)");
}

// --- parse_smt_int error path tests ---

#[test]
fn test_parse_smt_int_garbage_returns_error() {
    assert!(parse_smt_int("abc").is_err());
}

#[test]
fn test_parse_smt_int_malformed_negative_returns_error() {
    // Missing closing paren
    assert!(parse_smt_int("(- 7").is_err());
}

#[test]
fn test_parse_smt_int_negative_non_numeric_returns_error() {
    assert!(parse_smt_int("(- abc)").is_err());
}

#[test]
fn test_parse_smt_int_whitespace_padding() {
    assert_eq!(parse_smt_int("  42  ").unwrap(), 42);
}

#[test]
fn test_parse_smt_int_large_positive() {
    assert_eq!(parse_smt_int("2147483647").unwrap(), 2_147_483_647);
}

#[test]
fn test_parse_smt_int_large_negative() {
    assert_eq!(parse_smt_int("(- 2147483647)").unwrap(), -2_147_483_647);
}

// --- SolverConfig default test ---

#[test]
fn test_solver_config_default() {
    let config = SolverConfig::default();
    assert!(config.timeout_ms.is_none());
    assert!(!config.all_solutions);
}

// --- CheckSatResult derive tests ---

#[test]
fn test_check_sat_result_equality() {
    assert_eq!(CheckSatResult::Sat, CheckSatResult::Sat);
    assert_eq!(CheckSatResult::Unsat, CheckSatResult::Unsat);
    assert_eq!(CheckSatResult::Unknown, CheckSatResult::Unknown);
    assert_ne!(CheckSatResult::Sat, CheckSatResult::Unsat);
}

#[test]
fn test_check_sat_result_debug() {
    assert_eq!(format!("{:?}", CheckSatResult::Sat), "Sat");
    assert_eq!(format!("{:?}", CheckSatResult::Unsat), "Unsat");
}
