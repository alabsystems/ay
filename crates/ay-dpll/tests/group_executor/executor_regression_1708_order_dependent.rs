// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Regression test for BV soundness bug #1708/#1818.
//!
//! `regression_1708_order_dependent.smt2` was incorrectly reported SAT due to
//! missing propagation after watch reinitialization (same root cause as #1818).
//!
//! This test runs quickly (~1s) even in debug mode.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

#[test]
#[timeout(30_000)] // Should complete in <1s, allow generous margin
fn test_executor_regression_1708_order_dependent_unsat() {
    let mut path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("../../tests/bv/regression_1708_order_dependent.smt2");
    let input = std::fs::read_to_string(path).expect("read regression_1708_order_dependent.smt2");

    let commands = parse(&input).expect("parse");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all");

    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));
}
