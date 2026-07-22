// QF_UFLRA regression tests
//
// Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
//
// Tests for Nelson-Oppen combination of EUF (Equality + Uninterpreted Functions)
// with LRA (Linear Real Arithmetic). Tests verify bidirectional equality propagation
// between theories.

use ntest::timeout;
use std::process::Command;

fn run_ay(smt_file: &str) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    // CARGO_MANIFEST_DIR is crates/ay, go up two levels to workspace root
    let benchmark_path = format!(
        "{}/../../benchmarks/smt/QF_UFLRA/{}",
        env!("CARGO_MANIFEST_DIR"),
        smt_file
    );

    let output = Command::new(ay_path)
        .arg(&benchmark_path)
        .output()
        .expect("Failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    stdout.trim().lines().next().unwrap_or("").to_string()
}

/// f(x) = f(y) when x = y should be SAT
#[test]
#[timeout(60000)]
fn test_sat_equal_args() {
    let result = run_ay("sat_equal_args.smt2");
    assert_eq!(
        result, "sat",
        "sat_equal_args.smt2 should be sat, got: {result}"
    );
}

/// LRA constraints determine x=y=5.0, f(x)≠f(y) is UNSAT
#[test]
#[timeout(60000)]
fn test_unsat_equality_propagation() {
    let result = run_ay("unsat_equality_propagation.smt2");
    assert_eq!(
        result, "unsat",
        "unsat_equality_propagation.smt2 should be unsat, got: {result}"
    );
}

/// #6812: the exact cpachecker benchmark previously returned a false UNSAT.
/// The current soundness fix may answer `unknown`, but it must never return
/// `unsat` for this SAT benchmark again.
#[test]
#[timeout(60000)]
fn test_cpachecker_modulus_not_false_unsat_6812() {
    let result = run_ay(
        "cpachecker-induction-svcomp14/cpachecker-induction.modulus_true-unreach-call.i.smt2",
    );
    assert!(
        matches!(result.as_str(), "sat" | "unknown"),
        "cpachecker-induction.modulus_true-unreach-call.i.smt2 expected sat/unknown, got: {result}"
    );
}
