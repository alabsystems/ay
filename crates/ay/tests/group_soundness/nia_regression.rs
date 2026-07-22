// NIA regression tests
//
// Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
//
// These tests verify that NIA benchmarks continue to produce expected results.
// Currently NIA is incomplete for SAT-finding (returns Unknown for satisfiable
// problems), but the sign consistency MVP should always return UNSAT for
// sign-inconsistent problems.

use ntest::timeout;
use std::process::Command;

fn run_ay(smt_file: &str) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    // Benchmarks are at workspace root, not in crate directory
    // CARGO_MANIFEST_DIR is crates/ay, so go up two levels to workspace root
    let benchmark_path = format!(
        "{}/../../benchmarks/smt/QF_NIA/{}",
        env!("CARGO_MANIFEST_DIR"),
        smt_file
    );

    let output = Command::new(ay_path)
        .arg(&benchmark_path)
        .output()
        .expect("Failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();

    // Normalize the output - take just the first word (sat, unsat, unknown)
    stdout.trim().lines().next().unwrap_or("").to_string()
}

/// Test that sign consistency conflict detection works.
/// This is the core MVP feature for NIA: detecting sign-inconsistent constraints.
/// x > 0, y > 0, x*y < 0 should be UNSAT because positive * positive cannot be negative.
#[test]
#[timeout(60000)]
fn test_nia_sign_consistency_unsat() {
    let result = run_ay("sign_consistency.smt2");
    assert_eq!(
        result, "unsat",
        "sign_consistency.smt2 should be unsat, got: {result}"
    );
}

/// Test that simple_product_sat is solved by bounded enumeration.
/// This problem is satisfiable (x=2, y=3, x*y=6).
#[test]
#[timeout(60000)]
fn test_nia_simple_product_sat_soundness() {
    let result = run_ay("simple_product_sat.smt2");
    assert_eq!(
        result, "sat",
        "simple_product_sat.smt2 should be sat, got: {result}"
    );
}

/// Test that simple_product_unsat is solved by bounded enumeration.
/// This problem is unsatisfiable (x, y in [1, 2], x*y = 7).
#[test]
#[timeout(60000)]
fn test_nia_simple_product_unsat_soundness() {
    let result = run_ay("simple_product_unsat.smt2");
    assert_eq!(
        result, "unsat",
        "simple_product_unsat.smt2 should be unsat, got: {result}"
    );
}

/// Test that square_bounds is solved by bounded enumeration.
/// This problem is satisfiable (x=3 or x=-3, x^2=9).
#[test]
#[timeout(60000)]
fn test_nia_square_bounds_soundness() {
    let result = run_ay("square_bounds.smt2");
    assert_eq!(
        result, "sat",
        "square_bounds.smt2 should be sat, got: {result}"
    );
}

/// Test that tswift_pattern doesn't falsely claim UNSAT.
/// This is the pattern from tSwift that motivated NIA support.
/// Current behavior: Returns "unknown" (sound but incomplete).
#[test]
#[timeout(60000)]
fn test_nia_tswift_pattern_soundness() {
    let result = run_ay("tswift_pattern.smt2");
    // Sound: must NOT return "unsat" for a satisfiable problem
    assert_ne!(
        result, "unsat",
        "tswift_pattern.smt2 should not be unsat (it's satisfiable), got: {result}"
    );
}
