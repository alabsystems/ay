// UFLRA logic acceptance test
//
// Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
//
// Tests that AY accepts (set-logic UFLRA) as a valid SMT-LIB logic string.
// Part of #606: Executor should accept UFLRA set-logic.

use ntest::timeout;
use std::process::Command;

fn run_ay(smt_file: &str) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    // CARGO_MANIFEST_DIR is crates/ay, go up two levels to workspace root
    let benchmark_path = format!(
        "{}/../../benchmarks/smt/UFLRA/{}",
        env!("CARGO_MANIFEST_DIR"),
        smt_file
    );

    let output = Command::new(ay_path)
        .arg(&benchmark_path)
        .output()
        .expect("Failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();

    // Check stderr for "unsupported logic" error which would indicate failure
    if stderr.contains("unsupported logic") || stdout.contains("unsupported logic") {
        return format!("error: {stderr}");
    }

    stdout.trim().lines().next().unwrap_or("").to_string()
}

/// UFLRA logic should be accepted and the contradictory constraints should be UNSAT
#[test]
#[timeout(60000)]
fn test_uflra_logic_accepted() {
    let result = run_ay("uflra_simple.smt2");
    assert_eq!(
        result, "unsat",
        "uflra_simple.smt2 should be unsat (x < 0 AND x > 0 is contradictory), got: {result}"
    );
}
