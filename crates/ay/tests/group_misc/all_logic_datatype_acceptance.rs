// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Regression test for Issue #901: (set-logic ALL) should not be rejected when
// declare-datatype is present.

use ntest::timeout;
use std::process::Command;

#[test]
#[timeout(60000)]
fn test_all_logic_datatype_is_accepted() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    // CARGO_MANIFEST_DIR is crates/ay, go up two levels to workspace root.
    let benchmark_path = format!(
        "{}/../../benchmarks/smt/regression/all_logic_datatype_sat.smt2",
        env!("CARGO_MANIFEST_DIR")
    );

    let output = Command::new(ay_path)
        .arg(&benchmark_path)
        .output()
        .expect("failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();

    assert!(
        !stdout.contains("unsupported logic") && !stderr.contains("unsupported logic"),
        "expected ALL to be accepted, got stdout={stdout:?} stderr={stderr:?}"
    );

    assert_eq!(
        stdout.trim().lines().next().unwrap_or(""),
        "sat",
        "expected sat, got stdout={stdout:?} stderr={stderr:?}"
    );
}
