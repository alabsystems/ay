// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for stray SAT preprocess diagnostics leaking into normal CHC CLI output.

use ntest::timeout;
use std::process::Command;

#[test]
#[timeout(30_000)]
fn test_chc_cli_output_excludes_preprocess_diagnostics_5970() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let benchmark_path = format!(
        "{}/../../benchmarks/chc/counter_safe_chccomp.smt2",
        env!("CARGO_MANIFEST_DIR")
    );

    let output = Command::new(ay_path)
        .arg("--chc")
        .arg(&benchmark_path)
        .output()
        .expect("Failed to spawn ay");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}",
        output.status
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stdout.starts_with("sat\n") || stdout.trim() == "sat",
        "Expected CHC stdout to start with 'sat', got stdout={stdout:?} stderr={stderr:?}"
    );

    for marker in [
        "[preprocess-breakdown]",
        "[preprocess-phases]",
        "[preprocess-final]",
        "c preprocess:",
    ] {
        assert!(
            !stderr.contains(marker),
            "Expected no SAT preprocess diagnostics on stderr, found {marker:?} in {stderr:?}"
        );
    }
}
