// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Release-only CLI regression for #6564.
//!
//! The existing `ay-dpll` regression covers the in-process `Executor` path.
//! This file exercises the shipped `ay` binary via `CARGO_BIN_EXE_ay` so the
//! subprocess/CLI path cannot silently diverge from the library path.

#[cfg(not(debug_assertions))]
use ntest::timeout;
#[cfg(not(debug_assertions))]
use std::process::Command;

#[cfg(not(debug_assertions))]
fn run_ay_file(path: &str) -> (std::process::ExitStatus, String, String) {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let output = Command::new(ay_path)
        .arg(path)
        .output()
        .expect("failed to spawn ay");
    (
        output.status,
        String::from_utf8_lossy(&output.stdout).to_string(),
        String::from_utf8_lossy(&output.stderr).to_string(),
    )
}

#[cfg(not(debug_assertions))]
#[test]
#[timeout(120_000)]
fn test_constraints_tempo_width_10_is_always_sat_via_cli_6564() {
    let benchmark_path = format!(
        "{}/../../benchmarks/smtcomp/QF_LRA/constraints-tempo-width-10.smt2",
        env!("CARGO_MANIFEST_DIR")
    );
    assert!(
        std::path::Path::new(&benchmark_path).exists(),
        "benchmark not found: {benchmark_path}"
    );

    for run in 0..10 {
        let (status, stdout, stderr) = run_ay_file(&benchmark_path);
        assert!(
            status.success(),
            "release CLI run {run} exited with {status:?}\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );

        let first_line = stdout.lines().next().unwrap_or_default().trim();
        assert_eq!(
            first_line, "sat",
            "release CLI run {run} disagreed on constraints-tempo-width-10 (#6564)\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
    }
}
