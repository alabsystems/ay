// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Release-only CLI regression for #6564's implied slack-row reason path.
//!
//! The existing `ay-dpll` regression covers the in-process `Executor` path.
//! This file exercises the shipped `ay` binary via `CARGO_BIN_EXE_ay` so the
//! subprocess/CLI path cannot silently diverge from the library path.
//! The input is hand-authored and Apache-2.0 rather than copied from the
//! externally licensed SMT-LIB benchmark that originally exposed the defect.

#[cfg(not(debug_assertions))]
use ntest::timeout;
#[cfg(not(debug_assertions))]
use std::process::Command;

#[cfg(not(debug_assertions))]
fn run_ay_file(path: &str) -> (std::process::ExitStatus, String, String) {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let output = Command::new(ay_path)
        .arg("--stats")
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
fn stat_u64(stderr: &str, name: &str) -> Option<u64> {
    let prefix = format!(":{name} ");
    stderr.lines().find_map(|line| {
        line.trim()
            .strip_prefix(&prefix)
            .and_then(|raw| raw.parse().ok())
    })
}

#[cfg(not(debug_assertions))]
#[test]
#[timeout(120_000)]
fn qf_lra_cli_release_mechanism_slack_reason_sat_6564() {
    let benchmark_path = format!(
        "{}/../../benchmarks/smt/regression/qf_lra_release_soundness/slack_reason_sat.smt2",
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
            "release CLI run {run} disagreed on the #6564 slack-reason reduction\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            stat_u64(&stderr, "lra_emitted_implied").is_some_and(|count| count > 0),
            "release CLI run {run} did not exercise implied-bound propagation\nstderr:\n{stderr}"
        );
        assert!(
            stat_u64(&stderr, "lra_reasons_lazy_emitted").is_some_and(|count| count > 0),
            "release CLI run {run} did not materialize a lazy LRA reason\nstderr:\n{stderr}"
        );
    }
}
