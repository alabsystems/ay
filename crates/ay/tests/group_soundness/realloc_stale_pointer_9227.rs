// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression guard for #9227.
//!
//! `realloc_stale_pointer_fail.rs::test_realloc_stale_pointer_should_fail`
//! intentionally dereferences the old pointer after `realloc`. Z3 confirms the
//! emitted CHC is reachable (`sat`), so AY may find the counterexample or fail
//! closed to `unknown`, but it must never report `unsat`/PROOF.

use ntest::timeout;
use std::process::Command;

fn first_verdict_line(stdout: &str) -> Option<&str> {
    stdout
        .lines()
        .map(str::trim)
        .find(|line| matches!(*line, "sat" | "unsat" | "unknown"))
}

#[test]
#[timeout(10_000)]
fn realloc_stale_pointer_9227_never_returns_false_proof() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let fixture = format!(
        "{}/tests/group_soundness/fixtures/realloc_stale_pointer_9227.smt2",
        env!("CARGO_MANIFEST_DIR")
    );

    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--chc")
        .arg("--timeout")
        .arg("1000")
        .arg(&fixture)
        .output()
        .expect("failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let verdict = first_verdict_line(&stdout).unwrap_or("<missing>");

    assert_ne!(
        verdict, "unsat",
        "Soundness regression (#9227): AY returned unsat/PROOF for a reachable \
         stale-pointer CHC. Expected sat or fail-closed unknown.\nstatus={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout,
        stderr
    );
    assert!(
        matches!(verdict, "sat" | "unknown"),
        "Unexpected AY CHC verdict for #9227 fixture: {verdict}\nstatus={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout,
        stderr
    );
}
