// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A memout leaves no synthesized-default proof status lock (2026-10-08).
//!
//! `ay x.cnf` reserves `x.cnf.drat.ay-status.lock` for its default proof
//! before anything else. Under `--memory 1` the memory watchdog ends the run
//! at once, and the lock used to be left behind: no exit-time owner knew of
//! it until the proof file was registered. A stranded lock makes every later
//! run on that path skip its proof ("status transaction ... is already
//! active"). MEASURED on d5887e3fb, debug binary: 23 of 30 sequential runs
//! left the lock; with the status custody (dimacs/status_custody.rs), 0 of 30.

use ntest::timeout;
use std::process::Command;
use std::time::Duration;

use crate::spawn::OutputTimeout;

#[test]
#[timeout(180_000)]
fn a_memout_leaves_no_status_lock_beside_its_input() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    for run in 0..5 {
        let dir = tempfile::tempdir().expect("tempdir");
        let input = dir.path().join("t.cnf");
        std::fs::write(&input, "p cnf 1 2\n1 0\n-1 0\n").expect("write CNF");
        let output = Command::new(ay_path)
            .args(["--quiet", "--memory", "1", "-T:20"])
            .arg(&input)
            .current_dir(dir.path())
            .output_timeout(Duration::from_secs(60))
            .expect("spawn ay");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stdout.lines().any(|line| line == "s UNKNOWN"),
            "run {run}: a memout answers UNKNOWN; stdout: {stdout} stderr: {stderr}"
        );
        assert_eq!(
            output.status.code(),
            Some(124),
            "run {run}: the memout exit code; stderr: {stderr}"
        );
        let mut left: Vec<String> = std::fs::read_dir(dir.path())
            .expect("read the run's directory")
            .map(|entry| {
                entry
                    .expect("entry")
                    .file_name()
                    .to_string_lossy()
                    .into_owned()
            })
            .filter(|name| {
                name.ends_with(".ay-status.lock") || name.starts_with(".ay-dimacs-proof-")
            })
            .collect();
        left.sort();
        assert!(
            left.is_empty(),
            "run {run}: the memout stranded {left:?}; stderr: {stderr}"
        );
    }
}

/// The negative twin of the unanswered exit's revocation
/// (dimacs/status_custody.rs): an unanswered exit rewrites a published
/// `current-same-run` marker `stale-not-current`, but a run that printed its
/// UNSAT verdict keeps that marker through the process-exit sweep, still
/// naming the bytes of its proof.
#[test]
#[timeout(120_000)]
fn a_decisive_unsat_keeps_its_current_marker_through_the_exit_sweep() {
    use sha2::{Digest, Sha256};
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let dir = tempfile::tempdir().expect("tempdir");
    let input = dir.path().join("t.cnf");
    std::fs::write(&input, "p cnf 1 2\n1 0\n-1 0\n").expect("write CNF");
    let output = Command::new(ay_path)
        .arg(&input)
        .current_dir(dir.path())
        .output_timeout(Duration::from_mins(1))
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(20),
        "stdout: {stdout} stderr: {stderr}"
    );
    assert!(
        stdout.lines().any(|line| line == "s UNSATISFIABLE"),
        "stdout: {stdout}"
    );
    let proof = std::fs::read(dir.path().join("t.cnf.drat")).expect("the published proof");
    let marker = std::fs::read_to_string(dir.path().join("t.cnf.drat.ay-status"))
        .expect("the status marker");
    assert!(
        marker.lines().any(|line| line == "status=current-same-run"),
        "marker: {marker} stderr: {stderr}"
    );
    let sha256 = format!("sha256={:x}", Sha256::digest(proof));
    assert!(
        marker.lines().any(|line| line == sha256),
        "marker: {marker}"
    );
}
