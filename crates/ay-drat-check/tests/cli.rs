// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

static TEMP_SEQUENCE: AtomicU64 = AtomicU64::new(0);

fn fixture_paths(label: &str) -> (PathBuf, PathBuf) {
    let sequence = TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed);
    let stem = format!(
        "ay_drat_check_cli_{label}_{}_{sequence}",
        std::process::id()
    );
    let root = std::env::temp_dir();
    (
        root.join(format!("{stem}.cnf")),
        root.join(format!("{stem}.drat")),
    )
}

fn run_checker(label: &str, cnf: &[u8], proof: &[u8], args: &[&str]) -> Output {
    let (cnf_path, proof_path) = fixture_paths(label);
    std::fs::write(&cnf_path, cnf).expect("write CLI CNF fixture");
    std::fs::write(&proof_path, proof).expect("write CLI DRAT fixture");
    let output = Command::new(env!("CARGO_BIN_EXE_ay-drat-check"))
        .arg(&cnf_path)
        .arg(&proof_path)
        .args(args)
        .output()
        .expect("run ay-drat-check CLI");
    let _ = std::fs::remove_file(cnf_path);
    let _ = std::fs::remove_file(proof_path);
    output
}

fn assert_verified(output: &Output, mode: &str) {
    assert!(
        output.status.success(),
        "{mode} checker failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout), "s VERIFIED\n");
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(mode),
        "checker diagnostics should identify {mode} mode"
    );
}

#[test]
fn verifies_originally_unsat_formula_in_forward_and_backward_modes() {
    let cnf = b"p cnf 1 2\n1 0\n-1 0\n";
    assert_verified(&run_checker("forward", cnf, b"", &[]), "Forward");
    assert_verified(
        &run_checker("backward", cnf, b"", &["--backward"]),
        "Backward",
    );
}

#[test]
fn malformed_drat_fails_closed() {
    let output = run_checker("malformed", b"p cnf 1 1\n1 0\n", b"not-a-literal\n", &[]);
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(String::from_utf8_lossy(&output.stdout), "s NOT VERIFIED\n");
    assert!(String::from_utf8_lossy(&output.stderr).contains("cannot parse"));
}

#[test]
fn incomplete_proof_fails_closed() {
    let output = run_checker("incomplete", b"p cnf 1 1\n1 0\n", b"", &[]);
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(String::from_utf8_lossy(&output.stdout), "s NOT VERIFIED\n");
    assert!(String::from_utf8_lossy(&output.stderr).contains("verification failed"));
}
