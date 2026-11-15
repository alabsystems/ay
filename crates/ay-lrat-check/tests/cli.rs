// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exit-status contract of the `ay-lrat-check` binary: 0 and `s VERIFIED`
//! only for a checked refutation; 1 and `s NOT VERIFIED` otherwise. `main`
//! now returns an `ExitCode` instead of calling `std::process::exit`, and
//! these tests pin that the statuses did not move.

#![forbid(unsafe_code)]

use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

static TEMP_SEQUENCE: AtomicU64 = AtomicU64::new(0);

fn fixture_paths(label: &str) -> (PathBuf, PathBuf) {
    let sequence = TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed);
    let stem = format!(
        "ay_lrat_check_cli_{label}_{}_{sequence}",
        std::process::id()
    );
    let root = std::env::temp_dir();
    (
        root.join(format!("{stem}.cnf")),
        root.join(format!("{stem}.lrat")),
    )
}

fn run_checker(label: &str, cnf: &[u8], proof: &[u8]) -> Output {
    let (cnf_path, proof_path) = fixture_paths(label);
    std::fs::write(&cnf_path, cnf).expect("write CLI CNF fixture");
    std::fs::write(&proof_path, proof).expect("write CLI LRAT fixture");
    let output = Command::new(env!("CARGO_BIN_EXE_ay-lrat-check"))
        .arg(&cnf_path)
        .arg(&proof_path)
        .output()
        .expect("run ay-lrat-check CLI");
    let _ = std::fs::remove_file(cnf_path);
    let _ = std::fs::remove_file(proof_path);
    output
}

#[test]
fn verified_proof_exits_zero() {
    // (x) and (~x): the empty clause 3 follows from hints 1 and 2.
    let output = run_checker("verified", b"p cnf 1 2\n1 0\n-1 0\n", b"3 0 1 2 0\n");
    assert_eq!(output.status.code(), Some(0), "{output:?}");
    assert_eq!(String::from_utf8_lossy(&output.stdout), "s VERIFIED\n");
}

#[test]
fn rejected_proof_exits_one() {
    // (x) alone is satisfiable: the empty clause cannot follow from hint 1.
    let output = run_checker("rejected", b"p cnf 1 1\n1 0\n", b"2 0 1 0\n");
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert_eq!(String::from_utf8_lossy(&output.stdout), "s NOT VERIFIED\n");
}

#[test]
fn unreadable_input_exits_one() {
    let output = Command::new(env!("CARGO_BIN_EXE_ay-lrat-check"))
        .arg("/nonexistent/ay-lrat-check/f.cnf")
        .arg("/nonexistent/ay-lrat-check/p.lrat")
        .output()
        .expect("run ay-lrat-check CLI");
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert_eq!(String::from_utf8_lossy(&output.stdout), "s NOT VERIFIED\n");
}

#[test]
fn usage_error_exits_one() {
    let output = Command::new(env!("CARGO_BIN_EXE_ay-lrat-check"))
        .output()
        .expect("run ay-lrat-check CLI");
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert_eq!(String::from_utf8_lossy(&output.stdout), "s NOT VERIFIED\n");
    assert!(String::from_utf8_lossy(&output.stderr).starts_with("usage: "));
}

#[test]
fn provenance_exits_zero() {
    let output = Command::new(env!("CARGO_BIN_EXE_ay-lrat-check"))
        .arg("--provenance")
        .output()
        .expect("run ay-lrat-check CLI");
    assert_eq!(output.status.code(), Some(0), "{output:?}");
    assert!(String::from_utf8_lossy(&output.stdout).contains("ay-exact-binary-provenance-v1"));
}
