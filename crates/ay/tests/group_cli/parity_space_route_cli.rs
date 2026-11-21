// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The parity-space route (AY-SAT-2) is reached on the scoreboard's path:
//! `ay solve --proof P --proof-format veripb file.cnf` goes through
//! `run_dimacs_proof_from_file`, not the in-memory content route. A run that
//! answers through it prints `c parity-space: model ...` on stderr; with the
//! route switched off the ordinary search answers the same formula without
//! that line.

use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

/// x1 ^ x2 ^ x3 = 1 written as three clauses plus the supporting binary
/// (x1 | x2), and x3 ^ x4 ^ x5 = 0 in full.
const NEAR_PURE_XOR: &str = "p cnf 5 8
-1 -2 3 0
-1 2 -3 0
1 -2 -3 0
1 2 0
3 4 -5 0
3 -4 5 0
-3 4 5 0
-3 -4 -5 0
";

struct Paths {
    cnf: PathBuf,
    proof: PathBuf,
}

impl Drop for Paths {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.cnf);
        let _ = std::fs::remove_file(&self.proof);
    }
}

fn paths(stem: &str) -> Paths {
    static ID: AtomicUsize = AtomicUsize::new(0);
    let id = ID.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let dir = std::env::temp_dir();
    let cnf = dir.join(format!("ay_parity_space_{pid}_{stem}_{id}.cnf"));
    let proof = dir.join(format!("ay_parity_space_{pid}_{stem}_{id}.pbp"));
    std::fs::write(&cnf, NEAR_PURE_XOR).expect("write temp cnf");
    Paths { cnf, proof }
}

fn solve(paths: &Paths, proof: bool, extra: &[&str]) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_ay"));
    command.arg("solve");
    if proof {
        command
            .arg("--proof")
            .arg(&paths.proof)
            .args(["--proof-format", "veripb", "--proof-checker", "veripb"])
            .arg("--no-verify-proof");
    }
    command.args(extra).arg(&paths.cnf);
    command.output().expect("spawn ay")
}

/// The model of the v-lines, by variable (1-based; index 0 unused).
fn model(stdout: &str) -> Vec<Option<bool>> {
    let mut values = vec![None; 6];
    for line in stdout.lines().filter(|line| line.starts_with("v ")) {
        for token in line[2..].split_whitespace() {
            let lit: i64 = token.parse().expect("v-line literal");
            if lit != 0 {
                let var = usize::try_from(lit.unsigned_abs()).expect("var");
                if var < values.len() {
                    values[var] = Some(lit > 0);
                }
            }
        }
    }
    values
}

fn assert_sat_with_a_model(output: &Output) -> (String, String) {
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    let code = output.status.code();
    assert_eq!(code, Some(10), "stdout={stdout}; stderr={stderr}");
    let sat = stdout.lines().any(|line| line == "s SATISFIABLE");
    assert!(sat, "stdout={stdout}");
    let values = model(&stdout);
    for line in NEAR_PURE_XOR.lines().skip(1) {
        let satisfied = line
            .split_whitespace()
            .map(|token| token.parse::<i64>().expect("literal"))
            .take_while(|&lit| lit != 0)
            .any(|lit| {
                let var = usize::try_from(lit.unsigned_abs()).expect("var");
                values[var] == Some(lit > 0)
            });
        assert!(satisfied, "clause {line} unsatisfied; stdout={stdout}");
    }
    (stdout, stderr)
}

#[test]
fn a_cnf_file_with_a_veripb_proof_is_answered_by_the_parity_space_route() {
    let paths = paths("proof");
    let output = solve(&paths, true, &[]);
    let (_, stderr) = assert_sat_with_a_model(&output);
    assert!(
        stderr.contains("c parity-space: model"),
        "the proof-mode file path did not reach the route: {stderr}"
    );
}

#[test]
fn a_cnf_file_without_a_proof_is_answered_by_the_parity_space_route() {
    let paths = paths("noproof");
    let output = solve(&paths, false, &[]);
    let (_, stderr) = assert_sat_with_a_model(&output);
    let reached = stderr.contains("c parity-space: model");
    assert!(reached, "stderr={stderr}");
}

#[test]
fn the_switch_and_a_zero_budget_turn_the_route_off() {
    for extra in [
        &["--sat-parity-space-route", "false"][..],
        &["--sat-parity-space-budget-ms", "0"][..],
    ] {
        let paths = paths("off");
        let output = solve(&paths, true, extra);
        let (_, stderr) = assert_sat_with_a_model(&output);
        assert!(
            !stderr.contains("c parity-space"),
            "{extra:?} did not turn the route off: {stderr}"
        );
    }
}
