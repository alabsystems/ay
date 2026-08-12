// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Competition-mode switch plumbing, CLI surface (#proof-capability B1).
//!
//! `AY_COMPETITION=1` is the generic harness env signal: it must enter
//! competition mode exactly like `--competition` (suppressing the default
//! proof-certificate emission), while an explicit `--proof FILE` still WINS
//! (documented precedence, never a clap conflict).

use ntest::timeout;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

struct CleanupGuard(PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn temp_path(extension: &str) -> (PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_competition_mode_b1_{}_{}.{}",
        std::process::id(),
        file_id,
        extension
    ));
    (path.clone(), CleanupGuard(path))
}

fn write_temp(contents: &str, extension: &str) -> (PathBuf, CleanupGuard) {
    let (path, cleanup) = temp_path(extension);
    std::fs::write(&path, contents).expect("write temp input");
    (path, cleanup)
}

/// Trivially unsatisfiable QF_UF instance.
const TRIVIAL_UNSAT_SMT: &str = "(set-logic QF_UF)\n\
(declare-const p Bool)\n\
(assert p)\n\
(assert (not p))\n\
(check-sat)\n";

/// The default (certified, batteries-on) run emits the sibling `.alethe`
/// certificate for an UNSAT verdict — the baseline the env signal must
/// suppress.
#[test]
#[timeout(120_000)]
fn default_run_emits_sibling_alethe_artifact() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_UNSAT_SMT, "smt2");
    let alethe = PathBuf::from(format!("{}.alethe", input.display()));
    let _alethe_cleanup = CleanupGuard(alethe.clone());

    let output = Command::new(ay_path)
        .arg(&input)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.lines().any(|line| line.trim() == "unsat"),
        "default certified run must publish unsat, got stdout={stdout} stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        alethe.exists(),
        "default run must emit the sibling .alethe certificate"
    );
}

/// `AY_COMPETITION=1` (no flag at all) enters competition mode: the default
/// proof-certificate emission is suppressed. The verdict remains sound and
/// fail-closed — in v1 (pre-B3 raw admission) an UNSAT may degrade to
/// `unknown`; it must never publish anything else.
#[test]
#[timeout(120_000)]
fn ay_competition_env_suppresses_default_proof_artifact() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_UNSAT_SMT, "smt2");
    let alethe = PathBuf::from(format!("{}.alethe", input.display()));
    let _alethe_cleanup = CleanupGuard(alethe.clone());

    let output = Command::new(ay_path)
        .env("AY_COMPETITION", "1")
        .arg(&input)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let verdict = stdout
        .lines()
        .map(str::trim)
        .find(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .unwrap_or_default()
        .to_string();
    assert!(
        verdict == "unsat" || verdict == "unknown",
        "competition-mode UNSAT must stay fail-closed (unsat or unknown), \
         got stdout={stdout} stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        !alethe.exists(),
        "AY_COMPETITION=1 must suppress the default .alethe emission"
    );
}

/// Documented precedence: an explicit `--proof FILE` WINS over competition
/// mode — even with the env signal set, the run restores the certified lane,
/// publishes `unsat`, and writes the requested proof.
#[test]
#[timeout(120_000)]
fn explicit_proof_flag_wins_over_competition_env() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_UNSAT_SMT, "smt2");
    let (proof, _proof_cleanup) = temp_path("alethe");

    let output = Command::new(ay_path)
        .env("AY_COMPETITION", "1")
        .arg("--proof")
        .arg(&proof)
        .arg(&input)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.lines().any(|line| line.trim() == "unsat"),
        "--proof must win over AY_COMPETITION=1 and publish certified unsat, \
         got stdout={stdout} stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let proof_len = std::fs::metadata(&proof).map(|m| m.len()).unwrap_or(0);
    assert!(
        proof_len > 0,
        "--proof must still write the requested certificate under \
         AY_COMPETITION=1"
    );
}
