// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Symmetry proof routing must fail closed without a route-blind CLI refusal.
//!
//! Plain composite and signed lex leaders are no-proof-only. Proof-mode routing
//! permits the family-specific aux-free SR constructions and HHW, and otherwise
//! skips symmetry before any clause is installed. The old generic DPR/full-SR
//! switches are removed rather than left as certificate-producing experiments.

use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

struct DirGuard(PathBuf);

impl Drop for DirGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// Small UNSAT formula for CLI routing and retired-flag checks. Tests that need
/// to exercise symmetry preprocessing itself live in `ay-sat`.
const UNSAT_CNF: &str = "p cnf 1 2\n1 0\n-1 0\n";

fn scratch() -> (PathBuf, DirGuard) {
    static ID: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "ay_uncertifiable_symmetry_{}_{}",
        std::process::id(),
        ID.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("unsat.cnf"), UNSAT_CNF).unwrap();
    (dir.clone(), DirGuard(dir))
}

/// Run AY on `unsat.cnf`, optionally with the composite-symmetry opt-in flag.
/// Returns `(exit code, stderr)`.
fn run(dir: &PathBuf, composite: bool, args: &[&str]) -> (i32, String) {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_ay"));
    cmd.arg("solve").args(args).arg(dir.join("unsat.cnf"));
    if composite {
        cmd.arg("--sat-composite-symmetry");
    }
    let output = cmd.output().expect("failed to run ay");
    let code = output.status.code().expect("ay died on a signal");
    (code, String::from_utf8_lossy(&output.stderr).into_owned())
}

/// Composite symmetry plus an unchecked proof no longer needs a process-wide
/// refusal: preprocessing itself skips the plain lex-leader route.
#[test]
fn composite_symmetry_with_unchecked_proof_falls_back_safely() {
    let (dir, _guard) = scratch();
    let proof = dir.join("p.drat");
    let (code, stderr) = run(
        &dir,
        true,
        &[
            "--no-verify-proof",
            "--proof",
            proof.to_str().unwrap(),
            "--proof-format",
            "drat",
        ],
    );
    assert_eq!(
        code, 20,
        "safe fallback must solve, got {code}; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("certificates that external checkers reject"),
        "the retired route-blind refusal must be gone; stderr: {stderr}"
    );
}

/// HHW is a checker-consumable composite proof route, so a blanket composite
/// gate must not reject it when post-solve rechecking is disabled.
#[test]
fn hhw_with_unchecked_proof_is_not_route_blind_refused() {
    let (dir, _guard) = scratch();
    let proof = dir.join("p.drat");
    let (code, stderr) = run(
        &dir,
        true,
        &[
            "--sat-symmetry-hhw",
            "--no-verify-proof",
            "--proof",
            proof.to_str().unwrap(),
            "--proof-format",
            "drat",
        ],
    );
    assert_eq!(
        code, 20,
        "HHW configuration must be allowed, got {code}; stderr: {stderr}"
    );
}

/// The two uncomposed witness experiments are removed from the CLI, not merely
/// hidden behind another unsafe combination of flags.
#[test]
fn retired_generic_sr_flags_are_unavailable() {
    for flag in ["--sat-symmetry-sr", "--sat-signed-symmetry-sr"] {
        let (dir, _guard) = scratch();
        let (code, stderr) = run(&dir, false, &[flag]);
        assert_eq!(
            code, 2,
            "retired flag {flag} must be rejected; stderr: {stderr}"
        );
        assert!(
            stderr.contains(flag),
            "diagnostic must name {flag}: {stderr}"
        );
    }
}

/// Control 1: the same flag with NO proof requested is untouched. Nothing
/// claims the answer is certified, so the route stays available for research.
#[test]
fn composite_symmetry_without_proof_still_solves() {
    let (dir, _guard) = scratch();
    let (code, stderr) = run(&dir, true, &[]);
    assert_eq!(
        code, 20,
        "composite symmetry without a proof must still answer UNSAT (exit 20), got {code}; \
         stderr: {stderr}"
    );
}

/// Control 2: an unchecked proof WITHOUT the flag is untouched. This is the
/// test that fails if the gate is ever widened into a blanket refusal of
/// `--no-verify-proof`.
#[test]
fn unchecked_proof_without_composite_symmetry_still_solves() {
    let (dir, _guard) = scratch();
    let proof = dir.join("p.drat");
    let (code, stderr) = run(
        &dir,
        false,
        &[
            "--no-verify-proof",
            "--proof",
            proof.to_str().unwrap(),
            "--proof-format",
            "drat",
        ],
    );
    assert_eq!(
        code, 20,
        "an unchecked proof without composite symmetry must still answer UNSAT (exit 20), \
         got {code}; stderr: {stderr}"
    );
}
