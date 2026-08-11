// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `AY_SAT_COMPOSITE_SYMMETRY` must not produce an UNSAT that nobody checks.
//!
//! The composite lex-leader route breaks symmetry with an equal-prefix aux
//! tower that is not single-witness PR, so the steps it appends to the proof
//! are not SR-checkable. Measured on the SAT-COMP 2026 instance `count_p2_M21`:
//! AY reports `s UNSATISFIABLE` in 276 ms with an 11 378-line proof, and
//! `dsr-trim` rejects it with `No UP contradiction for RAT clause 11670`.
//!
//! Two of the three legs are individually safe. With proof re-checking ON the
//! internal checker fails closed and the bad certificate never escapes; with no
//! proof requested the answer is uncertified but claims nothing. It is the
//! conjunction -- route active, proof written, re-check off -- that yields a
//! confident unverifiable artifact, and that conjunction is exactly what
//! `--competition` produces. A stderr warning is not enough there because a
//! competition harness reads the verdict and keeps the proof.
//!
//! These tests pin all three legs against the same binary, so the refusal
//! cannot pass by refusing unconditionally.

use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

struct DirGuard(PathBuf);

impl Drop for DirGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// Small UNSAT formula. The refusal is a configuration gate gated before the
/// solve, so it does not need an instance that actually triggers the route.
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

/// Run AY on `unsat.cnf`, optionally with the composite-symmetry env flag set.
/// Returns `(exit code, stderr)`.
fn run(dir: &PathBuf, composite: bool, args: &[&str]) -> (i32, String) {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_ay"));
    cmd.arg("solve").args(args).arg(dir.join("unsat.cnf"));
    if composite {
        cmd.env("AY_SAT_COMPOSITE_SYMMETRY", "1");
    } else {
        cmd.env_remove("AY_SAT_COMPOSITE_SYMMETRY");
    }
    let output = cmd.output().expect("failed to run ay");
    let code = output.status.code().expect("ay died on a signal");
    (code, String::from_utf8_lossy(&output.stderr).into_owned())
}

/// The unsafe conjunction: route on, proof written, re-check off. Must refuse.
#[test]
fn composite_symmetry_with_unchecked_proof_is_refused() {
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
        code, 1,
        "composite symmetry + written proof + no re-check must exit 1, got {code}; stderr: {stderr}"
    );
    assert!(
        stderr.contains("AY_SAT_COMPOSITE_SYMMETRY"),
        "the refusal must name the flag responsible; stderr: {stderr}"
    );
    // Never publish an UNSAT verdict alongside the refusal.
    assert!(
        !stderr.contains("s UNSATISFIABLE"),
        "refusal must not also report a verdict; stderr: {stderr}"
    );
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
