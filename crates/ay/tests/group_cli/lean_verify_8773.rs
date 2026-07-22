// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `--lean-verify` (#8773, Phase 1 thin wrapper).
//!
//! Validates the Phase 1 deliverables from
//! the development design notes:
//! 1. The CLI flag is registered on `ay solve --help` alongside
//!    `--verify-proof` (#8771).
//! 2. The flag is gated on `--proof FILE` (clap `requires = "proof"`) and
//!    `--lean-path` is gated on `--lean-verify`.
//! 3. End-to-end on a trivial UNSAT DIMACS with a `.lean4` proof path, ay
//!    emits `s UNSATISFIABLE`, invokes the Lean verifier, and exits with a
//!    contract-defined code: 20 (Lean accepted) or accepts graceful
//!    "unavailable" degradation when the `lean` binary is not installed.
//! 4. Rejection path: when `--lean-path` points at a bogus binary, the
//!    verifier reports `Unavailable` (not a soundness failure) and ay still
//!    exits 20. This guards against CI environments without Lean installed
//!    from flagging a correct UNSAT as a soundness failure.

use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Trivially-UNSAT DIMACS: (x) AND (not x). Smallest possible UNSAT input
/// so the whole pipeline finishes within the default test timeout. Phase 1
/// uses DIMACS input (SAT path) because Lean4 export is already wired for
/// DIMACS in `ay-sat::lean_export` — the SMT path is Phase 2+ work.
const TRIVIAL_UNSAT: &str = "p cnf 1 2\n1 0\n-1 0\n";

struct CleanupGuard(Vec<PathBuf>);
impl Drop for CleanupGuard {
    fn drop(&mut self) {
        for p in &self.0 {
            let _ = std::fs::remove_file(p);
        }
    }
}

fn temp_paths(stem: &str) -> (PathBuf, PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let cnf = std::env::temp_dir().join(format!("ay_lean_verify_{pid}_{stem}_{id}.cnf"));
    let proof = std::env::temp_dir().join(format!("ay_lean_verify_{pid}_{stem}_{id}.lean4"));
    std::fs::write(&cnf, TRIVIAL_UNSAT).expect("write temp cnf");
    let guard = CleanupGuard(vec![cnf.clone(), proof.clone()]);
    (cnf, proof, guard)
}

fn ay_binary() -> &'static str {
    env!("CARGO_BIN_EXE_ay")
}

/// `--lean-verify` and `--lean-path` MUST appear in `ay solve --help` so
/// users discover the flag. Confirms clap registration.
#[test]
fn test_lean_verify_flag_in_help() {
    let output = Command::new(ay_binary())
        .arg("solve")
        .arg("--help")
        .output()
        .expect("spawn ay --help");
    let help = String::from_utf8_lossy(&output.stdout);
    assert!(
        help.contains("--lean-verify"),
        "--lean-verify must appear in ay solve --help; help={help}"
    );
    assert!(
        help.contains("--lean-path"),
        "--lean-path must appear in ay solve --help; help={help}"
    );
}

/// `--lean-verify` is gated on `--proof FILE` via clap `requires = "proof"`.
/// Invoking it without `--proof` MUST error out at argument parsing time,
/// not silently succeed.
#[test]
fn test_lean_verify_without_proof_flag_errors() {
    let (cnf, _, _guard) = temp_paths("requires_proof");
    let output = Command::new(ay_binary())
        .arg("--lean-verify")
        .arg(&cnf)
        .output()
        .expect("spawn ay");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_ne!(
        output.status.code(),
        Some(20),
        "--lean-verify without --proof must NOT report UNSAT as verified; stderr={stderr}"
    );
    // clap emits "the following required arguments were not provided" or
    // similar when a `requires` gate fails. Accept either a non-zero exit
    // (preferred) or a warning that --lean-verify was ignored.
    assert!(
        output.status.code() != Some(0) && output.status.code() != Some(20),
        "expected non-success exit when --lean-verify missing --proof; exit={:?}; stderr={stderr}",
        output.status.code()
    );
}

/// `--lean-path` is gated on `--lean-verify` via clap `requires`. Invoking
/// `--lean-path` alone (without `--lean-verify`) must error at argument
/// parsing time.
#[test]
fn test_lean_path_without_lean_verify_errors() {
    let (cnf, proof, _guard) = temp_paths("lean_path_req");
    let output = Command::new(ay_binary())
        .arg("--lean-path")
        .arg("/nonexistent/lean")
        .arg("--proof")
        .arg(&proof)
        .arg(&cnf)
        .output()
        .expect("spawn ay");
    assert_ne!(
        output.status.code(),
        Some(20),
        "--lean-path without --lean-verify must not succeed; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// End-to-end: run ay on a trivial UNSAT DIMACS with `--lean-verify` and a
/// `.lean4` proof path, pointing `--lean-path` at a definitely-missing
/// binary. The verifier MUST report `Unavailable` (not Rejected), and
/// because Unavailable is NOT a soundness failure, ay MUST still exit 20.
///
/// This is the contract from the development design notes:
/// Unavailable means "we could not run Lean" (missing / timed out / IO
/// error), which is distinct from Rejected ("Lean ran and said NO"). CI
/// environments without `lean` installed still get a valid UNSAT result.
#[test]
fn test_lean_verify_unavailable_bogus_binary_still_accepts_unsat() {
    let (cnf, proof, _guard) = temp_paths("unavailable");
    let output = Command::new(ay_binary())
        .arg("--lean-verify")
        .arg("--lean-path")
        .arg("/nonexistent/bogus-lean-binary-xyz")
        .arg("--proof")
        .arg(&proof)
        .arg(&cnf)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stdout.contains("s UNSATISFIABLE"),
        "expected UNSATISFIABLE on stdout; stdout={stdout}; stderr={stderr}"
    );
    assert_eq!(
        output.status.code(),
        Some(20),
        "missing lean binary MUST degrade gracefully (exit 20), \
         not falsely report soundness failure; stderr={stderr}"
    );
    assert!(
        stderr.contains("Lean verification unavailable"),
        "expected 'Lean verification unavailable' note on stderr; stderr={stderr}"
    );
    // Crucially: the Unavailable path must NOT print a soundness-failure
    // message. Only genuine Rejected outcomes should mention SOUNDNESS.
    assert!(
        !stderr.contains("SOUNDNESS FAILURE"),
        "Unavailable path must not claim soundness failure; stderr={stderr}"
    );
}

/// `--proof file.lean4` must emit a kernel-checkable proof artifact, not the
/// legacy data-only proof-step dump. This is the CLI boundary needed by #8697:
/// the file carries original clauses plus a `proof_valid` theorem that Lean's
/// kernel can accept or reject.
#[test]
fn test_lean4_proof_output_contains_kernel_checker_boundary() {
    let (cnf, proof, _guard) = temp_paths("kernel_artifact");
    let output = Command::new(ay_binary())
        .arg("--proof")
        .arg(&proof)
        .arg(&cnf)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(20),
        "expected UNSAT exit 20; stdout={stdout}; stderr={stderr}"
    );

    let emitted = std::fs::read_to_string(&proof).expect("read emitted Lean4 proof");
    for marker in [
        "def originalClauses",
        "def lratCheck",
        "def proofSteps",
        "theorem proof_valid",
        "native_decide",
        "(1, [1])",
        "(2, [-1])",
    ] {
        assert!(
            emitted.contains(marker),
            "Lean4 proof missing marker {marker:?}; first 800 bytes:\n{}",
            &emitted[..emitted.len().min(800)]
        );
    }
    assert!(
        !emitted.contains("Original clauses referenced"),
        "Lean4 proof should not use the legacy data-only emitter"
    );
}

/// `--lean-verify` only runs when the emitted proof is Lean4. If the user
/// combines `--lean-verify` with a `.drat` proof path, ay emits a warning
/// and treats the flag as a no-op — the DRAT proof is still validated by
/// `--verify-proof` (when enabled) via the internal checker. This test
/// ensures the flag does not accidentally reject valid DRAT proofs.
#[test]
fn test_lean_verify_with_drat_proof_warns_and_accepts() {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let cnf = std::env::temp_dir().join(format!("ay_lean_verify_drat_{pid}_{id}.cnf"));
    let proof = std::env::temp_dir().join(format!("ay_lean_verify_drat_{pid}_{id}.drat"));
    std::fs::write(&cnf, TRIVIAL_UNSAT).expect("write temp cnf");
    let _guard = CleanupGuard(vec![cnf.clone(), proof.clone()]);

    let output = Command::new(ay_binary())
        .arg("--lean-verify")
        .arg("--proof")
        .arg(&proof)
        .arg(&cnf)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stdout.contains("s UNSATISFIABLE"),
        "expected UNSATISFIABLE on stdout; stdout={stdout}; stderr={stderr}"
    );
    assert_eq!(
        output.status.code(),
        Some(20),
        "DRAT proof with --lean-verify should still exit 20 (flag becomes no-op); stderr={stderr}"
    );
    // The warning is emitted by `verify_lean_proof()` when format != Lean4.
    assert!(
        stderr.contains("--lean-verify requires a Lean4 proof"),
        "expected format-mismatch warning on stderr; stderr={stderr}"
    );
}
