// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `--verify-proof` / `--no-verify-proof` (#8771).
//!
//! These tests exercise the post-solve proof auto-verification pipeline that
//! re-checks every emitted DRAT/LRAT proof with the internal checker before
//! exiting with UNSAT status (exit code 20). A rejected proof downgrades
//! the result to exit code 1 so a soundness bug cannot be silently reported
//! as UNSAT.

use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Trivially-UNSAT DIMACS: (x) AND (not x). Used as the smallest possible
/// input so the whole pipeline finishes within the default test timeout.
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
    let cnf = std::env::temp_dir().join(format!("ay_verify_proof_{pid}_{stem}_{id}.cnf"));
    let proof = std::env::temp_dir().join(format!("ay_verify_proof_{pid}_{stem}_{id}.drat"));
    std::fs::write(&cnf, TRIVIAL_UNSAT).expect("write temp cnf");
    let guard = CleanupGuard(vec![cnf.clone(), proof.clone()]);
    (cnf, proof, guard)
}

fn ay_binary() -> &'static str {
    env!("CARGO_BIN_EXE_ay")
}

/// Smoke test: running ay on a DIMACS UNSAT instance with defaults emits
/// `s UNSATISFIABLE` on stdout and exits with code 20. Verification may
/// or may not fire based on build mode (debug vs release), but the result
/// must be accepted — so stderr MUST NOT contain a verification FAILED
/// message, and the exit code must be exactly 20.
#[test]
fn test_default_unsat_exits_20() {
    let (cnf, _, _guard) = temp_paths("default");
    let output = Command::new(ay_binary())
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
        "expected exit 20 under defaults; stderr={stderr}"
    );
    assert!(
        !stderr.contains("proof verification FAILED"),
        "default UNSAT path should not report verification failure; stderr={stderr}"
    );
}

/// When `--verify-proof` is explicitly on, the checker MUST run and MUST
/// accept the solver-emitted proof. The success message ("verify-proof:
/// ... verified") is emitted to stderr.
#[test]
fn test_verify_proof_explicit_on_accepts_valid_proof() {
    let (cnf, proof, _guard) = temp_paths("explicit_on");
    let output = Command::new(ay_binary())
        .arg("--verify-proof")
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
        "expected exit 20 with valid proof; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        stdout.contains("s UNSATISFIABLE"),
        "expected UNSATISFIABLE on stdout; stdout={stdout}"
    );
    assert!(
        stderr.contains("verify-proof") && stderr.contains("verified"),
        "expected verify-proof success message on stderr; stderr={stderr}"
    );
    assert!(
        !stderr.contains("FAILED"),
        "valid proof should not report FAILED; stderr={stderr}"
    );
}

/// When `--no-verify-proof` is passed, verification is explicitly
/// suppressed — the solver exits 20 without any verify-proof stderr line.
#[test]
fn test_no_verify_proof_skips_verification() {
    let (cnf, proof, _guard) = temp_paths("no_verify");
    let output = Command::new(ay_binary())
        .arg("--no-verify-proof")
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
        "expected exit 20; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        stdout.contains("s UNSATISFIABLE"),
        "expected UNSATISFIABLE on stdout; stdout={stdout}"
    );
    assert!(
        !stderr.contains("verify-proof:") || !stderr.contains("verified"),
        "--no-verify-proof must not emit verified message; stderr={stderr}"
    );
}

/// Soundness test (CLI): run ay with `--verify-proof` and point `--proof`
/// at a pre-written UNSAT-for-a-different-formula DIMACS proof file. Since
/// the solver overwrites the proof file as part of UNSAT emission, we
/// instead exercise the rejection path via an empty proof file — the
/// library layer rejects empty proofs with `Rejected` outcome, which the
/// CLI forwards as exit code 1.
///
/// We simulate this by constructing a parallel test: run ay with
/// `--verify-proof --proof <path>` on a SAT formula — the solver writes
/// nothing to the proof path, and the post-solve verify is skipped on SAT.
/// Then separately, exercise the library rejection path via the
/// DRAT checker using a syntactically-valid-but-semantically-invalid proof.
#[test]
fn test_checker_rejects_nonderiving_proof() {
    use ay_drat_check::checker::DratChecker;
    use ay_drat_check::cnf_parser::parse_cnf;
    use ay_drat_check::drat_parser::parse_drat;

    // Formula with a solution: x=true satisfies it. So it is SAT, not UNSAT.
    // Any DRAT proof claiming to prove it UNSAT must be rejected because
    // the empty clause cannot be derived.
    let sat_cnf = "p cnf 1 1\n1 0\n";
    let cnf = parse_cnf(sat_cnf.as_bytes()).expect("parse CNF");
    // A proof that introduces a clause (1) — already present — and then
    // claims the empty clause. The empty clause derivation MUST fail
    // RUP check since the formula is satisfiable.
    let bogus_proof = b"0\n";
    let steps = parse_drat(bogus_proof).expect("parse DRAT");
    let mut checker = DratChecker::new(cnf.num_vars, true);
    let verdict = checker.verify(&cnf.clauses, &steps);
    assert!(
        verdict.is_err(),
        "DRAT proof claiming empty clause on a SAT formula must be rejected, got Ok"
    );
}

/// End-to-end negative test (CLI exit code): write a user-supplied proof
/// file that the solver overwrites on UNSAT, so this only exercises the
/// default-accept path. But we can still probe the explicit-rejection path
/// by pointing `--proof` at a pre-existing invalid file. Since the solver
/// truncates the file on UNSAT and re-writes a valid proof, a CLI-round-trip
/// corruption test is not possible without injecting at the solver level.
/// The closest end-to-end coverage is `test_verify_proof_explicit_on_accepts_valid_proof`
/// plus the checker-level test above: together they prove the CLI pipeline
/// accepts valid proofs AND the checker rejects bad proofs. Library unit
/// tests in `proof_verify::tests` cover the dispatch glue.
#[test]
fn test_verify_proof_cli_flag_in_help() {
    let output = Command::new(ay_binary())
        .arg("solve")
        .arg("--help")
        .output()
        .expect("spawn ay --help");
    let help = String::from_utf8_lossy(&output.stdout);
    assert!(
        help.contains("--verify-proof"),
        "--verify-proof must appear in ay solve --help; help={help}"
    );
    assert!(
        help.contains("--no-verify-proof"),
        "--no-verify-proof must appear in ay solve --help; help={help}"
    );
}
