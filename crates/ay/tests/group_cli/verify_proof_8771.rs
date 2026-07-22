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

/// `--strict-proofs` and `--self-check` are route-independent result promises.
/// On DIMACS they therefore require AY to emit, descriptor-seal, and re-check
/// a same-run DRAT/LRAT refutation before publishing UNSAT. Explicit proof or
/// checker opt-outs are incompatible and must fail before any verdict.
#[test]
fn test_dimacs_required_proof_gates_reject_proof_opt_outs_before_verdict() {
    for gate in ["--strict-proofs", "--self-check"] {
        let (cnf, proof, _guard) = temp_paths(&format!(
            "{}_opt_out",
            gate.trim_start_matches("--").replace('-', "_")
        ));

        let no_proof = Command::new(ay_binary())
            .arg(gate)
            .arg("--no-proof")
            .arg(&cnf)
            .output()
            .expect("spawn ay --no-proof gate regression");
        let stdout = String::from_utf8_lossy(&no_proof.stdout);
        let stderr = String::from_utf8_lossy(&no_proof.stderr);
        assert_eq!(
            no_proof.status.code(),
            Some(1),
            "{gate} --no-proof must fail closed; stdout={stdout}; stderr={stderr}"
        );
        assert!(
            !stdout.contains("SATISFIABLE") && !stdout.contains("UNKNOWN"),
            "{gate} --no-proof leaked a DIMACS verdict: {stdout}"
        );
        assert!(
            stderr.contains("requires a same-run DIMACS refutation"),
            "{gate} --no-proof diagnostic did not explain the contract: {stderr}"
        );

        let no_verify = Command::new(ay_binary())
            .arg(gate)
            .arg("--no-verify-proof")
            .arg("--proof")
            .arg(&proof)
            .arg(&cnf)
            .output()
            .expect("spawn ay --no-verify-proof gate regression");
        let stdout = String::from_utf8_lossy(&no_verify.stdout);
        let stderr = String::from_utf8_lossy(&no_verify.stderr);
        assert_eq!(
            no_verify.status.code(),
            Some(1),
            "{gate} --no-verify-proof must fail closed; stdout={stdout}; stderr={stderr}"
        );
        assert!(
            !stdout.contains("SATISFIABLE") && !stdout.contains("UNKNOWN"),
            "{gate} --no-verify-proof leaked a DIMACS verdict: {stdout}"
        );
        assert!(
            stderr.contains("requires authenticated DIMACS proof re-checking"),
            "{gate} --no-verify-proof diagnostic did not explain the contract: {stderr}"
        );
        assert!(
            !proof.exists(),
            "incompatible {gate} route should be rejected before creating a proof"
        );
    }
}

#[test]
fn test_dimacs_required_proof_gates_emit_and_recheck_same_run_proof() {
    for gate in ["--strict-proofs", "--self-check"] {
        let (cnf, proof, _guard) = temp_paths(&format!(
            "{}_checked",
            gate.trim_start_matches("--").replace('-', "_")
        ));
        let output = Command::new(ay_binary())
            .arg(gate)
            .arg("--proof")
            .arg(&proof)
            .arg(&cnf)
            .output()
            .expect("spawn ay required DIMACS proof gate");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(20),
            "{gate} should accept a verified same-run proof; stdout={stdout}; stderr={stderr}"
        );
        assert!(
            stdout.contains("s UNSATISFIABLE"),
            "{gate} did not publish checked UNSAT: {stdout}"
        );
        assert!(
            stderr.contains("verify-proof:") && stderr.contains("verified"),
            "{gate} did not run the independent proof checker: {stderr}"
        );
        assert!(proof.exists(), "{gate} did not emit its required proof");
    }
}

/// Soundness test for the checker itself: a proof that claims the empty
/// clause for a satisfiable formula must be rejected.
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

/// An explicitly required checker is an authority gate, so a proof format the
/// internal DIMACS checker cannot verify must fail before any public UNSAT
/// surface is emitted. The rejected same-run proof publication is retired
/// (descriptor-invalidated), and neither result statistics nor a
/// proof-artifact envelope may claim that the run was authorized.
#[test]
fn test_required_verification_precedes_unsat_stats_and_artifact() {
    let (cnf, drat, mut guard) = temp_paths("authority_order");
    let proof = drat.with_extension("alethe");
    let artifact = drat.with_extension("proof-artifact.json");
    guard.0.push(proof.clone());
    guard.0.push(artifact.clone());

    let output = Command::new(ay_binary())
        .arg("--verify-proof")
        .arg("--stats-json")
        .arg("--proof")
        .arg(&proof)
        .arg("--proof-artifact")
        .arg(&artifact)
        .arg(&cnf)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert_eq!(
        output.status.code(),
        Some(1),
        "unsupported mandatory verification must fail; stdout={stdout}; stderr={stderr}"
    );
    // The failed authority gate retires the rejected same-run publication
    // (descriptor-invalidated and quarantined), so no proof file may remain
    // at the public path to be mistaken for an authorized artifact.
    assert!(
        !proof.exists(),
        "failed authority gate must retire the rejected proof publication"
    );
    assert!(
        !stdout.contains("s UNSATISFIABLE"),
        "failed authority gate leaked an UNSAT verdict: {stdout}"
    );
    assert!(
        !stderr.lines().any(|line| {
            serde_json::from_str::<serde_json::Value>(line)
                .ok()
                .and_then(|value| value.get("result").cloned())
                .is_some_and(|result| result == "unsat")
        }),
        "failed authority gate leaked UNSAT statistics: {stderr}"
    );
    assert!(
        !artifact.exists(),
        "failed authority gate published a proof artifact"
    );
}

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
