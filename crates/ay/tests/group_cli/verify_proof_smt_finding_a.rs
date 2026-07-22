// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for synthesized proof configuration in SMT-LIB mode.
//!
//! Debug builds default `VERIFY_PROOF_ENABLED` to `true`, which caused
//! `build_proof_config` to synthesize a temporary `ay-verify-<pid>.drat`
//! config. The SMT-LIB execution paths in `run.rs` then rejected that
//! config because SMT-LIB solving produces Alethe proofs, not DRAT —
//! every raw SMT invocation under `cargo test` exited with code 1 and
//! the error "SMT-LIB mode requires Alethe output".
//!
//! The fix drops verify-only temporary configs on the SMT-LIB route: AY's
//! built-in post-checker supports DIMACS DRAT/LRAT, not Alethe, so writing and
//! deleting an unchecked temporary Alethe file only spent memory while giving
//! a false impression that verification occurred.
//!
//! Implicit default verification therefore leaves ordinary SMT solving usable,
//! while an explicit `--verify-proof` request fails closed with a qualified
//! error instead of silently skipping the requested check.

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

fn write_temp_smt(contents: &str) -> (PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_verify_proof_smt_finding_a_{}_{}.smt2",
        std::process::id(),
        id
    ));
    std::fs::write(&path, contents).expect("write temp smt2");
    (path.clone(), CleanupGuard(path))
}

/// Smallest QF_LIA SAT instance that exercises the standard DPLL(T) path.
const TRIVIAL_SAT_SMT: &str =
    "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (= x 0))\n(check-sat)\n";

/// Smallest QF_LIA UNSAT instance — exercises the Alethe proof write path
/// under synthesized `--verify-proof`. Pre-fix, the solver rejected the
/// synthesized DRAT config before even starting the solve.
const TRIVIAL_UNSAT_SMT: &str =
    "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (= x 0))\n(assert (= x 1))\n(check-sat)\n";

/// QF_UF sample exercising problem-scoped declarations and preservation of
/// `(distinct a c)` in Alethe replay.
const QF_UF_UNSAT_TRANSITIVITY: &str = r#"
(set-info :status unsat)
(set-logic QF_UF)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(assert (= a b))
(assert (= b c))
(assert (distinct a c))
(check-sat)
(exit)
"#;

fn ay_binary() -> &'static str {
    env!("CARGO_BIN_EXE_ay")
}

/// Baseline: running ay on SMT with defaults must not error out with
/// "SMT-LIB mode requires Alethe". Under debug builds this is the
/// regressing path — `VERIFY_PROOF_ENABLED` is true and the synthesizer
/// produces a DRAT config.
#[test]
#[timeout(60_000)]
fn test_smt_default_verify_proof_debug_does_not_reject() {
    let (input, _c) = write_temp_smt(TRIVIAL_SAT_SMT);

    let output = Command::new(ay_binary())
        .arg(&input)
        .output()
        .expect("spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        !stderr.contains("SMT-LIB mode requires Alethe"),
        "SMT default run must not reject synthesized proof config; stderr={stderr}"
    );
    assert!(
        stdout.contains("sat"),
        "expected sat output; stdout={stdout}; stderr={stderr}"
    );
    // Successful SMT solve exits 0 (or 10 for SAT in DIMACS convention, but
    // the SMT path emits sat/unsat text and exits 0).
    assert_eq!(
        output.status.code(),
        Some(0),
        "expected exit 0 on trivial SAT; stdout={stdout}; stderr={stderr}"
    );
}

/// Explicit `--verify-proof` on SMT input must fail closed: the built-in
/// checker cannot verify Alethe.
#[test]
#[timeout(60_000)]
fn test_smt_explicit_verify_proof_rejects_sat_before_solving() {
    let (input, _c) = write_temp_smt(TRIVIAL_SAT_SMT);

    let output = Command::new(ay_binary())
        .arg("--verify-proof")
        .arg(&input)
        .output()
        .expect("spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stdout.trim().is_empty(),
        "must not emit a verdict; stdout={stdout}"
    );
    assert!(
        stderr.contains("--verify-proof cannot verify SMT-LIB Alethe certificates"),
        "missing qualified Alethe rejection; stderr={stderr}"
    );
    assert_eq!(
        output.status.code(),
        Some(1),
        "explicit unsupported verification must exit 1; stdout={stdout}; stderr={stderr}"
    );
}

/// Rejection is independent of the latent solver result: an UNSAT instance is
/// also refused before its unchecked verdict or certificate can be emitted.
#[test]
#[timeout(60_000)]
fn test_smt_explicit_verify_proof_rejects_unsat_before_solving() {
    let (input, _c) = write_temp_smt(TRIVIAL_UNSAT_SMT);

    let output = Command::new(ay_binary())
        .arg("--verify-proof")
        .arg(&input)
        .output()
        .expect("spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stdout.trim().is_empty(),
        "must not emit a verdict; stdout={stdout}"
    );
    assert!(
        stderr.contains("--verify-proof cannot verify SMT-LIB Alethe certificates"),
        "missing qualified Alethe rejection; stderr={stderr}"
    );
    assert_eq!(
        output.status.code(),
        Some(1),
        "explicit unsupported verification must exit 1; stdout={stdout}; stderr={stderr}"
    );
}

/// Explicit SMT Alethe proof files are replayed by external checkers together
/// with the original SMT-LIB problem file. Problem declarations therefore
/// belong only in the problem file, and proof assumptions must keep surface
/// syntax that Carcara can match against the original assertions.
#[test]
#[timeout(60_000)]
fn test_smt_explicit_alethe_proof_is_problem_scoped_for_external_replay() {
    let (input, _input_guard) = write_temp_smt(QF_UF_UNSAT_TRANSITIVITY);
    let proof_path = std::env::temp_dir().join(format!(
        "ay_verify_proof_smt_problem_scoped_{}.alethe",
        std::process::id()
    ));
    let _proof_guard = CleanupGuard(proof_path.clone());

    let output = Command::new(ay_binary())
        .arg("solve")
        .arg("--proof")
        .arg(&proof_path)
        .arg(&input)
        .output()
        .expect("spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "expected exit 0 on SMT UNSAT proof emission; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        stdout.contains("unsat"),
        "expected unsat output; stdout={stdout}; stderr={stderr}"
    );

    let proof = std::fs::read_to_string(&proof_path)
        .unwrap_or_else(|error| panic!("failed to read proof {}: {error}", proof_path.display()));
    assert!(
        !proof.contains("(declare-fun"),
        "problem symbols must be declared only in the SMT-LIB problem file:\n{proof}"
    );
    assert!(
        !proof.contains("(declare-sort"),
        "problem sorts must be declared only in the SMT-LIB problem file:\n{proof}"
    );
    assert!(
        proof
            .lines()
            .next()
            .is_some_and(|line| line.starts_with("(assume ")),
        "proof should start with proof commands, got:\n{proof}"
    );
    assert!(
        proof.contains("(distinct a c)"),
        "proof assumptions must preserve original distinct syntax for Carcara matching:\n{proof}"
    );
}

/// Explicit `--proof foo.drat` on SMT input — user misconfiguration, not a
/// CLI default glitch — MUST still surface the "SMT-LIB mode requires
/// Alethe" error. We only silently rewrite *synthesized* (temp) configs.
#[test]
#[timeout(60_000)]
fn test_smt_explicit_drat_proof_still_rejected() {
    let (input, _c) = write_temp_smt(TRIVIAL_SAT_SMT);
    let proof_path = std::env::temp_dir().join(format!(
        "ay_verify_proof_smt_finding_a_explicit_{}.drat",
        std::process::id()
    ));
    let _guard = CleanupGuard(proof_path.clone());

    let output = Command::new(ay_binary())
        .arg("--proof")
        .arg(&proof_path)
        .arg(&input)
        .output()
        .expect("spawn ay");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("SMT-LIB mode requires Alethe"),
        "explicit --proof foo.drat on SMT must still error clearly; stderr={stderr}"
    );
    assert_eq!(
        output.status.code(),
        Some(1),
        "explicit DRAT on SMT must exit 1; stderr={stderr}"
    );
}
