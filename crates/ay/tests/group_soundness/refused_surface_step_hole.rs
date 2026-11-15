// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--proof FILE` never loses an `unsat` to a surface step the printer cannot
//! spell: the step is the honest `hole` over its own clause, the certificate
//! line counts it, and `--strict-proofs` still withholds the verdict.
//!
//! REGRESSION (measured 2026-10-02 on main 8eb4d6baba and on the
//! negative-literal branch, pinned Carcara 1.1.0 git 9a352ee): each problem
//! below is `unsat` to z3 5.1.0, and `ay --proof FILE` exited 1 with NO
//! verdict — `refusing to write unverifiable proof (#8821): invalid surface
//! congruence step` / `invalid surface proof step` — because the authored
//! spelling (`(div -7 2)` beside its value, `(f x -2)` beside `(f -1 -2)`, the
//! chained `(< -5 x -3)`) left a checked internal step with no certified
//! external bridge. The derivation exists; only its spelling is missing.

use ntest::timeout;
use std::process::Command;

use crate::alethe_dialect_disclosure::pinned_carcara_verdict_in;
use crate::spawn::OutputTimeout;
use crate::strict_certificate_publication::{verdict_lines, QUERY_TIMEOUT};

const REFUSED_SURFACE_STEPS: [(&str, &str); 4] = [
    (
        "d14: (div -7 2) beside its value",
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (= x (div -7 2)))
(assert (> x -4))
(check-sat)
",
    ),
    (
        "d12: eq_congruent over (f x -2) and (f -1 -2)",
        "(set-logic QF_UFLIA)
(declare-fun f (Int Int) Int)
(declare-const x Int)
(assert (= x -1))
(assert (not (= (f x -2) (f -1 -2))))
(check-sat)
",
    ),
    (
        "b05: (* -2 y) beside its canonical product",
        "(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= x (* -2 y)))
(assert (= y 1))
(assert (> x 0))
(check-sat)
",
    ),
    (
        "g09: the chained comparison (< -5 x -3)",
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (< -5 x -3))
(assert (not (= x -4)))
(check-sat)
",
    ),
];

struct Run {
    verdicts: Vec<String>,
    certificate: Option<String>,
    stderr: String,
    problem: std::path::PathBuf,
    proof: std::path::PathBuf,
    _dir: tempfile::TempDir,
}

fn run(script: &str, flags: &[&str]) -> Run {
    let dir = tempfile::tempdir().expect("tempdir");
    let problem = dir.path().join("query.smt2");
    let proof = dir.path().join("query.alethe");
    std::fs::write(&problem, script).expect("write query");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg(&problem)
        .args(flags)
        .arg("--proof")
        .arg(&proof)
        .output_timeout(QUERY_TIMEOUT)
        .expect("ay answers");
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    Run {
        verdicts: verdict_lines(&String::from_utf8_lossy(&output.stdout)),
        certificate: stderr
            .lines()
            .find(|line| line.starts_with("c ay.proof.certificate "))
            .map(str::to_string),
        stderr,
        problem,
        proof,
        _dir: dir,
    }
}

#[test]
#[timeout(300_000)]
fn a_refused_surface_step_is_a_counted_hole_not_a_lost_verdict() {
    for (label, script) in REFUSED_SURFACE_STEPS {
        let run = run(script, &[]);
        assert_eq!(run.verdicts, ["unsat"], "{label}\n{}", run.stderr);
        let certificate = run
            .certificate
            .clone()
            .unwrap_or_else(|| panic!("{label}: no certificate line\n{}", run.stderr));
        let document = std::fs::read_to_string(&run.proof).expect("the certificate is written");
        assert!(document.contains(":rule hole"), "{label}: {document}");
        assert!(
            !certificate.contains(" unproved_steps=0 ") && certificate.contains(" trust_free=no "),
            "{label}: {certificate}"
        );
        if let Some((verdict, why)) = pinned_carcara_verdict_in(&run.problem, &run.proof, &[]) {
            assert_eq!(verdict, "holey", "{label}: {why}\n{document}");
        }
    }
}

/// NEGATIVE CONTROL: the hole is not a certificate, so `--strict-proofs`
/// never publishes `unsat` on it.
#[test]
#[timeout(300_000)]
fn strict_proofs_still_withhold_the_verdict_on_the_hole() {
    for (label, script) in REFUSED_SURFACE_STEPS {
        let run = run(script, &["--strict-proofs"]);
        assert_ne!(run.verdicts, ["unsat"], "{label}\n{}", run.stderr);
    }
}
