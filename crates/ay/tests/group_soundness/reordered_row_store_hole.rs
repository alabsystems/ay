// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--proof FILE` never loses an `unsat` to a ROW step over a store chain the
//! problem wrote in another order than the term store interns it.
//!
//! `mk_store` sorts adjacent stores at distinct constant indices, so the
//! authored `(store (store F 7 true) 5 true)` is interned as
//! `store(store(F, 5, true), 7, true)`, and the ROW1/ROW2 printer, handed the
//! problem's spelling of the chain, cannot spell `arrays_row` over it.
//! REGRESSION (measured 2026-10-31, pinned Carcara 1.1.0 git 9a352ee): each
//! problem below is `unsat` to z3 5.1.0, and `ay --proof FILE` exited 1 with
//! NO verdict on `ROW2 select surface override changes the certified array or
//! indices` (#8821). The symbolic-base problem did so on main already; the
//! two const-base problems answered `unknown` until the folded Bool read lemma
//! beside the ROW step certified. The printed clause is the certified one (the
//! same writes at distinct constant indices), so the step is the honest `hole`
//! (`ay_proof` `reordered_row_store`).

use ntest::timeout;
use std::process::Command;

use crate::alethe_dialect_disclosure::pinned_carcara_verdict_in;
use crate::spawn::OutputTimeout;
use crate::strict_certificate_publication::{verdict_lines, QUERY_TIMEOUT};

const REORDERED_STORE_CHAINS: [(&str, &str); 3] = [
    (
        "a01: a const-false chain written 7 then 5, read through an alias",
        "(set-logic QF_AUFLIA)
(declare-const c (Array Int Bool))
(declare-const x Int)
(assert (= c (store (store ((as const (Array Int Bool)) false) 7 true) 5 true)))
(assert (not (= x 5)))
(assert (not (= x 7)))
(assert (select c x))
(check-sat)
",
    ),
    (
        "b03: the same chain read directly",
        "(set-logic QF_AUFLIA)
(declare-const x Int)
(assert (not (= x 5)))
(assert (not (= x 7)))
(assert (select (store (store ((as const (Array Int Bool)) false) 7 true) 5 true) x))
(check-sat)
",
    ),
    (
        "b04: a symbolic base written 7 then 5",
        "(set-logic QF_AUFLIA)
(declare-const c (Array Int Bool))
(declare-const d (Array Int Bool))
(declare-const x Int)
(assert (= c (store (store d 7 true) 5 true)))
(assert (not (= x 5)))
(assert (not (= x 7)))
(assert (not (select d x)))
(assert (select c x))
(check-sat)
",
    ),
];

/// TWIN: a01 with its stores written in the interned order 5 then 7, which
/// the ROW printer spells with `arrays_row` and no hole.
const CANONICAL_ORDER: &str = "(set-logic QF_AUFLIA)
(declare-const c (Array Int Bool))
(declare-const x Int)
(assert (= c (store (store ((as const (Array Int Bool)) false) 5 true) 7 true)))
(assert (not (= x 5)))
(assert (not (= x 7)))
(assert (select c x))
(check-sat)
";

struct Run {
    verdicts: Vec<String>,
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
    Run {
        verdicts: verdict_lines(&String::from_utf8_lossy(&output.stdout)),
        stderr: String::from_utf8_lossy(&output.stderr).to_string(),
        problem,
        proof,
        _dir: dir,
    }
}

fn certificate_line(run: &Run, label: &str) -> String {
    run.stderr
        .lines()
        .find(|line| line.starts_with("c ay.proof.certificate "))
        .map(str::to_string)
        .unwrap_or_else(|| panic!("{label}: no certificate line\n{}", run.stderr))
}

#[test]
#[timeout(300_000)]
fn a_row_step_over_a_reordered_store_chain_is_a_counted_hole_not_a_lost_verdict() {
    for (label, script) in REORDERED_STORE_CHAINS {
        let run = run(script, &[]);
        assert_eq!(run.verdicts, ["unsat"], "{label}\n{}", run.stderr);
        let certificate = certificate_line(&run, label);
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

/// TWIN: the interned write order needs no hole, so the reorder decline is not
/// what certifies the family.
#[test]
#[timeout(300_000)]
fn the_interned_write_order_still_prints_arrays_row() {
    let run = run(CANONICAL_ORDER, &[]);
    assert_eq!(run.verdicts, ["unsat"], "{}", run.stderr);
    let document = std::fs::read_to_string(&run.proof).expect("the certificate is written");
    assert!(document.contains(":rule arrays_row"), "{document}");
    if let Some((verdict, why)) = pinned_carcara_verdict_in(&run.problem, &run.proof, &[]) {
        assert_ne!(verdict, "invalid", "{why}\n{document}");
    }
}

/// NEGATIVE CONTROL: the hole is not a certificate, so `--strict-proofs`
/// never publishes `unsat` on it.
#[test]
#[timeout(300_000)]
fn strict_proofs_still_withhold_the_verdict_on_the_reordered_store_hole() {
    for (label, script) in REORDERED_STORE_CHAINS {
        let run = run(script, &["--strict-proofs"]);
        assert_ne!(run.verdicts, ["unsat"], "{label}\n{}", run.stderr);
    }
}
