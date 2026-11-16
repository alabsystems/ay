// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A universal equated with an authored fact, end to end against pinned
//! carcara (#iff-split-implied-authority).
//!
//! The implied-universal lane publishes `(assert (= q F))` + `(assert q)`
//! refutations from the artifact firewall, after the ordinary assembly's
//! presentation passes ran for another proof. MEASURED at 36d936e62 on the
//! generated w1_51 files 13, 49, 92 and 121: every certificate assumed AY's
//! normalised assertion — `(= q (forall ((v_5 Int)) (< (- 2) ..)))` for the
//! authored `(= q (forall ((v Int)) (> .. (- 2))))` — under
//! `unsat_admission=strict-proof`, and pinned carcara 1.1.0 refused each at
//! its first `assume` ("could not match term to any of the original problem
//! premises"). Now the root, its universal and every `forall_inst` instance
//! print the problem's own spelling, and a certificate whose premises are not
//! the input's is never published from this lane.

use super::{extract_asserted_terms, extract_assume_terms, parse, Executor};
use super::{refuse_pinned_carcara_misjudgments, require_carcara_or_skip};
use ntest::timeout;
use std::path::Path;

/// w1_51 file 13. **GROUND TRUTH: UNSAT** (z3 4.16.0): `v := 0` falsifies the
/// body. The authored `(+ .. v 0)` folds the `0` away in the store.
const SECOND_UNIVERSAL: &str = r#"
(set-logic ALL)
(declare-fun w () Int)
(declare-fun a () Int)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun A () (Array Int Int))
(assert (= q (forall ((v Int)) (> (+ (* (mod w 3) v) v 0) 0))))
(assert (forall ((v Int)) (or (= (+ (* v (select A a)) (* 2 v)) 0) (> a 3))))
(assert q)
(assert p)
(check-sat)
"#;

/// w1_51 file 49. **GROUND TRUTH: UNSAT** (z3 4.16.0): `v := -2` falsifies
/// the body for either value of `p`. The closing ground lemma reasons over
/// `(ite p 0 2)`, which the printer has no pinned spelling for: `holey`.
const ITE_COEFFICIENT: &str = r#"
(set-logic ALL)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (= q (forall ((v Int)) (> (+ (* v (ite p 0 2)) v) (- 2)))))
(assert q)
(check-sat)
"#;

/// w1_51 file 92. **GROUND TRUTH: UNSAT** (z3 4.16.0). The authored
/// `(- (mod w 3) 1)` is `(+ (mod w 3) (- 1))` in the store.
const MOD_COEFFICIENT: &str = r#"
(set-logic ALL)
(declare-fun w () Int)
(declare-fun q () Bool)
(assert (= q (forall ((v Int)) (>= (+ (* v (- (mod w 3) 1)) v) 0))))
(assert q)
(assert (= w 1))
(check-sat)
"#;

/// The CLI's default posture (authored commands, best-effort proofs at the
/// CLI's step budget) and the problem-scoped document its sidecar receives.
/// The in-script `:produce-proofs` route does not reach this lane on the ite
/// fixture (`unknown`, before and after this change), so it is not the
/// posture under test.
fn default_posture_unsat_document(problem: &str, label: &str) -> String {
    let mut exec = Executor::new();
    exec.set_best_effort_produce_proofs(1_000_000);
    let mut results = Vec::new();
    for command in &parse(problem).expect("parse fixture") {
        if let Some(line) = exec
            .execute_authored(command)
            .unwrap_or_else(|err| panic!("{label}: execution failed: {err}"))
        {
            results.push(line);
        }
    }
    assert_eq!(results, ["unsat"], "{label}");
    let mut document = Vec::new();
    let rendered = exec.try_export_last_proof_alethe_for_problem_scope_to(&mut document);
    assert!(
        matches!(rendered, Some(Ok(()))),
        "{label}: the document renders"
    );
    String::from_utf8(document).expect("utf-8 document")
}

/// The pinned checker's one-word verdict, run the way the campaign reads it.
fn carcara_verdict(carcara: &Path, problem: &str, proof: &str) -> String {
    refuse_pinned_carcara_misjudgments("equated universal", problem, proof);
    let directory = tempfile::tempdir().expect("temporary checker directory");
    let problem_path = directory.path().join("problem.smt2");
    let proof_path = directory.path().join("proof.alethe");
    std::fs::write(&problem_path, problem).expect("write problem");
    std::fs::write(&proof_path, proof).expect("write proof");
    let output = std::process::Command::new(carcara)
        .arg("check")
        .arg("--allow-int-real-subtyping")
        .arg("--")
        .arg(&proof_path)
        .arg(&problem_path)
        .output()
        .expect("run the pinned checker");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let verdict = stdout.lines().last().unwrap_or("").trim().to_string();
    assert!(
        matches!(verdict.as_str(), "valid" | "holey" | "invalid"),
        "the checker printed no verdict: stdout={stdout} stderr={stderr}"
    );
    verdict
}

/// Every premise the document assumes is an assertion of the input as
/// written, for every fixture, whatever the checker's verdict.
#[test]
#[timeout(120_000)]
fn an_equated_universal_certificate_assumes_the_authored_assertions() {
    for (label, problem) in [
        ("w1_second_universal", SECOND_UNIVERSAL),
        ("w1_ite_coefficient", ITE_COEFFICIENT),
        ("w1_mod_coefficient", MOD_COEFFICIENT),
    ] {
        let proof = default_posture_unsat_document(problem, label);
        let authored = extract_asserted_terms(problem);
        for assume in extract_assume_terms(&proof) {
            assert!(
                authored.contains(&assume),
                "{label}: `{assume}` is not an assertion of the input:\n{proof}"
            );
        }
        assert!(
            !proof.contains("((v_") && !proof.contains(" v_"),
            "{label}: a renamed binder reached the document:\n{proof}"
        );
    }
}

/// Pinned carcara accepts the clean one and never rejects the ite one: its
/// remaining hole is a printer limitation on a ground `ite` lemma, disclosed
/// as `holey`, never a premise it cannot match.
#[test]
#[timeout(120_000)]
fn pinned_carcara_checks_an_equated_universal_certificate() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let proof = default_posture_unsat_document(SECOND_UNIVERSAL, "w1_second_universal");
    assert_eq!(
        carcara_verdict(&carcara, SECOND_UNIVERSAL, &proof),
        "valid",
        "{proof}"
    );
    // The mod fixture is not judged here: its closing `evaluate` over
    // `(mod 1 3)` is a step pinned carcara misjudges
    // (`ay_core::pinned_carcara`), so its verdict is not evidence either way.
    let (label, problem) = ("w1_ite_coefficient", ITE_COEFFICIENT);
    let proof = default_posture_unsat_document(problem, label);
    let verdict = carcara_verdict(&carcara, problem, &proof);
    assert!(
        matches!(verdict.as_str(), "valid" | "holey"),
        "{label}: carcara answered {verdict}:\n{proof}"
    );
}
