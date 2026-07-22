// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Producer-side tests for the linear-conjunction fold-to-false rebuild
//! (`rebuild_linear_and_collapse` in `proof_trust_surgery.rs`).
//!
//! The QF_LIA CAV_2009 family asserts ONE `let`-bound conjunction of linear
//! `<=` atoms; when the preprocessor folds the conjunction to `false` (e.g.
//! a conjunct whose linear form cancels to `0 <= -1`), the exported proof
//! used to degenerate to the misused `:rule false` collapse external
//! checkers reject. The rebuild re-proves `(cl)` from the ORIGINAL
//! conjunction: `and_pos` extraction of exactly the participating conjuncts
//! (identified by LRA Farkas synthesis, independently re-verified at
//! external `la_generic` strength) + one certified `la_generic` lemma +
//! resolutions.

use ay_dpll::Executor;
use ay_frontend::parse;
use ay_proof::{check_proof_strict, ProofQuality};
use ntest::timeout;

/// Solve an UNSAT script with proofs enabled; return the executor and the
/// rendered Alethe text.
fn solve_unsat(script: &str) -> (Executor, String) {
    let commands = parse(script).expect("parse SMT-LIB script");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute SMT-LIB script");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "expected UNSAT, got {outputs:?}"
    );
    let alethe = outputs.last().cloned().unwrap_or_default();
    (exec, alethe)
}

fn strict_quality(exec: &Executor) -> ProofQuality {
    let proof = exec.last_proof().expect("last proof after UNSAT");
    check_proof_strict(proof, exec.terms())
        .expect("strict checker rejected the rebuilt proof (trust/hole or invalid step)")
}

/// The CAV09 shape in miniature: a `let`-bound conjunction whose FIRST
/// conjunct cancels to `0 <= -1` (`x0 - x0 <= -1`). The preprocessor folds
/// the whole assertion to `false`; the rebuilt proof must extract exactly
/// that conjunct (`and_pos` index 0), refute it with a certified
/// `la_generic` lemma, and close by resolution — with no misused `false`
/// rule and no trust.
#[test]
#[timeout(10_000)]
fn test_let_conjunction_cancelling_conjunct_rebuilds_strict() {
    let script = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-fun x0 () Int)
        (declare-fun x1 () Int)
        (assert (let ((?v_0 (* 1 x0)) (?v_1 (* (- 1) x0)))
          (and (<= (+ ?v_0 ?v_1) (- 1)) (<= (+ (* 1 x1) (* 0 x0)) 0))))
        (check-sat)
        (get-proof)
    "#;
    let (exec, alethe) = solve_unsat(script);
    let quality = strict_quality(&exec);
    assert_eq!(quality.trust_count, 0, "no trust steps: {quality}");
    assert_eq!(quality.hole_count, 0, "no hole steps: {quality}");
    assert!(
        quality.theory_lemma_count >= 1,
        "expected a certified Farkas lemma: {quality}"
    );
    assert!(
        !alethe.contains(":rule false"),
        "the misused `false` collapse must be rebuilt:\n{alethe}"
    );
    assert!(
        !alethe.contains(":rule trust"),
        "printed Alethe must be trust-free:\n{alethe}"
    );
    assert!(
        alethe.contains(":rule and_pos"),
        "expected conjunct extraction via and_pos:\n{alethe}"
    );
    assert!(
        alethe.contains(":rule la_generic"),
        "expected a certified la_generic refutation:\n{alethe}"
    );
    // Scale discipline: only the PARTICIPATING conjunct is extracted — the
    // irrelevant `x1` conjunct must not appear as an and_pos step.
    assert_eq!(
        alethe.matches(":rule and_pos").count(),
        1,
        "exactly one participating conjunct:\n{alethe}"
    );
}

/// Same class without `let` sugar: the direct conjunction still rebuilds.
#[test]
#[timeout(10_000)]
fn test_plain_conjunction_cancelling_conjunct_rebuilds_strict() {
    let script = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-fun x0 () Int)
        (declare-fun x1 () Int)
        (assert (and (<= (+ (* 1 x0) (* (- 1) x0)) (- 1)) (<= (+ (* 1 x1) (* 0 x0)) 0)))
        (check-sat)
        (get-proof)
    "#;
    let (exec, alethe) = solve_unsat(script);
    let quality = strict_quality(&exec);
    assert_eq!(quality.trust_count, 0, "no trust steps: {quality}");
    assert_eq!(quality.hole_count, 0, "no hole steps: {quality}");
    assert!(
        !alethe.contains(":rule false"),
        "the misused `false` collapse must be rebuilt:\n{alethe}"
    );
    assert!(
        alethe.contains(":rule la_generic"),
        "expected a certified la_generic refutation:\n{alethe}"
    );
}
