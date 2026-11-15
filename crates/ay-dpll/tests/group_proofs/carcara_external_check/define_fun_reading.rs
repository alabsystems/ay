// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pinned carcara cannot unfold a PARAMETERIZED problem `define-fun`, so a
//! checked step that needs one unfolded stays a disclosed `hole`.
//!
//! The gates run pinned carcara 1.1.0 (git 9a352ee) in its default reading of
//! a problem `define-fun`: a declared `f` plus the premise
//! `(= f (lambda ((x S)) body))` (`parser/mod.rs` `parse_problem`). From that
//! premise `ho_cong` derives `(= (f a) ((lambda ((x S)) body) a))`, and no rule
//! reduces the application to `body[a/x]`. The rule table (`checker/shared.rs`
//! `get_rule`) has no beta rule. `evaluate` leaves an application unevaluated
//! (`ast/evaluate.rs`), and `refl` compares it structurally. `rare_rewrite`
//! needs a `--rare-file`, which is an allowance, and `lia_generic` is a hole.
//! The `--apply-function-defs` reading expands the macro instead, but it drops
//! the premise `(= a body)` that the nullary bridge assumes (`closed_guard.rs`,
//! LIMITATIONS.md), so the gates do not use it.
//!
//! So `model_checker_consumer_quantified_artifact_total_function_unsat` and
//! `model_checker_consumer_quantified_counterexample_total_default_unsat` stay listed holey
//! (`corpus_rows.rs`). Each problem is SATISFIABLE with its `define-fun` read as
//! a `declare-fun` (z3), so every refutation needs the unfolding. The first
//! test pins the missing rule against the real checker: if the checker gains
//! it, the test fails and the rows get re-measured. The second test shrinks
//! the two shapes and pins that AY discloses the unfolding as exactly one
//! `hole`, and never prints a step that default carcara refuses.

use super::{
    carcara_verdict_without_allowances, require_carcara_or_skip, solve_unsat_and_get_proof,
    CarcaraVerdict,
};
use ntest::timeout;
use std::path::Path;

/// A problem whose one parameterized definition carcara must unfold.
const CONSTANT_FUNCTION: &str = "(set-logic QF_BV)\n\
    (define-fun f ((x (_ BitVec 2))) (_ BitVec 2) (_ bv1 2))\n\
    (assert (= (f #b00) #b00))\n\
    (check-sat)\n";

/// The `model_checker_consumer_quantified_artifact_total_function` shape: the refuting
/// instance is the Skolem `choice` witness, which the constant body drops.
const TOTAL_FUNCTION: &str = "(set-logic BV)\n\
    (define-fun f ((x (_ BitVec 3))) (_ BitVec 3) #b101)\n\
    (assert (forall ((i (_ BitVec 3))) (= (f i) #b000)))\n\
    (check-sat)\n";

/// The `model_checker_consumer_quantified_counterexample_total_default` shape, at 16 bits:
/// the instance at the boundary index is false only once `summary` is
/// unfolded, inside a four-literal theory lemma.
const TOTAL_DEFAULT: &str = "(set-logic ALL)\n\
    (define-fun summary ((x (_ BitVec 16))) (_ BitVec 1) (ite (bvult x #x0040) #b1 #b0))\n\
    (declare-const local (_ BitVec 16))\n\
    (assert (= local #x0007))\n\
    (assert (= (summary local) #b1))\n\
    (assert (forall ((i (_ BitVec 16))) (=> (bvult i #x0041) (= (summary i) #b1))))\n\
    (check-sat)\n";

/// Pinned carcara in the corpus runner's invocation: `(exit ok, stdout,
/// stderr)`, with no gate policy applied.
fn gate_invocation_output(carcara: &Path, problem: &str, proof: &str) -> (bool, String, String) {
    let directory = tempfile::tempdir().expect("temporary Carcara directory");
    let problem_path = directory.path().join("problem.smt2");
    let proof_path = directory.path().join("proof.alethe");
    std::fs::write(&problem_path, problem).expect("write problem");
    std::fs::write(&proof_path, proof).expect("write proof");
    let output = std::process::Command::new(carcara)
        .args(["check", "--no-color", "--expand-let-bindings", "--"])
        .arg(&proof_path)
        .arg(&problem_path)
        .output()
        .expect("run carcara check");
    (
        output.status.success(),
        String::from_utf8_lossy(&output.stdout).trim().to_string(),
        String::from_utf8_lossy(&output.stderr).trim().to_string(),
    )
}

#[test]
#[timeout(60_000)]
fn pinned_carcara_has_no_rule_that_unfolds_a_parameterized_define_fun() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let application = "((lambda ((x (_ BitVec 2))) (_ bv1 2)) #b00)";
    let refused = [
        (
            format!("(step t1 (cl (= {application} #b01)) :rule beta)\n"),
            "with rule 'beta': unknown rule",
        ),
        (
            format!("(step t1 (cl (= {application} #b01)) :rule evaluate)\n"),
            "with rule 'evaluate': expected terms to be equal",
        ),
        (
            format!("(step t1 (cl (= {application} #b01)) :rule refl)\n"),
            "with rule 'refl': reflexivity failed",
        ),
        (
            format!("(step t1 (cl (= {application} #b01)) :rule rare_rewrite)\n"),
            "with rule 'rare_rewrite': expected a rare rule",
        ),
        // What a printer lowering over the authored application would emit.
        (
            "(step t1 (cl (= (= (f #b00) #b01) true)) :rule evaluate)\n".to_string(),
            "with rule 'evaluate': expected terms to be equal",
        ),
        (
            "(step t1 (cl (= (f #b00) #b01)) :rule refl)\n".to_string(),
            "with rule 'refl': reflexivity failed",
        ),
    ];
    for (proof, diagnostic) in refused {
        let (ok, stdout, stderr) = gate_invocation_output(&carcara, CONSTANT_FUNCTION, &proof);
        assert!(
            !ok && stdout == "invalid" && stderr.contains(diagnostic),
            "pinned carcara no longer refuses this unfolding step as measured; if it can now \
             unfold a define-fun, re-measure the define-fun rows in \
             ORACLE_UNSAT_HOLEY_PROOF_ROWS:\n{proof}\nstdout={stdout}\nstderr={stderr}"
        );
    }
    // What the default reading does hold: the premise `(= f (lambda ..))`,
    // and through `ho_cong` only the unreduced application. The document is
    // `holey` because of its closing `hole` alone, so both steps before it
    // are accepted.
    let holds = format!(
        "(assume a0 (= f (lambda ((x (_ BitVec 2))) (_ bv1 2))))\n\
         (step t1 (cl (= #b00 #b00)) :rule refl)\n\
         (step t2 (cl (= (f #b00) {application})) :rule ho_cong :premises (a0 t1))\n\
         (step t3 (cl) :rule hole)\n"
    );
    assert_eq!(
        carcara_verdict_without_allowances(
            &carcara,
            "define_fun_reading",
            CONSTANT_FUNCTION,
            &holds
        ),
        CarcaraVerdict::Holey,
        "default carcara must hold the lambda premise and its ho_cong application"
    );
}

#[test]
#[timeout(60_000)]
fn a_step_that_needs_a_define_fun_unfolded_stays_one_disclosed_hole() {
    for (label, problem, unfolded) in [
        ("define_fun_total_function", TOTAL_FUNCTION, "(f (choice"),
        (
            "define_fun_total_default",
            TOTAL_DEFAULT,
            "(summary #b0000000001000000)",
        ),
    ] {
        let proof = solve_unsat_and_get_proof(problem, label);
        let holes: Vec<&str> = proof.lines().filter(|l| l.contains(":rule hole")).collect();
        assert!(
            holes.len() == 1 && holes[0].contains(unfolded) && !proof.contains(":rule trust"),
            "{label}: the unfolding must be the one disclosed hole:\n{proof}"
        );
        let Some(carcara) = require_carcara_or_skip() else {
            continue;
        };
        assert_eq!(
            carcara_verdict_without_allowances(&carcara, label, problem, &proof),
            CarcaraVerdict::Holey,
            "{label}: a hole, never a step default carcara refuses"
        );
    }
}
