// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for #6759: combined deferred-postprocessing routes must
//! preserve original proof premises instead of exporting temporary preprocessing
//! artifacts as problem assumptions.

use ay_core::{AletheRule, Proof, ProofStep};
use ay_dpll::Executor;
use ay_frontend::parse;
use ay_proof::{check_proof, check_proof_with_quality, ProofQuality};
use ntest::timeout;

fn describe_proof_steps(exec: &Executor, proof: &Proof) -> Vec<String> {
    proof
        .steps
        .iter()
        .enumerate()
        .map(|(idx, step)| match step {
            ProofStep::Assume(term) => {
                format!("t{idx}: assume {term:?} {:?}", exec.terms().get(*term))
            }
            ProofStep::TheoryLemma { clause, kind, .. } => {
                let rendered: Vec<_> = clause
                    .iter()
                    .map(|term| format!("{:?}", exec.terms().get(*term)))
                    .collect();
                format!(
                    "t{idx}: theory {:?} len={} {rendered:?}",
                    kind,
                    clause.len()
                )
            }
            ProofStep::Step {
                rule,
                clause,
                premises,
                ..
            } => {
                let trust = matches!(rule, AletheRule::Trust);
                let rendered: Vec<_> = clause
                    .iter()
                    .map(|term| format!("{:?}", exec.terms().get(*term)))
                    .collect();
                format!(
                    "t{idx}: step {:?} len={} premises={} trust={} {rendered:?}",
                    rule,
                    clause.len(),
                    premises.len(),
                    trust
                )
            }
            ProofStep::Resolution { clause, .. } => {
                format!("t{idx}: resolution len={}", clause.len())
            }
            ProofStep::Anchor { .. } => format!("t{idx}: anchor"),
            other => format!("t{idx}: other {other:?}"),
        })
        .collect()
}

fn run_unsat_proof(input: &str) -> (String, ProofQuality, Vec<String>) {
    let commands = parse(input).expect("proof-enabled SMT-LIB script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("proof-enabled SMT-LIB script should execute");

    assert_eq!(outputs.len(), 2, "expected check-sat + get-proof output");
    assert_eq!(outputs[0].trim(), "unsat", "expected UNSAT result");

    let proof_text = outputs[1].clone();
    let proof = exec
        .last_proof()
        .expect("expected get-proof to populate the last proof object");
    check_proof(proof, exec.terms()).expect("internal proof checker rejected proof");
    let quality = check_proof_with_quality(proof, exec.terms())
        .expect("proof quality checker rejected proof");
    let steps = describe_proof_steps(&exec, proof);
    (proof_text, quality, steps)
}

fn assert_no_aux_mod_div_assumptions(proof_text: &str) {
    for line in proof_text.lines() {
        if !line.contains("(assume ") {
            continue;
        }
        assert!(
            !line.contains("_mod_q")
                && !line.contains("_mod_r")
                && !line.contains("_div_q")
                && !line.contains("_div_r"),
            "temporary mod/div auxiliary term leaked into proof assumption: {line}\n{proof_text}"
        );
    }
}

#[test]
#[timeout(5_000)]
fn test_lira_push_pop_mod_premises_export_original_assertions_6759() {
    let input = r#"
        (set-logic QF_LIRA)
        (set-option :produce-proofs true)
        (declare-const x Int)
        (declare-const y Real)
        (push 1)
        (assert (= y (to_real x)))
        (assert (= (mod x 2) 0))
        (assert (= (mod x 2) 1))
        (check-sat)
        (get-proof)
    "#;

    let (proof_text, quality, steps) = run_unsat_proof(input);

    // The mod/div auxiliary identity (e.g. x = div_q * 2 + mod_r) is a
    // derived constraint that is correctly demoted to trust by the narrowed
    // provenance-aware whitelist (#6759). `ProofQuality` also counts the
    // exported Generic theory lemma as trust (#5657). Only original user
    // assertions should survive as `assume` steps.
    assert!(
        quality.trust_count <= 2,
        "push/pop LIRA proof should only trust-demote the mod/div identity and Generic theory lemma: {quality:?}\nsteps={steps:?}\n{proof_text}"
    );
    assert_eq!(
        quality.hole_count, 0,
        "push/pop LIRA proof should not contain holes: {quality:?}\nsteps={steps:?}\n{proof_text}"
    );
    assert!(
        proof_text.contains("(mod x 2)"),
        "push/pop LIRA proof should retain original mod syntax:\n{proof_text}"
    );
    assert_no_aux_mod_div_assumptions(&proof_text);
}

#[test]
#[timeout(5_000)]
fn test_lira_check_sat_assuming_mod_premises_export_original_assertions_6759() {
    let input = r#"
        (set-logic QF_LIRA)
        (set-option :produce-proofs true)
        (declare-const x Int)
        (declare-const y Real)
        (assert (= y (to_real x)))
        (assert (= (mod x 2) 0))
        (check-sat-assuming ((= (mod x 2) 1)))
        (get-proof)
    "#;

    let (proof_text, quality, steps) = run_unsat_proof(input);

    // The narrowed provenance whitelist correctly preserves the original base
    // assertion and assumption as `assume` steps while trust-demoting the
    // derived Euclidean-division identity used by the mixed arithmetic lemma.
    // `ProofQuality` also counts the exported Generic theory lemma as trust
    // (#5657).
    assert!(
        quality.trust_count <= 2,
        "LIRA check-sat-assuming proof should only trust-demote the mod/div identity and Generic theory lemma, not rewritten user premises: {quality:?}\nsteps={steps:?}\n{proof_text}"
    );
    assert_eq!(
        quality.hole_count, 0,
        "LIRA check-sat-assuming proof should not contain holes: {quality:?}\nsteps={steps:?}\n{proof_text}"
    );
    assert!(
        proof_text.contains("(= (mod x 2) 0)"),
        "combined check-sat-assuming proof should keep the base mod assertion visible:\n{proof_text}"
    );
    assert!(
        proof_text.contains("(= (mod x 2) 1)"),
        "combined check-sat-assuming proof should keep the assumption-side mod assertion visible:\n{proof_text}"
    );
    assert_no_aux_mod_div_assumptions(&proof_text);
}
