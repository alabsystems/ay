// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_check_proof_with_quality_theory_lemma_verified() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    // Use LraFarkas — a verified theory lemma kind (exports as la_generic, not trust)
    let tl = proof.add_theory_lemma_with_farkas_and_kind(
        "LRA",
        vec![not_x],
        FarkasAnnotation::from_ints(&[1]),
        TheoryLemmaKind::LraFarkas,
    );
    proof.add_rule_step(AletheRule::ThResolution, vec![], vec![h0, tl], vec![]);

    let quality =
        check_proof_with_quality(&proof, &terms).expect("th_resolution proof should pass");

    assert_eq!(quality.total_steps, 3);
    assert_eq!(quality.assume_count, 1);
    assert_eq!(quality.theory_lemma_count, 1);
    assert_eq!(quality.trust_count, 0);
    assert_eq!(quality.th_resolution_count, 1);
    assert!(quality.is_complete());
}

#[test]
fn test_check_proof_with_quality_theory_lemma_trust_kind() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    // Generic theory lemma exports as trust — should be counted (#5657)
    let tl = proof.add_theory_lemma("BV", vec![not_x]);
    proof.add_rule_step(AletheRule::ThResolution, vec![], vec![h0, tl], vec![]);

    let quality =
        check_proof_with_quality(&proof, &terms).expect("th_resolution proof should pass");

    assert_eq!(quality.total_steps, 3);
    assert_eq!(quality.theory_lemma_count, 1);
    assert_eq!(
        quality.trust_count, 1,
        "Generic theory lemma should count as trust (#5657)"
    );
    assert!(
        !quality.is_complete(),
        "proof with trust-exported theory lemma is not complete"
    );
}

#[test]
fn test_has_trust_steps_true_for_generic_theory_lemma() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    // Generic theory lemma exports as trust
    let tl = proof.add_theory_lemma("BV", vec![not_x]);
    proof.add_rule_step(AletheRule::ThResolution, vec![], vec![h0, tl], vec![]);

    let quality = check_proof_with_quality(&proof, &terms).expect("quality check should pass");
    assert!(
        quality.has_trust_steps(),
        "has_trust_steps should be true when Generic theory lemma present"
    );
    assert_eq!(quality.trust_theory_kinds.len(), 1);
    assert_eq!(quality.trust_theory_kinds[0], TheoryLemmaKind::Generic);
}

#[test]
fn test_has_trust_steps_false_for_verified_proof() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let p0 = proof.add_assume(x, None);
    let p1 = proof.add_assume(not_x, None);
    proof.add_resolution(vec![], x, p0, p1);

    let quality = check_proof_with_quality(&proof, &terms).expect("valid proof should pass");
    assert!(
        !quality.has_trust_steps(),
        "has_trust_steps should be false for fully verified proof"
    );
    assert!(quality.trust_theory_kinds.is_empty());
}

#[test]
fn test_strict_proof_mode_rejects_trust() {
    let quality = ProofQuality {
        trust_count: 2,
        trust_theory_kinds: vec![TheoryLemmaKind::Generic, TheoryLemmaKind::Generic],
        ..ProofQuality::default()
    };

    let err = quality
        .check_strict_proof_mode(true)
        .expect_err("strict mode should reject trust steps");
    let msg = format!("{err}");
    assert!(
        msg.contains("strict proof mode"),
        "error should mention strict proof mode: {msg}"
    );
    assert!(
        msg.contains("Generic"),
        "error should identify the theory lemma kind: {msg}"
    );
    assert!(
        msg.contains("2 trust step(s)"),
        "error should count trust steps: {msg}"
    );
}

#[test]
fn test_strict_proof_mode_passes_when_disabled() {
    let quality = ProofQuality {
        trust_count: 5,
        trust_theory_kinds: vec![TheoryLemmaKind::Generic],
        ..ProofQuality::default()
    };

    quality
        .check_strict_proof_mode(false)
        .expect("strict mode disabled should pass even with trust steps");
}

#[test]
fn test_strict_proof_mode_passes_with_no_trust() {
    let quality = ProofQuality {
        resolution_count: 10,
        assume_count: 5,
        total_steps: 15,
        ..ProofQuality::default()
    };

    quality
        .check_strict_proof_mode(true)
        .expect("strict mode should pass when no trust steps");
}

#[test]
fn test_strict_proof_mode_identifies_sat_trust_steps() {
    // Trust steps from SAT proof reconstruction (not theory lemmas)
    let quality = ProofQuality {
        trust_count: 3,
        trust_theory_kinds: vec![TheoryLemmaKind::Generic],
        ..ProofQuality::default()
    };

    let err = quality
        .check_strict_proof_mode(true)
        .expect_err("strict mode should reject");
    let msg = format!("{err}");
    assert!(
        msg.contains("SAT proof reconstruction"),
        "error should note additional SAT trust steps: {msg}"
    );
}

#[test]
fn test_proof_quality_display() {
    let quality = ProofQuality {
        assume_count: 2,
        resolution_count: 3,
        th_resolution_count: 1,
        theory_lemma_count: 1,
        trust_count: 0,
        trust_fallback_count: 0,
        hole_count: 0,
        drup_count: 0,
        other_rule_count: 0,
        total_steps: 7,
        trust_theory_kinds: vec![],
    };

    let display = format!("{quality}");
    assert!(display.contains("steps=7"));
    assert!(display.contains("verified=4"));
    assert!(display.contains("axiom=3"));
    assert!(display.contains("fallback=0"));
}
