// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::common;

use ay_core::TheoryLemmaKind;
use ay_proof::{check_proof_strict, ProofCheckError};

#[test]
fn test_strict_mode_accepts_valid_lra_farkas_theory_lemma() {
    let (terms, proof) = common::build_valid_lra_farkas_proof();

    let quality = check_proof_strict(&proof, &terms)
        .expect("strict mode should accept semantically valid LraFarkas lemmas");
    assert_eq!(quality.theory_lemma_count, 1);
    assert_eq!(quality.trust_count, 0);
}

#[test]
fn test_strict_mode_rejects_non_lra_theory_lemma_kinds() {
    let (terms, proof) = common::build_unsound_theory_lemma_proof();

    let err = check_proof_strict(&proof, &terms)
        .expect_err("strict mode must reject unsupported theory lemma kinds");
    assert_eq!(
        err,
        ProofCheckError::UnsupportedTheoryLemmaKind {
            step: ay_core::ProofId(2),
            kind: TheoryLemmaKind::Generic,
        }
    );
}

// --- EUF Transitive ---

#[test]
fn test_strict_accepts_valid_euf_transitive() {
    let (terms, proof) = common::build_valid_euf_transitive_proof();

    let quality = check_proof_strict(&proof, &terms)
        .expect("strict mode should accept valid EufTransitive lemmas");
    assert_eq!(quality.theory_lemma_count, 1);
    assert_eq!(quality.trust_count, 0);
}

#[test]
fn test_strict_rejects_broken_transitive_chain() {
    let (terms, proof) = common::build_broken_euf_transitive_proof();

    let err = check_proof_strict(&proof, &terms)
        .expect_err("strict mode must reject broken transitive chain");
    match err {
        ProofCheckError::InvalidTheoryLemma { step, reason } => {
            assert_eq!(step, ay_core::ProofId(2));
            assert!(
                reason.contains("do not form a chain"),
                "unexpected reason: {reason}"
            );
        }
        other => panic!("expected InvalidTheoryLemma, got {other:?}"),
    }
}

// --- EUF Congruent ---

#[test]
fn test_strict_accepts_valid_euf_congruent() {
    let (terms, proof) = common::build_valid_euf_congruent_proof();

    let quality = check_proof_strict(&proof, &terms)
        .expect("strict mode should accept valid EufCongruent lemmas");
    assert_eq!(quality.theory_lemma_count, 1);
    assert_eq!(quality.trust_count, 0);
}

#[test]
fn test_strict_rejects_congruent_wrong_symbol() {
    let (terms, proof) = common::build_broken_euf_congruent_wrong_symbol_proof();

    let err = check_proof_strict(&proof, &terms)
        .expect_err("strict mode must reject congruent with wrong symbol");
    match err {
        ProofCheckError::InvalidTheoryLemma { step, reason } => {
            assert_eq!(step, ay_core::ProofId(1));
            assert!(
                reason.contains("different function symbols"),
                "unexpected reason: {reason}"
            );
        }
        other => panic!("expected InvalidTheoryLemma, got {other:?}"),
    }
}

// --- EUF Congruent Pred ---

#[test]
fn test_strict_accepts_valid_euf_congruent_pred() {
    let (terms, proof) = common::build_valid_euf_congruent_pred_proof();

    let quality = check_proof_strict(&proof, &terms)
        .expect("strict mode should accept valid EufCongruentPred lemmas");
    assert_eq!(quality.theory_lemma_count, 1);
    assert_eq!(quality.trust_count, 0);
}

#[test]
fn test_strict_rejects_congruent_pred_arity_mismatch() {
    let (terms, proof) = common::build_broken_euf_congruent_pred_arity_proof();

    let err = check_proof_strict(&proof, &terms)
        .expect_err("strict mode must reject congruent_pred with arity mismatch");
    match err {
        ProofCheckError::InvalidTheoryLemma { step, reason } => {
            assert_eq!(step, ay_core::ProofId(2));
            assert!(
                reason.contains("arities differ"),
                "unexpected reason: {reason}"
            );
        }
        other => panic!("expected InvalidTheoryLemma, got {other:?}"),
    }
}
