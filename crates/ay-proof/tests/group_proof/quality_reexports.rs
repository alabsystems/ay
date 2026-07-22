// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{AletheRule, Proof, Sort, TermStore};
use ay_proof::{check_proof_strict, check_proof_with_quality, ProofCheckError, ProofQuality};

#[test]
fn test_quality_reexports_enforce_trust_rules() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    let trust = proof.add_rule_step(AletheRule::Trust, vec![not_x], vec![], vec![]);
    proof.add_resolution(vec![], x, trust, h0);

    let quality = check_proof_with_quality(&proof, &terms)
        .expect("non-strict quality check should accept trust fallback");
    assert_eq!(quality.total_steps, 3);
    assert_eq!(quality.trust_count, 1);
    assert_eq!(quality.fallback_count(), 1);
    assert!(!quality.is_complete());

    let err = check_proof_strict(&proof, &terms).expect_err("strict mode must reject trust");
    assert_eq!(
        err,
        ProofCheckError::TrustStep {
            step: ay_core::ProofId(1)
        }
    );
}

#[test]
fn test_proof_quality_reexport_helpers() {
    let mut quality = ProofQuality::default();
    quality.assume_count = 2;
    quality.resolution_count = 1;
    quality.theory_lemma_count = 1;
    quality.trust_count = 1;
    quality.hole_count = 0;
    quality.drup_count = 1;
    quality.th_resolution_count = 2;
    quality.other_rule_count = 3;
    quality.total_steps = 11;

    assert_eq!(quality.verified_count(), 4);
    assert_eq!(quality.axiom_count(), 3);
    assert_eq!(quality.fallback_count(), 1);
    assert!(!quality.is_complete());
}
