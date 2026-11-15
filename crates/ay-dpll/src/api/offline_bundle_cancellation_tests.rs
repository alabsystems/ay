// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::{
    re_check_bundle_strict, re_check_bundle_strict_with_cancellation, SerializableProofBundle,
};
use ay_core::{Proof, Sort, TermStore};

fn contradiction() -> SerializableProofBundle {
    let mut terms = TermStore::new();
    let p = terms.mk_var("public-replay-p", Sort::Bool);
    let not_p = terms.mk_not(p);
    let mut proof = Proof::new();
    let positive = proof.add_assume(p, None);
    let negative = proof.add_assume(not_p, None);
    proof.add_resolution(vec![], p, positive, negative);
    SerializableProofBundle::from_proof(&proof, &terms, vec![p, not_p])
}

#[test]
fn public_cancel_reader_matches_legacy_complete_contradiction() {
    let bundle = contradiction();
    let original = serde_json::to_vec(&bundle).unwrap();
    let expected = re_check_bundle_strict(&bundle).unwrap();
    let mut polls = 0;
    let actual = re_check_bundle_strict_with_cancellation(&bundle, &mut || {
        polls += 1;
        true
    })
    .unwrap();
    assert!(actual.quality.is_complete());
    assert!(expected.quality.is_complete());
    assert_eq!(actual.assume_terms, expected.assume_terms);
    assert!(polls > bundle.steps.len());
    assert_eq!(serde_json::to_vec(&bundle).unwrap(), original);
}

#[test]
fn public_cancel_reader_declines_before_invalid_schema_diagnostics() {
    let mut bundle = contradiction();
    bundle.schema = "not-the-schema".to_owned();
    let mut calls = 0;
    assert!(matches!(
        re_check_bundle_strict_with_cancellation(&bundle, &mut || {
            calls += 1;
            false
        }),
        Err(super::ProofCheckError::ResourceLimit)
    ));
    assert_eq!(calls, 1);
    assert!(matches!(
        re_check_bundle_strict(&bundle),
        Err(super::ProofCheckError::BundleSchemaMismatch { .. })
    ));
}

#[test]
fn public_cancel_reader_rejects_omitted_source_assumption() {
    let mut bundle = contradiction();
    bundle.obligation_assertions.pop();
    assert!(re_check_bundle_strict_with_cancellation(&bundle, &mut || true).is_err());
    assert!(re_check_bundle_strict(&bundle).is_err());
}
