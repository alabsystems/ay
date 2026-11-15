// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Downstream-only native certificate smoke tests. These use public APIs and
//! the normal ay-proof library, not the full internal unit-test module tree.
//! Bundle replay authenticates internal derivation, not an external problem.

use ay_core::{
    Constant, NraSosCertificate, NraSosOrigin, NraSosRational, NraSosTerm, Proof, ProofStep,
    RationalWrapper, Sort, TermData, TermId, TermStore,
};
use ay_proof::{re_check_bundle_strict, ProofCheckError, SerializableProofBundle};
use num_bigint::BigInt;
use num_rational::BigRational;

#[path = "model_checker_consumer_certificate_api/contexts.rs"]
mod contexts;

fn rational(value: i64) -> NraSosRational {
    NraSosRational {
        numerator: BigInt::from(value),
        denominator: BigInt::from(1),
    }
}

fn fixture() -> (TermStore, Proof, Vec<TermId>) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("consumer_x", Sort::Real);
    let one = terms.mk_rational(BigRational::from_integer(BigInt::from(1)));
    let zero = terms.mk_rational(BigRational::from_integer(BigInt::from(0)));
    let lower = terms.mk_ge(x, one);
    let upper = terms.mk_le(x, zero);
    let not_lower = terms.mk_not(lower);
    let not_upper = terms.mk_not(upper);
    let certificate = NraSosCertificate {
        basis: vec![vec![], vec![x]],
        gram: vec![vec![rational(0); 2]; 2],
        terms: vec![
            NraSosTerm {
                origin: NraSosOrigin::ClauseLiteral { position: 0 },
                multiplier: rational(1),
            },
            NraSosTerm {
                origin: NraSosOrigin::ClauseLiteral { position: 1 },
                multiplier: rational(1),
            },
        ],
        rhs: rational(-1),
    };
    let mut proof = Proof::new();
    let lemma = proof.add_step(ProofStep::NraSos {
        clause: vec![not_lower, not_upper],
        certificate,
    });
    let first = proof.add_assume(lower, None);
    let second = proof.add_assume(upper, None);
    let tail = proof.add_resolution(vec![not_upper], lower, lemma, first);
    proof.add_resolution(vec![], upper, tail, second);
    (terms, proof, vec![lower, upper])
}

fn copy(
    terms: &TermStore,
    proof: &Proof,
    assertions: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<SerializableProofBundle, ProofCheckError> {
    SerializableProofBundle::from_proof_with_progress(proof, terms, assertions, progress)
}

#[test]
fn downstream_native_sos_roundtrip_replays_without_a_producer_solver() {
    let (terms, proof, assertions) = fixture();
    let bundle = copy(&terms, &proof, &assertions, &mut |_, _| true).unwrap();
    let encoded = serde_json::to_vec(&bundle).unwrap();
    let decoded: SerializableProofBundle = serde_json::from_slice(&encoded).unwrap();
    let checked = re_check_bundle_strict(&decoded).unwrap();
    assert_eq!(checked.assume_terms, assertions);
    assert_eq!(checked.quality.theory_lemma_count, 1);
    assert_eq!(checked.quality.resolution_count, 2);
    assert_eq!(checked.quality.trust_count, 0);
    assert_eq!(checked.quality.hole_count, 0);
}

#[test]
fn downstream_native_sos_rejects_forged_identity_source_and_missing_handles() {
    let (terms, proof, assertions) = fixture();
    for mutation in 0..3 {
        let mut bundle = copy(&terms, &proof, &assertions, &mut |_, _| true).unwrap();
        let ProofStep::NraSos {
            clause,
            certificate,
        } = &mut bundle.steps[0]
        else {
            panic!("native SOS fixture");
        };
        match mutation {
            0 => certificate.terms[0].multiplier = rational(2),
            1 => clause[0] = assertions[0],
            _ => certificate.basis[1][0] = TermId(u32::MAX),
        }
        assert!(re_check_bundle_strict(&bundle).is_err());
    }
}

#[test]
fn downstream_copy_refuses_every_callback_without_publishing_partial_data() {
    let (terms, proof, assertions) = fixture();
    let mut count = 0;
    copy(&terms, &proof, &assertions, &mut |_, _| {
        count += 1;
        true
    })
    .unwrap();
    for stop in 1..=count {
        let mut calls = 0;
        let result = copy(&terms, &proof, &assertions, &mut |_, _| {
            calls += 1;
            calls != stop // Later approval must not resume a refused operation.
        });
        assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(calls, stop);
    }
}

#[test]
fn downstream_copy_keeps_one_budget_across_repeated_operations() {
    let (terms, proof, assertions) = fixture();
    let mut required = 0;
    copy(&terms, &proof, &assertions, &mut |_, bytes| {
        required += bytes;
        true
    })
    .unwrap();
    let mut used = 0;
    let mut progress = |_, bytes| {
        used += bytes;
        used <= required
    };
    assert!(copy(&terms, &proof, &assertions, &mut progress).is_ok());
    assert!(matches!(
        copy(&terms, &proof, &assertions, &mut progress),
        Err(ProofCheckError::ResourceLimit)
    ));
}

#[test]
fn downstream_copy_does_not_authenticate_malformed_boolean_metadata() {
    let raw = TermStore::from_entries(vec![], None, Some(TermId(u32::MAX)), 23);
    let proof = Proof::from_steps(vec![ProofStep::Assume(TermId(99))]);
    let copied = copy(&raw, &proof, &[TermId(99)], &mut |_, _| true).unwrap();
    assert_eq!(copied.true_term, None);
    assert_eq!(copied.false_term, Some(TermId(u32::MAX)));
    assert_eq!(copied.var_counter, 23);
    assert_eq!(copied.steps, proof.steps);
    assert!(re_check_bundle_strict(&copied).is_err());
}

#[test]
fn downstream_native_sos_renders_checked_alethe_not_an_invented_rule() {
    let (terms, proof, _) = fixture();
    let rendered = ay_proof::try_export_alethe(&proof, &terms).unwrap();
    assert!(rendered.contains("ay-nra-sos:"));
    assert!(rendered.contains(":rule la_generic"), "{rendered}");
    assert!(!rendered.contains(":rule hole"), "{rendered}");
    assert!(!rendered.contains(":rule nra_sos"));
}

#[test]
fn downstream_preflight_rejects_unused_raw_zero_denominator_before_equality() {
    let (terms, proof, assertions) = fixture();
    let mut bundle = copy(&terms, &proof, &assertions, &mut |_, _| true).unwrap();
    // Public in-memory snapshots bypass serde's nonzero-denominator check.
    // Reject this unused value before canonical-entry Eq can divide by zero.
    bundle.term_entries.push((
        TermData::Const(Constant::Rational(RationalWrapper(BigRational::new_raw(
            BigInt::from(1),
            BigInt::from(0),
        )))),
        Sort::Real,
    ));
    assert!(matches!(
        re_check_bundle_strict(&bundle),
        Err(ProofCheckError::MalformedProofBundle { .. })
    ));
}

#[test]
fn downstream_preflight_retains_nonreduced_and_negative_denominator_encodings() {
    let (terms, proof, assertions) = fixture();
    for (numerator, denominator) in [(2, 6), (1, -3)] {
        let mut bundle = copy(&terms, &proof, &assertions, &mut |_, _| true).unwrap();
        let raw = TermData::Const(Constant::Rational(RationalWrapper(BigRational::new_raw(
            BigInt::from(numerator),
            BigInt::from(denominator),
        ))));
        bundle.term_entries.push((raw, Sort::Real));
        let before = serde_json::to_vec(&bundle).unwrap();
        assert!(re_check_bundle_strict(&bundle).is_ok());
        assert_eq!(serde_json::to_vec(&bundle).unwrap(), before);
    }
}

#[test]
fn downstream_preflight_rejects_numeric_aliases_even_with_distinct_raw_rational_hashes() {
    let (terms, proof, assertions) = fixture();
    for pair in [[(1, 2), (2, 4)], [(1, -2), (-1, 2)], [(0, 7), (0, -3)]] {
        let mut bundle = copy(&terms, &proof, &assertions, &mut |_, _| true).unwrap();
        for (numerator, denominator) in pair {
            bundle.term_entries.push((
                TermData::Const(Constant::Rational(RationalWrapper(BigRational::new_raw(
                    BigInt::from(numerator),
                    BigInt::from(denominator),
                )))),
                Sort::Real,
            ));
        }
        let before = serde_json::to_vec(&bundle).unwrap();
        assert!(matches!(
            re_check_bundle_strict(&bundle),
            Err(ProofCheckError::MalformedProofBundle { .. })
        ));
        assert_eq!(serde_json::to_vec(&bundle).unwrap(), before);
    }
}
