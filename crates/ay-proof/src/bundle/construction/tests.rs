// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{AletheRule, NraSosCertificate, NraSosRational};
use num_bigint::BigInt;

use super::*;

fn fixture() -> (TermStore, Proof, Vec<TermId>) {
    let mut terms = TermStore::new();
    let positive = terms.mk_var("bundle_meter_p", Sort::Bool);
    let negative = terms.mk_not(positive);
    let mut proof = Proof::new();
    let left = proof.add_assume(positive, None);
    let right = proof.add_assume(negative, None);
    proof.add_resolution(vec![], positive, left, right);
    (terms, proof, vec![positive, negative])
}

#[test]
fn namespace_identity_copying_preserves_opaque_meaning_and_original_storage_limits() {
    let (mut terms, proof, assertions) = fixture();
    let identity = "opaque_user_identity_".repeat(1024);
    terms.register_declared_function(&identity);
    let plain = SerializableProofBundle::from_proof(&proof, &terms, assertions.clone());
    let copied = construct(&terms, &proof, &assertions, &mut |_, _| true).unwrap();
    assert_eq!(plain.declared_function_identities, vec![identity.clone()]);
    assert_eq!(
        copied.declared_function_identities,
        plain.declared_function_identities
    );
    let cloned = copied.try_clone_with_progress(&mut |_, _| true).unwrap();
    assert_eq!(
        cloned.declared_function_identities,
        plain.declared_function_identities
    );
    assert!(re_check_bundle_strict(&cloned)
        .unwrap()
        .quality
        .is_complete());
    let mut remaining = identity.len() - 1;
    assert!(matches!(
        construct(&terms, &proof, &assertions, &mut |_, bytes| {
            match remaining.checked_sub(bytes) {
                Some(left) => {
                    remaining = left;
                    true
                }
                None => false,
            }
        }),
        Err(ProofCheckError::ResourceLimit)
    ));
    let mut json = serde_json::to_value(&plain).unwrap();
    json.as_object_mut()
        .unwrap()
        .remove("declared_function_identities");
    assert!(serde_json::from_value::<SerializableProofBundle>(json).is_err());
}

fn construct(
    terms: &TermStore,
    proof: &Proof,
    assertions: &[TermId],
    progress: Progress<'_>,
) -> Result<SerializableProofBundle, ProofCheckError> {
    SerializableProofBundle::from_proof_with_progress(proof, terms, assertions, progress)
}

fn usage(terms: &TermStore, proof: &Proof, assertions: &[TermId]) -> (usize, usize, usize) {
    let (mut work, mut bytes, mut polls) = (0, 0, 0);
    construct(terms, proof, assertions, &mut |w, b| {
        work += w;
        bytes += b;
        polls += 1;
        true
    })
    .expect("small borrowed copy");
    (work, bytes, polls)
}

#[test]
fn metered_bundle_matches_legacy_bytes_and_rechecks_independently() {
    let (terms, proof, assertions) = fixture();
    let old = SerializableProofBundle::from_proof(&proof, &terms, assertions.clone());
    let new = construct(&terms, &proof, &assertions, &mut |_, _| true).unwrap();
    assert_eq!(
        serde_json::to_vec(&old).unwrap(),
        serde_json::to_vec(&new).unwrap()
    );
    let checked = re_check_bundle_strict(&new).expect("fresh independent Boolean replay");
    assert_eq!(checked.assume_terms, assertions);
    assert_eq!(checked.quality.resolution_count, 1);
    assert_eq!(checked.quality.trust_count, 0);
}

#[test]
fn metered_bundle_aborts_at_every_callback_including_final_poll() {
    let (terms, proof, assertions) = fixture();
    let (_, _, polls) = usage(&terms, &proof, &assertions);
    for refused_poll in 1..=polls {
        let mut calls = 0;
        let result = construct(&terms, &proof, &assertions, &mut |_, _| {
            calls += 1;
            calls != refused_poll // Would approve later calls; none may occur.
        });
        assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(calls, refused_poll);
    }
}

#[test]
fn metered_bundle_enforces_exact_cumulative_work_and_byte_allowances() {
    let (terms, proof, assertions) = fixture();
    let (work, bytes, _) = usage(&terms, &proof, &assertions);
    for (work_limit, byte_limit, success) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
        (0, usize::MAX, false),
        (usize::MAX, 0, false),
    ] {
        let (mut w, mut b) = (0, 0);
        let result = construct(&terms, &proof, &assertions, &mut |dw, db| {
            w += dw;
            b += db;
            w <= work_limit && b <= byte_limit
        });
        assert_eq!(result.is_ok(), success);
    }
}

#[test]
fn metered_bundle_does_not_reset_an_envelope_between_copies() {
    let (terms, proof, assertions) = fixture();
    let (work, bytes, _) = usage(&terms, &proof, &assertions);
    let (mut w, mut b) = (0, 0);
    let mut progress = |dw, db| {
        w += dw;
        b += db;
        w <= work && b <= bytes
    };
    assert!(construct(&terms, &proof, &assertions, &mut progress).is_ok());
    assert!(matches!(
        construct(&terms, &proof, &assertions, &mut progress),
        Err(ProofCheckError::ResourceLimit)
    ));
}

#[test]
fn metered_bundle_prices_unused_payload_even_after_zero_ledger_reconstruction() {
    let (mut terms, proof, assertions) = fixture();
    let (_, small_bytes, _) = usage(&terms, &proof, &assertions);
    terms.mk_string("unused-certificate-payload".repeat(4096));
    let restored = TermStore::from_entries(
        terms.entries_snapshot(),
        Some(terms.true_term()),
        Some(terms.false_term()),
        terms.var_counter(),
    );
    assert_eq!(restored.instance_term_bytes(), 0);
    let (_, large_bytes, _) = usage(&restored, &proof, &assertions);
    assert!(large_bytes >= small_bytes + 4096 * "unused-certificate-payload".len());
    let mut bytes = 0;
    assert!(matches!(
        construct(&restored, &proof, &assertions, &mut |_, b| {
            bytes += b;
            bytes <= small_bytes
        }),
        Err(ProofCheckError::ResourceLimit)
    ));
}

#[test]
fn metered_bundle_preserves_malformed_handles_without_granting_authority() {
    for ids in [
        (None, None),
        (Some(TermId::new(u32::MAX)), Some(TermId::new(3))),
    ] {
        let terms = TermStore::from_entries(vec![], ids.0, ids.1, 0);
        let proof = Proof::from_steps(vec![ProofStep::Assume(TermId::new(99))]);
        let bundle = construct(&terms, &proof, &[TermId::new(99)], &mut |_, _| true).unwrap();
        assert_eq!((bundle.true_term, bundle.false_term), ids);
        assert_eq!(bundle.steps, proof.steps);
        assert!(re_check_bundle_strict(&bundle).is_err());
    }
}

#[test]
fn metered_bundle_copies_typed_context_exactly_and_prices_nested_sorts() {
    let (terms, mut proof, assertions) = fixture();
    let nested = Sort::Seq(Box::new(Sort::Uninterpreted("owned-sort".repeat(128))));
    proof.add_step(ProofStep::Anchor {
        end_step: ProofId(0),
        variables: vec![("binder".repeat(128), nested.clone())],
    });
    let declarations = vec![("D".repeat(128), vec!["C".repeat(128)])];
    let selectors = vec![("C".repeat(128), vec!["field".repeat(128)])];
    let signatures = vec![DatatypeMemberSignature {
        identity: "member".repeat(128),
        argument_sorts: vec![nested.clone()],
        result_sort: nested,
        nullary_term: Some(TermId::new(1)),
    }];
    let mut bytes = 0;
    let new = SerializableProofBundle::from_proof_with_typed_context_and_progress(
        &proof,
        &terms,
        &assertions,
        &declarations,
        &selectors,
        &signatures,
        &mut |_, b| {
            bytes += b;
            true
        },
    )
    .unwrap();
    let old = SerializableProofBundle::from_proof_with_typed_context(
        &proof,
        &terms,
        assertions,
        declarations,
        selectors,
        signatures,
    );
    assert_eq!(
        serde_json::to_vec(&old).unwrap(),
        serde_json::to_vec(&new).unwrap()
    );
    assert!(bytes > 3 * "owned-sort".len() * 128);
    assert!(re_check_bundle_strict(&new).is_err()); // Copying is not context authentication.
}

#[test]
fn metered_bundle_rejects_overdeep_declaration_and_anchor_sorts_before_clone() {
    let (terms, mut proof, assertions) = fixture();
    let mut deep = Sort::Bool;
    for _ in 0..258 {
        deep = Sort::Seq(Box::new(deep));
    }
    let signatures = vec![DatatypeMemberSignature {
        identity: "deep".into(),
        argument_sorts: vec![],
        result_sort: deep.clone(),
        nullary_term: None,
    }];
    assert!(matches!(
        SerializableProofBundle::from_proof_with_typed_context_and_progress(
            &proof,
            &terms,
            &assertions,
            &[],
            &[],
            &signatures,
            &mut |_, _| true,
        ),
        Err(ProofCheckError::ResourceLimit)
    ));
    proof.add_step(ProofStep::Anchor {
        end_step: ProofId(0),
        variables: vec![("x".into(), deep)],
    });
    assert!(matches!(
        construct(&terms, &proof, &assertions, &mut |_, _| true),
        Err(ProofCheckError::ResourceLimit)
    ));
}

#[test]
fn metered_bundle_prices_custom_rules_and_all_sos_integer_limbs() {
    let (terms, mut proof, assertions) = fixture();
    let (small_work, small_bytes, _) = usage(&terms, &proof, &assertions);
    proof.add_step(ProofStep::Step {
        rule: AletheRule::Custom("rule".repeat(1024)),
        clause: assertions.clone(),
        premises: vec![ProofId(0); 64],
        args: assertions.clone(),
    });
    let integer = BigInt::from(1u8) << 8192usize;
    let rational = NraSosRational {
        numerator: integer.clone(),
        denominator: integer,
    };
    let certificate = NraSosCertificate {
        basis: vec![assertions.clone()],
        gram: vec![vec![rational.clone()]],
        terms: vec![ay_core::NraSosTerm {
            origin: ay_core::NraSosOrigin::ClauseLiteral { position: 0 },
            multiplier: rational.clone(),
        }],
        rhs: rational,
    };
    proof.add_step(ProofStep::NraSos {
        clause: assertions.clone(),
        certificate,
    });
    let (large_work, large_bytes, _) = usage(&terms, &proof, &assertions);
    assert!(large_bytes >= small_bytes + 4096 + 6 * 1024);
    assert!(large_work > small_work + 4096);
    let copied = construct(&terms, &proof, &assertions, &mut |_, _| true).unwrap();
    assert_eq!(copied.steps, proof.steps);
    assert!(re_check_bundle_strict(&copied).is_err()); // Deliberately over-limit SOS DTO.
}

#[test]
fn metered_bundle_prices_both_farkas_and_cutting_plane_arrays() {
    let (terms, mut proof, assertions) = fixture();
    let (_, small_bytes, _) = usage(&terms, &proof, &assertions);
    let coefficients = vec![num_rational::Rational64::from_integer(1); 512];
    let annotation = ay_core::FarkasAnnotation { coefficients };
    proof.add_step(ProofStep::TheoryLemma {
        theory: "untrusted-theory-name".repeat(128),
        clause: assertions.clone(),
        farkas: Some(annotation.clone()),
        kind: TheoryLemmaKind::Generic,
        lia: Some(ay_core::LiaAnnotation::CuttingPlane(
            ay_core::CuttingPlaneAnnotation {
                farkas: annotation,
                divisor: 2,
            },
        )),
    });
    let (_, large_bytes, _) = usage(&terms, &proof, &assertions);
    assert!(large_bytes >= small_bytes + 1024 * size_of::<num_rational::Rational64>());
    let copied = construct(&terms, &proof, &assertions, &mut |_, _| true).unwrap();
    assert_eq!(copied.steps, proof.steps);
}
