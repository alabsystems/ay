// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Serialized proofs must use the same checked producer as direct checking.
use super::*;
use ay_core::{Sort, Symbol, TheoryLemmaKind};
use num_bigint::BigInt;

fn bounded_mask_claim(width: u32, operator: &str, comparison: &str) -> SerializableProofBundle {
    let mut terms = TermStore::new();
    let x = terms.mk_var("wide-independent-input", Sort::bitvec(width));
    let mask = terms.mk_bitvec(BigInt::from(15), width);
    let masked = terms.mk_app(Symbol::named(operator), &[x, mask], Sort::bitvec(width));
    let bound = terms.mk_bitvec(BigInt::from(16), width);
    let theorem = terms.mk_app(Symbol::named(comparison), &[masked, bound], Sort::Bool);
    let assumption = terms.mk_not_raw(theorem);
    let mut proof = Proof::new();
    let assumed = proof.add_assume(assumption, None);
    let lemma = proof.add_theory_lemma_with_kind("BV", vec![theorem], TheoryLemmaKind::BvBitBlast);
    proof.add_resolution(vec![], theorem, lemma, assumed);
    SerializableProofBundle::from_proof(&proof, &terms, vec![assumption])
}

#[test]
fn wide_bv_replay_accepts_checked_refutations_after_serialization() {
    for width in [63, 64, 65, 96, 127, 128] {
        let bundle = bounded_mask_claim(width, "bvand", "bvult");
        let bytes = serde_json::to_vec(&bundle).unwrap();
        let restored = serde_json::from_slice(&bytes).unwrap();
        let checked =
            re_check_bundle_strict(&restored).unwrap_or_else(|e| panic!("width {width}: {e:?}"));
        assert!(checked.quality.is_complete());
        assert_eq!(checked.quality.trust_count, 0);
        assert_eq!(serde_json::to_vec(&restored).unwrap(), bytes);
    }
}

#[test]
fn wide_bv_replay_rejects_forged_clauses_and_out_of_range_words() {
    for width in [64, 65, 96, 128] {
        // OR admits high bits; AND is not greater than 16. Both source
        // negations are satisfiable, so neither authored refutation is valid.
        for (operator, comparison) in [("bvor", "bvult"), ("bvand", "bvugt")] {
            let bundle = bounded_mask_claim(width, operator, comparison);
            assert!(
                re_check_bundle_strict(&bundle).is_err(),
                "{width}: {operator}/{comparison}"
            );
        }
    }
    assert!(re_check_bundle_strict(&bounded_mask_claim(129, "bvand", "bvult")).is_err());
}

#[test]
fn wide_bv_replay_cancellation_does_not_publish_acceptance() {
    let bundle = bounded_mask_claim(128, "bvand", "bvult");
    let mut calls = 0;
    let checked = re_check_bundle_strict_with_cancellation(&bundle, &mut || {
        calls += 1;
        true
    })
    .unwrap();
    assert!(checked.quality.is_complete());
    assert_eq!(checked.quality.trust_count, 0);
    for stop in [1, calls / 2, calls] {
        let mut seen = 0;
        let result = re_check_bundle_strict_with_cancellation(&bundle, &mut || {
            seen += 1;
            seen != stop
        });
        assert!(
            matches!(result, Err(ProofCheckError::ResourceLimit)),
            "stop {stop}: {result:?}"
        );
    }
    assert!(re_check_bundle_strict(&bundle)
        .unwrap()
        .quality
        .is_complete());
}

#[test]
fn wide_bv_replay_preserves_global_signature_and_reference_refusals() {
    for mutation in 0..3 {
        let mut bundle = bounded_mask_claim(128, "bvand", "bvult");
        let (data, sort) = bundle.term_entries.iter_mut().find(|(data, _)| {
            matches!(data, TermData::App(Symbol::Named(name), _) if name == "bvand")
        }).unwrap();
        let TermData::App(_, args) = data else {
            unreachable!()
        };
        match mutation {
            0 => {
                args.pop();
            }
            1 => {
                args[0] = TermId(u32::MAX);
            }
            _ => {
                *sort = Sort::Bool;
            }
        }
        assert!(
            matches!(
                re_check_bundle_strict(&bundle),
                Err(ProofCheckError::MalformedProofBundle { .. })
            ),
            "mutation {mutation}"
        );
    }
}
