// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{
    re_check_bundle_strict, re_check_bundle_strict_with_cancellation, SerializableProofBundle,
};

#[derive(Clone, Copy)]
enum RegistryKind {
    ExtDiff,
    FreshDef,
}

fn registry_fixture(kind: RegistryKind) -> (TermStore, Proof, Vec<TermId>) {
    let mut terms = TermStore::new();
    let mut proof = Proof::new();
    match kind {
        RegistryKind::ExtDiff => {
            let array_sort = Sort::Array(Box::new(ay_core::ArraySort::new(Sort::Int, Sort::Int)));
            let left = terms.mk_var("registry-left", array_sort.clone());
            let right = terms.mk_var("registry-right", array_sort);
            let witness = terms.mk_var("registry-witness", Sort::Int);
            proof.add_rule_step(
                AletheRule::ArrayExtDiffIntro,
                vec![],
                vec![],
                vec![witness, left, right],
            );
        }
        RegistryKind::FreshDef => {
            let source = terms.mk_var("registry-source", Sort::Int);
            let defined = terms.mk_var("registry-defined", Sort::Int);
            let bound = terms.mk_le(defined, source);
            let equality = terms.mk_eq(defined, source);
            proof.add_rule_step(
                AletheRule::FreshDefBound,
                vec![bound],
                vec![],
                vec![defined],
            );
            proof.add_rule_step(
                AletheRule::FreshDefEq,
                vec![equality],
                vec![],
                vec![defined],
            );
        }
    }
    // The introduction is unused, but whole-proof provenance must still be
    // validated. The refutation itself is a genuine Boolean contradiction.
    let positive = terms.mk_var("registry-contradiction", Sort::Bool);
    let negative = terms.mk_not(positive);
    let first = proof.add_assume(positive, None);
    let second = proof.add_assume(negative, None);
    proof.add_resolution(vec![], positive, first, second);
    (terms, proof, vec![positive, negative])
}

fn sample_payload() -> PayloadStats {
    PayloadStats {
        work: 100,
        bytes: 200,
        unfolded_work: 100,
        fp_assignments: 0,
        order_assignments: 0,
    }
}

fn census(
    kind: RegistryKind,
    terms: &TermStore,
    proof: &Proof,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(usize, usize), ProofCheckError> {
    match kind {
        RegistryKind::ExtDiff => ext_diff_registry_charge(proof, terms, sample_payload(), progress),
        RegistryKind::FreshDef => fresh_def_registry_charge(proof, sample_payload(), progress),
    }
}

#[test]
fn registry_census_preserves_reservations_and_adds_only_zero_charge_polls() {
    for kind in [RegistryKind::ExtDiff, RegistryKind::FreshDef] {
        let (terms, proof, _) = registry_fixture(kind);
        let mut polls = 0;
        let actual = census(kind, &terms, &proof, &mut |work, bytes| {
            assert_eq!((work, bytes), (0, 0));
            polls += 1;
            true
        })
        .unwrap();
        assert_eq!(polls, proof.steps.len() + 2);
        let expected = match kind {
            RegistryKind::ExtDiff => {
                let ProofStep::Step { args, .. } = &proof.steps[0] else {
                    panic!("fixture introduction");
                };
                let TermData::Var(name, _) = terms.get(args[0]) else {
                    panic!("fixture witness");
                };
                (
                    2 * 100 + 1 + proof.steps.len(),
                    2 * 200 + name.capacity() + size_of::<String>() + 32 + 128,
                )
            }
            RegistryKind::FreshDef => (2 * 100 + proof.steps.len(), 2 * 200 + 2 * 128),
        };
        assert_eq!(actual, expected);
    }
}

#[test]
fn registry_census_refuses_every_poll_including_empty_and_final() {
    for kind in [RegistryKind::ExtDiff, RegistryKind::FreshDef] {
        let (terms, proof, _) = registry_fixture(kind);
        for candidate in [&proof, &Proof::new()] {
            for stop in 1..=candidate.steps.len() + 2 {
                let mut calls = 0;
                let result = census(kind, &terms, candidate, &mut |_, _| {
                    calls += 1;
                    calls != stop
                });
                assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
                assert_eq!(calls, stop, "the same census must not retry after refusal");
            }
            assert!(census(kind, &terms, candidate, &mut |_, _| true).is_ok());
        }
    }
}

#[test]
fn offline_reader_with_each_registry_refuses_every_callback_without_publication() {
    for kind in [RegistryKind::ExtDiff, RegistryKind::FreshDef] {
        let (terms, proof, assertions) = registry_fixture(kind);
        let bundle = SerializableProofBundle::from_proof(&proof, &terms, assertions.clone());
        let original = serde_json::to_vec(&bundle).unwrap();
        let expected = re_check_bundle_strict(&bundle).unwrap();
        assert!(expected.quality.is_complete());
        assert_eq!(expected.assume_terms, assertions);
        let mut total = 0;
        let actual = re_check_bundle_strict_with_cancellation(&bundle, &mut || {
            total += 1;
            true
        })
        .unwrap();
        assert_eq!(actual.quality, expected.quality);
        assert_eq!(actual.assume_terms, expected.assume_terms);
        assert!(total > proof.steps.len());

        for stop in 1..=total {
            let mut calls = 0;
            let result = re_check_bundle_strict_with_cancellation(&bundle, &mut || {
                calls += 1;
                // Returning true after the selected refusal would resurrect a
                // non-sticky wrapper. No callback after that refusal is allowed.
                calls != stop
            });
            assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
            assert_eq!(calls, stop);
        }
        assert_eq!(serde_json::to_vec(&bundle).unwrap(), original);
        let retried = re_check_bundle_strict_with_cancellation(&bundle, &mut || true).unwrap();
        assert_eq!(retried.quality, expected.quality);
        assert_eq!(retried.assume_terms, assertions);
    }
}

#[test]
fn strict_reader_exposes_each_collectors_actual_inner_polls() {
    for kind in [RegistryKind::ExtDiff, RegistryKind::FreshDef] {
        let (terms, proof, assertions) = registry_fixture(kind);
        let payload = meter_authentication_payload(
            &proof,
            &terms,
            None,
            None,
            None,
            Some(&assertions),
            &mut |_, _| true,
        )
        .unwrap()
        .aggregate;
        let reservation = match kind {
            RegistryKind::ExtDiff => {
                ext_diff_registry_charge(&proof, &terms, payload, &mut |_, _| true).unwrap()
            }
            RegistryKind::FreshDef => {
                fresh_def_registry_charge(&proof, payload, &mut |_, _| true).unwrap()
            }
        };
        let mut inner_polls = 0;
        let mut count_inner = |work, bytes| {
            assert_eq!((work, bytes), (0, 0));
            inner_polls += 1;
            true
        };
        match kind {
            RegistryKind::ExtDiff => {
                ExtDiffRegistry::collect_with_progress(
                    &proof,
                    &terms,
                    &assertions,
                    &mut count_inner,
                )
                .unwrap();
            }
            RegistryKind::FreshDef => {
                FreshDefRegistry::collect_with_progress(
                    &proof,
                    &terms,
                    Some(&assertions),
                    &mut count_inner,
                )
                .unwrap();
            }
        }
        let mut trace = Vec::new();
        check_proof_strict_with_context_and_progress(
            &proof,
            &terms,
            None,
            None,
            Some(&assertions),
            &mut |work, bytes| {
                trace.push((work, bytes));
                true
            },
        )
        .unwrap();
        // The fixture's nonzero aggregate reservation uniquely locates this
        // registry, avoiding test-only production hooks. All of its actual
        // inner polls must follow it. Reverting the call to `collect` removes
        // these zero-charge events and fails this assertion.
        let positions: Vec<_> = trace
            .iter()
            .enumerate()
            .filter_map(|(index, charge)| (*charge == reservation).then_some(index))
            .collect();
        assert_eq!(positions.len(), 1);
        let start = positions[0] + 1;
        assert!(inner_polls > 3);
        assert_eq!(
            &trace[start..start + inner_polls],
            vec![(0, 0); inner_polls]
        );
        // Refuse inside the identified collector, not only at its entry or at
        // an unrelated offline phase. No later callback may run.
        let stop = start + 3;
        let mut calls = 0;
        let result = check_proof_strict_with_context_and_progress(
            &proof,
            &terms,
            None,
            None,
            Some(&assertions),
            &mut |_, _| {
                calls += 1;
                calls != stop
            },
        );
        assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(calls, stop);
    }
}

#[test]
fn offline_reader_keeps_unused_registry_introductions_fail_closed() {
    for kind in [RegistryKind::ExtDiff, RegistryKind::FreshDef] {
        let (terms, mut proof, assertions) = registry_fixture(kind);
        let ProofStep::Step { args, .. } = &mut proof.steps[0] else {
            panic!("fixture introduction");
        };
        args.clear();
        let bundle = SerializableProofBundle::from_proof(&proof, &terms, assertions);
        let expected = re_check_bundle_strict(&bundle).unwrap_err().to_string();
        let actual = re_check_bundle_strict_with_cancellation(&bundle, &mut || true)
            .unwrap_err()
            .to_string();
        assert_eq!(actual, expected);
        assert!(matches!(
            re_check_bundle_strict_with_cancellation(&bundle, &mut || false),
            Err(ProofCheckError::ResourceLimit)
        ));
    }
}

/// A `divmod_def` binds TWO symbols, and a proof whose only fresh definitions
/// are `divmod_def` steps must still debit the registry's traversals: without
/// the arm, `bounds == 0` returns the free `(steps, 0)` reservation.
#[test]
fn a_divmod_def_only_proof_debits_the_registry_for_both_bindings() {
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::DivModDef, vec![], vec![], vec![]);
    let payload = sample_payload();
    let (work, bytes) = fresh_def_registry_charge(&proof, payload, &mut |_, _| true).unwrap();
    assert_eq!(work, 2 * payload.work + proof.steps.len());
    assert_eq!(bytes, 2 * payload.bytes + 2 * 128);
}
