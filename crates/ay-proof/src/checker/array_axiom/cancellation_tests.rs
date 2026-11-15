// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

mod graph;
mod names;

fn intro(witness: TermId, a: TermId, b: TermId) -> ProofStep {
    ProofStep::Step {
        rule: AletheRule::ArrayExtDiffIntro,
        clause: vec![],
        premises: vec![],
        args: vec![witness, a, b],
    }
}

fn basic() -> (TermStore, Proof, TermId) {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let b = terms.mk_var("b", Sort::array(Sort::Int, Sort::Int));
    let k = terms.mk_var("k", Sort::Int);
    let proof = Proof::from_steps(vec![intro(k, a, b)]);
    (terms, proof, k)
}

fn bindings(registry: &ExtDiffRegistry) -> Vec<(String, TermId, TermId, TermId, ProofId)> {
    let mut result: Vec<_> = registry
        .bindings
        .iter()
        .map(|(name, binding)| {
            (
                name.clone(),
                binding.witness,
                binding.array_a,
                binding.array_b,
                binding.step,
            )
        })
        .collect();
    result.sort_by(|left, right| left.0.cmp(&right.0));
    result
}

fn every_poll(proof: &Proof, terms: &TermStore, assertions: &[TermId]) {
    let expected = ExtDiffRegistry::collect(proof, terms, assertions);
    let mut total = 0;
    let controlled =
        ExtDiffRegistry::collect_with_progress(proof, terms, assertions, &mut |work, bytes| {
            assert_eq!(
                (work, bytes),
                (0, 0),
                "existing external accounting is not replaced"
            );
            total += 1;
            true
        });
    match (expected, controlled) {
        (Ok(expected), Ok(actual)) => assert_eq!(bindings(&actual), bindings(&expected)),
        (Err(expected), Err(actual)) => assert_eq!(actual, expected),
        (expected, actual) => panic!("live compatibility mismatch: {expected:?} / {actual:?}"),
    }
    assert!(total >= 2);
    for stop_at in 1..=total {
        let mut calls = 0;
        let result =
            ExtDiffRegistry::collect_with_progress(proof, terms, assertions, &mut |_, _| {
                calls += 1;
                calls != stop_at
            });
        assert!(
            matches!(result, Err(ProofCheckError::ResourceLimit)),
            "poll {stop_at}"
        );
        assert_eq!(
            calls, stop_at,
            "no callback or partial-registry retry after refusal"
        );
    }
}

#[test]
fn empty_and_live_registries_preserve_bindings_and_poll_every_boundary() {
    let (terms, proof, _) = basic();
    every_poll(&Proof::new(), &terms, &[]);
    every_poll(&proof, &terms, &[]);
    let expected = ExtDiffRegistry::collect(&proof, &terms, &[]).unwrap();
    let actual =
        ExtDiffRegistry::collect_with_progress(&proof, &terms, &[], &mut |_, _| true).unwrap();
    assert_eq!(bindings(&actual), bindings(&expected));
    assert_eq!(
        actual.folded_work_remaining.load(Ordering::Relaxed),
        FOLDED_REGISTRY_WORK_LIMIT
    );
}

#[test]
fn identical_and_different_duplicate_introductions_both_remain_forbidden() {
    let (mut terms, proof, k) = basic();
    let ProofStep::Step { args, .. } = &proof.steps[0] else {
        panic!("introduction fixture");
    };
    let other = terms.mk_var("other-array", terms.sort(args[1]).clone());
    for duplicate in [proof.steps[0].clone(), intro(k, args[1], other)] {
        let duplicate = Proof::from_steps(vec![proof.steps[0].clone(), duplicate]);
        let error = ExtDiffRegistry::collect(&duplicate, &terms, &[]).unwrap_err();
        assert!(
            matches!(error, ProofCheckError::InvalidTheoryLemma { step: ProofId(1), reason }
            if reason.contains("introduced more than once") && reason.contains(&format!("step {}", ProofId(0))))
        );
        every_poll(&duplicate, &terms, &[]);
    }
}

#[test]
fn malformed_introduction_is_still_rejected_and_can_be_precancelled() {
    let (terms, mut proof, _) = basic();
    let ProofStep::Step { clause, .. } = &mut proof.steps[0] else {
        panic!("introduction fixture");
    };
    clause.push(terms.true_term());
    let error = ExtDiffRegistry::collect(&proof, &terms, &[]).unwrap_err();
    assert!(
        matches!(error, ProofCheckError::InvalidTheoryLemma { reason, .. }
        if reason.contains("must conclude no clause"))
    );
    every_poll(&proof, &terms, &[]);
}

#[test]
fn fresh_attempts_do_not_reset_the_single_returned_registry_folded_allowance() {
    let (terms, proof, _) = basic();
    let registry =
        ExtDiffRegistry::collect_with_progress(&proof, &terms, &[], &mut |_, _| true).unwrap();
    registry.set_folded_work_budget_for_test(2);
    for remaining in [1, 0] {
        assert!(!validate_folded_registry_match_with_budget(
            &terms,
            ProofId(1),
            &[],
            &registry,
            &mut |_, _| true,
        )
        .unwrap());
        assert_eq!(
            registry.folded_work_remaining.load(Ordering::Relaxed),
            remaining
        );
    }
    assert!(validate_folded_registry_match_with_budget(
        &terms,
        ProofId(2),
        &[],
        &registry,
        &mut |_, _| true,
    )
    .is_err());
    assert!(matches!(
        ExtDiffRegistry::collect_with_progress(&proof, &terms, &[], &mut |_, _| false),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert_eq!(registry.folded_work_remaining.load(Ordering::Relaxed), 0);
}

#[test]
fn callback_panics_do_not_modify_proof_or_publish_a_registry() {
    let (terms, proof, _) = basic();
    let original = format!("{:?}", proof.steps);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        ExtDiffRegistry::collect_with_progress(&proof, &terms, &[], &mut |_, _| {
            std::panic::panic_any(712u32)
        })
    }));
    assert_eq!(*result.unwrap_err().downcast::<u32>().unwrap(), 712);
    assert_eq!(format!("{:?}", proof.steps), original);
    assert!(ExtDiffRegistry::collect(&proof, &terms, &[]).is_ok());
}
