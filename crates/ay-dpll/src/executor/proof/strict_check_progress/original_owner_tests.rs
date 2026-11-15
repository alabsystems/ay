// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::api::proofs::EnvelopeStop;
use ay_core::resource::{enter_check_stop, ChildSpec, DeadlineSource, Guard, NodeLabel};
use ay_core::time::Instant;
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};

#[test]
fn stopped_explicit_original_reaches_strict_partial_revert_and_plain_walks() {
    let mut executor = Executor::new();
    let proof = tests::valid_empty_clause_proof(&mut executor);
    let _owner = enter_check_stop(Arc::new(|| true));
    assert_eq!(
        executor.check_proof_strict_derivation_with_datatypes(&proof),
        Err(ProofCheckError::Cancelled)
    );
    assert_eq!(
        executor.certification_stop.get(),
        Some(EnvelopeStop::Caller)
    );
    let partial = check_partial_with_executor_progress(&executor, &proof, WantQuality::Yes);
    assert_eq!(partial.error, Some(ProofCheckError::Cancelled));
    assert!(partial.quality.is_none());
    assert_eq!(
        check_proof_gate_with_executor_progress(&executor, &proof),
        Err(ProofCheckError::Cancelled)
    );
    assert!(executor.check_proof_strict_until_stopped(&proof).is_err());
    assert!(!executor.recognize_bv_bitblast_until_stopped(&[executor.ctx.terms.true_term()]));
}

#[test]
fn strict_walk_obeys_ancestor_deadline_and_certify_cancel_only_boundary() {
    let mut executor = Executor::new();
    let proof = tests::valid_empty_clause_proof(&mut executor);
    let search = Guard::root_child(
        ChildSpec::new(NodeLabel::Search).with_deadline(DeadlineSource::Fixed(Instant::now())),
    );
    let _search = search.enter();
    let full = search.child(ChildSpec::new(NodeLabel::Check));
    {
        let _full = full.enter();
        assert_eq!(
            executor.check_proof_strict_derivation_with_datatypes(&proof),
            Err(ProofCheckError::Cancelled)
        );
        assert_eq!(
            executor.certification_stop.get(),
            Some(EnvelopeStop::Backstop)
        );
    }
    let certify = search.child(ChildSpec::new(NodeLabel::Certify).cancel_only());
    let _certify = certify.enter();
    // A document fact under the new certification envelope does not inherit
    // the search wall. The prior refusal remains recorded for its old owner.
    assert!(executor
        .check_proof_strict_derivation_with_datatypes(&proof)
        .is_ok());
    let _original = enter_check_stop(Arc::new(|| true));
    assert_eq!(
        executor.check_proof_strict_derivation_with_datatypes(&proof),
        Err(ProofCheckError::Cancelled)
    );
}

#[test]
fn strict_guard_work_refusal_is_not_falsely_reported_as_memory() {
    let mut executor = Executor::new();
    let proof = tests::valid_empty_clause_proof(&mut executor);
    let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(0)));
    let _scope = guard.enter();
    assert_eq!(
        executor.check_proof_strict_derivation_with_datatypes(&proof),
        Err(ProofCheckError::Cancelled)
    );
    assert_eq!(
        executor.certification_stop.get(),
        Some(EnvelopeStop::WorkLimit)
    );
    let (origin, reason, _) = EnvelopeStop::WorkLimit.unknown();
    assert_eq!(origin, crate::UnknownOrigin::DeterministicResourceBudget);
    assert_eq!(reason, crate::UnknownReason::ResourceLimit);
    let (origin, reason, detail) = EnvelopeStop::Caller.unknown();
    assert_eq!(origin, crate::UnknownOrigin::UntaggedSolverUnknown);
    assert_eq!(reason, crate::UnknownReason::Unknown);
    assert!(!detail.contains("memory"));
}

#[test]
fn a_one_shot_original_stop_cannot_be_repolled_into_acceptance() {
    let mut executor = Executor::new();
    let proof = tests::valid_empty_clause_proof(&mut executor);
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = calls.clone();
    let _original = enter_check_stop(Arc::new(move || {
        observed.fetch_add(1, Ordering::SeqCst) == 0
    }));
    assert_eq!(
        executor.check_proof_strict_derivation_with_datatypes(&proof),
        Err(ProofCheckError::Cancelled)
    );
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_eq!(
        executor.certification_stop.get(),
        Some(EnvelopeStop::Caller)
    );
}
