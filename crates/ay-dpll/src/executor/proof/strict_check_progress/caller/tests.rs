// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Prepared fixture construction/trace storage is test DATA, not solver work.

use super::*;
use ay_core::original_query::{
    FiniteAdmissionGrant, OriginalAdmission, OriginalAdmissionError, QueryError,
};
use ay_core::time::Instant;
use std::cell::Cell;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

#[path = "tests/completion.rs"]
mod completion;
#[path = "tests/original_completion.rs"]
mod original_completion;
#[path = "tests/ownership.rs"]
mod ownership;

#[test]
fn borrowed_walk_retains_the_envelopes_typed_stop_after_the_signal_clears() {
    let (mut executor, proof, scope) = fixture();
    let interrupt = Arc::new(AtomicBool::new(true));
    executor.set_solve_controls(Some(Arc::clone(&interrupt)), None);
    let should_stop = executor.make_strict_check_stop();
    let mut offered = false;
    let result = check_with_caller_progress(
        &executor,
        walk(&proof, &scope),
        &should_stop,
        &mut |_, _| {
            offered = true;
            true
        },
    );
    assert!(matches!(result.0, Err(ProofCheckError::Cancelled)));
    assert!(
        !offered,
        "a stopped envelope cannot charge the original sink"
    );
    interrupt.store(false, Ordering::SeqCst);
    assert_eq!(
        executor.certification_stop.get(),
        Some(crate::api::proofs::EnvelopeStop::Interrupt)
    );
}

fn fixture() -> (Executor, Proof, Vec<TermId>) {
    let mut executor = Executor::new();
    let proof = super::super::tests::valid_empty_clause_proof(&mut executor);
    let scope = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ay_core::ProofStep::Assume(term) => Some(*term),
            _ => None,
        })
        .collect();
    (executor, proof, scope)
}

fn walk<'a>(proof: &'a Proof, scope: &'a [TermId]) -> StrictWalk<'a> {
    StrictWalk {
        proof,
        datatype_decls: None,
        selector_decls: None,
        datatype_member_signatures: &[],
        problem_assertions: Some(scope),
    }
}

fn end() -> Instant {
    Instant::now() + Duration::from_secs(20)
}

fn native_offers(
    executor: &Executor,
    proof: &Proof,
    scope: &[TermId],
    deadline: Instant,
) -> Vec<(usize, usize)> {
    let mut offers = vec![(0, 0)];
    let outcome = ay_proof::check_proof_strict_with_typed_context_and_progress(
        proof,
        &executor.ctx.terms,
        None,
        None,
        &[],
        Some(scope),
        &mut |work, bytes| {
            offers.push((work, bytes));
            Instant::now() < deadline
        },
    );
    assert!(
        outcome.is_ok(),
        "the existing checker must accept the fixture"
    );
    offers
}

fn totals(offers: &[(usize, usize)]) -> (u64, usize) {
    let work = offers.iter().map(|(work, _)| *work as u64).sum();
    let bytes = offers.iter().map(|(_, bytes)| *bytes).sum();
    (work, bytes)
}

fn owner(work: u64, bytes: usize, deadline: Instant) -> OriginalAdmission {
    OriginalAdmission::new(
        FiniteAdmissionGrant::new(work, bytes),
        deadline,
        Arc::new(|| false),
    )
}

fn owned_walk(
    owner: &OriginalAdmission,
    executor: &Executor,
    proof: &Proof,
    scope: &[TermId],
    offers: &Cell<usize>,
) -> Result<Result<ProofQuality, ProofCheckError>, OriginalAdmissionError> {
    owner.with_work(|work| {
        let should_stop = executor.make_should_stop();
        let outcome = check_with_caller_progress(
            executor,
            walk(proof, scope),
            &should_stop,
            &mut |units, bytes| {
                offers.set(offers.get() + 1);
                work.admit(units, bytes).is_ok()
            },
        )
        .0;
        // Internal allocation/local-meter refusal is not a new grant or a
        // retryable proof defect. Preserve the SAME original first latch.
        if matches!(&outcome, Err(ProofCheckError::ResourceLimit)) {
            return Err(work.refuse_exhaustion());
        }
        Ok(outcome)
    })
}

#[test]
fn borrowed_strict_walk_forwards_every_exact_offer_including_zero() {
    let deadline = end();
    let (executor, proof, scope) = fixture();
    let expected = native_offers(&executor, &proof, &scope, deadline);
    let mut actual = Vec::new();
    let outcome = check_with_caller_progress(
        &executor,
        walk(&proof, &scope),
        &|| Instant::now() >= deadline,
        &mut |work, bytes| {
            actual.push((work, bytes));
            true
        },
    );
    assert!(outcome.0.is_ok());
    assert_eq!(actual, expected);
    assert!(actual.iter().any(|offer| *offer == (0, 0)));
    assert!(actual.iter().any(|(work, _)| *work > 0));
    assert!(actual.iter().any(|(_, bytes)| *bytes > 0));
    assert_eq!(outcome.1 as u64, totals(&expected).0);
}

#[test]
fn accepting_caller_preserves_legacy_result_work_and_stop_poll_count() {
    let deadline = end();
    let (executor, proof, scope) = fixture();
    let legacy_polls = Cell::new(0);
    let legacy = check_strict_under_controls(&executor, walk(&proof, &scope), &|| {
        legacy_polls.set(legacy_polls.get() + 1);
        Instant::now() >= deadline
    });
    let caller_polls = Cell::new(0);
    let caller = check_with_caller_progress(
        &executor,
        walk(&proof, &scope),
        &|| {
            caller_polls.set(caller_polls.get() + 1);
            Instant::now() >= deadline
        },
        &mut |_, _| true,
    );
    assert_eq!(caller, legacy);
    assert!(caller.0.is_ok());
    assert_eq!(caller_polls.get(), legacy_polls.get());
}

#[test]
fn caller_refusal_at_every_offer_stops_without_another_sink_call() {
    let deadline = end();
    let (executor, proof, scope) = fixture();
    let total = native_offers(&executor, &proof, &scope, deadline).len();
    for refused_at in 0..total {
        let calls = Cell::new(0);
        let outcome = check_with_caller_progress(
            &executor,
            walk(&proof, &scope),
            &|| Instant::now() >= deadline,
            &mut |_, _| {
                let index = calls.get();
                calls.set(index + 1);
                index != refused_at
            },
        );
        assert_eq!(outcome.0, Err(ProofCheckError::ResourceLimit));
        assert_eq!(calls.get(), refused_at + 1);
    }
}

#[test]
fn borrowed_scope_authority_still_rejects_foreign_assumptions() {
    let deadline = end();
    let (executor, proof, _) = fixture();
    let foreign = [executor.ctx.terms.false_term()];
    let outcome = check_with_caller_progress(
        &executor,
        walk(&proof, &foreign),
        &|| Instant::now() >= deadline,
        &mut |_, _| true,
    )
    .0;
    assert!(matches!(
        &outcome,
        Err(ProofCheckError::UnauthorizedAssumption { .. })
    ));
    let direct = ay_proof::check_proof_strict_with_typed_context_and_progress(
        &proof,
        &executor.ctx.terms,
        None,
        None,
        &[],
        Some(&foreign),
        &mut |_, _| true,
    );
    assert_eq!(outcome, direct);
}
