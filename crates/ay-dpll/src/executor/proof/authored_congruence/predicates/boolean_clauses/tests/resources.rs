// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::time::Instant;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};
use std::time::Duration;

#[test]
fn conditional_full_65_app_attempts_share_exact_work_and_commit_limits() {
    for source in [activated(), both_branches()] {
        let (outcome, _, measured) = with_budget(&source, MAX_WORK, 0);
        assert_eq!(outcome, Outcome::Committed);
        assert_eq!(measured.checks, 1);
        let used = MAX_WORK - measured.work;
        assert!(
            used > 0 && used < MAX_WORK,
            "actual metered full fixture cost {used}"
        );
        let (outcome, _, exact) = with_budget(&source, used, 0);
        assert_eq!(outcome, Outcome::Committed);
        assert_eq!(exact.work, 0);
        assert_eq!(with_budget(&source, used - 1, 0).0, Outcome::Declined);
        assert_eq!(with_budget(&source, 0, 0).0, Outcome::Declined);
        let (outcome, _, last) = with_budget(&source, MAX_WORK, MAX_COMMIT_ATTEMPTS - 1);
        assert_eq!(outcome, Outcome::Committed);
        assert_eq!(last.checks, MAX_COMMIT_ATTEMPTS);
        let (outcome, _, exhausted) = with_budget(&source, MAX_WORK, MAX_COMMIT_ATTEMPTS);
        assert_eq!(outcome, Outcome::Declined);
        assert_eq!(exhausted.checks, MAX_COMMIT_ATTEMPTS);

        let mut executor = parsed(&source);
        let (roots, equalities) = scope(&executor);
        let mut conditional_only = Attempt::new();
        let nans =
            equality_evidence::collect(&mut executor, &roots, &mut conditional_only).unwrap();
        assert_eq!(
            executor.try_authored_binary_predicates(
                &mut Proof::new(),
                &roots,
                &equalities,
                &nans,
                &mut conditional_only,
            ),
            Outcome::Committed
        );
        assert!(
            used >= MAX_WORK - conditional_only.work + roots.len(),
            "the direct arm's root census must not reset before conditional continuation"
        );
    }
}

#[test]
fn conditional_stops_remain_terminal_after_collection_and_live_flag_recovery() {
    let mut executor = parsed(&both_branches());
    let (roots, equalities) = scope(&executor);
    let mut attempt = Attempt::new();
    let inputs = Inputs::collect(&mut executor, &roots, &mut attempt).unwrap();
    let nans = equality_evidence::collect(&mut executor, &roots, &mut attempt).unwrap();
    assert_eq!(inputs.atoms.len(), 3);
    let interrupt = Arc::new(AtomicBool::new(true));
    executor.set_interrupt(interrupt.clone());
    let mut proof = Proof::new();
    assert_eq!(
        executor.try_authored_binary_predicates(
            &mut proof,
            &roots,
            &equalities,
            &nans,
            &mut attempt,
        ),
        Outcome::Stopped
    );
    interrupt.store(false, Ordering::Relaxed);
    assert_eq!(
        executor.try_authored_predicate_with_attempt(
            &mut proof,
            &roots,
            &equalities,
            &mut Attempt::new(),
        ),
        Outcome::Stopped
    );
    assert_eq!(proof.steps, [] as [ProofStep; 0]);
    for origin in [
        UnknownOrigin::SolveDeadline,
        UnknownOrigin::MemoryBudget,
        UnknownOrigin::DeterministicResourceBudget,
    ] {
        let mut executor = parsed(&both_branches());
        let (roots, equalities) = scope(&executor);
        executor.record_unknown_from_origin(origin);
        assert_eq!(
            executor.try_authored_predicate_with_attempt(
                &mut proof,
                &roots,
                &equalities,
                &mut Attempt::new(),
            ),
            Outcome::Stopped
        );
    }
    let mut executor = parsed(&both_branches());
    let (roots, equalities) = scope(&executor);
    executor.set_deadline(Some(
        Instant::now()
            .checked_sub(Duration::from_secs(1))
            .expect("the monotonic clock can represent one second ago"),
    ));
    assert_eq!(
        executor.try_authored_predicate_with_attempt(
            &mut proof,
            &roots,
            &equalities,
            &mut Attempt::new(),
        ),
        Outcome::Stopped
    );
    assert_eq!(proof.steps, [] as [ProofStep; 0]);
}
