// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Live Check controls must reach NIA's checked SOS path, not just LIA.
use crate::NiaSolver;
use ay_core::resource::{self, ChildSpec, DeadlineSource, Guard, NodeLabel};
use ay_core::term::{TermId, TermStore};
use ay_core::{Sort, TheoryResult, TheorySolver};
use num_bigint::BigInt;
use std::time::{Duration, Instant};

fn expired_deadline() -> Instant {
    Instant::now()
        .checked_sub(Duration::from_secs(1))
        .expect("one second before now must be representable for expired-deadline setup")
}

fn contradiction() -> (TermStore, TermId) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let difference = terms.mk_sub(vec![x, y]);
    let square = terms.mk_mul(vec![difference, difference]);
    let zero = terms.mk_int(BigInt::from(0));
    let atom = terms.mk_lt(square, zero);
    (terms, atom)
}

#[test]
fn shared_expired_deadline_stops_despite_a_future_solver_deadline() {
    let (terms, atom) = contradiction();
    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(atom, true);
    solver.set_deadline(Instant::now() + Duration::from_secs(60));
    let guard = Guard::root_child(
        ChildSpec::new(NodeLabel::Check).with_deadline(DeadlineSource::Fixed(expired_deadline())),
    );
    let _scope = guard.enter();
    assert!(resource::check_stop_requested());
    assert!(matches!(solver.check(), TheoryResult::Unknown));
    assert!(!solver.took_sos_unsat_certificate());
    assert!(solver.try_build_unsat_sos_certificate().is_none());
}

#[test]
fn shared_cancel_stops_a_solver_without_an_own_deadline() {
    let (terms, atom) = contradiction();
    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(atom, true);
    let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check));
    guard.cancel();
    let _scope = guard.enter();
    assert!(resource::check_stop_requested());
    assert!(matches!(solver.check(), TheoryResult::Unknown));
    assert!(!solver.took_sos_unsat_certificate());
    assert!(solver.try_build_unsat_sos_certificate().is_none());
}

#[test]
fn spent_grant_stops_and_dropping_it_allows_a_fresh_checked_attempt() {
    let (terms, atom) = contradiction();
    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(atom, true);
    let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check));
    let _scope = guard.enter();
    let grant = resource::enter_work_grant(0);
    resource::work().note_round_trip();
    assert!(resource::work_grant_spent());
    assert!(matches!(solver.check(), TheoryResult::Unknown));
    assert!(!solver.took_sos_unsat_certificate());
    drop(grant);
    assert!(!resource::check_stop_requested());
    assert!(matches!(solver.check(), TheoryResult::Unsat(_)));
    assert!(solver.took_sos_unsat_certificate());
}

#[test]
fn own_expired_deadline_still_stops_without_a_shared_stop() {
    let (terms, atom) = contradiction();
    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(atom, true);
    solver.set_deadline(expired_deadline());
    assert!(!resource::check_stop_requested());
    assert!(matches!(solver.check(), TheoryResult::Unknown));
    assert!(!solver.took_sos_unsat_certificate());
}

#[test]
fn one_shot_shared_stop_cannot_resume_the_outer_cascade() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;

    let (terms, atom) = contradiction();
    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(atom, true);
    let polls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&polls);
    // The first two outer polls allow the exact pre-phases. The seventh
    // callback refuses inside SOS, then would allow subsequent work again.
    const STOP_AT: usize = 7;
    let _scope = resource::enter_check_stop(Arc::new(move || {
        observed.fetch_add(1, Ordering::SeqCst) + 1 == STOP_AT
    }));
    let result = solver.check();
    assert!(matches!(result, TheoryResult::Unknown));
    assert!(!solver.took_sos_unsat_certificate());
    assert_eq!(
        polls.load(Ordering::SeqCst),
        STOP_AT,
        "SOS refusal must reach the caller without consulting the cleared stop again"
    );
}
