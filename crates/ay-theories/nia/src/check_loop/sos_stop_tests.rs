// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::Duration;

use ay_core::resource::{
    enter_check_stop, ChildSpec, DeadlineSource, Guard, LiveDeadline, NodeLabel,
};
use ay_core::term::{TermId, TermStore};
use ay_core::time::Instant;
use ay_core::{Sort, TheoryResult, TheorySolver};
use num_bigint::BigInt;

use crate::NiaSolver;

fn nonlinear_atom(terms: &mut TermStore) -> TermId {
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let difference = terms.mk_sub(vec![x, y]);
    let square = terms.mk_mul(vec![difference, difference]);
    let zero = terms.mk_int(BigInt::from(0));
    terms.mk_lt(square, zero)
}

fn solver<'a>(terms: &'a TermStore, atoms: &[TermId]) -> NiaSolver<'a> {
    let mut solver = NiaSolver::new(terms);
    for &atom in atoms {
        solver.assert_literal(atom, true);
    }
    solver
}

#[test]
fn expired_explicit_deadline_stops_decision_and_attachment() {
    let mut terms = TermStore::new();
    let atom = nonlinear_atom(&mut terms);
    let mut solver = solver(&terms, &[atom]);
    solver.set_deadline(Instant::now());
    assert!(matches!(
        solver.try_sos_positivstellensatz_unsat(),
        Some(TheoryResult::Unknown)
    ));
    assert!(solver.try_build_unsat_sos_certificate().is_none());
    assert!(!solver.took_sos_unsat_certificate());

    solver.set_deadline(Instant::now() + Duration::from_secs(3600));
    assert!(matches!(
        solver.try_sos_positivstellensatz_unsat(),
        Some(TheoryResult::Unsat(_))
    ));
    assert!(solver.took_sos_unsat_certificate());
}

#[test]
fn a_moved_live_deadline_permits_a_fresh_attempt_without_latching_the_guard() {
    let mut terms = TermStore::new();
    let atom = nonlinear_atom(&mut terms);
    let mut solver = solver(&terms, &[atom]);
    let deadline = LiveDeadline::new(Some(Instant::now()));
    let check = Guard::root_child(
        ChildSpec::new(NodeLabel::Check).with_deadline(DeadlineSource::Live(deadline.clone())),
    );
    let _scope = check.enter();
    assert!(matches!(
        solver.try_sos_positivstellensatz_unsat(),
        Some(TheoryResult::Unknown)
    ));
    assert!(solver.try_build_unsat_sos_certificate().is_none());
    assert_eq!(check.stopped(), None);
    deadline.set(Some(Instant::now() + Duration::from_secs(3600)));
    assert!(matches!(
        solver.try_sos_positivstellensatz_unsat(),
        Some(TheoryResult::Unsat(_))
    ));
    assert!(solver.took_sos_unsat_certificate());
}

#[test]
fn a_one_shot_stop_in_sos_cannot_fall_through_to_other_solver_work() {
    let mut terms = TermStore::new();
    let atom = nonlinear_atom(&mut terms);
    let mut solver = solver(&terms, &[atom]);
    let calls = Arc::new(AtomicUsize::new(0));
    let scope = enter_check_stop({
        let calls = Arc::clone(&calls);
        Arc::new(move || calls.fetch_add(1, Ordering::Relaxed) == 2)
    });
    assert!(matches!(solver.nia_check_loop(), TheoryResult::Unknown));
    assert_eq!(
        calls.load(Ordering::Relaxed),
        3,
        "no fallback after the observed SOS stop"
    );
    assert!(!solver.took_sos_unsat_certificate());
    assert_eq!(solver.conflict_count, 0);
    drop(scope);

    assert!(matches!(solver.nia_check_loop(), TheoryResult::Unsat(_)));
    assert!(solver.took_sos_unsat_certificate());
}

#[test]
fn stopped_optional_attachment_preserves_an_independently_established_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let square = terms.mk_mul(vec![x, x]);
    let two = terms.mk_int(BigInt::from(2));
    // The integer root procedure refutes this before SOS. Over the reals it
    // is satisfiable, so the independent SOS checker cannot certify it.
    let atoms = [terms.mk_eq(square, two)];
    let polls = Arc::new(AtomicUsize::new(0));
    let counting = enter_check_stop({
        let polls = Arc::clone(&polls);
        Arc::new(move || {
            polls.fetch_add(1, Ordering::Relaxed);
            false
        })
    });
    let mut baseline = solver(&terms, &atoms);
    let expected = baseline.nia_check_loop_inner();
    assert!(matches!(expected, TheoryResult::Unsat(_)), "{expected:?}");
    assert!(!baseline.took_sos_unsat_certificate());
    let inner_polls = polls.load(Ordering::Relaxed);
    drop(counting);

    let calls = Arc::new(AtomicUsize::new(0));
    let _scope = enter_check_stop({
        let calls = Arc::clone(&calls);
        Arc::new(move || calls.fetch_add(1, Ordering::Relaxed) >= inner_polls)
    });
    let mut candidate = solver(&terms, &atoms);
    let actual = candidate.nia_check_loop();
    assert!(calls.load(Ordering::Relaxed) > inner_polls);
    match (actual, expected) {
        (TheoryResult::Unsat(actual), TheoryResult::Unsat(expected)) => {
            assert_eq!(actual, expected)
        }
        (actual, expected) => {
            panic!("attachment changed the established verdict: {actual:?}, {expected:?}")
        }
    }
    assert!(!candidate.took_sos_unsat_certificate());
}

#[test]
fn a_cancelled_new_check_cannot_reuse_a_previous_sos_certificate() {
    let mut terms = TermStore::new();
    let atom = nonlinear_atom(&mut terms);
    let mut solver = solver(&terms, &[atom]);
    assert!(matches!(solver.check(), TheoryResult::Unsat(_)));
    assert!(solver.took_sos_unsat_certificate());
    {
        let check = Guard::root_child(ChildSpec::new(NodeLabel::Check));
        check.cancel();
        let _scope = check.enter();
        assert!(matches!(solver.check(), TheoryResult::Unknown));
        assert!(!solver.took_sos_unsat_certificate());
    }
    assert!(matches!(solver.check(), TheoryResult::Unsat(_)));
    assert!(solver.took_sos_unsat_certificate());
}
