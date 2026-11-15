// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use std::cell::Cell;

mod lifting;

fn boolean_cfg() -> (ChcProblem, PredicateId, PredicateId, ChcVar) {
    let mut problem = ChcProblem::new();
    let header = problem.declare_predicate("header", vec![ChcSort::Bool]);
    let body = problem.declare_predicate("body", vec![ChcSort::Bool]);
    let x = ChcVar::new("x", ChcSort::Bool);
    let var = ChcExpr::var(x.clone());
    let neg = ChcExpr::Op(ChcOp::Not, vec![Arc::new(var.clone())]);
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(header, vec![ChcExpr::Bool(false)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(header, vec![var.clone()])]),
        ClauseHead::Predicate(body, vec![neg.clone()]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(body, vec![var.clone()])]),
        ClauseHead::Predicate(header, vec![neg]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(header, vec![var.clone()])], Some(var)),
        ClauseHead::False,
    ));
    (problem, header, body, x)
}

fn deadline() -> ay_core::time::Instant {
    ay_core::time::Instant::now() + Duration::from_secs(60)
}

#[test]
fn lowering_every_callback_refuses_without_partial_transition_system() {
    let (problem, header, _, _) = boolean_cfg();
    let calls = Cell::new(0);
    let mut callback = || {
        calls.set(calls.get() + 1);
        true
    };
    let control = Control::new(deadline(), &mut callback);
    let baseline =
        lower_loop_controlled(&problem, BlastWidth::new(8), &control).expect("Boolean CFG lowers");
    assert_eq!(baseline.orig_header, Some(header));
    assert_eq!(baseline.ts.num_state_vars, 1);
    assert!(!baseline.ts.init_clauses.is_empty());
    assert!(!baseline.ts.trans_clauses.is_empty());
    let full = calls.get();
    assert!(full > 30, "actual linearization and encoding traversals");
    for stop in 1..=full {
        let count = Cell::new(0);
        let mut refusal = || {
            count.set(count.get() + 1);
            count.get() != stop
        };
        let control = Control::new(deadline(), &mut refusal);
        assert!(
            lower_loop_controlled(&problem, BlastWidth::new(8), &control).is_none(),
            "poll {stop}"
        );
        assert_eq!(count.get(), stop);
        assert!(control.stopped());
        assert!(lower_loop_controlled(&problem, BlastWidth::new(8), &control).is_none());
        assert_eq!(count.get(), stop);
    }
    let fresh = lower_loop(&problem, BlastWidth::new(8)).expect("fresh attempt remains supported");
    assert_eq!(fresh.ts.init_clauses, baseline.ts.init_clauses);
    assert_eq!(fresh.ts.trans_clauses, baseline.ts.trans_clauses);
    assert_eq!(fresh.ts.bad_literals, baseline.ts.bad_literals);
    assert_eq!(fresh.ts.total_vars, baseline.ts.total_vars);
}

#[test]
fn completed_lowering_is_discarded_when_final_callback_expires() {
    let (problem, _, _, _) = boolean_cfg();
    let calls = Cell::new(0);
    let mut count = || {
        calls.set(calls.get() + 1);
        true
    };
    assert!(lower_loop_controlled(
        &problem,
        BlastWidth::new(8),
        &Control::new(deadline(), &mut count)
    )
    .is_some());
    let final_poll = calls.get();
    let start = ay_core::time::Instant::now();
    let end = start + Duration::from_secs(60);
    let now = Cell::new(start);
    let clock = || now.get();
    calls.set(0);
    let mut expire = || {
        calls.set(calls.get() + 1);
        if calls.get() == final_poll {
            now.set(end);
        }
        true
    };
    let control = Control::with_clock(end, &mut expire, &clock);
    assert!(lower_loop_controlled(&problem, BlastWidth::new(8), &control).is_none());
    assert_eq!(calls.get(), final_poll);
    assert!(control.stopped());
}

#[test]
fn public_zero_and_overflowing_timeout_decline_before_solver() {
    let (problem, _, _, _) = boolean_cfg();
    assert!(try_prove_chc_loop(&problem, Duration::ZERO).is_none());
    assert!(try_prove_chc_loop(&problem, Duration::MAX).is_none());
}

#[test]
fn non_equality_conjuncts_are_polled_during_each_elimination_scan() {
    let n = 128;
    let atoms = vec![ChcExpr::Bool(true); n];
    let expr = ChcExpr::Op(ChcOp::And, atoms.into_iter().map(Arc::new).collect());
    let calls = Cell::new(0);
    let mut callback = || {
        calls.set(calls.get() + 1);
        true
    };
    let control = Control::new(deadline(), &mut callback);
    assert!(resolve_temps_to_args(&expr, &HashSet::new(), &control).is_some());
    // Entry, iterative root+edges+leaves+final, outer round, every skipped atom,
    // and final result admission. Non-Eq atoms cannot bypass the scan poll.
    assert_eq!(calls.get(), 3 * n + 5);
}
