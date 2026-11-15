// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used, clippy::panic)]

use super::*;
use crate::bmc::{AcyclicBranchEnumeration, AcyclicNames, BmcConfig, BmcStats};
use crate::{CancellationToken, ChcExpr, ChcProblem};
use std::cell::Cell;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::time::Duration;

fn solver() -> BmcSolver {
    BmcSolver::new(ChcProblem::new(), BmcConfig::default())
}

fn counts(stats: &BmcStats) -> [usize; 4] {
    [
        stats.safe_first_decision_requests_started,
        stats.safe_first_decision_requests_completed,
        stats.safe_first_raw_model_requests_started,
        stats.safe_first_raw_model_requests_completed,
    ]
}

// Every caller below forces a pre-SMT refusal or a syntactically false branch.
// There is deliberately no injectable backend or real solver call in these tests.
fn preflight_branch(
    solver: &BmcSolver,
    expression: ChcExpr,
    deadline: ay_core::time::Instant,
    names: &mut AcyclicNames<'_>,
) -> AcyclicBranchEnumeration {
    solver.check_acyclic_safe_first_branch(
        &[expression],
        0,
        34,
        deadline,
        ay_core::time::Instant::now(),
        &[],
        &[],
        None,
        names,
    )
}

#[test]
fn unknown_completes_a_request_without_claiming_coverage_or_holding_a_borrow() {
    let solver = solver();
    let result = solver.safe_first_smt_request(SafeFirstRequestKind::Decision, || {
        let mut stats = solver.stats.borrow_mut();
        assert_eq!(counts(&stats), [1, 0, 0, 0]);
        stats.total_time_secs = 0.25;
        SmtResult::Unknown
    });
    assert!(result.is_unknown());
    let stats = solver.stats();
    assert_eq!(counts(&stats), [1, 1, 0, 0]);
    assert_eq!(stats.num_checks, 0);
    assert_eq!(stats.total_time_secs, 0.25);
    assert!(!stats.exhausted_search);
    assert!(!stats.budget_exhausted);
}

#[test]
fn unsat_then_preparation_decline_retains_the_completed_request() {
    let solver = solver();
    let keep_going = Cell::new(true);
    let mut live = || keep_going.get();
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    assert!(solver
        .safe_first_smt_request(SafeFirstRequestKind::Decision, || SmtResult::Unsat)
        .is_unsat());
    keep_going.set(false);
    let result = preflight_branch(
        &solver,
        ChcExpr::Bool(true),
        ay_core::time::Instant::now() + Duration::from_secs(60),
        &mut names,
    );
    assert!(matches!(result, AcyclicBranchEnumeration::Unsupported));
    assert!(names.stopped());
    let stats = solver.stats();
    assert_eq!(counts(&stats), [1, 1, 0, 0]);
    assert_eq!(stats.num_checks, 0);
    assert!(!stats.exhausted_search);
}

#[test]
fn syntactic_false_makes_no_request_and_legacy_depth_updates_stay_separate() {
    let solver = solver();
    let mut live = || true;
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    assert!(matches!(
        preflight_branch(
            &solver,
            ChcExpr::Bool(false),
            ay_core::time::Instant::now() + Duration::from_secs(60),
            &mut names,
        ),
        AcyclicBranchEnumeration::Completed
    ));
    assert_eq!(counts(&solver.stats()), [0; 4]);
    solver.mark_acyclic_exhaustive_stats(34, 0.5);
    let stats = solver.stats();
    assert_eq!(stats.num_checks, 35);
    assert_eq!(stats.max_depth_reached, 34);
    assert!(stats.exhausted_search);
    assert_eq!(counts(&stats), [0; 4]);
    assert!(solver
        .safe_first_smt_request(SafeFirstRequestKind::Decision, || SmtResult::Unknown)
        .is_unknown());
    solver.record_depth(7, 0.125);
    solver.mark_acyclic_exhaustive_stats(9, 0.25);
    let stats = solver.stats();
    assert_eq!(stats.num_checks, 10);
    assert_eq!(counts(&stats), [1, 1, 0, 0]);
}

#[test]
fn cancelled_or_expired_branch_starts_no_request() {
    for cancelled in [false, true] {
        let cancellation = CancellationToken::new();
        let mut config = BmcConfig::default();
        config.base.cancellation_token = Some(cancellation.clone());
        let solver = BmcSolver::new(ChcProblem::new(), config);
        let mut live = || true;
        let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
        let now = ay_core::time::Instant::now();
        let deadline = if cancelled {
            cancellation.cancel();
            now + Duration::from_secs(60)
        } else {
            now
        };
        assert!(matches!(
            preflight_branch(&solver, ChcExpr::Bool(true), deadline, &mut names),
            AcyclicBranchEnumeration::TimedOut
        ));
        assert_eq!(counts(&solver.stats()), [0; 4]);
    }
}

#[test]
fn raw_model_requests_are_disjoint_and_preserve_returned_model_or_unknown() {
    let solver = solver();
    let mut model = crate::bmc::FxHashMap::default();
    model.insert("x".to_owned(), crate::smt::SmtValue::Int(7));
    let result = solver.safe_first_smt_request(SafeFirstRequestKind::Decision, || {
        SmtResult::Sat(model.clone())
    });
    assert_eq!(result.model(), Some(&model));
    let raw = solver.safe_first_smt_request(SafeFirstRequestKind::RawModelCompletion, || {
        assert_eq!(counts(&solver.stats()), [1, 1, 1, 0]);
        SmtResult::Unknown
    });
    assert!(raw.is_unknown());
    // This is the existing caller's fallback, not a policy in the counter helper.
    let retained = match raw {
        SmtResult::Sat(full) => full,
        _ => model.clone(),
    };
    assert_eq!(retained, model);
    let raw = solver.safe_first_smt_request(SafeFirstRequestKind::RawModelCompletion, || {
        SmtResult::Sat(model.clone())
    });
    assert_eq!(raw.model(), Some(&model));
    assert_eq!(counts(&solver.stats()), [1, 1, 2, 2]);
    assert_eq!(solver.stats().num_checks, 0);
}

#[test]
fn panic_leaves_started_greater_than_completed_and_does_not_poison_stats() {
    let solver = solver();
    for kind in [
        SafeFirstRequestKind::Decision,
        SafeFirstRequestKind::RawModelCompletion,
    ] {
        let outcome = catch_unwind(AssertUnwindSafe(|| {
            solver.safe_first_smt_request(kind, || panic!("request did not return"))
        }));
        assert!(outcome.is_err());
        assert!(solver
            .safe_first_smt_request(kind, || SmtResult::Unknown)
            .is_unknown());
    }
    assert_eq!(counts(&solver.stats()), [2, 1, 2, 1]);
}

#[test]
fn request_counters_saturate_and_a_new_solver_starts_empty() {
    let solver = solver();
    {
        let mut stats = solver.stats.borrow_mut();
        stats.safe_first_decision_requests_started = usize::MAX - 1;
        stats.safe_first_decision_requests_completed = usize::MAX - 1;
        stats.safe_first_raw_model_requests_started = usize::MAX - 1;
        stats.safe_first_raw_model_requests_completed = usize::MAX - 1;
    }
    for _ in 0..3 {
        for kind in [
            SafeFirstRequestKind::Decision,
            SafeFirstRequestKind::RawModelCompletion,
        ] {
            assert!(solver
                .safe_first_smt_request(kind, || SmtResult::Unknown)
                .is_unknown());
        }
    }
    assert_eq!(counts(&solver.stats()), [usize::MAX; 4]);
    let fresh = BmcSolver::new(ChcProblem::new(), BmcConfig::default());
    assert_eq!(counts(&fresh.stats()), [0; 4]);
    assert_eq!(counts(&solver.stats()), [usize::MAX; 4]);
}
