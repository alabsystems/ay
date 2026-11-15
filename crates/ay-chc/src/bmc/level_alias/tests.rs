// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::has_shared_ancestry;
use crate::bmc::{BmcConfig, BmcSolver};
use crate::{ChcEngineResult, ChcExpr, ChcProblem, ClauseBody, ClauseHead, HornClause};
use std::cell::Cell;

mod fixtures;
mod graph;
mod native;

#[test]
fn final_refusal_and_inner_refusals_never_admit_a_scan_result() {
    for problem in [
        fixtures::graph(4, &[(1, vec![0]), (2, vec![0])], &[1, 2]),
        fixtures::graph(4, &[(1, vec![0]), (3, vec![2])], &[1, 3]),
    ] {
        let polls = Cell::new(0usize);
        let expected = has_shared_ancestry(&problem, &mut || {
            polls.set(polls.get() + 1);
            true
        })
        .unwrap();
        assert!(polls.get() > 8);
        for stop in 1..=polls.get() {
            let visits = Cell::new(0usize);
            assert_eq!(
                has_shared_ancestry(&problem, &mut || {
                    visits.set(visits.get() + 1);
                    visits.get() != stop
                }),
                None,
                "stop {stop}"
            );
            assert_eq!(visits.get(), stop, "no post-refusal callback");
        }
        assert_eq!(has_shared_ancestry(&problem, &mut || true), Some(expected));
    }
}

#[test]
fn interrupted_safe_admission_clears_exhaustion_without_running_recovery() {
    let token = crate::CancellationToken::new();
    let solver = BmcSolver::new(
        fixtures::graph(4, &[(1, vec![0]), (2, vec![0])], &[1, 2]),
        BmcConfig::default().with_cancellation(token.clone()),
    );
    solver.stats.borrow_mut().exhausted_search = true;
    token.cancel();
    assert_eq!(solver.level_flat_may_alias_ancestry(), None);
    assert!(matches!(
        solver.resolve_unrepresentable_safe(ChcEngineResult::Safe(
            crate::pdr::model::InvariantModel::default()
        )),
        ChcEngineResult::Unknown
    ));
    assert!(!solver.stats().exhausted_search);
    assert!(!solver.stats().budget_exhausted);
    assert_eq!(solver.stats().num_checks, 0);

    let expired = BmcSolver::new(fixtures::graph(2, &[], &[0, 1]), BmcConfig::default());
    expired.stats.borrow_mut().exhausted_search = true;
    expired
        .solve_deadline
        .set(Some(ay_core::time::Instant::now()));
    assert!(matches!(
        expired.resolve_unrepresentable_safe(ChcEngineResult::Safe(
            crate::pdr::model::InvariantModel::default()
        )),
        ChcEngineResult::Unknown
    ));
    assert!(!expired.stats().exhausted_search);
    assert!(expired.stats().budget_exhausted);
    assert_eq!(expired.stats().num_checks, 0);
}

#[test]
fn non_safe_result_bypasses_alias_admission_scan() {
    let token = crate::CancellationToken::new();
    let solver = BmcSolver::new(
        fixtures::graph(4, &[(1, vec![0]), (2, vec![0])], &[1, 2]),
        BmcConfig::default().with_cancellation(token.clone()),
    );
    assert_eq!(solver.level_flat_may_alias_ancestry(), Some(true));
    // No fabricated Unsafe evidence is needed: non-Safe Unknown also proves
    // the alias scan is exclusive to Safe and leaves a live attempt alone.
    solver.stats.borrow_mut().exhausted_search = true;
    assert!(matches!(
        solver.resolve_unrepresentable_safe(ChcEngineResult::Unknown),
        ChcEngineResult::Unknown
    ));
    assert!(solver.stats().exhausted_search);
    assert_eq!(solver.stats().num_checks, 0);

    // Attempt-level cancellation is independent of that alias scan. Even an
    // Unknown must not retain complete-search evidence after terminal refusal.
    token.cancel();
    assert!(matches!(
        solver.resolve_unrepresentable_safe(ChcEngineResult::Unknown),
        ChcEngineResult::Unknown
    ));
    assert!(!solver.stats().exhausted_search);
    assert!(!solver.stats().budget_exhausted);
    assert_eq!(solver.stats().num_checks, 0);
    token.reset();
    assert!(matches!(
        solver.resolve_unrepresentable_safe(ChcEngineResult::Unknown),
        ChcEngineResult::Unknown
    ));
    assert!(!solver.stats().exhausted_search);
}
