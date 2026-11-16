// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use super::*;
use crate::executor_types::UnknownOrigin;

fn fixture() -> (Executor, Vec<TermId>, Vec<Vec<TermId>>) {
    let mut executor = Executor::new();
    let left = executor.ctx.terms.mk_var("partition_left", Sort::Bool);
    let right = executor.ctx.terms.mk_var("partition_right", Sort::Bool);
    let roots = vec![left, right];
    executor.ctx.assertions = roots.clone();
    executor.last_result = Some(SolveResult::Unknown);
    executor.record_unknown_from_origin(UnknownOrigin::IncompleteSolverLane);
    assert!(executor.finite_array_expansion.is_complete());
    (executor, roots, vec![vec![left], vec![right]])
}

#[test]
fn recorded_component_resource_stop_survives_restore_without_visiting_the_next_component() {
    for origin in [
        UnknownOrigin::DeterministicResourceBudget,
        UnknownOrigin::MemoryBudget,
        UnknownOrigin::InterruptFlag,
        UnknownOrigin::SolveDeadline,
    ] {
        let (mut executor, roots, components) = fixture();
        executor.skip_model_eval = true;
        executor.defer_model_validation = true;
        executor.last_model_validated = true;
        executor.last_assumption_core = Some(roots.clone());
        let mut visits = 0;
        let result = executor.run_partition_components(
            &components,
            &[],
            &roots,
            &mut RescueTally::default(),
            &mut |executor, component| {
                visits += 1;
                assert_eq!(visits, 1, "a recorded stop must end the component loop");
                assert_eq!(component, components[0].as_slice());
                // Model the isolated component window and its ordinary restore.
                // No live stop remains for the outer loop to rediscover.
                let saved = std::mem::replace(&mut executor.ctx.assertions, component.to_vec());
                executor.skip_model_eval = false;
                executor.defer_model_validation = false;
                executor.publish_unknown_from_origin(origin);
                executor.ctx.assertions = saved;
                assert!(executor.external_stop_reason().is_none());
                assert!(!executor.solve_deadline.expired());
                Ok(SolveResult::Unknown)
            },
        );
        assert!(matches!(result, Some(Ok(SolveResult::Unknown))));
        assert_eq!(visits, 1);
        assert_eq!(executor.ctx.assertions, roots);
        assert_eq!(executor.last_unknown_reason, Some(origin.reason()));
        assert_eq!(executor.unknown_origin(), Some(origin));
        assert!(matches!(executor.last_result, Some(SolveResult::Unknown)));
        assert!(executor.skip_model_eval);
        assert!(executor.defer_model_validation);
        assert!(executor.last_model.is_none());
        assert!(!executor.last_model_validated);
        assert!(executor.last_assumption_core.is_none());
    }
}

#[test]
fn ordinary_incomplete_component_still_allows_a_later_subset_refutation() {
    let (mut executor, roots, components) = fixture();
    let mut visits = 0;
    let result = executor.run_partition_components(
        &components,
        &[],
        &roots,
        &mut RescueTally::default(),
        &mut |executor, component| {
            assert_eq!(component, components[visits].as_slice());
            visits += 1;
            if visits == 1 {
                executor.record_unknown_from_origin(UnknownOrigin::IncompleteSolverLane);
                Ok(SolveResult::Unknown)
            } else {
                // This is a loop-policy control, not a solver/proof fixture.
                Ok(SolveResult::unsat())
            }
        },
    );
    assert!(matches!(result, Some(Ok(SolveResult::Unsat(_)))));
    assert_eq!(visits, 2);
    assert_eq!(executor.ctx.assertions, roots);
    assert_eq!(executor.last_unknown_reason, None);
}

/// The first component spends 9 work units and ends Incomplete; the second
/// spends 3 and returns `unsat` with no proof installed. Both are counted as
/// visited and in the total; only the second is in the decided maximum, and
/// none of `borrowed_rows`, `unowned_premises` and `borrow_lender` is
/// written.
#[test]
fn the_tally_counts_every_visited_component_and_only_decided_ones_in_the_maximum() {
    let (mut executor, roots, components) = fixture();
    let mut tally = RescueTally::default();
    let mut visits = 0;
    let result = executor.run_partition_components(
        &components,
        &[],
        &roots,
        &mut tally,
        &mut |executor, _component| {
            visits += 1;
            if visits == 1 {
                ay_core::resource::work().add_sat_work(9, 0);
                executor.record_unknown_from_origin(UnknownOrigin::IncompleteSolverLane);
                Ok(SolveResult::Unknown)
            } else {
                ay_core::resource::work().add_sat_work(3, 0);
                Ok(SolveResult::unsat())
            }
        },
    );
    assert!(matches!(result, Some(Ok(SolveResult::Unsat(_)))));
    executor.record_rescue_tally(&tally, &[]);
    let statistics = executor.statistics();
    assert_eq!(
        statistics.get_int("solver.partition_rescue.components_visited"),
        Some(2)
    );
    assert_eq!(
        statistics.get_int("solver.partition_rescue.component_work_total"),
        Some(12)
    );
    assert_eq!(
        statistics.get_int("solver.partition_rescue.component_work_max"),
        Some(3)
    );
    for key in [
        "solver.partition_rescue.borrowed_rows",
        "solver.partition_rescue.unowned_premises",
        "solver.partition_rescue.borrow_lender",
    ] {
        assert_eq!(statistics.get_int(key), None, "{key}");
    }
}

/// The first component spends 5 work units, then raises a live stop (the
/// interrupt flag in one run, an expired solve deadline in the other) and
/// returns `unsat`. It is counted as visited and in the total, and no
/// `component_work_max` is written.
#[test]
fn a_component_that_returns_under_a_live_stop_is_not_in_the_decided_maximum() {
    for raise_interrupt in [true, false] {
        let (mut executor, roots, components) = fixture();
        let interrupt = Arc::new(AtomicBool::new(false));
        executor.set_interrupt(Arc::clone(&interrupt));
        let mut tally = RescueTally::default();
        let result = executor.run_partition_components(
            &components,
            &[],
            &roots,
            &mut tally,
            &mut |executor, _component| {
                ay_core::resource::work().add_sat_work(5, 0);
                if raise_interrupt {
                    interrupt.store(true, Ordering::Relaxed);
                } else {
                    executor.solve_deadline.set(Some(Instant::now()));
                }
                Ok(SolveResult::unsat())
            },
        );
        assert!(matches!(result, Some(Ok(SolveResult::Unsat(_)))));
        executor.record_rescue_tally(&tally, &[]);
        let statistics = executor.statistics();
        assert_eq!(
            statistics.get_int("solver.partition_rescue.components_visited"),
            Some(1),
            "raise_interrupt={raise_interrupt}"
        );
        assert_eq!(
            statistics.get_int("solver.partition_rescue.component_work_total"),
            Some(5),
            "raise_interrupt={raise_interrupt}"
        );
        assert_eq!(
            statistics.get_int("solver.partition_rescue.component_work_max"),
            None,
            "raise_interrupt={raise_interrupt}"
        );
    }
}

#[test]
fn primary_resource_unknown_never_enters_partition_rescue() {
    let (mut executor, roots, _) = fixture();
    assert!(executor.partition_rescue_firing_gate(&roots));
    for origin in [
        UnknownOrigin::DeterministicResourceBudget,
        UnknownOrigin::MemoryBudget,
        UnknownOrigin::InterruptFlag,
        UnknownOrigin::SolveDeadline,
    ] {
        executor.publish_unknown_from_origin(origin);
        assert!(!executor.partition_rescue_firing_gate(&roots));
        assert!(matches!(
            executor.try_partition_rescue(Ok(SolveResult::Unknown), &roots),
            Ok(SolveResult::Unknown)
        ));
        assert_eq!(executor.unknown_origin(), Some(origin));
        assert_eq!(executor.ctx.assertions, roots);
    }
}
