// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

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
    let result =
        executor.run_partition_components(&components, &[], &roots, &mut |executor, component| {
            assert_eq!(component, components[visits].as_slice());
            visits += 1;
            if visits == 1 {
                executor.record_unknown_from_origin(UnknownOrigin::IncompleteSolverLane);
                Ok(SolveResult::Unknown)
            } else {
                // This is a loop-policy control, not a solver/proof fixture.
                Ok(SolveResult::unsat())
            }
        });
    assert!(matches!(result, Some(Ok(SolveResult::Unsat(_)))));
    assert_eq!(visits, 2);
    assert_eq!(executor.ctx.assertions, roots);
    assert_eq!(executor.last_unknown_reason, None);
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
