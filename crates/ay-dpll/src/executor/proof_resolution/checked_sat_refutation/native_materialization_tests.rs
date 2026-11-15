// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#[cfg(test)]
fn materialized_unit_executor() -> Executor {
    let (mut executor, p) = unstamped_contradictory_unit_executor();
    let mut sat = ay_sat::Solver::new(1);
    sat.enable_clause_trace();
    sat.add_clause(vec![Literal::positive(Variable::new(0))]);
    sat.add_clause(vec![Literal::negative(Variable::new(0))]);
    assert!(sat.solve().into_inner().is_unsat());
    executor.last_clause_trace = sat.take_clause_trace();
    executor.proof_problem_assertion_provenance = Some(
        crate::executor::theories::solve_harness::ProofProblemAssertionProvenance {
            original_problem_assertions: executor.ctx.assertions.clone(),
            problem_assertions: executor.ctx.assertions.clone(),
            assertion_sources: Default::default(),
        },
    );
    executor.refresh_checked_sat_refutation();
    assert_eq!(executor.last_var_to_term.as_ref().unwrap()[&0], p);
    assert!(executor
        .last_checked_sat_refutation
        .as_ref()
        .unwrap()
        .native_proof
        .is_some());
    executor
}

#[test]
fn native_materialization_can_be_taken_once_without_consuming_verdict_authority() {
    let mut executor = materialized_unit_executor();
    let proof = executor.take_current_checked_sat_proof().unwrap();
    assert!(executor
        .check_proof_strict_with_datatypes(&proof)
        .unwrap()
        .is_complete());
    assert!(executor.take_current_checked_sat_proof().is_none());
    assert!(executor.checked_sat_refutation_authorizes_current_query());
}

#[test]
fn native_materialization_take_rechecks_epoch_source_roots_and_assumptions() {
    let mut executor = materialized_unit_executor();
    executor.query_authority_epoch = QueryAuthorityEpoch::fresh();
    assert!(executor.take_current_checked_sat_proof().is_none());
    let mut executor = materialized_unit_executor();
    executor.ctx = Context::new();
    assert!(executor.take_current_checked_sat_proof().is_none());
    let mut executor = materialized_unit_executor();
    executor
        .last_checked_sat_refutation
        .as_mut()
        .unwrap()
        .ordered_authored_roots
        .reverse();
    assert!(executor.take_current_checked_sat_proof().is_none());
    let mut executor = materialized_unit_executor();
    executor
        .last_checked_sat_refutation
        .as_mut()
        .unwrap()
        .ordered_assumptions = vec![executor.ctx.assertions[0]].into_boxed_slice();
    assert!(executor.take_current_checked_sat_proof().is_none());
}

#[test]
fn native_materialization_does_not_erase_user_assumptions_as_scope_guards() {
    let (mut executor, _, _) = assumption_dependent_unit_executor();
    assert!(executor.last_checked_sat_refutation.is_some());
    assert!(executor.take_current_checked_sat_proof().is_none());
    assert!(executor.checked_sat_refutation_authorizes_current_query());
}
