// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[test]
fn direct_reset_revokes_every_query_artifact() {
    let mut executor = Executor::new();
    let old_term = executor.ctx.terms.true_term();
    let old_deadline = ay_core::time::Instant::now() + Duration::from_mins(1);
    executor.set_deadline(Some(old_deadline));
    assert_eq!(
        executor
            .emit_sat_verdict(SolveResult::Sat, &[])
            .expect("mint a checked SAT certificate"),
        SolveResult::Sat
    );
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(Model::empty());
    executor.last_lrat_certificate = Some(vec![1]);
    executor.last_proof_rebuild_originals.push(old_term);
    executor.last_proof_raw_original_assertions.push(old_term);
    executor
        .last_proof_expanded_let_sources
        .push((old_term, 0, "(let ((x true)) x)".to_string()));
    executor.pareto_state = Some(optimization::ParetoState::default());
    executor.self_check_authored_assertions = Some(vec![old_term]);
    executor.independent_gate_authored_assertions = Some(vec![old_term]);

    executor.reset();

    assert!(executor.last_result.is_none());
    assert!(executor.last_model.is_none());
    assert!(executor.last_sat_certificate.is_none());
    assert!(executor.last_lrat_certificate.is_none());
    assert!(executor.last_proof_rebuild_originals.is_empty());
    assert!(executor.last_proof_raw_original_assertions.is_empty());
    assert!(executor.last_proof_expanded_let_sources.is_empty());
    assert!(executor.pareto_state.is_none());
    assert!(executor.self_check_authored_assertions.is_none());
    assert!(executor.independent_gate_authored_assertions.is_none());
    assert_eq!(executor.solve_deadline.get(), None);
    assert_eq!(executor.certification_deadline.get(), None);
}

#[test]
fn command_reset_revokes_solve_local_authored_windows() {
    let mut executor = Executor::new();
    let old_term = executor.ctx.terms.true_term();
    executor.self_check_authored_assertions = Some(vec![old_term]);
    executor.independent_gate_authored_assertions = Some(vec![old_term]);

    assert!(executor
        .execute(&Command::Reset)
        .expect("SMT reset executes")
        .is_none());

    assert!(executor.self_check_authored_assertions.is_none());
    assert!(executor.independent_gate_authored_assertions.is_none());
}

#[test]
fn command_reset_assertions_revokes_solve_local_authored_windows() {
    let mut executor = Executor::new();
    let old_term = executor.ctx.terms.true_term();
    executor.ctx.assertions.push(old_term);
    executor.self_check_authored_assertions = Some(vec![old_term]);
    executor.independent_gate_authored_assertions = Some(vec![old_term]);

    assert!(executor
        .execute(&Command::ResetAssertions)
        .expect("SMT reset-assertions executes")
        .is_none());

    assert!(executor.ctx.assertions.is_empty());
    assert!(executor.self_check_authored_assertions.is_none());
    assert!(executor.independent_gate_authored_assertions.is_none());
    assert!(executor.independent_gate_query_roots().is_empty());
}
