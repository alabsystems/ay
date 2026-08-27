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
    executor.pareto_state = Some(optimization::ParetoState::default());

    executor.reset();

    assert!(executor.last_result.is_none());
    assert!(executor.last_model.is_none());
    assert!(executor.last_sat_certificate.is_none());
    assert!(executor.last_lrat_certificate.is_none());
    assert!(executor.last_proof_rebuild_originals.is_empty());
    assert!(executor.pareto_state.is_none());
    assert_eq!(executor.solve_deadline.get(), None);
    assert_eq!(executor.certification_deadline.get(), None);
}
