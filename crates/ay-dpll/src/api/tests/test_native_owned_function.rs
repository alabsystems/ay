// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::api::*;

#[test]
fn native_owned_function_collision_preserves_original_model_and_meaning() {
    let mut solver = Solver::new(Logic::All);
    let predicate = solver
        .try_declare_new_fun("owned_predicate", &[Sort::Int], Sort::Bool)
        .unwrap();
    let zero = solver.int_const(0);
    let application = solver.try_apply(&predicate, &[zero]).unwrap();
    solver.assert_term(application);
    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_sat() && details.result.was_model_validated(),
        "{details:?}"
    );
    let events = solver.native_replay_events().len();
    assert!(solver
        .try_declare_new_fun("owned_predicate", &[Sort::Int], Sort::Bool)
        .is_err());
    assert_eq!(solver.native_replay_events().len(), events);
    assert!(
        solver.model().is_some(),
        "a refused declaration must not invalidate the model"
    );
    let application_again = solver.try_apply(&predicate, &[zero]).unwrap();
    assert_eq!(application_again, application);
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    let replay = Solver::replay_native_replay_artifact(&artifact).unwrap();
    assert!(
        replay.result.is_sat() && replay.result.was_model_validated(),
        "{replay:?}"
    );
}

#[test]
fn native_owned_function_refuses_datatype_definition_constant_and_builtin_adoption() {
    let mut solver = Solver::new(Logic::All);
    let datatype = DatatypeSort::new(
        "OwnedPayload",
        vec![DatatypeConstructor::new(
            "owned_payload_make",
            vec![DatatypeField::new("owned_payload_get", Sort::Int)],
        )],
    );
    solver.try_declare_datatypes(&[datatype.clone()]).unwrap();
    let sort = Sort::Datatype(datatype);
    let events = solver.native_replay_events().len();
    assert!(solver
        .try_declare_new_fun("owned_payload_make", &[Sort::Int], sort.clone())
        .is_err());
    assert!(solver
        .try_declare_new_fun("owned_payload_get", &[sort], Sort::Int)
        .is_err());
    assert_eq!(solver.native_replay_events().len(), events);
    solver.declare_const("owned_constant", Sort::Int);
    assert!(solver
        .try_declare_new_fun("owned_constant", &[], Sort::Int)
        .is_err());
    let setup = ay_frontend::parse("(define-fun owned_definition ((x Int)) Int (+ x 1))").unwrap();
    solver.executor.execute_all(&setup).unwrap();
    assert!(solver
        .try_declare_new_fun("owned_definition", &[Sort::Int], Sort::Int)
        .is_err());
    let events = solver.native_replay_events().len();
    for name in [
        "",
        "and",
        "=",
        "+",
        "select",
        "forall",
        "exists",
        "let",
        "match",
        "choice",
        "step",
        "__ay_private",
    ] {
        assert!(
            solver
                .try_declare_new_fun(name, &[Sort::Int], Sort::Int)
                .is_err(),
            "{name}"
        );
    }
    assert_eq!(solver.native_replay_events().len(), events);
}

#[test]
fn native_owned_function_global_scope_and_strict_original_replay() {
    let mut solver = Solver::new(Logic::All);
    solver.push();
    let predicate = solver
        .try_declare_new_fun("owned_scoped_predicate", &[Sort::Int], Sort::Bool)
        .unwrap();
    solver.pop();
    assert!(solver
        .try_declare_new_fun("owned_scoped_predicate", &[Sort::Int], Sort::Bool)
        .is_err());
    let one = solver.int_const(1);
    let application = solver.try_apply(&predicate, &[one]).unwrap();
    let opposite = solver.not(application);
    solver.assert_term(application);
    solver.assert_term(opposite);
    let artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
    let (details, proof) = Solver::replay_native_replay_artifact_with_checked_proof(
        &artifact,
        std::time::Duration::from_secs(5),
    )
    .unwrap();
    assert!(details.result.is_unsat(), "{details:?}");
    let proof = proof.expect("strict owned-function proof");
    proof
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .unwrap();
    assert_eq!(proof.quality.trust_count, 0);
    assert_eq!(proof.quality.hole_count, 0);
    let problem = proof
        .alethe_problem_smt2
        .as_ref()
        .expect("original scoped problem");
    assert!(problem.contains("owned_scoped_predicate"));
    super::test_native_datatype_batch::check_whole_paired_document(
        problem,
        &proof.alethe,
        &proof.carcara_surface,
    );
}
