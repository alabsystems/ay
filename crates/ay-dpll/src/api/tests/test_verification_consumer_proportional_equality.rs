// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native replay's first-query declaration/DAG order for the ghost-only
//! double(x)=x+x obligation. Register BOTH constants before rebuilding terms:
//! a macro-first query chooses another already-supported proof and hides the
//! arithmetic proportional-equality leaf this regression must exercise.

use crate::api::{Logic, ProofAcceptanceMode, Solver, Sort};

fn query(target: i64) -> Solver {
    let mut s = Solver::try_new(Logic::Uflia).expect("native solver");
    s.set_produce_proofs(true);
    s.try_set_option(":check-proofs-strict", "true")
        .expect("strict policy");
    s.set_timeout(Some(std::time::Duration::from_secs(5)));
    let x = s.declare_const("__verification_consumer_source_var_v1_b_x", Sort::Int);
    let result = s.declare_const("__verification_consumer_source_var_v1_b_result", Sort::Int);
    let yes = s.bool_const(true);
    let two = s.int_const(2);
    let double = s.mul(x, two);
    let forty_two = s.int_const(42);
    let ghost = s.try_eq_no_ite_expand(double, forty_two).unwrap();
    let body = s.try_eq_no_ite_expand(x, result).unwrap();
    let target = s.int_const(target);
    let goal = s.try_eq_no_ite_expand(result, target).unwrap();
    let negative = s.not(goal);
    for root in [yes, ghost, body, negative] {
        s.assert_term(root);
    }
    s
}

#[test]
fn proportional_ghost_first_native_query_has_a_complete_checked_wire() {
    let mut solver = query(21);
    let details = solver.check_sat_with_details();
    assert!(details.result.is_unsat(), "{details:#?}");
    assert!(
        details.verification.unsat_proof_strictly_verified,
        "{details:#?}"
    );
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("first-query proof");
    artifact
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .expect("strict authority");
    assert!(artifact.quality.is_complete());
    assert!(
        !artifact.alethe.contains(":rule hole"),
        "{}",
        artifact.alethe
    );
    assert!(
        artifact.alethe.contains(":rule la_disequality"),
        "{}",
        artifact.alethe
    );
    assert!(
        solver.last_proof().unwrap().steps.iter().any(|step| {
            let ay_core::ProofStep::TheoryLemma {
                kind: ay_core::TheoryLemmaKind::ArithClauseTautology,
                clause,
                ..
            } = step
            else {
                return false;
            };
            ay_core::proof_validation::arith_proportional_equality_witness(solver.terms(), clause)
                .is_some_and(|witness| {
                    witness.multiplier == num_rational::BigRational::new(1.into(), 2.into())
                })
        }),
        "the actual arithmetic producer must exercise the proportional lemma"
    );
}

#[test]
fn proportional_ghost_wrong_target_has_a_validated_countermodel() {
    let mut solver = query(22);
    let details = solver.check_sat_with_details();
    assert!(details.result.is_sat(), "{details:#?}");
    assert!(details.verification.sat_model_validated, "{details:#?}");
}
