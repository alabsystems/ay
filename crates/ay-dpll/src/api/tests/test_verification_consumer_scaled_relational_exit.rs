// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native first-query loop exit: j=2*i, i<=n, !(i<n) implies j=2*n.
//! The weaker direct i=n query avoids the original scaled split producer.

use crate::api::{Logic, ProofAcceptanceMode, Solver, Sort};

fn query(shift_goal: bool) -> Solver {
    let mut s = Solver::try_new(Logic::QfLia).expect("solver");
    s.set_produce_proofs(true);
    s.try_set_option(":check-proofs-strict", "true")
        .expect("strict proof policy");
    s.set_timeout(Some(std::time::Duration::from_secs(10)));
    let n = s.declare_const("__verification_consumer_source_var_v1_b_n", Sort::Int);
    let zero = s.int_const(0);
    let requires = s.ge(n, zero);
    s.assert_term(requires);
    let j = s.declare_const("__verification_consumer_source_var_v1_b_j", Sort::Int);
    let two = s.int_const(2);
    let i = s.declare_const("__verification_consumer_source_var_v1_b_i", Sort::Int);
    let twice_i = s.mul(two, i);
    let relational = s.try_eq_no_ite_expand(j, twice_i).unwrap();
    s.assert_term(relational);
    let nonnegative = s.ge(i, zero);
    s.assert_term(nonnegative);
    let upper = s.le(i, n);
    s.assert_term(upper);
    let condition = s.lt(i, n);
    let exited = s.not(condition);
    s.assert_term(exited);
    let twice_n = s.mul(two, n);
    let target = if shift_goal {
        let one = s.int_const(1);
        s.add(twice_n, one)
    } else {
        twice_n
    };
    let goal = s.try_eq_no_ite_expand(j, target).unwrap();
    let negated_goal = s.not(goal);
    s.assert_term(negated_goal);
    s
}

#[test]
fn scaled_relational_exit_first_query_has_a_checked_scaled_split() {
    let mut solver = query(false);
    let details = solver.check_sat_with_details();
    assert!(details.result.is_unsat(), "{details:#?}");
    assert!(details.verification.unsat_proof_strictly_verified);
    let artifact = solver.export_last_unsat_artifact().expect("strict proof");
    artifact
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .expect("strict consumer authority");
    assert!(artifact.quality.is_complete());
    assert!(
        !artifact.alethe.contains(":rule hole"),
        "{}",
        artifact.alethe
    );
    assert!(
        artifact.alethe.contains(":args (1 2)"),
        "{}",
        artifact.alethe
    );
    let proof = solver.last_proof().expect("first-query proof");
    assert!(
        proof.steps.iter().any(|step| {
            let ay_core::ProofStep::TheoryLemma { clause, .. } = step else {
                return false;
            };
            let [a, b, c] = clause.as_slice() else {
                return false;
            };
            [
                [*a, *b, *c],
                [*a, *c, *b],
                [*b, *a, *c],
                [*b, *c, *a],
                [*c, *a, *b],
                [*c, *b, *a],
            ]
            .iter()
            .any(|ordered| {
                ay_core::proof_validation::arith_disequality_split_lowering_witness(
                    solver.terms(),
                    ordered,
                )
                .is_some_and(|witness| witness.guard_multiplier == num_bigint::BigInt::from(2))
            })
        }),
        "the native producer must exercise the scaled split"
    );
}

#[test]
fn scaled_relational_exit_shifted_target_has_a_validated_countermodel() {
    let mut solver = query(true);
    let details = solver.check_sat_with_details();
    assert!(details.result.is_sat(), "{details:#?}");
    assert!(details.verification.sat_model_validated, "{details:#?}");
}
