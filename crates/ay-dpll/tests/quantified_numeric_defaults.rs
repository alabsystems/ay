// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Finite exceptions must not force an unsuitable total function default.
//! These use actual native declarations and require accepted complete models.

use std::time::Duration;

use ay_dpll::api::{FuncDecl, Logic, ModelValue, SolveResult, Solver, Sort, Term};

fn solver(proofs: bool, logic: Logic) -> Solver {
    let mut solver = Solver::new(logic);
    solver.set_timeout(Some(Duration::from_secs(5)));
    solver.set_produce_proofs(proofs);
    if proofs {
        solver
            .try_set_option(":check-proofs-strict", "true")
            .unwrap();
    }
    solver
}

fn number(solver: &mut Solver, sort: &Sort, value: i64) -> Term {
    match sort {
        Sort::Int => solver.int_const(value),
        Sort::Real => solver.rational_const(value, 1),
        _ => panic!("numeric fixture requires a numeric range"),
    }
}

fn numeric_fixture(
    range: Sort,
    proofs: bool,
    exception: i64,
    otherwise: i64,
    seed: i64,
) -> (Solver, FuncDecl) {
    let logic = if range == Sort::Real {
        Logic::Auflira
    } else {
        Logic::Auflia
    };
    let mut solver = solver(proofs, logic);
    let function = solver.declare_fun("point", &[Sort::Int], range.clone());
    let variable = solver.int_var("bound");
    let read = solver.apply(&function, &[variable]);
    let zero = solver.int_const(0);
    let condition = solver.eq(variable, zero);
    let exceptional = number(&mut solver, &range, exception);
    let default = number(&mut solver, &range, otherwise);
    let at_exception = solver.eq(read, exceptional);
    let elsewhere = solver.eq(read, default);
    let body = solver.ite(condition, at_exception, elsewhere);
    let definition = solver
        .try_forall_with_triggers(&[variable], body, &[&[read]])
        .unwrap();
    solver.assert_term(definition);
    let key = solver.int_const(seed);
    let observed = solver.apply(&function, &[key]);
    let value = number(
        &mut solver,
        &range,
        if seed == 0 { exception } else { otherwise },
    );
    let observation = solver.eq(observed, value);
    solver.assert_term(observation);
    (solver, function)
}

fn accepted_sat(solver: &mut Solver) {
    let details = solver.check_sat_with_details();
    assert!(details.result.result().is_sat(), "{details:#?}");
    assert!(details.result.was_model_validated(), "{details:#?}");
    assert!(details.result.has_sat_emission_witness(), "{details:#?}");
    assert!(
        matches!(details.accept_for_consumer().cloned(), Ok(SolveResult::Sat)),
        "{details:#?}"
    );
}

fn accepted_unsat(solver: &mut Solver) {
    let details = solver.check_sat_with_details();
    assert!(details.result.result().is_unsat(), "{details:#?}");
    assert!(
        details.verification.unsat_proof_strictly_verified,
        "{details:#?}"
    );
    assert_eq!(
        details.verification.unsat_proof_checker_failures, 0,
        "{details:#?}"
    );
    assert!(
        matches!(
            details.accept_for_consumer().cloned(),
            Ok(SolveResult::Unsat(_))
        ),
        "{details:#?}"
    );
}

fn numeric_value(solver: &mut Solver, function: &FuncDecl, range: &Sort, key: i64, expected: i64) {
    let key = solver.int_const(key);
    let read = solver.apply(function, &[key]);
    let expected = number(solver, range, expected);
    let equal = solver.eq(read, expected);
    assert_eq!(solver.try_get_value(equal).unwrap(), ModelValue::Bool(true));
}

#[test]
fn native_integer_function_keeps_exception_and_completes_unobserved_points() {
    for proofs in [false, true] {
        let (mut solver, function) = numeric_fixture(Sort::Int, proofs, 1, 0, 0);
        accepted_sat(&mut solver);
        numeric_value(&mut solver, &function, &Sort::Int, 0, 1);
        numeric_value(&mut solver, &function, &Sort::Int, 104729, 0);
        numeric_value(&mut solver, &function, &Sort::Int, -104729, 0);
    }
}

#[test]
fn native_real_function_uses_a_real_zero_default() {
    for proofs in [false, true] {
        let (mut solver, function) = numeric_fixture(Sort::Real, proofs, 1, 0, 0);
        accepted_sat(&mut solver);
        numeric_value(&mut solver, &function, &Sort::Real, 0, 1);
        numeric_value(&mut solver, &function, &Sort::Real, 104729, 0);
    }
}

#[test]
fn an_existing_nonzero_default_remains_a_valid_first_candidate() {
    for proofs in [false, true] {
        let (mut solver, function) = numeric_fixture(Sort::Int, proofs, 0, 1, 1);
        accepted_sat(&mut solver);
        numeric_value(&mut solver, &function, &Sort::Int, 0, 0);
        numeric_value(&mut solver, &function, &Sort::Int, 104729, 1);
    }
}

#[test]
fn observed_rows_cannot_be_replaced_by_the_zero_proposal() {
    for range in [Sort::Int, Sort::Real] {
        let (mut solver, function) = numeric_fixture(range.clone(), true, 1, 0, 0);
        let key = solver.int_const(0);
        let read = solver.apply(&function, &[key]);
        let wrong = number(&mut solver, &range, 0);
        let contradictory = solver.eq(read, wrong);
        solver.assert_term(contradictory);
        accepted_unsat(&mut solver);
    }
}

#[test]
fn a_conflicting_nonexceptional_ground_row_cannot_earn_sat() {
    for range in [Sort::Int, Sort::Real] {
        let (mut solver, function) = numeric_fixture(range.clone(), true, 1, 0, 0);
        let key = solver.int_const(104729);
        let read = solver.apply(&function, &[key]);
        let wrong = number(&mut solver, &range, 1);
        let contradictory = solver.eq(read, wrong);
        solver.assert_term(contradictory);
        accepted_unsat(&mut solver);
    }
}

#[test]
fn scoped_contradiction_does_not_leave_a_stale_numeric_model() {
    let (mut solver, function) = numeric_fixture(Sort::Int, true, 1, 0, 0);
    accepted_sat(&mut solver);
    solver.push();
    let key = solver.int_const(104729);
    let read = solver.apply(&function, &[key]);
    let one = solver.int_const(1);
    let wrong = solver.eq(read, one);
    solver.assert_term(wrong);
    accepted_unsat(&mut solver);
    solver.pop();
    accepted_sat(&mut solver);
    numeric_value(&mut solver, &function, &Sort::Int, 104729, 0);
}

#[test]
fn numeric_and_boolean_total_model_proposals_are_checked_together() {
    let (mut solver, function) = numeric_fixture(Sort::Int, true, 1, 0, 0);
    let relation = solver.declare_fun("positive_relation", &[Sort::Int], Sort::Bool);
    let variable = solver.int_var("relation_bound");
    let predicate = solver.apply(&relation, &[variable]);
    let universal = solver
        .try_forall_with_triggers(&[variable], predicate, &[&[predicate]])
        .unwrap();
    solver.assert_term(universal);
    accepted_sat(&mut solver);
    numeric_value(&mut solver, &function, &Sort::Int, 104729, 0);
    let key = solver.int_const(104729);
    let read = solver.apply(&relation, &[key]);
    assert_eq!(solver.try_get_value(read).unwrap(), ModelValue::Bool(true));
}

#[test]
fn combined_proposal_cannot_erase_a_conflicting_boolean_ground_row() {
    let (mut solver, _) = numeric_fixture(Sort::Int, true, 1, 0, 0);
    let relation = solver.declare_fun("required_relation", &[Sort::Int], Sort::Bool);
    let variable = solver.int_var("required_relation_bound");
    let predicate = solver.apply(&relation, &[variable]);
    let universal = solver
        .try_forall_with_triggers(&[variable], predicate, &[&[predicate]])
        .unwrap();
    solver.assert_term(universal);
    let key = solver.int_const(123);
    let ground = solver.apply(&relation, &[key]);
    let denied = solver.not(ground);
    solver.assert_term(denied);
    accepted_unsat(&mut solver);
}

#[test]
fn captured_mapping_aliases_keep_distinct_predicates_in_one_total_model() {
    for proofs in [false, true] {
        let mut solver = solver(proofs, Logic::Auflia);
        let carrier = Sort::Uninterpreted("Mapping".into());
        let returned = solver.declare_fun("returned_mapping", &[Sort::Int], carrier.clone());
        let get = solver.declare_fun("mapping_get", &[carrier.clone(), Sort::Int], Sort::Int);
        let mut mappings = Vec::new();
        for (index, captured) in [0, 0, 1].into_iter().enumerate() {
            let mapping = solver.declare_const(&format!("mapping_{index}"), carrier.clone());
            mappings.push(mapping);
            let variable = solver.int_var(&format!("key_{index}"));
            let read = solver.apply(&get, &[mapping, variable]);
            let captured = solver.int_const(captured);
            let condition = solver.eq(variable, captured);
            let one = solver.int_const(1);
            let zero = solver.int_const(0);
            let selected = solver.eq(read, one);
            let elsewhere = solver.eq(read, zero);
            let body = solver.ite(condition, selected, elsewhere);
            let definition = solver
                .try_forall_with_triggers(&[variable], body, &[&[read]])
                .unwrap();
            solver.assert_term(definition);
            let result = solver.apply(&returned, &[captured]);
            let definition = solver.eq(result, mapping);
            solver.assert_term(definition);
        }
        accepted_sat(&mut solver);
        for (index, mapping) in mappings.into_iter().enumerate() {
            for key in [0, 1, 104729] {
                let key_term = solver.int_const(key);
                let read = solver.apply(&get, &[mapping, key_term]);
                let expected = i64::from(key == if index == 2 { 1 } else { 0 });
                let expected = solver.int_const(expected);
                let equal = solver.eq(read, expected);
                assert_eq!(solver.try_get_value(equal).unwrap(), ModelValue::Bool(true));
            }
        }
    }
}

#[test]
fn a_spent_query_budget_cannot_grant_a_numeric_default_model() {
    let (mut solver, _) = numeric_fixture(Sort::Int, true, 1, 0, 0);
    solver.set_timeout(Some(Duration::ZERO));
    let details = solver.check_sat_with_details();
    assert!(
        matches!(details.result.result(), SolveResult::Unknown),
        "{details:#?}"
    );
    assert!(!details.result.has_sat_emission_witness(), "{details:#?}");
}
