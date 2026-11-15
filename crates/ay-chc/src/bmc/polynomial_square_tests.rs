// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;
use crate::ground_derivation::validate_ground_derivation;
use crate::ClauseBody;
use std::cell::Cell;
use std::time::Duration;

mod fixtures;
mod progress;
use fixtures::*;

#[test]
fn separately_compiled_rules_keep_the_original_modulo_derivation() {
    let solver = fixture(SecondSquare::Rule, 4);
    let witness = derivation(SecondSquare::Rule, 2);
    assert_eq!(
        validate_ground_derivation(&solver.problem, &witness),
        Ok(())
    );
    let mut live = || true;
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    let compiled = compile(&solver, &mut names).unwrap();
    assert_eq!(compiled.squares, 2);
    let auxiliaries = auxiliary_names(&compiled.expression);
    assert_eq!(auxiliaries, vec![aux(0), aux(1)]);
    for y in [2, 3] {
        let model = satisfying_model(&solver, &compiled.expression, y, &auxiliaries);
        assert_true(&compiled.expression, &model);
    }

    // This is the previous cross-rule alias in the actual composed formula,
    // not an unsupported-operator or missing-model-variable rejection.
    let collapsed = compiled
        .expression
        .substitute_name_map(&FxHashMap::from_iter([(aux(1), variable(&aux(0)))]));
    let mut model = satisfying_model(&solver, &collapsed, 2, &[aux(0)]);
    for value in -10..=20 {
        model.insert(aux(0), SmtValue::Int(value));
        assert_eq!(
            evaluate_expr(&collapsed, &model),
            Some(SmtValue::Bool(false))
        );
    }
    let mut invalid = witness;
    invalid.steps[1]
        .env
        .insert("y".to_owned(), SmtValue::Int(1));
    assert!(validate_ground_derivation(&solver.problem, &invalid).is_err());
}

#[test]
fn a_query_square_does_not_reuse_its_premise_rules_auxiliary() {
    let solver = fixture(SecondSquare::Query, 4);
    assert_eq!(
        validate_ground_derivation(&solver.problem, &derivation(SecondSquare::Query, 2)),
        Ok(()),
    );
    let mut live = || true;
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    let compiled = compile(&solver, &mut names).unwrap();
    assert_eq!(compiled.squares, 2);
    let auxiliaries = auxiliary_names(&compiled.expression);
    assert_eq!(auxiliaries, vec![aux(0), aux(1)]);
    let model = satisfying_model(&solver, &compiled.expression, 2, &auxiliaries);
    assert_true(&compiled.expression, &model);
}

#[test]
fn repeated_compilations_share_one_allocator_but_fresh_attempts_reset_it() {
    let solver = fixture(SecondSquare::Rule, 4);
    let mut live = || true;
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    let first = compile(&solver, &mut names).unwrap();
    let second = compile(&solver, &mut names).unwrap();
    assert_eq!(auxiliary_names(&first.expression), vec![aux(0), aux(1)]);
    let second_aux = auxiliary_names(&second.expression);
    assert_eq!(second_aux, vec![aux(2), aux(3)]);
    assert_true(
        &second.expression,
        &satisfying_model(&solver, &second.expression, 2, &second_aux),
    );
    drop(names);
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    assert_eq!(
        compile(&solver, &mut names).unwrap().expression,
        first.expression
    );
}

#[test]
fn equal_residue_relaxation_does_not_grant_an_original_source_witness() {
    let solver = fixture(SecondSquare::Rule, 0);
    let mut live = || true;
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    let compiled = compile(&solver, &mut names).unwrap();
    let auxiliaries = auxiliary_names(&compiled.expression);
    assert_eq!(auxiliaries, vec![aux(0), aux(1)]);
    // This control deliberately has no original y in [2,3] with y*y mod 5=0.
    // The relaxation may admit more models; no SAT candidate becomes Unsafe.
    assert!(
        validate_ground_derivation(&solver.problem, &derivation(SecondSquare::Rule, 2),).is_err()
    );
    let mut model = satisfying_model(&solver, &compiled.expression, 2, &auxiliaries);
    model.insert(aux(1), SmtValue::Int(5));
    assert_true(&compiled.expression, &model);
}

#[test]
fn an_exact_simplification_and_later_polynomial_fallback_share_auxiliary_scope() {
    let solver = fixture(SecondSquare::Rule, 4);
    let mut live = || true;
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    let exact = exact_simplify::simplify(vec![constraint("u", 0, 0)], &mut names).unwrap();
    assert_eq!(auxiliary_names(&exact), vec![aux(0)]);
    let compiled = compile(&solver, &mut names).unwrap();
    let auxiliaries = auxiliary_names(&compiled.expression);
    assert_eq!(auxiliaries, vec![aux(1), aux(2)]);
    assert_true(
        &compiled.expression,
        &satisfying_model(&solver, &compiled.expression, 2, &auxiliaries),
    );
}
