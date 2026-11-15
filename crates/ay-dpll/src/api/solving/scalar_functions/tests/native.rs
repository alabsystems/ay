// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use std::time::Duration;

fn accepted(solver: &mut Solver) {
    let result = solver
        .try_check_sat_with_timeout(Duration::from_secs(3))
        .unwrap();
    assert!(result.is_sat());
    assert!(result.was_model_validated());
    assert!(result.has_sat_emission_witness());
}

#[test]
#[ntest::timeout(20_000)]
fn complete_native_scalar_tables_nullary_values_and_unused_defaults_replay() {
    let constraints = "(assert (= (f #x01) #x07))(assert (= (f #x02) #x09))
        (assert (= zero #x0b))";
    let mut solver = parsed(&format!(
        "(set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-fun unused (Bool) (_ BitVec 136))
        (declare-fun zero () (_ BitVec 8)){constraints}"
    ));
    accepted(&mut solver);
    let count = solver.terms().len();
    let definitions = solver
        .try_get_named_scalar_function_models(&["unused", "zero", "f"])
        .unwrap();
    assert_eq!(
        definitions.iter().map(|f| f.name()).collect::<Vec<_>>(),
        ["unused", "zero", "f"]
    );
    assert_eq!(definitions[0].arg_sorts(), [Sort::Bool]);
    assert_eq!(definitions[0].result_sort(), &Sort::bitvec(136));
    assert_eq!(solver.terms().len(), count);
    let mut text = definitions
        .iter()
        .map(|f| f.definition_smtlib())
        .collect::<Vec<_>>()
        .join("\n");
    text.push_str(constraints);
    let mut replay = parsed(&text);
    accepted(&mut replay);
    solver.executor.set_model_validated_for_testing(false);
    assert!(matches!(
        solver.try_get_named_scalar_function_models(&["f"]),
        Err(SolverError::SatModelNotValidated)
    ));
}

#[test]
#[ntest::timeout(20_000)]
fn adopted_closed_bv_definition_is_extracted_and_stale_results_refuse() {
    let mut solver = parsed(
        "(declare-fun |increment value| ((_ BitVec 8)) (_ BitVec 8))
        (assert (forall ((x (_ BitVec 8))) (= (|increment value| x) (bvadd x #x01))))
        (assert (= (|increment value| #xff) #x00))",
    );
    assert!(solver
        .executor
        .context()
        .adopted_macro_interp("increment value")
        .is_some());
    accepted(&mut solver);
    let definitions = solver
        .try_get_named_scalar_function_models(&["increment value"])
        .unwrap();
    assert_eq!(definitions.len(), 1);
    assert_eq!(definitions[0].name(), "increment value");
    let mut replay = parsed(&format!(
        "{}
        (assert (= (|increment value| #xff) #x00))
        (assert (= (|increment value| #x10) #x11))",
        definitions[0].definition_smtlib()
    ));
    accepted(&mut replay);
    solver.parse_smtlib2("(assert false)").unwrap();
    assert!(matches!(
        solver.try_get_named_scalar_function_models(&["increment value"]),
        Err(SolverError::NoResult)
    ));
    let result = solver
        .try_check_sat_with_timeout(Duration::from_secs(3))
        .unwrap();
    assert!(result.is_unsat());
    assert!(matches!(
        solver.try_get_named_scalar_function_models(&["increment value"]),
        Err(SolverError::NotSat)
    ));
}
