// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::sync::Arc;
use std::time::Duration;

use super::*;
use crate::api::Logic;

fn parsed(source: &str) -> Solver {
    let mut solver = Solver::try_new(Logic::All).expect("ordinary native solver");
    solver.set_term_memory_limit(Some(64 * 1024 * 1024));
    solver
        .parse_smtlib2(source)
        .expect("exact source declarations");
    solver
}

fn scalar_sat() -> Solver {
    let mut solver = parsed(
        "(declare-const p Bool)(declare-const x Int)
         (declare-const a (Array Bool Int))
         (assert p)(assert (= x 7))
         (assert (= a ((as const (Array Bool Int)) 9)))",
    );
    assert!(solver
        .try_check_sat_with_timeout(Duration::from_secs(2))
        .expect("bounded original solve")
        .is_sat());
    solver
        .ensure_last_sat_model_accepted_for_consumer()
        .expect("actual accepted original model");
    solver
}

#[test]
#[ntest::timeout(10_000)]
fn complete_literals_preserve_input_order_duplicates_and_legacy_values() {
    let solver = scalar_sat();
    let size = solver.terms().len();
    let expected = solver
        .try_get_named_values(&["x", "p", "a", "x"])
        .expect("unchanged literal API");
    let complete = solver
        .try_get_named_values_complete(&["x", "p", "a", "x"])
        .expect("one complete typed batch");
    let literals: Vec<_> = complete
        .into_iter()
        .map(|value| match value {
            CompleteModelValue::Literal(value) => value,
            _ => panic!("ordinary literal must not acquire functional data"),
        })
        .collect();
    assert_eq!(literals, expected);
    assert_eq!(solver.terms().len(), size);
}

#[test]
#[ntest::timeout(10_000)]
fn complete_batch_rejects_unbound_names_and_stale_query_without_partial_values() {
    let mut solver = scalar_sat();
    assert!(matches!(
        solver.try_get_named_values_complete(&["x", "missing"]),
        Err(SolverError::InvalidArgument { .. })
    ));
    assert!(solver.try_get_named_values_complete(&["x"]).is_ok());
    solver
        .parse_smtlib2("(assert false)")
        .expect("new original query");
    assert!(matches!(
        solver.try_get_named_values_complete(&["x"]),
        Err(SolverError::NoResult)
    ));
}

#[test]
fn complete_empty_batch_still_requires_current_accepted_sat() {
    let solver = parsed("");
    assert!(matches!(
        solver.try_get_named_values_complete(&[]),
        Err(SolverError::NoResult)
    ));
}

#[test]
fn complete_request_authentication_rejects_definitions_overloads_and_wrong_sorts() {
    let solver = parsed(
        "(declare-const x Int)(declare-const x Bool)
         (define-fun fixed () Int 7)(declare-fun f (Int) Int)",
    );
    for name in ["x", "fixed", "f", "(f x)"] {
        assert!(solver.named_value_requests(&[name]).is_err());
    }
    let mut work = MAX_SORT_WORK;
    assert!(matching_sorts(&Sort::bitvec(8), &Sort::bitvec(16), &mut work).is_none());
    let mut work = MAX_SORT_WORK;
    assert!(matching_sorts(
        &Sort::array(Sort::bitvec(64), Sort::Bool),
        &Sort::array(Sort::bitvec(64), Sort::bitvec(1)),
        &mut work,
    )
    .is_none());
}

#[test]
#[ntest::timeout(10_000)]
fn complete_nested_cancelled_read_is_terminal_on_the_same_original_owner() {
    let solver = scalar_sat();
    let result = solver.with_model_evaluation_read(|| {
        solver.interrupt();
        assert!(solver.try_get_named_values_complete(&["x", "a"]).is_err());
        solver.clear_interrupt();
        assert!(solver.try_get_named_values_complete(&["x"]).is_err());
        assert!(solver.try_get_named_values_complete(&[]).is_err());
        Ok(())
    });
    assert!(matches!(result, Err(SolverError::ModelGenerationFailed(_))));
    assert!(solver
        .executor
        .last_result()
        .expect("original SAT")
        .is_sat());
    assert!(solver.executor.was_model_validated());
    assert!(solver.try_get_named_values_complete(&["x"]).is_ok());
}

#[test]
#[ntest::timeout(10_000)]
fn complete_zero_memory_and_deadline_refuse_without_rearming_nested_reads() {
    let mut solver = scalar_sat();
    solver.set_term_memory_limit(Some(0));
    assert!(solver.try_get_named_values_complete(&["x"]).is_err());
    solver.set_term_memory_limit(Some(64 * 1024 * 1024));
    solver.set_timeout(Some(Duration::ZERO));
    assert!(solver.try_get_named_values_complete(&[]).is_err());
    solver.set_timeout(None);
    let result = solver.with_model_evaluation_read(|| {
        let reason = solver.executor.complete_named_value_allocation_refused();
        assert!(reason.contains("allocation refused"));
        assert!(solver.try_get_named_values_complete(&["x"]).is_err());
        Ok(())
    });
    assert!(matches!(result, Err(SolverError::ModelGenerationFailed(_))));
    assert!(solver.try_get_named_values_complete(&["x"]).is_ok());
}

#[test]
#[ntest::timeout(10_000)]
fn complete_huge_array_is_native_data_not_lambda_text_or_finite_samples() {
    let mut solver = parsed(
        "(declare-fun d () (Array (_ BitVec 64) (_ BitVec 8)))
         (declare-fun s () (Array (_ BitVec 64) (_ BitVec 8)))
         (declare-fun w () (Array (_ BitVec 64) (_ BitVec 8)))
         (declare-const p Bool)(assert p)
         (assert (= w (lambda ((i (_ BitVec 64)))
           (ite (and (bvule (_ bv1 64) i) (bvult i (_ bv1152921504606846976 64)))
                (select s (bvsub i (_ bv1 64))) (select d i)))))
         (assert (= (select d (_ bv0 64)) (_ bv7 8)))
         (assert (= (select s (_ bv0 64)) (_ bv9 8)))",
    );
    assert!(solver
        .try_check_sat_with_timeout(Duration::from_secs(2))
        .expect("actual original huge-range solve")
        .is_sat());
    solver
        .ensure_last_sat_model_accepted_for_consumer()
        .expect("actual native model acceptance");
    let values = solver
        .try_get_named_values_complete(&["w", "p", "w"])
        .expect("complete one-model batch");
    let [CompleteModelValue::FunctionalArray(first), CompleteModelValue::Literal(ModelValue::Bool(true)), CompleteModelValue::FunctionalArray(duplicate)] =
        values.as_slice()
    else {
        panic!("every selected native interpretation stays complete data")
    };
    assert!(Arc::ptr_eq(first, duplicate));
    let mut work = 10_000;
    let key = ay_model_check::ModelValue::bitvec(1.into(), 64);
    assert!(matches!(
        first.read(&key, &mut work).expect("independent data read"),
        ay_model_check::ModelValue::BitVec { value, width: 8 } if value == 9.into()
    ));
    let request = solver
        .named_value_requests(&["w"])
        .expect("exact source carrier");
    assert_eq!(first.sort(), solver.terms().sort(request[0].1));
    assert!(solver.try_get_named_values(&["w"]).is_err());
}
