// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::api::{Logic, Solver};

#[test]
fn native_anonymous_and_named_api_assertions_record_positive_origin() {
    let mut solver = Solver::new(Logic::QfLia);
    let a = solver.bool_const(true);
    let b = solver.bool_const(false);
    solver.try_assert_term(a).unwrap();
    solver.try_assert_named(b, "native_label").unwrap();
    assert_eq!(
        solver
            .executor
            .ctx
            .native_authored_assertion_terms_aligned_bounded(2),
        Some(vec![a.id(), b.id()])
    );
}

#[test]
fn parsed_assertions_remain_text_after_native_solver_check_entry() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.parse_smtlib2("(assert false)").unwrap();
    solver.set_produce_proofs(true);
    assert!(solver.check_sat().is_unsat());
    assert!(solver.executor.native_proof_source_scope.is_none());
}

#[test]
fn native_plain_check_captures_complete_input_before_proof_growth() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_proofs(true);
    let x = solver
        .try_declare_const("native_source_x", crate::api::Sort::Int)
        .unwrap();
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let first = solver.try_eq(x, zero).unwrap();
    let second = solver.try_eq(x, one).unwrap();
    solver.try_assert_term(first).unwrap();
    solver.try_assert_term(second).unwrap();
    assert!(solver.check_sat().is_unsat());
    let scope = solver
        .executor
        .native_proof_source_scope
        .as_ref()
        .expect("audited native query must capture");
    assert_eq!(scope.roots(), &[first.id(), second.id()]);
    assert!(scope.is_current_after_proof_growth(&solver.executor));
}
