// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for public Term handle inspection and pretty-printing (#1494).

use crate::api::*;

#[test]
fn term_id_raw_roundtrip_and_display_are_stable_handles() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA should construct");
    let x = solver.declare_const("x", Sort::Int);

    let id: TermId = x.id();
    assert_eq!(id.index() as u32, x.to_raw());
    assert_eq!(Term::from_raw(x.to_raw()).id(), id);
    assert_eq!(format!("{x}"), format!("Term({id})"));
}

#[test]
fn solver_format_term_renders_smtlib_for_api_terms() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA should construct");
    let x = solver.declare_const("x", Sort::Int);
    let reserved = solver.declare_const("let", Sort::Int);
    let one = solver.int_const(1);
    let zero = solver.int_const(0);
    let sum = solver.try_add(x, one).expect("int + int");
    let gt = solver.try_gt(sum, zero).expect("int > int");

    assert_eq!(solver.format_term(x), "x");
    assert_eq!(solver.format_term(reserved), "|let|");
    assert_eq!(solver.format_term(one), "1");
    assert_eq!(solver.format_term(sum), "(+ x 1)");
    assert_eq!(solver.format_term(gt), "(< 0 (+ x 1))");
}

#[test]
fn formatted_terms_match_structural_inspection() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA should construct");
    let x = solver.declare_const("x", Sort::Int);
    let one = solver.int_const(1);
    let sum = solver.try_add(x, one).expect("int + int");

    assert_eq!(solver.term_sort(sum), Sort::Int);
    assert!(matches!(
        solver.term_kind(sum),
        TermKind::App { name, num_args } if name == "+" && num_args == 2
    ));

    let children = solver.term_children(sum);
    assert_eq!(children, vec![x, one]);
    assert_eq!(solver.format_term(children[0]), "x");
    assert_eq!(solver.format_term(children[1]), "1");
}

#[test]
fn update_term_preserves_privileged_application_child_sorts() {
    let mut solver = Solver::try_new(Logic::QfAuflia).expect("QF_AUFLIA should construct");
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let first_array = solver.declare_const("first_array", array_sort.clone());
    let second_array = solver.declare_const("second_array", array_sort);
    let first_index = solver.int_const(0);
    let second_index = solver.int_const(1);
    let select = solver
        .try_select(first_array, first_index)
        .expect("well-sorted select");

    let rebuilt = solver
        .try_update_term(select, &[second_array, second_index])
        .expect("same-sort select children should be replaceable");
    assert_eq!(
        solver.term_children(rebuilt),
        vec![second_array, second_index]
    );
    assert_eq!(solver.term_sort(rebuilt), Sort::Int);

    let not_an_array = solver.int_const(2);
    assert!(matches!(
        solver.try_update_term(select, &[not_an_array, second_index]),
        Err(SolverError::SortMismatch {
            operation: "update_term",
            ..
        })
    ));
    assert_eq!(
        solver.update_term(select, &[not_an_array, second_index]),
        None
    );
}

#[test]
fn update_term_checks_non_application_children_and_binder_bodies() {
    let mut solver = Solver::try_new(Logic::Uflia).expect("UFLIA should construct");
    let p = solver.declare_const("p", Sort::Bool);
    let q = solver.declare_const("q", Sort::Bool);
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);

    let not_p = solver.try_not(p).expect("boolean negation");
    let not_q = solver
        .try_update_term(not_p, &[q])
        .expect("boolean Not child should be replaceable");
    assert_eq!(solver.term_children(not_q), vec![q]);
    assert!(matches!(
        solver.try_update_term(not_p, &[x]),
        Err(SolverError::SortMismatch { .. })
    ));

    let ite = solver.try_ite(p, x, y).expect("well-sorted ITE");
    let rebuilt_ite = solver
        .try_update_term(ite, &[q, y, x])
        .expect("same-sort ITE children should be replaceable");
    assert_eq!(solver.term_children(rebuilt_ite), vec![q, y, x]);
    assert!(matches!(
        solver.try_update_term(ite, &[x, y, x]),
        Err(SolverError::SortMismatch { .. })
    ));
    assert!(matches!(
        solver.try_update_term(ite, &[q, p, x]),
        Err(SolverError::SortMismatch { .. })
    ));

    let bound = solver.fresh_var("bound", Sort::Int);
    let zero = solver.int_const(0);
    let body = solver.try_gt(bound, zero).expect("integer comparison");
    let forall = solver
        .try_forall(&[bound], body)
        .expect("boolean quantifier body");
    let rebuilt_forall = solver
        .try_update_term(forall, &[q])
        .expect("boolean binder body should be replaceable");
    assert_eq!(solver.term_children(rebuilt_forall), vec![q]);
    assert!(matches!(
        solver.try_update_term(forall, &[x]),
        Err(SolverError::SortMismatch { .. })
    ));
}

#[test]
fn update_term_rejects_wrong_sort_occurrences_captured_by_preserved_binders() {
    let mut solver = Solver::try_new(Logic::Uflia).expect("UFLIA should construct");
    let bound = solver.fresh_var("captured", Sort::Int);
    let bound_name = match solver.terms().get(bound.0) {
        ay_core::term::TermData::Var(name, _) => name.clone(),
        other => panic!("fresh variable should be a Var, got {other:?}"),
    };
    let zero = solver.int_const(0);
    let original_body = solver.try_gt(bound, zero).expect("integer comparison");
    let forall = solver
        .try_forall(&[bound], original_body)
        .expect("well-sorted source quantifier");

    // Manufacture a distinct Bool variable with the exact binder spelling.
    // Immediate child validation sees a Bool quantifier body either way; the
    // preserved binder must additionally reject capture at the wrong sort.
    let wrong_sort = Term(
        solver
            .terms_mut()
            .mk_fresh_named_var(bound_name.clone(), Sort::Bool),
    );
    assert!(matches!(
        solver.try_update_term(forall, &[wrong_sort]),
        Err(SolverError::InvalidArgument {
            operation: "update_term",
            ..
        })
    ));

    // A nested binder with the same spelling shadows the preserved outer
    // binder, so its differently-sorted occurrence remains valid.
    let nested = solver
        .try_forall(&[wrong_sort], wrong_sort)
        .expect("nested Bool binder");
    solver
        .try_update_term(forall, &[nested])
        .expect("nested same-name binder should shadow the outer binder");

    // The same capture rule applies to a preserved `let` name.  Binding values
    // precede the body in update-term child order.
    let let_var = Term(
        solver
            .terms_mut()
            .mk_fresh_named_var("let_captured", Sort::Int),
    );
    let let_body = solver.try_gt(let_var, zero).expect("well-sorted let body");
    let let_term = Term(
        solver
            .terms_mut()
            .mk_let(vec![("let_captured".to_string(), zero.0)], let_body.0),
    );
    let wrong_let_var = Term(
        solver
            .terms_mut()
            .mk_fresh_named_var("let_captured", Sort::Bool),
    );
    assert!(matches!(
        solver.try_update_term(let_term, &[zero, wrong_let_var]),
        Err(SolverError::InvalidArgument {
            operation: "update_term",
            ..
        })
    ));
}

#[test]
fn update_term_rejects_invalid_handles_and_child_counts_without_panicking() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA should construct");
    let p = solver.declare_const("p", Sort::Bool);
    let not_p = solver.try_not(p).expect("boolean negation");
    let invalid = Term::from_raw(u32::MAX);

    assert!(matches!(
        solver.try_update_term(invalid, &[]),
        Err(SolverError::InvalidArgument {
            operation: "update_term",
            ..
        })
    ));
    assert!(matches!(
        solver.try_update_term(not_p, &[invalid]),
        Err(SolverError::InvalidArgument {
            operation: "update_term",
            ..
        })
    ));
    assert!(matches!(
        solver.try_update_term(not_p, &[]),
        Err(SolverError::InvalidArgument {
            operation: "update_term",
            ..
        })
    ));
    assert_eq!(solver.update_term(invalid, &[]), None);
    assert_eq!(solver.update_term(not_p, &[invalid]), None);
    assert_eq!(solver.update_term(not_p, &[]), None);
}
