// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for public Term handle inspection and pretty-printing (#1494).

use crate::api::*;
use std::panic::{catch_unwind, AssertUnwindSafe};

#[test]
fn term_id_raw_roundtrip_and_display_are_stable_handles() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA should construct");
    let x = solver.declare_const("x", Sort::Int);

    let id: TermId = x.id();
    assert_eq!(id.index() as u32, x.to_raw());
    let stripped = Term::from_raw(x.to_raw());
    assert_eq!(stripped.id(), id);
    assert_ne!(
        stripped, x,
        "raw round-trip must not recreate term authority"
    );
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
    let bound_name = match solver.terms().get(bound.id()) {
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
    let wrong_sort_id = solver
        .terms_mut()
        .mk_fresh_named_var(bound_name.clone(), Sort::Bool);
    let wrong_sort = solver.wrap_term(wrong_sort_id);
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
    let let_var_id = solver
        .terms_mut()
        .mk_fresh_named_var("let_captured", Sort::Int);
    let let_var = solver.wrap_term(let_var_id);
    let let_body = solver.try_gt(let_var, zero).expect("well-sorted let body");
    let let_term_id = solver
        .terms_mut()
        .mk_let(vec![("let_captured".to_string(), zero.id())], let_body.id());
    let let_term = solver.wrap_term(let_term_id);
    let wrong_let_var_id = solver
        .terms_mut()
        .mk_fresh_named_var("let_captured", Sort::Bool);
    let wrong_let_var = solver.wrap_term(wrong_let_var_id);
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
        Err(SolverError::InvalidTermHandle {
            operation: "update_term",
            ..
        })
    ));
    assert!(matches!(
        solver.try_update_term(not_p, &[invalid]),
        Err(SolverError::InvalidTermHandle {
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

#[test]
fn term_handles_reject_foreign_solver_aliases_before_indexing() {
    let mut first = Solver::new(Logic::All);
    let mut second = Solver::new(Logic::All);

    let foreign_same_sort = first.declare_const("p", Sort::Bool);
    let local_same_sort = second.declare_const("q", Sort::Bool);
    assert_eq!(foreign_same_sort.to_raw(), local_same_sort.to_raw());
    assert!(matches!(
        second.try_not(foreign_same_sort),
        Err(SolverError::InvalidTermHandle {
            operation: "not",
            ..
        })
    ));

    let foreign_different_sort = first.declare_const("i", Sort::Int);
    let local_different_sort = second.declare_const("r", Sort::Real);
    assert_eq!(
        foreign_different_sort.to_raw(),
        local_different_sort.to_raw()
    );
    assert!(matches!(
        second.try_add(foreign_different_sort, foreign_different_sort),
        Err(SolverError::InvalidTermHandle {
            operation: "add",
            ..
        })
    ));
}

#[test]
fn full_reset_rotates_term_authority_even_when_numeric_ids_repeat() {
    let mut solver = Solver::new(Logic::All);
    let stale = solver.declare_const("before-reset", Sort::Bool);

    solver.try_reset().expect("full reset");
    let current = solver.declare_const("after-reset", Sort::Bool);
    assert_eq!(stale.to_raw(), current.to_raw());
    assert_ne!(stale, current);
    assert!(matches!(
        solver.try_not(stale),
        Err(SolverError::InvalidTermHandle {
            operation: "not",
            ..
        })
    ));
    assert!(solver.try_not(current).is_ok());
}

#[test]
fn logical_scopes_preserve_live_term_authority() {
    let mut solver = Solver::new(Logic::All);
    let before = solver.declare_const("before-scope", Sort::Bool);
    solver.try_push().expect("push");
    let inside = solver.declare_const("inside-scope", Sort::Bool);
    solver.try_pop().expect("pop");

    assert!(solver.try_not(before).is_ok());
    assert!(solver.try_not(inside).is_ok());
    solver
        .try_reset_assertions()
        .expect("reset-assertions preserves the term arena");
    assert!(solver.try_not(before).is_ok());
    assert!(solver.try_not(inside).is_ok());
}

#[test]
fn arbitrary_raw_terms_fail_with_typed_errors_without_panicking() {
    let mut solver = Solver::new(Logic::All);
    let live = solver.declare_const("live", Sort::Bool);

    for invalid in [Term::from_raw(live.to_raw()), Term::from_raw(u32::MAX)] {
        assert!(matches!(
            solver.try_not(invalid),
            Err(SolverError::InvalidTermHandle {
                operation: "not",
                ..
            })
        ));
    }
}

#[test]
fn canonical_proof_renderer_authenticates_term_handles_before_store_access() {
    let mut first = Solver::new(Logic::All);
    let second = Solver::new(Logic::All);
    let foreign = first.declare_const("foreign-proof-term", Sort::Bool);

    for invalid in [foreign, Term::from_raw(foreign.to_raw())] {
        let result = catch_unwind(AssertUnwindSafe(|| second.render_term_canonical(invalid)));
        assert!(
            result.is_err(),
            "unauthenticated term reached proof renderer"
        );
    }
}
