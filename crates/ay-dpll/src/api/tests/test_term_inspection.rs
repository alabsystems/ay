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
