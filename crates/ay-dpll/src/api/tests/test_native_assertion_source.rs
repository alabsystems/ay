// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::api::{Logic, ProofAcceptanceMode, Solver, Sort, Term};
use ay_frontend::Command;

#[test]
fn retains_noncanonical_source_for_native_proof() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    solver.set_produce_proofs(true);
    let x = solver.declare_const("x", Sort::Int);
    let four = solver.int_const(4);
    let lower = solver.try_gt(x, four).unwrap();
    let upper = solver.try_le(x, four).unwrap();
    let conjunction = solver.try_and_many(&[lower, upper, lower]).unwrap();
    let source = "(assert (and (> x 4) (<= x 4) (> x 4)))";
    solver
        .try_assert_term_with_source(conjunction, source)
        .unwrap();
    let Command::Assert(parsed) = ay_frontend::parse(source).unwrap().remove(0) else {
        panic!("assertion fixture");
    };
    assert_eq!(solver.executor.context().assertions_parsed(), &[parsed]);
    assert!(solver.check_sat().is_unsat());
    let artifact = solver.export_last_unsat_artifact().unwrap();
    artifact
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .unwrap();
    assert_eq!(artifact.quality.trust_count, 0);
    assert!(
        artifact.alethe.contains("(and (> x 4) (<= x 4) (> x 4))"),
        "{}",
        artifact.alethe
    );
}

#[test]
fn rejects_different_assertions_without_changing_the_query() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let x = solver.declare_const("x", Sort::Int);
    let four = solver.int_const(4);
    let native = solver.try_gt(x, four).unwrap();
    for source in [
        "(assert (< x 4))",
        "(assert true)",
        "(assert false)",
        "(assert (> absent 4))",
    ] {
        assert!(
            solver.try_assert_term_with_source(native, source).is_err(),
            "{source}"
        );
        assert_eq!(solver.assertions(), [] as [Term; 0]);
    }
    solver
        .try_assert_term_with_source(native, "(assert (> x 4))")
        .unwrap();
    assert!(solver.check_sat().is_sat());
}

#[test]
fn rejects_extra_commands_before_execution() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let native = solver.bool_const(true);
    for source in [
        "",
        "(assert true",
        "(check-sat)",
        "(push 1)",
        "(assert true) (assert false)",
        "(assert true) (reset)",
        "(declare-const injected Int) (assert true)",
    ] {
        assert!(
            solver.try_assert_term_with_source(native, source).is_err(),
            "{source}"
        );
        assert_eq!(solver.assertions(), [] as [Term; 0]);
        assert_eq!(solver.num_scopes(), 0);
    }
    assert!(solver.check_sat().is_sat());
}

#[test]
fn rejects_foreign_terms_and_nonboolean_sources() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let mut foreign = Solver::try_new(Logic::QfLia).unwrap();
    let native = foreign.bool_const(true);
    assert!(solver
        .try_assert_term_with_source(native, "(assert true)")
        .is_err());
    let number = solver.int_const(42);
    assert!(solver
        .try_assert_term_with_source(number, "(assert 42)")
        .is_err());
    assert_eq!(solver.assertions(), [] as [Term; 0]);
}

#[test]
fn source_retention_follows_push_pop_and_reset() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let positive = solver.try_gt(x, zero).unwrap();
    let negative = solver.try_le(x, zero).unwrap();
    solver
        .try_assert_term_with_source(positive, "(assert (> x 0))")
        .unwrap();
    solver.try_push().unwrap();
    solver
        .try_assert_term_with_source(negative, "(assert (<= x 0))")
        .unwrap();
    assert!(solver.check_sat().is_unsat());
    solver.try_pop().unwrap();
    assert_eq!(solver.assertions().len(), 1);
    assert_eq!(solver.executor.context().assertions_parsed().len(), 1);
    assert!(solver.check_sat().is_sat());
    solver.try_reset_assertions().unwrap();
    assert_eq!(solver.assertions(), [] as [Term; 0]);
    assert_eq!(solver.executor.context().assertions_parsed(), []);
}

#[test]
fn oversized_source_cannot_enter_assertion_history() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let native = solver.bool_const(true);
    let source = format!("(assert true){}", " ".repeat(8 * 1024 * 1024));
    assert!(solver.try_assert_term_with_source(native, &source).is_err());
    assert_eq!(solver.assertions(), [] as [Term; 0]);
    assert_eq!(solver.executor.context().assertions_parsed(), []);
}

/// `Level = zero | succ(pred: Level)`, declared natively.
fn level() -> ay_core::DatatypeSort {
    ay_core::DatatypeSort::new(
        "Level",
        vec![
            ay_core::DatatypeConstructor::new("zero", vec![]),
            ay_core::DatatypeConstructor::new(
                "succ",
                vec![ay_core::DatatypeField::new(
                    "pred",
                    Sort::Uninterpreted("Level".to_string()),
                )],
            ),
        ],
    )
}

fn level_solver() -> (Solver, Term) {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    solver.set_produce_proofs(true);
    solver.try_declare_datatype(&level()).unwrap();
    let l = solver.declare_const("l", Sort::Datatype(level()));
    (solver, l)
}

/// The native datatype builders produce the term the SMT-LIB spelling
/// elaborates to, so a nested constructor/selector/tester assertion is
/// retained with its authored source.
#[test]
fn nested_datatype_terms_reconstruct_from_their_source() {
    let (mut solver, l) = level_solver();
    let dt = level();
    let succ_l = solver.try_datatype_constructor(&dt, "succ", &[l]).unwrap();
    let succ_succ_l = solver
        .try_datatype_constructor(&dt, "succ", &[succ_l])
        .unwrap();
    let zero = solver.try_datatype_constructor(&dt, "zero", &[]).unwrap();
    let succ_zero = solver
        .try_datatype_constructor(&dt, "succ", &[zero])
        .unwrap();
    let pred_succ_l = solver
        .try_datatype_selector("pred", succ_l, Sort::Datatype(dt.clone()))
        .unwrap();
    let pred_pred = solver
        .try_datatype_selector("pred", succ_succ_l, Sort::Datatype(dt.clone()))
        .unwrap();
    let pred_pred = solver
        .try_datatype_selector("pred", pred_pred, Sort::Datatype(dt.clone()))
        .unwrap();
    let is_succ = solver.try_datatype_tester("succ", succ_l).unwrap();
    let is_zero = solver.try_datatype_tester("zero", succ_succ_l).unwrap();
    let cases: Vec<(Term, &str)> = vec![
        (
            solver.try_eq(pred_succ_l, l).unwrap(),
            "(assert (= (pred (succ l)) l))",
        ),
        (
            solver.try_eq(succ_succ_l, succ_l).unwrap(),
            "(assert (= (succ (succ l)) (succ l)))",
        ),
        (
            solver.try_eq(pred_pred, l).unwrap(),
            "(assert (= (pred (pred (succ (succ l)))) l))",
        ),
        (is_succ, "(assert ((_ is succ) (succ l)))"),
        (
            solver.try_not(is_zero).unwrap(),
            "(assert (not ((_ is zero) (succ (succ l)))))",
        ),
        (
            solver.try_eq(l, succ_zero).unwrap(),
            "(assert (= l (succ (as zero Level))))",
        ),
    ];
    for (native, source) in cases {
        solver.try_push().unwrap();
        solver
            .try_assert_term_with_source(native, source)
            .unwrap_or_else(|error| panic!("{source}: {error}"));
        solver.try_pop().unwrap();
    }
}

/// A source that spells a different datatype term than the native one is
/// still refused, fold or no fold.
#[test]
fn different_datatype_sources_are_still_refused() {
    let (mut solver, l) = level_solver();
    let dt = level();
    let succ_l = solver.try_datatype_constructor(&dt, "succ", &[l]).unwrap();
    let pred_succ_l = solver
        .try_datatype_selector("pred", succ_l, Sort::Datatype(dt.clone()))
        .unwrap();
    let pred_l = solver
        .try_datatype_selector("pred", l, Sort::Datatype(dt.clone()))
        .unwrap();
    let folded = solver.try_eq(pred_succ_l, l).unwrap();
    let opaque = solver.try_eq(pred_l, l).unwrap();
    let is_succ = solver.try_datatype_tester("succ", succ_l).unwrap();
    for (native, source) in [
        (folded, "(assert (= (pred l) l))"),
        (opaque, "(assert (= (pred (succ l)) l))"),
        (is_succ, "(assert ((_ is zero) (succ l)))"),
        (is_succ, "(assert ((_ is succ) l))"),
        (folded, "(assert (= (succ (succ l)) (succ l)))"),
    ] {
        assert!(
            solver.try_assert_term_with_source(native, source).is_err(),
            "{source}"
        );
        assert_eq!(solver.assertions(), [] as [Term; 0]);
    }
}

/// The native builders fold exactly as elaboration does: a selector over its
/// constructor is the field, a tester over a literal constructor is a
/// Boolean constant, and a constructor equality is the equality of the fields.
///
/// A SOLE-constructor tester over an OPAQUE scrutinee is the exception that
/// proves the rule: the standard `((_ is C) e)` spelling folds it to `true`,
/// but the native builder keeps the application — as does the non-standard
/// named `(is-C e)` spelling — because the fold discards the scrutinee and
/// with it the datatype model collector's record that the query tested that
/// term. `test_datatype_tester_spellings` owns that case in full.
#[test]
fn native_datatype_builders_fold_like_elaboration() {
    let (mut solver, l) = level_solver();
    let dt = level();
    let succ_l = solver.try_datatype_constructor(&dt, "succ", &[l]).unwrap();
    let succ_succ_l = solver
        .try_datatype_constructor(&dt, "succ", &[succ_l])
        .unwrap();
    let pred_succ_l = solver
        .try_datatype_selector("pred", succ_l, Sort::Datatype(dt.clone()))
        .unwrap();
    assert_eq!(pred_succ_l, l);
    let is_succ = solver.try_datatype_tester("succ", succ_l).unwrap();
    assert_eq!(is_succ, solver.bool_const(true));
    let is_zero = solver.try_datatype_tester("zero", succ_l).unwrap();
    assert_eq!(is_zero, solver.bool_const(false));
    let injective = solver.try_eq(succ_succ_l, succ_l).unwrap();
    let fields = solver.try_eq(succ_l, l).unwrap();
    assert_eq!(injective, fields);
    let opaque = solver.try_datatype_tester("succ", l).unwrap();
    assert_ne!(opaque, solver.bool_const(true));

    let pair = ay_core::DatatypeSort::new(
        "Pair",
        vec![ay_core::DatatypeConstructor::new(
            "mk",
            vec![
                ay_core::DatatypeField::new("fst", Sort::Int),
                ay_core::DatatypeField::new("snd", Sort::Int),
            ],
        )],
    );
    solver.try_declare_datatype(&pair).unwrap();
    let p = solver.declare_const("p", Sort::Datatype(pair.clone()));
    let is_mk = solver.try_datatype_tester("mk", p).unwrap();
    assert_ne!(is_mk, solver.bool_const(true));
    solver
        .try_assert_term_with_source(is_mk, "(assert (is-mk p))")
        .unwrap();
    let one = solver.int_const(1);
    let two = solver.int_const(2);
    let mk = solver
        .try_datatype_constructor(&pair, "mk", &[one, two])
        .unwrap();
    let fst = solver.try_datatype_selector("fst", mk, Sort::Int).unwrap();
    assert_eq!(fst, one);
    let claim = solver.try_eq(fst, two).unwrap();
    solver
        .try_assert_term_with_source(claim, "(assert (= (fst (mk 1 2)) 2))")
        .unwrap();
    assert!(!solver.check_sat().is_sat());
}
