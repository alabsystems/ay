// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Which datatype-tester spellings reconstruct a natively built tester.
//!
//! SMT-LIB 2.6 spells a tester `((_ is C) e)`. AY also accepts the
//! non-standard named spelling `(is-C e)` that several producers emit.
//! `try_assert_term_with_source` retains a native assertion only when its
//! source re-elaborates, in this solver, to the very term that was asserted,
//! so which spellings reconstruct a native tester is decided entirely by which
//! spellings elaborate to the term the native builder builds.
//!
//! The axes are the datatype's constructor count and whether the scrutinee is
//! a LITERAL constructor application or OPAQUE. Three of those four cells fold
//! identically under both spellings. The fourth — a SOLE-constructor tester
//! over an OPAQUE scrutinee — does not, and deliberately so:
//!
//!   * `((_ is C) e)` elaborates to `true` (`elaborate_indexed_app`). That
//!     fold is sound and load-bearing: it collapses an `ite` guard so the
//!     standalone DT occurs-check can see a cycle through the guarded branch.
//!   * `(is-C e)` and the native builder keep the application, because the
//!     fold DISCARDS the scrutinee, and a scrutinee the datatype model
//!     collector never sees costs its class
//!     `ConstructorForceOrigin::PositiveTester` and its authored W6
//!     array-field authorization.
//!
//! So the named spelling reconstructs there and the indexed one does not —
//! which is also what origin/main did. This file pins every cell so a future
//! change to any of them is deliberate, and pins the provenance consequence of
//! folding.

use crate::api::{Logic, Solver, Sort, Term};

/// `Level = zero | succ(pred: Level)` — two constructors.
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

/// `Box = box(unbox: Int)` — one constructor, so `((_ is box) b)` is
/// definitionally `true` for every `b: Box`.
fn boxed() -> ay_core::DatatypeSort {
    ay_core::DatatypeSort::new(
        "Box",
        vec![ay_core::DatatypeConstructor::new(
            "box",
            vec![ay_core::DatatypeField::new("unbox", Sort::Int)],
        )],
    )
}

/// A solver with both datatypes declared, plus an opaque constant of each.
fn tester_solver() -> (Solver, Term, Term) {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    solver.try_declare_datatype(&level()).unwrap();
    solver.try_declare_datatype(&boxed()).unwrap();
    let l = solver.declare_const("l", Sort::Datatype(level()));
    let b = solver.declare_const("b", Sort::Datatype(boxed()));
    (solver, l, b)
}

/// Every listed source must reconstruct `native`, on a scope that is rolled
/// back so the assertions cannot interact.
fn assert_each_source_reconstructs(solver: &mut Solver, native: Term, sources: &[&str]) {
    for source in sources {
        solver.try_push().unwrap();
        solver
            .try_assert_term_with_source(native, source)
            .unwrap_or_else(|error| panic!("{source} must reconstruct the native tester: {error}"));
        solver.try_pop().unwrap();
    }
}

/// Every listed source must be REFUSED, with nothing entering the stack.
fn assert_each_source_is_refused(solver: &mut Solver, native: Term, sources: &[&str]) {
    for source in sources {
        assert!(
            solver.try_assert_term_with_source(native, source).is_err(),
            "{source} must not reconstruct this native tester",
        );
        assert_eq!(solver.assertions(), [] as [Term; 0]);
    }
}

/// SOLE constructor, OPAQUE scrutinee — the one cell where the two spellings
/// part company.
///
/// The native tester keeps the application, so the named `(is-box b)` spelling
/// reconstructs it and the indexed `((_ is box) b)` spelling — which folds to
/// `true` — does not. This is the regression the fix restores: while the
/// native builder folded here, `(is-box b)` was refused for a query that
/// authored it.
#[test]
fn sole_constructor_tester_over_an_opaque_scrutinee_keeps_the_named_spelling() {
    let (mut solver, _l, b) = tester_solver();
    let is_box = solver.try_datatype_tester("box", b).unwrap();
    assert_ne!(
        is_box,
        solver.bool_const(true),
        "the native sole-constructor tester keeps its scrutinee observable",
    );
    assert_each_source_reconstructs(&mut solver, is_box, &["(assert (is-box b))"]);
    assert_each_source_is_refused(&mut solver, is_box, &["(assert ((_ is box) b))"]);
}

/// SOLE constructor, LITERAL scrutinee. Here the tester folds to `true` by
/// constructor distinctness under BOTH spellings and in the native builder, so
/// both spellings reconstruct it.
#[test]
fn sole_constructor_tester_over_a_literal_scrutinee_folds_under_both_spellings() {
    let (mut solver, _l, _b) = tester_solver();
    let dt = boxed();
    let seven = solver.int_const(7);
    let box_7 = solver
        .try_datatype_constructor(&dt, "box", &[seven])
        .unwrap();
    let is_box = solver.try_datatype_tester("box", box_7).unwrap();
    assert_eq!(is_box, solver.bool_const(true));
    assert_each_source_reconstructs(
        &mut solver,
        is_box,
        &["(assert (is-box (box 7)))", "(assert ((_ is box) (box 7)))"],
    );
}

/// MULTI constructor, OPAQUE scrutinee. The tester carries information, so it
/// folds under NEITHER spelling — the sole-constructor rule must not leak to a
/// datatype that has a second constructor — and both spellings name the same
/// application.
#[test]
fn multi_constructor_tester_stays_opaque_under_both_spellings() {
    let (mut solver, l, _b) = tester_solver();
    let is_succ = solver.try_datatype_tester("succ", l).unwrap();
    let is_zero = solver.try_datatype_tester("zero", l).unwrap();
    assert_ne!(
        is_succ,
        solver.bool_const(true),
        "`(is-succ l)` for an opaque `l` is not definitionally true",
    );
    assert_ne!(is_succ, solver.bool_const(false));
    assert_ne!(
        is_succ, is_zero,
        "the two constructors' testers are different assertions",
    );
    assert_each_source_reconstructs(
        &mut solver,
        is_succ,
        &["(assert (is-succ l))", "(assert ((_ is succ) l))"],
    );
    assert_each_source_reconstructs(
        &mut solver,
        is_zero,
        &["(assert (is-zero l))", "(assert ((_ is zero) l))"],
    );

    // The guard is not weakened by any fold: a tester naming the OTHER
    // constructor, or the right constructor over another scrutinee, is a
    // different assertion and is refused under both spellings.
    assert_each_source_is_refused(
        &mut solver,
        is_succ,
        &[
            "(assert (is-zero l))",
            "(assert ((_ is zero) l))",
            "(assert (is-succ (succ l)))",
            "(assert ((_ is succ) (succ l)))",
        ],
    );
}

/// MULTI constructor, LITERAL scrutinee. The tester folds by distinctness —
/// `true` for the constructor that built it, `false` for the other — and both
/// spellings reach the same constant.
#[test]
fn multi_constructor_tester_folds_by_distinctness_under_both_spellings() {
    let (mut solver, l, _b) = tester_solver();
    let dt = level();
    let succ_l = solver.try_datatype_constructor(&dt, "succ", &[l]).unwrap();
    let is_succ = solver.try_datatype_tester("succ", succ_l).unwrap();
    let is_zero = solver.try_datatype_tester("zero", succ_l).unwrap();
    assert_eq!(is_succ, solver.bool_const(true));
    assert_eq!(is_zero, solver.bool_const(false));
    assert_each_source_reconstructs(
        &mut solver,
        is_succ,
        &[
            "(assert (is-succ (succ l)))",
            "(assert ((_ is succ) (succ l)))",
        ],
    );
    assert_each_source_reconstructs(
        &mut solver,
        is_zero,
        &[
            "(assert (is-zero (succ l)))",
            "(assert ((_ is zero) (succ l)))",
        ],
    );
}

/// PROVENANCE BOUND, pinned so a future change to it is deliberate.
///
/// `try_assert_term_with_source` compares the BUILT assertion — one canonical
/// `TermId` — against the term its source elaborates to. For a tester that
/// folds all the way to a CONSTANT, every source that elaborates to that same
/// constant is that same `TermId`, so an unrelated `(assert true)` is accepted
/// as the retained source of `((_ is succ) (succ l))`.
///
/// This certifies what it always certified: the retained text denotes exactly
/// the formula that entered the assertion stack. It does NOT certify that the
/// text is the caller's own spelling, nor that it shares any structure with
/// how the term was built — for a folded constant there is no structure left
/// to share. A source denoting a DIFFERENT formula, including the opposite
/// constant, is still refused.
#[test]
fn a_tester_that_folds_to_a_constant_accepts_any_source_for_that_constant() {
    let (mut solver, l, _b) = tester_solver();
    let dt = level();
    let succ_l = solver.try_datatype_constructor(&dt, "succ", &[l]).unwrap();
    let is_succ = solver.try_datatype_tester("succ", succ_l).unwrap();
    let is_zero = solver.try_datatype_tester("zero", succ_l).unwrap();
    assert_eq!(is_succ, solver.bool_const(true));
    assert_eq!(is_zero, solver.bool_const(false));

    // Accepted: an unrelated source that elaborates to the same constant,
    // including one folded out of a different datatype's tester.
    assert_each_source_reconstructs(
        &mut solver,
        is_succ,
        &["(assert true)", "(assert ((_ is box) b))"],
    );
    assert_each_source_reconstructs(&mut solver, is_zero, &["(assert false)"]);

    // Refused: the opposite constant is a different formula.
    assert_each_source_is_refused(&mut solver, is_succ, &["(assert false)"]);
    assert_each_source_is_refused(&mut solver, is_zero, &["(assert true)"]);
}
