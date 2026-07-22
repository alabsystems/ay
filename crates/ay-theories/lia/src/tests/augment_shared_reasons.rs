// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for `augment_farkas_with_shared_reasons` (#8147 +
//! adversarial-review fix on #rank-4 increment 2).
//!
//! The appended shared-equality/Dioph reasons are load-bearing exactly when
//! the simplex Farkas builder missed pivoted-away slack reasons (#8147), but
//! `minimize_farkas_conflict` (ay-dpll) strips every zero-coefficient literal
//! from the learned clause in ALL builds. A certificate zero-extended over
//! appended reasons therefore re-creates the #8147 false-UNSAT class. The
//! contract under test: augmentation that appends literals DROPS the
//! certificate; the no-append case keeps it.

use super::*;
use ay_core::{FarkasAnnotation, TheoryConflict, TheoryLit, TheorySolver};
use num_rational::Rational64;

fn farkas_ones(n: usize) -> FarkasAnnotation {
    FarkasAnnotation::new(vec![Rational64::from(1); n])
}

/// Augmentation that APPENDS a shared-equality reason must drop the
/// certificate entirely (never zero-extend it over the appended literals).
#[test]
fn test_augmentation_appending_reasons_drops_certificate() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let seven = terms.mk_int(BigInt::from(7));
    let eq_x0 = terms.mk_eq(x, zero);
    let eq_x1 = terms.mk_eq(x, one);
    let eq_y7 = terms.mk_eq(y, seven); // the shared-equality reason

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq_x0, true);
    solver.assert_literal(eq_x1, true);
    solver.assert_literal(eq_y7, true);
    // Shared equality x = y with a live reason literal. The conflict
    // literals mention x, so the reason is relevant and must be appended.
    solver.assert_shared_equality(x, y, &[TheoryLit::new(eq_y7, true)]);

    let conflict = TheoryConflict::with_farkas(
        vec![TheoryLit::new(eq_x0, true), TheoryLit::new(eq_x1, true)],
        farkas_ones(2),
    );
    let augmented = solver.augment_farkas_with_shared_reasons(conflict);

    assert!(
        augmented.literals.contains(&TheoryLit::new(eq_y7, true)),
        "the relevant shared-equality reason must be appended: {augmented:?}"
    );
    assert_eq!(augmented.literals.len(), 3, "{augmented:?}");
    assert!(
        augmented.farkas.is_none(),
        "appended reasons may be load-bearing; the certificate must be \
         DROPPED, not zero-extended (minimize_farkas_conflict strips \
         zero-coefficient literals in all builds): {augmented:?}"
    );
}

/// Augmentation that appends NOTHING (shared equalities exist but are
/// irrelevant to the conflict) keeps the certificate — still a strict
/// improvement over the parent, which dropped it wholesale.
#[test]
fn test_augmentation_without_appends_keeps_certificate() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let seven = terms.mk_int(BigInt::from(7));
    let eq_w0 = terms.mk_eq(w, zero);
    let eq_w1 = terms.mk_eq(w, one);
    let eq_y7 = terms.mk_eq(y, seven);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq_w0, true);
    solver.assert_literal(eq_w1, true);
    solver.assert_literal(eq_y7, true);
    // Shared equality over x/y — unreachable from the w-only conflict.
    solver.assert_shared_equality(x, y, &[TheoryLit::new(eq_y7, true)]);

    let conflict = TheoryConflict::with_farkas(
        vec![TheoryLit::new(eq_w0, true), TheoryLit::new(eq_w1, true)],
        farkas_ones(2),
    );
    let augmented = solver.augment_farkas_with_shared_reasons(conflict);

    assert_eq!(
        augmented.literals.len(),
        2,
        "irrelevant shared-equality reasons must NOT be appended: {augmented:?}"
    );
    let farkas = augmented
        .farkas
        .expect("no-append augmentation must keep the certificate");
    assert_eq!(farkas.coefficients.len(), 2);
}
