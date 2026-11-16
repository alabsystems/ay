// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The native lane reads a shift by a literal amount as a power-of-two
//! scale; the wire lane never does.

use super::*;

/// external-codegen's `ConstMul_Shift_Sub_I64 a=7`: `x * 127 == (x << 7) - x`.
fn shift_identity(terms: &mut TermStore, constant: u128, shift: u128) -> TermId {
    let width = 64;
    let x = terms.mk_var("x", Sort::bitvec(width));
    let literal = super::constant(terms, constant, width);
    let product = app(terms, "bvmul", literal, x, width);
    let amount = super::constant(terms, shift, width);
    let shifted = app(terms, "bvshl", x, amount, width);
    let difference = app(terms, "bvsub", shifted, x, width);
    eq(terms, product, difference)
}

#[test]
fn a_literal_shift_is_a_power_of_two_scale_in_the_native_lane_only() {
    let mut terms = TermStore::new();
    let identity = shift_identity(&mut terms, 127, 7);
    assert!(check_native(&terms, &[identity], &mut |_, _| true).unwrap());
    // `poly_simp` has no `bvshl`: the wire lane keeps the shift an atom.
    assert!(!check(&terms, &[identity], &mut |_, _| true).unwrap());
    // A wrong scale is refused.
    let mut terms = TermStore::new();
    let wrong = shift_identity(&mut terms, 126, 7);
    assert!(!check_native(&terms, &[wrong], &mut |_, _| true).unwrap());
}

/// A shift past the width is zero, and a symbolic amount stays an atom.
#[test]
fn an_overshift_is_zero_and_a_symbolic_shift_is_an_atom() {
    let width = 8;
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(width));
    let y = terms.mk_var("y", Sort::bitvec(width));
    let nine = constant(&mut terms, 9, width);
    let zero = constant(&mut terms, 0, width);
    let overshift = app(&mut terms, "bvshl", x, nine, width);
    let equality = eq(&mut terms, overshift, zero);
    assert!(check_native(&terms, &[equality], &mut |_, _| true).unwrap());
    let symbolic = app(&mut terms, "bvshl", x, y, width);
    let doubled = app(&mut terms, "bvadd", x, x, width);
    let equality = eq(&mut terms, symbolic, doubled);
    assert!(!check_native(&terms, &[equality], &mut |_, _| true).unwrap());
}

/// The printer lowers such an identity through the checked bit-blast lane
/// when it arrives as a native arithmetic tautology.
#[test]
fn a_native_shift_identity_has_a_checked_lowering() {
    let mut terms = TermStore::new();
    let identity = shift_identity(&mut terms, 127, 7);
    assert!(crate::theory_lemma_bv_arithmetic_lowering_supported(
        &terms,
        &TheoryLemmaKind::ArithClauseTautology,
        &[identity],
        None,
        &mut crate::ArithPolySimpPromotionBudget::standalone(),
    ));
}
