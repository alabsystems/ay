// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rows with a non-integral constant, and rows over Real-sorted columns.
//!
//! Regression for the QSAT kernel's wrong UNSAT (fuzzer fz5/s505_12): the
//! kernel solves UNPREPROCESSED roots, so the LIA lane received
//! `(= (to_real c) (+ (to_real c) 1/2))` with `to_real c` uncancelled. The
//! linear parse dropped the non-integral constant, read the atom as `0 = 0`,
//! and refuted its (valid) negation as a self-contradictory disequality.

use super::*;
use ay_core::term::Symbol;
use num_rational::BigRational;

fn half(terms: &mut TermStore) -> TermId {
    terms.mk_rational(BigRational::new(BigInt::from(1), BigInt::from(2)))
}

/// `(= lhs rhs)` built raw: no term-layer folding may hide the shape.
fn raw_eq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [lhs, rhs], Sort::Bool)
}

fn raw_add(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("+"), [lhs, rhs], Sort::Real)
}

fn raw_to_real(terms: &mut TermStore, arg: TermId) -> TermId {
    terms.mk_app(Symbol::named("to_real"), [arg], Sort::Real)
}

fn is_unsat(result: &TheoryResult) -> bool {
    matches!(
        result,
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
    )
}

#[test]
fn nonintegral_constant_row_is_scaled_not_dropped() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Int);
    let d = terms.mk_var("d", Sort::Int);
    let rc = raw_to_real(&mut terms, c);
    let rd = raw_to_real(&mut terms, d);
    let h = half(&mut terms);
    let rhs = raw_add(&mut terms, rd, h);

    let solver = LiaSolver::new(&terms);
    let (coeffs, constant) = solver.parse_linear_expr_with_vars(rc, rhs);
    // to_real c - to_real d = 1/2, scaled by 2.
    assert_eq!(coeffs.get(&rc), Some(&BigInt::from(2)));
    assert_eq!(coeffs.get(&rd), Some(&BigInt::from(-2)));
    assert_eq!(constant, BigInt::from(1));

    // The self-referential atom normalises to the constant row `0 = 1/2`,
    // never `0 = 0`.
    let self_rhs = raw_add(&mut terms, rc, h);
    let solver = LiaSolver::new(&terms);
    let (coeffs, constant) = solver.parse_linear_expr_with_vars(rc, self_rhs);
    assert!(coeffs.values().all(Zero::is_zero), "{coeffs:?}");
    assert!(!constant.is_zero());
}

/// The kernel's exact shape: `c = d` (so the affine check runs) beside the
/// VALID disequality `to_real c != to_real c + 1/2`. Before the fix this was
/// a 1-literal conflict on the disequality.
#[test]
fn valid_nonintegral_disequality_is_never_a_conflict() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Int);
    let d = terms.mk_var("d", Sort::Int);
    let rc = raw_to_real(&mut terms, c);
    let h = half(&mut terms);
    let rhs = raw_add(&mut terms, rc, h);
    let taut = raw_eq(&mut terms, rc, rhs);
    let c_eq_d = raw_eq(&mut terms, c, d);

    let mut solver = LiaSolver::new(&terms);
    solver.register_atom(taut);
    solver.register_atom(c_eq_d);
    solver.assert_literal(c_eq_d, true);
    solver.assert_literal(taut, false);
    let result = solver.check();
    assert!(!is_unsat(&result), "valid disequality refuted: {result:?}");
}

/// Two variables: `to_real c = to_real d` and `to_real c != to_real d + 1/2`
/// is satisfiable (any c = d); the dropped constant made the affine check
/// read the disequality as the negation of the equality and refute it.
#[test]
fn nonintegral_offset_disequality_is_not_implied_false() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Int);
    let d = terms.mk_var("d", Sort::Int);
    let rc = raw_to_real(&mut terms, c);
    let rd = raw_to_real(&mut terms, d);
    let h = half(&mut terms);
    let rhs = raw_add(&mut terms, rd, h);
    let offset_eq = raw_eq(&mut terms, rc, rhs);
    let c_eq_d = raw_eq(&mut terms, rc, rd);

    let mut solver = LiaSolver::new(&terms);
    solver.register_atom(offset_eq);
    solver.register_atom(c_eq_d);
    solver.assert_literal(c_eq_d, true);
    solver.assert_literal(offset_eq, false);
    let result = solver.check();
    assert!(
        !is_unsat(&result),
        "satisfiable context refuted: {result:?}"
    );
}

/// The equality itself is impossible over integer-valued columns, and the
/// exact (scaled) row lets the GCD test say so: `2c - 2d = 1`.
#[test]
fn nonintegral_offset_equality_over_integer_columns_is_refuted() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Int);
    let d = terms.mk_var("d", Sort::Int);
    let rc = raw_to_real(&mut terms, c);
    let rd = raw_to_real(&mut terms, d);
    let h = half(&mut terms);
    let rhs = raw_add(&mut terms, rd, h);
    let offset_eq = raw_eq(&mut terms, rc, rhs);

    let mut solver = LiaSolver::new(&terms);
    solver.register_atom(offset_eq);
    solver.assert_literal(offset_eq, true);
    let conflict = solver
        .gcd_test()
        .expect("2c - 2d = 1 has no integer solution");
    assert_eq!(conflict.literals, vec![TheoryLit::new(offset_eq, true)]);
    assert!(!matches!(solver.check(), TheoryResult::Sat));
}

/// A Real-sorted column may take a fractional value: `2·r = 1` holds at
/// r = 1/2, so integer divisibility must not refute it.
#[test]
fn real_sorted_column_gets_no_integer_divisibility_conflict() {
    let mut terms = TermStore::new();
    let r = terms.mk_var("r", Sort::Real);
    let two = terms.mk_rational(BigRational::from_integer(BigInt::from(2)));
    let one = terms.mk_rational(BigRational::from_integer(BigInt::from(1)));
    let two_r = terms.mk_app(Symbol::named("*"), [two, r], Sort::Real);
    let eq = raw_eq(&mut terms, two_r, one);

    let solver = LiaSolver::new(&terms);
    let cached = solver.cached_linear(two_r, one);
    assert!(cached.gcd_divides, "Real column refuted by divisibility");
    assert_eq!(
        cached.modular_candidates.as_slice(),
        &[] as &[(TermId, BigInt, BigInt)]
    );

    let mut solver = LiaSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    assert!(solver.gcd_test().is_none());
}

/// A barren `gcd_test` verdict is a pure function of the asserted
/// positive equalities (each atom's cached linear form is
/// assignment-independent), so the scan stamps the positive-equality
/// epoch and an inequality-only assertion must not invalidate it.
/// The stamp is what lets repeat calls skip the scan entirely.
#[test]
fn gcd_barren_stamp_survives_inequality_only_assertion() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let ten = terms.mk_int(BigInt::from(10));
    let x_plus_y = terms.mk_add(vec![x, y]);
    let eq = terms.mk_eq(x_plus_y, three);
    let lt = terms.mk_lt(x, ten);

    let mut solver = LiaSolver::new(&terms);
    solver.register_atom(eq);
    solver.register_atom(lt);
    solver.assert_literal(eq, true);

    assert!(solver.gcd_test().is_none(), "x + y = 3 is divisible");
    let stamp = solver.gcd_barren_pos_eq_epoch;
    assert_eq!(
        stamp,
        Some(solver.assertion_view_cache.pos_eq_epoch()),
        "barren scan must stamp the positive-equality epoch"
    );

    solver.assert_literal(lt, true);
    assert!(solver.gcd_test().is_none());
    assert_eq!(
        solver.gcd_barren_pos_eq_epoch, stamp,
        "an inequality-only assertion must not move the barren stamp"
    );
}
