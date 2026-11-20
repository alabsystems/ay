// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Red-first tests for the ICP relaxed second parse pass: atoms
//! the exact multivariate parser declines (division by a
//! proven-nonzero denominator, uninterpreted-function leaves)
//! enter the ICP problem in cleared/opaque form for UNSAT only.
//! Genuine z3 decides the first four systems `unsat`; before the
//! relaxed pass existed, `check()` returned `Unknown` on each.
//! The last system is satisfiable precisely because its
//! denominator is not proven nonzero, and must never be refuted.

use crate::NraSolver;
use ay_core::term::{Symbol, TermId, TermStore};
use ay_core::{Sort, TheoryResult, TheorySolver};
use num_bigint::BigInt;
use num_rational::BigRational;

fn rat(terms: &mut TermStore, value: i64) -> TermId {
    terms.mk_rational(BigRational::from_integer(BigInt::from(value)))
}

fn frac(terms: &mut TermStore, num: i64, den: i64) -> TermId {
    terms.mk_rational(BigRational::new(BigInt::from(num), BigInt::from(den)))
}

#[test]
fn division_by_proven_positive_variable_is_cleared_and_refuted() {
    // x >= 1, y = 1/x, y > 1: clearing the proven-positive
    // denominator gives y*x = 1 with y > 1 and x >= 1, infeasible.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let one = rat(&mut terms, 1);
    let x_ge_1 = terms.mk_ge(x, one);
    let recip = terms.mk_div(one, x);
    let y_eq_recip = terms.mk_eq(y, recip);
    let y_gt_1 = terms.mk_gt(y, one);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(x_ge_1, true);
    solver.assert_literal(y_eq_recip, true);
    solver.assert_literal(y_gt_1, true);
    assert!(
        matches!(solver.check(), TheoryResult::Unsat(_)),
        "x>=1, y=1/x, y>1 is UNSAT"
    );
}

#[test]
fn self_division_below_one_half_is_refuted() {
    // x >= 2 and x/x < 1/2: with x proven nonzero, x/x = 1.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let two = rat(&mut terms, 2);
    let half = frac(&mut terms, 1, 2);
    let x_ge_2 = terms.mk_ge(x, two);
    let self_div = terms.mk_div(x, x);
    let lt_half = terms.mk_lt(self_div, half);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(x_ge_2, true);
    solver.assert_literal(lt_half, true);
    assert!(
        matches!(solver.check(), TheoryResult::Unsat(_)),
        "x>=2, x/x<1/2 is UNSAT"
    );
}

#[test]
fn opaque_uf_square_negative_is_refuted() {
    // f(x)^2 = -1: treating the UF leaf as an opaque real in the
    // relaxed problem refutes it for every UF interpretation.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let fx = terms.mk_app(Symbol::Named("f".to_string().into()), [x], Sort::Real);
    let sq = terms.mk_mul(vec![fx, fx]);
    let neg_one = rat(&mut terms, -1);
    let eq = terms.mk_eq(sq, neg_one);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(eq, true);
    assert!(
        matches!(solver.check(), TheoryResult::Unsat(_)),
        "f(x)^2 = -1 is UNSAT"
    );
}

#[test]
fn uf_equal_to_reciprocal_above_two_is_refuted() {
    // x >= 1, f(x) = 1/x, f(x) > 2: clearing gives f(x)*x = 1
    // with the opaque leaf above 2 and x at least 1, infeasible.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let fx = terms.mk_app(Symbol::Named("f".to_string().into()), [x], Sort::Real);
    let one = rat(&mut terms, 1);
    let two = rat(&mut terms, 2);
    let x_ge_1 = terms.mk_ge(x, one);
    let recip = terms.mk_div(one, x);
    let fx_eq_recip = terms.mk_eq(fx, recip);
    let fx_gt_2 = terms.mk_gt(fx, two);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(x_ge_1, true);
    solver.assert_literal(fx_eq_recip, true);
    solver.assert_literal(fx_gt_2, true);
    assert!(
        matches!(solver.check(), TheoryResult::Unsat(_)),
        "x>=1, f(x)=1/x, f(x)>2 is UNSAT"
    );
}

#[test]
fn division_without_nonzero_proof_is_not_refuted() {
    // y = 1/x and y > 1 with NO bound on x is SAT (x = 1/2); the
    // denominator has no sign proof, so nothing may be cleared
    // and the relaxed pass must not manufacture a refutation.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let one = rat(&mut terms, 1);
    let recip = terms.mk_div(one, x);
    let y_eq_recip = terms.mk_eq(y, recip);
    let y_gt_1 = terms.mk_gt(y, one);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(y_eq_recip, true);
    solver.assert_literal(y_gt_1, true);
    assert!(
        !matches!(
            solver.check(),
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "y=1/x, y>1 is SAT at x=1/2"
    );
}
