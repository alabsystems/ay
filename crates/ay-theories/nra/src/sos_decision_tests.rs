// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end decision tests for the verified SOS certificate lane:
//! small polynomial systems whose only refutation in the bounded
//! search is a Positivstellensatz certificate must be decided
//! `Unsat` by `check()`, and a satisfiable neighbour must not be
//! refuted. Genuine z3 decides every system here `unsat`/`sat`
//! accordingly; before the decision lane was wired, `check()`
//! returned `Unknown` on the two strict systems (the homogeneous
//! quadratic pre-phase declines their linear terms, and interval
//! branch-and-prune cannot exhaust their unbounded boxes).

use crate::NraSolver;
use ay_core::term::{TermId, TermStore};
use ay_core::{Sort, TheoryResult, TheorySolver};
use num_bigint::BigInt;
use num_rational::BigRational;

fn rat(terms: &mut TermStore, value: i64) -> TermId {
    terms.mk_rational(BigRational::from_integer(BigInt::from(value)))
}

/// `(x-1)^2 + (y-1)^2`, expanded: `x^2 + y^2 - 2x - 2y + 2`.
fn shifted_circle(terms: &mut TermStore, x: TermId, y: TermId) -> TermId {
    let x2 = terms.mk_mul(vec![x, x]);
    let y2 = terms.mk_mul(vec![y, y]);
    let neg_two = rat(terms, -2);
    let neg_two_x = terms.mk_mul(vec![neg_two, x]);
    let neg_two_y = terms.mk_mul(vec![neg_two, y]);
    let two = rat(terms, 2);
    terms.mk_add(vec![x2, y2, neg_two_x, neg_two_y, two])
}

#[test]
fn shifted_sum_of_squares_strict_is_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let poly = shifted_circle(&mut terms, x, y);
    let zero = rat(&mut terms, 0);
    let atom = terms.mk_lt(poly, zero);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(atom, true);
    assert!(
        matches!(solver.check(), TheoryResult::Unsat(_)),
        "(x-1)^2+(y-1)^2 < 0 is UNSAT"
    );
}

#[test]
fn quartic_sum_of_squares_strict_is_unsat() {
    // (x^2-1)^2 + (xy-1)^2 < 0, expanded.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let x2 = terms.mk_mul(vec![x, x]);
    let x4 = terms.mk_mul(vec![x, x, x, x]);
    let x2y2 = terms.mk_mul(vec![x, x, y, y]);
    let xy = terms.mk_mul(vec![x, y]);
    let neg_two = rat(&mut terms, -2);
    let neg_two_x2 = terms.mk_mul(vec![neg_two, x2]);
    let neg_two_xy = terms.mk_mul(vec![neg_two, xy]);
    let two = rat(&mut terms, 2);
    let poly = terms.mk_add(vec![x4, x2y2, neg_two_x2, neg_two_xy, two]);
    let zero = rat(&mut terms, 0);
    let atom = terms.mk_lt(poly, zero);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(atom, true);
    assert!(
        matches!(solver.check(), TheoryResult::Unsat(_)),
        "(x^2-1)^2+(xy-1)^2 < 0 is UNSAT"
    );
}

#[test]
fn shifted_sum_of_squares_nonstrict_is_not_refuted() {
    // (x-1)^2 + (y-1)^2 <= 0 holds at (1,1): no certificate exists
    // and the decision lane must not manufacture one.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let poly = shifted_circle(&mut terms, x, y);
    let zero = rat(&mut terms, 0);
    let atom = terms.mk_le(poly, zero);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(atom, true);
    assert!(
        !matches!(
            solver.check(),
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "(x-1)^2+(y-1)^2 <= 0 is SAT at (1,1)"
    );
}
