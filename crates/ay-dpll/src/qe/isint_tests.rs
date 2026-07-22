// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the dedicated `is_int` existential eliminator (`isint.rs`).
//!
//! The eliminator handles `∃x. φ`; the `∀` cases the pre-pass decides are
//! `¬∃x.¬φ`, so a `∀`-probe is tested by eliminating the negated body and
//! reading the negated result. Closed formulas (no free variable but `x`)
//! reduce to a boolean constant, which is asserted directly.

#![allow(clippy::panic)]

use super::eliminate_exists_isint;
use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;

fn rvar(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::Real)
}

fn rc(terms: &mut TermStore, n: i64, d: i64) -> TermId {
    terms.mk_rational(BigRational::new(BigInt::from(n), BigInt::from(d)))
}

/// `is_int(x + n/d)`.
fn is_int_shift(terms: &mut TermStore, x: TermId, n: i64, d: i64) -> TermId {
    if n == 0 {
        return terms.mk_is_int(x);
    }
    let c = rc(terms, n, d);
    let sum = terms.mk_add(vec![x, c]);
    terms.mk_is_int(sum)
}

/// Eliminate and expect a boolean CONSTANT result; return it.
fn elim_const(terms: &mut TermStore, body: TermId, var: TermId) -> bool {
    let qf = eliminate_exists_isint(terms, body, var).expect("expected elimination to succeed");
    match terms.get(qf) {
        TermData::Const(Constant::Bool(b)) => *b,
        other => panic!("expected a boolean constant, got {other:?}"),
    }
}

/// `∃x. is_int(x) ∧ ¬is_int(x+1)` — unsatisfiable (shift by an integer keeps
/// integrality), so `∃` folds to `false`.
#[test]
fn exists_isint_and_not_isint_shift_one_is_false() {
    let mut t = TermStore::new();
    let x = rvar(&mut t, "x");
    let a = is_int_shift(&mut t, x, 0, 1);
    let b = is_int_shift(&mut t, x, 1, 1);
    let nb = t.mk_not(b);
    let body = t.mk_and(vec![a, nb]);
    assert!(!elim_const(&mut t, body, x));
}

/// `∃x. ¬is_int(x) ∧ ¬is_int(x+1/2)` — the all-false residue vector is
/// attainable (pick `frac(x) ∉ {0, 1/2}`), so `∃` is `true`.
#[test]
fn exists_all_false_vector_attainable_is_true() {
    let mut t = TermStore::new();
    let x = rvar(&mut t, "x");
    let a = is_int_shift(&mut t, x, 0, 1);
    let b = is_int_shift(&mut t, x, 1, 2);
    let na = t.mk_not(a);
    let nb = t.mk_not(b);
    let body = t.mk_and(vec![na, nb]);
    assert!(elim_const(&mut t, body, x));
}

/// `∃x. is_int(x) ∨ is_int(x+1/2)` — the residue-0 vector satisfies it.
#[test]
fn exists_disjunction_is_true() {
    let mut t = TermStore::new();
    let x = rvar(&mut t, "x");
    let a = is_int_shift(&mut t, x, 0, 1);
    let b = is_int_shift(&mut t, x, 1, 2);
    let body = t.mk_or(vec![a, b]);
    assert!(elim_const(&mut t, body, x));
}

/// `∀x. is_int(x) ∨ is_int(x+1/2)` decided as `¬∃x.(¬is_int(x) ∧ ¬is_int(x+1/2))`
/// — the inner `∃` is `true`, so the `∀` is `false` (unsat). This is the
/// wrong-fact twin: fractional-offset disjunction is NOT valid.
#[test]
fn forall_frac_offset_disjunction_is_false() {
    let mut t = TermStore::new();
    let x = rvar(&mut t, "x");
    let a = is_int_shift(&mut t, x, 0, 1);
    let b = is_int_shift(&mut t, x, 1, 2);
    // Negated body: ¬(a ∨ b) = ¬a ∧ ¬b.
    let na = t.mk_not(a);
    let nb = t.mk_not(b);
    let neg_body = t.mk_and(vec![na, nb]);
    // Inner ∃ is true → ∀ is ¬true = false.
    assert!(elim_const(&mut t, neg_body, x));
}

/// Refuse a non-unit coefficient: `is_int(2·x)` — `frac(x) ∈ {0, 1/2}` is not a
/// single critical residue in the `1·x + c` normal form.
#[test]
fn refuses_non_unit_coefficient() {
    let mut t = TermStore::new();
    let x = rvar(&mut t, "x");
    let two = rc(&mut t, 2, 1);
    let two_x = t.mk_mul(vec![two, x]);
    let body = t.mk_is_int(two_x);
    assert!(eliminate_exists_isint(&mut t, body, x).is_none());
}

/// Refuse when `x` occurs outside an `is_int` atom (an LRA bound).
#[test]
fn refuses_var_outside_isint() {
    let mut t = TermStore::new();
    let x = rvar(&mut t, "x");
    let a = is_int_shift(&mut t, x, 0, 1);
    let five = rc(&mut t, 5, 1);
    let lt = t.mk_lt(x, five);
    let body = t.mk_and(vec![a, lt]);
    assert!(eliminate_exists_isint(&mut t, body, x).is_none());
}

/// Refuse a non-constant offset: `is_int(x + y)` (another variable in the
/// offset).
#[test]
fn refuses_non_constant_offset() {
    let mut t = TermStore::new();
    let x = rvar(&mut t, "x");
    let y = rvar(&mut t, "y");
    let sum = t.mk_add(vec![x, y]);
    let body = t.mk_is_int(sum);
    assert!(eliminate_exists_isint(&mut t, body, x).is_none());
}

/// No `is_int` over `x` at all → `None` (LW's job, not ours).
#[test]
fn declines_when_no_isint_over_var() {
    let mut t = TermStore::new();
    let x = rvar(&mut t, "x");
    let five = rc(&mut t, 5, 1);
    let body = t.mk_lt(x, five);
    assert!(eliminate_exists_isint(&mut t, body, x).is_none());
}

/// A free LRA side-constraint (`y < 3`) not mentioning `x` is retained
/// symbolically; the result is not a constant but must still verify.
#[test]
fn keeps_x_free_side_constraint() {
    let mut t = TermStore::new();
    let x = rvar(&mut t, "x");
    let y = rvar(&mut t, "y");
    let a = is_int_shift(&mut t, x, 0, 1);
    let three = rc(&mut t, 3, 1);
    let yc = t.mk_lt(y, three);
    let body = t.mk_and(vec![a, yc]);
    // ∃x. (is_int(x) ∧ y<3) ≡ (y<3): residue-0 vector makes is_int(x) true.
    let qf = eliminate_exists_isint(&mut t, body, x).expect("should eliminate");
    // Result must not mention x and must equal `y < 3`.
    assert_eq!(qf, yc);
}

/// Fail-closed shadow gate (#isint-shadow). When a user declaration has
/// shadowed `is_int` (`TermStore::mark_is_int_shadowed`), the eliminator must
/// decline on the *same* body it would otherwise decide — the shadowed symbol
/// is a free uninterpreted predicate, so applying integrality reasoning would
/// fabricate its semantics. Regression for the wrong-UNSAT introduced by the
/// eliminator: `(declare-fun is_int (Real) Bool)` +
/// `(forall ((x Real)) (is_int x))` decided `unsat` where z3 exhibits the model
/// `is_int ≡ λx.true`.
#[test]
fn declines_when_is_int_shadowed() {
    // Baseline: the un-shadowed body eliminates to a boolean constant.
    let mut base = TermStore::new();
    let x0 = rvar(&mut base, "x");
    let body0 = is_int_shift(&mut base, x0, 0, 1);
    assert!(
        eliminate_exists_isint(&mut base, body0, x0).is_some(),
        "un-shadowed builtin is_int must still be eliminated (no over-refusal)"
    );

    // Shadowed: the byte-identical body must be refused (fail-closed).
    let mut t = TermStore::new();
    t.mark_is_int_shadowed();
    let x = rvar(&mut t, "x");
    let body = is_int_shift(&mut t, x, 0, 1);
    assert!(
        eliminate_exists_isint(&mut t, body, x).is_none(),
        "shadowed is_int must fail-close (decline elimination)"
    );
}
