// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for Loos-Weispfenning virtual substitution (`lw.rs`).
//!
//! Semantic cases evaluate the eliminated output with the module's own
//! independent evaluator at concrete free-variable points and compare with
//! the hand-computed truth of `∃x.φ`. Adversarial coverage: equalities,
//! strict bounds over the DENSE reals (where the Int intuition is wrong),
//! `≠` punctures (including a punctured closed point), unbounded directions,
//! scaled coefficients, and out-of-fragment refusals.

#![allow(clippy::panic)]

use super::{eliminate_exists_real, eval_real, RealEval};
use crate::qe::QeResult;
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;
use std::collections::HashMap;

fn rvar(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::Real)
}

fn rc(terms: &mut TermStore, n: i64, d: i64) -> TermId {
    terms.mk_rational(BigRational::new(BigInt::from(n), BigInt::from(d)))
}

/// Eliminate and expect success; panic (test failure) on refusal.
fn elim(terms: &mut TermStore, body: TermId, var: TermId) -> TermId {
    match eliminate_exists_real(terms, body, var) {
        QeResult::Eliminated(qf) => qf,
        QeResult::NotSupported => panic!("expected elimination to succeed"),
    }
}

/// Evaluate the eliminated output at a ground point.
fn eval_at(terms: &TermStore, result: TermId, binds: &[(TermId, BigRational)]) -> bool {
    let assign: HashMap<TermId, BigRational> = binds.iter().cloned().collect();
    match eval_real(terms, result, &assign) {
        Some(RealEval::Bool(b)) => b,
        _ => panic!("LW output must evaluate to a definite boolean"),
    }
}

fn ratio(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

/// Whether `var` occurs in `term` (the eliminated variable must not).
fn mentions(terms: &TermStore, term: TermId, var: TermId) -> bool {
    if term == var {
        return true;
    }
    match terms.get(term) {
        TermData::Not(inner) => mentions(terms, *inner, var),
        TermData::App(_, args) => args.iter().any(|&a| mentions(terms, a, var)),
        TermData::Ite(c, t, e) => {
            mentions(terms, *c, var) || mentions(terms, *t, var) || mentions(terms, *e, var)
        }
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Equality substitution
// ---------------------------------------------------------------------------

#[test]
fn equality_always_solvable() {
    // ∃x. x = y + 1 — true for every y (the p1 probe core).
    let mut terms = TermStore::new();
    let x = rvar(&mut terms, "x");
    let y = rvar(&mut terms, "y");
    let one = rc(&mut terms, 1, 1);
    let yp1 = terms.mk_add(vec![y, one]);
    let body = terms.mk_eq(x, yp1);
    let qf = elim(&mut terms, body, x);
    assert!(!mentions(&terms, qf, x));
    for v in [ratio(0, 1), ratio(5, 1), ratio(-3, 2), ratio(1000, 7)] {
        assert!(eval_at(&terms, qf, &[(y, v)]));
    }
}

#[test]
fn conflicting_equalities_unsolvable() {
    // ∃x. (x = y + 1 ∧ x = y + 2) — false for every y (the wrong-twin core).
    let mut terms = TermStore::new();
    let x = rvar(&mut terms, "x");
    let y = rvar(&mut terms, "y");
    let one = rc(&mut terms, 1, 1);
    let two = rc(&mut terms, 2, 1);
    let yp1 = terms.mk_add(vec![y, one]);
    let yp2 = terms.mk_add(vec![y, two]);
    let e1 = terms.mk_eq(x, yp1);
    let e2 = terms.mk_eq(x, yp2);
    let body = terms.mk_and(vec![e1, e2]);
    let qf = elim(&mut terms, body, x);
    for v in [ratio(0, 1), ratio(-7, 3), ratio(42, 1)] {
        assert!(!eval_at(&terms, qf, &[(y, v)]));
    }
}

#[test]
fn scaled_equality_with_guard() {
    // ∃x. (2x = y ∧ x > 0) — true iff y > 0.
    let mut terms = TermStore::new();
    let x = rvar(&mut terms, "x");
    let y = rvar(&mut terms, "y");
    let two = rc(&mut terms, 2, 1);
    let zero = rc(&mut terms, 0, 1);
    let two_x = terms.mk_mul(vec![two, x]);
    let e = terms.mk_eq(two_x, y);
    let g = terms.mk_gt(x, zero);
    let body = terms.mk_and(vec![e, g]);
    let qf = elim(&mut terms, body, x);
    assert!(eval_at(&terms, qf, &[(y, ratio(1, 1))]));
    assert!(eval_at(&terms, qf, &[(y, ratio(1, 3))]));
    assert!(!eval_at(&terms, qf, &[(y, ratio(0, 1))]));
    assert!(!eval_at(&terms, qf, &[(y, ratio(-2, 1))]));
}

// ---------------------------------------------------------------------------
// Strict bounds over the dense reals
// ---------------------------------------------------------------------------

#[test]
fn empty_strict_interval_is_false() {
    // ∃x. (x > y ∧ x < y) — false for every y.
    let mut terms = TermStore::new();
    let x = rvar(&mut terms, "x");
    let y = rvar(&mut terms, "y");
    let g = terms.mk_gt(x, y);
    let l = terms.mk_lt(x, y);
    let body = terms.mk_and(vec![g, l]);
    let qf = elim(&mut terms, body, x);
    for v in [ratio(0, 1), ratio(9, 4)] {
        assert!(!eval_at(&terms, qf, &[(y, v)]));
    }
}

#[test]
fn open_unit_interval_is_true_over_reals() {
    // ∃x. (x > y ∧ x < y + 1) — TRUE over the dense reals for every y
    // (the Int analogue is false; classic strictness pitfall).
    let mut terms = TermStore::new();
    let x = rvar(&mut terms, "x");
    let y = rvar(&mut terms, "y");
    let one = rc(&mut terms, 1, 1);
    let yp1 = terms.mk_add(vec![y, one]);
    let g = terms.mk_gt(x, y);
    let l = terms.mk_lt(x, yp1);
    let body = terms.mk_and(vec![g, l]);
    let qf = elim(&mut terms, body, x);
    for v in [ratio(0, 1), ratio(-5, 2), ratio(17, 3)] {
        assert!(eval_at(&terms, qf, &[(y, v)]));
    }
}

// ---------------------------------------------------------------------------
// ≠ punctures
// ---------------------------------------------------------------------------

#[test]
fn closed_point_true_but_punctured_point_false() {
    // ∃x. (x ≥ y ∧ x ≤ y) — true (the point x = y) …
    let mut terms = TermStore::new();
    let x = rvar(&mut terms, "x");
    let y = rvar(&mut terms, "y");
    let ge = terms.mk_ge(x, y);
    let le = terms.mk_le(x, y);
    let point = terms.mk_and(vec![ge, le]);
    let qf_point = elim(&mut terms, point, x);
    assert!(eval_at(&terms, qf_point, &[(y, ratio(3, 2))]));

    // … but ∃x. (x ≥ y ∧ x ≤ y ∧ x ≠ y) — false (the single point is
    // punctured away).
    let eq = terms.mk_eq(x, y);
    let ne = terms.mk_not(eq);
    let punctured = terms.mk_and(vec![ge, le, ne]);
    let qf_punct = elim(&mut terms, punctured, x);
    for v in [ratio(0, 1), ratio(3, 2), ratio(-11, 5)] {
        assert!(!eval_at(&terms, qf_punct, &[(y, v)]));
    }
}

#[test]
fn punctured_open_interval_stays_true() {
    // ∃x. (x > y ∧ x < y + 2 ∧ x ≠ y + 1) — true (density survives one hole).
    let mut terms = TermStore::new();
    let x = rvar(&mut terms, "x");
    let y = rvar(&mut terms, "y");
    let one = rc(&mut terms, 1, 1);
    let two = rc(&mut terms, 2, 1);
    let yp1 = terms.mk_add(vec![y, one]);
    let yp2 = terms.mk_add(vec![y, two]);
    let g = terms.mk_gt(x, y);
    let l = terms.mk_lt(x, yp2);
    let eq = terms.mk_eq(x, yp1);
    let ne = terms.mk_not(eq);
    let body = terms.mk_and(vec![g, l, ne]);
    let qf = elim(&mut terms, body, x);
    for v in [ratio(0, 1), ratio(7, 2)] {
        assert!(eval_at(&terms, qf, &[(y, v)]));
    }
}

// ---------------------------------------------------------------------------
// Unbounded directions
// ---------------------------------------------------------------------------

#[test]
fn unbounded_below_is_true() {
    // ∃x. x < y — true for every y (−∞ case).
    let mut terms = TermStore::new();
    let x = rvar(&mut terms, "x");
    let y = rvar(&mut terms, "y");
    let body = terms.mk_lt(x, y);
    let qf = elim(&mut terms, body, x);
    assert!(eval_at(&terms, qf, &[(y, ratio(-1000, 1))]));
}

#[test]
fn single_disequality_is_true() {
    // ∃x. x ≠ y — true for every y.
    let mut terms = TermStore::new();
    let x = rvar(&mut terms, "x");
    let y = rvar(&mut terms, "y");
    let eq = terms.mk_eq(x, y);
    let body = terms.mk_not(eq);
    let qf = elim(&mut terms, body, x);
    assert!(eval_at(&terms, qf, &[(y, ratio(4, 7))]));
}

#[test]
fn unbounded_above_lower_bound_is_true() {
    // ∃x. x > y — true (covered by the e+ε candidate, not −∞).
    let mut terms = TermStore::new();
    let x = rvar(&mut terms, "x");
    let y = rvar(&mut terms, "y");
    let body = terms.mk_gt(x, y);
    let qf = elim(&mut terms, body, x);
    assert!(eval_at(&terms, qf, &[(y, ratio(123, 8))]));
}

// ---------------------------------------------------------------------------
// Refusals (fail-closed)
// ---------------------------------------------------------------------------

#[test]
fn refuses_int_bound_variable() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let body = terms.mk_gt(x, zero);
    assert_eq!(
        eliminate_exists_real(&mut terms, body, x),
        QeResult::NotSupported
    );
}

#[test]
fn refuses_bare_int_free_variable() {
    // A BARE Int variable in a literal (not bridged through `to_real`) must
    // still refuse: the emitted substitution terms would not be well-sorted.
    let mut terms = TermStore::new();
    let x = rvar(&mut terms, "x");
    let n = terms.mk_var("n", Sort::Int);
    let body = terms.mk_app(Symbol::named("<="), vec![n, x], Sort::Bool);
    assert_eq!(
        eliminate_exists_real(&mut terms, body, x),
        QeResult::NotSupported
    );
}

#[test]
fn refuses_nonlinear_matrix() {
    // ∃x. x·x = y — out of fragment.
    let mut terms = TermStore::new();
    let x = rvar(&mut terms, "x");
    let y = rvar(&mut terms, "y");
    let xx = terms.mk_mul(vec![x, x]);
    let body = terms.mk_eq(xx, y);
    assert_eq!(
        eliminate_exists_real(&mut terms, body, x),
        QeResult::NotSupported
    );
}

#[test]
fn refuses_uninterpreted_function() {
    // ∃x. f(x) ≤ 0 — out of fragment.
    let mut terms = TermStore::new();
    let x = rvar(&mut terms, "x");
    let fx = terms.mk_app(Symbol::named("f"), vec![x], Sort::Real);
    let zero = rc(&mut terms, 0, 1);
    let body = terms.mk_le(fx, zero);
    assert_eq!(
        eliminate_exists_real(&mut terms, body, x),
        QeResult::NotSupported
    );
}

#[test]
fn refuses_division_by_variable() {
    // ∃x. (y / x) ≤ 1 — non-constant divisor.
    let mut terms = TermStore::new();
    let x = rvar(&mut terms, "x");
    let y = rvar(&mut terms, "y");
    let div = terms.mk_app(Symbol::named("/"), vec![y, x], Sort::Real);
    let one = rc(&mut terms, 1, 1);
    let body = terms.mk_le(div, one);
    assert_eq!(
        eliminate_exists_real(&mut terms, body, x),
        QeResult::NotSupported
    );
}

// ---------------------------------------------------------------------------
// Division by a constant stays in fragment
// ---------------------------------------------------------------------------

#[test]
fn constant_divisor_supported() {
    // ∃x. (x / 2 = y ∧ x > y) — x = 2y with guard 2y > y, i.e. y > 0.
    let mut terms = TermStore::new();
    let x = rvar(&mut terms, "x");
    let y = rvar(&mut terms, "y");
    let two = rc(&mut terms, 2, 1);
    let half_x = terms.mk_app(Symbol::named("/"), vec![x, two], Sort::Real);
    let e = terms.mk_eq(half_x, y);
    let g = terms.mk_gt(x, y);
    let body = terms.mk_and(vec![e, g]);
    let qf = elim(&mut terms, body, x);
    assert!(eval_at(&terms, qf, &[(y, ratio(1, 2))]));
    assert!(!eval_at(&terms, qf, &[(y, ratio(-1, 2))]));
    assert!(!eval_at(&terms, qf, &[(y, ratio(0, 1))]));
}

// ---------------------------------------------------------------------------
// to_real purification (mixed-sort bridge)
// ---------------------------------------------------------------------------

/// Whether any `__ay_qe_toreal` purification fresh variable leaked into the
/// output (must never happen — new-symbol regression).
fn mentions_purify_fresh(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::Var(name, _) => name.starts_with("__ay_qe_toreal"),
        TermData::Not(inner) => mentions_purify_fresh(terms, *inner),
        TermData::App(_, args) => args.iter().any(|&a| mentions_purify_fresh(terms, a)),
        TermData::Ite(c, t, e) => {
            mentions_purify_fresh(terms, *c)
                || mentions_purify_fresh(terms, *t)
                || mentions_purify_fresh(terms, *e)
        }
        _ => false,
    }
}

#[test]
fn purifies_to_real_bridge_equality_to_true() {
    // ∃r. r = to_real(n) — true for every Int n (the mixed-block core: the
    // purified body is ∃r. r = u, and back-substitution restores to_real(n)
    // into an already-constant-folded output).
    let mut terms = TermStore::new();
    let r = rvar(&mut terms, "r");
    let n = terms.mk_var("n", Sort::Int);
    let body = terms.mk_eq_coerce(r, n); // (= r (to_real n))
    let qf = elim(&mut terms, body, r);
    assert!(
        matches!(
            terms.get(qf),
            TermData::Const(ay_core::term::Constant::Bool(true))
        ),
        "∃r. r = to_real(n) must fold to true, got {:?}",
        terms.get(qf)
    );
}

#[test]
fn purified_contradictory_bridge_folds_to_false() {
    // ∃r. (r = to_real(n) ∧ r < to_real(n)) — false for every n (the
    // opposite-verdict twin of the bridge equality).
    let mut terms = TermStore::new();
    let r = rvar(&mut terms, "r");
    let n = terms.mk_var("n", Sort::Int);
    let tr = terms.mk_to_real(n);
    let eq = terms.mk_eq(r, tr);
    let lt = terms.mk_lt(r, tr);
    let body = terms.mk_and(vec![eq, lt]);
    let qf = elim(&mut terms, body, r);
    assert!(
        matches!(
            terms.get(qf),
            TermData::Const(ay_core::term::Constant::Bool(false))
        ),
        "∃r. (r = to_real n ∧ r < to_real n) must fold to false, got {:?}",
        terms.get(qf)
    );
}

#[test]
fn purified_bounds_back_substitute_without_fresh_leak() {
    // ∃r. (r = to_real(n) ∧ 0 < r ∧ r < 1) — eliminates to a formula over
    // to_real(n); the eliminated var and every purification fresh var must be
    // gone from the output.
    let mut terms = TermStore::new();
    let r = rvar(&mut terms, "r");
    let n = terms.mk_var("n", Sort::Int);
    let tr = terms.mk_to_real(n);
    let zero = rc(&mut terms, 0, 1);
    let one = rc(&mut terms, 1, 1);
    let eq = terms.mk_eq(r, tr);
    let lo = terms.mk_lt(zero, r);
    let hi = terms.mk_lt(r, one);
    let body = terms.mk_and(vec![eq, lo, hi]);
    let qf = elim(&mut terms, body, r);
    assert!(!mentions(&terms, qf, r), "eliminated var must not survive");
    assert!(
        !mentions_purify_fresh(&terms, qf),
        "purification fresh vars must not leak into the output"
    );
}

#[test]
fn refuses_shadowed_to_real() {
    // A user-shadowed (uninterpreted) `to_real` must NOT be purified — that
    // would fabricate builtin semantics for a free function.
    let mut terms = TermStore::new();
    let r = rvar(&mut terms, "r");
    let n = terms.mk_var("n", Sort::Int);
    let tr = terms.mk_to_real(n);
    let body = terms.mk_eq(r, tr);
    terms.mark_to_real_shadowed();
    assert_eq!(
        eliminate_exists_real(&mut terms, body, r),
        QeResult::NotSupported
    );
}

#[test]
fn refuses_to_real_argument_mentioning_eliminated_var() {
    // ∃r. to_real(to_int(r)) = r — the Int argument reaches the eliminated
    // Real var through to_int, so the substitution-instance soundness
    // argument does not apply. Must refuse (review-mandated occurs gate; the
    // qe_prepass screen also refuses to_int, but the pub contract must not
    // depend on caller screening).
    let mut terms = TermStore::new();
    let r = rvar(&mut terms, "r");
    let ti = terms.mk_to_int(r);
    let tr = terms.mk_to_real(ti);
    let body = terms.mk_eq(tr, r);
    assert_eq!(
        eliminate_exists_real(&mut terms, body, r),
        QeResult::NotSupported
    );
}

#[test]
fn purified_multi_to_real_atoms_supported_at_lw_level() {
    // ∃r. (r = to_real(n) ∧ to_real(n) - to_real(m) ≤ 1/2) — multiple bridge
    // nodes purify to distinct fresh vars; the second atom survives into the
    // output as a Real atom over both to_reals (the KNOWN LIMIT for the
    // OUTER Int peel lives in qe_prepass's screen, not here). No fresh leak.
    let mut terms = TermStore::new();
    let r = rvar(&mut terms, "r");
    let n = terms.mk_var("n", Sort::Int);
    let m = terms.mk_var("m", Sort::Int);
    let trn = terms.mk_to_real(n);
    let trm = terms.mk_to_real(m);
    let eq = terms.mk_eq(r, trn);
    let diff = terms.mk_sub(vec![trn, trm]);
    let half = rc(&mut terms, 1, 2);
    let le = terms.mk_le(diff, half);
    let body = terms.mk_and(vec![eq, le]);
    let qf = elim(&mut terms, body, r);
    assert!(!mentions(&terms, qf, r));
    assert!(!mentions_purify_fresh(&terms, qf));
}
