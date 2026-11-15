// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #stale-accept-sat-lane: `try_sat_before_stale_accept` runs the clausal
//! local search only when the model the solver would report PROVABLY
//! falsifies a root assertion, and then claims only an exactly verified
//! witness. Any other model is left exactly as it was — the split loop's
//! `Sat` round goes to the model gate with it unchanged.

use super::*;

fn value_of(model: &NiaModel, t: TermId) -> BigInt {
    model
        .values
        .get(&t)
        .cloned()
        .expect("every root leaf is valued")
}

fn deadline(solver: &mut NiaSolver<'_>) {
    solver.set_deadline(ay_core::time::Instant::now() + std::time::Duration::from_secs(10));
}

/// The reported point `x = y = 0` falsifies the root `x*y = 12 ∧ x >= 3 ∧
/// y >= 3` (only `x >= 0`, `y >= 0` are asserted): the lane runs, claims, and
/// `extract_model` then serves a witness of the root.
#[test]
fn stale_accept_lane_replaces_a_model_that_falsifies_a_root() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let xy = terms.mk_mul(vec![x, y]);
    let zero = terms.mk_int(BigInt::from(0));
    let three = terms.mk_int(BigInt::from(3));
    let twelve = terms.mk_int(BigInt::from(12));
    let product = terms.mk_eq(xy, twelve);
    let x_big = terms.mk_ge(x, three);
    let y_big = terms.mk_ge(y, three);
    let root = terms.mk_and(vec![product, x_big, y_big]);
    let x_nonneg = terms.mk_ge(x, zero);
    let y_nonneg = terms.mk_ge(y, zero);

    let mut solver = NiaSolver::new(&terms);
    deadline(&mut solver);
    solver.set_root_assertions(vec![root]);
    solver.assert_literal(x_nonneg, true);
    solver.assert_literal(y_nonneg, true);
    assert!(
        matches!(solver.check(), TheoryResult::Sat),
        "x, y >= 0 is linear-feasible"
    );
    assert!(
        solver.reported_model_falsifies_a_root(),
        "test premise: the reported point must falsify the root"
    );
    assert!(
        solver.try_sat_before_stale_accept(),
        "the lane must find a 3 x 4 witness"
    );
    let model = solver
        .extract_model()
        .expect("a claimed lane serves its model");
    let (vx, vy) = (value_of(&model, x), value_of(&model, y));
    assert_eq!(&vx * &vy, BigInt::from(12));
    assert!(
        vx >= BigInt::from(3) && vy >= BigInt::from(3),
        "x = {vx}, y = {vy}"
    );
}

/// The reported point satisfies the only root: the lane declines and does
/// not run the local search (it would find a witness of this satisfiable
/// root and claim it), so the reported model is untouched.
#[test]
fn stale_accept_lane_leaves_a_model_that_satisfies_the_roots() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let x_nonneg = terms.mk_ge(x, zero);
    let y_nonneg = terms.mk_ge(y, zero);
    let root = terms.mk_and(vec![x_nonneg, y_nonneg]);

    let mut solver = NiaSolver::new(&terms);
    deadline(&mut solver);
    solver.set_root_assertions(vec![root]);
    solver.assert_literal(x_nonneg, true);
    solver.assert_literal(y_nonneg, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    let before = solver.extract_model().expect("a Sat check reports a model");
    assert!(!solver.reported_model_falsifies_a_root());
    assert!(!solver.try_sat_before_stale_accept());
    let after = solver.extract_model().expect("still a model");
    assert_eq!(
        before.values, after.values,
        "a declined lane must leave the model alone"
    );
    // The local search did not run: the split-walk lane can still use it.
    assert!(solver.try_sat_before_split_giveup());
}

/// A root leaf with no value in the reported model (`y` is never asserted,
/// so the inner LIA never registers it): the evaluator cannot refute the
/// point, so the lane declines — although the root is satisfiable and the
/// local search would claim a witness of it.
#[test]
fn stale_accept_lane_leaves_a_model_it_cannot_evaluate() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let xy = terms.mk_mul(vec![x, y]);
    let zero = terms.mk_int(BigInt::from(0));
    let three = terms.mk_int(BigInt::from(3));
    let twelve = terms.mk_int(BigInt::from(12));
    let product = terms.mk_eq(xy, twelve);
    let x_big = terms.mk_ge(x, three);
    let root = terms.mk_and(vec![product, x_big]);
    let x_nonneg = terms.mk_ge(x, zero);

    let mut solver = NiaSolver::new(&terms);
    deadline(&mut solver);
    solver.set_root_assertions(vec![root]);
    solver.assert_literal(x_nonneg, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    let model = solver.extract_model().expect("a Sat check reports a model");
    assert!(
        !model.values.contains_key(&y),
        "test premise: y must be unvalued in the reported model"
    );
    assert!(!solver.try_sat_before_stale_accept());
    assert!(
        solver.try_sat_before_split_giveup(),
        "the local search is still unused"
    );
}

/// Every Int leaf is valued, but the root holds a Boolean variable the exact
/// evaluator cannot decide (`p ∨ x >= 3` at `x = 0`): the point is not
/// provably wrong, so the lane declines WITHOUT running the local search
/// (which would consume this solver's one search and drop its tentative
/// scope for nothing: it could never verify such a root).
#[test]
fn stale_accept_lane_leaves_a_model_with_an_undecidable_root() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let p = terms.mk_var("p", Sort::Bool);
    let zero = terms.mk_int(BigInt::from(0));
    let three = terms.mk_int(BigInt::from(3));
    let x_big = terms.mk_ge(x, three);
    let root = terms.mk_or(vec![p, x_big]);
    let x_nonneg = terms.mk_ge(x, zero);

    let mut solver = NiaSolver::new(&terms);
    deadline(&mut solver);
    solver.set_root_assertions(vec![root]);
    solver.assert_literal(x_nonneg, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert!(!solver.reported_model_falsifies_a_root());
    assert!(!solver.try_sat_before_stale_accept());
    assert!(
        !solver.local_search_done,
        "a declined lane must not run the local search"
    );
}

/// No root assertions (every non-QF_NIA user of `NiaSolver`): inert.
#[test]
fn stale_accept_lane_is_inert_without_roots() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let ge = terms.mk_ge(x, three);
    let mut solver = NiaSolver::new(&terms);
    deadline(&mut solver);
    solver.assert_literal(ge, true);
    let _ = solver.check();
    assert!(!solver.try_sat_before_stale_accept());
}
