// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #split-walk-sat-fallback: `try_sat_before_split_giveup` is the clausal
//! local search over the ORIGINAL assertions, offered when the split loop's
//! oscillation guard is about to end the search `unknown`. SAT-only: it
//! claims a model only when every root assertion evaluates true under it,
//! and then `extract_model` serves exactly that witness.

use super::*;

/// A satisfiable root with no finite box around it (`x*y = 12`, both factors
/// at least 3 and unbounded above — the models are 3 × 4 and 4 × 3): the lane
/// finds one, claims it, and `extract_model` reports values that satisfy
/// every root.
#[test]
fn split_giveup_lane_claims_only_a_verified_model_of_the_roots() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let xy = terms.mk_mul(vec![x, y]);
    let twelve = terms.mk_int(BigInt::from(12));
    let three = terms.mk_int(BigInt::from(3));
    let product = terms.mk_eq(xy, twelve);
    let x_big = terms.mk_ge(x, three);
    let y_big = terms.mk_ge(y, three);
    let root = terms.mk_and(vec![product, x_big, y_big]);

    let mut solver = NiaSolver::new(&terms);
    solver.set_deadline(ay_core::time::Instant::now() + std::time::Duration::from_secs(10));
    solver.set_root_assertions(vec![root]);
    for atom in [product, x_big, y_big] {
        solver.assert_literal(atom, true);
    }
    assert!(
        solver.try_sat_before_split_giveup(),
        "the lane must find a 3 x 4 witness"
    );
    let model = solver
        .extract_model()
        .expect("a claimed lane serves its model");
    let value = |t: TermId| {
        model
            .values
            .get(&t)
            .cloned()
            .expect("every root leaf is valued")
    };
    let (vx, vy) = (value(x), value(y));
    assert_eq!(&vx * &vy, BigInt::from(12));
    assert!(
        vx >= BigInt::from(3) && vy >= BigInt::from(3),
        "x = {vx}, y = {vy}"
    );
}

/// An unsatisfiable root (`x*x = 2`): the lane never claims.
#[test]
fn split_giveup_lane_never_claims_an_unsatisfiable_root() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let xx = terms.mk_mul(vec![x, x]);
    let two = terms.mk_int(BigInt::from(2));
    let root = terms.mk_eq(xx, two);

    let mut solver = NiaSolver::new(&terms);
    solver.set_deadline(ay_core::time::Instant::now() + std::time::Duration::from_millis(200));
    solver.set_root_assertions(vec![root]);
    solver.assert_literal(root, true);
    assert!(!solver.try_sat_before_split_giveup());
}

/// No root assertions (every non-QF_NIA user of `NiaSolver`): the lane is
/// inert, so the guard's `unknown` stands.
#[test]
fn split_giveup_lane_is_inert_without_roots() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let ge = terms.mk_ge(x, zero);
    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(ge, true);
    assert!(!solver.try_sat_before_split_giveup());
}
