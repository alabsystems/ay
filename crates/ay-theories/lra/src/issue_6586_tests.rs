// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// test_eager_relative_slack_queues_refinement_without_simplex_issue_6586:
// Removed in #6617 — the inline per-variable eager refinement path was deleted.
// Relative slack refinements are now handled by the post-simplex batch path
// (compute_implied_bounds + queue_post_simplex_refinements).

use super::*;
use ay_core::term::TermStore;
use ay_core::Sort;

#[test]
fn test_eager_additive_slack_stays_disabled_without_simplex_issue_6586() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let two = terms.mk_rational(BigRational::from(BigInt::from(2)));
    let sum = terms.mk_add(vec![x, y]);
    let x_le_1 = terms.mk_le(x, one);
    let y_le_2 = terms.mk_le(y, two);
    let sum_le_10 = terms.mk_le(sum, ten);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_le_1);
    solver.register_atom(y_le_2);
    solver.register_atom(sum_le_10);
    let x_var = solver.ensure_var_registered(x);
    let y_var = solver.ensure_var_registered(y);

    solver.assert_var_bound(
        x_var,
        Rational::one(),
        BoundType::Upper,
        false,
        x_le_1,
        true,
        Rational::one(),
    );
    assert!(
        solver.take_bound_refinements().is_empty(),
        "one additive endpoint bound alone must not queue a refinement"
    );

    solver.assert_var_bound(
        y_var,
        Rational::new(2, 1),
        BoundType::Upper,
        false,
        y_le_2,
        true,
        Rational::one(),
    );

    assert!(
        solver.take_bound_refinements().is_empty(),
        "additive slack targets must stay disabled before simplex"
    );
}
