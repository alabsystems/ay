// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The compound wake decides an unasserted `x + y <= 3` from the interval of
//! `x + y` when neither the shared slack's direct bounds nor its row-derived
//! bounds do. The interval is computed once per candidate and serves both the
//! TRUE and the FALSE probe; these tests pin each probe's verdict and the
//! deferred-reason kind it queues.

use super::*;

/// `x + y <= 3` with `x`, `y` bounded on `side` by `value` through reason
/// atoms; returns the solver after one compound wake over the dirty sources.
fn wake_after_source_bounds(side: BoundType, value: i64) -> (LraSolver, TermId) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let rx = terms.mk_var("rx", Sort::Bool);
    let ry = terms.mk_var("ry", Sort::Bool);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_3);
    solver.propagation_dirty_vars.clear();
    solver.pending_propagations.clear();

    let x_expr = solver.parse_linear_expr(x);
    let y_expr = solver.parse_linear_expr(y);
    let v = Rational::new(value, 1);
    solver.assert_bound_with_reasons(x_expr, v.clone(), side, false, &[(rx, true)], None);
    solver.assert_bound_with_reasons(y_expr, v, side, false, &[(ry, true)], None);

    let dirty: Vec<u32> = solver.propagation_dirty_vars.iter().copied().collect();
    solver.queue_compound_propagations_for_dirty_vars(&dirty);
    (solver, sum_le_3)
}

fn queued_interval(solver: &LraSolver, atom: TermId, value: bool) -> bool {
    solver.pending_propagations.iter().any(|pending| {
        pending.propagation.literal == TheoryLit::new(atom, value)
            && matches!(pending.deferred, Some(DeferredReason::Interval { atom_term, .. }) if atom_term == atom)
    })
}

/// `x >= 2`, `y >= 2`: the TRUE probe finds nothing, and the FALSE probe —
/// reusing the interval the TRUE probe computed — refutes `x + y <= 3`.
#[test]
fn compound_wake_refutes_the_atom_from_the_interval_lower_end() {
    let (solver, atom) = wake_after_source_bounds(BoundType::Lower, 2);
    assert!(
        queued_interval(&solver, atom, false),
        "x >= 2, y >= 2 must queue NOT(x + y <= 3) with an interval reason, got {:?}",
        solver.pending_propagations
    );
    assert!(!queued_interval(&solver, atom, true));
    assert_eq!(solver.last_compound_propagations_queued, 1);
}

/// `x <= 1`, `y <= 1`: the TRUE probe proves `x + y <= 3` from the
/// interval's upper end and the wake stops there.
#[test]
fn compound_wake_proves_the_atom_from_the_interval_upper_end() {
    let (solver, atom) = wake_after_source_bounds(BoundType::Upper, 1);
    assert!(
        queued_interval(&solver, atom, true),
        "x <= 1, y <= 1 must queue (x + y <= 3) with an interval reason, got {:?}",
        solver.pending_propagations
    );
    assert!(!queued_interval(&solver, atom, false));
    assert_eq!(solver.last_compound_propagations_queued, 1);
}

/// `x >= 1`, `y >= 1`: the interval `[2, +inf)` decides neither polarity.
#[test]
fn compound_wake_queues_nothing_from_an_undecided_interval() {
    let (solver, atom) = wake_after_source_bounds(BoundType::Lower, 1);
    assert!(!queued_interval(&solver, atom, true));
    assert!(!queued_interval(&solver, atom, false));
    assert_eq!(solver.last_compound_propagations_queued, 0);
}
