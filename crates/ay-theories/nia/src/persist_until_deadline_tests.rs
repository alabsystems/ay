// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #nia-persist-until-deadline (AY-SMT-5): the top-level QF_NIA search keeps
//! working until its wall deadline instead of ending `unknown` early. These
//! tests pin the two theory-side pieces: the split-drift continuation hook
//! (fix 2; `split_walk_continues_only_under_policy_and_live_deadline` fails
//! when the `continue_split_walk_until_deadline` override is removed) and
//! the geometric box split on a half-bounded monomial factor (fix 3;
//! `half_bounded_factor_gets_a_box_split_only_under_policy` fails when the
//! offer in `monomial_sign_split` is removed). Both are off unless the
//! policy is requested AND a deadline is installed and not yet reached.

use super::*;
use crate::bounded_enum::half_bounded_box_floor;

fn far_deadline() -> ay_core::time::Instant {
    ay_core::time::Instant::now() + std::time::Duration::from_secs(3600)
}

/// The split loop may branch past its drift guard only while the policy is
/// on and a future deadline will end the walk.
#[test]
fn split_walk_continues_only_under_policy_and_live_deadline() {
    let terms = TermStore::new();

    let solver = NiaSolver::new(&terms);
    assert!(
        !solver.continue_split_walk_until_deadline(),
        "default: the drift guard keeps ending the walk"
    );

    let mut solver = NiaSolver::new(&terms);
    solver.set_persist_until_deadline(true);
    assert!(
        !solver.continue_split_walk_until_deadline(),
        "no deadline: nothing else would end an unbounded walk"
    );

    let mut solver = NiaSolver::new(&terms);
    solver.set_deadline(far_deadline());
    assert!(
        !solver.continue_split_walk_until_deadline(),
        "deadline without the policy: sub-solves keep the guard"
    );

    let mut solver = NiaSolver::new(&terms);
    solver.set_persist_until_deadline(true);
    solver.set_deadline(far_deadline());
    assert!(
        solver.continue_split_walk_until_deadline(),
        "policy and a live deadline: keep branching"
    );

    let mut solver = NiaSolver::new(&terms);
    solver.set_persist_until_deadline(true);
    solver.set_deadline(ay_core::time::Instant::now());
    assert!(
        !solver.continue_split_walk_until_deadline(),
        "a passed deadline ends the walk"
    );
}

/// The box arithmetic: `[5, +inf)` splits at `5 + 5 = 10` (box `[5, 10]`),
/// `[0, +inf)` at `0 + 1 = 1`, and the mirrored `(-inf, -3]` at
/// `-3 - 3 - 1 = -7` (`v <= -7 OR v >= -6`, box `[-6, -3]`). Two-sided and
/// unbounded factors get none.
#[test]
fn box_split_width_follows_the_open_bound() {
    let b = |v: i64| BigInt::from(v);
    assert_eq!(half_bounded_box_floor(Some(&b(5)), None), Some(b(10)));
    assert_eq!(half_bounded_box_floor(Some(&b(0)), None), Some(b(1)));
    assert_eq!(half_bounded_box_floor(Some(&b(-4)), None), Some(b(0)));
    assert_eq!(half_bounded_box_floor(None, Some(&b(-3))), Some(b(-7)));
    assert_eq!(half_bounded_box_floor(None, Some(&b(0))), Some(b(-2)));
    assert_eq!(half_bounded_box_floor(Some(&b(0)), Some(&b(9))), None);
    assert_eq!(half_bounded_box_floor(None, None), None);
}

/// Effective integer box of `v` from its CURRENT direct LRA bounds, rounded
/// the way `monomial_sign_split` rounds them.
fn int_box(solver: &NiaSolver<'_>, v: TermId) -> (Option<BigInt>, Option<BigInt>) {
    let Some((lb, ub)) = solver.lia.lra_solver().get_bounds_ref(v) else {
        return (None, None);
    };
    let lo = lb.map(|b| {
        let value = b.value_big();
        let floor = value.floor().to_integer();
        if value.is_integer() && !b.strict {
            floor
        } else {
            floor + 1
        }
    });
    let hi = ub.map(|b| {
        let value = b.value_big();
        let floor = value.floor().to_integer();
        if b.strict && value.is_integer() {
            floor - 1
        } else {
            floor
        }
    });
    (lo, hi)
}

/// Every split `monomial_sign_split` offers on this solver, plus the one a
/// stall inside `check` may already have taken when it is a box split.
fn collect_offers(
    solver: &mut NiaSolver<'_>,
    checked: TheoryResult,
    expected: &[(TermId, BigInt)],
) -> Vec<(TermId, BigInt)> {
    let mut offered = Vec::new();
    if let TheoryResult::NeedSplit(split) = checked {
        if expected.contains(&(split.variable, split.floor.clone())) {
            offered.push((split.variable, split.floor));
        }
    }
    while let Some(split) = solver.monomial_sign_split() {
        assert!(!split.value.is_integer(), "split value must be fractional");
        offered.push((split.variable, split.floor));
        assert!(offered.len() <= 16, "offers must be finite: {offered:?}");
    }
    offered
}

/// `x*y = 7` with `x >= 0` and `y >= 0`: both factors are sign-determined
/// and bounded on one side only. The box offers expected are computed from
/// the bounds the solver actually holds after `check`, so the test does not
/// depend on how far `check` tightened them. Without the policy none of
/// them is offered; with it, every one is.
#[test]
fn half_bounded_factor_gets_a_box_split_only_under_policy() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let xy = terms.mk_mul(vec![x, y]);
    let seven = terms.mk_int(BigInt::from(7));
    let zero = terms.mk_int(BigInt::from(0));
    let eq = terms.mk_eq(xy, seven);
    let x_ge_0 = terms.mk_ge(x, zero);
    let y_ge_0 = terms.mk_ge(y, zero);

    let expected_for = |solver: &NiaSolver<'_>| -> Vec<(TermId, BigInt)> {
        [x, y]
            .into_iter()
            .filter_map(|v| {
                let (lo, hi) = int_box(solver, v);
                half_bounded_box_floor(lo.as_ref(), hi.as_ref()).map(|f| (v, f))
            })
            .collect()
    };

    let mut solver = NiaSolver::new(&terms);
    for atom in [eq, x_ge_0, y_ge_0] {
        solver.assert_literal(atom, true);
    }
    let checked = solver.check();
    let expected = expected_for(&solver);
    let offered = collect_offers(&mut solver, checked, &expected);
    for offer in &expected {
        assert!(
            !offered.contains(offer),
            "without the policy no box split: {offered:?}"
        );
    }

    let mut solver = NiaSolver::new(&terms);
    solver.set_persist_until_deadline(true);
    solver.set_deadline(far_deadline());
    for atom in [eq, x_ge_0, y_ge_0] {
        solver.assert_literal(atom, true);
    }
    let checked = solver.check();
    let expected = expected_for(&solver);
    assert!(
        !expected.is_empty(),
        "the setup must leave a factor bounded on one side only"
    );
    let offered = collect_offers(&mut solver, checked, &expected);
    for offer in &expected {
        assert!(offered.contains(offer), "missing {offer:?} in {offered:?}");
    }
}
