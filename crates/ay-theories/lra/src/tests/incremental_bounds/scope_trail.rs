// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #lra-scope-trail: an atom's bounds belong to the scope of its ASSERTION,
//! not to the scope of the first `check` that happens to apply them.
//!
//! `assert_literal` only records an atom (`asserted` / `asserted_trail`);
//! the bound writes happen lazily in `process_check_atoms` during the next
//! `check`/`check_during_propagate`, and every bound-trail entry lands in
//! whatever scope is current at that check. A consumer that asserts at
//! scope k, pushes, and checks at scope k+n therefore had the bound trailed
//! at k+n; the first `pop` back below k+n restored it while the atom stayed
//! in `asserted` and `bound_atoms`, so it was never re-applied: the solver
//! answered `Sat` with models violating a still-asserted atom (found by the
//! HornSmt session bridge, WP-2 finding 1, 2026-09-19).
//!
//! Contract locked here (see `TheorySolver::push` in `ay-core/src/theory.rs`):
//! after `push(); <mutations>; pop();` the solver behaves as if the
//! mutations never happened — whatever the check cadence was.

use super::*;

fn lra_with_x() -> (TermStore, TermId, TermId, TermId, TermId, TermId) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_lt_0 = terms.mk_lt(x, zero);
    let x_le_m1 = {
        let m1 = terms.mk_rational(BigRational::from(BigInt::from(-1)));
        terms.mk_le(x, m1)
    };
    (terms, x, x_ge_0, x_lt_0, x_le_m1, one)
}

fn is_unsat(result: &TheoryResult) -> bool {
    matches!(
        result,
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
    )
}

/// Assert at scope 0, push twice, check at scope 2, pop to scope 1: the
/// scope-0 bound must still be enforced by the next check and visible in
/// `get_bounds`.
#[test]
fn bound_asserted_at_scope_zero_survives_pop_of_the_scope_that_applied_it() {
    let (terms, x, x_ge_0, x_lt_0, _x_le_m1, _one) = lra_with_x();
    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_ge_0);
    solver.register_atom(x_lt_0);

    solver.assert_literal(x_ge_0, true); // scope 0
    solver.push(); // scope 1
    solver.push(); // scope 2
    assert!(
        matches!(solver.check(), TheoryResult::Sat),
        "x >= 0 alone is satisfiable"
    );
    solver.pop(); // back to scope 1 — must not touch the scope-0 bound

    let (lo, hi) = solver.get_bounds(x).expect("x is an LRA variable");
    assert!(
        lo.is_some(),
        "x's scope-0 lower bound must survive a pop of scope 2 (got lower={lo:?} upper={hi:?})"
    );

    solver.assert_literal(x_lt_0, true); // scope 1: contradicts the scope-0 atom
    let result = solver.check();
    assert!(
        is_unsat(&result),
        "x >= 0 (scope 0) with x < 0 (scope 1) must be Unsat after popping scope 2, got {result:?}"
    );
}

/// Same shape, but the pop lands exactly on the assertion scope (assert at
/// scope 1, check at scope 3, pop to scope 1), and the follow-up check has
/// no new atom: the model must still respect the scope-1 bound.
#[test]
fn bound_asserted_at_scope_one_is_kept_by_pops_down_to_scope_one() {
    let (terms, x, x_ge_0, _x_lt_0, x_le_m1, _one) = lra_with_x();
    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_ge_0);
    solver.register_atom(x_le_m1);

    solver.push(); // scope 1
    solver.assert_literal(x_ge_0, true);
    solver.push(); // scope 2
    solver.push(); // scope 3
    assert!(matches!(solver.check(), TheoryResult::Sat));
    solver.pop(); // scope 2
    solver.pop(); // scope 1

    let (lo, _hi) = solver.get_bounds(x).expect("x is an LRA variable");
    assert!(
        lo.is_some(),
        "x >= 0 was asserted at scope 1 and scope 1 is live"
    );
    assert!(matches!(solver.check(), TheoryResult::Sat));
    let value = solver.get_value(x).expect("x has a model value");
    assert!(
        value >= BigRational::zero(),
        "model must respect x >= 0, got x = {value}"
    );

    solver.assert_literal(x_le_m1, true); // scope 1
    let result = solver.check();
    assert!(
        is_unsat(&result),
        "x >= 0 with x <= -1 must be Unsat, got {result:?}"
    );

    // And once scope 1 itself is popped, the bound is gone.
    solver.pop();
    let (lo, hi) = solver.get_bounds(x).expect("x is an LRA variable");
    assert!(
        lo.is_none() && hi.is_none(),
        "scope-1 bounds must be undone by popping scope 1"
    );
}

/// The HornSmt bridge shape (WP-2 finding 1): one atom per scope, a single
/// check at the top, a pop of the top scope only. `x ∈ [0,0]` from scopes 1
/// and 2 must survive popping scope 5, and the split atom `x < y` asserted
/// afterwards must give `x = 0`, never `x = -1/2`.
#[test]
fn per_scope_assumption_prefix_survives_a_pop_of_the_top_scope() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let c0 = terms.mk_rational(BigRational::zero());
    let c1 = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let x_lo = terms.mk_ge(x, c0);
    let x_hi = terms.mk_le(x, c0);
    let y_lo = terms.mk_ge(y, c0);
    let y_hi = terms.mk_le(y, c1);
    let eq = terms.mk_eq(x, y);
    let lt = terms.mk_lt(x, y);

    let mut solver = LraSolver::new(&terms);
    for a in [x_lo, x_hi, y_lo, y_hi, eq, lt] {
        solver.register_atom(a);
    }
    solver.push();
    solver.assert_literal(x_lo, true);
    solver.push();
    solver.assert_literal(x_hi, true);
    solver.push();
    solver.assert_literal(y_lo, true);
    solver.push();
    solver.assert_literal(y_hi, true);
    solver.push();
    solver.assert_literal(eq, false);
    let first = solver.check();
    assert!(
        matches!(
            first,
            TheoryResult::NeedExpressionSplit(_) | TheoryResult::NeedExpressionSplits(_)
        ),
        "x = y with x ∈ [0,0], y ∈ [0,1] asks for the split, got {first:?}"
    );
    // Pop the disequality's scope only.
    solver.pop();
    let (lo, hi) = solver.get_bounds(x).expect("x is an LRA variable");
    assert!(
        lo.is_some() && hi.is_some(),
        "x's scope-1/2 bounds survive a pop of scope 5 (got lower={lo:?} upper={hi:?})"
    );
    // Then assert the split atom at scope 4.
    solver.assert_literal(lt, true);
    let verdict = solver.check();
    assert!(matches!(verdict, TheoryResult::Sat), "{verdict:?}");
    let xv = solver.get_value(x).expect("x");
    let yv = solver.get_value(y).expect("y");
    assert_eq!(
        xv,
        BigRational::zero(),
        "x is fixed at 0 by never-popped bounds (got x={xv}, y={yv})"
    );
    assert!(
        yv > BigRational::zero() && yv <= BigRational::from(BigInt::from(1)),
        "y = {yv}"
    );
}

/// A constant-expression atom (`x - x >= 1`, i.e. `0 >= 1`) is recorded as
/// a trivial conflict when its bound is applied. Applying it in the scope of
/// its assertion must not let a pop of a DEEPER scope clear the conflict
/// while the atom is still asserted.
#[test]
fn trivial_conflict_of_a_lower_scope_atom_survives_a_pop_of_a_deeper_scope() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    // `x + y >= (y + x) + 1`: both sides cancel to the constant comparison
    // `0 >= 1` only inside the LRA parser (the term store keeps the atom as
    // an application, so this is the `trivial_conflict` path, not the
    // constant-Bool path of `constant_bool_contradiction_..._is_still_reported`).
    let lhs = terms.mk_add(vec![x, y]);
    let rhs_sum = terms.mk_add(vec![y, x]);
    let rhs = terms.mk_add(vec![rhs_sum, one]);
    let ge_one = terms.mk_ge(lhs, rhs);
    assert!(
        !matches!(terms.get(ge_one), TermData::Const(_)),
        "the term store must not fold the atom to a constant for this test to mean anything"
    );
    let le_one = terms.mk_le(x, one);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(ge_one);
    solver.register_atom(le_one);

    solver.push(); // scope 1
    solver.assert_literal(ge_one, true);
    solver.push(); // scope 2 — no check in between
    solver.assert_literal(le_one, true);
    solver.pop(); // scope 1: `0 >= 1` is still asserted
    let result = solver.check();
    assert!(
        is_unsat(&result),
        "0 >= 1 asserted at scope 1 must still refute after popping scope 2, got {result:?}"
    );
    solver.pop();
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

/// `true` asserted false is an immediate contradiction that `check` reports
/// before touching the tableau; a push between the assertion and the check
/// must not hide it.
#[test]
fn constant_bool_contradiction_asserted_below_a_push_is_still_reported() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let x_le_1 = terms.mk_le(x, one);
    let tt = terms.mk_bool(true);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_le_1);
    solver.register_atom(tt);

    solver.push(); // scope 1
    solver.assert_literal(tt, false);
    solver.push(); // scope 2
    solver.assert_literal(x_le_1, true);
    assert!(
        is_unsat(&solver.check()),
        "true = false must refute at scope 2"
    );
    solver.pop(); // scope 1: `true = false` still asserted
    assert!(
        is_unsat(&solver.check()),
        "true = false must still refute at scope 1"
    );
    solver.pop();
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

/// Multiple pending atoms across several pushes, mixed with an atom that is
/// applied in the scope of its own check: every bound is undone exactly when
/// the scope of ITS assertion is popped.
#[test]
fn pending_atoms_of_several_scopes_are_undone_scope_by_scope() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let c1 = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let c2 = terms.mk_rational(BigRational::from(BigInt::from(2)));
    let c3 = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let x_ge_1 = terms.mk_ge(x, c1);
    let x_ge_2 = terms.mk_ge(x, c2);
    let x_ge_3 = terms.mk_ge(x, c3);

    let mut solver = LraSolver::new(&terms);
    for a in [x_ge_1, x_ge_2, x_ge_3] {
        solver.register_atom(a);
    }
    let lower_of = |solver: &LraSolver| -> Option<BigRational> {
        solver
            .get_bounds(x)
            .and_then(|(lo, _)| lo)
            .map(|b| b.value.to_big())
    };

    solver.push(); // 1
    solver.assert_literal(x_ge_1, true);
    solver.push(); // 2
    solver.assert_literal(x_ge_2, true);
    solver.push(); // 3
    solver.assert_literal(x_ge_3, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert_eq!(lower_of(&solver), Some(BigRational::from(BigInt::from(3))));

    solver.pop(); // 2
    assert_eq!(
        lower_of(&solver),
        Some(BigRational::from(BigInt::from(2))),
        "popping scope 3 leaves the scope-2 bound"
    );
    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert!(solver.get_value(x).expect("x") >= BigRational::from(BigInt::from(2)));

    solver.pop(); // 1
    assert_eq!(
        lower_of(&solver),
        Some(BigRational::from(BigInt::from(1))),
        "popping scope 2 leaves the scope-1 bound"
    );

    solver.pop(); // 0
    assert_eq!(
        lower_of(&solver),
        None,
        "popping scope 1 removes the last bound"
    );
    assert!(matches!(solver.check(), TheoryResult::Sat));
}
