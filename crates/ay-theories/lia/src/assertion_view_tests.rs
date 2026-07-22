// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::Sort;
use num_traits::One;

#[test]
fn test_assertion_view_classifies_equalities_and_inequalities() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let one = terms.mk_int(BigInt::one());
    let eq = terms.mk_eq(x, one);
    let ge = terms.mk_ge(y, one);

    // (= x 1) true, (>= y 1) true
    let asserted = vec![(eq, true), (ge, true)];
    let view = AssertionView::build(&terms, &asserted);

    assert_eq!(view.positive_equalities.len(), 1);
    assert_eq!(view.negative_equalities.len(), 0);
    assert_eq!(view.inequalities.len(), 1);
    assert_eq!(view.equality_key.len(), 1);
    // y should have a lower bound of 1
    let y_bounds = view.bounds_by_term.get(&y).expect("y should have bounds");
    assert_eq!(y_bounds.lower, Some(BigInt::one()));
}

#[test]
fn test_assertion_view_negative_equality_is_disequality() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::ZERO);
    let eq = terms.mk_eq(x, zero);

    let asserted = vec![(eq, false)];
    let view = AssertionView::build(&terms, &asserted);

    assert_eq!(view.positive_equalities.len(), 0);
    assert_eq!(view.negative_equalities.len(), 1);
    assert_eq!(view.equality_key.len(), 0);
}

// ---------- Incremental cache equivalence (#C1) ----------

/// Assert that the incrementally maintained view is identical to a
/// from-scratch build over the same asserted trail.
fn assert_view_matches_build(
    cache: &AssertionViewCache,
    terms: &TermStore,
    asserted: &[(TermId, bool)],
) {
    let expected = AssertionView::build(terms, asserted);
    let actual = cache.view();
    assert_eq!(actual.positive_equalities, expected.positive_equalities);
    assert_eq!(actual.negative_equalities, expected.negative_equalities);
    assert_eq!(actual.inequalities, expected.inequalities);
    assert_eq!(actual.equality_key, expected.equality_key);
    assert_eq!(
        actual.bounds_by_term.len(),
        expected.bounds_by_term.len(),
        "bounds_by_term key count mismatch"
    );
    for (term, expected_bounds) in &expected.bounds_by_term {
        let actual_bounds = actual
            .bounds_by_term
            .get(term)
            .unwrap_or_else(|| panic!("missing bounds for term {}", term.0));
        assert_eq!(actual_bounds.lower, expected_bounds.lower);
        assert_eq!(actual_bounds.upper, expected_bounds.upper);
        assert_eq!(actual_bounds.reason_lits, expected_bounds.reason_lits);
    }
}

/// Mixed atoms covering every classification arm plus push/pop with
/// bound-tightening undo and duplicate-equality refcounts.
#[test]
fn test_incremental_view_matches_build_under_assert_push_pop() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let one = terms.mk_int(BigInt::one());
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));

    let eq_x1 = terms.mk_eq(x, one);
    let eq_yz = terms.mk_eq(y, z);
    let ge_y1 = terms.mk_ge(y, one);
    let le_y10 = terms.mk_le(y, ten);
    let le_y5 = terms.mk_le(y, five);
    let gt_z1 = terms.mk_gt(z, one);
    let lt_z10 = terms.mk_lt(z, ten);

    let mut cache = AssertionViewCache::default();
    let mut trail: Vec<(TermId, bool)> = Vec::new();
    let mut scope_stack: Vec<usize> = Vec::new();

    let do_assert = |cache: &mut AssertionViewCache,
                     trail: &mut Vec<(TermId, bool)>,
                     term: TermId,
                     value: bool| {
        trail.push((term, value));
        cache.on_assert(&terms, term, value);
    };

    // Scope 0: a positive equality, a disequality, two bounds on y.
    do_assert(&mut cache, &mut trail, eq_x1, true);
    do_assert(&mut cache, &mut trail, eq_yz, false);
    do_assert(&mut cache, &mut trail, ge_y1, true);
    do_assert(&mut cache, &mut trail, le_y10, true);
    assert_view_matches_build(&cache, &terms, &trail);

    // Scope 1: tighten y's upper bound (undo trail must restore le_y10
    // bound AND reason set on pop), assert eq_x1 AGAIN (duplicate —
    // refcounted so the key survives the pop), strict bounds on z.
    scope_stack.push(trail.len());
    cache.on_push();
    do_assert(&mut cache, &mut trail, le_y5, true);
    do_assert(&mut cache, &mut trail, eq_x1, true);
    do_assert(&mut cache, &mut trail, gt_z1, true);
    assert_view_matches_build(&cache, &terms, &trail);

    // Scope 2: another equality + negative inequality polarity.
    scope_stack.push(trail.len());
    cache.on_push();
    do_assert(&mut cache, &mut trail, eq_yz, true);
    do_assert(&mut cache, &mut trail, lt_z10, false);
    assert_view_matches_build(&cache, &terms, &trail);

    // Pop scope 2: eq_yz leaves the key, lt_z10 polarity removed.
    trail.truncate(scope_stack.pop().unwrap());
    cache.on_pop();
    assert_view_matches_build(&cache, &terms, &trail);
    assert!(cache.view().equality_key.contains(&eq_x1));
    assert!(!cache.view().equality_key.contains(&eq_yz));

    // Pop scope 1: y's bounds revert to [1, 10]; eq_x1 must REMAIN in the
    // key (still asserted at scope 0 — duplicate refcount).
    trail.truncate(scope_stack.pop().unwrap());
    cache.on_pop();
    assert_view_matches_build(&cache, &terms, &trail);
    assert_eq!(cache.view().equality_key, vec![eq_x1]);
    let y_bounds = cache.view().bounds_by_term.get(&y).expect("y bounds");
    assert_eq!(y_bounds.upper, Some(BigInt::from(10)));
}

/// `rebuild` mid-scope must keep prior undo entries valid: rebuilding from
/// the same trail produces identical content, so a later pop still restores
/// the exact outer-scope state.
#[test]
fn test_incremental_view_rebuild_mid_scope_then_pop() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::one());
    let five = terms.mk_int(BigInt::from(5));
    let eq_x5 = terms.mk_eq(x, five);
    let ge_x1 = terms.mk_ge(x, one);
    let le_x5 = terms.mk_le(x, five);

    let mut cache = AssertionViewCache::default();
    let mut trail: Vec<(TermId, bool)> = Vec::new();

    trail.push((ge_x1, true));
    cache.on_assert(&terms, ge_x1, true);

    let mark = trail.len();
    cache.on_push();
    trail.push((le_x5, true));
    cache.on_assert(&terms, le_x5, true);
    trail.push((eq_x5, true));
    cache.on_assert(&terms, eq_x5, true);

    // Defensive rebuild (shared-equality path) in the middle of a scope.
    cache.rebuild(&terms, &trail);
    assert_view_matches_build(&cache, &terms, &trail);

    // Pop must still restore the exact outer state.
    trail.truncate(mark);
    cache.on_pop();
    assert_view_matches_build(&cache, &terms, &trail);
    assert!(cache.view().equality_key.is_empty());
    let x_bounds = cache.view().bounds_by_term.get(&x).expect("x bounds");
    assert_eq!(x_bounds.lower, Some(BigInt::one()));
    assert_eq!(x_bounds.upper, None);
    assert_eq!(x_bounds.reason_lits, vec![TheoryLit::new(ge_x1, true)]);
}
