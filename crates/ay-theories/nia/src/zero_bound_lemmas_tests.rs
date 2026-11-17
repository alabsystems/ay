// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the zero-lower-bound product sign / monotonicity lemmas
//! (#nia-zero-bound, see `zero_bound_lemmas.rs`).
//!
//! Both directions are pinned for each lemma family:
//! - **should-prove**: the negation of a valid ordered-ring theorem must be
//!   UNSAT (previously stalled at `unknown` for unbounded variables);
//! - **must-not-prove** (soundness): the negation of an INVALID strengthening
//!   (strict conclusion from weak premises) must never be UNSAT — the `= 0`
//!   witness refutes it.

use super::super::*;

fn is_unsat(r: &TheoryResult) -> bool {
    matches!(r, TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_))
}

/// `x >= 0, y >= 0, x*y < 0` is UNSAT (lemma: nonneg * nonneg >= 0).
/// This is the negation of Verus nonlinear.rs test2 (`lemma_mul_stay_positive`).
#[test]
fn zero_bound_sign_nonneg_product_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let xy = terms.mk_mul(vec![x, y]);
    let zero = terms.mk_int(BigInt::from(0));
    let x_nonneg = terms.mk_ge(x, zero);
    let y_nonneg = terms.mk_ge(y, zero);
    let prod_neg = terms.mk_lt(xy, zero);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(x_nonneg, true);
    solver.assert_literal(y_nonneg, true);
    solver.assert_literal(prod_neg, true);

    let result = solver.check();
    assert!(
        is_unsat(&result),
        "x>=0, y>=0, x*y<0 must be UNSAT via the zero-bound sign lemma, got {result:?}"
    );
}

/// SOUNDNESS: `x >= 0, y >= 0, x*y <= 0` is SAT (witness x = 0). The lemma
/// must be the WEAK bound `x*y >= 0`, never the strict `x*y > 0`.
#[test]
fn zero_bound_sign_weak_conclusion_not_over_strengthened() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let xy = terms.mk_mul(vec![x, y]);
    let zero = terms.mk_int(BigInt::from(0));
    let x_nonneg = terms.mk_ge(x, zero);
    let y_nonneg = terms.mk_ge(y, zero);
    let prod_nonpos = terms.mk_le(xy, zero);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(x_nonneg, true);
    solver.assert_literal(y_nonneg, true);
    solver.assert_literal(prod_nonpos, true);

    let result = solver.check();
    assert!(
        !is_unsat(&result),
        "x>=0, y>=0, x*y<=0 is satisfied by x=0 — an UNSAT here would prove \
         the false theorem x>=0 && y>=0 -> x*y>0; got {result:?}"
    );
}

/// Mixed signs: `x >= 0, y <= 0, x*y > 0` is UNSAT (lemma: x*y <= 0).
#[test]
fn zero_bound_sign_mixed_product_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let xy = terms.mk_mul(vec![x, y]);
    let zero = terms.mk_int(BigInt::from(0));
    let x_nonneg = terms.mk_ge(x, zero);
    let y_nonpos = terms.mk_le(y, zero);
    let prod_pos = terms.mk_gt(xy, zero);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(x_nonneg, true);
    solver.assert_literal(y_nonpos, true);
    solver.assert_literal(prod_pos, true);

    let result = solver.check();
    assert!(
        is_unsat(&result),
        "x>=0, y<=0, x*y>0 must be UNSAT via the zero-bound sign lemma, got {result:?}"
    );
}

/// Both negative: `x <= 0, y <= 0, x*y < 0` is UNSAT (even parity: x*y >= 0).
#[test]
fn zero_bound_sign_nonpos_nonpos_product_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let xy = terms.mk_mul(vec![x, y]);
    let zero = terms.mk_int(BigInt::from(0));
    let x_nonpos = terms.mk_le(x, zero);
    let y_nonpos = terms.mk_le(y, zero);
    let prod_neg = terms.mk_lt(xy, zero);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(x_nonpos, true);
    solver.assert_literal(y_nonpos, true);
    solver.assert_literal(prod_neg, true);

    let result = solver.check();
    assert!(
        is_unsat(&result),
        "x<=0, y<=0, x*y<0 must be UNSAT via the zero-bound sign lemma, got {result:?}"
    );
}

/// Zero factor: `x = 0, x*y > 0` is UNSAT (both bounds: x*y = 0), with y
/// completely unconstrained.
#[test]
fn zero_bound_sign_zero_factor_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let xy = terms.mk_mul(vec![x, y]);
    let zero = terms.mk_int(BigInt::from(0));
    let x_zero = terms.mk_eq(x, zero);
    let prod_pos = terms.mk_gt(xy, zero);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(x_zero, true);
    solver.assert_literal(prod_pos, true);

    let result = solver.check();
    assert!(
        is_unsat(&result),
        "x=0, x*y>0 must be UNSAT via the zero-factor lemma, got {result:?}"
    );
}

/// Ternary: `x >= 0, y >= 0, z <= 0, x*y*z > 0` is UNSAT (odd parity).
#[test]
fn zero_bound_sign_ternary_odd_parity_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let xyz = terms.mk_mul(vec![x, y, z]);
    let zero = terms.mk_int(BigInt::from(0));
    let x_nonneg = terms.mk_ge(x, zero);
    let y_nonneg = terms.mk_ge(y, zero);
    let z_nonpos = terms.mk_le(z, zero);
    let prod_pos = terms.mk_gt(xyz, zero);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(x_nonneg, true);
    solver.assert_literal(y_nonneg, true);
    solver.assert_literal(z_nonpos, true);
    solver.assert_literal(prod_pos, true);

    let result = solver.check();
    assert!(
        is_unsat(&result),
        "x>=0, y>=0, z<=0, x*y*z>0 must be UNSAT via the zero-bound sign lemma, got {result:?}"
    );
}

/// `x <= y, z >= 0, x*z > y*z` is UNSAT (lemma: x*z <= y*z).
/// This is the negation of Verus nonlinear.rs test3
/// (`lemma_inequality_after_mul`).
#[test]
fn zero_bound_monotonicity_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let xz = terms.mk_mul(vec![x, z]);
    let yz = terms.mk_mul(vec![y, z]);
    let zero = terms.mk_int(BigInt::from(0));
    let x_le_y = terms.mk_le(x, y);
    let z_nonneg = terms.mk_ge(z, zero);
    let goal_neg = terms.mk_gt(xz, yz);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(x_le_y, true);
    solver.assert_literal(z_nonneg, true);
    solver.assert_literal(goal_neg, true);

    let result = solver.check();
    assert!(
        is_unsat(&result),
        "x<=y, z>=0, x*z>y*z must be UNSAT via the zero-bound monotonicity lemma, got {result:?}"
    );
}

/// SOUNDNESS: `x <= y, z >= 0, x*z >= y*z` is SAT (witness z = 0). The lemma
/// must be the WEAK `x*z <= y*z`, never the strict `x*z < y*z` — this is
/// exactly Verus nonlinear.rs test1_fails (`wrong_lemma_1`), which must keep
/// failing.
#[test]
fn zero_bound_monotonicity_strict_conclusion_not_over_strengthened() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let xz = terms.mk_mul(vec![x, z]);
    let yz = terms.mk_mul(vec![y, z]);
    let zero = terms.mk_int(BigInt::from(0));
    let x_le_y = terms.mk_le(x, y);
    let z_nonneg = terms.mk_ge(z, zero);
    let goal_neg_weak = terms.mk_ge(xz, yz);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(x_le_y, true);
    solver.assert_literal(z_nonneg, true);
    solver.assert_literal(goal_neg_weak, true);

    let result = solver.check();
    assert!(
        !is_unsat(&result),
        "x<=y, z>=0, x*z>=y*z is satisfied by z=0 — an UNSAT here would prove \
         the false theorem x<=y && z>=0 -> x*z<y*z (test1_fails); got {result:?}"
    );
}

/// Nonpositive multiplier flips the order: `x <= y, z <= 0, x*z < y*z` is
/// UNSAT (lemma: x*z >= y*z).
#[test]
fn zero_bound_monotonicity_nonpos_multiplier_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let xz = terms.mk_mul(vec![x, z]);
    let yz = terms.mk_mul(vec![y, z]);
    let zero = terms.mk_int(BigInt::from(0));
    let x_le_y = terms.mk_le(x, y);
    let z_nonpos = terms.mk_le(z, zero);
    let goal_neg = terms.mk_lt(xz, yz);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(x_le_y, true);
    solver.assert_literal(z_nonpos, true);
    solver.assert_literal(goal_neg, true);

    let result = solver.check();
    assert!(
        is_unsat(&result),
        "x<=y, z<=0, x*z<y*z must be UNSAT via the zero-bound monotonicity lemma, got {result:?}"
    );
}

/// Order asserted through a negated `>` atom: `NOT(x > y), z >= 0, x*z > y*z`
/// is UNSAT (the negated strict order implies the weak order x <= y).
#[test]
fn zero_bound_monotonicity_negated_order_atom_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let xz = terms.mk_mul(vec![x, z]);
    let yz = terms.mk_mul(vec![y, z]);
    let zero = terms.mk_int(BigInt::from(0));
    let x_gt_y = terms.mk_gt(x, y);
    let z_nonneg = terms.mk_ge(z, zero);
    let goal_neg = terms.mk_gt(xz, yz);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(x_gt_y, false);
    solver.assert_literal(z_nonneg, true);
    solver.assert_literal(goal_neg, true);

    let result = solver.check();
    assert!(
        is_unsat(&result),
        "NOT(x>y), z>=0, x*z>y*z must be UNSAT via the zero-bound monotonicity lemma, got {result:?}"
    );
}

/// SOUNDNESS / scoping: a zero-bound cut emitted inside a pushed scope must
/// be retracted on pop — the same product constraint must be SAT again once
/// the sign premises are gone.
#[test]
fn zero_bound_cuts_retracted_on_pop() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let xy = terms.mk_mul(vec![x, y]);
    let zero = terms.mk_int(BigInt::from(0));
    let x_nonneg = terms.mk_ge(x, zero);
    let y_nonneg = terms.mk_ge(y, zero);
    let prod_neg = terms.mk_lt(xy, zero);

    let mut solver = NiaSolver::new(&terms);
    solver.push();
    solver.assert_literal(x_nonneg, true);
    solver.assert_literal(y_nonneg, true);
    solver.assert_literal(prod_neg, true);
    let result = solver.check();
    assert!(
        is_unsat(&result),
        "scoped x>=0, y>=0, x*y<0 must be UNSAT, got {result:?}"
    );

    solver.pop();
    // Without the sign premises, x*y < 0 is satisfiable (e.g. x=1, y=-1).
    solver.assert_literal(prod_neg, true);
    let result = solver.check();
    assert!(
        !is_unsat(&result),
        "after pop, x*y<0 alone must not stay UNSAT (leaked zero-bound cut?), got {result:?}"
    );
}

/// Idempotency: repeated check() calls in one scope must not change the
/// verdict (dedup set prevents stacking duplicate cuts).
#[test]
fn zero_bound_lemmas_idempotent_across_checks() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let xz = terms.mk_mul(vec![x, z]);
    let yz = terms.mk_mul(vec![y, z]);
    let zero = terms.mk_int(BigInt::from(0));
    let x_le_y = terms.mk_le(x, y);
    let z_nonneg = terms.mk_ge(z, zero);
    let goal_neg = terms.mk_gt(xz, yz);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(x_le_y, true);
    solver.assert_literal(z_nonneg, true);
    solver.assert_literal(goal_neg, true);

    let first = solver.check();
    let second = solver.check();
    assert!(is_unsat(&first), "first check must be UNSAT, got {first:?}");
    assert!(
        is_unsat(&second),
        "second check must stay UNSAT, got {second:?}"
    );
}

// ---------------------------------------------------------------------------
// Family 3: ordered-box product comparison (pairwise factor order).
// ---------------------------------------------------------------------------

/// `x <= xb, y <= yb, x >= 0, y >= 0, x*y > xb*yb` is UNSAT
/// (lemma: `x*y <= xb*yb` — Verus nonlinear.rs test1, `lemma_mul_upper_bound`).
#[test]
fn zero_bound_pair_order_product_upper_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let xb = terms.mk_var("xb", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let yb = terms.mk_var("yb", Sort::Int);
    let xy = terms.mk_mul(vec![x, y]);
    let xbyb = terms.mk_mul(vec![xb, yb]);
    let zero = terms.mk_int(BigInt::from(0));
    let x_le = terms.mk_le(x, xb);
    let y_le = terms.mk_le(y, yb);
    let x_nonneg = terms.mk_ge(x, zero);
    let y_nonneg = terms.mk_ge(y, zero);
    let goal_neg = terms.mk_gt(xy, xbyb);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(x_le, true);
    solver.assert_literal(y_le, true);
    solver.assert_literal(x_nonneg, true);
    solver.assert_literal(y_nonneg, true);
    solver.assert_literal(goal_neg, true);

    let result = solver.check();
    assert!(
        is_unsat(&result),
        "x<=xb, y<=yb, x>=0, y>=0, x*y > xb*yb must be UNSAT via the \
         ordered-box pair lemma, got {result:?}"
    );
}

/// SOUNDNESS: without the non-negativity of `y`, the comparison is FALSE.
/// Witness: x = 2, y = -1, xb = 3, yb = -1 satisfies x <= xb, y <= yb,
/// x >= 0, and x*y = -2 > xb*yb = -3 — so dropping `y >= 0` MUST NOT yield
/// UNSAT (the pair lemma requires every left factor asserted non-negative).
#[test]
fn zero_bound_pair_order_requires_nonneg_factors() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let xb = terms.mk_var("xb", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let yb = terms.mk_var("yb", Sort::Int);
    let xy = terms.mk_mul(vec![x, y]);
    let xbyb = terms.mk_mul(vec![xb, yb]);
    let zero = terms.mk_int(BigInt::from(0));
    let x_le = terms.mk_le(x, xb);
    let y_le = terms.mk_le(y, yb);
    let x_nonneg = terms.mk_ge(x, zero);
    let goal_neg = terms.mk_gt(xy, xbyb);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(x_le, true);
    solver.assert_literal(y_le, true);
    solver.assert_literal(x_nonneg, true);
    solver.assert_literal(goal_neg, true);

    let result = solver.check();
    assert!(
        !is_unsat(&result),
        "without y >= 0 the pair comparison is refutable (x=2, y=-1, xb=3, \
         yb=-1) and must not be UNSAT; got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Family 4: non-negative-box product upper bound (justified LRA bounds).
// ---------------------------------------------------------------------------

/// `0 <= x <= 10, 0 <= y <= 20, x*y > 200` is UNSAT (lemma: `x*y <= 200`
/// from the factors' justified constant box — the iteration-0 form of the
/// McCormick upper envelope; Verus nonlinear.rs test5 block shape).
#[test]
fn box_product_upper_constant_box_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let xy = terms.mk_mul(vec![x, y]);
    let zero = terms.mk_int(BigInt::from(0));
    let ten = terms.mk_int(BigInt::from(10));
    let twenty = terms.mk_int(BigInt::from(20));
    let cap = terms.mk_int(BigInt::from(200));
    let x_nonneg = terms.mk_ge(x, zero);
    let y_nonneg = terms.mk_ge(y, zero);
    let x_ub = terms.mk_le(x, ten);
    let y_ub = terms.mk_le(y, twenty);
    let goal_neg = terms.mk_gt(xy, cap);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(x_nonneg, true);
    solver.assert_literal(y_nonneg, true);
    solver.assert_literal(x_ub, true);
    solver.assert_literal(y_ub, true);
    solver.assert_literal(goal_neg, true);

    let result = solver.check();
    assert!(
        is_unsat(&result),
        "0<=x<=10, 0<=y<=20, x*y > 200 must be UNSAT via the box product \
         upper cut, got {result:?}"
    );
}

/// SOUNDNESS: the box cut must be exactly `prod(ub)` — `x*y > 199` is SAT
/// (witness x = 10, y = 20) and must never become UNSAT.
#[test]
fn box_product_upper_exact_corner_not_over_tightened() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let xy = terms.mk_mul(vec![x, y]);
    let zero = terms.mk_int(BigInt::from(0));
    let ten = terms.mk_int(BigInt::from(10));
    let twenty = terms.mk_int(BigInt::from(20));
    let cap = terms.mk_int(BigInt::from(199));
    let x_nonneg = terms.mk_ge(x, zero);
    let y_nonneg = terms.mk_ge(y, zero);
    let x_ub = terms.mk_le(x, ten);
    let y_ub = terms.mk_le(y, twenty);
    let goal_neg = terms.mk_gt(xy, cap);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(x_nonneg, true);
    solver.assert_literal(y_nonneg, true);
    solver.assert_literal(x_ub, true);
    solver.assert_literal(y_ub, true);
    solver.assert_literal(goal_neg, true);

    let result = solver.check();
    assert!(
        !is_unsat(&result),
        "x*y > 199 is satisfied at the (10, 20) corner — an UNSAT would \
         over-tighten the box cut; got {result:?}"
    );
}

/// Zero product: `x >= 2, x*y = 0, y >= 1` is UNSAT — a zero product with
/// a factor bounded away from zero forces the other factor to zero.
#[test]
fn zero_product_forces_other_factor_zero_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let xy = terms.mk_mul(vec![x, y]);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let x_ge2 = terms.mk_ge(x, two);
    let prod_zero = terms.mk_eq(xy, zero);
    let y_ge1 = terms.mk_ge(y, one);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(x_ge2, true);
    solver.assert_literal(prod_zero, true);
    solver.assert_literal(y_ge1, true);

    let result = solver.check();
    assert!(
        is_unsat(&result),
        "x>=2, x*y=0, y>=1 must be UNSAT via the zero-product lemma, got {result:?}"
    );
}

/// Zero product, negative side: `x <= -2, x*y = 0, y <= -1` is UNSAT.
#[test]
fn zero_product_negative_factor_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let xy = terms.mk_mul(vec![x, y]);
    let zero = terms.mk_int(BigInt::from(0));
    let neg_one = terms.mk_int(BigInt::from(-1));
    let neg_two = terms.mk_int(BigInt::from(-2));
    let x_le = terms.mk_le(x, neg_two);
    let prod_zero = terms.mk_eq(xy, zero);
    let y_le = terms.mk_le(y, neg_one);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(x_le, true);
    solver.assert_literal(prod_zero, true);
    solver.assert_literal(y_le, true);

    let result = solver.check();
    assert!(
        is_unsat(&result),
        "x<=-2, x*y=0, y<=-1 must be UNSAT via the zero-product lemma, got {result:?}"
    );
}

/// SOUNDNESS: `x >= 0, x*y = 0, y >= 1` is SAT (witness x = 0) — the lemma
/// must require the factor to be bounded AWAY from zero, not merely signed.
#[test]
fn zero_product_signed_factor_not_over_strengthened() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let xy = terms.mk_mul(vec![x, y]);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let x_nonneg = terms.mk_ge(x, zero);
    let prod_zero = terms.mk_eq(xy, zero);
    let y_ge1 = terms.mk_ge(y, one);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(x_nonneg, true);
    solver.assert_literal(prod_zero, true);
    solver.assert_literal(y_ge1, true);

    let result = solver.check();
    assert!(
        !is_unsat(&result),
        "x>=0, x*y=0, y>=1 is satisfied by x=0 — an UNSAT would prove the \
         false theorem that a signed factor cannot be zero; got {result:?}"
    );
}

/// Chained zero product: `x >= 2, x*y = 0, y = z*z, z >= 1` is UNSAT —
/// the zero-product step forces `y = 0`, contradicting `y = z*z >= 1`.
#[test]
fn zero_product_chained_through_square_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let xy = terms.mk_mul(vec![x, y]);
    let zz = terms.mk_mul(vec![z, z]);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let x_ge2 = terms.mk_ge(x, two);
    let prod_zero = terms.mk_eq(xy, zero);
    let y_eq_zz = terms.mk_eq(y, zz);
    let z_ge1 = terms.mk_ge(z, one);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(x_ge2, true);
    solver.assert_literal(prod_zero, true);
    solver.assert_literal(y_eq_zz, true);
    solver.assert_literal(z_ge1, true);

    let result = solver.check();
    assert!(
        is_unsat(&result),
        "x>=2, x*y=0, y=z*z, z>=1 must be UNSAT via chained zero-product, got {result:?}"
    );
}

/// Nested zero product: `x >= 2, x*(z*z) = 0, z >= 1` is UNSAT — the
/// zero-product step on the binary outer monomial `[x, z*z]` forces the
/// sub-monomial `z*z = 0`, contradicting `z >= 1`.
#[test]
fn zero_product_nested_square_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let zz = terms.mk_mul(vec![z, z]);
    let xzz = terms.mk_mul(vec![x, zz]);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let x_ge2 = terms.mk_ge(x, two);
    let prod_zero = terms.mk_eq(xzz, zero);
    let z_ge1 = terms.mk_ge(z, one);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(x_ge2, true);
    solver.assert_literal(prod_zero, true);
    solver.assert_literal(z_ge1, true);

    let result = solver.check();
    assert!(
        is_unsat(&result),
        "x>=2, x*(z*z)=0, z>=1 must be UNSAT via nested zero-product, got {result:?}"
    );
}

/// Nonzero chain: `ai >= 0`, `ai*a(i+1) >= 1` for each link, finally
/// `a_last * b = 0` with `b >= 1` is UNSAT (bounded enumeration decides
/// it at theory level; the pipeline shape is pinned separately below).
#[test]
fn nonzero_chain_decided_unsat() {
    let n = 60;
    let mut terms = TermStore::new();
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let a: Vec<TermId> = (0..n)
        .map(|i| terms.mk_var(format!("a{i}"), Sort::Int))
        .collect();
    let b = terms.mk_var("b", Sort::Int);

    let mut atoms: Vec<TermId> = a.iter().map(|&ai| terms.mk_ge(ai, zero)).collect();
    for w in a.windows(2) {
        let prod = terms.mk_mul(vec![w[0], w[1]]);
        atoms.push(terms.mk_ge(prod, one));
    }
    let last_prod = terms.mk_mul(vec![a[n - 1], b]);
    atoms.push(terms.mk_eq(last_prod, zero));
    atoms.push(terms.mk_ge(b, one));
    let mut solver = NiaSolver::new(&terms);
    for atom in atoms {
        solver.assert_literal(atom, true);
    }

    let result = solver.check();
    assert!(
        is_unsat(&result),
        "nonzero chain must be UNSAT, got {result:?}"
    );
}

/// SOUNDNESS: the same chain with `b >= 0` is SAT (all ai = 1, b = 0).
#[test]
fn nonzero_chain_sat_twin_not_over_strengthened() {
    let n = 60;
    let mut terms = TermStore::new();
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let a: Vec<TermId> = (0..n)
        .map(|i| terms.mk_var(format!("a{i}"), Sort::Int))
        .collect();
    let b = terms.mk_var("b", Sort::Int);

    let mut atoms: Vec<TermId> = a.iter().map(|&ai| terms.mk_ge(ai, zero)).collect();
    for w in a.windows(2) {
        let prod = terms.mk_mul(vec![w[0], w[1]]);
        atoms.push(terms.mk_ge(prod, one));
    }
    let last_prod = terms.mk_mul(vec![a[n - 1], b]);
    atoms.push(terms.mk_eq(last_prod, zero));
    atoms.push(terms.mk_ge(b, zero));
    let mut solver = NiaSolver::new(&terms);
    for atom in atoms {
        solver.assert_literal(atom, true);
    }

    let result = solver.check();
    assert!(
        !is_unsat(&result),
        "chain with b>=0 is satisfied by ai=1, b=0; got {result:?}"
    );
}

/// Pipeline shape of the nonzero chain: root assertions installed (as the
/// executor does) plus a solve deadline. The SAT-only local-search lane
/// must not burn its shared wall budget ahead of bounded enumeration on
/// an UNSAT instance enumeration decides immediately — the sliced
/// first offer keeps the whole check far below the deadline.
#[test]
fn nonzero_chain_with_roots_decides_before_sls_budget() {
    let n = 60;
    let mut terms = TermStore::new();
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let a: Vec<TermId> = (0..n)
        .map(|i| terms.mk_var(format!("a{i}"), Sort::Int))
        .collect();
    let b = terms.mk_var("b", Sort::Int);
    let mut atoms: Vec<TermId> = a.iter().map(|&ai| terms.mk_ge(ai, zero)).collect();
    for w in a.windows(2) {
        let prod = terms.mk_mul(vec![w[0], w[1]]);
        atoms.push(terms.mk_ge(prod, one));
    }
    let last_prod = terms.mk_mul(vec![a[n - 1], b]);
    atoms.push(terms.mk_eq(last_prod, zero));
    atoms.push(terms.mk_ge(b, one));

    let mut solver = NiaSolver::new(&terms);
    solver.set_root_assertions(atoms.clone());
    let deadline = ay_core::time::Instant::now() + std::time::Duration::from_secs(20);
    solver.set_deadline(deadline);
    solver.set_local_search_deadline(
        ay_core::time::Instant::now() + std::time::Duration::from_secs(12),
    );
    for atom in atoms {
        solver.assert_literal(atom, true);
    }

    let start = ay_core::time::Instant::now();
    let result = solver.check();
    let elapsed = start.elapsed();
    assert!(
        is_unsat(&result),
        "chain with roots installed must be UNSAT, got {result:?}"
    );
    assert!(
        elapsed < std::time::Duration::from_secs(5),
        "check must decide via enumeration without burning the SLS budget, took {elapsed:?}"
    );
}

/// Quotient bounds: `x = 3`-pinned via bounds, `x*y <= 7`, `y >= 3` is
/// UNSAT because the fixed factor propagates `y <= 7/3` through the product.
#[test]
fn fixed_factor_quotient_bound_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let xy = terms.mk_mul(vec![x, y]);
    let three = terms.mk_int(BigInt::from(3));
    let seven = terms.mk_int(BigInt::from(7));
    let x_ge = terms.mk_ge(x, three);
    let x_le = terms.mk_le(x, three);
    let prod_le = terms.mk_le(xy, seven);
    let y_ge = terms.mk_ge(y, three);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(x_ge, true);
    solver.assert_literal(x_le, true);
    solver.assert_literal(prod_le, true);
    solver.assert_literal(y_ge, true);

    let result = solver.check();
    assert!(
        is_unsat(&result),
        "x=3, x*y<=7, y>=3 must be UNSAT via the quotient bound, got {result:?}"
    );
}

/// Family 2 (multiplication monotonicity) probes only pairs that can
/// name a registered monomial: an order side or shared factor that is
/// no monomial's factor makes the `[lo, z]` / `[hi, z]` lookups miss by
/// construction, so probing it re-derives nothing. The derivation runs
/// on every `check()`; on Certora `65782_..._8` the unfiltered
/// orders × signed-terms product was ~97k allocating probes per check
/// against 4 registered monomials (~93% of the zero-bound derivation,
/// itself ~69% of per-check cost).
#[test]
fn mul_monotonicity_probes_only_monomial_factor_pairs() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let xz = terms.mk_mul(vec![x, z]);
    let yz = terms.mk_mul(vec![y, z]);
    let zero = terms.mk_int(BigInt::from(0));
    let x_le_y = terms.mk_le(x, y);
    let z_nonneg = terms.mk_ge(z, zero);
    let xz_atom = terms.mk_ge(xz, zero);
    let yz_atom = terms.mk_ge(yz, zero);

    // Noise: signed terms and orders among variables that factor no
    // monomial. None of these can participate in a family-2 lemma.
    let mut noise_atoms = Vec::new();
    let mut prev: Option<TermId> = None;
    for i in 0..40 {
        let w = terms.mk_var(format!("w{i}"), Sort::Int);
        noise_atoms.push(terms.mk_ge(w, zero));
        if let Some(p) = prev {
            noise_atoms.push(terms.mk_le(p, w));
        }
        noise_atoms.push(terms.mk_le(w, x));
        prev = Some(w);
    }

    let mut solver = NiaSolver::new(&terms);
    for atom in [x_le_y, z_nonneg, xz_atom, yz_atom] {
        solver.assert_literal(atom, true);
    }
    for atom in noise_atoms {
        solver.assert_literal(atom, true);
    }

    let added = solver.add_zero_bound_product_lemmas();
    assert_eq!(
        added, 1,
        "exactly the x*z <= y*z monotonicity cut must be emitted"
    );
    assert!(
        solver.mul_mono_probe_count <= 4,
        "family 2 must probe only pairs over monomial factors, probed {}",
        solver.mul_mono_probe_count
    );
}
