// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for certificate-based theory-lemma leaf interpolation.

use super::*;
use ay_core::TermStore;

/// Equality-implication conflict with the disequality on the B side:
///   A-side rows: a = x, a = 5     (a is A-local, x shared)
///   B-side: b = x, NOT (b = 5)    (b is B-local)
/// Expected partial interpolant (A projection onto {x}): `x = 5`.
#[test]
fn test_cert_leaf_equality_shape_diseq_on_b() {
    let mut terms = TermStore::new();
    let true_tid = terms.mk_bool(true);
    let false_tid = terms.mk_bool(false);
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(5.into());

    let a_eq_x = terms.mk_eq(a, x);
    let a_eq_5 = terms.mk_eq(a, five);
    let b_eq_x = terms.mk_eq(b, x);
    let b_eq_5 = terms.mk_eq(b, five);

    // Clause = negated conflict: [!(a=x), !(a=5), !(b=x), (b=5)].
    let n1 = terms.mk_not(a_eq_x);
    let n2 = terms.mk_not(a_eq_5);
    let n3 = terms.mk_not(b_eq_x);
    let clause = vec![n1, n2, n3, b_eq_5];
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1, 1]);

    let a_atoms: HashSet<TermId> = [a_eq_x, a_eq_5].into_iter().collect();
    let b_atoms: HashSet<TermId> = [b_eq_x, b_eq_5].into_iter().collect();
    let a_vars: HashSet<TermId> = [a, x].into_iter().collect();
    let b_vars: HashSet<TermId> = [b, x].into_iter().collect();
    let shared_vars: HashSet<TermId> = [x].into_iter().collect();
    let part = CertPartition {
        a_atoms: &a_atoms,
        b_atoms: &b_atoms,
        a_vars: &a_vars,
        b_vars: &b_vars,
        shared_vars: &shared_vars,
    };

    reset_cert_leaf_stats();
    let itp = certificate_lemma_interpolant(
        &mut terms,
        &clause,
        &farkas,
        &part,
        InterpolantStrength::Strongest,
        true_tid,
        false_tid,
    )
    .expect("equality-shape certificate leaf must interpolate");

    let expected = terms.mk_eq(x, five);
    assert_eq!(itp, expected, "A projection onto shared {x} must be x = 5");
    let stats = last_cert_leaf_stats();
    assert_eq!(stats.attempted, 1);
    assert_eq!(stats.verified, 1);
    assert_eq!(stats.served, 1);
}

/// Pure inequality conflict: A: x <= 5, B: x >= 6. The A-part weighted sum
/// is `x <= 5`.
#[test]
fn test_cert_leaf_inequality_shape() {
    let mut terms = TermStore::new();
    let true_tid = terms.mk_bool(true);
    let false_tid = terms.mk_bool(false);
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(5.into());
    let six = terms.mk_int(6.into());

    let le5 = terms.mk_le(x, five);
    let ge6 = terms.mk_ge(x, six);
    let n1 = terms.mk_not(le5);
    let n2 = terms.mk_not(ge6);
    let clause = vec![n1, n2];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);

    let a_atoms: HashSet<TermId> = [le5].into_iter().collect();
    let b_atoms: HashSet<TermId> = [ge6].into_iter().collect();
    let a_vars: HashSet<TermId> = [x].into_iter().collect();
    let b_vars: HashSet<TermId> = [x].into_iter().collect();
    let shared_vars: HashSet<TermId> = [x].into_iter().collect();
    let part = CertPartition {
        a_atoms: &a_atoms,
        b_atoms: &b_atoms,
        a_vars: &a_vars,
        b_vars: &b_vars,
        shared_vars: &shared_vars,
    };

    reset_cert_leaf_stats();
    let itp = certificate_lemma_interpolant(
        &mut terms,
        &clause,
        &farkas,
        &part,
        InterpolantStrength::Strongest,
        true_tid,
        false_tid,
    )
    .expect("inequality-shape certificate leaf must interpolate");

    let expected = terms.mk_le(x, five);
    assert_eq!(itp, expected, "A-part weighted sum must be x <= 5");
}

/// All-A support: the refutation lives inside `A AND not(C|A)`, so the
/// partial interpolant is `false`.
#[test]
fn test_cert_leaf_all_a_support_is_false() {
    let mut terms = TermStore::new();
    let true_tid = terms.mk_bool(true);
    let false_tid = terms.mk_bool(false);
    let a = terms.mk_var("a", Sort::Int);
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());

    let a_eq_1 = terms.mk_eq(a, one);
    let a_eq_2 = terms.mk_eq(a, two);
    let n1 = terms.mk_not(a_eq_1);
    let n2 = terms.mk_not(a_eq_2);
    let clause = vec![n1, n2];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);

    let a_atoms: HashSet<TermId> = [a_eq_1, a_eq_2].into_iter().collect();
    let b_atoms: HashSet<TermId> = HashSet::default();
    let a_vars: HashSet<TermId> = [a].into_iter().collect();
    let b_vars: HashSet<TermId> = HashSet::default();
    let shared_vars: HashSet<TermId> = HashSet::default();
    let part = CertPartition {
        a_atoms: &a_atoms,
        b_atoms: &b_atoms,
        a_vars: &a_vars,
        b_vars: &b_vars,
        shared_vars: &shared_vars,
    };

    let itp = certificate_lemma_interpolant(
        &mut terms,
        &clause,
        &farkas,
        &part,
        InterpolantStrength::Strongest,
        true_tid,
        false_tid,
    )
    .expect("all-A certificate leaf must interpolate");
    assert_eq!(itp, false_tid);
}

/// A certificate that fails semantic re-verification must be REJECTED
/// (returns None; the caller keeps the old behavior).
#[test]
fn test_cert_leaf_invalid_certificate_rejected() {
    let mut terms = TermStore::new();
    let true_tid = terms.mk_bool(true);
    let false_tid = terms.mk_bool(false);
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(5.into());
    let six = terms.mk_int(6.into());

    let le5 = terms.mk_le(x, five);
    let ge6 = terms.mk_ge(x, six);
    let n1 = terms.mk_not(le5);
    let n2 = terms.mk_not(ge6);
    let clause = vec![n1, n2];
    // Zeroing the second coefficient leaves `x <= 5` alone: no contradiction.
    let farkas = FarkasAnnotation::from_ints(&[1, 0]);

    let a_atoms: HashSet<TermId> = [le5].into_iter().collect();
    let b_atoms: HashSet<TermId> = [ge6].into_iter().collect();
    let a_vars: HashSet<TermId> = [x].into_iter().collect();
    let b_vars: HashSet<TermId> = [x].into_iter().collect();
    let shared_vars: HashSet<TermId> = [x].into_iter().collect();
    let part = CertPartition {
        a_atoms: &a_atoms,
        b_atoms: &b_atoms,
        a_vars: &a_vars,
        b_vars: &b_vars,
        shared_vars: &shared_vars,
    };

    reset_cert_leaf_stats();
    let itp = certificate_lemma_interpolant(
        &mut terms,
        &clause,
        &farkas,
        &part,
        InterpolantStrength::Strongest,
        true_tid,
        false_tid,
    );
    assert!(itp.is_none(), "unverified certificate must be rejected");
    let stats = last_cert_leaf_stats();
    assert_eq!(stats.attempted, 1);
    assert_eq!(stats.verified, 0);
    assert_eq!(stats.served, 0);
}

/// Mixed equality+inequality conflict (rank-4 inc-6, the executor's
/// lia_generic shape): A: a = x, a <= 5 (a A-local, x shared);
/// B: b = x, b >= 6 (b B-local). Conflict: x <= 5 /\ x >= 6.
/// Expected A-part Farkas sum onto {x}: `x <= 5`.
#[test]
fn test_cert_leaf_mixed_eq_ineq_shape() {
    let mut terms = TermStore::new();
    let true_tid = terms.mk_bool(true);
    let false_tid = terms.mk_bool(false);
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(5.into());
    let six = terms.mk_int(6.into());

    let a_eq_x = terms.mk_eq(a, x);
    let a_le_5 = terms.mk_le(a, five);
    let b_eq_x = terms.mk_eq(b, x);
    let b_ge_6 = terms.mk_ge(b, six);

    // Clause = negated conflict: [!(a=x), !(a<=5), !(b=x), !(b>=6)].
    let n1 = terms.mk_not(a_eq_x);
    let n2 = terms.mk_not(a_le_5);
    let n3 = terms.mk_not(b_eq_x);
    let n4 = terms.mk_not(b_ge_6);
    let clause = vec![n1, n2, n3, n4];
    // a<=5 with weight 1, b>=6 (i.e. 6-b<=0) with weight 1; the equality
    // rows are oriented by the search: (x - a) and (b - x).
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1, 1]);

    let a_atoms: HashSet<TermId> = [a_eq_x, a_le_5].into_iter().collect();
    let b_atoms: HashSet<TermId> = [b_eq_x, b_ge_6].into_iter().collect();
    let a_vars: HashSet<TermId> = [a, x].into_iter().collect();
    let b_vars: HashSet<TermId> = [b, x].into_iter().collect();
    let shared_vars: HashSet<TermId> = [x].into_iter().collect();
    let part = CertPartition {
        a_atoms: &a_atoms,
        b_atoms: &b_atoms,
        a_vars: &a_vars,
        b_vars: &b_vars,
        shared_vars: &shared_vars,
    };

    reset_cert_leaf_stats();
    let itp = certificate_lemma_interpolant(
        &mut terms,
        &clause,
        &farkas,
        &part,
        InterpolantStrength::Strongest,
        true_tid,
        false_tid,
    )
    .expect("mixed-shape certificate leaf must interpolate");

    // A-part sum: 1*(a - x oriented as x - a = 0... whichever orientation
    // contradicts) + 1*(a - 5 <= 0) = x - 5 <= 0, rendered `x <= 5`.
    let expected = terms.mk_le(x, five);
    assert_eq!(itp, expected, "A-part Farkas sum must be x <= 5");
    let stats = last_cert_leaf_stats();
    assert_eq!(stats.attempted, 1);
    assert_eq!(stats.verified, 1);
    assert_eq!(stats.served, 1);
}

/// Mixed shape with a disequality still bails (case-split shape unsupported),
/// even when the certificate itself verifies: A: a = x, y <= 5;
/// B: x != a (as the distinct atom `x = a` asserted false), y >= 5.
/// The equality row absorbs the disequality's sign flip in each case-split
/// branch and the y bounds cancel, so the certificate is valid — but the
/// leaf rule must still return None for this shape (validated fallback).
#[test]
fn test_cert_leaf_mixed_with_diseq_bails() {
    let mut terms = TermStore::new();
    let true_tid = terms.mk_bool(true);
    let false_tid = terms.mk_bool(false);
    let a = terms.mk_var("a", Sort::Int);
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let five = terms.mk_int(5.into());

    let a_eq_x = terms.mk_eq(a, x);
    let x_eq_a = terms.mk_eq(x, a);
    let y_le_5 = terms.mk_le(y, five);
    let y_ge_5 = terms.mk_ge(y, five);

    // Clause = negated conflict: asserts a = x, x != a, y <= 5, y >= 5.
    let n1 = terms.mk_not(a_eq_x);
    let n3 = terms.mk_not(y_le_5);
    let n4 = terms.mk_not(y_ge_5);
    let clause = vec![n1, x_eq_a, n3, n4];
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1, 1]);

    let a_atoms: HashSet<TermId> = [a_eq_x, y_le_5].into_iter().collect();
    let b_atoms: HashSet<TermId> = [x_eq_a, y_ge_5].into_iter().collect();
    let a_vars: HashSet<TermId> = [a, x, y].into_iter().collect();
    let b_vars: HashSet<TermId> = [a, x, y].into_iter().collect();
    let shared_vars: HashSet<TermId> = [a, x, y].into_iter().collect();
    let part = CertPartition {
        a_atoms: &a_atoms,
        b_atoms: &b_atoms,
        a_vars: &a_vars,
        b_vars: &b_vars,
        shared_vars: &shared_vars,
    };

    reset_cert_leaf_stats();
    let itp = certificate_lemma_interpolant(
        &mut terms,
        &clause,
        &farkas,
        &part,
        InterpolantStrength::Strongest,
        true_tid,
        false_tid,
    );
    assert!(
        itp.is_none(),
        "disequality + inequality support must keep bailing (validated fallback)"
    );
    let stats = last_cert_leaf_stats();
    assert_eq!(stats.attempted, 1);
    assert_eq!(
        stats.verified, 1,
        "the case-split certificate itself must verify (the bail is the SHAPE)"
    );
    assert_eq!(stats.served, 0);
}

/// McMillan' (Weakest) labels shared atoms `a`: with the disequality shared,
/// it moves to the A side and the result is the negated B-side projection.
#[test]
fn test_cert_leaf_labeling_moves_shared_diseq() {
    let mut terms = TermStore::new();
    let true_tid = terms.mk_bool(true);
    let false_tid = terms.mk_bool(false);
    let b = terms.mk_var("b", Sort::Int);
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(5.into());

    // A: x = 5 ... B: b = x; shared diseq atom: (b = 5) occurs in BOTH.
    let x_eq_5 = terms.mk_eq(x, five);
    let b_eq_x = terms.mk_eq(b, x);
    let b_eq_5 = terms.mk_eq(b, five);
    let n1 = terms.mk_not(x_eq_5);
    let n2 = terms.mk_not(b_eq_x);
    let clause = vec![n1, n2, b_eq_5];
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);

    let a_atoms: HashSet<TermId> = [x_eq_5, b_eq_5].into_iter().collect();
    let b_atoms: HashSet<TermId> = [b_eq_x, b_eq_5].into_iter().collect();
    let a_vars: HashSet<TermId> = [x, b].into_iter().collect();
    let b_vars: HashSet<TermId> = [b, x].into_iter().collect();
    let shared_vars: HashSet<TermId> = [x, b].into_iter().collect();
    let part = CertPartition {
        a_atoms: &a_atoms,
        b_atoms: &b_atoms,
        a_vars: &a_vars,
        b_vars: &b_vars,
        shared_vars: &shared_vars,
    };

    // Weakest: shared diseq labeled `a` -> negated B projection.
    let itp = certificate_lemma_interpolant(
        &mut terms,
        &clause,
        &farkas,
        &part,
        InterpolantStrength::Weakest,
        true_tid,
        false_tid,
    )
    .expect("shared-diseq certificate leaf must interpolate under Weakest");
    // Expected: NOT of the rendered B row `b - x = 0`, replicating the
    // renderer's construction (sum = b + (-1)*x, rhs = 0).
    let expected = {
        let neg_one = terms.mk_int((-1).into());
        let minus_x = terms.mk_mul(vec![neg_one, x]);
        let sum = terms.mk_add(vec![b, minus_x]);
        let zero_t = terms.mk_int(0.into());
        let row = terms.mk_eq(sum, zero_t);
        terms.mk_not(row)
    };
    assert_eq!(
        itp, expected,
        "Weakest labeling must produce the negated B-side projection"
    );

    // Strongest: shared diseq labeled `b` -> A-side projection (x = 5).
    let itp_strong = certificate_lemma_interpolant(
        &mut terms,
        &clause,
        &farkas,
        &part,
        InterpolantStrength::Strongest,
        true_tid,
        false_tid,
    )
    .expect("shared-diseq certificate leaf must interpolate under Strongest");
    let expected_strong = terms.mk_eq(x, five);
    assert_eq!(itp_strong, expected_strong);
}

/// Integer-gap conflict (real-SAT, int-UNSAT): `x < y, y < z, z < w` on the
/// A side and `w < x + 2` on the B side. Over the rationals the strict rows
/// are satisfiable (`x = 0, y = 1/2, z = 1, w = 3/2`); the verifier accepts
/// the unit multipliers only after integer-strengthening every strict row
/// (`lin < 0` -> `lin + 1 <= 0`), so the served A-part sum must be built
/// over the TIGHTENED rows: `x - w + 3 <= 0`. The untightened sum `x - w < 0`
/// is not a LIA interpolant — `I /\ B` (`x < w < x + 2`) has the integer
/// model `w = x + 1`.
#[test]
fn test_cert_leaf_integer_gap_strict_rows_are_tightened() {
    let mut terms = TermStore::new();
    let true_tid = terms.mk_bool(true);
    let false_tid = terms.mk_bool(false);
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let two = terms.mk_int(2.into());
    let x_plus_2 = terms.mk_add(vec![x, two]);

    let xy = terms.mk_lt(x, y);
    let yz = terms.mk_lt(y, z);
    let zw = terms.mk_lt(z, w);
    let wx = terms.mk_lt(w, x_plus_2);
    let clause: Vec<TermId> = [xy, yz, zw, wx].iter().map(|&a| terms.mk_not(a)).collect();
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1, 1]);

    let a_atoms: HashSet<TermId> = [xy, yz, zw].into_iter().collect();
    let b_atoms: HashSet<TermId> = [wx].into_iter().collect();
    let a_vars: HashSet<TermId> = [x, y, z, w].into_iter().collect();
    let b_vars: HashSet<TermId> = [x, w].into_iter().collect();
    let shared_vars: HashSet<TermId> = [x, w].into_iter().collect();
    let part = CertPartition {
        a_atoms: &a_atoms,
        b_atoms: &b_atoms,
        a_vars: &a_vars,
        b_vars: &b_vars,
        shared_vars: &shared_vars,
    };

    reset_cert_leaf_stats();
    let itp = certificate_lemma_interpolant(
        &mut terms,
        &clause,
        &farkas,
        &part,
        InterpolantStrength::Strongest,
        true_tid,
        false_tid,
    )
    .expect("integer-gap certificate leaf must interpolate over the tightened rows");

    // Tightened A-part sum: (x - y + 1) + (y - z + 1) + (z - w + 1) <= 0,
    // i.e. x - w + 3 <= 0, rendered as `x + (-1 * w) <= -3`.
    let minus_one = terms.mk_int((-1).into());
    let neg_w = terms.mk_mul(vec![minus_one, w]);
    let sum = terms.mk_add(vec![x, neg_w]);
    let minus_three = terms.mk_int((-3).into());
    let expected = terms.mk_le(sum, minus_three);
    // The untightened, real-only sum `x - w < 0` must NOT be served.
    let zero = terms.mk_int(0.into());
    let untightened = terms.mk_lt(sum, zero);
    assert_ne!(
        itp, untightened,
        "served interpolant must not be the real-only sum x - w < 0"
    );
    assert_eq!(
        itp, expected,
        "A-part weighted sum must be over the tightened rows: x - w + 3 <= 0"
    );
    let stats = last_cert_leaf_stats();
    assert_eq!(stats.attempted, 1);
    assert_eq!(
        stats.verified, 1,
        "the verifier accepts the unit multipliers over the TIGHTENED rows"
    );
    assert_eq!(stats.served, 1);
}

/// The fail-closed side of the tightening gate: a strict row over REAL
/// variables must NOT be tightened. `A = {x < y}`, `B = {y <= x}` (unit
/// multipliers) is a real refutation whose A-part interpolant is the strict
/// row itself, `x - y < 0`; tightening it to `x - y + 1 <= 0` would serve a
/// formula A does not entail (`x = 0, y = 1/2`).
#[test]
fn test_cert_leaf_real_strict_row_is_not_tightened() {
    let mut terms = TermStore::new();
    let true_tid = terms.mk_bool(true);
    let false_tid = terms.mk_bool(false);
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);

    let xy = terms.mk_lt(x, y);
    let yx = terms.mk_le(y, x);
    let clause: Vec<TermId> = [xy, yx].iter().map(|&a| terms.mk_not(a)).collect();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);

    let a_atoms: HashSet<TermId> = [xy].into_iter().collect();
    let b_atoms: HashSet<TermId> = [yx].into_iter().collect();
    let a_vars: HashSet<TermId> = [x, y].into_iter().collect();
    let b_vars: HashSet<TermId> = [x, y].into_iter().collect();
    let shared_vars: HashSet<TermId> = [x, y].into_iter().collect();
    let part = CertPartition {
        a_atoms: &a_atoms,
        b_atoms: &b_atoms,
        a_vars: &a_vars,
        b_vars: &b_vars,
        shared_vars: &shared_vars,
    };

    reset_cert_leaf_stats();
    let itp = certificate_lemma_interpolant(
        &mut terms,
        &clause,
        &farkas,
        &part,
        InterpolantStrength::Strongest,
        true_tid,
        false_tid,
    )
    .expect("real strict-row certificate leaf must interpolate");

    // Untightened, as decoded: x - y < 0, rendered over Real as
    // `x + ((- 1) * y) < 0` — Real coefficients and constant, since ay-core's
    // `mk_mul`/`mk_add` refuse an Int constant beside a Real variable.
    let minus_one = terms.mk_rational(BigRational::from(BigInt::from(-1)));
    let neg_y = terms.mk_mul(vec![minus_one, y]);
    let sum = terms.mk_add(vec![x, neg_y]);
    let zero = terms.mk_rational(BigRational::from(BigInt::from(0)));
    let expected = terms.mk_lt(sum, zero);
    assert_eq!(
        itp, expected,
        "a Real strict row is served untightened: x - y < 0"
    );
    let stats = last_cert_leaf_stats();
    assert_eq!((stats.attempted, stats.verified, stats.served), (1, 1, 1));
}

/// The LRA solver's trust-kind restatement lemma `(cl (= v 1) (not (= -1 (- v))))`
/// is recognised as valid (the two equalities are the same linear equation);
/// different equations, or the same polarity twice, are not.
#[test]
fn test_equality_restatement_recognised() {
    let mut terms = TermStore::new();
    let v = terms.mk_var("v", Sort::Real);
    let one = terms.mk_rational(BigRational::one());
    let two = terms.mk_rational(BigRational::from_integer(BigInt::from(2)));
    let minus_one = terms.mk_rational(-BigRational::one());
    let eq = |terms: &mut TermStore, l: TermId, r: TermId| {
        terms.mk_app(Symbol::named("="), [l, r], Sort::Bool)
    };
    let neg_v = terms.mk_app(Symbol::named("-"), [v], Sort::Real);
    let v_is_1 = eq(&mut terms, v, one);
    let restated = eq(&mut terms, minus_one, neg_v);
    let v_is_2 = eq(&mut terms, v, two);
    let not_restated = terms.mk_not(restated);
    let not_v_is_2 = terms.mk_not(v_is_2);
    assert!(is_equality_restatement(&terms, &[v_is_1, not_restated]));
    assert!(is_equality_restatement(&terms, &[not_restated, v_is_1]));
    assert!(!is_equality_restatement(&terms, &[v_is_1, not_v_is_2]));
    assert!(!is_equality_restatement(&terms, &[v_is_1, restated]));
    assert!(!is_equality_restatement(&terms, &[v_is_1]));
}

#[test]
fn test_linear_arith_valid_clause_by_elimination() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let num = |terms: &mut TermStore, n: i64| {
        terms.mk_rational(BigRational::from_integer(BigInt::from(n)))
    };
    let (one, two, three) = (num(&mut terms, 1), num(&mut terms, 2), num(&mut terms, 3));
    let app = |terms: &mut TermStore, op: &str, l: TermId, r: TermId, sort: Sort| {
        terms.mk_app(Symbol::named(op), [l, r], sort)
    };
    let x_le_1 = app(&mut terms, "<=", x, one, Sort::Bool);
    let y_le_2 = app(&mut terms, "<=", y, two, Sort::Bool);
    let sum = app(&mut terms, "+", x, y, Sort::Real);
    let sum_le_3 = app(&mut terms, "<=", sum, three, Sort::Bool);
    let sum_le_2 = app(&mut terms, "<=", sum, two, Sort::Bool);
    let not_x_le_1 = terms.mk_not(x_le_1);
    let not_y_le_2 = terms.mk_not(y_le_2);
    // x <= 1 ∧ y <= 2 ⊨ x + y <= 3, but not x + y <= 2.
    assert!(is_linear_arith_valid_clause(
        &terms,
        &[not_x_le_1, not_y_le_2, sum_le_3]
    ));
    assert!(!is_linear_arith_valid_clause(
        &terms,
        &[not_x_le_1, not_y_le_2, sum_le_2]
    ));
    // Strictness: x <= 1 ∨ x >= 1 is valid, x < 1 ∨ x > 1 is not (x = 1).
    let x_ge_1 = app(&mut terms, ">=", x, one, Sort::Bool);
    let x_lt_1 = app(&mut terms, "<", x, one, Sort::Bool);
    let x_gt_1 = app(&mut terms, ">", x, one, Sort::Bool);
    assert!(is_linear_arith_valid_clause(&terms, &[x_le_1, x_ge_1]));
    assert!(!is_linear_arith_valid_clause(&terms, &[x_lt_1, x_gt_1]));
    // A positive equality asserts a disequality: not decided.
    let x_is_1 = app(&mut terms, "=", x, one, Sort::Bool);
    assert!(!is_linear_arith_valid_clause(
        &terms,
        &[x_is_1, x_lt_1, x_gt_1]
    ));
    assert!(!is_linear_arith_valid_clause(&terms, &[]));
}

/// A valid exact arithmetic witness is not partition authority. Conflicting
/// coloring that claims x is local to both sides but absent from the shared
/// symbols must not serve a partial interpolant from that witness.
#[test]
fn retained_certificate_refuses_a_conflicting_shared_partition() {
    let mut terms = TermStore::new();
    let true_tid = terms.mk_bool(true);
    let false_tid = terms.mk_bool(false);
    let x = terms.mk_var("retained_partition_x", Sort::Int);
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let low = terms.mk_le(x, zero);
    let high = terms.mk_ge(x, one);
    let clause = vec![terms.mk_not(low), terms.mk_not(high)];
    let witness = FarkasAnnotation::from_ints(&[1, 1]);
    let a_atoms: HashSet<TermId> = [low].into_iter().collect();
    let b_atoms: HashSet<TermId> = [high].into_iter().collect();
    let a_vars: HashSet<TermId> = [x].into_iter().collect();
    let b_vars: HashSet<TermId> = [x].into_iter().collect();
    let shared_vars = HashSet::default();
    let part = CertPartition {
        a_atoms: &a_atoms,
        b_atoms: &b_atoms,
        a_vars: &a_vars,
        b_vars: &b_vars,
        shared_vars: &shared_vars,
    };
    reset_cert_leaf_stats();
    assert!(certificate_lemma_interpolant(
        &mut terms,
        &clause,
        &witness,
        &part,
        InterpolantStrength::Strongest,
        true_tid,
        false_tid
    )
    .is_none());
    let stats = last_cert_leaf_stats();
    assert_eq!(
        stats.verified, 1,
        "the certificate itself is a real contradiction"
    );
    assert_eq!(
        stats.served, 0,
        "inconsistent partition ownership grants nothing"
    );
}
