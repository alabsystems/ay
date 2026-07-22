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
