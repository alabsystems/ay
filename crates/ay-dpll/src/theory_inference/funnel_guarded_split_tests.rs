// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The guarded-split funnel arm: the CDCL(T) learned-conflict shape whose
//! certificate is an integer case split over one of the clause's own literals.
//!
//! Before this arm existed the whole family stopped at `LiaGeneric`, which
//! both recorders normalize straight back to `Generic`/trust for want of a
//! certificate it can never have — its negation is satisfiable over ℚ, so no
//! Farkas row exists.

use super::*;
use crate::proof_tracker::ProofTracker;
use num_bigint::BigInt;

/// The corpus clause, copied literally from the census dump of
/// `benchmarks/chc-comp/2025/extra-small-lia/phases_m_000.smt2`:
///
/// ```text
/// (cl (not (= (+ (* 2 q2) r3) (+ (* 2 q0) 2))) (not (< r3 2))
///     (not (<= C (* 2 q0))) (not (<= 0 r3)) (= r3 0))
/// ```
fn census_phases_clause(terms: &mut TermStore) -> Vec<TermId> {
    let q0 = terms.mk_var("q0", Sort::Int);
    let q2 = terms.mk_var("q2", Sort::Int);
    let r3 = terms.mk_var("r3", Sort::Int);
    let c = terms.mk_var("C", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let two_q2 = terms.mk_mul(vec![two, q2]);
    let lhs = terms.mk_add(vec![two_q2, r3]);
    let two_b = terms.mk_int(BigInt::from(2));
    let two_q0 = terms.mk_mul(vec![two_b, q0]);
    let two_c = terms.mk_int(BigInt::from(2));
    let rhs = terms.mk_add(vec![two_q0, two_c]);
    let witness = terms.mk_eq(lhs, rhs);
    let l0 = terms.mk_not_raw(witness);
    let two_d = terms.mk_int(BigInt::from(2));
    let upper = terms.mk_lt(r3, two_d);
    let l1 = terms.mk_not_raw(upper);
    let two_e = terms.mk_int(BigInt::from(2));
    let two_q0_again = terms.mk_mul(vec![two_e, q0]);
    let c_bound = terms.mk_le(c, two_q0_again);
    let l2 = terms.mk_not_raw(c_bound);
    let zero = terms.mk_int(BigInt::from(0));
    let lower = terms.mk_le(zero, r3);
    let l3 = terms.mk_not_raw(lower);
    let zero_again = terms.mk_int(BigInt::from(0));
    let l4 = terms.mk_eq(r3, zero_again);
    vec![l0, l1, l2, l3, l4]
}

/// The funnel types the corpus conflict as `IntGuardedSplitGap` WITHOUT
/// reordering it, and the strict checker's own validator accepts exactly the
/// clause the funnel returns — the classifier==validator rule this funnel
/// states for every payload-free kind.
#[test]
fn funnel_types_the_census_integer_conflict_as_a_guarded_split() {
    let mut terms = TermStore::new();
    let clause = census_phases_clause(&mut terms);
    let (kind, ordered) =
        infer_theory_lemma_kind_from_clause_terms_and_farkas(&terms, &clause, None, None);
    assert_eq!(kind, TheoryLemmaKind::IntGuardedSplitGap);
    assert_eq!(
        ordered.as_ref(),
        clause.as_slice(),
        "the guarded-split arm must never reorder"
    );
    assert!(ay_core::proof_validation::recognize_int_guarded_split_gap(
        &terms, &ordered
    ));
}

/// The recorder types it too, so the tracker and any trace-indexed annotation
/// agree on the kind.
#[test]
fn record_funnel_classified_lemma_types_the_census_integer_conflict() {
    let mut terms = TermStore::new();
    let clause = census_phases_clause(&mut terms);
    let mut tracker = ProofTracker::new();
    let (kind, recorded) =
        record_funnel_classified_lemma(&mut tracker, &terms, clause.clone(), None);
    assert_eq!(kind, TheoryLemmaKind::IntGuardedSplitGap);
    assert_eq!(recorded, clause);
}

/// GUARD, two-sided: dropping the bound that makes the parity argument close
/// leaves a satisfiable branch, and the clause must stay trust-recorded.
/// FALSIFIED AT `r3 = 2, q0 = 0, q2 = 0, C = 0` — every remaining literal is
/// false there, so promoting it would be a meta-false PROVE. The witness is
/// checked below in plain integer arithmetic.
#[test]
fn a_falsifiable_integer_conflict_is_never_promoted_by_the_funnel() {
    let mut terms = TermStore::new();
    let full = census_phases_clause(&mut terms);
    let clause: Vec<TermId> = vec![full[0], full[2], full[3], full[4]];
    let (kind, ordered) =
        infer_theory_lemma_kind_from_clause_terms_and_farkas(&terms, &clause, None, None);
    assert_ne!(kind, TheoryLemmaKind::IntGuardedSplitGap);
    assert_eq!(ordered.as_ref(), clause.as_slice());
    let (q0, q2, r3, c) = (0i64, 0i64, 2i64, 0i64);
    assert_eq!(2 * q2 + r3, 2 * q0 + 2);
    assert!(c <= 2 * q0 && 0 <= r3 && r3 != 0);
}

/// A positional Farkas certificate must never flow into a payload-free kind:
/// the guarded-split validator does not consume one while downstream trace
/// rebinding and external printing do, so a certificate-bearing clause keeps
/// its own classification path.
#[test]
fn a_certificate_bearing_conflict_is_not_typed_as_a_guarded_split() {
    let mut terms = TermStore::new();
    let clause = census_phases_clause(&mut terms);
    let farkas = FarkasAnnotation::from_ints(&vec![1i64; clause.len()]);
    let (kind, _) =
        infer_theory_lemma_kind_from_clause_terms_and_farkas(&terms, &clause, Some(&farkas), None);
    assert_ne!(kind, TheoryLemmaKind::IntGuardedSplitGap);
}
