// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict-checker and external-lowering tests for the guarded-split rule's
//! DISEQUALITY arm — the CDCL(T) learned-conflict shape.
//!
//! The clause below is copied literally from the census dump of
//! `benchmarks/chc-comp/2025/extra-small-lia/phases_m_000.smt2`, which was the
//! single largest `theory=LIA` `Generic` family in the corpus. It carries no
//! payload of any kind: `ay-proof` re-derives the case split, the equality
//! substitution and the lattice gap from the CLAUSE, so there is nothing for a
//! producer to forge.
//!
//! Externally it is deliberately UNCHECKABLE: the pinned Alethe calculus has
//! no rule for "split a disequality, substitute an equality, then apply a
//! Bézout attainability argument", so the step renders as an honest `hole`.
//! `la_generic` would be FALSE here — the negation is satisfiable over ℚ at
//! `r3 = 1, q2 = q0 + 1/2`, so no rational combination of the rows is a
//! contradiction.

use super::*;
use ay_core::{FarkasAnnotation, Sort, TermStore, TheoryLemmaKind};
use num_bigint::BigInt;
use num_rational::Rational64;

/// ```text
/// (cl (not (= (+ (* 2 q2) r3) (+ (* 2 q0) 2)))
///     (not (< r3 2))
///     (not (<= C (* 2 q0)))
///     (not (<= 0 r3))
///     (= r3 0))
/// ```
fn phases_clause(terms: &mut TermStore) -> Vec<TermId> {
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

fn split_step(clause: Vec<TermId>, farkas: Option<FarkasAnnotation>) -> ProofStep {
    ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause,
        farkas,
        kind: TheoryLemmaKind::IntGuardedSplitGap,
        lia: None,
    }
}

#[test]
fn strict_checker_accepts_the_corpus_disequality_split() {
    let mut terms = TermStore::new();
    let clause = phases_clause(&mut terms);
    let step = split_step(clause, None);
    let mut derived = Vec::new();
    checker::validate_step(&terms, &mut derived, ProofId(0), &step, true, None)
        .expect("the corpus disequality split must validate in strict mode");
}

/// FORGERY: the same kind on a clause with no gap on either branch.
/// `(cl (= x 0) (not (<= 0 x)))` is falsified at `x = 5` — `x != 0` and
/// `x >= 0` both hold — so accepting it would be a meta-false PROVE.
#[test]
fn strict_checker_refuses_a_forged_disequality_split_label() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let goal = terms.mk_eq(x, zero);
    let zero_again = terms.mk_int(BigInt::from(0));
    let lower = terms.mk_le(zero_again, x);
    let lower = terms.mk_not_raw(lower);
    let forged = split_step(vec![goal, lower], None);
    let mut derived = Vec::new();
    assert!(
        checker::validate_step(&terms, &mut derived, ProofId(0), &forged, true, None).is_err(),
        "a forged IntGuardedSplitGap label must be refused: falsified at x = 5"
    );
}

/// FORGERY, the sharper one: the branch ranges are non-empty, so the clause is
/// false at the point they admit. `0 <= x <= 1` with `x != 0` is satisfied at
/// `x = 1`; the parity that made the corpus clause valid is absent.
#[test]
fn strict_checker_refuses_a_split_whose_branch_range_is_attainable() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let goal = terms.mk_eq(x, zero);
    let zero_again = terms.mk_int(BigInt::from(0));
    let lower = terms.mk_le(zero_again, x);
    let lower = terms.mk_not_raw(lower);
    let one = terms.mk_int(BigInt::from(1));
    let upper = terms.mk_le(x, one);
    let upper = terms.mk_not_raw(upper);
    let step = split_step(vec![goal, lower, upper], None);
    let mut derived = Vec::new();
    assert!(
        checker::validate_step(&terms, &mut derived, ProofId(0), &step, true, None).is_err(),
        "the branch `x >= 1` is attainable at x = 1, where the clause is false"
    );
}

/// The wire is an honest `hole`, never a rule name the pinned checker does not
/// implement (which would take the document from `holey` to `invalid`).
#[test]
fn the_disequality_split_prints_an_honest_hole() {
    let mut terms = TermStore::new();
    let clause = phases_clause(&mut terms);
    let step = split_step(clause, None);
    let printer = AlethePrinter::new(&terms);
    let text = printer
        .format_step(&step, ProofId(3))
        .expect("the disequality split renders");
    assert!(
        text.ends_with(":rule hole)"),
        "the disequality split has no Alethe rule and must print as a hole: {text}"
    );
    assert!(
        !text.contains("la_generic")
            && !text.contains("int_guarded")
            && !text.contains(":rule trust"),
        "no unimplemented rule name may reach the wire: {text}"
    );
}

/// A stale positional certificate must not reach the wire: `hole` takes no
/// `:args`, and `hole :args (..)` makes a document `invalid` rather than
/// `holey`.
#[test]
fn a_stale_farkas_payload_cannot_reach_the_disequality_split_wire() {
    let mut terms = TermStore::new();
    let clause = phases_clause(&mut terms);
    let farkas = FarkasAnnotation::new(vec![Rational64::new(1, 1); 5]);
    let step = split_step(clause, Some(farkas));
    let printer = AlethePrinter::new(&terms);
    let text = printer
        .format_step(&step, ProofId(3))
        .expect("the disequality split renders");
    assert!(
        !text.contains(":args"),
        "a hole step must carry no arguments: {text}"
    );
    assert!(text.ends_with(":rule hole)"), "{text}");
}

/// The internal rule NAME is stable and is the one the kind's own table gives.
#[test]
fn the_kind_keeps_its_internal_rule_name() {
    assert_eq!(
        TheoryLemmaKind::IntGuardedSplitGap.alethe_rule(),
        "int_guarded_split_gap"
    );
    assert_eq!(
        TheoryLemmaKind::IntGuardedSplitGap.alethe_wire_rule(),
        "hole"
    );
    assert!(!TheoryLemmaKind::IntGuardedSplitGap.is_trust());
}
