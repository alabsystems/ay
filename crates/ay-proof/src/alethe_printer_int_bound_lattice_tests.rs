// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict-checker and external-lowering tests for
//! `TheoryLemmaKind::IntBoundLatticeGap`.
//!
//! The lemma is certified INTERNALLY (`ay-proof` re-derives its integer core
//! from the clause) and is deliberately UNCHECKABLE externally: the pinned
//! Alethe calculus has no rule for the lattice argument, so the step renders as
//! an honest `hole`.
//!
//! The near-miss these tests exist to prevent is concrete. The sibling kind
//! `IntBoundsTautology` lowers to `la_generic :args (1 1)`, and that unit
//! combination is a genuine rational contradiction ONLY because its rule
//! demands `lower > upper`. This kind's whole point is `lower <= upper` with no
//! attainable lattice point between, where the same unit combination sums to
//! `0 >= 0` — TRUE — so re-using that lowering would print a FALSE sub-step.

use super::*;
use ay_core::{FarkasAnnotation, Sort, TermStore, TheoryLemmaKind};
use num_bigint::BigInt;
use num_rational::Rational64;

/// `(cl (< (* 2 q) 1) (not (<= (* 2 q) 1)))` — negating both literals pins
/// `2q` to exactly 1, impossible over ℤ and satisfiable at `q = 1/2` over ℚ.
fn lattice_gap_clause(terms: &mut TermStore) -> Vec<TermId> {
    let q = terms.mk_var("q", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let scaled = terms.mk_mul(vec![two, q]);
    let one = terms.mk_int(BigInt::from(1));
    let lower = terms.mk_lt(scaled, one);
    let one_again = terms.mk_int(BigInt::from(1));
    let upper = terms.mk_le(scaled, one_again);
    let not_upper = terms.mk_not(upper);
    vec![lower, not_upper]
}

fn lattice_step(clause: Vec<TermId>, farkas: Option<FarkasAnnotation>) -> ProofStep {
    ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause,
        farkas,
        kind: TheoryLemmaKind::IntBoundLatticeGap,
        lia: None,
    }
}

#[test]
fn strict_checker_accepts_the_lattice_gap_and_rejects_a_forged_label() {
    let mut terms = TermStore::new();
    let clause = lattice_gap_clause(&mut terms);
    let step = lattice_step(clause, None);
    let mut derived = Vec::new();
    checker::validate_step(&terms, &mut derived, ProofId(0), &step, true, None)
        .expect("the lattice gap must validate in strict mode");

    // FORGERY: the same kind on a clause with no gap at all. `x <= 0` is
    // falsified at x = 1, so accepting it would be a meta-false-PROVE.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let bound = terms.mk_le(x, zero);
    let forged = lattice_step(vec![bound], None);
    let mut derived = Vec::new();
    let error = checker::validate_step(&terms, &mut derived, ProofId(0), &forged, true, None)
        .expect_err("a forged lattice-gap label must be rejected");
    assert!(
        matches!(error, ProofCheckError::InvalidTheoryLemma { .. }),
        "{error:?}",
    );
}

#[test]
fn strict_checker_rejects_the_same_shape_over_real_sorted_variables() {
    // FALSIFYING ASSIGNMENT: r = 1/2. The lattice argument is INTEGER-only.
    let mut terms = TermStore::new();
    let r = terms.mk_var("r", Sort::Real);
    let two = terms.mk_rational(num_rational::BigRational::from(BigInt::from(2)));
    let scaled = terms.mk_mul(vec![two, r]);
    let one = terms.mk_rational(num_rational::BigRational::from(BigInt::from(1)));
    let lower = terms.mk_lt(scaled, one);
    let one_again = terms.mk_rational(num_rational::BigRational::from(BigInt::from(1)));
    let upper = terms.mk_le(scaled, one_again);
    let not_upper = terms.mk_not(upper);
    let step = lattice_step(vec![lower, not_upper], None);
    let mut derived = Vec::new();
    assert!(
        checker::validate_step(&terms, &mut derived, ProofId(0), &step, true, None).is_err(),
        "a Real-sorted form is satisfiable at r = 1/2 and must not validate",
    );
}

#[test]
fn lattice_gap_lowers_to_an_honest_hole_never_to_la_generic() {
    let mut terms = TermStore::new();
    let clause = lattice_gap_clause(&mut terms);
    let step = lattice_step(clause, None);

    let rendered = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(4))
        .expect("the lattice gap must render, not error");

    assert_eq!(
        rendered,
        "(step t4 (cl (< (* q 2) 1) (not (<= (* q 2) 1))) :rule hole)",
    );
    assert!(!rendered.contains("la_generic"), "{rendered}");
    assert!(!rendered.contains(":args"), "{rendered}");
}

#[test]
fn a_stale_farkas_payload_cannot_reach_the_wire() {
    // A promoted step could in principle still carry coefficients from an
    // earlier classification. `hole` takes no `:args`, and a rule name the
    // checker does not implement printed WITH args takes the whole document
    // from `holey` to `invalid`, so the hole arm must run BEFORE the Farkas
    // arm. Byte-identical output with and without the payload proves it does.
    let mut terms = TermStore::new();
    let clause = lattice_gap_clause(&mut terms);
    let coefficients = FarkasAnnotation::new(vec![Rational64::from_integer(1); 2]);
    let with_payload = lattice_step(clause.clone(), Some(coefficients));
    let without_payload = lattice_step(clause, None);

    let printer = AlethePrinter::new(&terms);
    assert_eq!(
        printer
            .format_step(&with_payload, ProofId(4))
            .expect("render"),
        printer
            .format_step(&without_payload, ProofId(4))
            .expect("render"),
    );
}

#[test]
fn the_int_bounds_tautology_lowering_would_have_been_false_here() {
    // The trap, stated as an executable fact rather than a comment: the
    // sibling kind's `la_generic :args (1 1)` lowering IS emitted for a
    // `lower > upper` gap, and the strict checker REFUSES to certify this
    // clause under that kind — so the two lowerings are not interchangeable.
    let mut terms = TermStore::new();
    let clause = lattice_gap_clause(&mut terms);

    let as_bounds_tautology = ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause: clause.clone(),
        farkas: None,
        kind: TheoryLemmaKind::IntBoundsTautology,
        lia: None,
    };
    let mut derived = Vec::new();
    assert!(
        checker::validate_step(
            &terms,
            &mut derived,
            ProofId(0),
            &as_bounds_tautology,
            true,
            None,
        )
        .is_err(),
        "IntBoundsTautology must not certify a lower <= upper lattice gap",
    );

    // And the genuine `lower > upper` gap it IS for still prints `la_generic`,
    // confirming the two kinds keep different wires.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let six = terms.mk_int(BigInt::from(6));
    let upper = terms.mk_le(x, five);
    let lower = terms.mk_lt(x, six);
    let gap = vec![terms.mk_not(upper), lower];
    let step = ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause: gap,
        farkas: None,
        kind: TheoryLemmaKind::IntBoundsTautology,
        lia: None,
    };
    let rendered = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(9))
        .expect("render");
    assert!(rendered.contains("la_generic"), "{rendered}");
}
