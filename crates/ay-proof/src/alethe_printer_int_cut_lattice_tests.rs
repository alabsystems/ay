// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict-checker and external-lowering tests for
//! `TheoryLemmaKind::IntCutLatticeGap`.
//!
//! The lemma is certified INTERNALLY (`ay-proof` re-derives both the cut
//! multipliers and the integer core from the clause) and is deliberately
//! UNCHECKABLE externally: the pinned Alethe calculus has no rule for a
//! Chvátal–Gomory combination followed by a lattice argument, so the step
//! renders as an honest `hole`.
//!
//! The near-miss these tests exist to prevent is the same one
//! `IntBoundLatticeGap` documents, one step further along. `la_generic` with
//! the cut's own multipliers would print a step that is FALSE: the combination
//! `2A >= 1` together with `2A <= 1` sums, rationally, to the TRUE `0 >= 0`.
//! The gap exists only over ℤ, which `la_generic` cannot state.

use super::*;
use ay_core::{FarkasAnnotation, Sort, TermStore, TheoryLemmaKind};

#[path = "alethe_printer_int_guarded_split_diseq_tests.rs"]
mod guarded_split_diseq;
use num_bigint::BigInt;
use num_rational::Rational64;

/// `(cl (< y 0) (not (<= y 0)) (< (+ (* 2 x) y) 1) (not (<= (+ (* 2 x) y) 1)))`
/// — negating all four pins `y` to 0 and `2x + y` to 1, hence `2x = 1`:
/// impossible over ℤ, satisfiable at `x = 1/2, y = 0` over ℚ, and reachable
/// only by ELIMINATING `y` between two rows.
fn cut_gap_clause(terms: &mut TermStore) -> Vec<TermId> {
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let two_x = terms.mk_mul(vec![two, x]);
    let form = terms.mk_add(vec![two_x, y]);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let y_lower = terms.mk_lt(y, zero);
    let y_upper = terms.mk_le(y, zero);
    let y_upper = terms.mk_not(y_upper);
    let f_lower = terms.mk_lt(form, one);
    let f_upper = terms.mk_le(form, one);
    let f_upper = terms.mk_not(f_upper);
    vec![y_lower, y_upper, f_lower, f_upper]
}

fn cut_step(clause: Vec<TermId>, farkas: Option<FarkasAnnotation>) -> ProofStep {
    ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause,
        farkas,
        kind: TheoryLemmaKind::IntCutLatticeGap,
        lia: None,
    }
}

#[test]
fn strict_checker_accepts_the_cut_gap_and_rejects_a_forged_label() {
    let mut terms = TermStore::new();
    let clause = cut_gap_clause(&mut terms);
    let step = cut_step(clause, None);
    let mut derived = Vec::new();
    checker::validate_step(&terms, &mut derived, ProofId(0), &step, true, None)
        .expect("the two-row cut gap must validate in strict mode");

    // FORGERY: the same kind on a clause with no gap at all. `(cl (< x 0))`
    // is falsified at x = 5, so accepting it would be a meta-false PROVE.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let atom = terms.mk_lt(x, zero);
    let forged = cut_step(vec![atom], None);
    let mut derived = Vec::new();
    assert!(
        checker::validate_step(&terms, &mut derived, ProofId(0), &forged, true, None).is_err(),
        "a forged IntCutLatticeGap label must be refused: falsified at x = 5"
    );
}

/// FORGERY, the sharper one: a clause whose rows DO combine but whose derived
/// range holds an attainable point. `2x + y ∈ [2, 2]` with `y ∈ [0, 0]` gives
/// `2x = 2`, satisfied at `x = 1, y = 0`, so the clause is false there.
#[test]
fn strict_checker_rejects_a_cut_whose_derived_range_is_attainable() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let two_x = terms.mk_mul(vec![two, x]);
    let form = terms.mk_add(vec![two_x, y]);
    let zero = terms.mk_int(BigInt::from(0));
    let two_again = terms.mk_int(BigInt::from(2));
    let y_lower = terms.mk_lt(y, zero);
    let y_upper = terms.mk_le(y, zero);
    let y_upper = terms.mk_not(y_upper);
    let f_lower = terms.mk_lt(form, two_again);
    let f_upper = terms.mk_le(form, two_again);
    let f_upper = terms.mk_not(f_upper);
    let step = cut_step(vec![y_lower, y_upper, f_lower, f_upper], None);
    let mut derived = Vec::new();
    assert!(
        checker::validate_step(&terms, &mut derived, ProofId(0), &step, true, None).is_err(),
        "the range [2, 2] contains the attainable value 2: falsified at x = 1, y = 0"
    );
}

/// The wire is an honest `hole`, never a rule name the pinned checker does not
/// implement (which would take the document from `holey` to `invalid`).
#[test]
fn the_cut_gap_prints_an_honest_hole() {
    let mut terms = TermStore::new();
    let clause = cut_gap_clause(&mut terms);
    let step = cut_step(clause, None);
    let printer = AlethePrinter::new(&terms);
    let text = printer
        .format_step(&step, ProofId(3))
        .expect("the cut gap renders");
    assert!(
        text.ends_with(":rule hole)"),
        "the cut gap has no Alethe rule and must print as a hole: {text}"
    );
    assert!(
        !text.contains("la_generic") && !text.contains("int_cut"),
        "no unimplemented rule name may reach the wire: {text}"
    );
}

/// `la_generic` would be FALSE here, and this pins why the kind does not reuse
/// it. The cut's own rows are `2x + y >= 1` and `-(2x + y) >= -1`; a unit
/// rational combination of them sums to `0 >= 0`, which is TRUE, so a
/// `la_generic` step over this clause would assert a contradiction that the
/// printed coefficients do not produce.
#[test]
fn the_la_generic_lowering_would_have_been_false_here() {
    let mut terms = TermStore::new();
    let clause = cut_gap_clause(&mut terms);
    // The rational combination the printer would have emitted, evaluated by
    // hand: coefficient 1 on each of the four rows.
    //   (2x + y) - (2x + y) + y - y = 0   and   1 - 1 + 0 - 0 = 0
    // i.e. `0 >= 0`, not a contradiction — over ℚ the negation is satisfiable
    // at x = 1/2, y = 0, which is exactly why the rule is an integer one.
    let step = cut_step(clause, None);
    let printer = AlethePrinter::new(&terms);
    let text = printer
        .format_step(&step, ProofId(3))
        .expect("the cut gap renders");
    assert!(!text.contains(":rule la_generic"), "{text}");
}

/// A stale positional certificate must not reach the wire: `hole` takes no
/// `:args`, and `hole :args (..)` makes a document `invalid` rather than
/// `holey`.
#[test]
fn a_stale_farkas_payload_cannot_reach_the_cut_wire() {
    let mut terms = TermStore::new();
    let clause = cut_gap_clause(&mut terms);
    let farkas = FarkasAnnotation::new(vec![
        Rational64::new(1, 1),
        Rational64::new(1, 1),
        Rational64::new(1, 1),
        Rational64::new(1, 1),
    ]);
    let step = cut_step(clause, Some(farkas));
    let printer = AlethePrinter::new(&terms);
    let text = printer
        .format_step(&step, ProofId(3))
        .expect("the cut gap renders");
    assert!(
        !text.contains(":args"),
        "a hole step must carry no arguments: {text}"
    );
    assert!(text.ends_with(":rule hole)"), "{text}");
}
