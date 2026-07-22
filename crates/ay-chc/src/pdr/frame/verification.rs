// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kani Verification Harnesses for Frame Invariants (#979)

use super::*;
use crate::PredicateId;

/// Generate a symbolic PredicateId for Kani proofs.
fn any_predicate_id() -> PredicateId {
    let id: u32 = kani::any();
    kani::assume(id < 10); // Bound to prevent state explosion
    PredicateId::new(id)
}

/// Generate a symbolic simple ChcExpr (Bool only for tractability).
fn any_simple_expr() -> ChcExpr {
    let v: u8 = kani::any();
    kani::assume(v < 3);
    match v {
        0 => ChcExpr::Bool(false),
        1 => ChcExpr::Bool(true),
        _ => ChcExpr::Int(kani::any::<i8>() as i64),
    }
}

/// Generate a symbolic Lemma.
fn any_lemma() -> Lemma {
    let predicate = any_predicate_id();
    let formula = any_simple_expr();
    let level = {
        let l: u8 = kani::any();
        kani::assume(l < 5);
        l as usize
    };
    let algebraically_verified = kani::any();

    Lemma::new(predicate, formula, level).with_algebraically_verified(algebraically_verified)
}

/// Proof: Adding the same lemma twice results in no duplicate.
/// Frame.add_lemma should deduplicate identical (predicate, formula) pairs.
#[kani::proof]
#[kani::unwind(5)]
fn proof_frame_add_lemma_deduplicates() {
    let mut frame = Frame::new();
    let lemma = any_lemma();
    let lemma_clone = lemma.clone();

    frame.add_lemma(lemma);
    let count_after_first = frame.lemmas.len();

    frame.add_lemma(lemma_clone);
    let count_after_second = frame.lemmas.len();

    // Adding the same lemma twice should not increase count
    assert_eq!(count_after_first, count_after_second);
}

/// Proof: Revision counter is monotonically non-decreasing.
/// Adding a new lemma should never decrease the revision counter.
#[kani::proof]
#[kani::unwind(5)]
fn proof_frame_revision_monotonic() {
    let mut frame = Frame::new();
    let pred = any_predicate_id();

    let rev_before = frame.predicate_lemma_revision(pred);

    let lemma = Lemma::new(pred, any_simple_expr(), 1);
    frame.add_lemma(lemma);

    let rev_after = frame.predicate_lemma_revision(pred);

    // Revision should never decrease
    assert!(rev_after >= rev_before);
}

/// Proof: MustSummaries deduplicates identical formulas.
#[kani::proof]
#[kani::unwind(5)]
fn proof_must_summaries_deduplicates() {
    let mut summaries = MustSummaries::new();
    let pred = any_predicate_id();
    let level: usize = {
        let l: u8 = kani::any();
        kani::assume(l < 3);
        l as usize
    };
    let formula = any_simple_expr();

    // First add should return true (unless formula is false)
    let first_add = summaries.add(level, pred, formula.clone());

    // Second add of same formula should return false (duplicate)
    let second_add = summaries.add(level, pred, formula);

    assert!(!second_add, "Duplicate formula should be rejected");
}

/// Proof: MustSummaries with true subsumes other formulas.
/// After adding true, subsequent non-true formulas are rejected.
#[kani::proof]
#[kani::unwind(5)]
fn proof_must_summaries_true_subsumes() {
    let mut summaries = MustSummaries::new();
    let pred = any_predicate_id();
    let level: usize = 1;

    // Add true
    let added_true = summaries.add(level, pred, ChcExpr::Bool(true));
    kani::assume(added_true); // Assume first add succeeded

    // Add something else - should be rejected (subsumed by true)
    let added_int = summaries.add(level, pred, ChcExpr::Int(42));

    assert!(!added_int, "Non-true formula should be rejected after true");
}

/// Proof: MustSummaries rejects false formulas.
/// false contributes nothing to a disjunction, so it should be skipped.
#[kani::proof]
fn proof_must_summaries_rejects_false() {
    let mut summaries = MustSummaries::new();
    let pred = any_predicate_id();
    let level: usize = 1;

    let added = summaries.add(level, pred, ChcExpr::Bool(false));

    assert!(!added, "false formula should be rejected");
}

/// Proof: Frame starts empty with zero revision.
#[kani::proof]
fn proof_frame_new_is_empty() {
    let frame = Frame::new();
    let pred = any_predicate_id();

    assert!(frame.lemmas.is_empty());
    assert_eq!(frame.predicate_lemma_revision(pred), 0);
}
