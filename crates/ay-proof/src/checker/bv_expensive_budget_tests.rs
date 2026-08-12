// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Whole-proof resource regressions for expensive BV semantic checkers.

use ay_core::{Proof, Sort, Symbol, TermStore, TheoryLemmaKind};

use super::*;

fn assert_expensive_cap(error: ProofCheckError) {
    assert!(matches!(
        error,
        ProofCheckError::InvalidTheoryLemma { step, reason }
            if step.0 as usize == MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF
                && reason.contains("whole-proof cap")
    ));
}

#[test]
fn exact_expensive_charge_keeps_bv_bitblast_classification() {
    let mut terms = TermStore::new();
    let wide = terms.mk_var("charged_bv", Sort::bitvec(16));
    let wide_eq = terms.mk_app(Symbol::named("="), vec![wide, wide], Sort::Bool);
    let not_wide_eq = terms.mk_not_raw(wide_eq);
    let narrow = terms.mk_var("bounded_bv", Sort::bitvec(4));
    let narrow_eq = terms.mk_app(Symbol::named("="), vec![narrow, narrow], Sort::Bool);
    let forged_lia = terms.mk_var("forged_lia", Sort::Bool);

    assert!(bv_bitblast_requires_proof_producer(
        &terms,
        &[wide_eq, not_wide_eq]
    ));
    assert!(!bv_bitblast_requires_proof_producer(&terms, &[narrow_eq]));

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "BV",
        vec![wide_eq, not_wide_eq],
        TheoryLemmaKind::BvBitBlast,
    );
    proof.add_theory_lemma_with_kind("BV", vec![narrow_eq], TheoryLemmaKind::BvBitBlast);
    proof.add_theory_lemma_with_kind("BV/LIA", vec![forged_lia], TheoryLemmaKind::BvLiaTautology);

    let charge = validate_expensive_bv_budget(&proof, &terms).expect("three-step preflight fits");
    assert_eq!(
        charge.work,
        usize::try_from(MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA).expect("published work fits usize")
            + usize::try_from(MAX_BV_LIA_TAUTOLOGY_WORK_PER_LEMMA)
                .expect("published work fits usize")
    );
    assert_eq!(
        charge.bytes,
        MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA + MAX_BV_LIA_TAUTOLOGY_BYTES_PER_LEMMA
    );
}

#[test]
fn bv_lia_cap_is_checked_before_non_progress_replay() {
    let mut terms = TermStore::new();
    let forged = terms.mk_var("cap_forged_lia", Sort::Bool);
    let mut proof = Proof::new();
    for _ in 0..=MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF {
        proof.add_theory_lemma_with_kind("BV/LIA", vec![forged], TheoryLemmaKind::BvLiaTautology);
    }

    let error = check_proof_collecting_trust(&proof, &terms)
        .expect_err("the direct strict checker must reject cap+1 before replay");
    assert_expensive_cap(error);
    let error = crate::check_proof_strict(&proof, &terms)
        .expect_err("the quality strict checker must reject cap+1 before replay");
    assert_expensive_cap(error);
}

#[test]
fn mixed_expensive_kinds_share_one_whole_proof_cap() {
    const BITBLAST_COUNT: usize = 4;

    let mut terms = TermStore::new();
    let value = terms.mk_var("mixed_cap_bv", Sort::bitvec(16));
    let equality = terms.mk_app(Symbol::named("="), vec![value, value], Sort::Bool);
    let negated = terms.mk_not_raw(equality);
    let forged_lia = terms.mk_var("mixed_cap_lia", Sort::Bool);
    let mut proof = Proof::new();
    for _ in 0..BITBLAST_COUNT {
        proof.add_theory_lemma_with_kind(
            "BV",
            vec![equality, negated],
            TheoryLemmaKind::BvBitBlast,
        );
    }
    for _ in 0..=(MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF - BITBLAST_COUNT) {
        proof.add_theory_lemma_with_kind(
            "BV/LIA",
            vec![forged_lia],
            TheoryLemmaKind::BvLiaTautology,
        );
    }

    let error = validate_expensive_bv_budget(&proof, &terms)
        .expect_err("the ninth mixed expensive lemma must exceed the shared cap");
    assert_expensive_cap(error);
}

#[test]
fn bv_lia_private_maxima_are_debited_before_replay() {
    let mut terms = TermStore::new();
    let forged = terms.mk_var("metered_forged_lia", Sort::Bool);
    let mut proof = Proof::new();
    for _ in 0..2 {
        proof.add_theory_lemma_with_kind("BV/LIA", vec![forged], TheoryLemmaKind::BvLiaTautology);
    }
    let expected_work = usize::try_from(MAX_BV_LIA_TAUTOLOGY_WORK_PER_LEMMA)
        .expect("published work fits usize")
        * 2;
    let expected_bytes = MAX_BV_LIA_TAUTOLOGY_BYTES_PER_LEMMA * 2;
    let mut proof_scan_debits = 0;
    let mut saw_private_maxima = false;

    let error = crate::authenticate_premise_clauses_strict_with_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        &[],
        &mut |work, bytes| {
            if work == proof.steps.len() && bytes == 0 {
                proof_scan_debits += 1;
            }
            if work == expected_work && bytes == expected_bytes {
                saw_private_maxima = true;
                false
            } else {
                true
            }
        },
    )
    .expect_err("the outer envelope must stop replay after observing its private maxima");

    assert_eq!(error, ProofCheckError::ResourceLimit);
    assert_eq!(proof_scan_debits, 2);
    assert!(saw_private_maxima);
}
