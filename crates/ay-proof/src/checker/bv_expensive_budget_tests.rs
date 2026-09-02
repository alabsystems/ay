// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Whole-proof resource regressions for expensive BV semantic checkers.

use ay_core::{AletheRule, Proof, ProofStep, Sort, Symbol, TermId, TermStore, TheoryLemmaKind};
use num_bigint::BigInt;

use super::*;

fn assert_expensive_cap(error: ProofCheckError) {
    assert!(matches!(
        error,
        ProofCheckError::InvalidTheoryLemma { step, reason }
            if step.0 as usize == MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF
                && reason.contains("whole-proof cap")
    ));
}

fn closed_wide_evaluate_step(terms: &mut TermStore) -> ProofStep {
    let zero64 = terms.mk_bitvec(BigInt::from(0_u8), 64);
    let extended = terms.mk_app(
        Symbol::indexed("zero_extend", vec![64]),
        [zero64],
        Sort::bitvec(128),
    );
    let eight = terms.mk_bitvec(BigInt::from(8_u8), 128);
    let product = terms.mk_app(Symbol::named("bvmul"), [extended, eight], Sort::bitvec(128));
    let high = terms.mk_app(
        Symbol::indexed("extract", vec![127, 64]),
        [product],
        Sort::bitvec(64),
    );
    let equality = terms.mk_app(Symbol::named("="), [high, zero64], Sort::Bool);
    ProofStep::Step {
        rule: AletheRule::Evaluate,
        clause: vec![equality],
        premises: Vec::new(),
        args: Vec::new(),
    }
}

fn legacy_concat_evaluate_step(terms: &mut TermStore) -> ProofStep {
    let high = terms.mk_bitvec(BigInt::from(1_u8), 8);
    let low = terms.mk_bitvec(BigInt::from(2_u8), 8);
    let concat = terms.mk_app(Symbol::named("concat"), [high, low], Sort::bitvec(16));
    let expected = terms.mk_bitvec(BigInt::from(0x0102_u16), 16);
    let equality = terms.mk_app(Symbol::named("="), [concat, expected], Sort::Bool);
    ProofStep::Step {
        rule: AletheRule::Evaluate,
        clause: vec![equality],
        premises: Vec::new(),
        args: Vec::new(),
    }
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
fn ground_bv_constants_use_bounded_evaluation_without_expensive_precharge() {
    for width in [8, 64] {
        let mut terms = TermStore::new();
        let five = terms.mk_bitvec(BigInt::from(5), width);
        let ten = terms.mk_bitvec(BigInt::from(10), width);
        let equality = terms.mk_app(Symbol::named("="), [five, ten], Sort::Bool);
        let disequality = terms.mk_not_raw(equality);
        let clause = [disequality];

        assert!(recognize_bv_bitblast(&terms, &clause));
        assert!(
            !bv_bitblast_requires_proof_producer(&terms, &clause),
            "closed width-{width} constants require one evaluation, not a SAT proof"
        );
        let mut proof = Proof::new();
        let assume = proof.add_assume(equality, None);
        let theorem =
            proof.add_theory_lemma_with_kind("BV", clause.to_vec(), TheoryLemmaKind::BvBitBlast);
        proof.add_resolution(Vec::new(), equality, assume, theorem);
        crate::check_proof_strict(&proof, &terms)
            .expect("ground constant disequality must replay without the expensive precharge");
    }
}

#[test]
fn closed_wide_evaluate_shares_the_expensive_cap_but_legacy_concat_does_not() {
    let mut terms = TermStore::new();
    let closed = closed_wide_evaluate_step(&mut terms);
    let mut proof = Proof::new();
    for _ in 0..MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF {
        proof.add_step(closed.clone());
    }
    let charge = validate_expensive_bv_budget(&proof, &terms)
        .expect("the exact closed-BV structural boundary must remain admitted");
    assert_eq!(
        charge.work,
        usize::try_from(closed_bv_evaluate::MAX_CLOSED_BV_EVALUATE_WORK_PER_LEMMA)
            .expect("published work fits usize")
            * MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF
    );
    assert_eq!(
        charge.bytes,
        closed_bv_evaluate::MAX_CLOSED_BV_EVALUATE_BYTES_PER_LEMMA
            * MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF
    );

    proof.add_step(closed);
    let error = validate_expensive_bv_budget(&proof, &terms)
        .expect_err("the ninth closed-BV evaluation must exceed the shared cap");
    assert_expensive_cap(error);

    let legacy = legacy_concat_evaluate_step(&mut terms);
    let mut legacy_proof = Proof::new();
    for _ in 0..=MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF {
        legacy_proof.add_step(legacy.clone());
    }
    let legacy_charge = validate_expensive_bv_budget(&legacy_proof, &terms)
        .expect("legacy <=64-bit concat evaluation is outside the expensive census");
    assert_eq!(legacy_charge.work, 0);
    assert_eq!(legacy_charge.bytes, 0);
}

#[test]
fn symbolic_wide_and_unsupported_ground_bv_stay_expensive_and_fail_closed() {
    let mut terms = TermStore::new();
    let symbolic = terms.mk_var("symbolic_width_8", Sort::bitvec(8));
    let symbolic_reflexive = terms.mk_app(Symbol::named("="), [symbolic, symbolic], Sort::Bool);
    assert!(bv_bitblast_requires_proof_producer(
        &terms,
        &[symbolic_reflexive]
    ));

    let wide_zero = terms.mk_bitvec(BigInt::from(0), 65);
    let wide_one = terms.mk_bitvec(BigInt::from(1), 65);
    let wide_equality = terms.mk_app(Symbol::named("="), [wide_zero, wide_one], Sort::Bool);
    let wide_disequality = terms.mk_not_raw(wide_equality);
    assert!(bv_bitblast_requires_proof_producer(
        &terms,
        &[wide_disequality]
    ));

    let unsupported = terms.mk_app(
        Symbol::named("unsupported_ground_bv"),
        Vec::<TermId>::new(),
        Sort::bitvec(8),
    );
    let unsupported_reflexive =
        terms.mk_app(Symbol::named("="), [unsupported, unsupported], Sort::Bool);
    assert!(bv_bitblast_requires_proof_producer(
        &terms,
        &[unsupported_reflexive]
    ));
    let mut forged = Proof::new();
    forged.add_theory_lemma_with_kind(
        "BV",
        vec![unsupported_reflexive],
        TheoryLemmaKind::BvBitBlast,
    );
    assert!(crate::check_proof_strict(&forged, &terms).is_err());
}

#[test]
fn published_single_lemma_reserve_covers_each_expensive_kind() {
    const {
        assert!(MAX_EXPENSIVE_BV_WORK_PER_LEMMA >= MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA);
        assert!(MAX_EXPENSIVE_BV_WORK_PER_LEMMA >= MAX_BV_LIA_TAUTOLOGY_WORK_PER_LEMMA);
        assert!(
            MAX_EXPENSIVE_BV_WORK_PER_LEMMA
                >= closed_bv_evaluate::MAX_CLOSED_BV_EVALUATE_WORK_PER_LEMMA
        );
        assert!(MAX_EXPENSIVE_BV_BYTES_PER_LEMMA >= MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA);
        assert!(MAX_EXPENSIVE_BV_BYTES_PER_LEMMA >= MAX_BV_LIA_TAUTOLOGY_BYTES_PER_LEMMA);
        assert!(
            MAX_EXPENSIVE_BV_BYTES_PER_LEMMA
                >= closed_bv_evaluate::MAX_CLOSED_BV_EVALUATE_BYTES_PER_LEMMA
        );
    }
}

#[test]
fn structural_count_cap_does_not_promise_aggregate_admission() {
    let mut terms = TermStore::new();
    let value = terms.mk_var("two_charged_bv", Sort::bitvec(16));
    let equality = terms.mk_app(Symbol::named("="), vec![value, value], Sort::Bool);
    let negated = terms.mk_not_raw(equality);
    let mut proof = Proof::new();
    for _ in 0..2 {
        proof.add_theory_lemma_with_kind(
            "BV",
            vec![equality, negated],
            TheoryLemmaKind::BvBitBlast,
        );
    }

    let charge = validate_expensive_bv_budget(&proof, &terms)
        .expect("two expensive lemmas remain below the structural count ceiling");
    const {
        assert!(2 <= MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF);
    }
    assert!(charge.bytes > MAX_EXPENSIVE_BV_BYTES_PER_LEMMA);
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
