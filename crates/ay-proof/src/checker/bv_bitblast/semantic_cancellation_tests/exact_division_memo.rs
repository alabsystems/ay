// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The proof build's exact-division sweep memo at the strict decision: the
//! first sweep of a divider obligation keeps the whole envelope, another
//! spelling of one whose sweep failed skips only its sweep, and a refusal
//! reached so is a decline for the build, never the store's refusal.

#![cfg(test)]

use super::*;
use crate::checker::bv_bitblast::producer_limits::strict_producer_envelope_id;
use crate::exact_division_sweeps::{self, ExactDivisionSweepMemo};

fn wide_identity() -> (TermStore, Vec<TermId>) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("division-memo-wide", Sort::bitvec(16));
    let equality = terms.mk_app(Symbol::named("="), [x, x], Sort::Bool);
    (terms, vec![equality])
}

/// The semantic decision with a stand-in producer, counting its entries.
fn decide(
    terms: &TermStore,
    clause: &[TermId],
    outcome: fn() -> Result<(), ProofProducingFailure>,
    entered: &mut usize,
) -> Result<(), ProofCheckError> {
    semantic_control::run(&mut |_, _| true, |poll| {
        validate_bv_bitblast_semantics_with_fallback(terms, ProofId(0), clause, poll, |_| {
            *entered += 1;
            outcome()
        })
    })
}

fn rejected() -> Result<(), ProofProducingFailure> {
    Err(ProofProducingFailure::Rejected(
        "proof resource `resolution proof output bytes` exceeds limit 1 (actual 2)".to_owned(),
    ))
}

/// A refusal reached after the build's memo withheld a sweep.
fn withheld() -> Result<(), ProofProducingFailure> {
    let (terms, clause) = in_range(40);
    exact_division_sweeps::exact_division(&terms, &clause, Some(true), 1, || {
        exact_division_sweeps::sweep_failed();
    });
    let skipped = exact_division_sweeps::exact_division(
        &terms,
        &clause,
        Some(true),
        1,
        exact_division_sweeps::skips_sweep,
    );
    assert!(skipped);
    rejected()
}

/// `(bvult (bvurem x 1000003) 1000003)` over a `width`-bit `x`: model-checker-consumer's
/// divider harness obligation.
fn in_range(width: u32) -> (TermStore, Vec<TermId>) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("division-memo-dividend", Sort::bitvec(width));
    let divisor = terms.mk_bitvec(1_000_003.into(), width);
    let remainder = terms.mk_app(Symbol::named("bvurem"), [x, divisor], Sort::bitvec(width));
    let atom = terms.mk_app(Symbol::named("bvult"), [remainder, divisor], Sort::Bool);
    (terms, vec![atom])
}

#[test]
fn a_refusal_after_a_withheld_sweep_is_the_builds_decline_and_never_the_stores() {
    let (terms, clause) = wide_identity();
    let mut entered = 0;
    let mut memo = ExactDivisionSweepMemo::new();
    {
        let _build = memo.begin_build();
        let first = decide(&terms, &clause, withheld, &mut entered);
        assert!(matches!(
            first,
            Err(ProofCheckError::InvalidTheoryLemma { .. })
        ));
        assert_eq!(entered, 1);
        assert!(
            terms
                .strict_bv_semantics_refusal(strict_producer_envelope_id(), &clause)
                .is_none(),
            "a refusal without its own sweep is not the envelope's"
        );
        // The stand-in would accept now; the build declined it already.
        let again = decide(&terms, &clause, || Ok(()), &mut entered);
        assert!(matches!(
            again,
            Err(ProofCheckError::InvalidTheoryLemma { .. })
        ));
        assert_eq!(entered, 1, "declined without entering the producer");
    }
    // Outside the build the clause is decided afresh.
    assert_eq!(decide(&terms, &clause, || Ok(()), &mut entered), Ok(()));
    assert_eq!(entered, 2);
    assert!(terms.strict_bv_semantics_validated(&clause));
}

#[test]
fn a_refusal_with_no_withheld_sweep_is_remembered_in_the_store_as_before() {
    let (terms, clause) = wide_identity();
    let mut entered = 0;
    let mut memo = ExactDivisionSweepMemo::new();
    let _build = memo.begin_build();
    decide(&terms, &clause, rejected, &mut entered).unwrap_err();
    assert!(terms
        .strict_bv_semantics_refusal(strict_producer_envelope_id(), &clause)
        .is_some());
    decide(&terms, &clause, || Ok(()), &mut entered).unwrap_err();
    assert_eq!(entered, 1);
}

/// The real producer on the 32-bit obligation: its exact-division sweep must
/// close (67,222 conflicts, measured 2026-10-14), and under a build's memo it
/// has the whole envelope to do so. A solve-relative allowance of 20,000
/// conflicts declined it, and `ay` published a hole for a lemma main admits.
#[test]
fn a_divider_obligations_first_sweep_keeps_the_whole_envelope_under_a_memo() {
    let (terms, clause) = in_range(32);
    let mut memo = ExactDivisionSweepMemo::new();
    let _build = memo.begin_build();
    Lane::BitBlast
        .run(&terms, &clause, &mut |_, _| true)
        .expect("the exact-division sweep closes within the envelope");
    assert!(terms.strict_bv_semantics_validated(&clause));
    assert_eq!(
        memo.failed_signatures(),
        0,
        "a closed sweep records nothing"
    );
    assert_eq!(memo.skipped_sweeps(), 0);
}

/// The real producer on the 40-bit obligation, which no sweep closes in the
/// envelope: once one spelling's sweep failed, a respelling of the same
/// disjunction still makes its monolithic attempt, which stops on a
/// proof-size cap, and skips the sweep. Nothing reaches the store, the exact
/// repeat is declined without a producer run, and nothing outlives the build.
#[test]
fn another_spelling_of_a_failed_divider_obligation_makes_only_its_monolithic_attempt() {
    let (mut terms, clause) = in_range(40);
    let negated = terms.mk_not_raw(clause[0]);
    let respelled = vec![terms.mk_not_raw(negated)];
    let attempts = || proof_producing_control::ATTEMPTS.with(std::cell::Cell::get);
    let mut memo = ExactDivisionSweepMemo::new();
    {
        let _build = memo.begin_build();
        let envelope = strict_producer_envelope_id();
        exact_division_sweeps::exact_division(&terms, &clause, Some(true), envelope, || {
            exact_division_sweeps::sweep_failed();
        });
        let before = attempts();
        let declined = Lane::BitBlast.run(&terms, &respelled, &mut |_, _| true);
        let Err(ProofCheckError::InvalidTheoryLemma { reason, .. }) = &declined else {
            panic!("expected a declined lemma, got {declined:?}");
        };
        assert!(reason.contains("resolution"), "a proof-size stop: {reason}");
        assert_eq!(attempts(), before + 1);
        assert_eq!(memo.skipped_sweeps(), 1, "the sweep, and only it, withheld");
        assert!(terms
            .strict_bv_semantics_refusal(strict_producer_envelope_id(), &respelled)
            .is_none());
        assert!(Lane::BitBlast
            .run(&terms, &respelled, &mut |_, _| true)
            .is_err());
        assert_eq!(attempts(), before + 1, "the exact repeat, declined");
    }
    assert!(!exact_division_sweeps::declined(
        &terms,
        &respelled,
        strict_producer_envelope_id()
    ));
}
