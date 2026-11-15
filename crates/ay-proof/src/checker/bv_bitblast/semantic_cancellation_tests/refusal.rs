// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The refusal half of the strict BV semantic memo: a counted refusal is
//! repeated without re-running the producer; a stop never is.

#![cfg(test)]

use super::*;
use crate::checker::bv_bitblast::producer_limits::strict_producer_envelope_id;

fn wide_identity() -> (TermStore, Vec<TermId>) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("refusal-wide", Sort::bitvec(16));
    let equality = terms.mk_app(Symbol::named("="), [x, x], Sort::Bool);
    (terms, vec![equality])
}

/// Run the semantic decision once with a scripted fallback, counting how many
/// times that fallback (the producer's stand-in) was entered.
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

fn counted() -> Result<(), ProofProducingFailure> {
    Err(ProofProducingFailure::Rejected(
        "proof resource `resolution conflicts` exceeds limit 1 (actual 2)".to_owned(),
    ))
}

fn hang_guard() -> Result<(), ProofProducingFailure> {
    Err(ProofProducingFailure::Stopped(
        "proof resource `resolution proof deadline` exceeds limit 0 (actual 1)".to_owned(),
    ))
}

fn cancelled() -> Result<(), ProofProducingFailure> {
    Err(ProofProducingFailure::Cancelled)
}

#[test]
fn a_counted_refusal_is_repeated_without_running_the_producer_again() {
    let (terms, clause) = wide_identity();
    let mut entered = 0;
    let first = decide(&terms, &clause, counted, &mut entered);
    assert!(matches!(
        first,
        Err(ProofCheckError::InvalidTheoryLemma { .. })
    ));
    assert_eq!(entered, 1);
    for _ in 0..3 {
        // The stand-in would ACCEPT now; the remembered refusal must win, and
        // the producer must not be entered at all.
        let again = decide(&terms, &clause, || Ok(()), &mut entered);
        assert_eq!(again, first, "the same refusal, word for word");
    }
    assert_eq!(
        entered, 1,
        "a remembered refusal never re-runs the producer"
    );
    assert!(!terms.strict_bv_semantics_validated(&clause));
    assert!(terms
        .strict_bv_semantics_refusal(strict_producer_envelope_id(), &clause)
        .is_some());
}

#[test]
fn stops_are_never_remembered_and_are_decided_again() {
    for (stop, expected) in [
        (hang_guard as fn() -> _, "hang guard"),
        (cancelled as fn() -> _, "cancellation"),
    ] {
        let (terms, clause) = wide_identity();
        let mut entered = 0;
        let first = decide(&terms, &clause, stop, &mut entered);
        let second = decide(&terms, &clause, stop, &mut entered);
        assert!(
            first.is_err() && second.is_err(),
            "{expected}: a stop still fails closed"
        );
        assert_eq!(
            entered, 2,
            "{expected}: a stop is not a verdict, so it is re-decided"
        );
        assert!(
            terms
                .strict_bv_semantics_refusal(strict_producer_envelope_id(), &clause)
                .is_none(),
            "{expected}: never recorded"
        );
        // After the stop, a completed decision is still reachable.
        assert_eq!(decide(&terms, &clause, || Ok(()), &mut entered), Ok(()));
        assert!(terms.strict_bv_semantics_validated(&clause));
    }
    let (terms, clause) = wide_identity();
    assert_eq!(
        decide(&terms, &clause, cancelled, &mut 0),
        Err(ProofCheckError::ResourceLimit),
        "a cancellation keeps its own error, not a lemma rejection"
    );
}

#[test]
fn a_refusal_is_keyed_by_store_clause_and_envelope() {
    let (mut terms, clause) = wide_identity();
    let mut entered = 0;
    decide(&terms, &clause, counted, &mut entered).unwrap_err();
    let envelope = strict_producer_envelope_id();
    assert!(terms
        .strict_bv_semantics_refusal(envelope, &clause)
        .is_some());
    // A different counted envelope never reads it.
    assert!(terms
        .strict_bv_semantics_refusal(envelope ^ 1, &clause)
        .is_none());
    // A different clause in the same store is decided on its own.
    let y = terms.mk_var("refusal-other", Sort::bitvec(16));
    let other = terms.mk_app(Symbol::named("="), [y, y], Sort::Bool);
    assert_eq!(decide(&terms, &[other], || Ok(()), &mut entered), Ok(()));
    assert_eq!(entered, 2);
    // A copy has the same term at every TermId: it keeps the refusal (and
    // never re-runs the producer for it), but starts with no acceptance.
    let copy = terms.clone();
    assert!(copy
        .strict_bv_semantics_refusal(envelope, &clause)
        .is_some());
    assert!(!copy.strict_bv_semantics_validated(&[other]));
    decide(&copy, &clause, || Ok(()), &mut entered).unwrap_err();
    assert_eq!(entered, 2);
    // A store built independently, even over the same terms, shares nothing.
    let (fresh, fresh_clause) = wide_identity();
    assert_eq!(fresh_clause, clause);
    assert_eq!(
        decide(&fresh, &fresh_clause, || Ok(()), &mut entered),
        Ok(())
    );
    assert_eq!(entered, 3);
}

/// A refusal is kept exactly while its clause still names the same terms.
#[test]
fn a_refusal_follows_its_terms_through_rollback_and_compaction() {
    let envelope = strict_producer_envelope_id();
    let mut terms = TermStore::new();
    // Unnamed and unrooted: compaction reclaims it, so later ids move down.
    let _garbage = terms.mk_bitvec(5.into(), 8);
    let x = terms.mk_var("refusal-moved", Sort::bitvec(16));
    let clause = vec![terms.mk_app(Symbol::named("="), [x, x], Sort::Bool)];
    let mut entered = 0;
    decide(&terms, &clause, counted, &mut entered).unwrap_err();
    // A rollback that keeps the clause's terms keeps its refusal ...
    let after_clause = terms.rollback_checkpoint();
    let _scratch = terms.mk_var("refusal-scratch", Sort::bitvec(16));
    terms.rollback_to(after_clause);
    assert!(terms
        .strict_bv_semantics_refusal(envelope, &clause)
        .is_some());
    // ... and a compaction relabels it to the clause's new ids.
    let remap = terms.mark_and_compact(&clause);
    let moved: Vec<TermId> = clause.iter().map(|&id| remap.get(id).unwrap()).collect();
    assert_ne!(
        moved, clause,
        "precondition: the compaction moved the clause"
    );
    assert!(terms
        .strict_bv_semantics_refusal(envelope, &moved)
        .is_some());
    decide(&terms, &moved, || Ok(()), &mut entered).unwrap_err();
    assert_eq!(
        entered, 1,
        "the relabelled refusal is still the producer's answer"
    );
    // A compaction that reclaims the clause drops it.
    terms.mark_and_compact(&[]);
    assert!(terms
        .strict_bv_semantics_refusal(envelope, &moved)
        .is_none());
    // A rollback below the clause's terms drops it: those ids can be re-minted.
    let mut terms = TermStore::new();
    let before_clause = terms.rollback_checkpoint();
    let x = terms.mk_var("refusal-reminted", Sort::bitvec(16));
    let clause = vec![terms.mk_app(Symbol::named("="), [x, x], Sort::Bool)];
    decide(&terms, &clause, counted, &mut entered).unwrap_err();
    terms.rollback_to(before_clause);
    assert!(terms
        .strict_bv_semantics_refusal(envelope, &clause)
        .is_none());
}

/// End to end through the real producer: a counted refusal (the pre-search
/// gate budget) runs the producer once, and every repetition answers from
/// the memo with the identical rejection.
#[test]
fn the_real_producer_runs_once_for_a_repeated_counted_refusal() {
    let mut terms = TermStore::new();
    let bv = terms.mk_var("refusal-mul", Sort::bitvec(64));
    let mut product = bv;
    // Ten 64-bit multipliers exceed the 100,000-gate bound before any search.
    for _ in 0..10 {
        product = terms.mk_app(Symbol::named("bvmul"), [product, bv], Sort::bitvec(64));
    }
    let eq = terms.mk_app(Symbol::named("="), [product, product], Sort::Bool);
    let attempts = || proof_producing_control::ATTEMPTS.with(std::cell::Cell::get);
    let before = attempts();
    let first = Lane::BitBlast.run(&terms, &[eq], &mut |_, _| true);
    let Err(ProofCheckError::InvalidTheoryLemma { reason, .. }) = &first else {
        panic!("expected a rejected lemma, got {first:?}");
    };
    assert!(reason.contains("estimated bit-blast gates"), "{reason}");
    assert_eq!(attempts(), before + 1);
    for _ in 0..4 {
        assert_eq!(Lane::BitBlast.run(&terms, &[eq], &mut |_, _| true), first);
    }
    assert_eq!(attempts(), before + 1, "four repetitions, no producer run");
}

/// A counted refusal the producer returns once the caller has stopped is the
/// stop, not the envelope's verdict: past its monolithic attempt's counted
/// cap the producer sweeps, and a sweep the caller's stop ends reports that
/// cap. It keeps the cancellation's own error and is never remembered, so the
/// clause is decided again. The twin: the same refusal with the caller still
/// going is remembered.
#[test]
fn a_refusal_returned_after_the_callers_stop_is_not_remembered() {
    let (terms, clause) = wide_identity();
    let stopped = std::cell::Cell::new(false);
    let result = semantic_control::run(&mut |_, _| !stopped.get(), |poll| {
        validate_bv_bitblast_semantics_with_fallback(&terms, ProofId(0), &clause, poll, |_| {
            stopped.set(true);
            counted()
        })
    });
    assert_eq!(result, Err(ProofCheckError::ResourceLimit));
    let envelope = strict_producer_envelope_id();
    assert!(terms
        .strict_bv_semantics_refusal(envelope, &clause)
        .is_none());
    let mut entered = 0;
    let decided = decide(&terms, &clause, counted, &mut entered);
    assert!(matches!(
        decided,
        Err(ProofCheckError::InvalidTheoryLemma { .. })
    ));
    assert_eq!(entered, 1, "the stopped refusal was decided again");
    assert!(terms
        .strict_bv_semantics_refusal(envelope, &clause)
        .is_some());
}
