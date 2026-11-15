// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The speculative envelope's memo discipline: a speculative refusal is
//! remembered only under its own identity (the strict checker re-decides),
//! while a strict refusal answers a speculative ask without re-deciding
//! (the speculative caps are component-wise at most the strict ones).

#![cfg(test)]

use super::*;
use crate::checker::bv_bitblast::producer_limits::ProducerEnvelope;

fn wide_identity() -> (TermStore, Vec<TermId>) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("speculative-wide", Sort::bitvec(16));
    let equality = terms.mk_app(Symbol::named("="), [x, x], Sort::Bool);
    (terms, vec![equality])
}

fn decide_env(
    terms: &TermStore,
    clause: &[TermId],
    envelope: ProducerEnvelope,
    outcome: fn() -> Result<(), ProofProducingFailure>,
    entered: &mut usize,
) -> Result<(), ProofCheckError> {
    semantic_control::run(&mut |_, _| true, |poll| {
        validate_bv_bitblast_semantics_with_fallback_envelope(
            terms,
            ProofId(0),
            clause,
            poll,
            envelope,
            |_| {
                *entered += 1;
                outcome()
            },
        )
    })
}

fn counted() -> Result<(), ProofProducingFailure> {
    Err(ProofProducingFailure::Rejected(
        "proof resource `resolution conflicts` exceeds limit 1 (actual 2)".to_owned(),
    ))
}

#[test]
fn speculative_refusal_is_invisible_to_the_strict_envelope() {
    let (terms, clause) = wide_identity();
    let mut entered = 0;
    let first = decide_env(
        &terms,
        &clause,
        ProducerEnvelope::Speculative,
        counted,
        &mut entered,
    );
    assert!(matches!(
        first,
        Err(ProofCheckError::InvalidTheoryLemma { .. })
    ));
    assert_eq!(entered, 1);
    assert!(
        terms
            .strict_bv_semantics_refusal(ProducerEnvelope::Speculative.id(), &clause)
            .is_some(),
        "the speculative refusal is remembered under its own identity"
    );
    assert!(
        terms
            .strict_bv_semantics_refusal(ProducerEnvelope::Strict.id(), &clause)
            .is_none(),
        "a speculative refusal must never answer for the strict checker"
    );
    // The strict envelope decides for itself: the producer runs again, and
    // its acceptance is recorded as usual.
    let strict = decide_env(
        &terms,
        &clause,
        ProducerEnvelope::Strict,
        || Ok(()),
        &mut entered,
    );
    assert_eq!(strict, Ok(()));
    assert_eq!(entered, 2, "the strict ask re-ran the producer");
    assert!(terms.strict_bv_semantics_validated(&clause));
}

#[test]
fn strict_refusal_answers_a_speculative_ask_without_re_deciding() {
    let (terms, clause) = wide_identity();
    let mut entered = 0;
    let first = decide_env(
        &terms,
        &clause,
        ProducerEnvelope::Strict,
        counted,
        &mut entered,
    );
    assert!(first.is_err());
    assert_eq!(entered, 1);
    // The speculative caps are component-wise at most the strict ones, so
    // the smaller envelope refuses whatever the larger refused: the
    // remembered strict refusal is repeated and the producer stays idle,
    // even though the stand-in would accept now.
    let again = decide_env(
        &terms,
        &clause,
        ProducerEnvelope::Speculative,
        || Ok(()),
        &mut entered,
    );
    assert_eq!(again, first, "the same refusal, word for word");
    assert_eq!(entered, 1, "a remembered strict refusal is never re-run");
}

#[test]
fn speculative_acceptance_is_a_strict_acceptance() {
    let (terms, clause) = wide_identity();
    let mut entered = 0;
    let first = decide_env(
        &terms,
        &clause,
        ProducerEnvelope::Speculative,
        || Ok(()),
        &mut entered,
    );
    assert_eq!(first, Ok(()));
    assert!(
        terms.strict_bv_semantics_validated(&clause),
        "an acceptance is a semantic fact, recorded envelope-free"
    );
    // A later strict ask is answered by the acceptance memo.
    let again = decide_env(
        &terms,
        &clause,
        ProducerEnvelope::Strict,
        counted,
        &mut entered,
    );
    assert_eq!(again, Ok(()));
    assert_eq!(entered, 1);
}

#[test]
fn a_speculative_withheld_decline_does_not_answer_a_strict_decision() {
    use crate::exact_division_sweeps::{self, ExactDivisionSweepMemo};

    let mut terms = TermStore::new();
    let x = terms.mk_var("speculative-withheld-dividend", Sort::bitvec(32));
    let divisor = terms.mk_bitvec(1_000_003.into(), 32);
    let remainder = terms.mk_app(Symbol::named("bvurem"), [x, divisor], Sort::bitvec(32));
    let atom = terms.mk_app(Symbol::named("bvult"), [remainder, divisor], Sort::Bool);
    let clause = [atom];
    let mut memo = ExactDivisionSweepMemo::new();
    let _build = memo.begin_build();

    // Prime the actual failed-signature memo under the speculative envelope.
    exact_division_sweeps::exact_division(
        &terms,
        &clause,
        Some(true),
        ProducerEnvelope::Speculative.id(),
        || {
            assert!(!exact_division_sweeps::skips_sweep());
            assert!(exact_division_sweeps::remembers_sweep());
            exact_division_sweeps::sweep_failed();
        },
    );
    assert_eq!(memo.failed_signatures(), 1);

    let mut entered = 0;
    let speculative = semantic_control::run(&mut |_, _| true, |poll| {
        validate_bv_bitblast_semantics_with_fallback_envelope(
            &terms,
            ProofId(0),
            &clause,
            poll,
            ProducerEnvelope::Speculative,
            |_| {
                entered += 1;
                exact_division_sweeps::exact_division(
                    &terms,
                    &clause,
                    Some(true),
                    ProducerEnvelope::Speculative.id(),
                    || {
                        assert!(exact_division_sweeps::skips_sweep());
                        Err(ProofProducingFailure::Rejected(
                            "withheld speculative sweep".into(),
                        ))
                    },
                )
            },
        )
    });
    assert!(matches!(
        speculative,
        Err(ProofCheckError::InvalidTheoryLemma { .. })
    ));
    assert_eq!(entered, 1);
    assert_eq!(memo.skipped_sweeps(), 1);
    assert!(
        terms
            .strict_bv_semantics_refusal(ProducerEnvelope::Speculative.id(), &clause)
            .is_none(),
        "a withheld sweep must not become a counted-envelope refusal"
    );
    assert!(terms
        .strict_bv_semantics_refusal(ProducerEnvelope::Strict.id(), &clause)
        .is_none());

    // The strict decision must reach its own callback; its rejection is
    // deliberately distinct, so this test never supplies proof acceptance.
    let strict = semantic_control::run(&mut |_, _| true, |poll| {
        validate_bv_bitblast_semantics_with_fallback_envelope(
            &terms,
            ProofId(0),
            &clause,
            poll,
            ProducerEnvelope::Strict,
            |_| {
                entered += 1;
                Err(ProofProducingFailure::Rejected(
                    "fresh strict decision".into(),
                ))
            },
        )
    });
    assert_eq!(
        entered, 2,
        "a speculative withheld decline must not suppress strict work"
    );
    assert!(
        matches!(strict, Err(ProofCheckError::InvalidTheoryLemma { reason, .. })
        if reason.contains("fresh strict decision"))
    );
}
