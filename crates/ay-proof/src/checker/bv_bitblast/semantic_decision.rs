// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The SEMANTIC half of `bv_bitblast` validation — exhaustive bounded
//! evaluation, falling back to the bounded bit-blast + LRAT proof producer and
//! its replay — memoized per `(store, clause)` in both directions.
//!
//! PERF. Proof finalization runs `check_proof_strict*` as an atomic revert gate
//! after each of ~30 individual surgery passes, and the proof classifier asks
//! `recognize_bv_bitblast` about the same clauses, so ONE `BvBitBlast` lemma is
//! re-decided many times per solve on an unchanged clause in an unchanged
//! store. MEASURED at b0a836719b over the 28 `shl_is_mul_by_pow2` queries: 226
//! entries into this decision procedure for 28 distinct decisions, and 41.3 s
//! of the 53.2 s spent here re-decided a clause already accepted. A lemma the
//! counted envelope REFUSES is re-decided just as often, and each repetition
//! pays the whole counted exhaustion; that is why refusals are memoized too.
//!
//! Nothing is checked less, and nothing is ever accepted from the memo that
//! was not accepted by a complete decision:
//! * the structural schema checks in [`super::validate_bv_bitblast`] (Boolean
//!   sorts, BV content, gate-annotation agreement) run on EVERY call and are
//!   never memoized — which is also why neither memo key needs the gate
//!   annotation;
//! * an acceptance is recorded only for a COMPLETED, ACCEPTING decision, keyed
//!   by the exact clause: "this clause holds under every assignment" is a
//!   store-and-clause-determined fact, so repeating it cannot change the
//!   answer;
//! * a refusal is recorded only when the producer's COUNTED envelope refused
//!   the clause ([`ProofProducingFailure::Rejected`]), keyed by the exact
//!   clause AND the envelope's identity ([`strict_producer_envelope_id`]).
//!   Replaying it can only make a check FAIL. A caller cancellation (which
//!   includes the caller's solve deadline and its progress budget) and a
//!   hang-guard stop ([`ProofProducingFailure::Stopped`]) end one attempt,
//!   not the clause's question, and are never recorded;
//! * `TermStore` clears both tables on the two operations that can change
//!   what a `TermId` means (`rollback_to`, `mark_and_compact`), and a cloned
//!   store starts empty;
//! * the whole-proof [`super::MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF`] budget is a
//!   structural count over the proof's steps, so it is unaffected;
//! * a refusal reached after the proof build's memo withheld an
//!   exact-division sweep (`crate::exact_division_sweeps`) is not the counted
//!   envelope's verdict on the clause: it is never recorded here, only in
//!   that memo, while it is installed.

use super::producer_limits::ProducerEnvelope;
use super::{
    bounded_eval, proof_producing_control, semantic_control, wiring, ProofCheckError, ProofId,
    ProofProducingFailure, TermId, TermStore,
};

pub(super) fn validate_bv_bitblast_semantics(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    poll: semantic_control::Poll<'_>,
) -> Result<(), ProofCheckError> {
    validate_bv_bitblast_semantics_with_fallback_envelope(
        terms,
        step_id,
        clause,
        poll,
        ProducerEnvelope::Strict,
        |poll| proof_producing_control::validate(terms, clause, poll),
    )
}

/// The speculative-envelope twin of [`validate_bv_bitblast_semantics`] for
/// capability probes (`super::recognize_bv_bitblast_speculative_with_progress`):
/// same structural checks, wiring decision and bounded evaluation; only the
/// proof-producing fallback runs under the reduced counted envelope. A
/// refusal remembered under the STRICT envelope is replayed without
/// re-deciding (the speculative caps are component-wise at most the strict
/// ones, so the smaller envelope refuses whatever the larger refused); a
/// speculative refusal is remembered only under the speculative identity and
/// never answers for the strict checker.
pub(super) fn validate_bv_bitblast_semantics_speculative(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    poll: semantic_control::Poll<'_>,
) -> Result<(), ProofCheckError> {
    validate_bv_bitblast_semantics_with_fallback_envelope(
        terms,
        step_id,
        clause,
        poll,
        ProducerEnvelope::Speculative,
        |poll| {
            proof_producing_control::validate_with_envelope(
                terms,
                clause,
                poll,
                ProducerEnvelope::Speculative,
            )
        },
    )
}

/// The private fallback seam lets cancellation controls prove no fallback was
/// entered without running a solver. Production always supplies the unchanged
/// proof-producing validator with the same caller control and hang guard.
pub(super) fn validate_bv_bitblast_semantics_with_fallback(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    poll: semantic_control::Poll<'_>,
    fallback: impl FnOnce(semantic_control::Poll<'_>) -> Result<(), ProofProducingFailure>,
) -> Result<(), ProofCheckError> {
    validate_bv_bitblast_semantics_with_fallback_envelope(
        terms,
        step_id,
        clause,
        poll,
        ProducerEnvelope::Strict,
        fallback,
    )
}

pub(super) fn validate_bv_bitblast_semantics_with_fallback_envelope(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    poll: semantic_control::Poll<'_>,
    envelope: ProducerEnvelope,
    fallback: impl FnOnce(semantic_control::Poll<'_>) -> Result<(), ProofProducingFailure>,
) -> Result<(), ProofCheckError> {
    poll()?;
    if terms.strict_bv_semantics_validated(clause) {
        poll()?;
        return Ok(());
    }
    poll()?;
    // A unit equality that holds by wiring alone is decided exactly and
    // symbolically (`wiring.rs`); anything else goes on to the bounded and
    // proof-producing checks unchanged.
    if wiring::holds_by_wiring(terms, clause) {
        poll()?;
        terms.record_strict_bv_semantics_validated(clause);
        return Ok(());
    }
    poll()?;
    let bounded_error = match bounded_eval::validate(terms, step_id, clause, poll) {
        Ok(()) => {
            // No acceptance is cached until the final success poll accepts.
            poll()?;
            terms.record_strict_bv_semantics_validated(clause);
            return Ok(());
        }
        Err(ProofCheckError::ResourceLimit) => return Err(ProofCheckError::ResourceLimit),
        Err(bounded_error) => bounded_error,
    };
    poll()?;
    let rejected = |proof_error: &str| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: format!(
            "bv_bitblast semantic checks failed: bounded checker: {bounded_error}; \
             proof-producing checker: {proof_error}"
        ),
    };
    // A refusal remembered under the STRICT envelope answers for both
    // envelopes (the speculative caps are component-wise at most the strict
    // ones); a speculative refusal answers only for the speculative one.
    if let Some(proof_error) =
        terms.strict_bv_semantics_refusal(ProducerEnvelope::Strict.id(), clause)
    {
        // The strict counted envelope already refused this exact clause in
        // this store. Repeat its refusal; never re-run its exhaustion.
        return Err(rejected(&proof_error));
    }
    if envelope == ProducerEnvelope::Speculative {
        if let Some(proof_error) = terms.strict_bv_semantics_refusal(envelope.id(), clause) {
            return Err(rejected(&proof_error));
        }
    }
    if crate::exact_division_sweeps::declined(terms, clause, envelope.id()) {
        // This proof build already refused this exact clause with a sweep
        // withheld under this envelope, and its memo withholds that sweep still.
        return Err(rejected(crate::exact_division_sweeps::DECLINED));
    }
    let (outcome, withheld) = crate::exact_division_sweeps::deciding(|| fallback(&mut *poll));
    match outcome {
        Ok(()) => {
            poll()?;
            terms.record_strict_bv_semantics_validated(clause);
            Ok(())
        }
        Err(ProofProducingFailure::Cancelled) => Err(ProofCheckError::ResourceLimit),
        Err(ProofProducingFailure::Rejected(proof_error)) if withheld => {
            // The build's memo withheld an exact-division sweep another
            // spelling already made: a decline for this build, not the
            // counted envelope's refusal. Remembered in that memo alone, and
            // only once a poll confirms the caller is still going.
            poll()?;
            crate::exact_division_sweeps::record_decline(terms, clause, envelope.id());
            Err(rejected(&proof_error))
        }
        Err(ProofProducingFailure::Rejected(proof_error)) => {
            // A caller's stop can come back as a counted refusal: past the
            // monolithic attempt's counted cap the producer sweeps
            // (`bv_blast_solver/sweep.rs`, `after_counted_cap`), and a sweep
            // the stop ends reports that cap. Measured on the guarded
            // collapse's `(bvult (bvmul P12 P7) (bvmul Q7 Q12))` under a 20 s
            // query timeout: the deadline fired inside that sweep and the
            // clause was remembered as refused by its output-bytes cap. So no
            // refusal is remembered until a poll confirms the caller is still
            // going, as no acceptance is; a stopped one is the cancellation.
            poll()?;
            terms.record_strict_bv_semantics_refusal(envelope.id(), clause, &proof_error);
            Err(rejected(&proof_error))
        }
        Err(ProofProducingFailure::Stopped(proof_error)) => Err(rejected(&proof_error)),
    }
}
