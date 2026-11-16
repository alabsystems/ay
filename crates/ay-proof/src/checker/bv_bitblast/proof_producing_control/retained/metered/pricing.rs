// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Planner charges precede source walks/decoding on the original owner.
//! Complete scalar/sparse cost scans are eligibility only: no producer,
//! source fact, skipped reader, refund, replacement owner or new deadline.

use super::*;
use crate::bv_blast_solver::retained::pricing::{self as expression_price, ReplayPrice};
use crate::checker::ProofCheckError;
use ay_core::{ProofId, ProofStep, Sort, Symbol, TermData, TheoryLemmaKind};

mod array_free;
mod sparse;
type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;

#[expect(
    clippy::too_many_arguments,
    reason = "live step, backing capacity, three independent limit owners, and progress stay explicit"
)]
pub(crate) fn price_clause(
    terms: &TermStore,
    step_id: ProofId,
    step: &ProofStep,
    bytes: &[u8],
    backing_capacity: usize,
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    wire: &WireLimits,
    progress: Progress<'_>,
) -> Result<Option<ReplayPrice>, ProofCheckError> {
    let (clause, gate) = match step {
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::BvBitBlast,
            clause,
            ..
        } => (clause.as_slice(), None),
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::BvBitBlastGate { gate_type, width },
            clause,
            ..
        } => (clause.as_slice(), Some((*gate_type, *width))),
        _ => return Ok(None),
    };
    let end = proof
        .resolution
        .deadline
        .ok_or(ProofCheckError::ResourceLimit)?
        .min(wire.deadline);
    let scalar = array_free::certify(terms, clause, progress)?;
    let native = if scalar {
        None
    } else if matches!(
        step,
        ProofStep::TheoryLemma {
            farkas: None,
            lia: None,
            ..
        }
    ) {
        sparse::plan(terms, clause, proof, progress)?
    } else {
        None
    };
    // A complete typed source licenses only bounded original route matching.
    // Unsupported/incomplete/expensive sources retain old fees.
    if !scalar && native.is_none() {
        return Ok(None);
    }
    // Preserve exact legacy malformed-source/gate error classification.
    // Actual strict replay repeats this independently; no check is replaced.
    crate::checker::bv_bitblast::validate_bv_bitblast_structure_with_progress(
        terms,
        step_id,
        clause,
        gate,
        &mut |_, _| progress(32, 0),
    )?;
    prepay_source_plan(bytes.len(), backing_capacity, proof, native, progress)?;
    run_price(
        terms,
        clause,
        step_id,
        bytes,
        backing_capacity,
        proof,
        gates,
        wire,
        native,
        end,
        progress,
    )
}

#[expect(
    clippy::too_many_arguments,
    reason = "live clause, wire, native price, deadline, limit owners, and progress stay explicit"
)]
fn run_price(
    terms: &TermStore,
    clause: &[TermId],
    step_id: ProofId,
    bytes: &[u8],
    backing_capacity: usize,
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    wire: &WireLimits,
    native: Option<sparse::Cost>,
    end: Instant,
    progress: Progress<'_>,
) -> Result<Option<ReplayPrice>, ProofCheckError> {
    let mut poll = || progress(32, 0);
    Control::new(end, &mut poll)
        .run_typed(|control| {
            // U includes the prepaid original recognizer envelope. Its result
            // is never a source fact: conditional readers/prerequisites remain
            // unchanged and keep old fees. Do not lower a conditional payload
            // through the ordinary numeric pricing path.
            if native.is_some() && !matches!(source_route(terms, clause, control)?, SourceRoute::Ordinary) {
                return Ok(None);
            }
            with_lowered_clause(terms, clause, control, |source, truth, control| {
                expression_price::price(source, truth, bytes, backing_capacity, proof, gates, wire,
                    &mut || control.poll().is_ok())
                    .map(|price| match native {
                        None => Some(price),
                        Some(native) => price.with_native_work(native.work).filter(|price| {
                            u64::try_from(price.work).is_ok_and(|work| {
                                work < crate::checker::bv_bitblast::MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA
                            }) && price.bytes <= crate::checker::bv_bitblast::MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA
                        }),
                    })
                    .map_err(price_error)
            })
        })
        .map_err(|error| {
            crate::checker::bv_bitblast::retained_session::bridge_error(step_id, error, end)
        })
}

fn prepay_source_plan(
    bytes: usize,
    backing_capacity: usize,
    proof: &BvExprProofLimits,
    native: Option<sparse::Cost>,
    progress: Progress<'_>,
) -> Result<(), ProofCheckError> {
    let (work, storage) =
        expression_price::wire_bounds(bytes).map_err(|_| ProofCheckError::ResourceLimit)?;
    // Preflight counts repeated names, not just distinct leaf identities.
    // Admit logical name copies/hash input before lowering/preflight entry;
    // every controlled source/iterator visit separately debits BEFORE work.
    // Opaque hash collisions, allocator internals and CPU/RSS remain open.
    let names = proof
        .max_leaf_name_bytes
        .checked_mul(16)
        .ok_or(ProofCheckError::ResourceLimit)?;
    let source_work = match native {
        Some(native) => native.work.checked_add(native.name_work),
        None => Some(names),
    }
    .ok_or(ProofCheckError::ResourceLimit)?;
    let work = work
        .checked_add(source_work)
        .ok_or(ProofCheckError::ResourceLimit)?;
    let scratch = proof
        .max_construction_bytes
        .checked_mul(2)
        .and_then(|source| source.checked_add(storage))
        .and_then(|source| source.checked_add(backing_capacity))
        .ok_or(ProofCheckError::ResourceLimit)?;
    debit(progress, work, scratch)
}

fn debit(progress: Progress<'_>, work: usize, bytes: usize) -> Result<(), ProofCheckError> {
    if progress(work, bytes) {
        Ok(())
    } else {
        Err(ProofCheckError::ResourceLimit)
    }
}

fn price_error(error: expression_price::PriceError) -> MeteredBridgeError {
    match error {
        expression_price::PriceError::Source(error) => MeteredError::Proof(error).into(),
        expression_price::PriceError::Wire(error) => MeteredError::Wire(error).into(),
        expression_price::PriceError::Resolution(ay_sat::ResolutionValidationError::Cancelled) => {
            BridgeError::Cancelled.into()
        }
        expression_price::PriceError::Resolution(
            ay_sat::ResolutionValidationError::DeadlineExceeded,
        ) => BridgeError::Deadline.into(),
        // These are numeric planning/overflow refusals, never proof verdicts.
        expression_price::PriceError::Overflow | expression_price::PriceError::Resolution(_) => {
            MeteredError::Work(WorkError::Refused).into()
        }
    }
}
