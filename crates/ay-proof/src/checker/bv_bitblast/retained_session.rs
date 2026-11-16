// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One source-borrowing retained session inside a strict proof check.
//!
//! A complete, ordered payload inventory is admitted before ANY step can use
//! a cheap checker or semantic memo. Only the prepaid ordinary BV steps are
//! intercepted here; their live source and gate annotation are rechecked, then
//! capture/replay uses the metered bridge without any semantic memo or fallback.
//! Conditional clauses replay the source-derived ordered prerequisite/final
//! pair, or disjoint/outside/final triple. No conditional fact precedes its
//! checked prerequisite. Unknown or malformed source shapes still refuse.
//! Output bytes are untrusted transport, not proof authority. The enclosing
//! checker must still validate every other step and the terminal contradiction.
//!
//! Every per-kind whole-proof reservation remains held through this attempt;
//! no successful lemma refunds work or bytes. Wire owners remain inside those
//! reservations, including across subsequent lemmas. Only the outer result
//! slots have a separate progress charge. These logical bounds are not RSS or
//! hard allocation/destructor latency guarantees.
//!
//! Each step's attempt ends at the original caller deadline or one
//! `PRODUCER_HANG_GUARD` after it starts, whichever is first: exactly the
//! legacy producer's per-attempt hang guard, so a far caller deadline never
//! lets a capture's SAT search or a replay run past it. Reaching the guard
//! before the caller's deadline is a resource refusal, not a cancellation.

use super::classification::PrepaidBvCredits;
use super::producer_limits::{proof_producing_limits, proof_replay_limits};
use super::proof_producing_control::retained::{
    metered::{self as bridge, MeteredBridgeError},
    BridgeError,
};
use super::{
    validate_bv_bitblast_structure_with_progress, Instant, ProofCheckError, ProofId, ProofStep,
    TermId, TheoryLemmaKind, MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF,
};
use crate::bv_blast_solver::retained::{
    wire::{WireError, WireLimits},
    work::MeteredError,
};
use crate::bv_blast_solver::BvExprProofLimits;

mod control;
mod inventory;
use control::Control;

/// Untrusted wire associated with an exact proof-step position. Neither the
/// association nor deserialization establishes that this step is valid.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RetainedStepPayload {
    pub(crate) step: u32,
    pub(crate) payload: Vec<u8>,
}

#[derive(Clone, Copy)]
pub(crate) enum RetainedOperation<'wire> {
    Capture,
    Replay(&'wire [RetainedStepPayload]),
}

pub(crate) struct RetainedSession<'proof, 'wire> {
    credits: PrepaidBvCredits<'proof>,
    operation: RetainedOperation<'wire>,
    wire: WireLimits,
    output: Vec<RetainedStepPayload>,
    completed: usize,
    failed: bool,
}

/// Existing source-counted ceilings for the enclosing retained transport.
/// They confer no work credit; callers may only intersect additional ceilings.
pub(crate) fn transport_wire_limits(deadline: Instant) -> WireLimits {
    inventory::effective_wire_limits(deadline, None)
}

impl<'proof, 'wire> RetainedSession<'proof, 'wire> {
    #[cfg(test)]
    pub(crate) fn new(
        credits: PrepaidBvCredits<'proof>,
        operation: RetainedOperation<'wire>,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Self, ProofCheckError> {
        Self::new_with_wire_limits(credits, operation, None, progress)
    }

    /// Additional per-operation wire ceilings, not another work allowance.
    /// One downward intersection is shared by inventory admission and every
    /// source-bound bridge call; the prepaid credit is never enlarged.
    pub(crate) fn new_with_wire_limits(
        credits: PrepaidBvCredits<'proof>,
        operation: RetainedOperation<'wire>,
        wire_limits: Option<WireLimits>,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Self, ProofCheckError> {
        let wire = inventory::effective_wire_limits(credits.deadline(), wire_limits);
        let mut control = Control::new(wire.deadline, progress);
        let result = (|| {
            control.poll()?;
            inventory::admit(&credits, &operation, &wire, &mut control)?;
            let output = inventory::output(&operation, &mut control)?;
            Ok(Self {
                credits,
                operation,
                wire,
                output,
                completed: 0,
                failed: false,
            })
        })();
        control.finish(result)
    }

    pub(crate) fn original_deadline(&self) -> Instant {
        self.wire.deadline
    }

    pub(crate) fn validate_step(
        &mut self,
        id: ProofId,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Option<&'proof [TermId]>, ProofCheckError> {
        let mut control = Control::new(self.original_deadline(), progress);
        if self.failed {
            drop(std::mem::take(&mut self.output));
            return control.finish(Err(ProofCheckError::ResourceLimit));
        }
        // Remain poisoned during all caller code and bridge work. If a caller
        // catches a panic, neither this step nor another can reuse the session.
        self.failed = true;
        let result = self.validate(id, &mut control);
        if result.is_err() {
            drop(std::mem::take(&mut self.output));
        }
        let result = control.finish(result);
        if result.is_err() {
            drop(std::mem::take(&mut self.output));
            let _ = control.poll();
        } else {
            self.failed = false;
        }
        result
    }

    fn validate(
        &mut self,
        id: ProofId,
        control: &mut Control<'_>,
    ) -> Result<Option<&'proof [TermId]>, ProofCheckError> {
        control.poll()?;
        if self.credits.source_step(id).is_none() {
            return Ok(None);
        }
        control.charge(1, 0)?;
        if self.credits.ordinary_ids().nth(self.completed) != Some(id) {
            return Err(invalid(
                id,
                "retained steps must be checked once in source order",
            ));
        }
        let credit = self
            .credits
            .take(id, &mut |work, bytes| control.charge(work, bytes).is_ok())
            .map_err(|_| ProofCheckError::ResourceLimit)?;
        let terms = credit.terms();
        let clause = credit.clause();
        let gate = match credit.step() {
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::BvBitBlast,
                ..
            } => None,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::BvBitBlastGate { gate_type, width },
                ..
            } => Some((*gate_type, *width)),
            _ => return Err(invalid(id, "retained credit is not an ordinary BV step")),
        };
        validate_bv_bitblast_structure_with_progress(
            terms,
            id,
            clause,
            gate,
            &mut |work, bytes| control.charge(work, bytes).is_ok(),
        )?;
        let original = self.original_deadline();
        let mut limits = attempt_limits(original);
        let gates = proof_replay_limits(&limits);
        let mut wire = self.wire;
        if let Some(price) = credit.replay_price() {
            price.tighten(&mut limits, &mut wire);
        }
        let allowance = credit.into_allowance();
        match &self.operation {
            RetainedOperation::Capture => {
                let result = bridge::capture_clause(
                    terms,
                    clause,
                    &limits,
                    &gates,
                    &wire,
                    allowance,
                    &mut || control.poll().is_ok(),
                )
                .map_err(|error| bridge_error(id, error, original))?;
                // Inner wire admission prices the owner before allocation.
                // The aggregate reservation is not released at this boundary.
                if result.value.capacity() > wire.max_storage_bytes
                    || result.value.len() > wire.max_json_bytes
                    || self.output.len() >= self.output.capacity()
                {
                    return Err(ProofCheckError::ResourceLimit);
                }
                control.poll()?;
                self.output.push(RetainedStepPayload {
                    step: id.0,
                    payload: result.value,
                });
            }
            RetainedOperation::Replay(payloads) => {
                let payload = payloads
                    .get(self.completed)
                    .ok_or_else(|| invalid(id, "missing retained payload"))?;
                bridge::replay_clause(
                    terms,
                    clause,
                    &payload.payload,
                    &limits,
                    &gates,
                    &wire,
                    allowance,
                    &mut || control.poll().is_ok(),
                )
                .map_err(|error| bridge_error(id, error, original))?;
            }
        }
        self.completed += 1; // Bounded by the complete, at-most-eight inventory.
        Ok(Some(clause))
    }

    pub(crate) fn finish(
        self,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Vec<RetainedStepPayload>, ProofCheckError> {
        let mut control = Control::new(self.original_deadline(), progress);
        let result = {
            let Self {
                credits,
                operation: _,
                output,
                failed,
                ..
            } = self;
            if failed {
                drop(output);
                Err(ProofCheckError::ResourceLimit)
            } else {
                match credits.finish() {
                    Ok(()) => Ok(output),
                    Err(_) => {
                        drop(output);
                        Err(ProofCheckError::ResourceLimit)
                    }
                }
            }
        };
        // Credits and session scratch have gone, including on missing steps.
        control.finish(result)
    }
}

/// One step's attempt envelope: the legacy producer's counted caps, ending at
/// the original deadline or one `PRODUCER_HANG_GUARD` from now, if sooner.
fn attempt_limits(original: Instant) -> BvExprProofLimits {
    proof_producing_limits(Some(original)).0
}

fn invalid(step: ProofId, reason: &str) -> ProofCheckError {
    ProofCheckError::InvalidTheoryLemma {
        step,
        reason: reason.to_owned(),
    }
}

pub(super) fn bridge_error(
    step: ProofId,
    error: MeteredBridgeError,
    original: Instant,
) -> ProofCheckError {
    match error {
        // Every attempt deadline is the original one or the earlier hang
        // guard, so a stop before the original deadline is the guard's.
        MeteredBridgeError::Bridge(BridgeError::Deadline) if Instant::now() < original => {
            ProofCheckError::ResourceLimit
        }
        MeteredBridgeError::Bridge(BridgeError::Cancelled | BridgeError::Deadline) => {
            ProofCheckError::Cancelled
        }
        #[cfg(test)]
        MeteredBridgeError::Bridge(BridgeError::Specialized(_)) => invalid(
            step,
            "conditional BV route requires additional retained prerequisite proofs",
        ),
        MeteredBridgeError::Retained(MeteredError::Work(_))
        | MeteredBridgeError::Retained(MeteredError::Wire(
            WireError::Limit { .. } | WireError::Overflow | WireError::Allocation,
        )) => ProofCheckError::ResourceLimit,
        _ => invalid(step, "source-bound retained BV refutation refused"),
    }
}

#[cfg(test)]
mod tests;
