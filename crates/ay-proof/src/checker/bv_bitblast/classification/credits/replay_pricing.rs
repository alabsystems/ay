// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Narrow eligible ordinary Replay charges BEFORE prepayment, never after
//! acceptance. Borrowed source and immutable inventory retain no authority.

use super::*;
use crate::bv_blast_solver::retained::wire::WireLimits;
use crate::checker::bv_bitblast::{
    producer_limits::{counted_limits_until, proof_replay_limits},
    proof_producing_control::retained::metered,
    retained_session::{transport_wire_limits, RetainedStepPayload},
};

impl ExpensiveBvCreditPlan<'_> {
    pub(crate) fn refine_replay(
        mut self,
        payloads: &[RetainedStepPayload],
        deadline: Instant,
        requested: Option<WireLimits>,
        progress: Progress<'_>,
    ) -> Result<Self, ProofCheckError> {
        let wire = effective_wire(deadline, requested);
        // Direct callers also obey an earlier requested absolute wire clock.
        let mut control = Control {
            deadline: wire.deadline,
            refused: false,
        };
        let mut owned_progress = |work, bytes| control.debit(work, bytes, progress).is_ok();
        if !owned_progress(1, 0) {
            return Err(ProofCheckError::ResourceLimit);
        }
        let ordinary = self
            .entries
            .iter()
            .flatten()
            .filter(|entry| entry.ordinary_clause().is_some())
            .count();
        if payloads.len() != ordinary {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: ProofId(0),
                reason: "retained payload inventory is incomplete or excessive".to_owned(),
            });
        }
        let proof = counted_limits_until(wire.deadline);
        let gates = proof_replay_limits(&proof);
        for (entry, payload) in self
            .entries
            .iter_mut()
            .flatten()
            .filter(|entry| entry.ordinary_clause().is_some())
            .zip(payloads)
        {
            refine_entry(
                self.terms,
                entry,
                payload,
                &proof,
                &gates,
                &wire,
                &mut owned_progress,
            )?;
        }
        let aggregate = sum_entries(&self.entries)?;
        if !owned_progress(0, 0) {
            return Err(ProofCheckError::ResourceLimit);
        }
        self.aggregate = aggregate;
        Ok(self)
    }
}

fn refine_entry(
    terms: &TermStore,
    entry: &mut Entry<'_>,
    payload: &RetainedStepPayload,
    proof: &crate::bv_blast_solver::BvExprProofLimits,
    gates: &crate::bv_blast_export::BvBlastValidateLimits,
    wire: &WireLimits,
    progress: Progress<'_>,
) -> Result<(), ProofCheckError> {
    if !progress(1, 0) {
        return Err(ProofCheckError::ResourceLimit);
    }
    let id = u32::try_from(entry.position).map_err(|_| ProofCheckError::ResourceLimit)?;
    if payload.step != id {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: ProofId(id),
            reason: "retained payload IDs do not match source order".to_owned(),
        });
    }
    if payload.payload.len() > wire.max_json_bytes
        || payload.payload.capacity() > wire.max_storage_bytes
    {
        return Err(ProofCheckError::ResourceLimit);
    }
    if let Some(price) = metered::price_clause(
        terms,
        ProofId(id),
        entry.step,
        &payload.payload,
        payload.payload.capacity(),
        proof,
        gates,
        wire,
        progress,
    )? {
        apply_price(entry, price);
    }
    Ok(())
}

fn apply_price(entry: &mut Entry<'_>, price: ReplayPrice) {
    // A larger conservative bound cannot be truncated into a smaller grant.
    // Numeric inability retains the entire exact original fee.
    if price.work >= entry.charge.work || price.bytes > entry.charge.bytes {
        return;
    }
    entry.charge = ExpensiveBvAggregateCharge {
        work: price.work,
        bytes: price.bytes,
    };
    entry.replay_price = Some(price);
}

fn sum_entries(
    entries: &[Option<Entry<'_>>],
) -> Result<ExpensiveBvAggregateCharge, ProofCheckError> {
    let mut aggregate = ExpensiveBvAggregateCharge::default();
    for entry in entries.iter().flatten() {
        aggregate.work = aggregate
            .work
            .checked_add(entry.charge.work)
            .ok_or(ProofCheckError::ResourceLimit)?;
        aggregate.bytes = aggregate
            .bytes
            .checked_add(entry.charge.bytes)
            .ok_or(ProofCheckError::ResourceLimit)?;
    }
    Ok(aggregate)
}

fn effective_wire(deadline: Instant, requested: Option<WireLimits>) -> WireLimits {
    let mut wire = transport_wire_limits(deadline);
    if let Some(requested) = requested {
        wire.max_json_bytes = wire.max_json_bytes.min(requested.max_json_bytes);
        wire.max_rows = wire.max_rows.min(requested.max_rows);
        wire.max_literals = wire.max_literals.min(requested.max_literals);
        wire.max_hints = wire.max_hints.min(requested.max_hints);
        wire.max_work = wire.max_work.min(requested.max_work);
        wire.max_storage_bytes = wire.max_storage_bytes.min(requested.max_storage_bytes);
        wire.deadline = wire.deadline.min(requested.deadline);
    }
    wire
}

#[cfg(test)]
mod tests;
