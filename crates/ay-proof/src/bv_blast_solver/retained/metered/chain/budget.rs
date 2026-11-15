// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Successful frames are never refunded, even when the closure drops one.
/// Capture retains actual returned Vec header/capacity; replay retains each
/// borrowed slice length, NOT unseen capacity in its caller's allocation.
/// Each next codec scratch grant excludes these prior frames. This is logical
/// coexistence accounting, not whole-solver, arbitrary closure-owner or RSS
/// accounting. The caller owns any enclosing frame container and future input.
pub(super) struct Budget {
    remaining: wire::WireLimits,
    pub(super) owners: usize,
}

impl Budget {
    pub(super) fn new(mut wire: wire::WireLimits, proof: &BvExprProofLimits) -> Self {
        let r = &proof.resolution;
        wire.max_rows = wire
            .max_rows
            .min(r.max_derived_steps)
            .min(r.validation.max_derived_steps);
        wire.max_literals = wire
            .max_literals
            .min(r.max_derived_literals)
            .min(r.validation.max_derived_literals);
        wire.max_hints = wire.max_hints.min(r.max_hints).min(r.validation.max_hints);
        wire.max_work = wire.max_work.min(r.validation.max_work);
        wire.max_storage_bytes = wire
            .max_storage_bytes
            .min(r.max_codec_bytes)
            .min(r.validation.max_bytes);
        Self {
            remaining: wire,
            owners: 0,
        }
    }

    pub(super) fn child(
        &self,
        proof: &mut BvExprProofLimits,
        end: Instant,
    ) -> Result<wire::WireLimits, MeteredError> {
        // Preserve the first child's existing admission. Later retained codec
        // and DAG scratch cannot spend storage already occupied by frames.
        proof.resolution.max_codec_bytes = subtract(
            "chain codec bytes",
            proof.resolution.max_codec_bytes,
            self.owners,
        )?;
        proof.resolution.validation.max_bytes = subtract(
            "chain replay bytes",
            proof.resolution.validation.max_bytes,
            self.owners,
        )?;
        let mut wire = self.remaining;
        wire.deadline = end;
        wire.max_storage_bytes =
            subtract("chain wire storage", wire.max_storage_bytes, self.owners)?;
        Ok(wire)
    }

    pub(super) fn commit(
        &mut self,
        shape: Shape,
        json: usize,
        owner: usize,
        used: u128,
    ) -> Result<(), MeteredError> {
        let r = &mut self.remaining;
        r.max_json_bytes = subtract("chain JSON bytes", r.max_json_bytes, json)?;
        r.max_rows = subtract("chain rows", r.max_rows, shape.rows)?;
        r.max_literals = subtract("chain literals", r.max_literals, shape.literals)?;
        r.max_hints = subtract("chain hints", r.max_hints, shape.hints)?;
        let used = u64::try_from(used).map_err(|_| wire::WireError::Overflow)?;
        r.max_work = r
            .max_work
            .checked_sub(used)
            .ok_or(wire::WireError::Overflow)?;
        self.owners = self
            .owners
            .checked_add(owner)
            .ok_or(wire::WireError::Overflow)?;
        subtract("chain frame owners", r.max_storage_bytes, self.owners)?;
        Ok(())
    }
}

fn subtract(resource: &'static str, limit: usize, actual: usize) -> Result<usize, MeteredError> {
    limit.checked_sub(actual).ok_or_else(|| {
        wire::WireError::Limit {
            resource,
            limit: limit as u128,
            actual: actual as u128,
        }
        .into()
    })
}
