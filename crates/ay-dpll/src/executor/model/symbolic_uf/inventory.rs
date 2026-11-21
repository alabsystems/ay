// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Prepay physical source-table scans used by the existing exact declaration
//! authority. This helper grants no declaration kind or model interpretation.

use super::{Executor, SymbolicAdmission};

pub(in crate::executor) fn symbolic_source_inventory_work(
    executor: &Executor,
    owner: &SymbolicAdmission,
    incoming_bytes: usize,
) -> Option<(usize, ay_frontend::ProjectionLookupFootprint)> {
    let footprint = executor
        .ctx
        .admit_projection_lookup_work_with_progress(incoming_bytes, &mut |work, bytes| {
            owner.pay(work, bytes)
        })?;
    let mut cost = footprint.work();
    for (surface, info) in executor.ctx.model_recovery_symbol_iter() {
        let identity = executor.ctx.symbol_identity_name(surface, info);
        // Every later overload-name hash and identity comparison is priced by
        // this immutable source inventory, including inactive sparse buckets.
        if surface.len() > 256 || identity.len() > 256 {
            return None;
        }
        let work = surface
            .len()
            .checked_add(identity.len())?
            .checked_add(incoming_bytes.checked_mul(2)?)?
            .checked_add(1)?;
        if !owner.pay(work, 0) {
            return None;
        }
        cost = cost.checked_add(work)?;
    }
    Some((cost, footprint))
}
