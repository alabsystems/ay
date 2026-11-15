// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::OriginalLedger;
use crate::clause_trace::originals::OriginalArena;
use crate::literal::Literal;
use std::mem::size_of;

impl OriginalLedger {
    pub(in crate::solver) fn trace_transfer_supported(&self) -> bool {
        self.scope_starts.is_empty()
            && self.pending_global_clauses.is_empty()
            && self.pending_global_offsets.is_empty()
            && self.pending_global_clause_ids.is_empty()
            && self.pending_global_depths.is_empty()
            && self.pending_global_scope_starts.is_empty()
    }

    pub(in crate::solver) fn trace_storage_bytes(&self) -> Option<usize> {
        self.literals
            .capacity()
            .checked_mul(size_of::<Literal>())?
            .checked_add(self.offsets.capacity().checked_mul(size_of::<u32>())?)?
            .checked_add(self.clause_ids.capacity().checked_mul(size_of::<u64>())?)
    }

    pub(in crate::solver) fn into_trace_arena(self) -> Option<OriginalArena> {
        if !self.trace_transfer_supported() {
            return None;
        }
        // Field moves preserve all three allocation identities and capacities.
        // Untransferred, empty scope buffers are dropped here, before sealing.
        Some(OriginalArena {
            literals: self.literals,
            offsets: self.offsets,
            ids: self.clause_ids,
        })
    }
}
