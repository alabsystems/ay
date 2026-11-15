// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) struct Binding {
    terms: TermStoreSnapshotStamp,
    metadata: u64,
    versions: (u64, u64),
    scope: Option<(usize, usize)>,
    frontier: usize,
}

impl Binding {
    pub(super) fn capture(
        source: &ArraySolver<'_>,
        work: &mut WorkBudget<'_>,
    ) -> Result<Self, QueryError> {
        work.admit(32, 8 * size_of::<Self>())?;
        Ok(Self {
            terms: source.terms.snapshot_stamp(),
            metadata: source.terms.checker_visible_metadata_generation(),
            versions: (source.eq_adj_version, source.propagate_state_version),
            scope: source
                .registered_term_scope
                .as_ref()
                .map(|scope| (scope.len(), scope.allocation_size())),
            frontier: source.populated_terms,
        })
    }

    pub(super) fn verify(
        &self,
        source: &ArraySolver<'_>,
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        work.admit(32, 8 * size_of::<TermStoreSnapshotStamp>())?;
        let current = source.terms.snapshot_stamp();
        let equal = self.terms == current
            && self.metadata == source.terms.checker_visible_metadata_generation()
            && self.versions == (source.eq_adj_version, source.propagate_state_version)
            && self.scope
                == source
                    .registered_term_scope
                    .as_ref()
                    .map(|scope| (scope.len(), scope.allocation_size()))
            && self.frontier == source.populated_terms
            && source.dirty
            && source.assign_dirty;
        drop(current);
        if equal {
            Ok(())
        } else {
            Err(work.refuse_exhaustion())
        }
    }
}
