// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{EntryInductiveFailureReason, PdrSolver};
use crate::PredicateId;

impl PdrSolver {
    #[inline]
    pub(super) fn record_entry_inductive_failure(
        &mut self,
        predicate: PredicateId,
        clause_index: usize,
        reason: EntryInductiveFailureReason,
    ) {
        let count = self
            .telemetry
            .entry_inductive_failure_counts
            .entry(reason)
            .and_modify(|value| *value = value.saturating_add(1))
            .or_insert(1);
        tracing::info!(
            action = "EntryInductiveFailure",
            predicate = predicate.index(),
            clause_index,
            reason = reason.as_str(),
            count = *count,
            "PDR: entry-inductiveness conservative failure"
        );
    }

    #[inline]
    pub(super) fn fail_entry_inductive(
        &mut self,
        predicate: PredicateId,
        clause_index: usize,
        reason: EntryInductiveFailureReason,
    ) -> bool {
        self.record_entry_inductive_failure(predicate, clause_index, reason);
        false
    }
}
