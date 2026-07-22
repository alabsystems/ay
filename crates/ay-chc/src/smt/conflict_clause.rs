// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Farkas conflict filtering helpers for CHC SMT.

use super::context::SmtContext;
use super::types::FarkasConflict;
use ay_core::kani_compat::DetHashSet as FxHashSet;

impl SmtContext {
    pub(super) fn filter_farkas_conflicts_by_indices(
        needed_conflict_indices: &FxHashSet<usize>,
        farkas_conflicts: Vec<FarkasConflict>,
    ) -> Vec<FarkasConflict> {
        if farkas_conflicts.is_empty() {
            return farkas_conflicts;
        }
        // When the SAT UNSAT core contains no activation literals, preserve all
        // Farkas conflicts rather than discarding them. The activation-literal
        // tracking is an optimization to select *relevant* conflicts, but the SAT
        // solver's UNSAT core is not guaranteed to include activation literals when
        // theory-derived blocking clauses contribute indirectly. Dropping all
        // conflicts here forces the zero-Farkas fallback path (synthetic uniform
        // weights), which produces weaker interpolants.
        //
        // Reference: OpenSMT/Golem always pass through all theory conflicts to
        // interpolation — they do not filter by activation-literal presence.
        if needed_conflict_indices.is_empty() {
            return farkas_conflicts;
        }
        let len = farkas_conflicts.len();
        debug_assert!(
            needed_conflict_indices.iter().all(|&i| i < len),
            "BUG: needed_conflict_indices contains out-of-bounds index (len={len})",
        );
        farkas_conflicts
            .into_iter()
            .enumerate()
            .filter(|(i, _)| needed_conflict_indices.contains(i))
            .map(|(_, conflict)| conflict)
            .collect()
    }
}
