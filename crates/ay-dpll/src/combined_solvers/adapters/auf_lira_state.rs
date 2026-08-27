// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Learned-state transfer, conflict collection, and replay accessors for AUFLIRA.

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_lra::LraSolver;

use super::auf_lira::AufLiraSolver;

impl AufLiraSolver<'_> {
    pub(crate) fn take_learned_state(
        &mut self,
    ) -> (Vec<ay_lia::StoredCut>, HashSet<ay_lia::HnfCutKey>) {
        self.lia.take_learned_state()
    }

    pub(crate) fn import_learned_state(
        &mut self,
        cuts: Vec<ay_lia::StoredCut>,
        seen: HashSet<ay_lia::HnfCutKey>,
    ) {
        self.lia.import_learned_state(cuts, seen);
    }

    pub(crate) fn take_dioph_state(&mut self) -> ay_lia::DiophState {
        self.lia.take_dioph_state()
    }

    pub(crate) fn import_dioph_state(&mut self, state: ay_lia::DiophState) {
        self.lia.import_dioph_state(state);
    }

    #[expect(dead_code, reason = "used by incremental split-loop conflict macros")]
    pub(crate) fn collect_all_bound_conflicts(
        &self,
        skip_first: bool,
    ) -> Vec<ay_core::TheoryConflict> {
        let mut lia_conflicts = self.lia.collect_all_bound_conflicts(false);
        let lra_conflicts = self.lra.collect_all_bound_conflicts(false);
        if skip_first && !lia_conflicts.is_empty() {
            lia_conflicts.remove(0);
        }
        if skip_first && lia_conflicts.is_empty() {
            return lra_conflicts.into_iter().skip(1).collect();
        }
        lia_conflicts.into_iter().chain(lra_conflicts).collect()
    }

    /// Replay learned cuts into the LRA solver (#6665).
    ///
    /// Forwards to both the standalone LRA solver and the LIA solver's
    /// internal LRA state.
    pub(crate) fn replay_learned_cuts(&mut self) {
        self.lra.replay_learned_cuts();
        self.lia.replay_learned_cuts();
    }

    /// Get the standalone LRA solver for bound conflict collection (#6665).
    pub(crate) fn lra_solver(&self) -> &LraSolver {
        &self.lra
    }
}
