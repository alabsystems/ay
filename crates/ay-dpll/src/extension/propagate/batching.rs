// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Theory-check scheduling and adaptive batching.
//!
//! A state-unchanged return only hands control back to CDCL; the final theory
//! check remains the soundness backstop. Materialized propagations and touched
//! row analysis always bypass batching so SAT-observable work is not stranded.

use ay_core::TheorySolver;
use ay_sat::ExtPropagateResult;

use super::*;

const PHASE1_STREAK: u32 = 512;
const PHASE1_BATCH: u32 = 2;
const PHASE2_STREAK: u32 = 1024;
const PHASE2_BATCH: u32 = 4;
const PHASE3_STREAK: u32 = 2048;
const PHASE3_BATCH: u32 = 8;

impl<T: TheorySolver> TheoryExtension<'_, T> {
    pub(super) fn prepare_bcp_check(&mut self, round: &PropagationRound<'_>) -> PhaseOutcome<()> {
        if self.state_is_unchanged(round) {
            self.eager_stats.state_unchanged_skips += 1;
            self.emit_eager_event(round.sat_level, 0, "skip", 0, round.started_at);
            return PhaseOutcome::Complete(ExtPropagateResult::none());
        }

        self.atoms_since_last_check += round.asserted_atoms as u32;
        self.deferred_atom_count += round.asserted_atoms as u32;
        let batch_target = self.bcp_batch_target();
        let theory_has_pending = self.theory.has_pending_propagations();
        let theory_has_analysis = self.theory.has_pending_analysis();
        let batching_ready = self.has_checked
            && batch_target > 0
            && self.zero_propagation_streak > 0
            && self.pending_split.is_none()
            && self.deferred_atom_count < batch_target
            && !theory_has_pending
            && !theory_has_analysis;
        if batching_ready && round.sat_level == 0 {
            self.eager_stats.level0_batch_guard_hits += 1;
        }
        if batching_ready && round.sat_level > 0 {
            self.eager_stats.batch_defers += 1;
            self.emit_eager_event(
                round.sat_level,
                round.asserted_atoms,
                "batch_defer",
                0,
                round.started_at,
            );
            return PhaseOutcome::Complete(ExtPropagateResult::none());
        }

        self.deferred_atom_count = 0;
        self.pending_theory_atoms_for_batch.set(0);
        self.atoms_since_last_check = 0;
        self.has_checked = true;
        if round.sat_level == 0 {
            self.eager_stats.level0_checks += 1;
        }
        PhaseOutcome::Continue(())
    }

    fn state_is_unchanged(&self, round: &PropagationRound<'_>) -> bool {
        round.asserted_atoms == 0
            && !round.pushed_scope
            && self.has_checked
            && !self.theory.has_pending_propagations()
    }

    fn bcp_batch_target(&self) -> u32 {
        if self.zero_propagation_streak >= PHASE3_STREAK {
            PHASE3_BATCH
        } else if self.zero_propagation_streak >= PHASE2_STREAK {
            PHASE2_BATCH
        } else if self.zero_propagation_streak >= PHASE1_STREAK {
            PHASE1_BATCH
        } else {
            0
        }
    }
}
