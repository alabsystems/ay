// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Relevance-ranked admission state owned by [`QuantifierManager`].

use super::QuantifierManager;
use crate::ematching::ScoredInstance;
use ay_core::TermId;

/// Carry queue and observation counters for relevance-ranked admission.
///
/// Carried instances are retained within one solve epoch. They are cleared at
/// every epoch and incremental-scope boundary because their entailment depends
/// on the assertions that were live when they were derived. Clearing can only
/// lose completeness; while live, the queue keeps `has_deferred` fail-closed.
#[derive(Debug, Default)]
pub(super) struct RelevanceState {
    carried: Vec<ScoredInstance>,
    stats: RelevanceStats,
}

/// Pure-observation counters for relevance-ranked admission.
#[derive(Clone, Copy, Debug, Default)]
struct RelevanceStats {
    /// Ranked admission rounds, including carry flushes below the fresh flood
    /// threshold.
    pub rounds_filtered: u64,
    /// Candidate instances selected for admission by ranked rounds.
    pub admitted: u64,
    /// Per-round withholding events. The same residual instance can contribute
    /// again when a later round re-ranks and carries it forward.
    pub withheld: u64,
    /// Carried instances later admitted by a subsequent round.
    pub flushed: u64,
    /// Stale carried instances discarded when the current E-matching epoch began.
    pub dropped: u64,
    /// Largest single-round candidate set the ranker saw.
    pub max_round_candidates: u64,
    /// Instances still carried when the counters were read.
    pub residual: u64,
}

impl RelevanceStats {
    /// Surface the counters under `quantifier.relevance.*` (pure output).
    /// Silent when this epoch has neither a ranked admission nor an opening drop.
    fn write_statistics(self, stats: &mut crate::Statistics) {
        if self.rounds_filtered == 0 && self.dropped == 0 {
            return;
        }
        stats.set_int("quantifier.relevance.rounds_filtered", self.rounds_filtered);
        stats.set_int("quantifier.relevance.admitted", self.admitted);
        stats.set_int("quantifier.relevance.withheld", self.withheld);
        stats.set_int("quantifier.relevance.flushed", self.flushed);
        stats.set_int("quantifier.relevance.dropped", self.dropped);
        stats.set_int("quantifier.relevance.residual", self.residual);
        stats.set_int(
            "quantifier.relevance.max_round_candidates",
            self.max_round_candidates,
        );
    }
}

impl QuantifierManager {
    /// Check whether cost, demand-lane, or relevance work is deferred.
    ///
    /// A non-empty carry queue must never grant a `Sat` certificate: the ground
    /// model does not yet include every ranked instance. The caller maps that
    /// state to `Unknown(QuantifierDeferred)`.
    pub(crate) fn has_deferred(&self) -> bool {
        !self.deferred.is_empty()
            || !self.demand.parked.is_empty()
            || !self.relevance.carried.is_empty()
    }

    /// Take the whole carry queue, ageing each entry by one round.
    pub(crate) fn carry_take(&mut self, age_bonus: f64) -> Vec<ScoredInstance> {
        let mut taken = std::mem::take(&mut self.relevance.carried);
        for entry in &mut taken {
            entry.age = entry.age.saturating_add(1);
            entry.score += age_bonus;
        }
        taken
    }

    /// Return instances to the carry queue (nothing is dropped).
    pub(crate) fn carry_put(&mut self, items: Vec<ScoredInstance>) {
        self.relevance.carried = items;
    }

    /// Number of instances currently withheld.
    pub(crate) fn carry_len(&self) -> usize {
        self.relevance.carried.len()
    }

    /// Generation (instantiation-chain depth) of a term, 0 for input terms.
    pub(crate) fn instance_generation(&self, term: TermId) -> u32 {
        self.generation_tracker.get(term)
    }

    /// Fold one ranked round's outcome into the observation counters.
    pub(crate) fn relevance_record_round(&mut self, candidates: u64, admitted: u64, flushed: u64) {
        let stats = &mut self.relevance.stats;
        stats.rounds_filtered += 1;
        stats.admitted += admitted;
        stats.flushed += flushed;
        stats.withheld += candidates.saturating_sub(admitted);
        stats.max_round_candidates = stats.max_round_candidates.max(candidates);
    }

    /// Snapshot of the relevance counters (pure observation).
    fn relevance_stats(&self) -> RelevanceStats {
        RelevanceStats {
            residual: self.relevance.carried.len() as u64,
            ..self.relevance.stats
        }
    }

    /// Write the current check's observation-only relevance counters.
    pub(crate) fn write_relevance_statistics(&self, stats: &mut crate::Statistics) {
        self.relevance_stats().write_statistics(stats);
    }

    /// Start per-check observation state, then account for stale carried work.
    pub(super) fn relevance_begin_epoch(&mut self) {
        let dropped = self.relevance.carried.len() as u64;
        self.relevance.carried.clear();
        self.relevance.stats = RelevanceStats {
            dropped,
            ..RelevanceStats::default()
        };
    }

    /// Clear carried terms at an incremental-scope boundary.
    ///
    /// Scope commands run outside the measured check-sat call, so this safety
    /// cleanup is intentionally observation-free. Epoch-start drops are counted
    /// by [`Self::relevance_begin_epoch`] against the current check instead.
    pub(super) fn relevance_clear_carried_at_scope_boundary(&mut self) {
        if !self.relevance.carried.is_empty() {
            // The matcher records a binding as seen before admission. Clearing
            // its only carried instance must also make that binding derivable
            // again; otherwise the next scope could publish SAT while silently
            // memo-suppressing a missing quantified consequence.
            self.match_state.reset_seen_frame();
        }
        self.relevance.carried.clear();
    }

    /// Clear relevance state when the term store and solver state are reset.
    pub(super) fn relevance_reset(&mut self) {
        self.relevance = RelevanceState::default();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::incremental_state::IncrementalSubsystem;

    fn scored(id: u32) -> ScoredInstance {
        ScoredInstance {
            inst: TermId::new(id),
            score: 0.0,
            support_root: false,
            age: 0,
        }
    }

    #[test]
    fn begin_epoch_resets_counters_then_charges_stale_carry() {
        let mut manager = QuantifierManager::new();
        manager.carry_put(vec![scored(1)]);
        manager.relevance_record_round(7, 2, 1);

        manager.begin_epoch();
        let current = manager.relevance_stats();
        assert_eq!(current.rounds_filtered, 0);
        assert_eq!(current.admitted, 0);
        assert_eq!(current.withheld, 0);
        assert_eq!(current.flushed, 0);
        assert_eq!(current.dropped, 1);
        assert_eq!(current.max_round_candidates, 0);
        assert_eq!(current.residual, 0);

        manager.begin_epoch();
        assert_eq!(manager.relevance_stats().dropped, 0);
    }

    #[test]
    fn scope_boundaries_clear_carry_without_charging_the_next_check() {
        let mut manager = QuantifierManager::new();
        let quantifier = TermId::new(10);
        let binding = vec![TermId::new(11)];

        manager.begin_epoch();
        assert!(manager.demand_seen_insert_for_test(quantifier, binding.clone()));
        manager.carry_put(vec![scored(1)]);
        IncrementalSubsystem::push(&mut manager);
        assert_eq!(manager.carry_len(), 0);
        assert_eq!(manager.seen_len(), 0);
        manager.begin_epoch();
        assert_eq!(manager.relevance_stats().dropped, 0);
        assert!(manager.demand_seen_insert_for_test(quantifier, binding.clone()));

        manager.carry_put(vec![scored(2)]);
        assert!(IncrementalSubsystem::pop(&mut manager));
        assert_eq!(manager.carry_len(), 0);
        assert_eq!(manager.seen_len(), 0);
        assert!(manager.demand_seen_insert_for_test(quantifier, binding));
        manager.begin_epoch();
        assert_eq!(manager.relevance_stats().dropped, 0);
    }
}
