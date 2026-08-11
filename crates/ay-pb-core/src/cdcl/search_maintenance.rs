// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Between-conflict search-state maintenance for `PbCdclSolver`: learned-clause
//! database reduction (LBD, activity, reduce-db), VSIDS activity bumping/decay,
//! backtracking, and restarts. Extracted from `cdcl.rs`; these remain methods on
//! [`super::PbCdclSolver`].

use super::*;
use crate::proof::ConstraintId;
use crate::types::PbConstraint;

/// Poll the memory guard once per this many conflicts in `should_reduce_db`
/// (the footprint read is a real syscall; conflicts are the hot cadence).
const REDUCE_DB_MEMORY_POLL_CONFLICTS: u64 = 1024;

/// Memory-pressure threshold (percent of the process limit) that forces an
/// early learnt-DB reduction — below the 95% hard guard so the reduction can
/// still avert the abort.
const REDUCE_DB_MEMORY_PRESSURE_PERCENT: usize = 80;

impl PbCdclSolver {
    /// Computes the LBD (Literal Block Distance) of a constraint.
    ///
    /// LBD = number of distinct decision levels among the currently falsified
    /// literals in the constraint. Lower LBD indicates higher quality: the
    /// constraint connects fewer decision levels and acts more like "glue"
    /// between propagation chains.
    ///
    /// Reference: Audemard & Simon, "Predicting Learnt Clauses Quality in
    /// Modern SAT Solvers" (IJCAI 2009).
    pub(super) fn compute_lbd(&self, constraint: &PbConstraint) -> u32 {
        let mut levels = Vec::new();
        for term in &constraint.terms {
            for pb_lit in &term.lits {
                let dimacs_lit = pb_lit_to_dimacs(*pb_lit);
                if self.propagator.value(dimacs_lit) == LitValue::False {
                    if let Some(level) = self.propagator.decision_level(-dimacs_lit) {
                        if !levels.contains(&level) {
                            levels.push(level);
                        }
                    }
                } else if self.propagator.value(dimacs_lit) == LitValue::True {
                    if let Some(level) = self.propagator.decision_level(dimacs_lit) {
                        if !levels.contains(&level) {
                            levels.push(level);
                        }
                    }
                }
            }
        }
        u32::try_from(levels.len()).unwrap_or(u32::MAX)
    }

    /// Returns whether it is time to run `reduce_db`.
    ///
    /// Default (opt-in flag OFF): the historical fixed modular cadence — fire
    /// every `reduce_interval` conflicts.
    ///
    /// Opt-in (flag ON): a growing interval (see `advance_reduce_db_schedule`):
    /// each reduction pushes the next trigger further out so the learned DB is
    /// allowed to grow as search deepens. The first trigger is derived from
    /// `config.reduce_interval`.
    pub(super) fn should_reduce_db(&self) -> bool {
        if self.config.reduce_interval == 0 || self.stats.conflicts == 0 {
            return false;
        }
        if !self.learned_active.iter().any(|&a| a) {
            return false;
        }
        // Memory pressure forces a reduction ahead of the conflict cadence:
        // the learnt DB is this engine's only unbounded growth, and a pure
        // conflict-count schedule lets it blow past the competition MEMLIMIT
        // into a SIGKILL with no s line. Polled once per
        // `REDUCE_DB_MEMORY_POLL_CONFLICTS` conflicts (the footprint read is a
        // syscall) at a threshold below the hard 95% guard, so shedding cold
        // learnt rows can avert the abort; a no-op when no limit is set.
        if self
            .stats
            .conflicts
            .is_multiple_of(REDUCE_DB_MEMORY_POLL_CONFLICTS)
            && ay_sys::process_memory_exceeded_at_percent(REDUCE_DB_MEMORY_PRESSURE_PERCENT)
        {
            return true;
        }
        if !self.config.learned_activity_reducedb_enabled {
            return self
                .stats
                .conflicts
                .is_multiple_of(self.config.reduce_interval);
        }
        let threshold = if self.next_reduce_db_conflicts == 0 {
            self.config.reduce_interval
        } else {
            self.next_reduce_db_conflicts
        };
        self.stats.conflicts >= threshold
    }

    fn locked_learned_constraints(&self) -> Vec<bool> {
        let mut locked = vec![false; self.learned_constraints.len()];
        let num_non_learned = self.constraints.len();

        for reason_cid in self.trail.iter().filter_map(|entry| entry.reason) {
            let Some(learned_idx) = reason_cid.checked_sub(num_non_learned) else {
                continue;
            };
            if learned_idx < locked.len() {
                locked[learned_idx] = true;
            }
        }

        locked
    }

    /// Deletes low-quality learned constraints.
    ///
    /// Keeps glue constraints protected and sorts deletable constraints by LBD
    /// descending, removing the worst half.
    #[cfg(test)]
    pub(super) fn reduce_db(&mut self) {
        let mut never_stop = |_: &Self| false;
        let interrupted = self.reduce_db_with_stop(&mut never_stop);
        debug_assert!(
            !interrupted,
            "non-interruptible reduce_db wrapper must not report interruption"
        );
    }

    pub(super) fn reduce_db_with_stop<S>(&mut self, should_stop: &mut S) -> bool
    where
        S: ConflictStop,
    {
        self.stats.reduce_db_calls += 1;
        // Under the opt-in growing cadence, push the next trigger out before any
        // early return: the schedule must advance whether or not this sweep
        // completes, so the search loop does not immediately re-attempt a
        // reduction on the next conflict. (No-op for the default modular cadence.)
        if self.config.learned_activity_reducedb_enabled {
            self.advance_reduce_db_schedule();
        }
        if should_stop.should_stop(self) {
            return true;
        }

        let locked = self.locked_learned_constraints();
        if should_stop.should_stop(self) {
            return true;
        }

        // Collect indices of deletable learned constraints.
        //
        // PROTECT (never deletable):
        //   - deactivated lemmas / locked reasons / permanent constraints,
        //   - high-quality "glue" lemmas (LBD <= glue threshold),
        //   - (opt-in) short lemmas (size <= REDUCE_DB_PROTECT_SIZE): cheap to
        //     keep and re-derived rarely.
        let size_protect = self.config.learned_activity_reducedb_enabled;
        let mut deletable = Vec::new();
        for (i, &is_locked) in locked
            .iter()
            .enumerate()
            .take(self.learned_constraints.len())
        {
            if should_stop.should_stop(self) {
                return true;
            }
            let deletable_now = self.learned_active[i]
                && !is_locked
                && !self.learned_permanent[i]
                && self.learned_lbd[i] > self.config.glue_lbd_threshold
                && !(size_protect && self.learned_constraint_size(i) <= REDUCE_DB_PROTECT_SIZE);
            if deletable_now {
                deletable.push(i);
            }
        }

        if deletable.is_empty() {
            return false;
        }

        if should_stop.should_stop(self) {
            return true;
        }

        // Sort by LBD descending (worst quality first). Under the opt-in
        // heuristic, break LBD ties by activity ascending (least recently useful
        // first) so equal-quality lemmas are evicted least-useful-first.
        if self.config.learned_activity_reducedb_enabled {
            deletable.sort_by(|&a, &b| {
                self.learned_lbd[b].cmp(&self.learned_lbd[a]).then_with(|| {
                    self.learned_activity[a]
                        .partial_cmp(&self.learned_activity[b])
                        .unwrap_or(std::cmp::Ordering::Equal)
                })
            });
        } else {
            deletable.sort_by(|&a, &b| self.learned_lbd[b].cmp(&self.learned_lbd[a]));
        }

        if should_stop.should_stop(self) {
            return true;
        }

        // Delete the worst half. Bookkeeping per row is cheap (flag + proof
        // log); the watch-list purge is ONE bulk sweep afterwards instead of a
        // per-row retain over every watched literal's list — the per-row purge
        // was quadratic-ish on counting-heavy learned DBs and dominated
        // UNSAT-grind profiles (P2e). No stop-polls inside the loop: the whole
        // deletion (including the bulk sweep) is bounded linear work, and
        // stopping between the bookkeeping and the purge would leave rows
        // marked deleted while still propagating.
        let delete_count = deletable.len() / 2;
        let num_original = self.constraints.len();

        let mut deactivate_cids = Vec::with_capacity(delete_count);
        for &learned_idx in &deletable[..delete_count] {
            self.learned_active[learned_idx] = false;
            let propagator_cid = num_original + learned_idx;
            deactivate_cids.push(propagator_cid);
            self.stats.learned_deletions += 1;

            // Log deletion in proof if proof logging is active.
            if let Some(proof_id) = self.proof_id_for_constraint(propagator_cid) {
                self.log_proof_step(ProofStep::Delete(proof_id));
            }
        }
        self.propagator
            .deactivate_constraints_bulk(&deactivate_cids);

        false
    }

    pub(super) fn backtrack_to(&mut self, level: u32) {
        if level >= self.decision_level {
            return;
        }

        // Find the trail position for the target level.
        let target_trail_pos = if level == 0 {
            0
        } else {
            self.trail_lim[level as usize]
        };

        // Unassign all literals above the target level and re-insert into heap.
        let mut unassigned_lits = Vec::with_capacity(self.trail.len() - target_trail_pos);
        while self.trail.len() > target_trail_pos {
            let entry = self.trail.pop().expect("trail not empty");
            let var = entry.lit.unsigned_abs();
            unassigned_lits.push(entry.lit);
            // Re-insert variable into VSIDS heap so it can be picked again.
            self.vsids_heap.insert(var, &self.activity);
        }
        self.propagator.unassign_literals(&unassigned_lits);

        // Remove trail limit markers.
        self.trail_lim.truncate(level as usize);
        self.decision_level = level;
    }

    pub(super) fn backtrack_to_interruptible<F>(&mut self, level: u32, should_stop: &mut F) -> bool
    where
        F: FnMut() -> bool,
    {
        if level >= self.decision_level {
            return false;
        }
        if self.interrupted || should_stop() {
            return true;
        }

        let target_trail_pos = if level == 0 {
            0
        } else {
            self.trail_lim[level as usize]
        };

        let mut unassigned_lits = Vec::with_capacity(self.trail.len() - target_trail_pos);
        while self.trail.len() > target_trail_pos {
            let entry = self.trail.pop().expect("trail not empty");
            let var = entry.lit.unsigned_abs();
            unassigned_lits.push(entry.lit);
            self.vsids_heap.insert(var, &self.activity);
        }

        self.trail_lim.truncate(level as usize);
        self.decision_level = level;

        self.propagator
            .unassign_literals_interruptible(&unassigned_lits, &mut *should_stop)
    }

    pub(super) fn bump_activity_weighted(&mut self, var: u32, coeff: i128) {
        if (var as usize) < self.activity.len() {
            let weight = (coeff.unsigned_abs().max(1)) as f64;
            self.activity[var as usize] += self.activity_inc * weight;
            // Rescale if too large.
            if self.activity[var as usize] > 1e100 {
                for a in &mut self.activity {
                    *a *= 1e-100;
                }
                self.activity_inc *= 1e-100;
                // After rescaling all activities, rebuild the heap ordering.
                // This is rare (once per ~1e100 bumps) so O(n) is acceptable.
                self.rebuild_heap();
                return;
            }
            // Percolate up in the heap since this variable's activity increased.
            self.vsids_heap.update(var, &self.activity);
        }
    }

    /// Rebuilds the heap ordering after activity rescaling.
    pub(super) fn rebuild_heap(&mut self) {
        let num_vars = self.num_vars;
        let old_heap = std::mem::replace(&mut self.vsids_heap, VsidsHeap::new(0));
        self.vsids_heap = VsidsHeap::from_vars_heapified(num_vars, old_heap.heap, &self.activity);
    }

    pub(super) fn decay_activity(&mut self) {
        self.activity_inc *= 1000.0 / self.config.activity_decay_milli as f64;
    }

    /// Bumps the activity of the learned constraint referenced by `constraint_id`
    /// (a propagator/reason index). Original (input) constraints have no activity
    /// and are ignored. Rescales all activities if the score overflows the
    /// VSIDS-style threshold. Called whenever the constraint participates in a
    /// conflict (as the conflict constraint or as a reason during analysis).
    /// No-op unless the opt-in activity heuristic is enabled. Heuristic only —
    /// affects `reduce_db` ranking, never lemma semantics.
    pub(super) fn bump_learned_activity(&mut self, constraint_id: usize) {
        if !self.config.learned_activity_reducedb_enabled {
            return;
        }
        let num_original = self.constraints.len();
        let Some(learned_idx) = constraint_id.checked_sub(num_original) else {
            return;
        };
        let inc = self.learned_constraint_inc;
        let Some(activity) = self.learned_activity.get_mut(learned_idx) else {
            return;
        };
        *activity += inc;
        if *activity > LEARNED_ACTIVITY_RESCALE_LIMIT {
            self.rescale_learned_activity();
        }
    }

    /// Rescales all learned-constraint activities (and the increment) down by the
    /// reciprocal of the overflow limit. Preserves relative ordering. Standard
    /// VSIDS rescale; rare (roughly once per `1e100` bumps).
    fn rescale_learned_activity(&mut self) {
        let scale = 1.0 / LEARNED_ACTIVITY_RESCALE_LIMIT;
        for a in &mut self.learned_activity {
            *a *= scale;
        }
        self.learned_constraint_inc *= scale;
    }

    /// Grows the learned-constraint activity increment by the decay factor so
    /// that bumps applied to more-recent conflicts outweigh older ones. Called
    /// once per conflict, mirroring the variable-activity decay. No-op unless the
    /// opt-in activity heuristic is enabled.
    pub(super) fn decay_learned_activity(&mut self) {
        if !self.config.learned_activity_reducedb_enabled {
            return;
        }
        self.learned_constraint_inc /= LEARNED_ACTIVITY_DECAY;
    }

    /// Recomputes the LBD of the learned constraint referenced by `constraint_id`
    /// (a propagator/reason index) under the current trail and keeps it only if
    /// it improved (Glucose lowers a reused clause's LBD, never raises it). A
    /// smaller LBD reflects that the lemma now links fewer decision levels, so it
    /// is more likely to be protected by `reduce_db`. No-op for original
    /// constraints, and a no-op unless the opt-in heuristic is enabled. Heuristic
    /// only — LBD never affects lemma semantics, only deletion ranking.
    pub(super) fn refresh_learned_lbd_on_reason_use(&mut self, constraint_id: usize) {
        if !self.config.learned_activity_reducedb_enabled {
            return;
        }
        let num_original = self.constraints.len();
        let Some(learned_idx) = constraint_id.checked_sub(num_original) else {
            return;
        };
        if learned_idx >= self.learned_constraints.len() {
            return;
        }
        let new_lbd = {
            let constraint = &self.learned_constraints[learned_idx];
            self.compute_lbd(constraint)
        };
        if let Some(slot) = self.learned_lbd.get_mut(learned_idx) {
            if new_lbd > 0 && new_lbd < *slot {
                *slot = new_lbd;
            }
        }
    }

    /// Number of literals in a learned constraint (sum of per-term literal
    /// counts). Linear terms contribute one literal each; non-linear product
    /// terms contribute their full literal count. Used by the opt-in two-tier
    /// `reduce_db` to protect short lemmas (size <= `REDUCE_DB_PROTECT_SIZE`).
    fn learned_constraint_size(&self, learned_idx: usize) -> usize {
        self.learned_constraints
            .get(learned_idx)
            .map(|c| c.terms.iter().map(|t| t.lits.len()).sum())
            .unwrap_or(0)
    }

    /// Advances the opt-in growing `reduce_db` schedule after a reduction. The
    /// next trigger is pushed out by the base interval plus a growth term
    /// proportional to the number of reductions performed (Glucose/MiniSat-style
    /// increasing cadence).
    fn advance_reduce_db_schedule(&mut self) {
        let base = self.config.reduce_interval.max(1);
        let growth = REDUCE_DB_INTERVAL_GROWTH.saturating_mul(self.stats.reduce_db_calls);
        self.next_reduce_db_conflicts = self
            .stats
            .conflicts
            .saturating_add(base)
            .saturating_add(growth);
    }

    pub(super) fn should_restart(&self) -> bool {
        if self.conflicts_since_restart < self.config.min_restart_interval {
            return false;
        }
        if self.stats.conflicts < self.config.glucose_warmup_conflicts || self.lbd_ema_global <= 0.0
        {
            return self.conflicts_since_restart >= self.restart_threshold;
        }
        // Glucose LBD-ratio trigger: restart when recent learned-lemma quality
        // (LBD) degrades sharply relative to the global average.
        if self.lbd_ema_recent / self.lbd_ema_global > self.config.glucose_lbd_ratio_threshold {
            return true;
        }
        // LUBY STARVATION FLOOR. On dense-PB instances the learned cutting-planes
        // lemmas have uniformly HIGH LBD (they span many decision levels), so the
        // glucose ratio sits at ~1 and the trigger above NEVER fires — the engine
        // would otherwise run the entire budget with ZERO restarts (measured on
        // BNN dense-PB rows). Fall back to the Luby schedule (the same threshold
        // already advanced per restart) so search still gets periodic restarts,
        // matching RoundingSat's pure-Luby policy on this class. Only ever ADDS
        // restarts the glucose policy missed. Gated by AY_PB_NO_RESTART_FLOOR.
        if restart_floor_enabled() {
            return self.conflicts_since_restart >= self.restart_threshold;
        }
        false
    }

    pub(super) fn restart(&mut self) {
        self.stats.restarts += 1;
        if self.stats.conflicts >= self.config.glucose_warmup_conflicts
            && self.lbd_ema_global > 0.0
            && self.lbd_ema_recent / self.lbd_ema_global > self.config.glucose_lbd_ratio_threshold
        {
            self.stats.glucose_restarts += 1;
        } else {
            self.stats.luby_restarts += 1;
        }
        self.backtrack_to(0);
        self.conflicts_since_restart = 0;
        self.luby_index += 1;
        self.restart_threshold = self.config.restart_base * luby_sequence(self.luby_index);
    }

    pub(super) fn restart_interruptible<F>(&mut self, should_stop: &mut F) -> bool
    where
        F: FnMut() -> bool,
    {
        if self.interrupted || should_stop() {
            return true;
        }

        let is_glucose = self.stats.conflicts >= self.config.glucose_warmup_conflicts
            && self.lbd_ema_global > 0.0
            && self.lbd_ema_recent / self.lbd_ema_global > self.config.glucose_lbd_ratio_threshold;

        if self.backtrack_to_interruptible(0, should_stop) {
            return true;
        }

        self.stats.restarts += 1;
        if is_glucose {
            self.stats.glucose_restarts += 1;
        } else {
            self.stats.luby_restarts += 1;
        }
        self.conflicts_since_restart = 0;
        self.luby_index += 1;
        self.restart_threshold = self.config.restart_base * luby_sequence(self.luby_index);
        false
    }

    pub(super) fn update_lbd_averages(&mut self, lbd: u32) {
        let lbd_f = f64::from(lbd);
        self.lbd_sum += lbd_f;
        self.lbd_count += 1;
        let window = self.config.glucose_recent_window.max(1) as f64;
        let alpha_recent = 1.0 / window;
        let alpha_global = 1.0 / (5.0 * window);
        if self.lbd_count == 1 {
            self.lbd_ema_recent = lbd_f;
            self.lbd_ema_global = lbd_f;
        } else {
            self.lbd_ema_recent = alpha_recent * lbd_f + (1.0 - alpha_recent) * self.lbd_ema_recent;
            self.lbd_ema_global = alpha_global * lbd_f + (1.0 - alpha_global) * self.lbd_ema_global;
        }
        self.stats.avg_lbd = self.lbd_sum / self.lbd_count as f64;
    }

    pub(super) fn record_learned_constraint_id(&mut self, proof_id: ConstraintId) {
        let constraint_index = self.constraints.len() + self.learned_constraints.len();
        if self.constraint_ids.len() == constraint_index {
            self.constraint_ids.push(proof_id);
        } else {
            // LOUD lockstep-guard failure (proof-tap spec, phase 0). A desync
            // here means some constraint entered `self.constraints` /
            // `self.learned_constraints` without a matching `constraint_ids`
            // entry: every LATER learned lemma silently loses its proof id and
            // degrades to the RUP fallback, bloating proofs and slowing the
            // checker. Surface it as a stat (release) and an assert (debug)
            // instead of silently degrading.
            self.stats.proof_id_lockstep_desyncs += 1;
            debug_assert!(
                false,
                "proof constraint-id lockstep desync: constraint_ids has {} entries \
                 but the next constraint index is {constraint_index}",
                self.constraint_ids.len(),
            );
        }
    }
}
