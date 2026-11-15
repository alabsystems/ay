// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kissat's binary-clause backbone (`backbone.c`, `compute_backbone`) on
//! AY's binary watches.
//!
//! `backbone_binary` decides each candidate literal, propagates over the
//! binary clauses and backtracks to level 0 before the next one, so a call
//! costs the sum of every literal's implication closure: about 100 ms per
//! call, and 107 of the 115 s of backbone time over the 146 field-solved
//! misses (300K-conflict screen, 2026-09-21). Kissat stacks the probes: a
//! probe that propagates without conflict stays assigned, the next probes
//! start from its closure, and a candidate that closure has satisfied is
//! dropped for good (its own closure lies inside a consistent one, so it is
//! not a failed literal). Only a conflict backtracks — to the level below the
//! probe — and asserts the probe's negation. A round is therefore about one
//! propagation pass over the binary clauses.
//!
//! Why stacking is sound. The assignment is closed under binary propagation
//! before every probe. A candidate still unassigned is then implied by none
//! of the stacked decisions, and neither is its negation, so its propagation
//! can conflict only inside its own closure: a conflict with an earlier
//! literal `y` would need `probe ⟹* ¬y`, whose contrapositive `y ⟹* ¬probe`
//! would already have assigned `¬probe`. A conflict inside the probe's own
//! closure makes the probe's negation a unit of the binary clauses alone, and
//! asserting it below the probe cannot conflict with the stack either, except
//! when the clauses are inconsistent at level 0 — which the level-0 replay at
//! the end of the round reports through the ordinary unit machinery. The
//! closure argument needs every binary watch to be seen, which
//! `backbone_binary_propagate` assumes (binary watches first); a conflict
//! whose literals are not both at the probe's level is not turned into a
//! unit and is counted in `backbone_stacked_guard_skips`.

use super::super::*;

/// Kissat `backbonerounds`: rounds per call while candidates remain.
const BACKBONE_STACKED_MAX_ROUNDS: usize = 100;
/// The wall cap of `backbone_binary`, kept.
const BACKBONE_STACKED_WALL_LIMIT_MS: u64 = 500;

impl Solver {
    /// Whether `backbone_binary` runs the stacked scheme: the test override,
    /// else `--sat-stacked-backbone`, else `--sat-inproc-nlogn-schedule`;
    /// never under LRAT, where the binary backbone learns nothing (see
    /// `backbone_binary_probe`).
    pub(in crate::solver) fn backbone_binary_stacked_enabled(&self) -> bool {
        !self.cold.lrat_enabled
            && self.cold.backbone_binary_stacked.unwrap_or_else(|| {
                let switches = ay_core::sat_ab_switches();
                switches
                    .stacked_backbone
                    .unwrap_or(switches.inproc_nlogn_schedule == Some(true))
            })
    }

    #[cfg(test)]
    pub(in crate::solver) fn set_backbone_binary_stacked(&mut self, on: bool) {
        self.cold.backbone_binary_stacked = Some(on);
    }

    /// The candidate literals in Kissat's order (`schedule_backbone_candidates`):
    /// the still-flagged ones first, then the rest.
    fn backbone_stacked_candidates(&mut self) -> Vec<Literal> {
        let n_lits = self.num_vars * 2;
        if self.cold.backbone_binary_candidate.len() < n_lits {
            self.cold.backbone_binary_candidate.resize(n_lits, true);
        }
        let mut flagged = Vec::new();
        let mut rest = Vec::new();
        for var_idx in 0..self.num_vars {
            if self.var_lifecycle.is_removed(var_idx) || self.var_is_assigned(var_idx) {
                continue;
            }
            let var = Variable(var_idx as u32);
            for lit in [Literal::positive(var), Literal::negative(var)] {
                if self.cold.backbone_binary_candidate[lit.index()] {
                    flagged.push(lit);
                } else {
                    rest.push(lit);
                }
            }
        }
        flagged.extend(rest);
        flagged
    }

    fn backbone_stacked_over_budget(
        &self,
        wall_start: ay_core::time::Instant,
        wall_start_ticks: u64,
        det: bool,
        work_start: u64,
    ) -> bool {
        if det {
            self.inproc_work_te().saturating_sub(work_start)
                >= crate::determinism::BACKBONE_BINARY_TICK_BUDGET
        } else {
            self.inproc_over_budget(
                wall_start,
                wall_start_ticks,
                BACKBONE_STACKED_WALL_LIMIT_MS,
                crate::determinism::BACKBONE_BINARY_TICK_BUDGET,
            )
        }
    }

    /// Kissat `compute_backbone`. Returns `true` when a unit was learned or
    /// the empty clause was derived.
    pub(in crate::solver) fn backbone_binary_stacked(&mut self) -> bool {
        debug_assert_eq!(self.qhead, self.trail.len());
        if !self.require_level_zero() || self.has_empty_clause {
            return false;
        }
        self.conflict.clear(&mut self.var_data);
        if let Some(conflict_ref) = self.search_propagate() {
            self.record_level0_conflict_chain(conflict_ref);
            return true;
        }
        let mut candidates = self.backbone_stacked_candidates();
        let wall_start = ay_core::time::Instant::now();
        let wall_start_ticks = self.total_search_ticks();
        let det = self.deterministic_inproc();
        let work_start = self.inproc_work_te();
        let mut found_any = false;
        let mut round = 0;
        while !candidates.is_empty()
            && round < BACKBONE_STACKED_MAX_ROUNDS
            && !self.has_empty_clause
        {
            round += 1;
            self.stats.backbone_stacked_rounds += 1;
            let mut kept: Vec<Literal> = Vec::with_capacity(candidates.len());
            let mut units: Vec<Literal> = Vec::new();
            let mut cut = false;
            for i in 0..candidates.len() {
                let probe = candidates[i];
                if i & 63 == 0
                    && (self.is_interrupted()
                        || self.backbone_stacked_over_budget(
                            wall_start,
                            wall_start_ticks,
                            det,
                            work_start,
                        ))
                {
                    kept.extend_from_slice(&candidates[i..]);
                    cut = true;
                    break;
                }
                let vi = probe.variable().index();
                if self.var_lifecycle.is_removed(vi) {
                    continue;
                }
                let val = self.lit_val(probe);
                if val > 0 {
                    // Satisfied by the stack: its closure lies inside a
                    // consistent one, so it is not a failed literal.
                    self.cold.backbone_binary_candidate[probe.index()] = false;
                    continue;
                }
                if val < 0 {
                    // Falsified by a decision: undecided, next round. At
                    // level 0 it is gone.
                    if self.var_data[vi].level > 0 {
                        kept.push(probe);
                    }
                    continue;
                }
                let level_before = self.decision_level;
                self.decide(probe);
                self.stats.backbone_stacked_probes += 1;
                let Some((clause_ref, lit_a, lit_b)) = self.backbone_binary_propagate() else {
                    // Consistent: the probe and its closure stay on the
                    // stack, and the probe is not a failed literal.
                    self.cold.backbone_binary_candidate[probe.index()] = false;
                    continue;
                };
                let probe_level = level_before + 1;
                let level_a = self.var_data[lit_a.variable().index()].level;
                let level_b = self.var_data[lit_b.variable().index()].level;
                let conflict_at_probe_level = level_a == probe_level && level_b == probe_level;
                let uip = self.backbone_binary_analyze(clause_ref, lit_a, lit_b);
                let uip_at_probe_level = self.var_data[uip.variable().index()].level == probe_level;
                self.backtrack_without_phase_saving(level_before);
                if !(conflict_at_probe_level && uip_at_probe_level) {
                    // The conflict reached below the probe: the closure was
                    // not complete here, and this is no unit. The counters
                    // say where it reached (schooltt-5-3 showed 60 of these
                    // in 3.1M probes, 2026-09-21): the falsified side at the
                    // root, on the stack, a dead clause still watched, or an
                    // analysis that left the level.
                    self.stats.backbone_stacked_guard_skips += 1;
                    let lower = level_a.min(level_b);
                    if lower == 0 {
                        self.stats.backbone_stacked_skip_other_root += 1;
                    } else if lower < probe_level {
                        self.stats.backbone_stacked_skip_other_stack += 1;
                    }
                    if self.arena.is_dead(clause_ref.0 as usize) {
                        self.stats.backbone_stacked_skip_dead_clause += 1;
                    }
                    if conflict_at_probe_level && !uip_at_probe_level {
                        self.stats.backbone_stacked_skip_uip_level += 1;
                    }
                    continue;
                }
                units.push(uip);
                self.stats.backbone_binary_units += 1;
                found_any = true;
                // Assert the unit on the stack (Kissat: `UNIT_REASON` at this
                // level). A conflict now means the binary clauses are
                // inconsistent at level 0, which the replay below reports.
                match self.lit_val(uip) {
                    0 => {
                        self.decide(uip);
                        if self.backbone_binary_propagate().is_some() {
                            break;
                        }
                    }
                    v if v < 0 => break,
                    _ => {}
                }
            }
            if self.decision_level > 0 {
                self.backtrack_without_phase_saving(0);
            }
            // Level-0 replay of the round's units through the ordinary
            // machinery (proof ids, UNSAT), as `backbone_binary_probe` does.
            for &unit in &units {
                if self.has_empty_clause {
                    break;
                }
                match self.lit_val(unit) {
                    v if v > 0 => self.backbone_materialize_unit(unit),
                    0 => {
                        self.learn_derived_unit(unit, &[]);
                        if self.backbone_binary_check_conflict() {
                            break;
                        }
                    }
                    _ => self.mark_empty_clause(),
                }
            }
            candidates = kept;
            if cut {
                break;
            }
        }
        // Kissat `keep_backbone_candidates`: when no remaining candidate is
        // still flagged, flag them all so the next call prioritizes them.
        if !candidates.is_empty()
            && !candidates
                .iter()
                .any(|lit| self.cold.backbone_binary_candidate[lit.index()])
        {
            for lit in &candidates {
                self.cold.backbone_binary_candidate[lit.index()] = true;
            }
        }
        if !self.has_empty_clause && self.qhead < self.trail.len() {
            if let Some(conflict_ref) = self.search_propagate() {
                self.record_level0_conflict_chain(conflict_ref);
            }
        }
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: backbone_binary_stacked() did not restore decision level to 0"
        );
        found_any || self.has_empty_clause
    }
}
