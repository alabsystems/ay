// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT sweeping (equivalence merging).
//!
//! Uses kitten sub-solver for COI-based sweep when available, falling back to
//! SCC-based sweep on binary clauses only.

use super::super::mutate::ReasonPolicy;
use super::super::*;
#[cfg(debug_assertions)]
use crate::kani_compat::DetHashSet as HashSet;

/// Sweep effort as per-mille of search ticks since last sweep call.
/// CaDiCaL: `sweepeffort = 100` (options.hpp). 100 per-mille = 10%.
/// Sweep-deepening default (B4: was AY_AB_SWEEP_DEEPEN; ships OFF).
const SWEEP_DEEPEN_DEFAULT: bool = false;
/// Min-effort floor when deepening (B4: was AY_AB_SWEEP_MINEFF).
#[allow(dead_code)]
const SWEEP_DEEPEN_MIN_EFFORT_FLOOR: u64 = 10_000_000;
const SWEEP_EFFORT_PERMILLE: u64 = 100;

/// Maximum sweep effort (ticks) per call.
/// CaDiCaL: `sweepmaxeff = 2e8` (options.hpp).
const SWEEP_MAX_EFFORT: u64 = 200_000_000;

/// Minimum sweep effort (ticks) per call.
/// CaDiCaL: `sweepmineff = 0` (options.hpp). Match CaDiCaL default.
/// On small formulas (battleship: 442 vars), the old 100K floor caused
/// 791ms of wasted sweep work per round (3 rounds × 0 rewrites = 2.4s
/// total). With 0, the proportional budget governs effort naturally.
const SWEEP_MIN_EFFORT: u64 = 0;

impl Solver {
    /// Run SAT sweeping (wrapper: reschedules with growing backoff).
    ///
    /// Uses growing backoff when unproductive (no rewrites): interval doubles
    /// per unproductive call, capped at SWEEP_MAX_INTERVAL. Productive calls
    /// reset to base interval (#7480 D5).
    ///
    /// Returns true if UNSAT was detected.
    pub(in crate::solver) fn sweep(&mut self) -> bool {
        let rewrites_before = self.inproc.sweeper.stats().clauses_rewritten;
        self.defer_stale_reason_cleanup = true;
        let result = self.sweep_body();
        self.defer_stale_reason_cleanup = false;
        self.clear_stale_reasons();
        let productive = self.inproc.sweeper.stats().clauses_rewritten > rewrites_before;
        if productive {
            // Productive: reset to base interval (CaDiCaL reduce_delay).
            self.inproc_ctrl
                .sweep
                .reschedule(self.num_conflicts, SWEEP_INTERVAL);
        } else {
            // Unproductive: growing backoff (CaDiCaL bump_delay).
            // CaDiCaL NEVER permanently disables sweep — it uses a Delay
            // mechanism (delay.hpp) where bump_delay() increments a skip
            // counter and reduce_delay() halves it on productive rounds.
            // AY matches via 2x interval growth up to SWEEP_MAX_INTERVAL.
            // On hard industrial formulas, sweep may find equivalences only
            // after BVE/vivify/decompose have simplified the formula through
            // several inprocessing rounds (#8450).
            //
            // Bug fix (#8448): when SWEEP_INTERVAL = 0, growing backoff
            // computes 0 * 2 = 0, so the interval never grows. Use
            // SWEEP_UNPRODUCTIVE_BACKOFF_FLOOR as the minimum growth base
            // to ensure actual backoff on unproductive rounds.
            self.inproc_ctrl.sweep.reschedule_growing(
                self.num_conflicts,
                SWEEP_UNPRODUCTIVE_BACKOFF_FLOOR,
                2,
                1,
                SWEEP_MAX_INTERVAL,
            );
        }
        result
    }

    /// Sweep body — early returns are safe; wrapper handles rescheduling.
    ///
    /// Uses kitten sub-solver to find backbone literals and literal equivalences
    /// from arbitrary clause neighborhoods (COI-based). Falls back to SCC-based
    /// sweep on binary clauses when kitten finds nothing.
    ///
    /// This must be called at decision level 0 (after a restart) for correctness.
    fn sweep_body(&mut self) -> bool {
        if !self.require_level_zero() {
            return false;
        }

        // Defense-in-depth: sweep uses push_sweep reconstruction, so it must
        // not fire in incremental mode even if re-enabled via set_sweep_enabled.
        // Matches condition()/decompose() (#3662).
        //
        // Migration (#8162 Part A step 1): superset-OR with in_scoped_mode().
        if self.in_scoped_mode() || self.cold.has_been_incremental {
            return false;
        }
        // Sweep substitutes and deletes irredundant clauses — maintained
        // incrementally via apply_decompose_mutation's BVE occ hooks (#8096).

        #[cfg(debug_assertions)]
        let recon_steps_before = self.inproc.reconstruction.len();

        // LRAT override handled centrally by inproc_ctrl.with_proof_overrides() (#4557).

        // Proportional sweep effort (CaDiCaL sweep.cpp pattern).
        // Budget = SWEEP_EFFORT_PERMILLE / 1000 * (ticks_since_last_sweep),
        // clamped to [SWEEP_MIN_EFFORT, SWEEP_MAX_EFFORT].
        //
        // First-call initial budget (#9215): when search_ticks are zero (e.g.,
        // during preprocessing or the first inprocessing round), the proportional
        // calculation yields zero ticks, causing sweep to exit immediately without
        // probing any variables. CaDiCaL's sweep fires during preprocessing with
        // a fixed initial effort. On shuffling-2, Kissat's first sweep solves
        // 1824 vars — the critical technique that enables SAT in 784 conflicts.
        // Scale initial budget by formula size (#8448): on stable-300 (300
        // vars, density 58), 200M ticks takes 10+ seconds of kitten probing
        // with zero rewrites. Use num_vars * 1000 capped at SWEEP_MAX_EFFORT.
        // For shuffling-2 (138K vars) this gives 138M; for stable-300, 300K.
        let total_ticks = self.search_ticks[0] + self.search_ticks[1];
        let delta_ticks = total_ticks.saturating_sub(self.cold.last_sweep_ticks);
        self.cold.last_sweep_ticks = total_ticks;
        let raw_effort = delta_ticks * SWEEP_EFFORT_PERMILLE / 1000;
        // First-call initial budget (#8448): detect the first sweep call by
        // checking round count instead of total_ticks==0, because init_solve's
        // BCP can accumulate a few search_ticks before preprocessing runs,
        // causing total_ticks>0 and the old check to fall through to a tiny
        // proportional budget (e.g., 3 ticks instead of 138M). On shuffling-2,
        // the 3-tick budget meant kitten could not even solve one COI
        // environment. Fix: use sweeper round count as the first-call detector.
        // First-call budget (#8448): use sweeper round count as first-call
        // detector (not total_ticks==0), because init_solve's BCP can
        // accumulate search_ticks before preprocessing runs.
        //
        // Budget scaling: Kissat's sweep on shuffling-2 (138K vars) uses only
        // 1M kitten_ticks and 0.15s wall time, finding 0 equivalences but
        // probing 452 variables. AY's initial vars*1000 budget (138M ticks)
        // caused 6.5s of sweep, delaying search fatally. Cap at 2M for the
        // first call -- enough to probe hundreds of variables but bounded
        // enough to not starve search.
        let is_first_sweep = self.inproc.sweeper.stats().rounds == 0;
        let first_call_budget = if is_first_sweep {
            let vars = self.num_vars as u64;
            // Cap first-call budget: Kissat uses ~1M ticks on shuffling-2.
            // Use vars*10 capped at 2M to scale with formula size while
            // keeping a tight bound for large formulas.
            (vars * 10).min(2_000_000)
        } else {
            0
        };

        // ── Sweep-deepening lever (B4: env reads deleted; constants) ────────
        // AY's SWEEP_MIN_EFFORT is 0, so on large formulas the proportional
        // budget (10% of Δsearch_ticks) plus the ≤2M first-call cap probe only
        // ~0.03–0.28% of variables per call. kissat clamps its sweep effort to
        // a floor of ~1M–10M ticks, letting each call probe far more variables.
        // Under the lever, raise the per-call floor (default 10M) so — with the
        // persistent cursor in sweep_with_kitten — coverage actually deepens.
        // The lever ships OFF; flipping it belongs to a priced batch via a
        // typed option, not an env var nothing sets (B8 in the migration spec).
        let deepen = SWEEP_DEEPEN_DEFAULT;
        let min_effort_floor = if deepen {
            SWEEP_DEEPEN_MIN_EFFORT_FLOOR
        } else {
            SWEEP_MIN_EFFORT
        };
        // OFF: min_effort_floor == SWEEP_MIN_EFFORT (0), so this reduces to the
        // original `.max(first_call_budget).clamp(0, SWEEP_MAX_EFFORT)`. Using
        // .min last (rather than clamp) is panic-safe even if the env floor is
        // set above SWEEP_MAX_EFFORT.
        let sweep_budget = raw_effort
            .max(first_call_budget)
            .max(min_effort_floor)
            .min(SWEEP_MAX_EFFORT);

        // Run kitten-based sweep (COI + backbone + equivalence probing).
        let outcome = self.inproc.sweeper.sweep_with_kitten(
            &self.arena,
            &self.vals,
            &self.cold.freeze_counts,
            sweep_budget,
        );

        if outcome.unsat {
            // Kitten proved UNSAT on a COI subset. In proof mode, we cannot
            // derive an empty clause directly from kitten's internal proof
            // (kitten doesn't produce DRAT steps). Let normal search re-derive
            // the empty clause with a proper proof chain.
            if self.proof_manager.is_some() {
                return false;
            }
            self.mark_empty_clause();
            #[cfg(debug_assertions)]
            {
                let recon_steps_after = self.inproc.reconstruction.len();
                debug_assert_eq!(
                    recon_steps_after, recon_steps_before,
                    "BUG: sweep() added reconstruction steps on UNSAT path"
                );
            }
            debug_assert!(
                self.has_empty_clause,
                "BUG: sweep() returned UNSAT without setting has_empty_clause"
            );
            debug_assert_eq!(
                self.decision_level, 0,
                "BUG: sweep() did not restore decision level to 0"
            );
            return true;
        }

        // Check if any variable was actually merged (not identity mapping)
        let has_merges = !outcome.lit_map.is_empty()
            && outcome
                .lit_map
                .iter()
                .enumerate()
                .any(|(idx, &mapped)| mapped.index() != idx);

        // Short-circuit: if no equivalences found and no units, skip all
        // expensive work. This is critical for random 3-SAT where sweep
        // finds nothing but rebuild_watches() costs O(clauses).
        if !has_merges && outcome.new_units.is_empty() {
            #[cfg(debug_assertions)]
            {
                let recon_steps_after = self.inproc.reconstruction.len();
                debug_assert_eq!(
                    recon_steps_after, recon_steps_before,
                    "BUG: sweep() added reconstruction steps without merges"
                );
            }
            debug_assert_eq!(
                self.decision_level, 0,
                "BUG: sweep() did not restore decision level to 0"
            );
            return false;
        }

        // Record the equivalence mapping for reconstruction if non-trivial.
        // Convert internal lit_map to external index space (#5250).
        if has_merges {
            let ext_num_vars = self.cold.e2i.len();
            let mut ext_lit_map = vec![Literal(0); ext_num_vars * 2];
            for ext_var in 0..ext_num_vars {
                let ext_pos = Literal::positive(Variable(ext_var as u32));
                let ext_neg = Literal::negative(Variable(ext_var as u32));
                let int_var = self.cold.e2i[ext_var];
                if int_var == compact::UNMAPPED || (int_var as usize) >= self.num_vars {
                    // Compacted-away or out-of-range: identity map
                    ext_lit_map[ext_pos.index()] = ext_pos;
                    ext_lit_map[ext_neg.index()] = ext_neg;
                } else {
                    let int_pos = Literal::positive(Variable(int_var));
                    let int_neg = Literal::negative(Variable(int_var));
                    if int_pos.index() < outcome.lit_map.len() {
                        ext_lit_map[ext_pos.index()] =
                            self.externalize(outcome.lit_map[int_pos.index()]);
                        ext_lit_map[ext_neg.index()] =
                            self.externalize(outcome.lit_map[int_neg.index()]);
                    } else {
                        ext_lit_map[ext_pos.index()] = ext_pos;
                        ext_lit_map[ext_neg.index()] = ext_neg;
                    }
                }
            }
            self.inproc
                .reconstruction
                .push_sweep(ext_num_vars, ext_lit_map);
        }

        // Phase 3 (#7037): Apply equivalences to the clause arena.
        // CaDiCaL sweep.cpp:1697-1698 substitutes immediately after each variable.
        // AY batches: rewrite all clauses after collecting all equivalences.
        // Previously, AY recorded equivalences for reconstruction but NEVER
        // rewrote clauses, making sweep a no-op for search simplification and
        // corrupting models via reconstruction of non-existent substitutions.
        if has_merges {
            use crate::decompose::rewrite_clauses;

            let rewrite = rewrite_clauses(&self.arena, &outcome.lit_map, &self.vals);

            if rewrite.is_unsat {
                // Sweep-derived UNSAT from clause rewriting (empty clause after
                // substitution). In proof mode, let normal search re-derive it.
                if self.proof_manager.is_some() {
                    return false;
                }
                self.mark_empty_clause();
                return true;
            }

            // ── DRAT proof emission for clause mutations (#7913) ─────────
            //
            // Two-phase emission mirroring decompose's pattern:
            //   Phase 1: emit all ADD proof steps (new clauses are RUP)
            //   Phase 2: emit all DELETE proof steps (remove old clauses)
            //
            // Sweep equivalences are proved by kitten on a COI subset. By
            // monotonicity, any clause derivable from a subset is derivable
            // from the full formula. The rewritten clauses are RUP: they
            // follow from the original clause plus the equivalence a ≡ b
            // (which itself is RUP because each implication direction was
            // UNSAT on the COI subset).
            //
            // In DRAT mode, no explicit hints are needed — the DRAT checker
            // verifies RUP automatically via reverse unit propagation.
            // CaDiCaL sweep.cpp:1127-1168 emits add_derived_clause +
            // delete_clause for each substituted clause.
            if self.proof_manager.is_some() {
                // Pre-compute clause IDs before borrowing proof_manager mutably.
                let mutation_ids: Vec<u64> = rewrite
                    .actions
                    .iter()
                    .map(|m| {
                        let ci = match m {
                            crate::decompose::ClauseMutation::Deleted { clause_idx, .. }
                            | crate::decompose::ClauseMutation::Replaced { clause_idx, .. }
                            | crate::decompose::ClauseMutation::Unit { clause_idx, .. } => {
                                *clause_idx
                            }
                        };
                        self.clause_id(ClauseRef(ci as u32))
                    })
                    .collect();

                // Phase 1: emit all ADD steps while original formula is intact.
                // CaDiCaL sweep.cpp:1127-1152.
                let mut unit_pids: Vec<(Literal, u64)> = Vec::new();
                for (mutation, &cid) in rewrite.actions.iter().zip(mutation_ids.iter()) {
                    match mutation {
                        crate::decompose::ClauseMutation::Replaced {
                            new, clause_idx, ..
                        } => {
                            // In DRAT mode, the rewritten clause is RUP: it
                            // follows from the original clause (with one literal
                            // substituted by its equivalent representative).
                            // If the original clause has a proof ID, use it as
                            // the sole hint for better checker performance.
                            let hints: Vec<u64> = if cid != 0 { vec![cid] } else { Vec::new() };
                            let kind = if hints.is_empty() {
                                ProofAddKind::TrustedTransform
                            } else {
                                ProofAddKind::Derived
                            };
                            let new_id = self.proof_emit_add(new, &hints, kind).unwrap_or(0);
                            // Update clause_ids so later deletions use the new
                            // proof ID, not the stale original.
                            if new_id != 0 && *clause_idx < self.cold.clause_ids.len() {
                                self.cold.clause_ids[*clause_idx] = new_id;
                            }
                        }
                        crate::decompose::ClauseMutation::Unit { unit, .. } => {
                            let hints: Vec<u64> = if cid != 0 { vec![cid] } else { Vec::new() };
                            let kind = if hints.is_empty() {
                                ProofAddKind::TrustedTransform
                            } else {
                                ProofAddKind::Derived
                            };
                            let pid = self.proof_emit_unit(*unit, &hints, kind);
                            if pid != 0 {
                                unit_pids.push((*unit, pid));
                            }
                        }
                        crate::decompose::ClauseMutation::Deleted { .. } => {}
                    }
                }

                // Phase 2: emit all DELETE steps.
                for (mutation, &cid) in rewrite.actions.iter().zip(mutation_ids.iter()) {
                    match mutation {
                        crate::decompose::ClauseMutation::Deleted { old, .. }
                        | crate::decompose::ClauseMutation::Replaced { old, .. }
                        | crate::decompose::ClauseMutation::Unit { old, .. } => {
                            let _ = self.proof_emit_delete(old, cid);
                        }
                    }
                }

                // Apply deferred unit_proof_id stores.
                for (unit, pid) in unit_pids {
                    self.record_unit_proof_id_for_lit(unit, pid);
                }
            }

            // Apply clause mutations (delete tautologies, replace shortened).
            // Reuses the same mutation protocol as decompose (#3440).
            for action in &rewrite.actions {
                self.apply_decompose_mutation(action);
            }
            self.cold.clause_db_changes +=
                u64::from(rewrite.removed) + u64::from(rewrite.shortened);

            // Enqueue rewrite-derived units with contradiction detection.
            // CaDiCaL sweep.cpp:1210-1217: checks if both a literal and its
            // negation become units → learn_empty_clause().
            for unit in &rewrite.new_units {
                let vi = unit.variable().index();
                if let Some(val) = self.var_value_from_vals(vi) {
                    if val != unit.is_positive() {
                        // Contradicting unit: formula is UNSAT.
                        // In proof mode, let BCP derive the conflict with a
                        // proper proof chain (#4596).
                        if self.proof_manager.is_some() {
                            return false;
                        }
                        self.mark_empty_clause();
                        return true;
                    }
                    // Same polarity: already assigned, skip.
                } else if !self.var_lifecycle.is_inactive(vi) {
                    self.enqueue(*unit, None);
                    self.fixed_count += 1;
                    self.var_lifecycle.mark_fixed(vi);
                    self.l0_gc_dirty[vi] = true;
                }
            }

            // Mark substituted variables: remove from VSIDS heap so the solver
            // doesn't waste decisions on variables that no longer appear in clauses.
            // CaDiCaL: sweep.cpp via mark_substituted after substitution.
            for var_idx in 0..self.num_vars {
                let pos = Literal::positive(Variable(var_idx as u32));
                if pos.index() >= outcome.lit_map.len() {
                    continue;
                }
                let repr = outcome.lit_map[pos.index()];
                if repr == pos {
                    continue; // self-representative
                }
                if self.var_lifecycle.is_removed(var_idx) || self.var_lifecycle.is_fixed(var_idx) {
                    continue;
                }
                let repr_var = repr.variable().index();
                if repr_var < self.num_vars && self.var_is_assigned(repr_var) {
                    continue;
                }
                self.var_lifecycle.mark_substituted(var_idx);
                self.inproc.bve.mark_removed_external(var_idx);
                self.vsids.remove_from_heap(Variable(var_idx as u32));
            }

            // GC clauses containing removed (eliminated/substituted) variables
            // (#8464, #5149).
            //
            // rewrite_clauses rewrites non-garbage clauses whose literals have
            // changed representatives in the sweep reprs map. However, variables
            // eliminated by BVE (or marked substituted by earlier passes) are
            // self-representative in the sweep reprs map, so rewrite_clauses
            // does NOT flag their clauses for rewriting. Any surviving clause
            // with such a variable would reach compact() with an unmapped
            // literal, triggering a panic.
            //
            // Scan ALL active clauses (learned + irredundant) — matching
            // decompose's comprehensive GC at decompose.rs:589-604.
            // Previously this only scanned learned + garbage irredundant,
            // trusting rewrite_clauses for live irredundant. That left a gap
            // for irredundant clauses with BVE-eliminated variables not in
            // the sweep equivalence map.
            // Reuse persistent buffer to avoid arena-proportional allocation (#8602).
            self.cold.reduce_indices_buf.clear();
            self.cold.reduce_indices_buf.extend(self.arena.indices());
            for i in 0..self.cold.reduce_indices_buf.len() {
                let idx = self.cold.reduce_indices_buf[i];
                if self.arena.is_empty_clause(idx) || !self.arena.is_active(idx) {
                    continue;
                }
                let has_removed = self
                    .arena
                    .literals(idx)
                    .iter()
                    .any(|lit| self.var_lifecycle.is_removed(lit.variable().index()));
                if has_removed {
                    self.delete_clause_checked(idx, ReasonPolicy::ClearLevel0);
                }
            }
        }

        // Finalize incrementally-maintained watches (#8093). Clause mutations
        // updated watches eagerly inside apply_decompose_mutation(). The
        // blocker-staleness issue (OOB panic from stale watcher blockers) is
        // now resolved by the incremental detach/attach in the mutation helper.
        if has_merges {
            // Sweep rewrites clause literals (variable substitution), so full
            // re-propagation from position 0 is needed (#8095).
            self.mark_trail_affected(0);
            self.finalize_incremental_watches();
        }

        // Process backbone units derived from kitten probing.
        // Guard: skip variables already substituted/removed/fixed by the equivalence
        // processing above — enqueue_derived_unit calls mark_fixed which requires Active state.
        //
        // Track units skipped due to proof-mode RUP failure so the post-condition
        // assertion doesn't fire on legitimately skipped backbone literals (#8116).
        #[cfg(debug_assertions)]
        let mut proof_skipped_units = HashSet::default();
        for &unit_lit in &outcome.new_units {
            let vi = unit_lit.variable().index();
            if !self.var_is_assigned(vi)
                && !self.var_lifecycle.is_removed(vi)
                && !self.var_lifecycle.is_fixed(vi)
            {
                let hints = self.collect_rup_unit_lrat_hints(unit_lit);
                if self.has_empty_clause {
                    return false;
                }
                // DRAT has no explicit hint channel for kitten-derived backbone
                // units, so proof mode must only keep units that can be replayed
                // as direct RUP under `¬unit`.
                if hints.is_empty() && self.proof_manager.is_some() {
                    if !self.is_rup_unit_under_negation(unit_lit) {
                        #[cfg(debug_assertions)]
                        proof_skipped_units.insert(vi);
                        continue;
                    }
                    if self.has_empty_clause {
                        return false;
                    }
                }
                // Hint collection / RUP probing can drain pending level-0 BCP
                // and assign the unit as a side effect. Re-check before
                // enqueue_derived_unit, which requires an unassigned variable.
                if self.var_is_assigned(vi)
                    || self.var_lifecycle.is_removed(vi)
                    || self.var_lifecycle.is_fixed(vi)
                {
                    continue;
                }
                self.enqueue_derived_unit(unit_lit, &hints);
            }
        }

        // Final watch finalization: backbone unit processing above may add new
        // unit clauses (via enqueue_derived_unit) that need watch integration,
        // and the RUP probing can modify watch state via BCP. Finalize once
        // more to ensure qhead is correctly positioned for re-propagation.
        if has_merges {
            // Sweep substitution already marked position 0 above; this second
            // finalization inherits that (#8095).
            self.mark_trail_affected(0);
            self.finalize_incremental_watches();
        }

        #[cfg(debug_assertions)]
        {
            let recon_steps_after = self.inproc.reconstruction.len();
            // push_sweep now emits per-equivalence binary witness entries
            // (2 per non-identity mapping). At minimum, if has_merges is true,
            // we expect some new entries.
            if has_merges {
                debug_assert!(
                    recon_steps_after > recon_steps_before,
                    "BUG: sweep() with merges added no reconstruction entries"
                );
            } else {
                debug_assert_eq!(
                    recon_steps_after, recon_steps_before,
                    "BUG: sweep() without merges added reconstruction entries"
                );
            }

            // Post-condition: each newly derived unit literal must now be assigned
            // OR belong to a variable that was substituted/removed by equivalence
            // processing OR was intentionally skipped because it could not be
            // justified via RUP in proof mode (#8116).
            for &unit_lit in &outcome.new_units {
                let var_idx = unit_lit.variable().index();
                debug_assert!(
                    self.var_is_assigned(var_idx)
                        || self.var_lifecycle.is_removed(var_idx)
                        || self.var_lifecycle.is_fixed(var_idx)
                        || proof_skipped_units.contains(&var_idx),
                    "BUG: sweep() left derived unit {unit_lit:?} unassigned \
                     (removed={}, fixed={}, proof_skipped={})",
                    self.var_lifecycle.is_removed(var_idx),
                    self.var_lifecycle.is_fixed(var_idx),
                    proof_skipped_units.contains(&var_idx),
                );
            }
        }
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: sweep() did not restore decision level to 0"
        );

        false
    }
}
