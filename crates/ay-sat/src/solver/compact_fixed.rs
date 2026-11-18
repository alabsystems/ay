// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--sat-compact-fixed`: variable compaction also removes root-fixed
//! variables.
//!
//! By default compaction (compact.rs) renumbers away eliminated and
//! substituted variables only, so every variable fixed at the root keeps its
//! slot in every per-variable and per-literal table and its entry on the
//! level-0 trail: about three million of them on b54b26f3 and 180e6d8b, 6.8
//! million on e85fb114. CaDiCaL counts fixed variables as inactive
//! (`active ()`, internal.hpp:363-379; `compacting ()`, compact.cpp:13-27),
//! and so does Kissat (flags.c:36-48, collect.c:633-643). Both drop them
//! when they compact.
//!
//! Both keep one fixed variable as a representative for all the others:
//! CaDiCaL maps every fixed literal to plus or minus `first_fixed`
//! (compact.cpp:31-101), and Kissat re-imports every fixed external
//! variable onto one literal (compact.c:19-95, 275-288). That needs signed
//! external maps, and AY's `e2i` maps variables. AY instead drops a
//! root-fixed variable only once NO arena clause mentions it, and it keeps
//! no representative:
//!
//! * `compact_with_fixed` first runs the level-0 collection to its fixpoint,
//!   bypassing the collection's fixed-count guard. That guard does not see
//!   units derived later in the round or clauses created since the last
//!   sweep. The collection deletes root-satisfied clauses and strips
//!   root-false literals with its usual proof lines, as CaDiCaL's
//!   `garbage_collection ()` does before `compact ()` (collect.cpp:73-90).
//! * `droppable_fixed_vars` picks the root-fixed variables that no arena
//!   clause mentions, husks included. A clause the collection could not
//!   clean (a refused deletion, a garbage-kept husk) keeps its variables, so
//!   correctness never depends on the collection being complete.
//! * A variable's own root-true unit clause does not keep it. Compaction
//!   removes that clause from the arena and logs no proof deletion: neither
//!   reference solver ever deletes a unit from a DRAT proof, and no
//!   remaining clause mentions the variable, so the unit is inert in the
//!   checker.
//! * A dropped variable's `e2i` entry becomes `UNMAPPED`, and compaction
//!   saves its root value in `eliminated_ext_vals` (Phase 4b). That is where
//!   `finalize_sat_model` and `extend_dumped_model` already read every
//!   compacted variable from, so a model keeps every fixed external value.
//!
//! The proof needs nothing new. No clause mentions a dropped variable, so no
//! later proof line does either. A line that mentions a kept variable is
//! externalized through `i2e`, as after any compaction. LRAT, clause traces
//! and the backward-proof mode never compact (`compacting`).
//!
//! The switch applies only to a solver that may remove variables
//! (`compact_fixed_active`). Default compaction needs removed variables, so
//! a solver with BVE, decompose, sweep and congruence all off never
//! compacts. Extension and theory solves are such solvers
//! (`disable_extension_inprocessing`), and the CP and XOR extensions keep
//! internal variable indices across the search without freezing them.

use super::compact::{VariableMap, COMPACT_INTERVAL_BASE, UNMAPPED};
use super::*;
use crate::literal::Literal;

impl Solver {
    /// Whether `--sat-compact-fixed` applies: the switch is on, the solve is
    /// one-shot (the DIMACS route: no assumptions, no second solve, no
    /// extension or theory backend; embedders such as the CP engine and the
    /// XOR extension never set it, and a second solve would rebuild the
    /// arena from the original ledger in uncompacted numbering), and one of
    /// the passes that remove variables (BVE, decompose, sweep, congruence)
    /// is enabled, so default compaction can already renumber this solver.
    pub(super) fn compact_fixed_active(&self) -> bool {
        self.cold.compact_fixed
            && self.cold.symmetry_oneshot
            && (self.inproc_ctrl.bve.enabled
                || self.inproc_ctrl.decompose.enabled
                || self.inproc_ctrl.sweep.enabled
                || self.inproc_ctrl.congruence.enabled)
    }

    /// Root-assigned variables that are not already eliminated or
    /// substituted: the fixed variables `--sat-compact-fixed` counts as
    /// inactive. At level 0 the trail holds exactly the root assignments.
    pub(super) fn count_root_fixed_unremoved(&self) -> usize {
        debug_assert_eq!(self.decision_level, 0);
        self.trail
            .iter()
            .filter(|lit| !self.var_lifecycle.is_removed(lit.variable().index()))
            .count()
    }

    /// The compaction step of an inprocessing round under
    /// `--sat-compact-fixed`. Returns `true` when the formula is UNSAT.
    pub(super) fn compact_with_fixed(&mut self) -> bool {
        // Force a complete level-0 collection. The fixed-unit counter never
        // equals -1, so the collection's fixpoint guard cannot skip it. If
        // the collection returns before a complete sweep, the guard gets its
        // old value back.
        let guard = self.cold.last_collect_fixed;
        self.cold.last_collect_fixed = -1;
        let unsat = self.collect_level0_garbage();
        if self.cold.last_collect_fixed == -1 {
            self.cold.last_collect_fixed = guard;
        }
        if unsat || self.propagate_check_unsat() {
            return true;
        }
        let (compactions, vars_before, root_trail_before) =
            (self.cold.compact_count, self.num_vars, self.trail.len());
        self.compact();
        tracing::debug!(
            vars_before,
            vars_after = self.num_vars,
            root_trail_before,
            root_trail_after = self.trail.len(),
            "compact: --sat-compact-fixed"
        );
        if self.cold.compact_count == compactions {
            // Every fixed variable is still in some clause. Wait out
            // CaDiCaL's interval (compact.cpp:540-541) before trying again.
            let delta = COMPACT_INTERVAL_BASE.saturating_mul(self.cold.compact_count + 1);
            self.cold.compact_next_conflict = self.num_conflicts.saturating_add(delta);
        }
        false
    }

    /// For each variable, whether compaction may drop it as root-fixed. The
    /// variable must be assigned at the root, must not be removed already
    /// (removed variables are dropped anyway), and no arena clause may
    /// mention it except its own root-true unit clause. Husks count, because
    /// they keep their literal data and compaction renumbers them too.
    pub(super) fn droppable_fixed_vars(&self) -> Vec<bool> {
        debug_assert_eq!(self.decision_level, 0);
        let mut droppable = vec![false; self.num_vars];
        for lit in &self.trail {
            let var = lit.variable().index();
            if !self.var_lifecycle.is_removed(var) {
                droppable[var] = true;
            }
        }
        for idx in self.arena.active_indices() {
            if self.is_root_true_unit_clause(idx) {
                continue;
            }
            for lit in self.arena.literals(idx) {
                if let Some(slot) = droppable.get_mut(lit.variable().index()) {
                    *slot = false;
                }
            }
        }
        // Never leave an empty variable space. When every other variable
        // would go, the first fixed one stays, as CaDiCaL always keeps one
        // fixed representative (compact.cpp:57-63).
        let survivor =
            (0..self.num_vars).any(|var| !droppable[var] && !self.var_lifecycle.is_removed(var));
        if !survivor {
            if let Some(first) = droppable.iter().position(|&drop| drop) {
                droppable[first] = false;
            }
        }
        droppable
    }

    /// A live unit clause whose literal is true at the root.
    fn is_root_true_unit_clause(&self, idx: usize) -> bool {
        let lits = self.arena.literals(idx);
        lits.len() == 1
            && self.lit_val(lits[0]) > 0
            && !self.arena.is_garbage_any(idx)
            && !self.is_pending_theory_conflict_clause(idx)
    }

    /// Remove the root-true unit clauses of the root-fixed variables `map`
    /// drops, with no proof deletion (module docs). A unit clause has no
    /// watches and is never a reason (it is enqueued with none), so the
    /// arena is the only place to remove it from.
    pub(super) fn drop_fixed_unit_clauses(&mut self, map: &VariableMap) {
        let units: Vec<usize> = self
            .arena
            .active_indices()
            .filter(|&idx| {
                if !self.is_root_true_unit_clause(idx) {
                    return false;
                }
                let var = self.arena.literal(idx, 0).variable().index();
                map.map_var(var).is_none() && !self.var_lifecycle.is_removed(var)
            })
            .collect();
        for idx in units {
            self.stats.clear_bcp_learned_1963_blocker_cert(idx);
            self.record_clause_retirement(idx);
            self.note_direct_arena_delete(idx);
            self.arena.delete(idx);
            self.cold.clause_db_changes += 1;
        }
    }

    /// Run just before compaction replaces the trail. Two trail positions
    /// are stored outside the trail: the minimal-rewind mark (#8095) and the
    /// end of the conflict-free prefix. This moves both onto the compacted
    /// trail. Dropped variables leave the trail, so an old position can lie
    /// past its new end. A rewind to such a position would set `qhead` past
    /// literals enqueued later, and BCP would never propagate them.
    pub(super) fn remap_trail_marks_for_compaction(&mut self, map: &VariableMap) {
        let kept_before = |trail: &[Literal], pos: usize| {
            trail[..pos.min(trail.len())]
                .iter()
                .filter(|lit| map.map_lit(**lit).is_some())
                .count()
        };
        if let Some(pos) = self.earliest_affected_trail_pos {
            self.earliest_affected_trail_pos = Some(kept_before(self.trail.as_slice(), pos));
        }
        self.no_conflict_until = kept_before(self.trail.as_slice(), self.no_conflict_until);
    }

    /// The end of a compaction under `--sat-compact-fixed`: the state the
    /// renumbering leaves stale.
    pub(super) fn finish_fixed_compaction(&mut self, map: &VariableMap) {
        // Phase 7 rebuilt the lifecycle with every variable Active. Root
        // assignments that were kept are Fixed again (CaDiCaL
        // flags.cpp:5-21), so `count_active` and the target and best
        // recounts skip them.
        for lit in &self.trail {
            let var = lit.variable().index();
            if !self.var_lifecycle.is_inactive(var) {
                self.var_lifecycle.mark_fixed(var);
            }
        }
        // The clause reason marks still name the reasons of dropped variables.
        self.invalidate_reason_clause_marks();
        // Extension variables are the indices from this boundary on. The map
        // is monotone, so the new boundary is the number of kept variables
        // below the old one.
        let first = self.cold.first_extension_var_index;
        if first != usize::MAX {
            let end = first.min(map.old_to_new.len());
            self.cold.first_extension_var_index = map.old_to_new[..end]
                .iter()
                .filter(|&&new| new != UNMAPPED)
                .count();
        }
    }
}
