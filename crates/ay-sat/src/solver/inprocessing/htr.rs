// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Hyper ternary resolution (HTR).

use super::super::mutate::{AddResult, ReasonPolicy};
use super::super::*;

impl Solver {
    /// Run hyper-ternary resolution (wrapper: always reschedules).
    ///
    /// Returns true if binary resolvents were produced (caller should re-run
    /// decompose to exploit new binary implication graph edges).
    pub(in crate::solver) fn htr(&mut self) -> bool {
        let result = self.htr_body();
        self.inproc_ctrl
            .htr
            .reschedule(self.num_conflicts, HTR_INTERVAL);
        result
    }

    /// HTR body — early returns are safe; wrapper handles rescheduling.
    ///
    /// Resolves pairs of ternary clauses to produce binary or ternary resolvents.
    /// Reference: CaDiCaL `ternary.cpp`.
    ///
    /// This must be called at decision level 0 (after a restart) for correctness.
    fn htr_body(&mut self) -> bool {
        if !self.enter_inprocessing() {
            return false;
        }
        // See the BCE entry point: size the occurrence list on first use
        // rather than paying 128 B/var at solver construction.
        self.inproc.htr.ensure_num_vars(self.num_vars);
        // LRAT override handled centrally by InprocessingControls::with_proof_overrides().

        // Scale HTR resolvent limit with active variables.
        // CaDiCaL uses SET_EFFORT_LIMIT for ternary; fixed cap starves on large
        // formulas. Base: MAX_HTR_RESOLVENTS, scale: active_vars / 50.
        let active_vars = self
            .num_vars
            .saturating_sub(self.var_lifecycle.count_removed());
        let htr_limit = MAX_HTR_RESOLVENTS.max(active_vars / 50);

        // Run hyper-ternary resolution
        let result =
            self.inproc
                .htr
                .run_with_marks(&self.arena, &self.vals, htr_limit, &mut self.lit_marks);
        self.inproc
            .htr
            .set_last_search_ticks(self.search_ticks[0] + self.search_ticks[1]);

        let produced_binary = result.resolvents.iter().any(|(r, _, _)| r.len() == 2);
        let derived_base = result.derived_base;

        // First, add all new resolvents (for proof correctness).
        // For LRAT, track assigned clause IDs of ternary resolvents so that
        // multi-round HTR can reference earlier-round resolvents as antecedents (#4398).
        let mut derived_lrat_ids: Vec<u64> = Vec::new();
        for (resolvent, ante1, ante2) in &result.resolvents {
            // Build LRAT hints from antecedent clause IDs.
            let hints = if self.cold.lrat_enabled {
                let id1 = if *ante1 < derived_base {
                    self.clause_id(ClauseRef(*ante1 as u32))
                } else {
                    // Virtual derived ternary from earlier HTR round.
                    // Missing entry: io_failed prevented push in prior round (#4572).
                    // Invalid 0 is filtered by lrat_reverse_hints (#4577).
                    let di = *ante1 - derived_base;
                    derived_lrat_ids.get(di).copied().unwrap_or_default()
                };
                let id2 = if *ante2 < derived_base {
                    self.clause_id(ClauseRef(*ante2 as u32))
                } else {
                    let di = *ante2 - derived_base;
                    derived_lrat_ids.get(di).copied().unwrap_or_default()
                };
                // Filter out sentinel 0 from hints to avoid malformed LRAT
                // (#4577). Sentinel 0 occurs when emit_add returned Ok(0)
                // after I/O failure, or when a derived index is out of range.
                let raw_hints: Vec<u64> = [id1, id2].into_iter().filter(|&id| id != 0).collect();
                Self::lrat_reverse_hints(&raw_hints)
            } else {
                Vec::new()
            };

            // Log resolvent to proof and sync ID counter (#4398).
            // The manager may consume extra IDs for deletion flushes, so we
            // must sync next_clause_id before add_clause_watched calls
            // add_clause_db_checked (which uses next_clause_id independently).
            if let Ok(new_id) =
                self.proof_emit_add_prechecked(resolvent, &hints, ProofAddKind::Derived)
            {
                // Guard against io_failed sentinel Ok(0) -- see #4572.
                if self.cold.lrat_enabled && new_id != 0 {
                    self.cold.next_clause_id = new_id;
                    // Track LRAT IDs of ternary resolvents for multi-round reference.
                    if resolvent.len() == 3 {
                        derived_lrat_ids.push(new_id);
                    }
                }
            }

            let mut lits = resolvent.clone();
            let add_result = self.add_clause_watched(&mut lits);
            // CaDiCaL ternary.cpp: mark HTR resolvents for one-round
            // lifetime in reduce_db (reduce.cpp:116-120).
            match add_result {
                AddResult::Added(cref) | AddResult::Unit(cref) => {
                    let clause_idx = cref.0 as usize;
                    self.arena.set_hyper(clause_idx, true);
                    // Notify BVE occ lists of the new irredundant clause (#8096).
                    let new_lits = self.arena.literals(clause_idx).to_vec();
                    self.note_irredundant_clause_added_for_bve(clause_idx, &new_lits);
                }
                AddResult::Empty => {}
            }
        }

        // Then, delete antecedent clauses (those subsumed by binary resolvents)
        for clause_idx in &result.to_delete {
            // Notify BVE occ lists of irredundant clause removal (#8096).
            if !self.arena.is_learned(*clause_idx) {
                let old_lits = self.arena.literals(*clause_idx).to_vec();
                self.note_irredundant_clause_removed_for_bve(*clause_idx, &old_lits);
            }
            self.delete_clause_checked(*clause_idx, ReasonPolicy::Skip);
        }

        produced_binary
    }
}
