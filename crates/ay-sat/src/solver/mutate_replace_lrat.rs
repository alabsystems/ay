// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LRAT hint computation for clause replacement.
//!
//! Contains `replace_clause_impl` (computes LRAT hint chains from level-0
//! reason graphs) and `collect_level0_reason_chain` (BFS transitive closure
//! over level-0 variables for explicit hint construction).
//!
//! Extracted from `mutate_replace.rs` to keep each file under 500 lines.
//! The core replacement API (wrappers, `replace_clause_core`) remains in
//! `mutate_replace.rs`.

use super::*;
use crate::solver::mutate::ReplaceResult;

impl Solver {
    /// Collect transitive level-0 reason chain for LRAT hint construction.
    ///
    /// BFS through level-0 reason clauses starting from `seed_vars`, excluding
    /// variables in `exclude_vars` (which are already in the new clause). Returns
    /// proof IDs in trail-forward order (LRAT checker processing order).
    ///
    /// CaDiCaL reference: elim.cpp:303-308,349-350 (#5026).
    pub(super) fn collect_level0_reason_chain(
        &mut self,
        seed_vars: &[usize],
        exclude_vars: &[usize],
    ) -> Vec<u64> {
        if !self.cold.lrat_enabled {
            return Vec::new();
        }
        let num_vars = self.num_vars;
        debug_assert!(self.min.lrat_to_clear.is_empty());

        // Mark excluded variables (in new clause — checker already knows them).
        for &vi in exclude_vars {
            if vi < num_vars {
                self.min.minimize_flags[vi] |= LRAT_B;
            }
        }

        // Phase 1: Seed the BFS with the given variables.
        for &vi in seed_vars {
            if vi < num_vars
                && self.var_data[vi].level == 0
                && self.has_any_proof_id(vi)
                && self.min.minimize_flags[vi] & (LRAT_A | LRAT_B) == 0
            {
                self.min.minimize_flags[vi] |= LRAT_A;
                self.min.lrat_to_clear.push(vi);
            }
        }

        // Phase 2: BFS transitive closure on level-0 variables.
        let mut head = 0;
        while head < self.min.lrat_to_clear.len() {
            let vi = self.min.lrat_to_clear[head];
            head += 1;
            let Some(reason_ref) = self.var_reason(vi) else {
                continue;
            };
            let ci = reason_ref.0 as usize;
            if ci >= self.arena.len() {
                continue;
            }
            let clen = self.arena.len_of(ci);
            for li in 0..clen {
                let rl = self.arena.literal(ci, li);
                let rv = rl.variable().index();
                if rv != vi
                    && rv < num_vars
                    && self.var_data[rv].level == 0
                    && self.min.minimize_flags[rv] & (LRAT_A | LRAT_B) == 0
                    && self.has_any_proof_id(rv)
                {
                    self.min.minimize_flags[rv] |= LRAT_A;
                    self.min.lrat_to_clear.push(rv);
                }
            }
        }

        // Phase 3: Collect proof IDs in trail-forward order (LRAT checker
        // processing order). Earlier trail variables are dependencies of later
        // ones, so they must appear first in the hint chain.
        let mut hints = Vec::new();
        let level0_end = self.trail_lim.first().copied().unwrap_or(self.trail.len());
        for i in 0..level0_end {
            let lit = self.trail[i];
            let var_idx = lit.variable().index();
            if var_idx < num_vars && self.min.minimize_flags[var_idx] & LRAT_A != 0 {
                if let Some(id) = self.level0_var_proof_id(var_idx) {
                    Self::push_lrat_hint(&mut hints, id);
                }
            }
        }

        // Sparse cleanup.
        for &idx in &self.min.lrat_to_clear {
            self.min.minimize_flags[idx] &= !LRAT_A;
        }
        self.min.lrat_to_clear.clear();
        for &vi in exclude_vars {
            if vi < num_vars {
                self.min.minimize_flags[vi] &= !LRAT_B;
            }
        }

        hints
    }

    pub(super) fn replace_clause_impl(
        &mut self,
        clause_idx: usize,
        new_lits: &[Literal],
        extra_lrat_hints: &[u64],
        explicit_only: bool,
        proof_kind: ProofAddKind,
    ) -> ReplaceResult {
        // CaDiCaL clause.cpp: replacement only during inprocessing at level 0.
        // Soundness-critical: replacing at higher levels corrupts solver state (#4560).
        assert_eq!(
            self.decision_level, 0,
            "BUG: replace_clause_checked at decision level {}",
            self.decision_level,
        );
        // Replacement must produce a non-growing clause. Empty replacements
        // are valid for strengthening-derived contradictions and are handled
        // below by marking UNSAT.
        // No duplicate variables in the replacement (CaDiCaL subsume.cpp pattern).
        // Soundness-critical: duplicates break 2WL invariant (#4560).
        debug_assert!(
            {
                let mut vars: Vec<u32> = new_lits.iter().map(|l| l.variable().0).collect();
                vars.sort_unstable();
                vars.windows(2).all(|w| w[0] != w[1])
            },
            "BUG: replace_clause_checked: duplicate variables in new_lits for clause {clause_idx}",
        );
        // All literal variables must be in range.
        // Soundness-critical: out-of-range causes silent corruption (#4560).
        // MUST be assert!() not debug_assert!() — see #5141.
        assert!(
            new_lits
                .iter()
                .all(|l| l.variable().index() < self.num_vars),
            "BUG: replace_clause_checked: literal variable out of range (num_vars={})",
            self.num_vars,
        );
        // Husk guard (husk adjudication #3/#4): garbage-kept / pending-garbage
        // clauses are logically deleted. `arena.replace()` clears the
        // GARBAGE|PENDING bits and re-attaches watches + BVE occ entries,
        // which would REVIVE a deliberately deleted clause. Skipping is always
        // sound: the husk stays dead and is reaped normally. Mirrors the sink
        // guard in replace_clause_core (mutate_replace.rs).
        if !self.arena.is_active(clause_idx) || self.arena.is_garbage_any(clause_idx) {
            return ReplaceResult::Skipped;
        }
        // #A2b search-time proof bookkeeping: an LRAT clause replacement
        // rebuilds hint chains and mutates the clause trace (add + delete of
        // a full clause). Charge deterministic units — literal/hint counts,
        // never wall time — against the SAME budget as level-0 unit
        // materialization, so inprocessing-LRAT-heavy runs (QF_ALIA
        // pointer-safe-5 default mode, 2026-07-12 reprofile) can reach
        // exhaustion and degrade to no-proof search at the next safe point
        // (`run_incremental_inprocessing` entry). Synthesized-default
        // certificates only: explicit `--proof`/`:produce-proofs` runs have
        // no budget, so this is a no-op there.
        if self.cold.lrat_enabled {
            // Byte-denominated deterministic units, matching the trace-add
            // charge (a replacement clones the old literals, builds a hint
            // chain, and records an add + a delete).
            let units = (self.arena.len_of(clause_idx) as u64 + new_lits.len() as u64) * 4
                + (extra_lrat_hints.len() as u64) * 8
                + 32;
            let _ = self.charge_proof_bookkeeping(units);
        }
        let was_irredundant = !self.arena.is_learned(clause_idx);
        // New clause must not be longer than original (CaDiCaL subsume.cpp:84).
        // Soundness-critical: growing a clause overwrites adjacent arena memory (#4560).
        // O(1) check — must be assert!() because arena overwrite is silent corruption.
        assert!(
            new_lits.len() <= self.arena.len_of(clause_idx),
            "BUG: replace_clause_checked: new_lits ({}) longer than original ({}) at clause {clause_idx}",
            new_lits.len(),
            self.arena.len_of(clause_idx),
        );
        let clause_ref = ClauseRef(clause_idx as u32);
        let old_clause_id = self.clause_id(clause_ref);
        let old_lits: Vec<Literal> = self.arena.literals(clause_idx).to_vec();

        if new_lits.is_empty() {
            let proof_hints = if self.cold.lrat_enabled {
                self.ensure_level0_unit_proof_ids();
                let mut hints = Vec::with_capacity(old_lits.len() + extra_lrat_hints.len() + 1);
                let old_clause_first_in_checker = old_lits.len() <= 1;

                if !old_clause_first_in_checker {
                    Self::push_lrat_hint(&mut hints, old_clause_id);
                }
                for &hint in extra_lrat_hints {
                    if hint != old_clause_id {
                        Self::push_lrat_hint(&mut hints, hint);
                    }
                }
                if !explicit_only {
                    let mut signed_unit_hints = Vec::new();
                    let mut signed_units_complete = true;

                    for &old_lit in &old_lits {
                        let required_lit = old_lit.negated();
                        if let Some(id) = self.level0_unit_chain_proof_id_for_lit(required_lit) {
                            if id != old_clause_id && !signed_unit_hints.contains(&id) {
                                signed_unit_hints.push(id);
                            }
                        } else {
                            let var_idx = old_lit.variable().index();
                            if var_idx < self.num_vars
                                && self.var_data[var_idx].level == 0
                                && self.has_any_proof_id(var_idx)
                            {
                                signed_units_complete = false;
                                break;
                            }
                        }
                    }

                    if !signed_units_complete {
                        return ReplaceResult::Skipped;
                    }

                    for &id in &signed_unit_hints {
                        Self::push_lrat_hint(&mut hints, id);
                    }
                }
                if old_clause_first_in_checker {
                    Self::push_lrat_hint(&mut hints, old_clause_id);
                }
                Self::lrat_reverse_hints(&hints)
            } else if old_clause_id != 0 {
                vec![old_clause_id]
            } else {
                Vec::new()
            };

            if self.cold.lrat_enabled {
                self.materialize_level0_unit_proofs();
                if !self.lrat_replacement_level0_reason_units_ready(
                    clause_idx,
                    &old_lits,
                    new_lits,
                    old_clause_id,
                ) {
                    return ReplaceResult::Skipped;
                }
            }
            self.mark_empty_clause_with_hints(&proof_hints);
            return ReplaceResult::Empty;
        }

        // CaDiCaL has zero reason-clause protection during level-0 inprocessing.
        // At level 0, replacement is in-place (same arena slot) so the ClauseRef
        // remains valid as a reason reference (#5237, R1:1113).

        // Reorder literals for optimal watch placement (#3812).
        // Without this, after strengthening/BVE the first two literals may both
        // be falsified at low levels, causing BCP to miss unit propagations.
        let mut reordered = new_lits.to_vec();
        let watched =
            self.prepare_watched_literals(&mut reordered, WatchOrderPolicy::AssignmentScore);

        // Proof logging: add-before-delete ordering (DRAT/LRAT requirement)
        let proof_hints = if self.cold.lrat_enabled {
            // Materialize unit proof IDs for level-0 variables so that
            // level0_var_proof_id() (used by collect_level0_unit_chain) can
            // find them in LRAT mode (#7108).
            self.ensure_level0_unit_proof_ids();
            let mut hints = Vec::with_capacity(old_lits.len() + extra_lrat_hints.len() + 1);
            let removed_lits: Vec<Literal> = old_lits
                .iter()
                .copied()
                .filter(|old_lit| !reordered.contains(old_lit))
                .collect();
            // Count how many literals were removed.  This determines where the
            // original clause goes in the hint chain (#4398):
            //
            //   removed == 1: old clause is immediately unit under RUP negation
            //     (all new-clause literals FALSE, one removed literal unassigned).
            //     Push it LAST in pre-reversal → FIRST after reversal.  This lets
            //     the checker propagate the removed variable before any hint that
            //     references it.
            //
            //   removed > 1: old clause has multiple unassigned literals.  Push it
            //     FIRST in pre-reversal → LAST after reversal.  The probe chain
            //     must establish removed-variable values first.
            let removed_count = removed_lits.len();
            let old_clause_first_in_checker = removed_count <= 1;

            if !old_clause_first_in_checker {
                Self::push_lrat_hint(&mut hints, old_clause_id);
            }
            // Include explicitly captured reason chain (vivify probe chain,
            // subsumption hints, etc.).  After reversal these appear before
            // the old clause in the checker's processing order.
            for &hint in extra_lrat_hints {
                if hint != old_clause_id {
                    Self::push_lrat_hint(&mut hints, hint);
                }
            }
            // Include exact signed unit proofs for removed literals (#9068).
            // RUP for a replacement clause assumes the negation of every new
            // literal. To make the old clause conflict, each removed old
            // literal must be falsified, so the required unit is
            // old_lit.negated(). The generic level-0 unit chain is keyed by
            // variable/current assignment and can therefore emit the opposite
            // polarity, satisfying the old clause instead of falsifying it.
            //
            // Skipped when explicit_only=true: subsumption strengthening provides
            // the complete hint chain (subsumer + original) and level-0 reasons
            // for the removed literal are irrelevant to the derivation.
            if !explicit_only {
                let require_all_signed_units = extra_lrat_hints.is_empty() || reordered.len() == 1;
                let mut signed_unit_hints = Vec::new();
                let mut signed_units_complete = true;

                for &old_lit in &removed_lits {
                    let required_lit = old_lit.negated();
                    if let Some(id) = self.level0_unit_chain_proof_id_for_lit(required_lit) {
                        if id != old_clause_id && !signed_unit_hints.contains(&id) {
                            signed_unit_hints.push(id);
                        }
                    } else {
                        let var_idx = old_lit.variable().index();
                        let needs_signed_unit = require_all_signed_units
                            || (var_idx < self.num_vars
                                && self.var_data[var_idx].level == 0
                                && self.has_any_proof_id(var_idx));
                        if needs_signed_unit {
                            signed_units_complete = false;
                            break;
                        }
                    }
                }

                if !signed_units_complete {
                    return ReplaceResult::Skipped;
                }

                for &id in &signed_unit_hints {
                    Self::push_lrat_hint(&mut hints, id);
                }
            }
            // For single-removal: push old clause LAST in pre-reversal so it
            // becomes FIRST after reversal (immediately unit under RUP negation).
            // For multi-removal: old clause was already pushed first.
            if old_clause_first_in_checker {
                Self::push_lrat_hint(&mut hints, old_clause_id);
            }
            Self::lrat_reverse_hints(&hints)
        } else if old_clause_id != 0 {
            vec![old_clause_id]
        } else {
            Vec::new()
        };

        if self.cold.lrat_enabled {
            self.materialize_level0_unit_proofs();
            if !self.lrat_replacement_level0_reason_units_ready(
                clause_idx,
                &old_lits,
                &reordered,
                old_clause_id,
            ) {
                return ReplaceResult::Skipped;
            }
        }

        let mut replacement_clause_id = None;
        // Forward check + proof emit: add clause, then delete old (#4564).
        if let Ok(new_id) = self.proof_emit_add(&reordered, &proof_hints, proof_kind) {
            // Guard: LRAT returns Ok(0) as a no-op sentinel after I/O
            // failure (CaDiCaL-style). Do NOT update clause ID state
            // with this sentinel -- it would corrupt clause_ids and
            // next_clause_id. See #4434.
            if self.cold.lrat_enabled && new_id != 0 {
                replacement_clause_id = Some(new_id);
            }
        }
        // Fix #6270: Before deleting old_clause_id, check if any variable's
        // unit_proof_id references it. If so, re-derive the unit using the
        // replacement clause ID, preventing stale LRAT hint references.
        if self.cold.lrat_enabled && old_clause_id != 0 {
            for &lit in &old_lits {
                let vi = lit.variable().index();
                if vi < self.unit_proof_id.len()
                    && self.unit_proof_id[vi] == old_clause_id
                    && self.unit_proof_sign.get(vi).copied().unwrap_or(0) == lit.sign_i8()
                    && self.var_data[vi].level == 0
                {
                    // The old clause is about to be deleted. Re-derive the unit
                    // from the replacement clause (which has already been added).
                    if let Some(new_id) = replacement_clause_id {
                        let unit_id = self
                            .proof_emit_add(&[lit], &[new_id], ProofAddKind::Derived)
                            .unwrap_or(0);
                        if unit_id != 0 {
                            self.record_unit_proof_id_for_lit(lit, unit_id);
                        }
                    }
                }
            }
        }
        // Derive unit proof IDs for variables whose reason clause is being
        // replaced BEFORE deleting the old clause. The derivation uses
        // old_clause_id as a hint; the old ID must still be in known_lrat_ids.
        // Moving the delete before this call would cause "LRAT hint references
        // unknown/deleted clause" when the derivation tries to reference the
        // just-deleted old clause (#8093).
        self.clear_level0_reasons_removed_by_replacement(
            clause_idx,
            &old_lits,
            &reordered,
            old_clause_id,
        );

        // Delete old clause unconditionally (CaDiCaL: always emit delete
        // for replaced clause regardless of add outcome).
        let _ = self.proof_emit_delete(&old_lits, old_clause_id);

        // Keep clause-ID mapping synchronized with LRAT writer IDs.
        if let Some(new_clause_id) = replacement_clause_id {
            debug_assert!(
                new_clause_id != 0,
                "BUG: LRAT sentinel 0 leaked into clause ID update (#4434)"
            );
            debug_assert!(
                clause_idx < self.cold.clause_ids.len(),
                "BUG: clause_idx {} missing LRAT ID slot (clause_ids len={})",
                clause_idx,
                self.cold.clause_ids.len()
            );
            self.cold.clause_ids[clause_idx] = new_clause_id;
            // Do NOT advance next_clause_id here (#5239). Replacement
            // clauses get their IDs from the proof writer. Derived clauses
            // sync next_clause_id from the writer in add_learned_clause.

            // Propagate replacement clause + resolution hints to clause_trace
            // (#4124). The proof_manager already has the LRAT step; the
            // clause_trace needs a matching entry for SMT proof reconstruction.
            if let Some(ref mut trace) = self.cold.clause_trace {
                trace.add_clause_with_hints(
                    new_clause_id,
                    reordered.clone(),
                    false,
                    proof_hints.clone(),
                );
            }
        }

        // SAT diagnostic trace: clause_replace event (Wave 2, #4211)
        if let Some(ref writer) = self.cold.diagnostic_trace {
            let dimacs_lits: Vec<i64> =
                reordered.iter().map(|l| i64::from(l.to_dimacs())).collect();
            writer.emit_clause_replace(old_clause_id, &dimacs_lits, self.cold.diagnostic_pass);
        }

        // Remove old watches
        let old_len = self.arena.len_of(clause_idx);
        if old_len >= 2 {
            let (lit0, lit1) = self.arena.watched_literals(clause_idx);
            self.remove_watch(lit0, ClauseRef(clause_idx as u32));
            self.remove_watch(lit1, ClauseRef(clause_idx as u32));
        }

        if let Some(ref mut gc_occ) = self.gc_occ {
            let old_lits = self.arena.literals(clause_idx);
            gc_occ.remove_clause(clause_idx, old_lits);
        }
        // Update the clause with reordered literals
        self.drain_pending_garbage_mark(clause_idx);
        self.stats.clear_bcp_learned_1963_blocker_cert(clause_idx);
        self.arena.replace(clause_idx, &reordered);
        if let Some(ref mut gc_occ) = self.gc_occ {
            gc_occ.add_clause(clause_idx, &reordered);
        }
        self.arena.set_saved_pos(clause_idx, 2);
        self.cold.clause_db_changes += 1; // BVE dual-signal fixpoint guard (#3416)
        if was_irredundant {
            self.mark_factor_candidates_dirty_clause(&reordered);
        }

        // Online witness check: shrunken/replaced clauses must remain satisfied
        // by the solution witness. CaDiCaL parity: check_solution_on_shrunken_clause.
        self.check_solution_on_replaced_clause(&reordered);

        // Add new watches based on new clause size
        if let Some((lit0, lit1)) = watched {
            self.attach_clause_watches(clause_ref, (lit0, lit1), reordered.len() == 2);
            ReplaceResult::Replaced
        } else if reordered.len() == 1 {
            // Unit clause: enqueue immediately for propagation.
            let unit_lit = reordered[0];
            match self.lit_value(unit_lit) {
                Some(true) => {
                    // Already satisfied — no action needed
                }
                Some(false) => {
                    // Contradiction at decision level 0: derive empty clause
                    // from replacement clause + assignment reason (#5236 Gap 1).
                    // Use BFS transitive closure for complete LRAT chain (#7108).
                    if self.cold.lrat_enabled {
                        let cid = self.clause_id(clause_ref);
                        let hints =
                            self.collect_empty_clause_hints_for_unit_contradiction(cid, unit_lit);
                        self.mark_empty_clause_with_hints(&hints);
                    } else {
                        self.mark_empty_clause();
                    }
                    return ReplaceResult::Empty;
                }
                None => {
                    // Unit clause from literal replacement: reason=None (#6257).
                    // Store proof ID for LRAT and clause-trace (#6368).
                    if let Some(pid) = replacement_clause_id {
                        self.record_unit_proof_id_for_lit(unit_lit, pid);
                    }
                    // Mark variable dirty for occurrence-guided GC (#8097).
                    // enqueue(lit, None) doesn't go through the BCP dirty path;
                    // mark explicitly so the GC fixpoint loop re-visits clauses
                    // containing this newly-assigned variable.
                    if self.decision_level == 0 {
                        self.l0_gc_dirty[unit_lit.variable().index()] = true;
                    }
                    self.enqueue(unit_lit, None);
                }
            }
            ReplaceResult::Unit
        } else {
            // Empty replacement → UNSAT. Derive empty clause with the
            // replacement clause ID as hint (#5236 Gap 1).
            if self.cold.lrat_enabled {
                let cid = self.clause_id(clause_ref);
                let hints: Vec<u64> = if cid != 0 { vec![cid] } else { Vec::new() };
                self.mark_empty_clause_with_hints(&hints);
            } else {
                self.mark_empty_clause();
            }
            ReplaceResult::Empty
        }
    }
}
