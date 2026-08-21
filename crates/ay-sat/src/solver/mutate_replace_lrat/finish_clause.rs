// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Solver {
    pub(super) fn finish_lrat_clause_replacement(
        &mut self,
        clause_ref: ClauseRef,
        clause_idx: usize,
        old_clause_id: u64,
        reordered: &[Literal],
        watched: Option<(Literal, Literal)>,
        was_irredundant: bool,
        replacement_clause_id: Option<u64>,
    ) -> ReplaceResult {
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
            // Empty replacement → UNSAT; derive empty with its ID (#5236 Gap 1).
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
