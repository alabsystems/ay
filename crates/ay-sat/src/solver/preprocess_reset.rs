// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Chronological backtracking and search state reset.
//!
//! Split from `preprocess.rs` for file-size compliance (#5142).
//! Contains chrono backtracking level computation and incremental
//! solve reset logic.

use super::*;

impl Solver {
    /// Handle initial unit clauses (before solve loop).
    ///
    /// Returns `None` on success, or `Some(conflict_ref)` if a contradictory
    /// unit clause is found (all its literals falsified). The caller should
    /// use the conflict ref for LRAT hint collection via
    /// `record_level0_conflict_chain`.
    pub(super) fn process_initial_clauses(&mut self) -> Option<ClauseRef> {
        // Must be at decision level 0 when processing initial units
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: process_initial_clauses at level {} (expected 0)",
            self.decision_level,
        );
        // Reuse persistent buffer to avoid arena-proportional allocation (#8602).
        self.cold.reduce_indices_buf.clear();
        self.cold.reduce_indices_buf.extend(self.arena.indices());
        for j in 0..self.cold.reduce_indices_buf.len() {
            let i = self.cold.reduce_indices_buf[j];
            if !self.arena.is_active(i) {
                continue;
            }
            let off = i;
            if self.arena.len_of(off) == 1 {
                let lit = self.arena.literal(off, 0);
                if let Some(val) = self.lit_value(lit) {
                    if !val {
                        // Unit clause is already falsified — return conflict ref
                        // so caller can collect LRAT resolution hints.
                        return Some(ClauseRef(off as u32));
                    }
                    // Already satisfied, skip
                } else {
                    // Propagate unit clause (CaDiCaL: clause.cpp:361-363).
                    // Use reason=None: unit clauses have no antecedent literals,
                    // so they cannot be used as reason clauses in conflict
                    // analysis (which requires len >= 2). (#6257)
                    // Store proof ID for LRAT and clause-trace (#6368).
                    let cid = self.cold.clause_ids.get(off).copied().unwrap_or(0);
                    if cid != 0 {
                        self.record_unit_proof_id_for_lit(lit, cid);
                    }
                    self.enqueue(lit, None);
                    if !self.var_lifecycle.is_inactive(lit.variable().index()) {
                        self.fixed_count += 1;
                        self.var_lifecycle.mark_fixed(lit.variable().index());
                        self.l0_gc_dirty[lit.variable().index()] = true;
                    }
                }
            }
        }
        None
    }

    /// Pick the polarity for a decision variable using phase saving with target phases
    ///
    /// Phase selection priority:
    /// 1. Forced phase (if set via `set_phase()`): External hint from IC3/user.
    /// 2. Target phase (if available): Uses the assignment from the longest conflict-free
    ///    trail seen. This guides the search toward promising regions.
    /// 3. Saved phase: The last polarity this variable was assigned.
    /// 4. Default: Positive polarity if no phase information exists.
    ///
    /// Target phases help the solver explore variations of assignments that were
    /// close to satisfying the formula.
    pub(super) fn pick_phase(&self, var: Variable) -> Literal {
        let idx = var.index();
        // Variable must be within bounds
        debug_assert!(
            idx < self.num_vars,
            "BUG: pick_phase for var {} >= num_vars {}",
            idx,
            self.num_vars,
        );
        // Variable must be unassigned (we're picking a phase for a decision)
        debug_assert!(
            !self.var_is_assigned(idx),
            "BUG: pick_phase for already-assigned var {idx}",
        );

        // External forced phase has highest priority (CaDiCaL phases.forced,
        // decide.cpp:134). IC3 uses this to bias cube polarity.
        let fp = self.cold.forced_phase[idx];
        if fp != 0 {
            return if fp > 0 {
                Literal::positive(var)
            } else {
                Literal::negative(var)
            };
        }

        // Target phases in stable mode only (CaDiCaL target=1, decide.cpp:148).
        // Target phases record the assignment at the longest conflict-free trail.
        // Using them in stable mode guides EVSIDS toward promising regions.
        //
        // Previously used in both modes (Kissat target=2), but this hurts hard
        // UNSAT instances like clique_n2_k10 (#8466): target phases override
        // focused-mode diversification, trapping the solver in a near-satisfying
        // region that can never be completed. CaDiCaL's default target=1 (stable
        // only) avoids this by letting focused mode freely diversify phases.
        if self.stable_mode {
            let tp = self.target_phase[idx];
            if tp != 0 {
                return if tp > 0 {
                    Literal::positive(var)
                } else {
                    Literal::negative(var)
                };
            }
        }

        // Kissat-style focused-mode phase cycling (decide.c:178-187).
        // Uses `(switched >> 1) & 7` to produce an 8-step cycle where
        // slots 1 and 3 force INITIAL_PHASE (+1) and inverted (-1),
        // overriding saved phases 25% of the time. This diversifies
        // focused-mode search on hard combinatorial instances like
        // battleship-14-26 and stable-300 (#8085).
        if !self.stable_mode {
            let slot = (self.cold.mode_switch_count >> 1) & 7;
            match slot {
                1 => return Literal::positive(var),
                3 => return Literal::negative(var),
                _ => {}
            }
        }

        // Fall back to saved phase (0 = unset defaults to positive)
        if self.phase[idx] < 0 {
            Literal::negative(var)
        } else {
            Literal::positive(var)
        }
    }

    /// Compute the actual backtrack level, deciding between chronological and
    /// non-chronological backtracking based on the jump distance.
    ///
    /// Based on the SAT'18 paper "Chronological Backtracking" and CaDiCaL's
    /// `chronoreusetrail` optimization:
    ///
    /// - If the jump would skip many levels (> CHRONO_LEVEL_LIMIT), use
    ///   chronological backtracking (just go back one level)
    /// - Otherwise, try to reuse trail by finding the best variable above the
    ///   jump level and backtracking only to that level
    pub(super) fn compute_chrono_backtrack_level(&mut self, jump_level: u32) -> u32 {
        // CaDiCaL analyze.cpp:653: backtrack level must be strictly below current level
        debug_assert!(
            jump_level < self.decision_level,
            "BUG: jump_level ({jump_level}) >= decision_level ({})",
            self.decision_level,
        );

        if !self.chrono_enabled {
            return jump_level;
        }

        // Unit clauses (jump_level == 0) MUST backtrack to level 0.
        // Chronological backtracking cannot be used here because the unit literal
        // would be enqueued at a non-zero level, and subsequent backtracking could
        // undo the assignment. The unit clause would then be unsatisfied in the model.
        // This was the root cause of #1696.
        if jump_level == 0 {
            return 0;
        }

        // If jump level is at or above current level - 1, no point in chrono BT
        if jump_level >= self.decision_level.saturating_sub(1) {
            return jump_level;
        }

        // Compute how many levels we'd skip with NCB
        let skip_levels = self.decision_level - jump_level;

        let actual_level = if skip_levels > CHRONO_LEVEL_LIMIT {
            // Too many levels to skip - use chronological backtracking
            self.stats.chrono_backtracks += 1;
            self.decision_level - 1
        } else if self.chrono_reuse_trail && !self.deep_dive_full_backjump() {
            // CaDiCaL-style trail reuse: find the best variable above the jump level
            // and only backtrack to that level to keep more of the useful trail.
            // CaDiCaL analyze.cpp:675 applies this unconditionally in both stable
            // and focused modes — use_scores() selects the metric (VSIDS activity
            // for stable, bump order for focused), not whether to apply trail reuse.
            self.compute_chrono_reuse_level(jump_level)
        } else {
            // Deep-diving (or trail reuse disabled): full non-chronological
            // backjump straight to the asserting level, matching kissat
            // learn.c::kissat_determine_new_level. On a fruitless deep dive,
            // CaDiCaL-style trail reuse keeps the solver pinned deep (staying at
            // the level of the highest-priority variable above the asserting
            // level after every conflict), inflating decisions-per-conflict and
            // starving conflict generation. kissat backjumps to exactly the
            // asserting level and reuses trail only at restart, generating far
            // more conflicts per second on the same core (profile lever #1).
            jump_level
        };

        // Emit diagnostic event when chrono BT was chosen (#4172, #4674).
        if actual_level != jump_level {
            self.emit_diagnostic_chrono_backtrack(self.decision_level, jump_level, actual_level);
        }

        actual_level
    }

    /// Deep-dive full-backjump gate (retired profile lever #1, kissat parity).
    ///
    /// The historical lever returned `true` when the decisions-per-conflict EMA
    /// crossed its threshold, forcing an asserting-level backjump instead of
    /// reusing the trail. Production now always returns `false`.
    ///
    /// MEASURED RESULT (workflow wf_22647919, adversarial verify REJECTED
    /// default-ON): the profile A/B on ebbda8d9 moved telemetry sharply toward
    /// kissat (conflicts +53%, conf/s +53%, decisions/conflict 1706→1098), but
    /// on independent re-run the lever flipped ZERO instances at 120s — every
    /// deep-dive target (ebbda8d9, ac388757, d0298807, cdd89d1b, 5dbe7b31)
    /// stayed unknown ON exactly as OFF (ebbda 96956→341320 conflicts, still no
    /// solve). Those losses are inprocessing-bound (kissat's kitten sweep
    /// substitutes up to 1.39M vars), not search-policy-bound. Worse, the
    /// original "floor untouched by construction, healthy=2–10 dpc" premise was
    /// FALSE: floor-flip df813fe7 runs at dpc≈220 and would fire at default-64
    /// (it still solved, but "untouched" was wrong), and force-firing on a
    /// currently-solved instance (43fbacb2, base SAT@91k conflicts) turned it
    /// into an 18× timeout. So default-ON has zero measured upside and an
    /// unbounded, demonstrated downside. Kept OFF as a composable lever: it is
    /// the one clean per-conflict search delta vs kissat and may earn default-ON
    /// only paired with a hard-core branching/phase lever AND a full-corpus
    /// PAR-2 A/B re-solving every currently-solved dpc>64 instance.
    ///
    /// B21 retired the opt-in after that rejected experiment; the gate remains
    /// permanently off until a paired-lever campaign reintroduces it in code.
    fn deep_dive_full_backjump(&self) -> bool {
        false
    }

    /// Find the best variable above the jump level and return its level.
    ///
    /// This implements CaDiCaL's `chronoreusetrail` optimization. Instead of
    /// always backtracking to the asserting level, we look for valuable variables
    /// above that level. In stable mode, we look for the variable with highest
    /// VSIDS activity. In focused mode, we look for the most recently bumped
    /// variable. We then backtrack only to the level containing that trail
    /// position, preserving more of the useful search state.
    ///
    /// Key: we use trail POSITION to determine level, not the variable's stored
    /// level. This is important for correctness with chronological backtracking
    /// where variables can have out-of-order level assignments.
    pub(super) fn compute_chrono_reuse_level(&mut self, jump_level: u32) -> u32 {
        // Precondition: jump_level must be below decision level
        debug_assert!(
            jump_level < self.decision_level,
            "BUG: compute_chrono_reuse_level: jump_level {} >= decision_level {}",
            jump_level,
            self.decision_level,
        );
        // Get the trail position where jump_level+1 starts
        let start_pos = if (jump_level as usize) < self.trail_lim.len() {
            self.trail_lim[jump_level as usize]
        } else {
            return jump_level;
        };

        // If no assignments above jump level, just use jump level
        if start_pos >= self.trail.len() {
            return jump_level;
        }

        // Find the best variable's trail position (not just index)
        let mut best_pos: Option<usize> = None;

        for i in start_pos..self.trail.len() {
            let var = self.trail[i].variable();
            let is_better = match best_pos {
                Some(current_best) => self.branch_priority_is_lower(
                    self.trail[current_best].variable(),
                    var,
                    self.active_branch_heuristic,
                ),
                None => true,
            };
            if is_better {
                best_pos = Some(i);
            }
        }

        // Find the level containing the best variable's trail position
        // CaDiCaL: while (res < level - 1 && control[res + 1].trail <= best_pos) res++;
        let Some(best_pos) = best_pos else {
            return jump_level;
        };

        // CaDiCaL: while (res < level - 1 && control[res + 1].trail <= best_pos) res++;
        // In AY: trail_lim[i] = start of level i+1's assignments
        // So to match control[res+1].trail (start of level res+1), use trail_lim[res]
        let mut res = jump_level;
        while res < self.decision_level - 1
            && (res as usize) < self.trail_lim.len()
            && self.trail_lim[res as usize] <= best_pos
        {
            res += 1;
        }

        if res > jump_level {
            self.stats.chrono_backtracks += 1;
        }

        // Post-condition: result must be between jump_level and decision_level - 1
        debug_assert!(
            res >= jump_level && res < self.decision_level,
            "BUG: chrono_reuse_level result {} out of range [{}, {})",
            res,
            jump_level,
            self.decision_level,
        );
        res
    }

    /// Reset transient search state so the solver can be reused across multiple `solve()` calls.
    ///
    /// This keeps the clause database intact (including learned clauses), but clears assignments,
    /// watches, and scheduling state that assume a fresh search.
    pub(super) fn reset_search_state(&mut self) {
        self.stats.clear_bcp_learned_1963_blocker_certs();

        // #unguarded-tvalid-lemmas STAGE 0: per-solve assumption-prefix
        // depth. `solve_with_assumptions_impl` re-sets this right after the
        // reset; no-assumption solve entries leave it at 0.
        self.cold.active_assumption_count = 0;

        // Default to full watch rebuild. Case (b) below may upgrade this to
        // an incremental attach if the arena is preserved (#8374).
        self.cold.incremental_watch_boundary = None;

        // #inc-pending-conflict: a pending theory conflict is within-solve
        // state — the ClauseRef refers to a clause that was all-false under
        // the PREVIOUS solve's trail (add_theory_lemma's level>0 all-false
        // detection, #6262). If the previous solve returned without draining
        // it (e.g. UNSAT via a level-0 BCP conflict), the ref survives into
        // the next solve call. After a pop() swept the scoped clause and the
        // arena rebuild below replaced every offset, take_pending_theory_conflict
        // in cdcl_loop_impl dereferences a stale offset from the old arena
        // (observed under AY_LRA_EAGER_LAZY: arena len 6, index ~174M).
        // The trail is cleared by this reset regardless, so the "conflict
        // under current assignment" is meaningless for the new solve: drop it.
        self.pending_theory_conflicts.clear();
        self.pending_theory_unit_proof_ids.clear();

        #[cfg(debug_assertions)]
        {
            // Proof mode must not toggle during a solve call. Snapshot it at
            // solve/reset entry so proof-sensitive passes can assert stability.
            self.solve_proof_mode = Some(self.proof_manager.is_some());
        }

        // #5031: Restore formula to pristine state after inprocessing.
        //
        // The previous solve's inprocessing may have permanently modified
        // clause_db in ways not tracked by the reconstruction stack:
        // - Decompose: substitutes equivalent variables and deletes subsumed
        //   clauses WITHOUT reconstruction entries
        // - Congruence: merges gates and deletes duplicate clauses
        // - BVE/BCE: deletes clauses WITH reconstruction entries
        // - Level-0 GC: deletes satisfied clauses permanently
        //
        // Drain reconstruction stack first (BVE/BCE witness clauses).
        if self.inproc.reconstruction.len() > 0 {
            let drain_result = self.inproc.reconstruction.drain_witness_entries();
            self.inproc.reconstruction = ReconstructionStack::new();
            let mut reactivated_bve_vars = false;

            // Targeted reactivation (#3644 Wave 3): reactivate variables
            // from drained witness entries. Give them competitive VSIDS
            // activity so they are actually decided (#7981).
            let reactivation_activity = self.vsids.current_increment();
            for &idx in &drain_result.reactivate_vars {
                if idx < self.var_lifecycle.len() && self.var_lifecycle.can_reactivate(idx) {
                    if let Some(ref writer) = self.cold.diagnostic_trace {
                        writer.emit_var_transition(
                            idx as u32,
                            crate::diagnostic_trace::VarState::Eliminated,
                            crate::diagnostic_trace::VarState::Active,
                            self.cold.diagnostic_pass,
                        );
                    }
                    self.var_lifecycle.reactivate(idx);
                    self.inproc.bve.clear_removed_external(idx);
                    // #7981: Reactivated variables had zero activity from
                    // BVE elimination. Without a competitive score they sit
                    // at the bottom of the decision heap and may never be
                    // branched on, causing incomplete search → false UNSAT.
                    let var = Variable(idx as u32);
                    if self.vsids.activity(var) == 0.0 {
                        self.vsids.set_activity(var, reactivation_activity);
                    }
                    reactivated_bve_vars = true;
                }
            }
            if reactivated_bve_vars {
                self.inproc.bve.invalidate_occ_lists();
            }
        }

        // JIT incremental cache (#8225): move the compiled formula to the
        // cache before the arena may be rebuilt. If the arena IS rebuilt
        // (case a below), we invalidate the cache. If it is NOT rebuilt,
        // the cache remains valid for delta recompilation on the next solve.

        // #5031/#5608: Restore original clauses for incremental solving.
        //
        // Two cases:
        // (a) Inprocessing deleted some original clauses (subsumption, BVE,
        //     decompose, level-0 GC): rebuild arena from original_clauses
        //     ledger. Count only non-learned clauses to detect this — learned
        //     clauses inflate active_count and mask missing originals.
        // (b) No deletions, but new originals were appended (bound-tightening
        //     from add_upper_bound/add_lower_bound): add only the new ones.
        if !self.cold.original_ledger.is_empty() {
            // live_indices (husk adjudication #4): garbage-kept husks are
            // logically deleted; counting them inflates the census, masks the
            // destructive-rebuild trigger, and routes into the (now-guarded)
            // learned-husk revival path below.
            let active_original_count = self
                .arena
                .live_indices()
                .filter(|&idx| !self.arena.is_learned(idx))
                .count();
            let ledger_count = self.cold.original_ledger.num_clauses();
            // #7987: Use != instead of < to also detect when preprocessing
            // added derived irredundant clauses (active > ledger). Such
            // clauses preserve equisatisfiability but NOT logical equivalence;
            // they can exclude models that were valid for the original formula.
            // On incremental solves with new clauses added between calls,
            // those excluded models may be the only satisfying assignments,
            // causing spurious UNSAT. Also rebuild when
            // inprocessing_modified_clause_db is set (catches equal-count
            // add+delete edge case).
            //
            // #8375: Separate destructive-inprocessing rebuilds (BVE/BCE/
            // congruence/decompose — destroy learned clauses) from L0 GC
            // rebuilds (only deletes satisfied clauses and removes false
            // literals — safe to preserve learned clauses).
            let needs_destructive_rebuild =
                active_original_count != ledger_count || self.cold.inprocessing_modified_clause_db;
            let needs_l0_gc_rebuild =
                !needs_destructive_rebuild && self.cold.l0_gc_modified_clause_db;
            if needs_destructive_rebuild || needs_l0_gc_rebuild {
                // #8375: When only L0 GC modified the clause DB (no BVE/BCE/
                // congruence), learned clauses are safe to preserve. They were
                // derived under the original clause set (L0 GC only removes
                // satisfied clauses and false literals, never adds derived
                // irredundant clauses or eliminates variables).
                let saved_learned: Vec<Vec<Literal>> = if needs_l0_gc_rebuild {
                    // live_indices (husk adjudication #4): garbage-kept learned
                    // husks (eager-subsume, OTFS-subsumed) are logically
                    // deleted — re-adding them live across an incremental
                    // rebuild revives them, undoing subsumption and desyncing
                    // an attached forward checker that already saw the delete.
                    self.arena
                        .live_indices()
                        .filter(|&idx| self.arena.is_learned(idx))
                        .map(|idx| self.arena.literals(idx).to_vec())
                        .collect()
                } else {
                    // Case (a): Destructive inprocessing (BVE/BCE/congruence).
                    // Do NOT preserve learned clauses — they may have been
                    // derived under BVE-simplified clause sets and can force
                    // level-0 assignments that conflict with new bounds
                    // (TSP regression).
                    Vec::new()
                };

                let rebuild_reactivation_activity = self.vsids.current_increment();
                for i in 0..self.var_lifecycle.len() {
                    if self.var_lifecycle.is_removed(i) && self.var_lifecycle.can_reactivate(i) {
                        self.var_lifecycle.reactivate(i);
                        self.inproc.bve.clear_removed_external(i);
                        // #7981: Give reactivated variables competitive VSIDS
                        // activity so they are branched on during search.
                        let var = Variable(i as u32);
                        if self.vsids.activity(var) == 0.0 {
                            self.vsids.set_activity(var, rebuild_reactivation_activity);
                        }
                    }
                }
                self.arena = ClauseArena::new();
                // A fresh arena restarts `formula_epoch` at 0, so the epoch
                // guard alone cannot see this; drop the frontier cache.
                self.relevancy_frontier.invalidate();
                // #inc-rebuild-reasons: the rebuild invalidates EVERY old
                // arena offset (even preserved learned clauses get new
                // indices below), but level-0 trail entries can still carry
                // reason refs into the old arena — e.g. extension theory
                // lemmas added at scope depth 0 (correctly unswept by pop
                // GC, absent from the ledger) that propagated root facts.
                // Dereferencing such a ref after the rebuild reads a stale
                // offset (observed: clause_arena len 6, index ~171M panic in
                // cdcl_loop_impl on the post-pop check under the eager-lazy
                // lane). We are at solve entry / decision level 0, so every
                // assigned var is a root fact: normalize all reasons to
                // NO_REASON — root facts need no reason for search; clause
                // minimization treats NO_REASON as non-removable (sound,
                // at worst slightly weaker minimization).
                for vd in self.var_data.iter_mut() {
                    vd.reason = NO_REASON;
                }
                self.bump_reason_graph_epoch();
                self.cold.clause_ids.clear();
                self.cold.bcp_learned_clause_birth_conflicts.clear();
                // #unguarded-tvalid-lemmas STAGE 0: stale arena offsets —
                // clear with clause_ids. Rebuilt clauses read as birth
                // epoch 0 ("pre-existing"), which is the honest attribution
                // after a ledger rebuild.
                self.cold.clause_birth_solve.clear();
                for (ordinal, clause) in self.cold.original_ledger.iter_clauses().enumerate() {
                    let idx = self.arena.add(clause, false);
                    // Assign clause ID unconditionally (#8197, #8069 Phase 2a).
                    if !self.cold.clause_ids_disabled {
                        // Split-borrow form: the ledger iteration above holds
                        // `cold.original_ledger` borrowed.
                        super::cold::ColdState::grow_clause_ids(
                            &mut self.cold.clause_ids,
                            self.cold.clause_ids_reserve_hint,
                            idx,
                        );
                        self.cold.clause_ids[idx] = (ordinal as u64) + 1;
                    }
                }
                // #8375: Re-add preserved learned clauses after rebuilding
                // originals from ledger.
                for learned_lits in &saved_learned {
                    if learned_lits.len() >= 2 {
                        self.arena.add(learned_lits, true);
                    }
                }
                self.cold.incremental_original_boundary = self.cold.original_ledger.num_clauses();
                // Clear flags after rebuild so subsequent solves that don't
                // run inprocessing don't trigger unnecessary rebuilds.
                self.cold.inprocessing_modified_clause_db = false;
                self.cold.l0_gc_modified_clause_db = false;
                self.inproc.bve.invalidate_occ_lists();
                // JIT cache (#8225): arena was rebuilt from scratch, all
                // cached compiled code is invalid.
            } else if self.cold.incremental_original_boundary
                < self.cold.original_ledger.num_clauses()
            {
                // Case (b): No rebuild needed, just add new original clauses.
                // Record arena boundary before appending so initialize_watches()
                // can skip clearing existing watches and attach only new clauses
                // (#8374). This is safe because the existing clause database is
                // unchanged — only new originals are appended at the end.
                self.cold.incremental_watch_boundary = Some(self.arena.len());
                let start = self.cold.incremental_original_boundary;
                let new_count = self.cold.original_ledger.num_clauses();
                for clause_idx in start..new_count {
                    let clause = self.cold.original_ledger.clause(clause_idx);
                    let idx = self.arena.add(clause, false);
                    // Assign clause ID unconditionally (#8197, #8069 Phase 2a).
                    if !self.cold.clause_ids_disabled {
                        // Split-borrow form: `clause` above borrows
                        // `cold.original_ledger`.
                        super::cold::ColdState::grow_clause_ids(
                            &mut self.cold.clause_ids,
                            self.cold.clause_ids_reserve_hint,
                            idx,
                        );
                        self.cold.clause_ids[idx] = (clause_idx as u64) + 1;
                    }

                    // Subsumption scheduling (#8376): mark variables in new
                    // original clauses as subsume-dirty so the next subsumption
                    // pass picks them up as candidates. Without this, new
                    // clauses added between incremental solves (e.g., IC3/PDR
                    // blocking clauses) wait until a full subsumption round
                    // discovers them, missing early optimization opportunities.
                    // Mirrors the irredundant path in clause_add_internal.rs.
                    for &lit in clause {
                        let v = lit.variable().index();
                        if v < self.subsume_dirty.len() {
                            self.subsume_dirty[v] = true;
                        }
                    }

                    // JIT cache (#8225): mark variables in new clauses as dirty
                    // so delta recompilation regenerates their functions.
                }
                self.cold.incremental_original_boundary = new_count;
            }
        }

        // Core assignment / trail state (#3758 Phase 3: vals[] is sole source)
        self.vals.fill(0);
        // Clear conflict analyzer seen marks before resetting var_data, because
        // seen marks now live in var_data.flags (#6994). Without this, the fill
        // below silently erases seen marks without updating seen_true_count.
        self.conflict.clear(&mut self.var_data);
        self.var_data.fill(VarData::UNASSIGNED);
        self.bump_reason_graph_epoch();
        // #relevancy-frontier-incremental: the incremental relevancy frontier
        // folds a PREFIX of the trail; rewriting the trail outside backtrack
        // invalidates that correspondence, so drop the cache (the next query
        // rebuilds with the original from-scratch walk).
        self.relevancy_frontier.invalidate();
        self.trail.clear();
        self.trail_lim.clear();
        self.decision_level = 0;
        self.qhead = 0;

        // Clear LRAT proof provenance arrays (#5229). Without this, stale
        // proof IDs from the previous solve persist across incremental solves.
        // The 3-tier fallback (reason → unit_proof_id → level0_proof_id)
        // could consult stale entries if a variable ends up at level 0 with
        // reason=None for a reason other than BVE ClearLevel0.
        self.unit_proof_id.fill(0);
        self.unit_proof_sign.fill(0);
        self.cold.level0_proof_id.fill(0);
        self.cold.level0_proof_sign.fill(0);
        self.cold.lrat_level0_unit_materialize_cursor = 0;
        self.cold.lrat_level0_unit_materialize_pinned.clear();

        // IC3 state preservation (#8643): in IC3 mode, skip destructive
        // CHB/VSIDS resets. IC3 depends on VSIDS activity accumulating
        // across incremental calls so the solver focuses on variables
        // relevant to the current proof obligation. CHB state is unused
        // in IC3 (set_ic3_mode() locks to EVSIDS), so skip reset.
        if !self.cold.ic3_mode {
            // Reset CHB state before rebuilding the heap.
            // After chb_reset(), chb_loaded is false. Reset active_branch_heuristic
            // to Evsids so that sync_active_branch_heuristic() (called later) will
            // correctly re-swap into CHB mode if the selector mode requires it.
            self.vsids.chb_reset();
            self.active_branch_heuristic = BranchHeuristic::Evsids;
        }

        // Reset VSIDS heap to include all variables (they are all unassigned now),
        // then remove non-active variables — they must never be decided.
        // Activities are preserved — only the heap ordering is rebuilt.
        self.vsids.reset_heap();
        for (i, state) in self.var_lifecycle.iter_enumerated() {
            if state.is_removed() {
                self.vsids.remove_from_heap(Variable(i as u32));
            }
        }
        self.vsids.reset_vmtf_unassigned();

        // Invalidate GC occ list — arena may have been rebuilt (#8097).
        self.gc_occ = None;
        self.cold.last_collect_trail_pos = 0;

        // Watches: either full clear+rebuild or incremental attach (#8374).
        //
        // When the arena was preserved (case b: only new originals appended),
        // the existing watch lists are still valid for all pre-existing clauses.
        // Skip the expensive clear() and let initialize_watches() attach only
        // the new clauses from the boundary onward.
        //
        // When the arena was rebuilt (case a) or this is the first solve,
        // incremental_watch_boundary is None and we do the full clear.
        if self.cold.incremental_watch_boundary.is_none() {
            self.watches.clear();
        }
        self.watches.ensure_num_vars(self.num_vars);

        // Restart / scheduling state
        // #qfuflia-stats: fold this solve's restarts into the lifetime total
        // before zeroing (mirrors lifetime_conflicts below).
        self.cold.lifetime_restarts = self
            .cold
            .lifetime_restarts
            .saturating_add(self.cold.restarts);
        self.conflicts_since_restart = 0;
        self.cold.luby_idx = 1;
        self.cold.restarts = 0;

        // Glucose-style EMA state (ADAM bias-corrected)
        self.cold.lbd_ema_fast = 0.0;
        self.cold.lbd_ema_slow = 0.0;
        self.cold.lbd_ema_fast_biased = 0.0;
        self.cold.lbd_ema_slow_biased = 0.0;
        self.cold.lbd_ema_fast_exp = 1.0;
        self.cold.lbd_ema_slow_exp = 1.0;
        self.cold.saved_lbd_ema_fast = 0.0;
        self.cold.saved_lbd_ema_slow = 0.0;
        self.cold.saved_lbd_ema_fast_biased = 0.0;
        self.cold.saved_lbd_ema_slow_biased = 0.0;
        self.cold.saved_lbd_ema_fast_exp = 1.0;
        self.cold.saved_lbd_ema_slow_exp = 1.0;
        self.cold.ema_swapped = false;

        // Focused-mode EMA restart throttling.
        self.cold.consecutive_ema_restarts = 0;

        // Stabilization state
        self.stable_mode = matches!(self.cold.mode_lock, cold::ModeLock::Stable);
        self.cold.stable_mode_start_conflicts = 0;
        self.cold.stable_phase_length = self.cold.stable_phase_init;
        self.cold.stable_phase_count = 0;
        self.search_ticks = [0; 2];
        self.cold.stabilize_tick_inc = 0;
        self.cold.focused_ticks_at_entry = 0;
        self.cold.mode_equiticks_cached = None;
        self.cold.stabilize_tick_limit = 0;
        self.cold.reluctant_u = 1;
        self.cold.reluctant_v = 1;
        self.cold.reluctant_countdown = RELUCTANT_INIT;
        self.cold.reluctant_ticked_at = 0;
        self.sync_active_branch_heuristic();

        self.no_conflict_until = 0;
        self.target_trail_len = 0;
        self.target_phase.fill(0);
        // Note: best_phase and best_trail_len are kept across solves for rephasing

        // Bumpreason rate-limiting state (must reset with num_decisions/num_conflicts).
        // Without this, bumpreason_saved_decisions retains the previous solve's value
        // while num_decisions resets to 0, causing u64 wrapping in the delta computation
        // and disabling reason bumping for the first many conflicts (#5119).
        self.cold.bumpreason_delay_interval = [0; 2];

        // Accumulate conflicts from this solve into lifetime total before reset (#8208).
        self.cold.lifetime_conflicts = self
            .cold
            .lifetime_conflicts
            .saturating_add(self.num_conflicts);
        // #qfuflia-stats: decisions/propagations lifetime twins.
        self.cold.lifetime_decisions = self
            .cold
            .lifetime_decisions
            .saturating_add(self.num_decisions);
        self.cold.lifetime_propagations = self
            .cold
            .lifetime_propagations
            .saturating_add(self.num_propagations);

        // Track incremental solve calls for between-solve cleanup (#8435).
        if self.cold.has_solved_once {
            self.cold.incremental_solve_count += 1;
        }

        // VSIDS activity rescaling (#8470): unconditionally rescale VSIDS
        // activities between incremental solves to prevent unbounded growth.
        // Previously this was gated inside between_solve_reduce(), which
        // returns early when learned clause count stays below the reduction
        // threshold. In IC3/PDR workloads with aggressive reduction or very
        // small formulas, rescaling never fired, and the VSIDS increment
        // grew multiplicatively across solves. Although the proactive rescale
        // in decay() prevents actual Inf at the 1e100 threshold, periodic
        // normalization to max=1.0 keeps the heap well-distributed and
        // prevents reactivated variables (assigned current_increment())
        // from having incomparable magnitudes with stale activities.
        if self.cold.incremental_solve_count > 0
            && self
                .cold
                .incremental_solve_count
                .is_multiple_of(INCREMENTAL_VSIDS_RESCALE_INTERVAL)
        {
            self.vsids.rescale_for_reorder();
        }

        // Between-solve learned clause reduction (#8435).
        // IC3/PDR engines make thousands of short incremental queries. Each
        // learns a few clauses but never reaches the 300-conflict reduce_db
        // threshold. This cleanup prunes accumulated learned clauses to prevent
        // unbounded DB growth. Only fires when:
        // (1) enough lifetime conflicts have passed since last cleanup, AND
        // (2) learned clause count exceeds a threshold relative to originals
        if self.cold.has_solved_once {
            self.between_solve_reduce();
        }

        // Clause database management scheduling (counters restart each solve).
        self.num_conflicts = 0;
        self.num_decisions = 0;
        // Wander-abort baselines snapshot arm-time counter values; the restart
        // invalidates them (relevancy.rs, #relevancy-lazy-routing).
        self.wander_abort_base_conflicts = 0;
        self.wander_abort_base_decisions = 0;
        self.num_propagations = 0;
        self.num_search_propagations = 0;
        self.num_original_clauses = 0;
        // (#8435) Lower the reduce_db threshold for incremental mode so that
        // reduce_db fires within short IC3 queries. After enough incremental
        // solves, we know the workload is IC3-like and benefit from more
        // aggressive in-solve reduction.
        self.cold.next_reduce_db =
            if self.cold.incremental_solve_count >= INCREMENTAL_REDUCE_DB_RAMP {
                INCREMENTAL_FIRST_REDUCE_DB
            } else {
                FIRST_REDUCE_DB
            };
        self.cold.process_memory_interrupt = false;
        self.cold.process_memory_interrupt_pending = false;
        self.cold.process_memory_armed_at = None;

        // Learned clause trail: arena offsets of recently learned clauses for
        // eager subsumption in conflict analysis. Must be cleared because the
        // arena may have been rebuilt above (offsets are stale), and even
        // without rebuild, learned clauses from the previous solve have
        // different reduction/GC eligibility in the new search.
        self.cold.learned_clause_trail.clear();

        // Conditioning root-satisfied clauses (#8574): clauses removed by
        // conditioning's root-satisfied GC are saved here for restore on
        // incremental re-solve. Clear them now — the arena rebuild above
        // already restored originals from the ledger, so these stale
        // entries would only grow unboundedly across solve calls when
        // decompose doesn't fire.
        self.cold.root_satisfied_saved.clear();

        // Walk/rephase state: walk_last_ticks is compared against
        // search_ticks (reset above to [0; 2]). Without resetting
        // walk_last_ticks, walk effort = ticks - stale_high_watermark
        // underflows via saturating_sub → walk never triggers until ticks
        // catch up to the stale value.
        self.phase_init.walk_last_ticks = 0;

        // Bumpreason rate limiting: compared against num_decisions (reset
        // above to 0). Stale saved_decisions produces wrong delta on the
        // first conflicts of the new solve.
        self.cold.bumpreason_saved_decisions = 0;
        self.cold.bumpreason_decision_rate = 0.0;
        self.cold.bumpreason_delay_remaining = [0; 2];
        self.cold.bumpreason_delay_interval = [0; 2];
        self.cold.next_flush = FLUSH_INIT;
        self.cold.flush_inc = FLUSH_INIT;
        self.cold.num_flushes = 0;
        self.cold.num_arena_compactions = 0;
        self.cold.num_reductions = 0;
        self.cold.last_inprobe_reduction = 0;
        self.cold.inprobe_phases = 0;
        self.cold.eager_subsumed = 0;

        // Tick watermarks: search_ticks reset to [0,0] above, so last_*_ticks
        // must also be zeroed or saturating_sub blocks all tick-gated passes.
        self.cold.last_vivify_ticks = 0;
        self.cold.last_vivify_irred_ticks = 0;
        // Engine watermarks: same saturating_sub starvation pattern as vivify.
        // search_ticks and num_propagations reset above; engine watermarks must
        // follow or the affected technique is starved until ticks catch up (#8159).
        self.cold.last_factor_ticks = 0;
        self.cold.last_sweep_ticks = 0;
        self.cold.last_backbone_ticks = 0;
        self.cold.last_probe_ticks = 0;
        self.cold.last_subsume_ticks = 0;
        self.cold.last_bve_ticks = 0;
        self.cold.bve_consecutive_unproductive = 0;
        self.cold.last_transred_ticks = 0;
        self.cold.last_bce_ticks = 0;
        self.cold.last_sbva_ticks = 0;
        self.inproc.reset_watermarks();

        // Effort demotion persistence (#8159 D4): the runtime effort demotion
        // selector (profile.rs) one-way reduces bve_effort_permille and
        // subsume_effort_permille. On incremental re-solve with a changed
        // formula, the solver must re-evaluate effort from defaults.
        self.cold.bve_effort_permille = BVE_EFFORT_PER_MILLE;
        self.cold.subsume_effort_permille = SUBSUME_EFFORT_PER_MILLE;

        // Inprocessing scheduling (relative to `num_conflicts`).
        //
        // On incremental re-solves (lifetime_conflicts > 0), set per-technique
        // thresholds to 0 so they fire on the first inprocessing round (#8208).
        // Without this, techniques with large default intervals (e.g., BVE at
        // 2000 conflicts) would never fire during IC3/PDR's many tiny solves.
        let incremental_ready = self.cold.lifetime_conflicts > 0;
        let base_or_zero = |base: u64| -> u64 {
            if incremental_ready {
                0
            } else {
                base
            }
        };
        self.inproc_ctrl.vivify.next_conflict = base_or_zero(VIVIFY_INTERVAL);
        self.inproc_ctrl.vivify_irred.next_conflict = base_or_zero(VIVIFY_IRRED_INTERVAL);
        self.cold.vivify_irred_delay_multiplier = 1;
        self.inproc_ctrl
            .subsume
            .reset_interval(if incremental_ready {
                0
            } else {
                SUBSUME_INTERVAL
            });
        self.inproc_ctrl.probe.next_conflict = base_or_zero(PROBE_INTERVAL);
        self.inproc_ctrl.bve.next_conflict = base_or_zero(BVE_INTERVAL_BASE);
        self.inproc_ctrl.bce.next_conflict = base_or_zero(BCE_INTERVAL);
        self.inproc_ctrl.transred.next_conflict = base_or_zero(TRANSRED_INTERVAL);
        self.inproc_ctrl.htr.next_conflict = base_or_zero(HTR_INTERVAL);
        self.inproc_ctrl.sweep.next_conflict = base_or_zero(SWEEP_INTERVAL);
        self.inproc_ctrl.condition.next_conflict = base_or_zero(CONDITION_INTERVAL);
        self.inproc_ctrl.decompose.next_conflict = 0;
        self.inproc_ctrl.factor.next_conflict = base_or_zero(FACTOR_INTERVAL);
        self.inproc_ctrl.sbva.next_conflict = base_or_zero(SBVA_INTERVAL);
        self.inproc_ctrl.congruence.next_conflict = 0;
        self.cold.next_rephase = REPHASE_INITIAL;
        self.tiers.next_recompute_tier = TIER_RECOMPUTE_INIT;
        self.fixed_count = 0;
        self.cold.last_collect_fixed = 0;
        // Reset propfixed so every literal becomes re-probable after
        // fixed_count resets to 0. Without this, stale propfixed entries
        // from the prior solve (where fixed_count was high) cause
        // false skips: propfixed[lit] >= 0 > new fixed_count=0.
        self.inproc.prober.reset_propfixed();
        self.pending_garbage_count = 0;
        self.l0_gc_dirty.iter_mut().for_each(|d| *d = false);
        // Revert Fixed -> Active since all assignments are cleared.
        self.var_lifecycle.reset_fixed();
        self.reset_branch_heuristic_selector();

        // Post-conditions: search state is clean
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: reset_search_state left decision_level non-zero"
        );
        debug_assert!(
            self.trail.is_empty(),
            "BUG: reset_search_state left trail non-empty"
        );
        debug_assert_eq!(self.qhead, 0, "BUG: reset_search_state left qhead non-zero");
        debug_assert_eq!(
            self.num_conflicts, 0,
            "BUG: reset_search_state left num_conflicts non-zero"
        );
    }

    /// Check whether the incremental reset fast path can be used (#8443, #8569).
    ///
    /// Returns true when:
    /// 1. The assumption cache is valid (no push/pop or new vars since the
    ///    last solve). Note: `add_clause` no longer invalidates the cache —
    ///    it sets `ic3_new_clauses_pending` instead (#8569).
    /// 2. No reconstruction stack entries exist (no inprocessing modified the arena)
    /// 3. No destructive ledger rebuild is needed (BVE/BCE/congruence/L0 GC)
    ///
    /// When `ic3_new_clauses_pending` is true, the incremental reset handles
    /// new clause attachment inline in O(new_clauses) time instead of falling
    /// back to the full O(num_vars) reset. This is the key optimization for
    /// IC3 throughput — IC3 adds blocking clauses between every query.
    ///
    /// When these hold, `reset_search_state_incremental` can be used instead of
    /// the full `reset_search_state`, preserving level-0 trail state, watches,
    /// and VSIDS heap across incremental assumption-based solves.
    pub(super) fn can_use_incremental_reset(&self) -> bool {
        if !self.cold.assumption_cache_valid {
            return false;
        }

        // IC3 fast path (#8569 Gap 1): in IC3 mode the ordinary between-solves
        // arena mutation is add_clause (tracked by ic3_new_clauses_pending and
        // handled inline by the incremental reset), so we can skip the
        // O(clauses) arena scan that counts active non-learned clauses.
        //
        // SOUNDNESS (#8503): set_ic3_mode KEEPS scoped BVE enabled, so a push/pop
        // query CAN destructively rewrite the arena — eliminating a scope-local
        // variable, deleting its original clauses, adding resolvents, and pushing
        // reconstruction witnesses. When that has happened the arena encodes
        // `∃v.(clauses)` for the eliminated var, and the incremental reset does
        // NOT rebuild from the original ledger — so if a later clause/assumption
        // reactivates v (add_clause only re-marks it Active) the solver would
        // search a projected formula and can return a WRONG verdict (false
        // UNSAT / false SAT). Force a full ledger-rebuild reset in that case.
        // These are O(1) checks; ordinary BVE-free IC3 queries still take the
        // fast path. (The prior code assumed "IC3 disables all inprocessing",
        // which became stale when #8503 re-enabled scoped BVE for push/pop.)
        if self.cold.ic3_mode {
            if self.inproc.reconstruction.len() > 0
                || self.cold.inprocessing_modified_clause_db
                || self.cold.l0_gc_modified_clause_db
            {
                return false;
            }
            return true;
        }

        // Reconstruction stack non-empty means inprocessing modified the arena
        if self.inproc.reconstruction.len() > 0 {
            return false;
        }
        // Check if the arena would need a DESTRUCTIVE rebuild from original ledger
        // (BVE/BCE/congruence/L0 GC modified the clause DB). New clause appends
        // are handled inline by the incremental reset (#8569).
        if !self.cold.original_ledger.is_empty() {
            // Destructive modifications require full rebuild.
            if self.cold.inprocessing_modified_clause_db || self.cold.l0_gc_modified_clause_db {
                return false;
            }
            // live_indices (husk adjudication #4): exclude garbage-kept husks
            // from the census — see the matching census in reset above.
            let active_original_count = self
                .arena
                .live_indices()
                .filter(|&idx| !self.arena.is_learned(idx))
                .count();
            // Compare arena originals against the boundary (number of originals
            // at last solve), not the full ledger count. New appends since last
            // solve are tracked by incremental_original_boundary and handled
            // inline by the incremental reset (#8569).
            let expected_count = self.cold.incremental_original_boundary;
            if active_original_count != expected_count {
                return false;
            }
            // New originals appended since last solve: allowed on incremental
            // path when ic3_new_clauses_pending is set (#8569). The incremental
            // reset attaches watches for new clauses inline.
            if self.cold.incremental_original_boundary < self.cold.original_ledger.num_clauses()
                && !self.cold.ic3_new_clauses_pending
            {
                return false;
            }
        }
        true
    }

    /// Lightweight reset for incremental assumption-based solving (#8443, #8569).
    ///
    /// GipSAT pattern: instead of clearing all solver state (vals, var_data,
    /// trail, watches, VSIDS heap), backtrack to level 0 and reset only
    /// scheduling counters. Level-0 propagations, watches, and the VSIDS
    /// heap are preserved from the previous solve.
    ///
    /// When `ic3_new_clauses_pending` is true (#8569), new clauses added
    /// between solves are attached inline: arena append + watch attachment
    /// + unit propagation. This avoids the full O(num_vars) reset that
    ///   previously occurred on every IC3 `add_clause` call.
    ///
    /// SAFETY: Caller MUST verify `can_use_incremental_reset()` returns true.
    /// Using this when the arena has been destructively modified is unsound.
    pub(super) fn reset_search_state_incremental(&mut self) {
        self.stats.clear_bcp_learned_1963_blocker_certs();

        // #unguarded-tvalid-lemmas STAGE 0: per-solve assumption-prefix
        // depth. `solve_with_assumptions_impl` re-sets this right after the
        // reset; no-assumption solve entries leave it at 0.
        self.cold.active_assumption_count = 0;

        #[cfg(debug_assertions)]
        {
            self.solve_proof_mode = Some(self.proof_manager.is_some());
        }

        // Backtrack to level 0, preserving level-0 trail state.
        // This unassigns all decision-level variables while keeping
        // level-0 propagations intact on the trail.
        if self.decision_level > 0 {
            if self.cold.ic3_mode {
                // IC3-optimized backtrack (#8569): use backtrack_ic3 which
                // skips phase saving, target/best phase updates, LSCB lambda
                // checks, and vmtf_on_unassign. The no_conflict_until zeroing
                // is no longer needed as a workaround — backtrack_ic3 never
                // calls update_target_and_best_phases at all.
                self.no_conflict_until = 0;
                self.backtrack_ic3(0);
            } else {
                self.backtrack(0);
            }
        }

        // Clear conflict analyzer seen marks (they may be set from
        // the previous solve's conflict analysis).
        self.conflict.clear(&mut self.var_data);
        self.bump_reason_graph_epoch();

        // qhead: set to trail.len() so BCP doesn't re-propagate
        // level-0 literals that are already on the trail from the prior solve.
        self.qhead = self.trail.len();

        // IC3 new clause attachment (#8569): when add_clause was called
        // between solves, attach watches for the new clauses and propagate
        // any new units. This is O(new_clauses) instead of O(num_vars).
        //
        // IMPORTANT: done AFTER setting qhead. If new unit clauses are added,
        // they enqueue literals on the trail (trail.len() grows past qhead).
        // The IC3 solve loop's BCP call will then propagate these new units
        // because qhead < trail.len().
        if self.cold.ic3_new_clauses_pending {
            self.cold.ic3_new_clauses_pending = false;
            self.attach_new_clauses_incremental();
        }

        // VSIDS: don't rebuild the full heap. Just re-insert variables
        // that were unassigned by the backtrack but are still active.
        // The backtrack() call above already re-inserted them via the
        // standard backtrack_core path.

        // Invalidate GC occ list for safety.
        self.gc_occ = None;

        // IC3 fast path (#8569): in IC3 mode, the CDCL loop in
        // `solve_incremental_ic3` has its own Luby restart scheme, its own
        // reduce_db scheduling, and never runs inprocessing. Skip the cold
        // scheduling state resets that IC3 never reads, but keep the global
        // conflict counter monotonic so reduce_db scheduling carries across
        // incremental solves.
        if self.cold.ic3_mode {
            if self.cold.has_solved_once {
                self.cold.incremental_solve_count += 1;
            }
            // VSIDS activity rescaling (#8470): still needed to prevent
            // unbounded activity growth across thousands of IC3 queries.
            if self.cold.incremental_solve_count > 0
                && self
                    .cold
                    .incremental_solve_count
                    .is_multiple_of(INCREMENTAL_VSIDS_RESCALE_INTERVAL)
            {
                self.vsids.rescale_for_reorder();
            }
            // Between-solve learned clause reduction (#8435): in IC3 mode,
            // between_solve_reduce() delegates to ic3_between_solve_gc()
            // (#8672) which uses a conservative GC — only pruning high-LBD
            // unused clauses when learned count exceeds 10x irredundant.
            // In-solve reduce_db() also handles clause growth within each
            // IC3 query.
            if self.cold.has_solved_once {
                self.between_solve_reduce();
            }
            // Reset per-solve counters read directly by the IC3 CDCL loop.
            // `num_conflicts` stays monotonic across solves because
            // should_reduce_db() uses it to schedule clause reduction.
            self.num_decisions = 0;
            self.wander_abort_base_decisions = 0;
            self.num_propagations = 0;
            self.num_search_propagations = 0;
            self.conflicts_since_restart = 0;
            self.no_conflict_until = 0;
            self.cold.process_memory_interrupt = false;
            self.cold.process_memory_interrupt_pending = false;
            self.cold.process_memory_armed_at = None;
            self.cold.learned_clause_trail.clear();
            self.pending_garbage_count = 0;

            // Post-conditions
            debug_assert_eq!(
                self.decision_level, 0,
                "BUG: reset_search_state_incremental left decision_level non-zero"
            );
            debug_assert_eq!(
                self.conflicts_since_restart, 0,
                "BUG: reset_search_state_incremental left conflicts_since_restart non-zero"
            );
            return;
        }

        // === Non-IC3 scheduling state resets (same as full reset) ===

        // Restart / scheduling state
        // #qfuflia-stats: fold this solve's restarts into the lifetime total
        // before zeroing (mirrors lifetime_conflicts below).
        self.cold.lifetime_restarts = self
            .cold
            .lifetime_restarts
            .saturating_add(self.cold.restarts);
        self.conflicts_since_restart = 0;
        self.cold.luby_idx = 1;
        self.cold.restarts = 0;

        // Glucose-style EMA state (ADAM bias-corrected)
        self.cold.lbd_ema_fast = 0.0;
        self.cold.lbd_ema_slow = 0.0;
        self.cold.lbd_ema_fast_biased = 0.0;
        self.cold.lbd_ema_slow_biased = 0.0;
        self.cold.lbd_ema_fast_exp = 1.0;
        self.cold.lbd_ema_slow_exp = 1.0;
        self.cold.saved_lbd_ema_fast = 0.0;
        self.cold.saved_lbd_ema_slow = 0.0;
        self.cold.saved_lbd_ema_fast_biased = 0.0;
        self.cold.saved_lbd_ema_slow_biased = 0.0;
        self.cold.saved_lbd_ema_fast_exp = 1.0;
        self.cold.saved_lbd_ema_slow_exp = 1.0;
        self.cold.ema_swapped = false;

        // Stabilization state
        self.stable_mode = matches!(self.cold.mode_lock, cold::ModeLock::Stable);
        self.cold.stable_mode_start_conflicts = 0;
        self.cold.stable_phase_length = self.cold.stable_phase_init;
        self.cold.stable_phase_count = 0;
        self.search_ticks = [0; 2];
        self.cold.stabilize_tick_inc = 0;
        self.cold.focused_ticks_at_entry = 0;
        self.cold.mode_equiticks_cached = None;
        self.cold.stabilize_tick_limit = 0;
        self.cold.reluctant_u = 1;
        self.cold.reluctant_v = 1;
        self.cold.reluctant_countdown = RELUCTANT_INIT;
        self.cold.reluctant_ticked_at = 0;
        self.sync_active_branch_heuristic();

        self.no_conflict_until = 0;
        self.target_trail_len = 0;
        self.target_phase.fill(0);

        // Bumpreason rate-limiting state
        self.cold.bumpreason_delay_interval = [0; 2];

        // Accumulate conflicts from this solve into lifetime total before reset.
        self.cold.lifetime_conflicts = self
            .cold
            .lifetime_conflicts
            .saturating_add(self.num_conflicts);
        // #qfuflia-stats: decisions/propagations lifetime twins.
        self.cold.lifetime_decisions = self
            .cold
            .lifetime_decisions
            .saturating_add(self.num_decisions);
        self.cold.lifetime_propagations = self
            .cold
            .lifetime_propagations
            .saturating_add(self.num_propagations);

        // Track incremental solve calls for between-solve cleanup (#8435).
        if self.cold.has_solved_once {
            self.cold.incremental_solve_count += 1;
        }

        // VSIDS activity rescaling (#8470).
        if self.cold.incremental_solve_count > 0
            && self
                .cold
                .incremental_solve_count
                .is_multiple_of(INCREMENTAL_VSIDS_RESCALE_INTERVAL)
        {
            self.vsids.rescale_for_reorder();
        }

        // Between-solve learned clause reduction (#8435).
        if self.cold.has_solved_once {
            self.between_solve_reduce();
        }

        // Clause database management scheduling
        self.num_conflicts = 0;
        self.num_decisions = 0;
        // Wander-abort baselines: see the incremental reset above.
        self.wander_abort_base_conflicts = 0;
        self.wander_abort_base_decisions = 0;
        self.num_propagations = 0;
        self.num_search_propagations = 0;
        self.num_original_clauses = 0;
        self.cold.next_reduce_db =
            if self.cold.incremental_solve_count >= INCREMENTAL_REDUCE_DB_RAMP {
                INCREMENTAL_FIRST_REDUCE_DB
            } else {
                FIRST_REDUCE_DB
            };
        self.cold.process_memory_interrupt = false;
        self.cold.process_memory_interrupt_pending = false;
        self.cold.process_memory_armed_at = None;

        self.cold.learned_clause_trail.clear();

        // Conditioning root-satisfied clauses (#8574): same as full reset.
        self.cold.root_satisfied_saved.clear();

        // Walk/rephase state
        self.phase_init.walk_last_ticks = 0;

        // Bumpreason rate limiting
        self.cold.bumpreason_saved_decisions = 0;
        self.cold.bumpreason_decision_rate = 0.0;
        self.cold.bumpreason_delay_remaining = [0; 2];
        self.cold.bumpreason_delay_interval = [0; 2];
        self.cold.next_flush = FLUSH_INIT;
        self.cold.flush_inc = FLUSH_INIT;
        self.cold.num_flushes = 0;
        self.cold.num_arena_compactions = 0;
        self.cold.num_reductions = 0;
        self.cold.last_inprobe_reduction = 0;
        self.cold.inprobe_phases = 0;
        self.cold.eager_subsumed = 0;

        // Tick watermarks
        self.cold.last_vivify_ticks = 0;
        self.cold.last_vivify_irred_ticks = 0;
        self.cold.last_factor_ticks = 0;
        self.cold.last_sweep_ticks = 0;
        self.cold.last_backbone_ticks = 0;
        self.cold.last_probe_ticks = 0;
        self.cold.last_subsume_ticks = 0;
        self.cold.last_bve_ticks = 0;
        self.cold.bve_consecutive_unproductive = 0;
        self.cold.last_transred_ticks = 0;
        self.cold.last_bce_ticks = 0;
        self.cold.last_sbva_ticks = 0;
        self.inproc.reset_watermarks();

        // Effort demotion persistence (#8159 D4)
        self.cold.bve_effort_permille = BVE_EFFORT_PER_MILLE;
        self.cold.subsume_effort_permille = SUBSUME_EFFORT_PER_MILLE;

        // Inprocessing scheduling
        let incremental_ready = self.cold.lifetime_conflicts > 0;
        let base_or_zero = |base: u64| -> u64 {
            if incremental_ready {
                0
            } else {
                base
            }
        };
        self.inproc_ctrl.vivify.next_conflict = base_or_zero(VIVIFY_INTERVAL);
        self.inproc_ctrl.vivify_irred.next_conflict = base_or_zero(VIVIFY_IRRED_INTERVAL);
        self.cold.vivify_irred_delay_multiplier = 1;
        self.inproc_ctrl
            .subsume
            .reset_interval(if incremental_ready {
                0
            } else {
                SUBSUME_INTERVAL
            });
        self.inproc_ctrl.probe.next_conflict = base_or_zero(PROBE_INTERVAL);
        self.inproc_ctrl.bve.next_conflict = base_or_zero(BVE_INTERVAL_BASE);
        self.inproc_ctrl.bce.next_conflict = base_or_zero(BCE_INTERVAL);
        self.inproc_ctrl.transred.next_conflict = base_or_zero(TRANSRED_INTERVAL);
        self.inproc_ctrl.htr.next_conflict = base_or_zero(HTR_INTERVAL);
        self.inproc_ctrl.sweep.next_conflict = base_or_zero(SWEEP_INTERVAL);
        self.inproc_ctrl.condition.next_conflict = base_or_zero(CONDITION_INTERVAL);
        self.inproc_ctrl.decompose.next_conflict = 0;
        self.inproc_ctrl.factor.next_conflict = base_or_zero(FACTOR_INTERVAL);
        self.inproc_ctrl.sbva.next_conflict = base_or_zero(SBVA_INTERVAL);
        self.inproc_ctrl.congruence.next_conflict = 0;
        self.cold.next_rephase = REPHASE_INITIAL;
        self.tiers.next_recompute_tier = TIER_RECOMPUTE_INIT;
        // Do NOT reset fixed_count or var_lifecycle.reset_fixed() — level-0
        // assignments are preserved in the incremental path.
        self.pending_garbage_count = 0;
        self.reset_branch_heuristic_selector();

        // Post-conditions
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: reset_search_state_incremental left decision_level non-zero"
        );
        debug_assert_eq!(
            self.num_conflicts, 0,
            "BUG: reset_search_state_incremental left num_conflicts non-zero"
        );
    }

    /// Attach watches for new clauses added between incremental solves (#8569).
    ///
    /// Called by `reset_search_state_incremental` when `ic3_new_clauses_pending`
    /// is true. Appends new original clauses from the ledger to the arena,
    /// attaches 2-watched literal pointers, and propagates any new unit clauses.
    ///
    /// This is O(new_clauses) instead of the O(num_vars) cost of the full
    /// `reset_search_state()` + `initialize_watches()` path.
    ///
    /// REQUIRES: at decision level 0, all level-0 state intact from prior solve.
    fn attach_new_clauses_incremental(&mut self) {
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: attach_new_clauses_incremental at level {}",
            self.decision_level,
        );

        let start = self.cold.incremental_original_boundary;
        let new_count = self.cold.original_ledger.num_clauses();
        if start >= new_count {
            return;
        }

        for clause_idx in start..new_count {
            // Copy clause to avoid borrow conflict with self.
            let clause: Vec<Literal> = self.cold.original_ledger.clause(clause_idx).to_vec();

            // Unit clause: propagate directly at level 0.
            if clause.len() == 1 {
                let lit = clause[0];
                if let Some(val) = self.lit_value(lit) {
                    if !val {
                        // Contradictory unit clause -- mark empty.
                        self.mark_empty_clause();
                        break;
                    }
                    // Already satisfied, skip.
                } else {
                    let cid = (clause_idx as u64) + 1;
                    self.record_unit_proof_id_for_lit(lit, cid);
                    self.enqueue(lit, None);
                    if !self.var_lifecycle.is_inactive(lit.variable().index()) {
                        self.fixed_count += 1;
                        self.var_lifecycle.mark_fixed(lit.variable().index());
                        self.l0_gc_dirty[lit.variable().index()] = true;
                    }
                }
                // Add to arena even though it's unit (for consistency).
                let idx = self.arena.add(&clause, false);
                if !self.cold.clause_ids_disabled {
                    self.cold.clause_ids_grow_for(idx);
                    self.cold.clause_ids[idx] = (clause_idx as u64) + 1;
                }
                continue;
            }

            // Multi-literal clause: add to arena and attach watches.
            //
            // BUG FIX (#8633): When attaching clauses incrementally during
            // IC3 solves, some literals may already be assigned at level 0.
            // Naive watch placement on the first two literals can leave both
            // watches on false-at-level-0 literals, making the clause invisible
            // to BCP. This causes missed unit propagations and false UNSAT.
            //
            // Fix: reorder clause literals so that watches land on non-false
            // literals (prefer true, then unassigned, then false). If only one
            // non-false literal remains, propagate it as a unit. If all literals
            // are false, record a level-0 conflict.
            let clause_len = clause.len();
            let idx = self.arena.add(&clause, false);
            if !self.cold.clause_ids_disabled {
                self.cold.clause_ids_grow_for(idx);
                self.cold.clause_ids[idx] = (clause_idx as u64) + 1;
            }

            if clause_len >= 2 {
                // Reorder literals in the arena to place non-false literals
                // first. This ensures watches are on useful literals.
                // Score: true-at-l0 = 2, unassigned = 1, false-at-l0 = 0.
                // Swap the best two into positions 0 and 1.
                let mut best0 = 0usize; // index of best literal for watch 0
                let mut best0_score: i8 = -1;
                let mut best1 = 1usize; // index of best literal for watch 1
                let mut best1_score: i8 = -1;
                let mut num_non_false = 0u32;

                for j in 0..clause_len {
                    let lit = self.arena.literal(idx, j);
                    let v = self.lit_val(lit);
                    let score = if v > 0 {
                        2i8
                    } else if v == 0 {
                        1i8
                    } else {
                        0i8
                    };
                    if score > 0 {
                        num_non_false += 1;
                    }
                    if score > best0_score {
                        // Demote current best0 to best1 if it's better than best1
                        if best0_score > best1_score {
                            best1 = best0;
                            best1_score = best0_score;
                        }
                        best0 = j;
                        best0_score = score;
                    } else if score > best1_score {
                        best1 = j;
                        best1_score = score;
                    }
                }

                // Place best literals in positions 0 and 1.
                if best0 != 0 {
                    self.arena.swap_literals(idx, 0, best0);
                    // If best1 was at position 0, it moved to best0's old position.
                    if best1 == 0 {
                        best1 = best0;
                    }
                }
                if best1 != 1 {
                    self.arena.swap_literals(idx, 1, best1);
                }

                if num_non_false == 0 {
                    // All literals false at level 0 — clause is falsified.
                    // Record level-0 conflict.
                    self.record_level0_conflict_chain(ClauseRef(idx as u32));
                    break;
                } else if num_non_false == 1 && best0_score == 1 {
                    // Exactly one unassigned literal — propagate it as unit.
                    let unit_lit = self.arena.literal(idx, 0);
                    let clause_ref = ClauseRef(idx as u32);
                    self.enqueue(unit_lit, Some(clause_ref));
                    if !self.var_lifecycle.is_inactive(unit_lit.variable().index()) {
                        self.fixed_count += 1;
                        self.var_lifecycle.mark_fixed(unit_lit.variable().index());
                        self.l0_gc_dirty[unit_lit.variable().index()] = true;
                    }
                } else {
                    // At least 2 non-false literals — attach watches normally.
                    let clause_ref = ClauseRef(idx as u32);
                    let lit0 = self.arena.literal(idx, 0);
                    let lit1 = self.arena.literal(idx, 1);
                    let is_binary = clause_len == 2;
                    self.watches.watch_clause(clause_ref, lit0, lit1, is_binary);
                }

                // Subsumption scheduling for new clauses (#8376).
                for &lit in &clause {
                    let v = lit.variable().index();
                    if v < self.subsume_dirty.len() {
                        self.subsume_dirty[v] = true;
                    }
                }
            }
        }
        self.cold.incremental_original_boundary = new_count;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn incremental_reset_ic3_preserves_monotonic_conflict_counter() {
        let mut solver = Solver::new(4);
        solver.set_ic3_mode();
        solver.cold.has_solved_once = true;
        solver.cold.lifetime_conflicts = 11;
        solver.num_conflicts = 37;
        solver.conflicts_since_restart = 9;
        solver.num_decisions = 5;
        solver.num_propagations = 12;

        solver.reset_search_state_incremental();

        assert_eq!(solver.num_conflicts, 37);
        assert_eq!(
            solver.cold.lifetime_conflicts, 11,
            "IC3 incremental reset must not fold num_conflicts into lifetime_conflicts"
        );
        assert_eq!(solver.conflicts_since_restart, 0);
        assert_eq!(solver.num_decisions, 0);
        assert_eq!(solver.num_propagations, 0);
        assert_eq!(solver.cold.incremental_solve_count, 1);
    }
}
