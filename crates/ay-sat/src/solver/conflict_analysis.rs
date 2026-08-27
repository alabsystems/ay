// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! 1UIP conflict analysis and clause learning.

use super::*;
#[cfg(test)]
use crate::kani_compat::det_hash_set_new;
use crate::solver_log::solver_log;

// Soundness-triage antecedent recorder (--sat-ab-triage-clause): collects every
// clause ref resolved during the current conflict analysis so the learning
// tripwire can dump the exact antecedents of the target learned clause.
pub(super) fn triage_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| ay_core::misc_cli_flags().ab_triage_clause.is_some())
}
thread_local! {
    pub(super) static TRIAGE_ANTECEDENTS: std::cell::RefCell<Vec<u32>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

impl Solver {
    /// Analyze conflict and learn a clause using 1UIP scheme.
    ///
    /// Returns `None` when the backward trail scan fails to find a current-level
    /// seen literal (#8479). This can happen under chronological backtracking
    /// when trail_pos values are stale and the chrono-BT scan fix (#8360) pushes
    /// the scan index past `trail.len()`. The caller should backtrack to level 0
    /// and continue — no incorrect clause is learned.
    pub(super) fn analyze_conflict(&mut self, conflict_ref: ClauseRef) -> Option<ConflictResult> {
        solver_log!(self, "analyze conflict clause {}", conflict_ref.0);

        // Depth observability (see SolverStats::trail_at_conflict_sum): sampled
        // once per conflict, before any backtracking, so it records the state
        // the conflict was actually reached in.
        self.stats.trail_at_conflict_sum += self.trail.len() as u64;
        self.stats.level_at_conflict_sum += u64::from(self.decision_level);

        // #8707: If `materialize_current_level_lazy_reasons` failed to
        // reconstruct a lazy theory reason, the affected variable was
        // demoted to a fake decision (`reason = NO_REASON`). Running 1UIP
        // on a trail containing a fake current-level decision produces a
        // learned clause that is NOT RUP-derivable from the original CNF,
        // which can cause false UNSAT (e.g., QF_LIA n-queens n=6).
        //
        // CaDiCaL-style 1UIP assumes every current-level seen literal has
        // a reason clause; only the genuine decision literal may have
        // `reason = NO_REASON`, and it must be the UIP. When a failed
        // lazy reason demotes a propagated (non-UIP) current-level var to
        // NO_REASON, the Decision branch of the resolution loop violates
        // the `resolvent_size == counter + learned_count` invariant and
        // learns a clause with two current-level literals.
        //
        // The safe recovery is to abort this analysis and backtrack to
        // level 0, mirroring the trail-exhaustion bailout (#8479). The
        // caller at `solve/analyze.rs:122` already handles `None` by
        // backtracking to 0 without learning.
        if self.cold.lazy_materialization_failed {
            self.stats.trail_exhaustion_bailouts += 1;
            self.cold.lazy_materialization_failed = false;
            return None;
        }

        self.conflict.clear(&mut self.var_data);

        // Arm the incremental shrink-prescan bit (#8790). It is exact only
        // when the per-level seen counters start clean; the rare ghost-drop
        // bailout below returns without clear_level_seen, in which case
        // finalize falls back to the O(clause_len) prescan.
        self.min.level_seen_flag_valid = self.min.level_seen_to_clear.is_empty();
        self.min.level_seen_repeated_non_uip = false;

        // Entry cleanliness: learned clause and resolution chain must be empty
        // after clear(). clause_buf is a reusable workspace — stale content is
        // overwritten before use, so it is not checked here.
        // CaDiCaL reference: analyze.cpp:944-948.
        debug_assert_eq!(
            self.conflict.learned_count(),
            0,
            "BUG: learned clause buffer not empty at analysis entry"
        );
        debug_assert!(
            self.decision_level > 0,
            "BUG: conflict analysis called at decision level 0"
        );

        // #unguarded-tvalid-lemmas STAGE 0 (replay counters, behavior-
        // preserving): attribute this conflict for the incremental QF_LRA
        // carryover diagnostic.
        // (1) conflicts_from_prior_solve_clauses: the conflicting clause was
        //     born before the current incremental solve began (birth-solve
        //     stamp < incremental_solve_count; a missing stamp reads as
        //     epoch 0). Nonzero values prove cross-solve clause reuse.
        // (2) assumption_level_conflicts: the conflict fires within the
        //     assumption prefix (scope selectors + user assumptions), so the
        //     learned clause will resolve against assumption decisions and
        //     inherit the scope-selector guard.
        if self.cold.incremental_solve_count > 0 {
            let birth = self
                .cold
                .clause_birth_solve
                .get(conflict_ref.0 as usize)
                .copied()
                .unwrap_or(0);
            if u64::from(birth) < self.cold.incremental_solve_count {
                self.stats.conflicts_from_prior_solve_clauses += 1;
            }
        }
        if self.cold.active_assumption_count > 0
            && self.decision_level <= self.cold.active_assumption_count
        {
            self.stats.assumption_level_conflicts += 1;
        }

        let mut counter = 0; // Literals at current decision level
                             // Ghost-literal proof guard (#8434 follow-up, 2026-07-02): the ghost
                             // skips below drop unassigned antecedent literals from the learned
                             // clause, which makes the learned clause STRONGER than its resolution
                             // derivation — such clauses are not RUP and fail external DRAT
                             // verification (braun.8 add#671 repro: checker-identical clause set,
                             // pre-drop resolvent RUP, emitted clause not RUP). In proof mode we
                             // therefore ABORT the analysis when any ghost literal is dropped
                             // (same recovery as the lazy-materialization bailout: backtrack to
                             // level 0, no learning). Ghosts are rare (chrono-BT/push-pop windows),
                             // so the cost is negligible; no-proof mode keeps the #8434 behavior.
        let mut ghost_literal_dropped = false;
        let mut p: Option<Literal> = None;
        let mut index = self.trail.len();
        // Collect level-0 variables for the LRAT unit chain.
        // Reuse persistent buffer from cold state (#8603) — cleared per conflict
        // instead of reallocated. Conflicts happen thousands of times per second.
        self.cold.lrat_level0_vars_buf.clear();
        let mut lrat_level0_vars = std::mem::take(&mut self.cold.lrat_level0_vars_buf);

        // OTFS accounting: resolved steps, current resolvent size, antecedent
        // size of the just-processed clause, and the last reason clause.
        let mut resolved: u32 = 0;
        let mut resolvent_size: u32 = 0;
        let mut antecedent_size: u32;
        let mut last_reason_ref: Option<ClauseRef> = None;
        // Track conflict clause size for on-the-fly subsumption
        // (CaDiCaL analyze.cpp:1057,1064-1065).
        let mut conflict_size: u32 = 0;
        let mut current_conflict_ref = conflict_ref;

        // Bump conflict clause: set used, bump activity, recompute glue
        self.bump_clause(conflict_ref);

        if triage_enabled() {
            TRIAGE_ANTECEDENTS.with(|b| {
                let mut b = b.borrow_mut();
                b.clear();
                b.push(conflict_ref.0);
            });
        }

        // Streaming support: mark the conflict clause if it is original (#8250).
        self.mark_streaming_core(conflict_ref);

        // Forward LRAT chain: add the conflict clause ID to start the chain.
        // CaDiCaL analyze.cpp: the conflict clause is the seed of the resolution.
        if self.cold.lrat_enabled {
            let id = self.clause_id(conflict_ref);
            if id != 0 {
                self.conflict.add_to_chain(id);
            }
        }

        // CaDiCaL analyze.cpp:944: conflict clause must exist and be non-trivial
        debug_assert!(
            self.arena.len_of(conflict_ref.0 as usize) >= 2,
            "BUG: conflict clause {} has len {} (expected >= 2)",
            conflict_ref.0,
            self.arena.len_of(conflict_ref.0 as usize),
        );

        // Zero-copy clause iteration (#6989).
        let mut current_clause_offset = conflict_ref.0 as usize;
        let mut current_clause_len = self.arena.len_of(current_clause_offset);

        // Tick accounting: charge 1 search tick for the conflict clause itself.
        // CaDiCaL charges ticks per reason clause traversal in
        // bump_also_reason_literals (analyze.cpp:370), but that path is
        // rate-limited. The main resolution loop processes many more reason
        // clauses -- charging here closes the tick gap (#8148).
        self.search_ticks[usize::from(self.stable_mode)] += 1;

        loop {
            let clause_len = current_clause_len;
            // OTFS accounting starts with the pivot/UIP slot.
            antecedent_size = 1;

            // JIT fast path (#8277): use the compiled conflict processor to
            // handle the hot inner work (seen-flag read/modify/write + level
            // classification) in a tight native loop. A bookkeeping pass then
            // handles seen_to_clear, track_level_seen, ticks, LRAT, and
            // antecedent_size using the JIT's seen_vars output. VarData cache
            // lines are L1-hot from the JIT pass, so bookkeeping is cheap.
            #[cfg(feature = "jit")]
            let jit_handled = if let Some(ref processor) = self.jit_conflict_processor {
                // Incremental mode safety (#8489): push() adds variables via
                // new_var_internal() but does not recompile the JIT conflict
                // processor. The compiled code has baked-in buffer offsets
                // based on the original capacity, so we cannot just resize
                // the output buffer. Fall back to the scalar path when the
                // JIT's capacity is insufficient for the current var count.
                let num_vars = self.var_data.len();
                if processor.capacity() < num_vars {
                    false
                } else {
                    let lits = self.arena.literals(current_clause_offset);
                    let skip_lit = p.map_or(u32::MAX, |l| l.0);
                    // SAFETY: var_data is a valid VarData array covering all
                    // vars in the clause. The JIT writes only to VarData.flags
                    // (seen bit) and reads level fields. No concurrent access.
                    // The output buffer is pre-sized to num_vars (#8383), so
                    // overflow is impossible. vals[] is passed for ghost literal
                    // guard (#8434): after chrono-BT, unassigned literals are
                    // skipped to prevent counter inflation.
                    #[allow(unsafe_code)]
                    unsafe {
                        processor.process_literals(
                            bytemuck::cast_slice(lits),
                            self.var_data.as_mut_ptr().cast::<u8>(),
                            self.decision_level,
                            skip_lit,
                            &mut self.jit_conflict_output,
                            self.vals.as_ptr(),
                        );
                    }
                    self.stats.sat_conflict_analysis_native_applications = self
                        .stats
                        .sat_conflict_analysis_native_applications
                        .saturating_add(1);

                    // Debug-mode cross-validation (#8550): verify JIT scalar
                    // outputs match the interpreter. The JIT and interpreter
                    // implement the same algorithm; any mismatch indicates a
                    // code-generation bug. Only enabled in debug builds.
                    //
                    // Strategy: save post-JIT flags, restore pre-JIT flags,
                    // run interpreter, compare outputs, then restore post-JIT
                    // flags. The interpreter produces identical seen-flag
                    // side-effects, so the final state is correct.
                    #[cfg(debug_assertions)]
                    #[allow(unsafe_code)]
                    {
                        let raw_lits: &[u32] = bytemuck::cast_slice(lits);
                        // Save post-JIT flags for vars referenced by lits,
                        // then restore to pre-JIT state (clear seen bit for
                        // vars that the JIT just marked).
                        // Uses persistent buffer from cold state (#8599) —
                        // cleared per conflict instead of reallocated.
                        let jit_seen_count = self.jit_conflict_output.seen_count() as usize;
                        self.cold.debug_jit_flags_buf.clear();
                        for i in 0..jit_seen_count {
                            let var_idx = self.jit_conflict_output.seen_var(i) as usize;
                            let post_flags = self.var_data[var_idx].flags;
                            self.cold.debug_jit_flags_buf.push((var_idx, post_flags));
                            // Clear seen bit to restore pre-JIT state.
                            self.var_data[var_idx].flags = post_flags & !VarData::FLAG_SEEN_PUB;
                        }

                        // Reuse persistent interpreter output from cold state
                        // (#8599). Resize if num_vars grew since last use.
                        let num_vars_now = self.var_data.len();
                        if self.cold.debug_interp_output.capacity() < num_vars_now {
                            self.cold.debug_interp_output.resize(num_vars_now);
                        } else {
                            self.cold.debug_interp_output.reset();
                        }
                        // SAFETY: same invariants as the JIT call above — var_data
                        // and vals are valid, output buffer is sized to num_vars.
                        unsafe {
                            ay_jit::conflict_jit::process_literals_interpreter(
                                raw_lits,
                                self.var_data.as_mut_ptr().cast::<u8>(),
                                self.decision_level,
                                skip_lit,
                                &mut self.cold.debug_interp_output,
                                self.vals.as_ptr(),
                            );
                        }

                        debug_assert_eq!(
                            self.jit_conflict_output.counter(),
                            self.cold.debug_interp_output.counter(),
                            "BUG(#8550): JIT/interpreter counter mismatch: \
                         jit={} interp={}",
                            self.jit_conflict_output.counter(),
                            self.cold.debug_interp_output.counter(),
                        );
                        debug_assert_eq!(
                            self.jit_conflict_output.learned_count(),
                            self.cold.debug_interp_output.learned_count(),
                            "BUG(#8550): JIT/interpreter learned_count mismatch: \
                         jit={} interp={}",
                            self.jit_conflict_output.learned_count(),
                            self.cold.debug_interp_output.learned_count(),
                        );
                        debug_assert_eq!(
                            self.jit_conflict_output.resolvent_size(),
                            self.cold.debug_interp_output.resolvent_size(),
                            "BUG(#8550): JIT/interpreter resolvent_size mismatch: \
                         jit={} interp={}",
                            self.jit_conflict_output.resolvent_size(),
                            self.cold.debug_interp_output.resolvent_size(),
                        );
                        // Interpreter set the same seen bits as JIT, so
                        // var_data flags are now in the correct post-JIT state.
                        // No explicit flag restoration needed.
                    }

                    // Ghost literal handling (#8360, #8434, #8489): The JIT has
                    // a vals[]-based ghost guard that skips unassigned literals
                    // (vals[lit] >= 0) before counting or recording them. This
                    // means the JIT's counter, resolvent_size, learned_buf, and
                    // seen_vars outputs already EXCLUDE ghost literals. No
                    // post-hoc subtraction is needed.
                    //
                    // HISTORY: Before #8434 added the vals[] ghost guard to the
                    // JIT, a correction loop here subtracted ghost contributions
                    // from JIT counters. That loop was incorrect after #8434
                    // because it double-subtracted (JIT already excluded ghosts,
                    // then the loop subtracted again), causing u32 underflow
                    // panic (#8489). Removed in #8489.
                    //
                    // Optimization (#8466, #8489): when ghost_guard_needed is false
                    // (num_vars <= CHRONO_LEVEL_LIMIT AND not in incremental mode),
                    // neither chrono-BT nor push/pop can produce ghost literals.
                    // Skip the per-variable var_is_assigned() checks entirely.

                    let seen_count = self.jit_conflict_output.seen_count() as usize;

                    // Apply JIT classification results directly — ghost literals
                    // were already filtered by the JIT's vals[] guard (#8434).
                    counter += self.jit_conflict_output.counter();
                    resolvent_size += self.jit_conflict_output.resolvent_size();

                    // Add learned literals from JIT output buffer, filtering
                    // out ghost literals and non-false literals (#8482).
                    let learned_count = self.jit_conflict_output.learned_count() as usize;
                    let mut nonfals_learned_skipped: u32 = 0;
                    for i in 0..learned_count {
                        let raw_lit = self.jit_conflict_output.learned_lit(i);
                        let lit = Literal(raw_lit);
                        let var_idx = lit.variable().index();
                        // Guard (#8434): skip ghost literals from chrono-BT.
                        if !self.var_is_assigned(var_idx) {
                            continue;
                        }
                        // Guard (#8482): skip non-false literals. The JIT conflict
                        // processor classifies by level without checking vals[].
                        // Direct set_seen(false) bypasses ConflictAnalyzer
                        // bookkeeping (#8498). This is safe because:
                        // 1. The JIT set this seen flag in the CURRENT loop
                        //    iteration — register_jit_seen has not yet run.
                        // 2. The variable IS in the JIT's seen_vars output, but
                        //    the bookkeeping pass below (line ~205) skips it
                        //    because is_seen() returns false.
                        // 3. Net result: flag is false, var is not in
                        //    seen_to_clear — consistent state.
                        // 4. seen_true_count discrepancy (debug only) is handled
                        //    by the unconditional reset in clear().
                        if self.lit_val(lit) >= 0 {
                            nonfals_learned_skipped += 1;
                            self.var_data[var_idx].set_seen(false);
                            continue;
                        }
                        // Level load hits the VarData cache line the JIT just
                        // wrote (flags), feeding the backtrack-level/watch-swap
                        // fold (#8790).
                        let var_level = self.var_data[var_idx].level;
                        self.conflict.add_to_learned_tracked(lit, var_level);
                    }
                    // Correct resolvent_size for non-false learned literals that
                    // were skipped but counted by the JIT.
                    resolvent_size = resolvent_size.saturating_sub(nonfals_learned_skipped);

                    // Bookkeeping pass 1: register newly-seen vars and track
                    // max trail_pos of new current-level seen vars for the
                    // chrono-BT backward scan fix (#8360).
                    // The JIT wrote all newly-seen var_idx values into
                    // seen_vars. We iterate them to: push to seen_to_clear,
                    // call track_level_seen, and collect LRAT level-0 vars.
                    // With dynamic buffers (#8383), all vars are recorded.
                    // Ghost literals are excluded by the JIT's vals[] guard
                    // (#8434) so none should appear in seen_vars.
                    for i in 0..seen_count {
                        let var_idx = self.jit_conflict_output.seen_var(i) as usize;

                        // Skip ghost variables and non-false variables whose
                        // seen flag was cleared in the learned literal pass (#8482).
                        if !self.var_is_assigned(var_idx) {
                            continue;
                        }
                        if !self.var_data[var_idx].is_seen() {
                            continue;
                        }

                        self.conflict.register_jit_seen(var_idx);

                        let var_level = self.var_data[var_idx].level;
                        debug_assert!(
                            var_level <= self.decision_level,
                            "BUG: analyzed literal var={} at level {} exceeds \
                         decision level {}",
                            var_idx,
                            var_level,
                            self.decision_level,
                        );

                        if var_level > 0 {
                            self.track_level_seen(var_level, var_idx);
                        } else if self.cold.lrat_enabled {
                            lrat_level0_vars.push(var_idx);
                        }

                        // Chrono-BT scan fix (#8360): track max trail_pos of
                        // newly-seen current-level vars so the backward scan
                        // starts above all of them.
                        if var_level == self.decision_level {
                            let tp = self.var_data[var_idx].trail_pos as usize + 1;
                            if tp > index {
                                index = tp;
                            }
                        }
                    }
                    #[cfg(debug_assertions)]
                    {
                        for i in 0..seen_count {
                            let var_idx = self.jit_conflict_output.seen_var(i) as usize;
                            debug_assert!(
                                self.var_is_assigned(var_idx),
                                "BUG(#8760): conflict-analysis JIT emitted \
                                 unassigned ghost var {var_idx} in seen_vars"
                            );
                            self.conflict
                                .debug_assert_jit_seen_bookkeeping(var_idx, &self.var_data);
                        }
                    }

                    // Bookkeeping pass 2: tick accounting and antecedent_size.
                    // Batch tick: charge clause_len ticks upfront instead of
                    // per-literal increment (#8569). CaDiCaL charges 1 tick per
                    // literal in analyze_reason; batch is equivalent.
                    self.search_ticks[usize::from(self.stable_mode)] += clause_len as u64;

                    // OTFS antecedent_size: count non-level-0, non-p literals.
                    let lits = self.arena.literals(current_clause_offset);
                    for &lit in lits {
                        if let Some(p_lit) = p {
                            if lit == p_lit {
                                continue;
                            }
                        }

                        let var_idx = lit.variable().index();

                        // Guard (#8434): skip unassigned ghost literals after
                        // chrono-BT find_conflict_level backtrack.
                        // Optimization (#8466): skip check when ghosts impossible.
                        if self.ghost_guard_needed && self.lit_val(lit) >= 0 {
                            ghost_literal_dropped = true;
                            continue;
                        }

                        let var_level = self.var_data[var_idx].level;

                        debug_assert!(
                            !self.ghost_guard_needed || self.lit_val(lit) < 0,
                            "BUG: literal {:?} (var={}) in conflict/reason \
                         clause is not falsified (val={})",
                            lit,
                            var_idx,
                            self.lit_val(lit),
                        );

                        // OTFS: count non-level-0 literals toward
                        // antecedent_size regardless of seen status.
                        // CaDiCaL: analyze.cpp:270.
                        if var_level > 0 {
                            antecedent_size += 1;
                        }
                    }

                    true
                } // end capacity-sufficient else block
            } else {
                false
            };

            // Interpreter path: used when JIT is not compiled or not available.
            #[cfg(feature = "jit")]
            if !jit_handled {
                // Batch tick: charge clause_len ticks upfront (#8569).
                self.search_ticks[usize::from(self.stable_mode)] += clause_len as u64;
                for i in 0..clause_len {
                    let lit = self.arena.literal_at(current_clause_offset, i);
                    if let Some(p_lit) = p {
                        if lit == p_lit {
                            continue;
                        }
                    }
                    let var = lit.variable();
                    let var_idx = var.index();
                    // Guard (#8434): skip unassigned ghost literals after
                    // chrono-BT find_conflict_level backtrack.
                    // Optimization (#8466): skip check when ghosts impossible.
                    if self.ghost_guard_needed && self.lit_val(lit) >= 0 {
                        ghost_literal_dropped = true;
                        continue;
                    }
                    let var_level = self.var_data[var_idx].level;
                    debug_assert!(
                        !self.ghost_guard_needed || self.lit_val(lit) < 0,
                        "BUG: literal {:?} (var={}) in conflict/reason clause is not falsified (val={})",
                        lit, var_idx, self.lit_val(lit),
                    );
                    if var_level > 0 {
                        antecedent_size += 1;
                    }
                    if !self.conflict.is_seen(var_idx, &self.var_data) {
                        self.conflict.mark_seen(var_idx, &mut self.var_data);
                        debug_assert!(
                            var_level <= self.decision_level,
                            "BUG: analyzed literal var={} at level {} exceeds decision level {}",
                            var_idx,
                            var_level,
                            self.decision_level,
                        );
                        if var_level > 0 {
                            self.track_level_seen(var_level, var_idx);
                        }
                        if var_level == self.decision_level {
                            counter += 1;
                            // Chrono-BT scan fix (#8360): track max trail_pos
                            // so backward scan starts above all current-level
                            // seen vars.
                            let tp = self.var_data[var_idx].trail_pos as usize + 1;
                            if tp > index {
                                index = tp;
                            }
                        } else if var_level > 0 {
                            self.conflict.add_to_learned_tracked(lit, var_level);
                        } else if self.cold.lrat_enabled {
                            lrat_level0_vars.push(var_idx);
                        }
                        if var_level > 0 {
                            resolvent_size += 1;
                        }
                    }
                }
            }

            #[cfg(not(feature = "jit"))]
            {
                // Batch tick: charge clause_len ticks upfront instead of
                // per-literal increment (#8569). CaDiCaL charges per-literal in
                // analyze_literal / analyze_reason (analyze.cpp:253-327).
                self.search_ticks[usize::from(self.stable_mode)] += clause_len as u64;
                for i in 0..clause_len {
                    let lit = self.arena.literal_at(current_clause_offset, i);
                    if let Some(p_lit) = p {
                        if lit == p_lit {
                            continue;
                        }
                    }

                    let var = lit.variable();
                    let var_idx = var.index();

                    // Guard (#8434): after chrono-BT find_conflict_level backtracks,
                    // some conflict/reason clause literals may be unassigned. Their
                    // var_data.level retains a stale value (backtrack only clears
                    // vals[], not var_data). In release mode the debug_assert below
                    // is absent, so these ghost literals would inflate `counter` and
                    // cause the backward trail scan to exhaust. Skip them.
                    // Optimization (#8466): skip check when ghosts impossible.
                    if self.ghost_guard_needed && self.lit_val(lit) >= 0 {
                        ghost_literal_dropped = true;
                        continue;
                    }

                    let var_level = self.var_data[var_idx].level;

                    // Every literal in a conflict/reason clause must be falsified
                    // under the current assignment. CaDiCaL: analyze.cpp:265,276.
                    debug_assert!(
                    !self.ghost_guard_needed || self.lit_val(lit) < 0,
                    "BUG: literal {:?} (var={}) in conflict/reason clause is not falsified (val={})",
                    lit,
                    var_idx,
                    self.lit_val(lit),
                );

                    // OTFS: count non-level-0 literals toward antecedent_size
                    // regardless of seen status. CaDiCaL: analyze.cpp:270.
                    if var_level > 0 {
                        antecedent_size += 1;
                    }

                    if !self.conflict.is_seen(var_idx, &self.var_data) {
                        self.conflict.mark_seen(var_idx, &mut self.var_data);

                        debug_assert!(
                            var_level <= self.decision_level,
                            "BUG: analyzed literal var={} at level {} exceeds decision level {}",
                            var_idx,
                            var_level,
                            self.decision_level,
                        );

                        if var_level > 0 {
                            self.track_level_seen(var_level, var_idx);
                        }

                        if var_level == self.decision_level {
                            counter += 1;
                            // Chrono-BT scan fix (#8360): under chronological
                            // backtracking with trail compaction, a reason clause
                            // can introduce a newly-seen current-level literal
                            // whose trail_pos is ABOVE the current backward scan
                            // cursor. This happens because compaction preserves
                            // relative trail order but collapses gaps left by
                            // unassigned higher-level variables, so propagation
                            // order within a level may not match the compacted
                            // position order. Without this adjustment, the
                            // backward scan walks past all remaining current-level
                            // seen literals and panics at index=0.
                            // Fix: advance the scan cursor above this literal's
                            // trail_pos so the next backward scan will find it.
                            let tp = self.var_data[var_idx].trail_pos as usize + 1;
                            if tp > index {
                                index = tp;
                            }
                        } else if var_level > 0 {
                            self.conflict.add_to_learned_tracked(lit, var_level);
                        } else if self.cold.lrat_enabled {
                            lrat_level0_vars.push(var_idx);
                        }

                        if var_level > 0 {
                            resolvent_size += 1;
                        }
                    }
                }
            } // end cfg(not(feature = "jit")) block

            // CaDiCaL analyze.cpp:1066 invariant: resolvent_size == open + clause.size().
            // In AY: resolvent_size == counter (current-level seen) + learned_count
            // (non-current-level, non-level-0 literals added to the learned clause).
            // Fires immediately when stale seen marks corrupt the accounting.
            debug_assert_eq!(
                resolvent_size,
                counter + self.conflict.learned_count() as u32,
                "BUG: resolvent_size ({resolvent_size}) != counter ({counter}) + \
                 learned_count ({}) — possible stale seen mark (resolved={resolved})",
                self.conflict.learned_count(),
            );

            // CaDiCaL analyze.cpp:1064-1065: capture conflict clause size
            // (non-level-0 lits excluding UIP) on first iteration for OTF subsumption.
            if resolved == 0 {
                conflict_size = antecedent_size.saturating_sub(1);
            }

            // OTFS (#4598, #8105, #8439): strengthen the previous reason when
            // the current resolvent already subsumes it. Enabled unconditionally
            // (backward LRAT reconstruction handles proof obligations).
            // Safe during backbone probing: the pivot's reason pointer is
            // preserved after strengthening, so subsequent conflict analyses
            // resolve correctly without the suppress_otfs workaround.
            {
                // Under LRAT, otfs_strengthen() always returns false (it emits
                // TrustedTransform, unsupported by the backward LRAT pass), so the
                // whole OTFS block below is dead work in the competition hot loop:
                // the post_otfs_open scan + otfs_strengthen's clause-copy alloc run
                // every qualifying conflict only to fall through unchanged. Skip it
                // when LRAT is active — bit-identical solving, faster Main route.
                let otfs_active = !self.cold.lrat_enabled;
                if let Some(prev_reason) = last_reason_ref {
                    if otfs_active
                        && resolved > 0
                        && antecedent_size > 2
                        && resolvent_size < antecedent_size
                    {
                        self.stats.otfs_candidates += 1;
                        let p_lit = p.expect("conflict analysis: p set for OTFS");

                        // Skip OTFS if strengthening would remove every current-level
                        // literal or violate the watch invariant.
                        let pre_reason_lits = self.arena.literals(prev_reason.0 as usize);
                        let pivot_var = p_lit.variable();
                        let post_otfs_open = pre_reason_lits
                            .iter()
                            .filter(|l| {
                                l.variable() != pivot_var
                                    && self.var_data[l.variable().index()].level
                                        == self.decision_level
                            })
                            .count();

                        let watch_ok = pre_reason_lits.len() < 2
                            || self.lit_val(pre_reason_lits[0]) > 0
                            || self.lit_val(pre_reason_lits[1]) > 0;

                        if post_otfs_open == 0 || !watch_ok {
                            if post_otfs_open == 0 {
                                self.stats.otfs_blocked_open0 += 1;
                            }
                            if !watch_ok {
                                self.stats.otfs_blocked_watch += 1;
                            }
                            // Don't strengthen — fall through to normal analysis
                        } else if !self.otfs_strengthen(prev_reason, p_lit) {
                            self.stats.otfs_blocked_strengthen += 1;
                            // otfs_strengthen returned false — fall through
                        } else {
                            self.stats.otfs_subsumed += 1;

                            // CaDiCaL analyze.cpp:1097-1105: on-the-fly subsumption.
                            // When resolved==1 (first resolution step), the strengthened
                            // reason is a subset of the original conflict clause. The
                            // conflict clause is all-false and not a propagation reason,
                            // so it can be safely marked as garbage (deferred GC).
                            if resolved == 1
                                && conflict_size >= 2
                                && resolvent_size < conflict_size
                                && current_conflict_ref != prev_reason
                            {
                                self.stats.otfs_clause_subsumed += 1;
                                self.otfs_subsume(prev_reason, current_conflict_ref);
                            }

                            // CaDiCaL analyze.cpp:1107-1108: update conflict reference
                            // to the strengthened reason for subsequent OTFS iterations.
                            current_conflict_ref = prev_reason;

                            if post_otfs_open == 1 {
                                // Branch B: the strengthened clause is already asserting.
                                self.stats.otfs_branch_b += 1;
                                let (asserting_lit, bt_level) = {
                                    let strengthened_lits =
                                        self.arena.literals(prev_reason.0 as usize);
                                    let mut forced = None;
                                    let mut bt_level: u32 = 0;
                                    for &lit in strengthened_lits {
                                        let lv = self.var_data[lit.variable().index()].level;
                                        if lv == self.decision_level {
                                            debug_assert!(
                                                forced.is_none(),
                                                "BUG: OTFS Branch B found 2+ current-level lits"
                                            );
                                            forced = Some(lit);
                                        } else if lv > bt_level {
                                            bt_level = lv;
                                        }
                                    }
                                    (
                                        forced.expect(
                                            "BUG: OTFS Branch B: no current-level literal found",
                                        ),
                                        bt_level,
                                    )
                                };

                                self.conflict.clear(&mut self.var_data);
                                self.clear_level_seen();

                                let branch_b_offset = prev_reason.0 as usize;
                                let branch_b_len = self.arena.len_of(branch_b_offset);
                                self.conflict.set_asserting_literal(asserting_lit);
                                for i in 0..branch_b_len {
                                    let lit = self.arena.literal_at(branch_b_offset, i);
                                    if lit.variable() != asserting_lit.variable() {
                                        self.conflict.add_to_learned(lit);
                                    }
                                }

                                // compute_lbd already uses CaDiCaL convention (levels - 1).
                                // No additional +1 needed (#8135).
                                let lbd = self.conflict.compute_lbd(&self.var_data);
                                let mut result = self.conflict.get_result(bt_level, lbd);
                                crate::conflict::reorder_for_watches(
                                    &mut result.learned_clause,
                                    &self.var_data,
                                    bt_level,
                                );
                                result.otfs_driving_clause = Some(prev_reason);
                                self.cold.lrat_level0_vars_buf = lrat_level0_vars;
                                return Some(result);
                            }

                            debug_assert!(
                                post_otfs_open > 1,
                                "BUG: OTFS Branch C reached with open={post_otfs_open} <= 1"
                            );
                            // Branch C: analysis restarted from strengthened clause.
                            self.stats.otfs_branch_c += 1;
                            self.conflict.clear(&mut self.var_data);
                            self.clear_level_seen();
                            counter = 0;
                            p = None;
                            index = self.trail.len();
                            resolved = 0;
                            resolvent_size = 0;
                            lrat_level0_vars.clear();
                            last_reason_ref = None;

                            self.bump_clause(prev_reason);

                            // Streaming support: mark an original OTFS reason (#8250).
                            self.mark_streaming_core(prev_reason);

                            if self.cold.lrat_enabled {
                                let id = self.clause_id(prev_reason);
                                if id != 0 {
                                    self.conflict.add_to_chain(id);
                                }
                            }

                            current_clause_offset = prev_reason.0 as usize;
                            current_clause_len = self.arena.len_of(current_clause_offset);
                            continue;
                        }
                    }
                }
            } // end OTFS block

            // Scan backward for the next seen literal at the current level.
            //
            // Chrono-BT scan fix (#8360): `index` may have been advanced
            // above its previous value by the clause processing above when
            // a reason clause introduced a newly-seen current-level literal
            // at a higher trail_pos than the current scan cursor. The scan
            // starts from the (potentially raised) `index` and walks down.
            //
            // Trail exhaustion guard (#8479): under chronological backtracking,
            // trail_pos values can be stale (backtrack only clears vals[], not
            // var_data.trail_pos). The chrono-BT scan fix can push `index`
            // past trail.len(). Cap it, and if the scan exhausts without
            // finding a match, bail out gracefully instead of panicking.
            let trail_len = self.trail.len();
            if index > trail_len {
                index = trail_len;
            }
            if index == 0 {
                self.stats.trail_exhaustion_bailouts += 1;
                self.conflict.clear(&mut self.var_data);
                self.clear_level_seen();
                self.cold.lrat_level0_vars_buf = lrat_level0_vars;
                return None;
            }
            loop {
                index -= 1;
                let trail_lit = self.trail[index];
                let var_idx = trail_lit.variable().index();
                if self.conflict.is_seen(var_idx, &self.var_data)
                    && self.var_data[var_idx].level == self.decision_level
                {
                    p = Some(trail_lit);
                    break;
                }
                if index == 0 {
                    self.stats.trail_exhaustion_bailouts += 1;
                    self.conflict.clear(&mut self.var_data);
                    self.clear_level_seen();
                    self.cold.lrat_level0_vars_buf = lrat_level0_vars;
                    return None;
                }
            }

            // Keep seen marks until the end of analysis (#7331).
            // Counter must be > 0 because the backward scan just found a
            // seen+current-level literal, and counter was incremented for
            // each such literal during clause processing. If counter is 0,
            // the literal we found was somehow miscounted.
            debug_assert!(
                counter > 0,
                "BUG: analysis counter underflow before resolving {p:?} \
                 (counter={counter}, decision_level={}, resolved={resolved}, \
                 resolvent_size={resolvent_size})",
                self.decision_level,
            );
            if counter == 0 {
                // Release-mode guard: prevent u32 underflow.
                self.stats.trail_exhaustion_bailouts += 1;
                self.conflict.clear(&mut self.var_data);
                self.clear_level_seen();
                self.cold.lrat_level0_vars_buf = lrat_level0_vars;
                return None;
            }
            counter -= 1;

            if counter == 0 {
                solver_log!(
                    self,
                    "1UIP: {}",
                    p.expect("invariant: p set in resolution loop").to_dimacs()
                );
                break; // Found 1UIP
            }

            // Trail exhaustion guard: if index reached 0 but counter > 0,
            // bail out rather than continuing with a corrupted analysis.
            // This can happen under chrono-BT when trail_pos values are stale
            // or when OTFS modifies reason clauses, causing the backward scan
            // to exhaust without finding all expected current-level seen lits.
            // The debug_assert catches this for investigation; the release
            // guard prevents UB (index underflow) and data corruption.
            debug_assert!(
                index > 0,
                "BUG: trail exhausted with counter={counter} > 0 — no more seen literals \
                 (dl={}, resolved={resolved}, resolvent_size={resolvent_size}, \
                 otfs_strengthened={})",
                self.decision_level,
                self.stats.otfs_strengthened,
            );
            if index == 0 {
                self.stats.trail_exhaustion_bailouts += 1;
                self.conflict.clear(&mut self.var_data);
                self.clear_level_seen();
                self.cold.lrat_level0_vars_buf = lrat_level0_vars;
                return None;
            }

            let p_var = p
                .expect("conflict analysis: p set for reason lookup")
                .variable();
            debug_assert!(
                self.lit_val(p.expect("p for val check")) > 0,
                "BUG: resolved literal p (var={}) is not assigned true on trail",
                p_var.index(),
            );
            // LSCB (#8442): Lambda reason substitution DISABLED.
            // The lambda clause may not actually be the reason for the current
            // assignment at the current level. Using it in resolution produces
            // learned clauses that are not RUP-derivable, causing false UNSAT
            // on SAT instances (e.g., ecarev-110, battleship-14-26).
            // The lambda reason can only be safely used after the variable is
            // actually reimplied at the lower level during backtracking.
            let reason_kind = self.var_reason_kind(p_var.index());
            match reason_kind {
                ReasonKind::Decision => {
                    // We only query a reason after consuming a current-level
                    // seen literal and finding that more current-level literals
                    // remain (`counter > 0`). A genuine CDCL decision can only
                    // be the UIP and would have broken out before this point.
                    // Treat a non-UIP NO_REASON as unreconstructable analysis
                    // state and let the caller restart from level 0 rather than
                    // learning a clause with multiple current-level literals.
                    self.stats.trail_exhaustion_bailouts += 1;
                    self.conflict.clear(&mut self.var_data);
                    self.clear_level_seen();
                    self.cold.lrat_level0_vars_buf = lrat_level0_vars;
                    return None;
                }
                ReasonKind::BinaryLiteral(reason_lit) => {
                    // Binary literal reason (#8034): virtual clause [p, reason_lit].
                    // Resolve the single reason literal inline without arena access.
                    let var_idx = reason_lit.variable().index();
                    let var_level = self.var_data[var_idx].level;

                    debug_assert!(
                        !self.ghost_guard_needed || self.lit_val(reason_lit) < 0,
                        "BUG: binary reason literal {:?} (var={}) is not falsified (val={})",
                        reason_lit,
                        var_idx,
                        self.lit_val(reason_lit),
                    );

                    // Guard (#8434): skip unassigned ghost literals after
                    // chrono-BT find_conflict_level backtrack. The reason lit
                    // may be at a level above conflict_level and thus unassigned.
                    // Optimization (#8466): skip check when ghosts impossible.
                    if self.ghost_guard_needed && self.lit_val(reason_lit) >= 0 {
                        // Literal is unassigned — skip. Still count the resolution
                        // step. The tick, resolved++, resolvent_size-- are handled
                        // below after the seen block.
                        ghost_literal_dropped = true;
                    } else if !self.conflict.is_seen(var_idx, &self.var_data) {
                        self.conflict.mark_seen(var_idx, &mut self.var_data);

                        if var_level > 0 {
                            self.track_level_seen(var_level, var_idx);
                        }

                        if var_level == self.decision_level {
                            counter += 1;
                            // Chrono-BT scan fix (#8360): advance scan cursor
                            // above this literal so the backward scan finds it.
                            let tp = self.var_data[var_idx].trail_pos as usize + 1;
                            if tp > index {
                                index = tp;
                            }
                        } else if var_level > 0 {
                            self.conflict.add_to_learned_tracked(reason_lit, var_level);
                        } else if self.cold.lrat_enabled {
                            lrat_level0_vars.push(var_idx);
                        }

                        if var_level > 0 {
                            resolvent_size += 1;
                        }
                    }

                    // Tick accounting: charge 1 search tick per binary reason
                    // resolved. CaDiCaL processes all reasons (including binary)
                    // through Clause* which gets charged in bump_also. AY's jump
                    // reasons (#8034) bypass that path, so we charge here (#8148).
                    self.search_ticks[usize::from(self.stable_mode)] += 1;

                    resolved += 1;
                    last_reason_ref = None;
                    debug_assert!(
                        resolvent_size > 0,
                        "BUG: resolvent_size underflow during conflict analysis \
                         (counter={counter}, decision_level={}, resolved={resolved})",
                        self.decision_level,
                    );
                    resolvent_size = resolvent_size.saturating_sub(1);
                    current_clause_len = 0;
                    continue;
                }
                ReasonKind::LazyTheory(_lazy_idx) => {
                    // Lazy theory reason (#8467): current-level lazy reasons
                    // should have been pre-materialized by
                    // materialize_current_level_lazy_reasons() before analysis.
                    // If we reach here, it means a lazy reason at the current
                    // level was not materialized. As with non-UIP NO_REASON,
                    // fail closed instead of learning from an incomplete proof
                    // explanation.
                    self.stats.trail_exhaustion_bailouts += 1;
                    self.conflict.clear(&mut self.var_data);
                    self.clear_level_seen();
                    self.cold.lrat_level0_vars_buf = lrat_level0_vars;
                    return None;
                }
                ReasonKind::Clause(reason_ref) => {
                    // Note: this check is relaxed to allow OTFS-modified reason
                    // clauses (#8241, #8439). When OTFS strengthens a clause by
                    // removing the pivot literal, the pivot's reason pointer is
                    // preserved (points to the strengthened clause). The clause
                    // no longer contains p_lit, but this is correct: the `if lit
                    // == p_lit { continue; }` skip is a no-op (pivot absent), and
                    // all remaining literals are processed normally. The clause
                    // still semantically implies the pivot.
                    // CaDiCaL does not perform this check (analyze.cpp:316-327).
                    debug_assert!(
                        {
                            let p_lit = p.expect("conflict analysis: p for reason check");
                            let reason_lits = self.arena.literals(reason_ref.0 as usize);
                            // Allow OTFS-strengthened clauses where the pivot was
                            // removed: the clause must either contain p_lit OR have
                            // been modified by OTFS (detectable by the pivot's
                            // reason pointing to a clause that doesn't contain it).
                            reason_lits.contains(&p_lit) || self.stats.otfs_strengthened > 0
                        },
                        "BUG: reason clause for var={} does not contain the propagated literal \
                         (not OTFS-related: otfs_strengthened=0)",
                        p_var.index(),
                    );

                    debug_assert!(
                        !self.arena.is_empty_clause(reason_ref.0 as usize),
                        "BUG: reason clause {} for var={} is deleted during analysis",
                        reason_ref.0,
                        p_var.index(),
                    );
                    // Unit-reason clauses (len == 1) can occur legitimately when
                    // inprocessing strengthens a binary reason clause to a unit
                    // during level-0 subsumption/vivification (#8491). The
                    // variable's reason pointer is not cleared because the variable's
                    // literal is kept in the unit clause. Resolution handles this
                    // correctly: the single literal is the implied literal (p_lit),
                    // the `if lit == p_lit { continue; }` skip fires, and no new
                    // literals are added — equivalent to treating it as a decision.
                    // CaDiCaL does not check this (analyze.cpp:316-327).
                    debug_assert!(
                        self.arena.len_of(reason_ref.0 as usize) >= 1,
                        "BUG: reason clause {} for var={} has len {} < 1 (empty/deleted)",
                        reason_ref.0,
                        p_var.index(),
                        self.arena.len_of(reason_ref.0 as usize),
                    );

                    self.bump_clause(reason_ref);
                    if triage_enabled() {
                        TRIAGE_ANTECEDENTS.with(|b| b.borrow_mut().push(reason_ref.0));
                    }

                    // Streaming support: mark the reason if it is original (#8250).
                    self.mark_streaming_core(reason_ref);

                    // Tick accounting: charge 1 search tick per reason clause
                    // resolved during 1UIP analysis. This is the clause-access
                    // charge matching CaDiCaL's pattern where each resolved
                    // reason contributes to the effort metric (#8148).
                    self.search_ticks[usize::from(self.stable_mode)] += 1;

                    if self.cold.lrat_enabled {
                        let id = self.clause_id(reason_ref);
                        if id != 0 {
                            self.conflict.add_to_chain_with_pivot(
                                id,
                                p.expect("conflict analysis: p for resolution pivot"),
                            );
                        }
                    }

                    resolved += 1;
                    last_reason_ref = Some(reason_ref);

                    debug_assert!(
                        resolvent_size > 0,
                        "BUG: resolvent_size underflow during conflict analysis \
                         (counter={counter}, decision_level={}, resolved={resolved})",
                        self.decision_level,
                    );
                    resolvent_size = resolvent_size.saturating_sub(1);

                    current_clause_offset = reason_ref.0 as usize;
                    current_clause_len = self.arena.len_of(current_clause_offset);
                }
            }
        }

        debug_assert_eq!(
            counter, 0,
            "BUG: exited analysis loop with counter={counter} != 0"
        );

        if ghost_literal_dropped && self.proof_manager.is_some() {
            // See the ghost-literal proof guard comment above: a ghost-dropped
            // learned clause is not RUP-derivable; do not learn or emit it.
            self.stats.trail_exhaustion_bailouts += 1;
            self.cold.lrat_level0_vars_buf = lrat_level0_vars;
            return None;
        }
        let uip = p.expect("conflict analysis: 1UIP found").negated();
        Some(self.finalize_conflict_analysis(uip, lrat_level0_vars))
    }

    /// Mark an antecedent only when its bounded ID was issued to an original.
    /// Late-original allocation can leave derived IDs in `1..=num_originals`,
    /// so range membership alone is insufficient for streaming support.
    #[inline(always)]
    pub(super) fn mark_streaming_core(&mut self, clause_ref: ClauseRef) {
        let num_originals = self.cold.streaming_core_num_originals;
        if num_originals == 0 {
            return;
        }
        let id = self.clause_id(clause_ref);
        if id > 0 && id <= num_originals && self.is_original_clause_id(id) {
            if let Some(ref mut bitmap) = self.cold.streaming_core {
                // clause IDs are 1-based, bitmap is 0-based
                bitmap[(id - 1) as usize] = true;
            }
        }
    }
}
// Post-analysis variable bumping (VSIDS/VMTF) is in conflict_analysis_bumping.rs.

#[cfg(test)]
#[path = "conflict_analysis_tests.rs"]
mod tests;
