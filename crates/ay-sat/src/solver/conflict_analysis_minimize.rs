// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause minimization for conflict analysis.
//!
//! CaDiCaL-style minimization with poison/removable marking to cache
//! results and avoid redundant work. Also includes LRAT chain computation
//! for literals removed by shrink/minimize.
//!
//! Instruction-shave #3 (see CaDiCaL `minimize.cpp:minimize_literal`): the
//! hot recursion loads `VarData` once per queried literal, reads per-level
//! seen tracking from a single merged `LevelSeen` array (one indexed load,
//! like CaDiCaL's `control[v.level].seen`), decodes the reason kind inline
//! from the already-loaded `VarData`, and shares one early-abort block
//! between the binary-reason and clause-reason paths. Semantics are
//! identical to the pre-shave two-array implementation: same verdict per
//! queried literal, same flag/side-effect order, same tick accounting.

use super::*;

impl Solver {
    /// Clear per-level seen tracking (CaDiCaL: `clear_analyzed_levels`).
    ///
    /// Resets `level_seen` for all levels that were touched during the most
    /// recent conflict analysis. Uses a dirty list (`level_seen_to_clear`)
    /// for O(touched) cleanup instead of O(max_level).
    pub(super) fn clear_level_seen(&mut self) {
        for &lvl in &self.min.level_seen_to_clear {
            let l = lvl as usize;
            if l < self.min.level_seen.len() {
                self.min.level_seen[l] = minimization_state::LevelSeen::EMPTY;
            }
        }
        self.min.level_seen_to_clear.clear();
        // Reset the incremental shrink-prescan bit (#8790). Required for OTFS
        // Branch C restarts, which re-track from scratch mid-analysis.
        self.min.level_seen_repeated_non_uip = false;
    }

    /// Track a newly-seen literal's decision level for minimize early-aborts.
    ///
    /// CaDiCaL `analyze_literal` (analyze.cpp:303-309): increments `seen.count`
    /// and updates `seen.trail` (minimum trail position) for the literal's level.
    #[inline]
    pub(super) fn track_level_seen(&mut self, var_level: u32, var_idx: usize) {
        let lvl = var_level as usize;
        // Grow tracking array if needed (decision levels can exceed initial
        // capacity). Cold out-of-line path keeps the hot body small.
        if lvl >= self.min.level_seen.len() {
            self.min.grow_level_seen(lvl);
        }
        let tpos = self.var_data[var_idx].trail_pos;
        let entry = &mut self.min.level_seen[lvl];
        let old_count = entry.count;
        entry.count = old_count + 1;
        if tpos < entry.trail {
            entry.trail = tpos;
        }
        if old_count == 0 {
            self.min.level_seen_to_clear.push(var_level);
        }
        // Fold of the shrink prescan (#8790): every tracked variable below the
        // conflict level is exactly a learned-clause literal, so a non-UIP
        // level reaching count 2 — or a tracked literal with a stale trail
        // position — is precisely what
        // `learned_clause_has_repeated_non_uip_level` would detect at
        // finalize. (Its non-falsified and level-0 branches cannot fire for
        // tracked variables: learned literals are falsified with level > 0 at
        // add time and neither vals nor levels change during analysis.)
        if var_level != self.decision_level && (old_count >= 1 || tpos as usize >= self.trail.len())
        {
            self.min.level_seen_repeated_non_uip = true;
        }
    }

    /// Minimize the learned clause by removing redundant literals.
    ///
    /// Uses CaDiCaL-style minimization with poison/removable marking to cache
    /// results and avoid redundant work. A literal is redundant if it can be
    /// derived from other literals in the learned clause through resolution.
    pub(super) fn minimize_learned_clause(&mut self) {
        self.minimize_learned_clause_collect_removed(None);
    }

    pub(super) fn minimize_learned_clause_collect_removed(
        &mut self,
        mut removed_lits: Option<&mut Vec<Literal>>,
    ) {
        // Bulk copy learned literals to clause_buf (reusable scratch buffer)
        // to break the borrow conflict between self.conflict and self.minimize_*
        // arrays. Uses copy_learned_to_clause_buf for memcpy-speed instead of
        // per-element push (#8569).
        self.conflict.copy_learned_to_clause_buf();

        // CaDiCaL minimize.cpp:205-209: sort by trail position (ascending)
        // before minimization. Earlier-assigned literals are checked first;
        // their antecedents are more likely to be already marked removable
        // or visited, establishing base cases sooner for later recursion.
        {
            let var_data = &self.var_data;
            self.conflict
                .clause_buf_mut()
                .sort_unstable_by_key(|lit| var_data[lit.variable().index()].trail_pos);
        }

        // Mark all learned literals as "visited" (in the clause) and populate
        // per-level seen counters + earliest trail position (CaDiCaL l.seen).
        let buf_len = self.conflict.clause_buf_mut().len();
        for i in 0..buf_len {
            let lit = self.conflict.clause_buf_mut()[i];
            let var_idx = lit.variable().index();
            self.min.minimize_flags[var_idx] |= MIN_VISITED;
            self.min.minimize_to_clear.push(var_idx);

            let vd = self.var_data[var_idx];
            let lev = vd.level as usize;
            let entry = &mut self.min.minimize_level_seen[lev];
            if entry.count == 0 {
                self.min.minimize_levels_to_clear.push(lev as u32);
            }
            entry.count += 1;
            if vd.trail_pos < entry.trail {
                entry.trail = vd.trail_pos;
            }
        }

        // clause_buf is already sorted by trail position (sort above).
        // The marking loop above only reads clause_buf values — it does not
        // modify, remove, or reorder elements, so the sort order is preserved.

        // Run redundancy checks from the scratch buffer copy.
        // After this, minimize_removable[var] is true for literals that can be
        // removed; level-0 literals are also redundant but aren't in removable.
        // CaDiCaL minimize.cpp:134: progressively mark non-removable literals
        // as "keep" so later literals can use them as recursion base cases.
        for i in 0..buf_len {
            let lit = self.conflict.clause_buf_mut()[i];
            let redundant = self.is_redundant_cached(lit, 0);
            if !redundant {
                let v = lit.variable().index();
                self.min.minimize_flags[v] |= MIN_KEEP;
            }
        }

        // Compact learned in-place: retain only non-redundant literals.
        let var_data = &self.var_data;
        let flags = &self.min.minimize_flags;
        self.conflict.retain_learned(|lit| {
            let var_idx = lit.variable().index();
            let keep = var_data[var_idx].level != 0 && (flags[var_idx] & MIN_REMOVABLE == 0);
            if !keep {
                if let Some(removed) = removed_lits.as_deref_mut() {
                    removed.push(lit);
                }
            }
            keep
        });

        // Post-minimize: learned clause must be non-empty (UIP is separate,
        // but if all learned lits were removed, we still have a valid unit clause).
        // CaDiCaL: the learned clause can be empty (unit clause = just the UIP).

        // Clear all minimization state (CaDiCaL clear_minimized_literals)
        for &var_idx in &self.min.minimize_to_clear {
            self.min.minimize_flags[var_idx] = 0;
        }
        self.min.minimize_to_clear.clear();
        // Sparse reset of per-level tracking
        for &lev in &self.min.minimize_levels_to_clear {
            self.min.minimize_level_seen[lev as usize] = minimization_state::LevelSeen::EMPTY;
        }
        self.min.minimize_levels_to_clear.clear();
        // CaDiCaL analyze.cpp:448-450: all minimization flags cleared
        debug_assert!(
            self.min.minimize_to_clear.is_empty(),
            "BUG: minimize_to_clear not empty after clear"
        );
    }

    /// Check if a literal is redundant using cached poison/removable marks.
    ///
    /// Uses depth limiting and caches results for efficiency.
    /// Returns true if the literal can be removed from the learned clause.
    ///
    /// CaDiCaL `minimize_literal` (minimize.cpp:17-63). Flag-check order
    /// matters: removable/keep are checked BEFORE poison (a variable can
    /// carry both poison from a failed recursive check and keep from
    /// progressive marking; keep must win because the literal IS in the
    /// clause and is a valid dependency termination).
    pub(super) fn is_redundant_cached(&mut self, lit: Literal, depth: u32) -> bool {
        let var_idx = lit.variable().index();

        // Guard (#8434): after chrono-BT find_conflict_level backtracks,
        // reason clause literals can become unassigned while retaining stale
        // var_data.level values. During recursive minimization (depth > 0),
        // a reason clause may reference such ghost literals. Treating an
        // unassigned variable as non-removable is always safe — it prevents
        // the parent literal from being minimized away, which is conservative.
        if !self.var_is_assigned(var_idx) {
            return false;
        }

        // Single 16-byte VarData load for level/trail_pos/reason/flags
        // (CaDiCaL: one `Var &v = var(lit)` — shave #3 replaces the four
        // separate `self.var_data[var_idx].*` loads of the old code).
        let vd = self.var_data[var_idx];

        // Level 0 literals are always redundant (they're always false)
        if vd.level == 0 {
            return true;
        }

        // Check cached results — order matches CaDiCaL minimize.cpp:22-24:
        // removable and keep are checked BEFORE poison (see doc comment).
        let mf = self.min.minimize_flags[var_idx];
        if mf & (MIN_REMOVABLE | MIN_KEEP) != 0 {
            return true;
        }
        if mf & MIN_POISON != 0 {
            return false;
        }

        // CaDiCaL minimize.cpp:24: current-level literals cannot be minimized
        // (the only path through current-level literals is the 1UIP itself).
        if vd.level == self.decision_level {
            return false;
        }

        // For recursive calls (depth > 0): if literal is already in learned clause,
        // we've reached a "kept" literal which is good - this path terminates.
        // For top-level calls (depth == 0): we're checking if THIS literal can be
        // removed, so don't return early just because it's in the clause.
        if depth > 0 && mf & MIN_VISITED != 0 {
            return true;
        }

        // Decision variables and lazy theory reasons cannot be minimized
        // through normal clause recursion (same discrimination order as
        // `var_reason_kind`: NO_REASON, then lazy-theory flag, then the
        // binary-literal tag, else arena clause).
        // Lazy theory reasons (#8467) have not been materialized yet;
        // materializing during minimization is too expensive and may fail.
        let reason = vd.reason;
        if reason == NO_REASON || vd.is_lazy_theory_reason() {
            return false;
        }

        // Early-abort checks (CaDiCaL minimize.cpp:26-30), shared by the
        // binary-literal and clause reason paths.
        //
        // CaDiCaL reads `control[v.level].seen.count` and `.seen.trail` which
        // are populated for ALL variables seen during `analyze_literal` --
        // including current-level and resolved-away variables. AY mirrors this
        // via `level_seen` (set by `track_level_seen` during conflict
        // analysis). Using the analysis-phase data instead of the
        // minimize-phase data (which only covers learned-clause literals)
        // provides:
        //   1. Higher counts -- Knuth abort fires less often, enabling more
        //      minimization attempts on levels with resolved-away variables
        //   2. Lower trail positions -- trail-position abort fires less often,
        //      enabling minimization of variables assigned after resolved-away
        //      variables on the same level
        //
        // When analysis-phase data is available (normal pipeline:
        // analyze -> minimize -> clear_level_seen), prefer it. Fall back to
        // minimize-phase data for direct minimize_learned_clause() calls
        // (unit tests, isolated contexts).
        'aborts: {
            let var_level = vd.level as usize;
            let seen = if !self.min.level_seen_to_clear.is_empty()
                && var_level < self.min.level_seen.len()
            {
                self.min.level_seen[var_level]
            } else if !self.min.minimize_levels_to_clear.is_empty()
                && var_level < self.min.minimize_level_seen.len()
            {
                self.min.minimize_level_seen[var_level]
            } else {
                break 'aborts;
            };
            // Knuth's single-literal abort (CaDiCaL minimize.cpp:27-28):
            // if this is a top-level call and fewer than 2 literals from
            // this level were seen during analysis, minimization cannot
            // succeed (no other seen literal to serve as base case).
            if depth == 0 && seen.count < 2 {
                return false;
            }
            // Trail-position abort (CaDiCaL minimize.cpp:29-30): if this
            // variable was assigned at or before the earliest seen literal
            // on its level, it cannot be resolved away.
            if vd.trail_pos <= seen.trail {
                return false;
            }
        }

        // Depth limiting to prevent infinite recursion
        if depth > self.min.minimize_depth_limit {
            return false;
        }

        // Mark as visited for this minimization call (prevents infinite loops).
        // `mf` is still current: no flag writes to this variable can have
        // happened since it was loaded above (no recursion in between).
        if mf & MIN_VISITED == 0 {
            self.min.minimize_flags[var_idx] |= MIN_VISITED;
            self.min.minimize_to_clear.push(var_idx);
        }

        // CaDiCaL minimize.cpp:36: charge search tick per reason access.
        self.search_ticks[usize::from(self.stable_mode)] += 1;

        if is_binary_literal_reason(reason) {
            // Binary literal reason (#8034): single antecedent literal,
            // no arena clause to recurse into.
            let reason_lit = Literal(binary_reason_lit(reason));
            if !self.is_redundant_cached(reason_lit, depth + 1) {
                self.min.minimize_flags[var_idx] |= MIN_POISON;
                return false;
            }
            self.min.minimize_flags[var_idx] |= MIN_REMOVABLE;
            return true;
        }

        // Arena clause reason. Clause data must be intact: clauses marked
        // garbage via mark_garbage_keep_data (eager subsumption) retain
        // their literals.
        let clause_idx = reason as usize;
        debug_assert!(
            !self.arena.is_empty_clause(clause_idx),
            "BUG: reason clause {reason} for var {var_idx} is deleted during minimize",
        );

        // Check all literals in the reason clause (iterate by index to avoid allocation)
        let clause_len = self.arena.len_of(clause_idx);
        for i in 0..clause_len {
            let reason_lit = self.arena.literal(clause_idx, i);
            let reason_var_idx = reason_lit.variable().index();

            // Skip the literal itself
            if reason_var_idx == var_idx {
                continue;
            }

            // Recursively check if this literal is redundant
            if !self.is_redundant_cached(reason_lit, depth + 1) {
                // Found a non-redundant literal - mark as poison
                self.min.minimize_flags[var_idx] |= MIN_POISON;
                return false;
            }
        }

        // All reason literals are redundant - mark as removable
        self.min.minimize_flags[var_idx] |= MIN_REMOVABLE;
        true
    }
}
