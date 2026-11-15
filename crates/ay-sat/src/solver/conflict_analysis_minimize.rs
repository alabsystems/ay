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

pub(super) mod admitted;

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
        removed_lits: Option<&mut Vec<Literal>>,
    ) {
        match self.minimize_clause_admitted(removed_lits, &admitted::Ordinary) {
            Ok(()) => (),
            Err(never) => match never {},
        }
    }

    /// The ordinary cached CaDiCaL recursion and its exact flag/abort ordering.
    /// Shared with the original-owner counted continuation, not reimplemented.
    pub(super) fn is_redundant_cached(&mut self, lit: Literal, depth: u32) -> bool {
        match self.redundant_admitted(lit, depth, &admitted::Ordinary) {
            Ok(redundant) => redundant,
            Err(never) => match never {},
        }
    }
}
