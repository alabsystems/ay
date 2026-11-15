// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact CaDiCaL minimize.cpp cached recursion, not a replay cost model.
//! Keep/removable precede poison; visited short-circuits only recursively.

use super::*;

impl Solver {
    pub(in crate::solver) fn redundant_admitted<P: Policy>(
        &mut self,
        lit: Literal,
        depth: u32,
        p: &P,
    ) -> Result<bool, P::Error> {
        // Admission precedes the actual recursive frame and its data loads.
        p.frame(self, lit, depth)?;
        self.redundancy_frame(lit, depth, p)
    }

    fn redundancy_frame<P: Policy>(
        &mut self,
        lit: Literal,
        depth: u32,
        p: &P,
    ) -> Result<bool, P::Error> {
        let var = lit.variable().index();
        // Ordinary conservative handling of unassigned/chrono ghost literals.
        if !self.var_is_assigned(var) {
            return Ok(false);
        }
        let vd = self.var_data[var];
        if vd.level == 0 {
            return Ok(true);
        }
        let flags = self.min.minimize_flags[var];
        if flags & (MIN_REMOVABLE | MIN_KEEP) != 0 {
            return Ok(true);
        }
        if flags & MIN_POISON != 0 {
            return Ok(false);
        }
        if vd.level == self.decision_level {
            return Ok(false);
        }
        if depth > 0 && flags & MIN_VISITED != 0 {
            return Ok(true);
        }
        let reason = vd.reason;
        if reason == NO_REASON || vd.is_lazy_theory_reason() {
            return Ok(false);
        }
        if self.minimize_early_abort(vd, depth) {
            return Ok(false);
        }
        if depth > self.min.minimize_depth_limit {
            return Ok(false);
        }
        if flags & MIN_VISITED == 0 {
            p.mark(self)?;
            self.min.minimize_flags[var] |= MIN_VISITED;
            self.min.minimize_to_clear.push(var);
        }
        if !self.cold.analysis_ticks_kissat {
            self.minimize_tick_admitted(p)?;
        }
        let redundant = self.minimize_reason_admitted(lit, depth, reason, p)?;
        self.min.minimize_flags[var] |= if redundant { MIN_REMOVABLE } else { MIN_POISON };
        Ok(redundant)
    }

    fn minimize_early_abort(&self, vd: VarData, depth: u32) -> bool {
        let level = vd.level as usize;
        let seen = if !self.min.level_seen_to_clear.is_empty() && level < self.min.level_seen.len()
        {
            self.min.level_seen[level]
        } else if !self.min.minimize_levels_to_clear.is_empty()
            && level < self.min.minimize_level_seen.len()
        {
            self.min.minimize_level_seen[level]
        } else {
            return false;
        };
        (depth == 0 && seen.count < 2) || vd.trail_pos <= seen.trail
    }

    fn minimize_tick_admitted<P: Policy>(&mut self, p: &P) -> Result<(), P::Error> {
        let mode = usize::from(self.stable_mode);
        p.counter(self.search_ticks[mode], 1)?;
        self.search_ticks[mode] += 1;
        Ok(())
    }

    fn minimize_reason_admitted<P: Policy>(
        &mut self,
        lit: Literal,
        depth: u32,
        reason: u32,
        p: &P,
    ) -> Result<bool, P::Error> {
        if is_binary_literal_reason(reason) {
            let antecedent = Literal(binary_reason_lit(reason));
            p.antecedent(self, antecedent, lit)?;
            return self.redundant_admitted(antecedent, depth + 1, p);
        }
        let offset = reason as usize;
        let var = lit.variable().index();
        p.clause(self, lit, offset)?;
        debug_assert!(
            !self.arena.is_empty_clause(offset),
            "BUG: reason clause {reason} for var {var} is deleted during minimize"
        );
        let len = self.arena.len_of(offset);
        if self.cold.analysis_ticks_kissat && len > 2 {
            self.minimize_tick_admitted(p)?;
        }
        for index in 0..len {
            p.work(1)?;
            let antecedent = self.arena.literal(offset, index);
            if antecedent.variable().index() == var {
                continue;
            }
            p.antecedent(self, antecedent, lit)?;
            if !self.redundant_admitted(antecedent, depth + 1, p)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
}
