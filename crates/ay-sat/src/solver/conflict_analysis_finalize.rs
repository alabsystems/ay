// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ordinary finalization with admission around the same selected operations.

use super::*;

pub(in crate::solver) mod admitted;
mod finish;
mod minimize;

impl Solver {
    #[cfg(test)]
    pub(super) fn finalize_conflict_analysis(
        &mut self,
        uip: Literal,
        lrat_level0_vars: Vec<usize>,
    ) -> ConflictResult {
        match self.finalize_conflict_analysis_admitted(uip, lrat_level0_vars, &admitted::Ordinary) {
            Ok(result) => result,
            Err(never) => match never {},
        }
    }

    /// Must remain inside the original owner's exclusive analysis guard.
    /// A returned value is private continuation state, not a solver verdict.
    pub(in crate::solver) fn finalize_conflict_analysis_admitted<P: admitted::Policy>(
        &mut self,
        uip: Literal,
        lrat_level0_vars: Vec<usize>,
        p: &P,
    ) -> Result<ConflictResult, P::Error> {
        p.enter_finalize(self, &lrat_level0_vars)?;
        p.work(16)?;
        self.conflict.set_asserting_literal(uip);
        self.update_bumpreason_decision_rate();
        let lbd = (self.min.level_seen_to_clear.len() as u32).saturating_sub(1);
        let size = self.conflict.learned_count() + 1;
        debug_assert!((lbd as usize) < size || size <= 1);
        let chain_len = if self.cold.lrat_enabled {
            self.conflict.resolution_chain_len()
        } else {
            0
        };
        let removed = self.finalize_minimize_admitted(size, p)?;
        p.work(self.min.level_seen_to_clear.len())?;
        self.clear_level_seen();
        self.bump_reason_literals_admitted(p)?;
        self.bump_analyzed_variables_admitted(p)?;
        // Actual trace LRAT bookkeeping remains selected. Root-unit and
        // removed-literal augmentation require their separate admitted graph.
        self.finalize_lrat_phase(uip, lrat_level0_vars, removed, chain_len, p)?;
        self.finalize_result_admitted(uip, lbd, p)
    }

    pub(super) fn should_snapshot_lrat_original_learned(
        &self,
        pre_min_clause_size: usize,
        shrink_has_repeated_non_uip_level: bool,
    ) -> bool {
        self.cold.lrat_enabled
            && pre_min_clause_size > 2
            && (!self.shrink_enabled || shrink_has_repeated_non_uip_level)
    }

    fn finalize_lrat_phase<P: admitted::Policy>(
        &mut self,
        uip: Literal,
        mut lrat_level0_vars: Vec<usize>,
        mut removed_learned_buf: Option<Vec<Literal>>,
        ibcl_core_chain_len: usize,
        p: &P,
    ) -> Result<(), P::Error> {
        p.work(8)?;
        // Forward LRAT chain computation: add reason chains for literals
        // removed during minimization and level-0 unit proof IDs.
        // CaDiCaL: calculate_minimize_chain() in minimize.cpp:155-199,
        // then unit_chain in analyze.cpp:1240-1246.
        if let Some(removed_learned) = removed_learned_buf.as_deref() {
            if !removed_learned.is_empty() {
                self.stats.lrat_original_learned_snapshot_copies += 1;
                self.stats.lrat_original_learned_snapshot_literals += removed_learned.len() as u64;
                let minimize_level0 = self.compute_lrat_chain_for_removed_literals(removed_learned);
                lrat_level0_vars.extend(minimize_level0);
            }
        }
        if let Some(mut removed_learned) = removed_learned_buf.take() {
            removed_learned.clear();
            self.min.lrat_original_learned_buf = removed_learned;
        }

        if self.cold.lrat_enabled && !lrat_level0_vars.is_empty() {
            p.root_phase(self, uip, &lrat_level0_vars)?;
        }
        // Return the LRAT level-0 vars buffer to cold state for reuse (#8603).
        lrat_level0_vars.clear();
        self.cold.lrat_level0_vars_buf = lrat_level0_vars;

        self.finalize_ibcl_admitted(ibcl_core_chain_len, p)
    }

    fn finalize_ibcl_admitted<P: admitted::Policy>(
        &mut self,
        ibcl_core_chain_len: usize,
        p: &P,
    ) -> Result<(), P::Error> {
        // IBCL pass (#8269): interpolation-based clause learning.
        //
        // When LRAT proof mode is active, we have the core resolution chain:
        // clause IDs plus per-step pivot literals for reason clauses. A full
        // IBCL implementation would compute a Craig interpolant from this
        // proof, potentially yielding a shorter auxiliary learned constraint.
        //
        // Current status: stats-only infrastructure. The full interpolation
        // engine requires:
        // 1. A resolution proof DAG (the core chain is now pivot-annotated,
        //    but still linear and excludes minimization/unit-chain LRAT hints)
        // 2. A partition of variables into A-local, B-local, and shared sets
        //    — the natural partition uses decision level: variables decided
        //    before vs after the conflict as the A/B split
        // 3. An interpolation algorithm (McMillan 2003, Pudlak 1997, or
        //    Huang 2010 for size-optimal interpolants)
        //
        // For now, we record when the IBCL pass would attempt interpolation,
        // when the resolution chain is too short to benefit, and when proof
        // skeleton metadata is still insufficient. This data informs whether
        // investing in the full proof DAG is worthwhile.
        if self.cold.lrat_enabled && !self.should_prune_conflict_analysis_experiments() {
            let chain_len = ibcl_core_chain_len;
            let clause_size = self.conflict.learned_count() + 1; // +1 for UIP
            if chain_len < 3 || clause_size <= 2 {
                // Resolution chains shorter than 3 steps produce interpolants
                // that are at best equal to the 1UIP clause. Unit or binary
                // learned clauses are already minimal.
                p.counter(self.stats.ibcl_skipped_short_chain, 1)?;
                self.stats.ibcl_skipped_short_chain += 1;
            } else if {
                p.work(chain_len)?;
                !self.conflict.resolution_chain_prefix_has_pivots(chain_len)
            } {
                // Future extraction must fail closed unless every direct 1UIP
                // reason step has both a non-zero clause ID and a pivot literal.
                p.counter(self.stats.ibcl_skipped_missing_pivots, 1)?;
                self.stats.ibcl_skipped_missing_pivots += 1;
            } else {
                p.counter(self.stats.ibcl_attempts, 1)?;
                self.stats.ibcl_attempts += 1;
                // Future: compute interpolant here and compare size.
                // if interpolant_clause.len() < clause_size {
                //     self.stats.ibcl_improvements += 1;
                //     // Replace learned clause with interpolant
                // }
            }
        }
        Ok(())
    }
}
