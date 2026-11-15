// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl Solver {
    pub(super) fn finalize_result_admitted<P: admitted::Policy>(
        &mut self,
        uip: Literal,
        lbd: u32,
        p: &P,
    ) -> Result<ConflictResult, P::Error> {
        p.result(self)?;
        let (backtrack_level, swap_learned_idx) =
            self.conflict.backtrack_level_and_watch_swap(&self.var_data);
        debug_assert_eq!(
            backtrack_level,
            self.conflict.compute_backtrack_level(&self.var_data)
        );
        let mut result = self.conflict.get_result(backtrack_level, lbd);
        #[cfg(debug_assertions)]
        let reference = {
            let mut reference = p.debug_copy(&result.learned_clause)?;
            crate::conflict::reorder_for_watches(&mut reference, &self.var_data, backtrack_level);
            reference
        };
        if swap_learned_idx != usize::MAX {
            result.learned_clause.swap(1, swap_learned_idx + 1);
        }
        #[cfg(debug_assertions)]
        debug_assert_eq!(result.learned_clause, reference);
        if self.cold.learned_order_kissat && result.learned_clause.len() > 3 {
            p.learned_order(&mut result.learned_clause[1..], &self.var_data)?;
        }
        p.diagnostics(result.learned_clause.len())?;
        self.debug_assert_learned_clause_invariants(uip, backtrack_level, &result.learned_clause);
        // Counted entry refused an active writer before mutation. This keeps
        // inactive-cache initialization and ordinary actual proof collection.
        self.veripb_collect_hints(&result.learned_clause);
        p.work(1)?;
        Ok(result)
    }
}
