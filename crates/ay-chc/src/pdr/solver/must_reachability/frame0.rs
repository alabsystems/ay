// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    pub(in crate::pdr::solver) fn block_unreachable_predicates_at_frame0(&mut self) {
        // Collect unreachable predicate IDs first to avoid borrowing `self`
        // immutably (via predicates()) while also borrowing mutably (via add_lemma_to_frame).
        let unreachable: Vec<PredicateId> = self
            .problem
            .predicates()
            .iter()
            .filter(|pred| !self.predicate_is_reachable(pred.id))
            .map(|pred| pred.id)
            .collect();
        for pred_id in unreachable {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Adding frame[0] blocking for pred {} (unreachable) - all states blocked at level 0",
                    pred_id.index()
                );
            }
            // Invariant = false => no states allowed
            self.add_lemma_to_frame(Lemma::new(pred_id, ChcExpr::Bool(false), 0), 0);
        }
    }
}
