// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DIP-ERCL integration with conflict analysis (#8440).
//!
//! After 1UIP analysis produces a learned clause, this module attempts to find
//! a Dual Implication Point and split the clause into two shorter clauses using
//! an extension variable. The integration is called from the analyze_and_backtrack
//! skeleton in solve/analyze.rs.

use super::*;
use crate::solver::dip::DipErclResult;

impl Solver {
    /// Attempt DIP-ERCL on a learned clause after 1UIP analysis.
    ///
    /// If successful, returns the ERCL result containing pre/post-DIP clauses
    /// and definition clauses. The caller is responsible for:
    /// 1. Allocating the extension variable via `new_var_internal()`
    /// 2. Adding the definition clauses to the clause DB
    /// 3. Adding the pre-DIP and post-DIP clauses as learned clauses
    /// 4. Backtracking appropriately
    ///
    /// Returns `None` if DIP-ERCL is disabled or no valid DIP is found.
    pub(super) fn try_dip_ercl(&mut self, learned_clause: &[Literal]) -> Option<DipErclResult> {
        if !self.dip.enabled {
            return None;
        }

        // DIP-ERCL requires the learned clause to have enough literals.
        if learned_clause.len() < 4 {
            return None;
        }

        let next_var = self.num_vars as u32;
        let result = self.dip.try_dip_ercl(
            learned_clause,
            &self.trail,
            &self.var_data,
            self.decision_level,
            next_var,
        );

        // Update solver stats from DIP manager stats.
        if let Some(ref ercl) = result {
            self.stats.dip_found += 1;
            if ercl.ext_var.0 == next_var {
                // New extension variable was created.
                self.stats.dip_extensions_created += 1;
            } else {
                self.stats.dip_reuses += 1;
            }
        }
        self.stats.dip_attempts = self.dip.stats.dip_attempts;
        self.stats.dip_skipped = self.dip.stats.dip_skipped;

        result
    }

    /// Apply a DIP-ERCL result: allocate extension variable, add definition
    /// clauses, and return the two learned clauses.
    ///
    /// Called from the analyze_and_backtrack skeleton when DIP-ERCL succeeds.
    ///
    /// Returns `(pre_dip_clause_ref, post_dip_clause_ref, ext_var)`.
    pub(super) fn apply_dip_ercl(
        &mut self,
        ercl: DipErclResult,
    ) -> (ClauseRef, ClauseRef, Variable) {
        let ext_var = ercl.ext_var;

        // Allocate the extension variable if it's new (index == num_vars).
        if ext_var.index() >= self.num_vars {
            let allocated = self.new_var_internal();
            debug_assert_eq!(
                allocated, ext_var,
                "BUG: DIP-ERCL extension variable mismatch: expected {ext_var:?}, got {allocated:?}",
            );
            // Freeze the extension variable to protect it from BVE elimination.
            self.cold.freeze_counts[ext_var.index()] = 1;
        }

        // Add the three Tseitin definition clauses as irredundant (original).
        // These are structural definitions that must never be deleted.
        // CRITICAL (#8485): use add_clause_watched which handles watch attachment,
        // unit propagation, and conflict detection. Previously, add_clause_db was
        // called without watch attachment, leaving irredundant clauses invisible
        // to BCP, causing watch invariant violations and false SAT results.
        for def_clause in &ercl.definition_clauses {
            let mut lits = def_clause.clone();
            self.add_clause_watched(&mut lits);
        }

        // Add the pre-DIP clause as a learned clause.
        let pre_lbd = ercl.pre_dip_clause.len().min(255) as u32;
        let pre_ref = {
            let mut lits = ercl.pre_dip_clause;
            self.add_learned_clause_inner(&mut lits, pre_lbd, &[])
        };

        // Add the post-DIP clause as a learned clause.
        let post_lbd = ercl.post_dip_clause.len().min(255) as u32;
        let post_ref = {
            let mut lits = ercl.post_dip_clause;
            self.add_learned_clause_inner(&mut lits, post_lbd, &[])
        };

        (pre_ref, post_ref, ext_var)
    }

    /// Run DIP extension variable garbage collection if due.
    ///
    /// Called periodically from the conflict loop. Removes low-activity
    /// extension variables and their definition clauses.
    pub(super) fn dip_gc_if_needed(&mut self) {
        if !self.dip.enabled {
            return;
        }

        if !self.dip.tick_conflict() {
            return;
        }

        let deleted = self.dip.gc_extension_vars();
        if deleted.is_empty() {
            return;
        }

        self.stats.dip_gc_deleted += deleted.len() as u64;

        // For each deleted extension variable, we could search for and remove
        // clauses containing it. For now, let reduce_db handle cleanup of
        // learned clauses containing deleted extension variables (they will
        // have low activity and be naturally purged).
        //
        // The definition clauses (irredundant) will remain but are harmless:
        // the extension variable will never be assigned (it's unreferenced),
        // so the definition clauses are dead code.
    }
}
