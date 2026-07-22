// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Learned state management for LIA solver.
//!
//! Handles take/import of HNF cuts and Diophantine solver state
//! for preservation across theory instance recreations.

use super::*;

impl LiaSolver<'_> {
    /// Get the learned cuts and seen cut keys for external storage.
    ///
    /// Use this to preserve cuts across theory instances when the theory
    /// must be dropped temporarily (e.g., to allow mutable term store access).
    /// Returns (learned_cuts, seen_hnf_cut_keys).
    pub fn take_learned_state(&mut self) -> (Vec<StoredCut>, HashSet<HnfCutKey>) {
        let debug = self.debug_hnf;
        if debug {
            safe_eprintln!(
                "[HNF] Taking {} learned cuts, {} seen keys",
                self.learned_cuts.len(),
                self.seen_hnf_cuts.len()
            );
        }
        // #C7: take/import happen at scope depth 0, where the per-scope trail is
        // empty (only open scopes trail keys). Clear it so the trail stays
        // consistent with the (now emptied) set.
        self.seen_hnf_cuts_trail.clear();
        (
            std::mem::take(&mut self.learned_cuts),
            std::mem::take(&mut self.seen_hnf_cuts),
        )
    }

    /// Import previously learned cuts and seen cut keys.
    ///
    /// Use this to restore state from a previous theory instance.
    pub fn import_learned_state(&mut self, cuts: Vec<StoredCut>, seen: HashSet<HnfCutKey>) {
        let debug = self.debug_hnf;
        if debug {
            safe_eprintln!(
                "[HNF] Importing {} learned cuts, {} seen keys",
                cuts.len(),
                seen.len()
            );
        }
        self.learned_cuts = cuts;
        self.seen_hnf_cuts = seen;
        // #C7: imported keys are base (no open scope); start with an empty trail.
        self.seen_hnf_cuts_trail.clear();
    }

    /// Replay learned cuts into the LRA solver.
    ///
    /// Call this after asserting new literals to restore previously learned cuts.
    /// Cuts that reference unknown variables are skipped.
    pub fn replay_learned_cuts(&mut self) {
        // Cut replay can tighten single-var bounds — conservatively rescan
        // every integer var on the next bounds-conflict check (#C4).
        self.mark_int_bounds_all_dirty();
        let debug = self.debug_hnf;
        if debug && !self.learned_cuts.is_empty() {
            safe_eprintln!(
                "[HNF] Attempting to replay {} learned cuts, integer_vars={}, lra_vars={}",
                self.learned_cuts.len(),
                self.integer_vars.len(),
                self.lra.term_to_var().len()
            );
        }
        let mut replayed = 0;
        let mut skipped_no_var = 0;
        let mut skipped_no_int = 0;

        for cut in &self.learned_cuts {
            // Convert TermIds to LRA variable IDs
            let mut lra_coeffs: Vec<(u32, BigRational)> = Vec::new();
            let mut all_valid = true;

            for (term_id, coeff) in &cut.coeffs {
                if let Some(&lra_var) = self.lra.term_to_var().get(term_id) {
                    lra_coeffs.push((lra_var, coeff.clone()));
                } else {
                    // Variable not in current LRA state - skip this cut
                    all_valid = false;
                    skipped_no_var += 1;
                    break;
                }
            }

            if all_valid && !lra_coeffs.is_empty() {
                // Re-add the cut as a bound.
                // Use stored reasons from original HNF derivation for proper
                // conflict explanation (#5388).
                let gomory_cut = ay_lra::GomoryCut {
                    coeffs: lra_coeffs,
                    bound: cut.bound.clone(),
                    is_lower: cut.is_lower,
                    reasons: cut.reasons.clone(),
                    source_term: None,
                };
                // Only replay if we have at least one integer variable
                if self.integer_vars.iter().min().is_some() {
                    self.lra.add_gomory_cut(&gomory_cut, TermId::SENTINEL);
                    replayed += 1;
                } else {
                    skipped_no_int += 1;
                }
            }
        }

        if debug {
            if replayed > 0 {
                safe_eprintln!("[HNF] Replayed {} learned cuts", replayed);
            }
            if skipped_no_var > 0 || skipped_no_int > 0 {
                safe_eprintln!(
                    "[HNF] Skipped cuts: {} no LRA var, {} no int var",
                    skipped_no_var,
                    skipped_no_int
                );
            }
        }
    }

    /// Get the Diophantine solver state for external storage.
    ///
    /// Use this to preserve Diophantine analysis across theory instances when the
    /// theory must be dropped temporarily (e.g., for mutable term store access).
    ///
    /// The Diophantine solver analyzes equality structure to:
    /// 1. Eliminate variables via substitution
    /// 2. Identify safe dependent variables (poor branching candidates)
    /// 3. Propagate bounds through substitutions
    ///
    /// Since the equality structure typically doesn't change during lazy DPLL(T)
    /// (only inequality bounds change), preserving this state avoids redundant
    /// Diophantine analysis.
    pub fn take_dioph_state(&mut self) -> DiophState {
        let debug = self.debug_dioph;
        if debug {
            safe_eprintln!(
                "[DIOPH] Taking state: {} equalities, {} safe vars, {} substitutions",
                self.dioph_equality_key.len(),
                self.dioph_safe_dependent_vars.len(),
                self.dioph_cached_substitutions.len()
            );
        }
        let (lra_propagated_equality_pairs, lra_propagated_disequality_pairs) =
            self.lra.take_model_equality_proposal_state();
        DiophState {
            equality_key: std::mem::take(&mut self.dioph_equality_key),
            needs_full_check: self.dioph_needs_full_check,
            safe_dependent_vars: std::mem::take(&mut self.dioph_safe_dependent_vars),
            cached_substitutions: std::mem::take(&mut self.dioph_cached_substitutions),
            cached_modular_gcds: std::mem::take(&mut self.dioph_cached_modular_gcds),
            cached_reasons: std::mem::take(&mut self.dioph_cached_reasons),
            propagated_equality_pairs: {
                // Wholesale replacement of the pair set can change membership
                // without changing length — the one stamp component that is a
                // len(). Drop the algebraic-detection memo instead of risking
                // a stale hit that would skip a now-unsuppressed Case-2 pair.
                self.detect_algebraic_cache = None;
                std::mem::take(&mut self.propagated_equality_pairs)
            },
            propagated_disequality_pairs: std::mem::take(&mut self.propagated_disequality_pairs),
            lra_propagated_equality_pairs,
            lra_propagated_disequality_pairs,
        }
    }

    /// Import previously computed Diophantine solver state.
    ///
    /// Use this to restore state from a previous theory instance.
    pub fn import_dioph_state(&mut self, state: DiophState) {
        let debug = self.debug_dioph;
        if debug {
            safe_eprintln!(
                "[DIOPH] Importing state: {} equalities, {} safe vars, {} substitutions",
                state.equality_key.len(),
                state.safe_dependent_vars.len(),
                state.cached_substitutions.len()
            );
        }
        self.dioph_equality_key = state.equality_key;
        self.dioph_needs_full_check = state.needs_full_check;
        self.dioph_safe_dependent_vars = state.safe_dependent_vars;
        self.dioph_cached_substitutions = state.cached_substitutions;
        self.dioph_cached_modular_gcds = state.cached_modular_gcds;
        self.dioph_cached_reasons = state.cached_reasons;
        // See take_dioph_state: same-length pair-set replacement hazard.
        self.detect_algebraic_cache = None;
        self.propagated_equality_pairs = state.propagated_equality_pairs;
        self.propagated_disequality_pairs = state.propagated_disequality_pairs;
        self.lra.import_model_equality_proposal_state(
            state.lra_propagated_equality_pairs,
            state.lra_propagated_disequality_pairs,
        );
    }
}
