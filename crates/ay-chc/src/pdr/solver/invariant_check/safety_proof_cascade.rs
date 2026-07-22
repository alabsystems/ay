// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model verification cascade for safety proofs.
//!
//! Tries multiple model-building strategies with budget-aware verification:
//! 1. Fast path (verify_model_fast, 800ms deadline)
//! 2. Filtered model
//! 3. Inductive-only model
//! 4. Entry-inductive model
//! 5. Iterative conjunct weakening

use super::*;

impl PdrSolver {
    /// Try multiple model-building and verification strategies with a total budget.
    ///
    /// Returns `Some(model)` if any strategy produces a verified model, `None` otherwise.
    /// Total cascade budget is 2 seconds; individual verify_model calls get 1.5s.
    ///
    /// TOTAL BUDGET (#3121): When running under a portfolio, the model verification
    /// cascade can consume multiple seconds per verify_model call × 5 strategies = 15+ sec.
    /// This starves the main PDR loop of time.
    pub(super) fn try_model_verification_cascade(
        &mut self,
        model: InvariantModel,
    ) -> Option<InvariantModel> {
        let cascade_start = ay_core::time::Instant::now();
        let cascade_budget = std::time::Duration::from_secs(2);
        let verify_budget = std::time::Duration::from_millis(1500);

        // Strategy 1: Fast path with tight deadline
        let fast_deadline = cascade_start + std::time::Duration::from_millis(800);
        if self.verify_model_fast(&model, fast_deadline) {
            if self.config.verbose {
                safe_eprintln!("PDR: check_invariants_prove_safety: model verified (fast path)");
            }
            return Some(model);
        }

        if cascade_start.elapsed() >= cascade_budget {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: check_invariants_prove_safety: cascade budget exhausted ({:?}), skipping remaining models",
                    cascade_start.elapsed()
                );
            }
            return None;
        }

        // Strategy 2: Filtered model
        let filtered = self.build_model_from_frame_filtered(1);
        if self.verify_model_with_budget(&filtered, verify_budget) {
            if self.config.verbose {
                safe_eprintln!("PDR: check_invariants_prove_safety: filtered model verified");
            }
            return Some(filtered);
        }

        if cascade_start.elapsed() >= cascade_budget {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: check_invariants_prove_safety: cascade budget exhausted ({:?}), skipping remaining models",
                    cascade_start.elapsed()
                );
            }
            return None;
        }

        // Strategy 3: Inductive-only model
        let inductive_model = self.build_model_from_inductive_lemmas(1);
        if self.verify_model_with_budget(&inductive_model, verify_budget) {
            if self.config.verbose {
                safe_eprintln!("PDR: check_invariants_prove_safety: inductive-only model verified");
            }
            return Some(inductive_model);
        }

        if cascade_start.elapsed() >= cascade_budget {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: check_invariants_prove_safety: cascade budget exhausted ({:?}), skipping remaining models",
                    cascade_start.elapsed()
                );
            }
            return None;
        }

        // Strategy 4: Entry-inductive model
        let entry_inductive_model = self.build_model_from_entry_inductive_lemmas(1);
        if self.verify_model_with_budget(&entry_inductive_model, verify_budget) {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: check_invariants_prove_safety: entry-inductive model verified"
                );
            }
            return Some(entry_inductive_model);
        }

        if cascade_start.elapsed() >= cascade_budget {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: check_invariants_prove_safety: cascade budget exhausted ({:?}), skipping remaining models",
                    cascade_start.elapsed()
                );
            }
            return None;
        }

        // Strategy 5: Iterative conjunct weakening
        if let Some(weakened_model) = self.build_model_with_iterative_weakening(&inductive_model) {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: check_invariants_prove_safety: iteratively weakened model verified"
                );
            }
            return Some(weakened_model);
        }

        if self.config.verbose {
            safe_eprintln!(
                "PDR: check_invariants_prove_safety: model verification failed, cannot prove safety"
            );
        }
        None
    }
}
