// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded scalar minimization passes.

use super::*;

impl Executor {
    pub(super) fn minimize_scalar_model_values(
        &mut self,
        should_stop: &mut impl FnMut(&Self) -> bool,
    ) -> Option<(Option<Model>, bool, bool)> {
        let mut pre_minimization: Option<Model> = None;
        let mut scalar_changed = false;
        let mut stopped = false;
        'passes: for _pass in 0..MAX_MINIMIZATION_PASSES {
            if should_stop(self) {
                stopped = true;
                break;
            }
            // Phase 1: candidate lists, plus the BV dependency index they share
            // (one walk per pass, not one per candidate leaf).
            let (mut attempts, dependents) = self.collect_min_attempts_and_dependents()?;
            if attempts.is_empty() {
                break;
            }
            if pre_minimization.is_none() {
                pre_minimization = self.last_model.clone();
            }

            // Sort by descending magnitude — try the largest values first
            // since they have the most room to shrink.
            attempts.sort_by_key(|a| std::cmp::Reverse(a.magnitude()));

            // Phase 2: For each variable, try candidates via mutate-check-revert.
            let mut any_changed = false;
            for attempt in attempts {
                // Live poll between variables — a single variable's candidate
                // sweep is bounded by the same check inside try_*_candidates.
                if should_stop(self) {
                    stopped = true;
                    break 'passes;
                }
                let changed = match attempt {
                    MinAttempt::Lia(term_id, candidates) => {
                        self.try_lia_candidates(term_id, candidates)
                    }
                    MinAttempt::Lra(term_id, candidates) => {
                        self.try_lra_candidates(term_id, candidates)
                    }
                    MinAttempt::Bv(term_id, candidates) => {
                        self.try_bv_candidates(term_id, candidates, &dependents)
                    }
                };
                any_changed |= changed;
                scalar_changed |= changed;
            }

            // If nothing changed this pass, no point in another pass.
            if !any_changed {
                break;
            }
        }
        // A candidate check can itself consume the remaining budget. Poll once
        // more after the last mutation so even the final attempt of the final
        // pass cannot retain an un-gated cosmetic replacement past the stop.
        if scalar_changed && !stopped && should_stop(self) {
            stopped = true;
        }
        Some((pre_minimization, scalar_changed, stopped))
    }
}
