// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    pub(in crate::pdr::solver) fn block_unreachable_obligation(
        &mut self,
        pob: &mut ProofObligation,
        transition_constraints: Vec<ChcExpr>,
        clause_interpolation_data: Vec<ClauseInterpolationData>,
    ) -> BlockResult {
        let interp_result =
            self.run_interpolation_cascade(pob, transition_constraints, clause_interpolation_data);
        let generalized = self.refine_blocking_lemma(
            interp_result.formula,
            pob,
            interp_result.has_bool_normalization,
            &interp_result.all_bool_vars,
            interp_result.kind,
        );

        // Cancellation check before inductiveness SMT queries
        if self.is_cancelled() {
            return BlockResult::Unknown;
        }

        // BUG FIX #685 + #710: Verify the blocking formula is self-inductive at ALL levels.
        // The issue: is_inductive_blocking only checks that init/frame[level-1] + T => L',
        // but doesn't check that L + T => L' (self-inductiveness).
        // Without this, we can learn lemmas that block reachable states.
        //
        // #685: If self-inductiveness fails on a SAFETY PATH (no parent), the lemma may block
        //       reachable states, causing false Safe results → UNSOUND.
        // #710: If self-inductiveness fails on a COUNTEREXAMPLE PATH (has parent), we're tracing
        //       a concrete counterexample. We should learn the lemma anyway because:
        //       - We're not trying to prove Safe, we're looking for Unsafe
        //       - Learning a non-self-inductive lemma may cause incompleteness but not unsoundness
        //       - Returning Unknown causes infinite loops on unsafe examples (timeout)
        let (blocking_formula, is_on_counterexample_path) =
            match self.verify_inductiveness_or_fallback(generalized, pob) {
                Ok(result) => result,
                Err(result) => return result,
            };

        // Add blocking formula to cluster store for global generalization.
        // This enables Spacer-style global guidance over similar blocking cubes.
        //
        // Safety-path only: counterexample-tracing lemmas may be non-self-inductive and should
        // not guide global generalization (including via cluster membership).
        let final_blocking_formula =
            self.try_global_generalization(&blocking_formula, pob, is_on_counterexample_path);

        // #6047: Array-sorted canonical variables are now allowed in blocking
        // formulas via select(arr, idx) constraints from array cube support.
        // Non-canonical array variables from clause-local MBP are already handled
        // by the lemma filter in add_lemma_to_frame_impl.

        let mut lemma = Lemma::new(
            pob.predicate,
            ChcExpr::not(final_blocking_formula),
            pob.level,
        );

        // Tag lemma with the TLA+ action that generated the CTI this lemma blocks (#8215).
        // The action comes from the transition clause that produced the proof obligation.
        if let Some(clause_idx) = pob.incoming_clause {
            if let Some(action) = self.problem.clause_action(clause_idx) {
                lemma = lemma.with_action(action);
            }
        }

        BlockResult::Blocked(lemma)
    }

    pub(in crate::pdr::solver) fn is_safety_path_point_blocking_acceptable(
        &mut self,
        point_blocking: &ChcExpr,
        predicate: PredicateId,
        level: usize,
    ) -> bool {
        self.is_self_inductive_blocking(point_blocking, predicate)
            || self.is_inductive_blocking(point_blocking, predicate, level)
    }

    #[allow(clippy::result_large_err)]
    fn verify_inductiveness_or_fallback(
        &mut self,
        generalized: ChcExpr,
        pob: &mut ProofObligation,
    ) -> Result<(ChcExpr, bool), BlockResult> {
        let is_on_counterexample_path = pob.parent.is_some();
        let blocking_formula = if is_on_counterexample_path {
            // #710: For counterexample tracing, self-inductiveness is not required for soundness
            // (model verification guards Safe results). Avoid the extra SMT work here.
            generalized
        } else if self.is_self_inductive_blocking(&generalized, pob.predicate) {
            generalized
        } else if self.is_inductive_blocking(&generalized, pob.predicate, pob.level) {
            // The generalized blocking formula is valid for this frame level (i.e., it blocks
            // all states reachable from frame[level-1]), even if it is not self-inductive.
            //
            // Self-inductiveness is a useful filter, but requiring it can cause premature
            // Unknown on simple safe problems where the lemma is only *relatively* inductive
            // (PDR/IC3 standard). Safe results are guarded by model verification.
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Generalized formula {} not self-inductive at level {}, but is inductive; accepting",
                    generalized,
                    pob.level
                );
            }
            generalized
        } else if self.is_inductive_blocking(&pob.state, pob.predicate, pob.level) {
            // If generalization overshot (dropped a needed conjunct), fall back to the original
            // blocking formula instead of point-blocking. Point-blocking requires a concrete
            // cube; root POBs are often not point cubes, so this fallback would otherwise
            // return Unknown even when the original blocking formula is a valid inductive lemma.
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Generalized formula {} not inductive at level {}, using original blocking formula {}",
                    generalized,
                    pob.level,
                    pob.state
                );
            }
            pob.state.clone()
        } else {
            // On safety path, fall back to point blocking.
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Generalized formula {} not self-inductive at level {}, falling back to point blocking",
                    generalized,
                    pob.level
                );
            }

            match self.extract_point_blocking(pob) {
                Some(point) => {
                    // On safety path, point blocking should be self-inductive when possible.
                    // However, self-inductiveness is stronger than needed: a point cube may not
                    // be closed under *all* self-transitions (e.g. due to unreachable predecessors),
                    // yet still be inductive relative to the current frame.
                    //
                    // Only return Unknown if the point cube is neither self-inductive nor
                    // inductive relative to frame[level-1] (#831).
                    if self.is_safety_path_point_blocking_acceptable(
                        &point,
                        pob.predicate,
                        pob.level,
                    ) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Point blocking {} accepted (self-inductive or inductive at level {})",
                                point, pob.level
                            );
                        }
                        point
                    } else if let Some(refined) = self.try_refine_with_array_indices(pob) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Array lazy-Skolem refinement strengthened point blocking {} -> {}",
                                point,
                                refined
                            );
                        }
                        refined
                    } else {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Point blocking {} not self-inductive and not inductive at level {}, returning Unknown",
                                point, pob.level
                            );
                        }
                        return Err(BlockResult::Unknown);
                    }
                }
                None => {
                    if let Some(refined) = self.try_refine_with_array_indices(pob) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Array lazy-Skolem refinement recovered blocking cube {}",
                                refined
                            );
                        }
                        refined
                    } else {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Couldn't extract point blocking, returning Unknown"
                            );
                        }
                        return Err(BlockResult::Unknown);
                    }
                }
            }
        };

        Ok((blocking_formula, is_on_counterexample_path))
    }
}
