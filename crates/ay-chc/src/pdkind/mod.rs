// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PDKIND (Property-Directed K-Induction) engine for CHC
//!
//! PDKIND is an algorithm that combines k-induction with PDR-style frame strengthening.
//! It's particularly effective for linear CHC systems where standard k-induction fails.
//!
//! # Algorithm Overview
//!
//! PDKIND maintains an **induction frame** - a set of (lemma, counterexample) pairs.
//! The algorithm iteratively tries to prove the property is k-inductive by:
//! 1. Checking if the frame is k-inductive
//! 2. If not, strengthening the frame using interpolation
//! 3. Checking reachability of counterexamples
//!
//! # References
//!
//! - [Golem](https://github.com/usi-verification-and-security/golem)
//! - PDKIND paper: Kahsai et al. "Property-Directed K-Induction" (FMCAD 2017)

mod explanation;
mod push;
mod reachability;
mod types;

#[cfg(test)]
mod tests;

pub use types::IncrementalMode;
pub use types::PdkindConfig;
pub use types::PdkindResult;
pub(crate) use types::RawPdkindResult;
use types::*;

use crate::cancellation::CancellationToken;
use crate::engine_config::ChcEngineConfig;
use crate::engine_result::{build_single_pred_model, skeleton_counterexample, ChcEngineResult};
use crate::interpolant_validation::validate_inductive_invariant;
use crate::single_loop::SingleLoopTransformation;
use crate::smt::SmtResult;
use crate::transition_system::TransitionSystem;
use crate::{ChcExpr, ChcProblem, PredicateId};
use reachability::ReachabilityChecker;

/// PDKIND solver
pub struct PdkindSolver {
    problem: ChcProblem,
    config: PdkindConfig,
}

impl Drop for PdkindSolver {
    fn drop(&mut self) {
        std::mem::take(&mut self.problem).iterative_drop();
    }
}

impl PdkindSolver {
    /// Create a new PDKIND solver with the given config.
    pub(crate) fn new(problem: ChcProblem, config: PdkindConfig) -> Self {
        Self { problem, config }
    }

    /// Create a new PDKIND solver with default configuration.
    pub(crate) fn with_defaults(problem: ChcProblem) -> Self {
        Self::new(problem, PdkindConfig::default())
    }

    /// Create a new PDKIND solver with a cancellation token.
    pub(crate) fn with_cancellation(problem: ChcProblem, token: CancellationToken) -> Self {
        Self::new(
            problem,
            PdkindConfig {
                base: ChcEngineConfig {
                    verbose: false,
                    cancellation_token: Some(token),
                },
                ..PdkindConfig::default()
            },
        )
    }

    /// Build the transition system, applying SingleLoop fallback for
    /// multi-predicate linear CHC and preserving adaptive mode flags.
    fn extract_transition_system_with_singleloop_fallback(
        &self,
    ) -> Option<(TransitionSystem, IncrementalMode, u64, bool)> {
        // Preserve the caller's incremental mode configuration. SingleLoop
        // encoding no longer unconditionally forces FreshOnly (#8161) --
        // LIA problems benefit from incremental solving. Only BV problems
        // (set via config) and runtime degradation skip incremental.
        let incremental_mode = self.config.incremental_mode.clone();
        let mut obligation_timeout_secs = self.config.per_obligation_timeout_secs;
        let mut singleloop_encoded = false;

        let ts = match TransitionSystem::from_chc_problem(&self.problem) {
            Ok(ts) => ts,
            Err(_) => {
                // Fallback: multi-predicate linear problems via SingleLoop encoding
                // (Horn2VMT transformation, same as Golem PDKind uses).
                // SingleLoop creates Int location variables (.loc_N = 0/1) that pass
                // the interpolation sort guard. The TS is constructed and solved
                // directly by PDKIND.
                let mut tx = SingleLoopTransformation::new(self.problem.clone());
                match tx.transform() {
                    Some(sys) => {
                        if self.config.base.verbose {
                            safe_eprintln!(
                                "PDKIND: Using SingleLoop encoding ({} state vars)",
                                sys.state_vars.len()
                            );
                        }
                        // #8161: SingleLoop LIA problems now use incremental solving.
                        // Previously, all SingleLoop problems unconditionally forced
                        // skip_incremental=true (#2761). The real issue was BV state
                        // corruption and per-obligation timeouts, not SingleLoop per se.
                        // The adaptive fallback (#2675) handles false-UNSAT detection
                        // at the stable-frame level, degrading to non-incremental only
                        // when needed. BV problems are already handled by the caller
                        // setting FreshOnly in the config.
                        singleloop_encoded = true;
                        //
                        // Auto-bump timeout for SingleLoop encoding if still at
                        // default (5s). The portfolio path sets 60s explicitly via
                        // run_pdkind_with_singleloop(); this ensures direct callers
                        // get the same treatment (#2765).
                        if obligation_timeout_secs
                            == PdkindConfig::DEFAULT_PER_OBLIGATION_TIMEOUT_SECS
                        {
                            obligation_timeout_secs =
                                PdkindConfig::SINGLE_LOOP_PER_OBLIGATION_TIMEOUT_SECS;
                        }
                        TransitionSystem::new(
                            self.problem
                                .predicates()
                                .first()
                                .map_or(PredicateId::new(0), |p| p.id),
                            sys.state_vars,
                            sys.init,
                            sys.transition,
                            sys.query,
                        )
                    }
                    None => {
                        if self.config.base.verbose {
                            safe_eprintln!("PDKIND: Problem is not a linear transition system");
                        }
                        return None;
                    }
                }
            }
        };

        Some((
            ts,
            incremental_mode,
            obligation_timeout_secs,
            singleloop_encoded,
        ))
    }

    /// Solve the CHC problem using PDKIND.
    ///
    /// Returns a unified `ChcEngineResult` like all other CHC engines.
    pub fn solve(&self) -> ChcEngineResult {
        let raw = self.solve_raw();
        self.convert_raw_result(raw)
    }

    /// Solve returning the internal result type.
    ///
    /// Used by `portfolio::run_pdkind_with_singleloop` which needs the raw
    /// `PdkindInvariant` formula for SingleLoop back-translation before
    /// converting to `InvariantModel`.
    pub(crate) fn solve_raw(&self) -> RawPdkindResult {
        if self.config.base.is_cancelled() {
            if self.config.base.verbose {
                safe_eprintln!("PDKIND: Cancelled before initialization");
            }
            return RawPdkindResult::Unknown;
        }

        // Array soundness guard (#8675): PDKIND's k-induction checks and
        // interpolation-based strengthening rely on SMT completeness for
        // array formulas. The SMT solver can produce false-UNSAT on complex
        // array select/store constraints, making induction trivially pass
        // and producing false-SAFE. Same root cause as KIND array false-SAFE
        // and PDR array false-SAFE in #8675.
        if self.problem.has_array_sorts() {
            if self.config.base.verbose {
                safe_eprintln!("PDKIND: Skipping for array problem (soundness guard #8675)");
            }
            return RawPdkindResult::Unknown;
        }

        // Extract transition system (single-predicate direct, or multi-predicate via
        // SingleLoop) plus mode controls derived from the chosen encoding path.
        let Some((ts, mut incremental_mode, obligation_timeout_secs, singleloop_encoded)) =
            self.extract_transition_system_with_singleloop_fallback()
        else {
            return RawPdkindResult::Unknown;
        };

        // Reject unsupported state sorts. When BvToBool preprocessing was applied
        // (#5877), Bool state vars are expected from bit-blasting and we use the
        // relaxed guard. The #6500 false-unsat hazard (Bool SingleLoop LOCATION
        // variables) only exists when the system came through the SingleLoop
        // encoding, so the strict Bool-rejecting guard applies exactly there;
        // DIRECTLY-extracted systems keep their native Bool state vars (lustre
        // monitor flags) and use the same `allowing_bool` guard IMC/DAR/LAWI
        // already trust. Previously the strict guard rejected every Bool-heavy
        // lustre predicate before the first check, self-gating PDKIND off the
        // family golem's pdkind wins. Acceptance is unchanged either way: every
        // Safe answer still validates against the original clauses.
        let unsupported = if self.config.bv_to_bool_applied {
            ts.find_unsupported_transition_state_sort()
        } else if singleloop_encoded {
            ts.find_unsupported_interpolation_state_sort()
        } else {
            ts.find_unsupported_interpolation_state_sort_allowing_bool()
        };
        if unsupported.is_some() {
            return RawPdkindResult::Unknown;
        }

        // Check for trivial cases
        if let Some(result) = self.check_trivial_cases(&ts) {
            return result;
        }

        // Initialize
        let mut n = 0usize;
        let p = ChcExpr::not(ts.query.clone());
        let mut induction_frame = InductionFrame::default();
        induction_frame.insert(IFrameElement {
            lemma: p,
            counter_example: CounterExample {
                formula: ts.query.clone(),
                num_of_steps: 0,
            },
        });

        let mut reachability_checker = ReachabilityChecker::new(&ts, &self.config);

        // Main loop
        for iteration in 0..self.config.max_iterations {
            // Invariant: induction frame should not be empty — it is initialized
            // with the property lemma above, and push() preserves all obligations.
            // However, when all k-induction checks return Unknown (e.g., under
            // executor delegation #7985), the frame can legitimately empty.
            // Return Unknown rather than panicking.
            if induction_frame.is_empty() {
                if self.config.base.verbose {
                    safe_eprintln!(
                        "PDKIND: induction frame empty at iteration {} — returning Unknown",
                        iteration
                    );
                }
                return RawPdkindResult::Unknown;
            }

            // Check for cooperative cancellation or memory budget (#2769)
            if self.config.base.is_cancelled() {
                if self.config.base.verbose {
                    safe_eprintln!("PDKIND: Cancelled by portfolio or memory limit");
                }
                return RawPdkindResult::Unknown;
            }

            let k = n + 1;

            if self.config.base.verbose {
                safe_eprintln!(
                    "PDKIND: Iteration {}, n={}, k={}, frame_size={}",
                    iteration,
                    n,
                    k,
                    induction_frame.len()
                );
            }

            // Incremental k-induction via IncrementalQueryContext: encodes the
            // k-step transition once as background instead of re-encoding per
            // obligation. Adaptive fallback: if validate_inductive_invariant()
            // catches a false UNSAT, incremental_mode degrades for remaining
            // iterations (#2675, #8161).
            let use_incremental = !incremental_mode.skips_incremental();

            // Snapshot the frame BEFORE push() since push() mutates iframe in-place.
            // If the incremental result has false UNSAT, those mutations are wrong
            // and we need the original frame for the non-incremental retry.
            let iframe_snapshot = induction_frame.clone();
            let reachability_checkpoint = reachability_checker.lemma_size_checkpoint();
            let result = self.push(
                &ts,
                &mut induction_frame,
                n,
                k,
                &incremental_mode,
                &mut reachability_checker,
                obligation_timeout_secs,
            );

            if result.is_unknown {
                return RawPdkindResult::Unknown;
            }

            if result.is_invalid {
                // SOUNDNESS GUARD (#4729): Validate the claimed counterexample
                // with a non-incremental BMC check before declaring Unsafe.
                // MBP overgeneralization or incremental solver bugs can cause
                // push() to falsely claim reachability. Verify by unrolling:
                //   init@0 ∧ Trans^steps ∧ query@steps
                // If SAT, the counterexample is genuine. If UNSAT, it was spurious
                // and we continue with increased n.
                //
                // SOUNDNESS FIX (#2761/#6500): SingleLoop-encoded problems have
                // synthetic location variables in the transition system. BMC
                // validation on this TS can find paths that satisfy the encoded
                // init/trans/query but don't correspond to valid executions of
                // the original multi-predicate system. For SingleLoop problems,
                // don't trust BMC validation — treat all counterexamples as
                // potentially spurious and continue the main loop.
                let cex_steps = result.steps_to_cex;
                if !singleloop_encoded && Self::validate_counterexample(&ts, cex_steps) {
                    return RawPdkindResult::Unsafe(PdkindCounterexample { steps: cex_steps });
                }
                // Spurious counterexample — MBP or incremental solver gave a
                // false positive. Continue the main loop with increased n.
                if self.config.base.verbose {
                    safe_eprintln!(
                        "PDKIND: Spurious counterexample at {} steps — continuing",
                        cex_steps
                    );
                }
                n = result.n.max(n + 1);
                induction_frame = result.new_i_frame;
                continue;
            }

            // If ALL k-induction obligations timed out, the frame appears stable
            // only because timed-out obligations are kept. Skip the expensive
            // validate/retry path and advance n by stride (#4823).
            if result.kinduction_all_timed_out {
                if self.config.base.verbose {
                    safe_eprintln!(
                        "PDKIND: All k-induction checks timed out at k={}, advancing n",
                        k
                    );
                }
                n = result.n.max(n + 1);
                induction_frame = result.new_i_frame;
                continue;
            }

            if result.i_frame == result.new_i_frame {
                // Frame is stable - found k-inductive invariant
                let k_invariant = self.get_invariant(&result.i_frame);

                // Invariant: a stable k-inductive invariant should not be trivially
                // true — Bool(true) holds vacuously and is not a useful invariant.
                // It can arise from MBP overgeneralization or frame corruption.
                debug_assert!(
                    k_invariant != ChcExpr::Bool(true),
                    "BUG: stable frame produced trivial Bool(true) invariant at k={k}, n={n}, iteration={iteration}",
                );

                // Try to convert k-inductive invariant to 1-inductive if k > 1.
                // If conversion fails, use the k-inductive invariant directly —
                // it's still a valid safety proof (Golem PDKind does the same).
                // Previously, failure here caused an infinite n-doubling loop
                // because n grew exponentially when k-to-1 failed at every
                // stable frame.
                let invariant = if k > 1 {
                    if self.config.base.verbose {
                        safe_eprintln!(
                            "PDKIND: Converting k={} inductive invariant to 1-inductive",
                            k
                        );
                    }
                    match crate::k_to_1_inductive::convert(&k_invariant, k, &ts) {
                        Some(inv) => inv,
                        None => {
                            if self.config.base.verbose {
                                safe_eprintln!(
                                    "PDKIND: k-to-1 conversion failed at k={}, \
                                     accepting k-inductive invariant",
                                    k
                                );
                            }
                            k_invariant
                        }
                    }
                } else {
                    k_invariant
                };

                if !use_incremental {
                    // Non-incremental path: FreshOnly (BV) or Degraded (runtime
                    // false-UNSAT detection). Each push() creates a fresh
                    // IncrementalQueryContext, so per-obligation k-induction checks
                    // are reliable. The init+query guard catches any remaining
                    // structural issues (#2690, #8161).
                    //
                    // If any k-induction check in push() timed out, the frame can be
                    // stable without proving per-obligation inductiveness. In that
                    // case, require full inductive verification before returning Safe.
                    let verified = if result.has_unknown_kinduction {
                        validate_inductive_invariant(&ts, &invariant, Self::check_sat_10s).is_none()
                    } else {
                        self.verify_non_incremental_stable_invariant(&ts, &invariant, k)
                    };
                    if verified {
                        // SOUNDNESS GUARD (#6787): bounded BMC sanity check catches
                        // false Safe results. If it reaches the query within a
                        // small bound, return Unsafe instead of falling back to
                        // Unknown and forcing the portfolio to rediscover the bug.
                        let bmc_depth = (k * 5).clamp(30, 50);
                        if let Some(cex_depth) = self.bmc_sanity_counterexample_depth(bmc_depth) {
                            if self.config.base.verbose {
                                safe_eprintln!(
                                    "PDKIND: BMC sanity check found counterexample at depth {} after k={} stable frame (#6787)",
                                    cex_depth,
                                    k
                                );
                            }
                            return RawPdkindResult::Unsafe(PdkindCounterexample {
                                steps: cex_depth,
                            });
                        }
                        return RawPdkindResult::Safe(PdkindInvariant {
                            formula: invariant,
                            induction_depth: k,
                        });
                    }
                    // The stable frame was rejected (for example, vacuous
                    // k-inductiveness). Still check for a short concrete
                    // counterexample before giving up on this iteration.
                    let bmc_depth = (k * 5).clamp(30, 50);
                    if let Some(cex_depth) = self.bmc_sanity_counterexample_depth(bmc_depth) {
                        if self.config.base.verbose {
                            safe_eprintln!(
                                "PDKIND: bounded sanity BMC found counterexample at depth {} after rejecting stable frame at k={} (#6787)",
                                cex_depth,
                                k
                            );
                        }
                        return RawPdkindResult::Unsafe(PdkindCounterexample { steps: cex_depth });
                    }
                    n = result.n.max(n + 1);
                    induction_frame = result.new_i_frame;
                    continue;
                }

                // Incremental push was used — verify fully (including inductiveness)
                // to catch potential false UNSAT from IncrementalQueryContext.
                match validate_inductive_invariant(&ts, &invariant, Self::check_sat_10s) {
                    None => {
                        // validate_inductive_invariant checks 1-step inductiveness,
                        // so if it passes, the invariant is 1-inductive.
                        // SOUNDNESS GUARD (#6787): bounded BMC sanity check.
                        let bmc_depth = (k * 5).clamp(30, 50);
                        if let Some(cex_depth) = self.bmc_sanity_counterexample_depth(bmc_depth) {
                            if self.config.base.verbose {
                                safe_eprintln!(
                                    "PDKIND: BMC sanity check found counterexample at depth {} after incremental validation at k={} (#6787)",
                                    cex_depth,
                                    k
                                );
                            }
                            return RawPdkindResult::Unsafe(PdkindCounterexample {
                                steps: cex_depth,
                            });
                        }
                        return RawPdkindResult::Safe(PdkindInvariant {
                            formula: invariant,
                            induction_depth: 1,
                        });
                    }
                    Some(failed_check) => {
                        // Incremental solver gave false stability (#2690).
                        // Restore frame and retry with non-incremental solving.
                        // Adaptive fallback: degrade to non-incremental for remaining
                        // iterations to avoid repeated wasted work (#2675, #8161).
                        induction_frame = iframe_snapshot;
                        reachability_checker
                            .restore_lemma_size_checkpoint(&reachability_checkpoint);
                        incremental_mode = IncrementalMode::Degraded(format!(
                            "false-UNSAT detected: stable frame failed '{}' at k={}",
                            failed_check, k
                        ));

                        if self.config.base.verbose {
                            safe_eprintln!(
                                "PDKIND: Stable frame failed '{}' at k={}, \
                                 degrading to non-incremental and retrying",
                                failed_check,
                                k
                            );
                        }
                        let result_ni = self.push(
                            &ts,
                            &mut induction_frame,
                            n,
                            k,
                            &incremental_mode,
                            &mut reachability_checker,
                            obligation_timeout_secs,
                        );
                        if result_ni.is_unknown {
                            return RawPdkindResult::Unknown;
                        }
                        if result_ni.is_invalid {
                            // SOUNDNESS GUARD (#4729): same validation as incremental path.
                            // Skip for SingleLoop (#2761/#6500).
                            let cex_steps = result_ni.steps_to_cex;
                            if !singleloop_encoded && Self::validate_counterexample(&ts, cex_steps)
                            {
                                return RawPdkindResult::Unsafe(PdkindCounterexample {
                                    steps: cex_steps,
                                });
                            }
                            // Spurious — continue loop
                            n = result_ni.n.max(n + 1);
                            induction_frame = result_ni.new_i_frame;
                            continue;
                        }
                        if result_ni.i_frame == result_ni.new_i_frame {
                            let ni_k_inv = self.get_invariant(&result_ni.i_frame);
                            let ni_inv = if k > 1 {
                                crate::k_to_1_inductive::convert(&ni_k_inv, k, &ts)
                                    .unwrap_or(ni_k_inv)
                            } else {
                                ni_k_inv
                            };
                            // This path is a recovery from an incremental false-UNSAT
                            // signal. Keep the full inductive check as a guard so a
                            // weak k->1 conversion cannot slip through as Safe.
                            if validate_inductive_invariant(&ts, &ni_inv, Self::check_sat_10s)
                                .is_none()
                            {
                                // SOUNDNESS GUARD (#6787): bounded BMC sanity check.
                                let bmc_depth = (k * 5).clamp(30, 50);
                                if let Some(cex_depth) =
                                    self.bmc_sanity_counterexample_depth(bmc_depth)
                                {
                                    if self.config.base.verbose {
                                        safe_eprintln!(
                                            "PDKIND: BMC sanity check found counterexample at depth {} after ni-retry validation at k={} (#6787)",
                                            cex_depth,
                                            k
                                        );
                                    }
                                    return RawPdkindResult::Unsafe(PdkindCounterexample {
                                        steps: cex_depth,
                                    });
                                }
                                return RawPdkindResult::Safe(PdkindInvariant {
                                    formula: ni_inv,
                                    induction_depth: 1,
                                });
                            }
                        }
                        n = result_ni.n.max(n + 1);
                        induction_frame = result_ni.new_i_frame;
                        continue;
                    }
                }
            }

            n = result.n;
            induction_frame = result.new_i_frame;

            if n > self.config.max_n {
                if self.config.base.verbose {
                    safe_eprintln!("PDKIND: Exceeded max_n={}", self.config.max_n);
                }
                return RawPdkindResult::Unknown;
            }
        }

        if self.config.base.verbose {
            safe_eprintln!(
                "PDKIND: Exceeded max_iterations={}",
                self.config.max_iterations
            );
        }
        RawPdkindResult::Unknown
    }

    /// Convert an internal `RawPdkindResult` to a unified `ChcEngineResult`.
    fn convert_raw_result(&self, raw: RawPdkindResult) -> ChcEngineResult {
        match raw {
            RawPdkindResult::Safe(inv) => {
                match build_single_pred_model(&self.problem, inv.formula) {
                    Some(model) => ChcEngineResult::Safe(model),
                    None => ChcEngineResult::Unknown,
                }
            }
            RawPdkindResult::Unsafe(cex) => {
                ChcEngineResult::Unsafe(skeleton_counterexample(&self.problem, cex.steps))
            }
            RawPdkindResult::Unknown => ChcEngineResult::Unknown,
        }
    }

    /// Check trivial cases before main loop
    fn check_trivial_cases(&self, ts: &TransitionSystem) -> Option<RawPdkindResult> {
        let mut ctx = self.problem.make_smt_context();

        // Check if init is empty
        if ctx.check_sat(&ts.init).is_unsat() {
            return Some(RawPdkindResult::Safe(PdkindInvariant {
                formula: ChcExpr::Bool(false),
                induction_depth: 1,
            }));
        }

        // Check if init intersects query (immediate counterexample at step 0)
        let init_query = ChcExpr::and(ts.init.clone(), ts.query.clone());
        match ctx.check_sat(&init_query) {
            SmtResult::Sat(_) => {
                return Some(RawPdkindResult::Unsafe(PdkindCounterexample { steps: 0 }));
            }
            // SOUNDNESS NOTE (#2659): Unknown → fall through is conservative. We cannot
            // conclude immediate Unsafe, but the main PDKIND loop will still find the
            // counterexample through k-step reachability if it exists.
            SmtResult::Unknown => {}
            _ => {}
        }

        None
    }
}
