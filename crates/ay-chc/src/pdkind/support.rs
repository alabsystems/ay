// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Construction, SingleLoop fallback, and result conversion for PDKIND.

use super::*;

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
    pub(super) fn extract_transition_system_with_singleloop_fallback(
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

    /// Convert an internal `RawPdkindResult` to a unified `ChcEngineResult`.
    pub(super) fn convert_raw_result(&self, raw: RawPdkindResult) -> ChcEngineResult {
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
    pub(super) fn check_trivial_cases(&self, ts: &TransitionSystem) -> Option<RawPdkindResult> {
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
