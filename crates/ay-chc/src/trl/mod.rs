// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TRL (Transitive Relation Learning) Engine
//!
//! TRL is a BMC-based algorithm that proves safety by learning transitive relations
//! to shortcut loops. When the solver can no longer find paths to error states
//! (diameter reached), the system is safe.
//!
//! # Algorithm Overview
//!
//! 1. Run BMC incrementally, asserting init at time 0
//! 2. At each depth, check if query is reachable (SAT = unknown/unsafe)
//! 3. Check if any transition is possible (UNSAT = diameter reached = safe)
//! 4. If a trace contains a loop:
//!    - Learn a transitive relation summarizing the loop
//!    - Add blocking clause to prevent using the original loop
//!    - Backtrack to loop start
//!
//! # References
//!
//! - CADE 2025: "Infinite-State Model Checking by Learning Transitive Relations"
//! - LoAT implementation: `reference/loat-src/src/trl/trl.cpp`
//!
//! # Issue
//!
//! Part of #1163

mod certificates;
mod composition;
mod encoding;
#[cfg(test)]
pub(crate) mod interleaved;
mod loop_learning;

use certificates::{DiameterResult, UnsafeReplayResult};

use crate::cvp::cvp;
use crate::engine_config::ChcEngineConfig;
use crate::engine_result::ChcEngineResult;
use crate::kind::{KindConfig, KindSolver};
use crate::mbp::Mbp;
use crate::pdr::counterexample::{Counterexample, CounterexampleStep};
use crate::pdr::model::{InvariantModel, InvariantVerificationMethod, PredicateInterpretation};
use crate::pdr::{PdrConfig, PdrSolver};
use crate::smt::{
    IncrementalCheckResult, IncrementalQueryContext, SmtContext, SmtResult, SmtValue,
};
use crate::trace::{build_trace, Trace};
use crate::transition_system::TransitionSystem;
use crate::trp::Trp;
use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use std::time::Duration;

pub(crate) const TRP_N_VAR_NAME: &str = "__trp_n";
/// Self-loop saturation detection threshold (#1665).
/// When the same self-loop is detected this many times consecutively,
/// TRL returns Unknown to allow fallback to other CHC engines.
const TRL_SELF_LOOP_SATURATION_LIMIT: usize = 10;
/// Per-check timeout for incremental SMT queries.
///
/// Without this, a single `check_sat_incremental` call can consume the entire
/// portfolio budget. 2 seconds is generous for typical TRL checks (most complete
/// in <100ms) but prevents the DPLL(T) loop from spinning indefinitely on
/// hard post-learning formulas (bouncy_three_counters_merged #5294).
const TRL_PER_CHECK_TIMEOUT: Duration = Duration::from_secs(2);

/// Search direction for TRL reachability.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum TrlDirection {
    /// Standard forward search from init toward the query.
    #[default]
    Forward,
    /// Backward search from the query toward init.
    Backward,
}

/// TRL solver configuration.
///
/// Internal — only `Default::default()` is used in production.
#[derive(Debug, Clone)]
pub struct TrlConfig {
    /// Common engine settings (verbose, cancellation).
    pub base: ChcEngineConfig,
    /// Maximum unrolling depth (default: 1000).
    pub max_depth: usize,
    /// Maximum iterations (default: 10000).
    pub max_iterations: usize,
    /// Search direction (default: forward).
    pub direction: TrlDirection,
}

impl Default for TrlConfig {
    fn default() -> Self {
        Self {
            base: ChcEngineConfig::default(),
            max_depth: 1000,
            max_iterations: 10000,
            direction: TrlDirection::Forward,
        }
    }
}

// TrlResult removed — uses ChcEngineResult (#2791)

/// TRL solver state.
pub(crate) struct TrlSolver {
    pub(super) ts: TransitionSystem,
    config: TrlConfig,
    /// Learned transitive relations (index 0 = original transition).
    learned: Vec<ChcExpr>,
    /// Blocking clauses per depth: Map<depth, Map<learned_id, clause>>.
    blocked: FxHashMap<usize, FxHashMap<usize, ChcExpr>>,
    /// Track repeated loop handling to detect self-loop saturation.
    last_loop: Option<(usize, usize)>,
    same_loop_streak: usize,
    /// Execution trace with dependency graph.
    pub(super) trace: Trace,
    /// MBP instance for implicant extraction.
    pub(super) mbp: Mbp,
    /// TRP instance for transitive projection.
    trp: Trp,
    /// Incremental SMT context for persistent encoding across depths.
    /// Eliminates O(D^2) re-encoding cost — transitions are encoded once.
    inc_smt: IncrementalQueryContext,
    /// Helper SMT context for expression conversion (shared with inc_smt).
    smt_helper: SmtContext,
    /// Highest depth whose transition has been added to the incremental background.
    /// 0 means only init@0 is encoded (no transitions yet).
    encoded_depth: usize,
    /// Current unrolling depth (persisted across `do_step` calls).
    depth: usize,
    /// Total iteration count (persisted across `do_step` calls).
    iterations: usize,
}

impl TrlSolver {
    /// Create a new TRL solver with the given (crate-internal) config.
    pub(crate) fn new(ts: TransitionSystem, config: TrlConfig) -> Self {
        let transition = ts.transition.clone();
        let trp = Trp::new(ts.vars.clone());

        // Set up incremental SMT context with init@0 as permanent background.
        let mut inc_smt = IncrementalQueryContext::new();
        let mut smt_helper = SmtContext::new();
        let init_at_0 = TransitionSystem::version_expr(&ts.init, &ts.vars, 0);
        inc_smt.assert_background(&init_at_0, &mut smt_helper);
        inc_smt.finalize_background(&smt_helper);

        Self {
            ts,
            config,
            learned: vec![transition], // pi[0] = original transition
            blocked: FxHashMap::default(),
            last_loop: None,
            same_loop_streak: 0,
            trace: Trace::new(),
            mbp: Mbp::new(),
            trp,
            inc_smt,
            smt_helper,
            encoded_depth: 0,
            depth: 0,
            iterations: 0,
        }
    }

    fn record_loop_streak(&mut self, start: usize, end: usize) -> usize {
        match self.last_loop {
            Some((s, e)) if s == start && e == end => {
                self.same_loop_streak += 1;
            }
            _ => {
                self.last_loop = Some((start, end));
                self.same_loop_streak = 1;
            }
        }
        self.same_loop_streak
    }

    fn reset_loop_streak(&mut self) {
        self.last_loop = None;
        self.same_loop_streak = 0;
    }

    /// Main TRL algorithm.
    pub(crate) fn solve(&mut self) -> ChcEngineResult {
        loop {
            if let Some(result) = self.do_step() {
                return result;
            }
        }
    }

    #[cfg(test)]
    #[allow(dead_code)]
    pub(crate) fn trp_family_summary_statistics(
        &self,
    ) -> crate::trp::AcceleratedSummaryTrpFamilySummaryStatistics {
        self.trp.accelerated_summary_family_summary_statistics()
    }

    /// Perform one step of the TRL algorithm.
    ///
    /// Returns `None` if more work remains (caller should call again).
    /// Returns `Some(result)` when a definitive answer is reached.
    ///
    /// Port of LoAT StepwiseAnalysis::do_step() contract (#7327).
    pub(crate) fn do_step(&mut self) -> Option<ChcEngineResult> {
        // Check cancellation (includes memory budget check #2769)
        if self.config.base.is_cancelled() {
            return Some(ChcEngineResult::Unknown);
        }

        self.iterations += 1;
        if self.iterations > self.config.max_iterations {
            if self.config.base.verbose {
                safe_eprintln!(
                    "[TRL] Max iterations {} reached at depth {}, returning Unknown",
                    self.iterations,
                    self.depth
                );
            }
            return Some(ChcEngineResult::Unknown);
        }

        self.depth += 1;
        if self.depth > self.config.max_depth {
            if self.config.base.verbose {
                safe_eprintln!("[TRL] Max depth {} reached, returning Unknown", self.depth);
            }
            return Some(ChcEngineResult::Unknown);
        }

        let depth = self.depth;

        if self.config.base.verbose {
            safe_eprintln!(
                "[TRL] Depth {}, {} learned relations, {} blocked entries",
                depth,
                self.learned.len(),
                self.blocked
                    .values()
                    .map(|blocked| blocked.len())
                    .sum::<usize>()
            );
        }

        // Check if error is reachable at this depth.
        // SOUNDNESS FIX (#2659): Unknown must not be treated as "not reachable"
        // -- that could cause TRL to conclude diameter prematurely.
        if self.config.base.verbose {
            safe_eprintln!("[TRL] Checking error reachability at depth {}", depth);
        }
        let t0 = ay_core::time::Instant::now();
        match self.check_error_reachable(depth) {
            IncrementalCheckResult::Sat(_) => {
                match self.replay_unsafe_depth(depth) {
                    UnsafeReplayResult::Confirmed(cex) => {
                        if self.config.base.verbose {
                            safe_eprintln!(
                                "[TRL] Error reachable at depth {} ({:.1}ms), returning Unsafe",
                                depth,
                                t0.elapsed().as_secs_f64() * 1000.0
                            );
                        }
                        return Some(ChcEngineResult::Unsafe(cex));
                    }
                    UnsafeReplayResult::Spurious => {
                        if self.config.base.verbose {
                            safe_eprintln!(
                                "[TRL] Error reachable at depth {} ({:.1}ms), but exact-depth replay was spurious; continuing",
                                depth,
                                t0.elapsed().as_secs_f64() * 1000.0
                            );
                        }
                    }
                    UnsafeReplayResult::Inconclusive => {
                        // #7170: Treat inconclusive replay as spurious and continue.
                        // The replay solver timed out or returned Unknown on the original
                        // transition unrolling — this does NOT confirm the error path.
                        // Learned shortcut relations overapproximate, so the path found
                        // through shortcuts may not exist on the original system. Continue
                        // to deeper depths where the diameter bound or a confirmable path
                        // may be found. Max-depth/max-iterations/portfolio budget prevent
                        // unbounded exploration.
                        if self.config.base.verbose {
                            safe_eprintln!(
                                "[TRL] Error reachable at depth {} ({:.1}ms), but exact-depth replay inconclusive; treating as spurious, continuing",
                                depth,
                                t0.elapsed().as_secs_f64() * 1000.0
                            );
                        }
                    }
                }
            }
            IncrementalCheckResult::Unknown => {
                if self.config.base.verbose {
                    safe_eprintln!(
                        "[TRL] Error reachability unknown at depth {} ({:.1}ms), returning Unknown",
                        depth,
                        t0.elapsed().as_secs_f64() * 1000.0
                    );
                }
                return Some(ChcEngineResult::Unknown);
            }
            IncrementalCheckResult::Unsat => {
                if self.config.base.verbose {
                    safe_eprintln!(
                        "[TRL] Error unreachable at depth {} ({:.1}ms)",
                        depth,
                        t0.elapsed().as_secs_f64() * 1000.0
                    );
                }
            }
        }

        // Check if any path exists to this depth (encoding already extended above).
        if self.config.base.verbose {
            safe_eprintln!("[TRL] Checking path existence at depth {}", depth);
        }
        let t1 = ay_core::time::Instant::now();
        let mut path_result = self.inc_smt.check_sat_incremental(
            &[],
            &mut self.smt_helper,
            Some(TRL_PER_CHECK_TIMEOUT),
        );
        // #7165: Executor fallback for path existence when incremental returns Unknown.
        if matches!(path_result, IncrementalCheckResult::Unknown) {
            let fresh = self.build_error_reachability_formula(
                depth,
                &ChcExpr::Bool(true), // no query constraint — just check path existence
            );
            self.smt_helper.reset();
            // #7398: Reset incremental solver after TermStore reset to prevent
            // stale TermIds from crashing BvSolver::bitblast_predicate.
            self.reset_incremental_solver();
            let fresh_result = self
                .smt_helper
                .check_sat_with_executor_fallback_timeout(&fresh, TRL_PER_CHECK_TIMEOUT);
            match fresh_result {
                SmtResult::Sat(model) => {
                    path_result = IncrementalCheckResult::Sat(model);
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    path_result = IncrementalCheckResult::Unsat;
                }
                SmtResult::Unknown => {} // keep original Unknown
            }
        }
        if self.config.base.verbose {
            safe_eprintln!(
                "[TRL] Path check at depth {} completed ({:.1}ms): {:?}",
                depth,
                t1.elapsed().as_secs_f64() * 1000.0,
                match &path_result {
                    IncrementalCheckResult::Sat(_) => "sat",
                    IncrementalCheckResult::Unsat => "unsat",
                    IncrementalCheckResult::Unknown => "unknown",
                }
            );
        }
        match path_result {
            IncrementalCheckResult::Unsat => {
                if self.config.base.verbose {
                    safe_eprintln!(
                        "[TRL] Path UNSAT at depth {} — verifying diameter with fresh solver",
                        depth
                    );
                }
                let diameter_status = self.verify_diameter_fresh(depth);
                if self.config.base.verbose {
                    safe_eprintln!(
                        "[TRL] Diameter status at depth {}: {:?}",
                        depth,
                        diameter_status
                    );
                }

                // SOUNDNESS (#7384): Only attempt expanded-system invariant
                // synthesis when the diameter is genuinely confirmed. When
                // diameter is Spurious, blocking clauses caused the path UNSAT
                // — paths still exist in the original system, so a Safe claim
                // from the expanded system is unsound. When Inconclusive, we
                // cannot determine whether the diameter is real.
                match diameter_status {
                    DiameterResult::Confirmed => {
                        if let Some(model) = self.synthesize_safe_model_from_expanded_system(depth)
                        {
                            if self.config.base.verbose {
                                safe_eprintln!(
                                    "[TRL] Diameter confirmed, expanded-system invariant synthesized at depth {} — returning Safe",
                                    depth
                                );
                            }
                            return Some(ChcEngineResult::Safe(model));
                        }
                        if self.config.base.verbose {
                            safe_eprintln!(
                                "[TRL] Diameter confirmed at depth {} but synthesis failed — returning Unknown",
                                depth
                            );
                        }
                        return Some(ChcEngineResult::Unknown);
                    }
                    DiameterResult::Spurious => {
                        if self.config.base.verbose {
                            safe_eprintln!(
                                "[TRL] Diameter spurious at depth {} — continuing",
                                depth
                            );
                        }
                        return None; // continue to next step
                    }
                    DiameterResult::Inconclusive => {
                        // #1306: Don't give up when diameter can't be verified.
                        // The path UNSAT came from learned shortcuts + blocking,
                        // not the original system. Continue to deeper depths where
                        // TRL may learn more relations or confirm diameter.
                        // Golem's TPA also continues on inconclusive diameter.
                        // Max depth/iterations/portfolio budget prevent unbounded
                        // exploration.
                        if self.config.base.verbose {
                            safe_eprintln!(
                                "[TRL] Diameter inconclusive at depth {} — continuing (not giving up)",
                                depth
                            );
                        }
                        return None; // continue to next depth
                    }
                }
            }
            IncrementalCheckResult::Unknown => {
                if self.config.base.verbose {
                    safe_eprintln!("[TRL] Path check unknown at depth {depth}, skipping");
                }
                return None; // continue to next step
            }
            IncrementalCheckResult::Sat(model) => {
                // Build trace from model
                self.build_trace_from_model(depth, &model);

                // Check for loops
                if let Some((start, end)) = self.trace.find_looping_infix() {
                    if self.config.base.verbose {
                        safe_eprintln!("[TRL] Loop detected: {} -> {}", start, end);
                    }

                    if start == end {
                        let streak = self.record_loop_streak(start, end);
                        if streak > TRL_SELF_LOOP_SATURATION_LIMIT {
                            if self.config.base.verbose {
                                safe_eprintln!(
                                    "[TRL] Self-loop saturation detected: {} -> {} repeated {} times, returning Unknown",
                                    start, end, streak
                                );
                            }
                            return Some(ChcEngineResult::Unknown);
                        }
                    } else {
                        self.reset_loop_streak();
                    }

                    if !self.handle_loop(start, end) {
                        if self.config.base.verbose {
                            safe_eprintln!(
                                "[TRL] Loop handling could not make progress for {} -> {}, returning Unknown",
                                start, end
                            );
                        }
                        return Some(ChcEngineResult::Unknown);
                    }

                    // Backtrack to loop start.
                    self.depth = start;
                    return None; // continue to next step
                }
            }
        }

        None // no conclusion yet, continue
    }
}

#[cfg(test)]
impl interleaved::StepwiseTrl for TrlSolver {
    fn do_step(&mut self) -> Option<ChcEngineResult> {
        self.do_step()
    }
}

#[cfg(test)]
#[path = "tests.rs"]
mod tests;

#[cfg(kani)]
#[path = "verification.rs"]
mod verification;
