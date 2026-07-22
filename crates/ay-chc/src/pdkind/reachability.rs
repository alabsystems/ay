// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Reachability checking with interpolation for PDKIND.

use super::types::*;
use crate::engine_utils::check_sat_with_timeout;
use crate::interpolation::{interpolating_sat_constraints_until, InterpolatingSatResult};
use crate::smt::{IncrementalCheckResult, IncrementalQueryContext, SmtContext, SmtResult};
use crate::transition_system::TransitionSystem;
use crate::ChcExpr;

/// Result of reachability checking
#[derive(Debug)]
pub(super) enum ReachabilityResult {
    /// State is reachable in the given number of steps
    Reachable { steps: usize },
    /// State is unreachable, with explanation (interpolant)
    Unreachable { explanation: ChcExpr },
    /// Could not determine reachability within safety limits
    Unknown,
}

/// Reachability checker using interpolation
pub(super) struct ReachabilityChecker {
    /// Transition system
    pub(super) ts: TransitionSystem,
    /// Per-level lemmas for reachability frames
    pub(super) lemmas: Vec<Vec<ChcExpr>>,
    /// Reused SMT context (shared by incremental solver for term conversion).
    pub(super) smt: SmtContext,
    /// Cached 1-step transition relation used by all reachability queries.
    pub(super) one_step_transition: ChcExpr,
    /// Incremental SAT solver for feasibility checks (transition as permanent background).
    /// Mirrors Golem's FrameSolver pattern (PDKind.cc:95-136).
    feasibility_inc: IncrementalQueryContext,
    /// Incremental SAT solver for zero-step reachability (init as permanent background).
    /// Mirrors Golem's zeroStepSolver (PDKind.cc:146,152-157).
    /// Used for the SAT/UNSAT decision; interpolants computed via non-incremental fallback.
    zero_step_inc: IncrementalQueryContext,
    /// Safety limit: maximum depth for reachability checking
    max_reachability_depth: usize,
    /// Safety limit: maximum loop iterations per reachability level
    max_reachability_iterations: usize,
    /// Per-check timeout for feasibility and reachability SMT queries (#4823).
    pub(super) smt_timeout: Option<std::time::Duration>,
    /// Deadline for reachability operations (#4823). When set, reachable()
    /// returns Unknown if the deadline passes. This caps the total time
    /// spent in reachability regardless of recursion depth or iterations.
    deadline: Option<ay_core::time::Instant>,
    /// Whether BvToBool preprocessing was applied (#5877). When true, the
    /// state space is all-Bool and we use SAT-native UNSAT core extraction
    /// instead of the arithmetic interpolation cascade.
    pub(super) bv_to_bool_applied: bool,
}

impl ReachabilityChecker {
    pub(super) fn new(ts: &TransitionSystem, config: &PdkindConfig) -> Self {
        let one_step_transition = ts.k_transition(1);
        let mut smt = SmtContext::new();

        // Pre-encode transition into incremental feasibility solver.
        // The transition relation is expensive to encode for SingleLoop problems
        // (20+ state variables). Encoding once as background avoids re-encoding
        // on every check_feasibility_at_t1 call.
        let mut feasibility_inc = IncrementalQueryContext::new();
        feasibility_inc.assert_background(&one_step_transition, &mut smt);
        feasibility_inc.finalize_background(&smt);

        // Pre-encode init into incremental zero-step solver.
        // Mirrors Golem's zeroStepSolver (PDKind.cc:152-157): init is permanent
        // background, each zero_step_reachability call does push/check/pop.
        let mut zero_step_inc = IncrementalQueryContext::new();
        zero_step_inc.assert_background(&ts.init, &mut smt);
        zero_step_inc.finalize_background(&smt);

        Self {
            ts: ts.clone(),
            lemmas: Vec::new(),
            smt,
            one_step_transition,
            feasibility_inc,
            zero_step_inc,
            max_reachability_depth: config.max_reachability_depth,
            max_reachability_iterations: config.max_reachability_iterations,
            smt_timeout: None,
            deadline: None,
            bv_to_bool_applied: config.bv_to_bool_applied,
        }
    }

    /// Set the per-check timeout for reachability SMT queries.
    pub(super) fn set_smt_timeout(&mut self, timeout: std::time::Duration) {
        self.smt_timeout = Some(timeout);
    }

    /// Set a deadline for reachability operations. After this instant,
    /// reachable() and check_reachability() return Unknown.
    pub(super) fn set_deadline(&mut self, deadline: ay_core::time::Instant) {
        self.deadline = Some(deadline);
    }

    /// Check if the reachability deadline has passed.
    fn past_deadline(&self) -> bool {
        self.deadline
            .is_some_and(|d| ay_core::time::Instant::now() >= d)
    }

    /// Wall-clock deadline for an interpolation call (#421). The interpolation
    /// cascade is otherwise UNBOUNDED — it ignores `smt_timeout` and runs tens of
    /// seconds on hard instances (e.g. dillig01), which is the real reason PDKIND
    /// hung past the 60s test budget at iteration 0. Bound it by the reachability
    /// deadline, or `now + smt_timeout` as a fallback. SOUND: a hit deadline only
    /// yields Unknown (the cex stays unrefuted), never a wrong verdict.
    fn interpolation_deadline(&self) -> ay_core::time::Instant {
        self.deadline.unwrap_or_else(|| {
            ay_core::time::Instant::now()
                + self
                    .smt_timeout
                    .unwrap_or(std::time::Duration::from_secs(10))
        })
    }

    /// Ensure we have space for level k
    fn ensure_level(&mut self, k: usize) {
        while self.lemmas.len() <= k {
            self.lemmas.push(Vec::new());
        }
    }

    /// Add a lemma at level k
    pub(super) fn add_lemma(&mut self, k: usize, lemma: ChcExpr) {
        self.ensure_level(k);
        self.lemmas[k].push(lemma);
    }

    /// Snapshot per-level lemma counts so speculative push() work can roll back.
    pub(super) fn lemma_size_checkpoint(&self) -> Vec<usize> {
        self.lemmas.iter().map(Vec::len).collect()
    }

    /// Restore lemmas to a previous checkpoint captured by `lemma_size_checkpoint`.
    pub(super) fn restore_lemma_size_checkpoint(&mut self, checkpoint: &[usize]) {
        self.lemmas.truncate(checkpoint.len());
        for (level, &count) in checkpoint.iter().enumerate() {
            if let Some(lemmas) = self.lemmas.get_mut(level) {
                lemmas.truncate(count);
            }
        }
    }

    /// Check zero-step reachability (from init).
    ///
    /// Uses the incremental zero-step solver (init as permanent background) for
    /// the SAT/UNSAT decision. Falls back to non-incremental interpolation when
    /// UNSAT is confirmed and we need an explanation lemma.
    /// Mirrors Golem's zeroStepSolver (PDKind.cc:388-391).
    pub(super) fn zero_step_reachability(&mut self, state: &ChcExpr) -> ReachabilityResult {
        // Fast path: incremental SAT check with init as permanent background.
        self.zero_step_inc.push();
        let inc_result = self.zero_step_inc.check_sat_incremental(
            std::slice::from_ref(state),
            &mut self.smt,
            self.smt_timeout,
        );
        self.zero_step_inc.pop();

        match inc_result {
            IncrementalCheckResult::Sat(_) => ReachabilityResult::Reachable { steps: 0 },
            IncrementalCheckResult::Unsat => {
                // Guard against incremental false-UNSAT on assumption-based checks.
                // We have seen this pattern in PDKind incremental paths (#2690/#2750).
                // Confirm UNSAT with a fresh non-incremental query before learning an
                // unreachable explanation.
                let query = ChcExpr::and(self.ts.init.clone(), state.clone());
                let confirm_result = if let Some(timeout) = self.smt_timeout {
                    check_sat_with_timeout(&query, timeout)
                } else {
                    self.smt.check_sat(&query)
                };
                match confirm_result {
                    SmtResult::Sat(_) => return ReachabilityResult::Reachable { steps: 0 },
                    SmtResult::Unknown => return ReachabilityResult::Unknown,
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {}
                }

                // Incremental confirmed UNSAT. Compute explanation for the
                // unreachability lemma.
                let state_vars = self.ts.state_var_names();

                if self.bv_to_bool_applied {
                    // Boolean state space (#5877 Wave 2): use SAT-native UNSAT
                    // core extraction instead of arithmetic interpolation.
                    let init = self.ts.init.clone();
                    if let Some(expl) = self.boolean_unsat_core_explanation(
                        std::slice::from_ref(&init),
                        std::slice::from_ref(state),
                        &state_vars,
                    ) {
                        ReachabilityResult::Unreachable { explanation: expl }
                    } else {
                        ReachabilityResult::Unreachable {
                            explanation: ChcExpr::not(state.clone()),
                        }
                    }
                } else {
                    // Arithmetic state space: existing interpolation cascade.
                    match interpolating_sat_constraints_until(
                        std::slice::from_ref(&self.ts.init),
                        std::slice::from_ref(state),
                        &state_vars,
                        self.interpolation_deadline(),
                    ) {
                        InterpolatingSatResult::Unsat(interp) => ReachabilityResult::Unreachable {
                            explanation: interp,
                        },
                        InterpolatingSatResult::Unknown => ReachabilityResult::Unreachable {
                            explanation: ChcExpr::not(state.clone()),
                        },
                    }
                }
            }
            // SOUNDNESS FIX (#421/#2654): Unknown means we can't decide.
            // #421 fixed: Unknown→Reachable caused false Unsafe.
            // #2654 fixed: Unknown→Unreachable caused false Safe.
            // Correct: propagate Unknown so push() sets unknown=true and
            // solve_raw() returns RawPdkindResult::Unknown.
            IncrementalCheckResult::Unknown => ReachabilityResult::Unknown,
        }
    }

    /// Check feasibility of reaching state from level k via transition.
    ///
    /// Uses incremental SAT with the transition as permanent background.
    /// Lemmas and state are asserted in a push/pop scope.
    fn check_feasibility_at_t1(&mut self, k: usize, state_t1: &ChcExpr) -> IncrementalCheckResult {
        let mut assumptions = Vec::new();

        // Add lemmas at level k (scoped per query)
        if k < self.lemmas.len() {
            for lemma in &self.lemmas[k] {
                let versioned = self.ts.send_through_time(lemma, 0);
                assumptions.push(versioned);
            }
        }

        // Add state constraint at time 1.
        assumptions.push(state_t1.clone());

        self.feasibility_inc.push();
        let result = self.feasibility_inc.check_sat_incremental(
            &assumptions,
            &mut self.smt,
            self.smt_timeout,
        );
        self.feasibility_inc.pop();
        result
    }

    /// Iteratively check reachability in k steps (explicit stack; no recursion).
    pub(super) fn reachable(&mut self, k: usize, formula: &ChcExpr) -> ReachabilityResult {
        if k == 0 {
            return self.zero_step_reachability(formula);
        }

        if self.max_reachability_depth == 0 || self.max_reachability_iterations == 0 {
            return ReachabilityResult::Unknown;
        }

        #[derive(Clone, Copy, Debug)]
        enum ReachPhase {
            CheckFeasibility,
            ProcessChildResult,
        }

        #[derive(Debug)]
        struct ReachFrame {
            k: usize,
            formula: ChcExpr,
            versioned_formula: ChcExpr,
            iterations: usize,
            phase: ReachPhase,
        }

        // NOTE: We avoid pushing a k==0 frame; base reachability is computed directly.
        let mut stack: Vec<ReachFrame> = vec![ReachFrame {
            k,
            formula: formula.clone(),
            versioned_formula: self.ts.send_through_time(formula, 1),
            iterations: 0,
            phase: ReachPhase::CheckFeasibility,
        }];

        let mut last_result: Option<ReachabilityResult> = None;

        loop {
            // Invariant: stack depth must not exceed max_reachability_depth.
            debug_assert!(
                stack.len() <= self.max_reachability_depth + 1,
                "BUG: reachability stack depth {} exceeds max {} + 1",
                stack.len(),
                self.max_reachability_depth
            );

            let Some(frame) = stack.last_mut() else {
                break;
            };

            if self.past_deadline() {
                return ReachabilityResult::Unknown;
            }
            match frame.phase {
                ReachPhase::CheckFeasibility => {
                    if frame.iterations >= self.max_reachability_iterations {
                        last_result = Some(ReachabilityResult::Unknown);
                        stack.pop();
                        continue;
                    }
                    frame.iterations += 1;

                    // Check if formula is reachable from frames[k-1] via one transition
                    let feasibility =
                        self.check_feasibility_at_t1(frame.k - 1, &frame.versioned_formula);

                    match feasibility {
                        IncrementalCheckResult::Sat(model) => {
                            // Generalize and check k-1 step reachability.
                            // SOUNDNESS FIX (#421): Use 1-step transition as in Golem PDKind.cc:452-453
                            let g =
                                self.generalize(&model, &self.one_step_transition, &frame.formula);

                            frame.phase = ReachPhase::ProcessChildResult;

                            let child_k = frame.k - 1;
                            debug_assert!(
                                child_k < frame.k,
                                "BUG: child_k={} not less than frame.k={}",
                                child_k,
                                frame.k
                            );
                            if child_k == 0 {
                                last_result = Some(self.zero_step_reachability(&g));
                                continue;
                            }

                            if stack.len() >= self.max_reachability_depth {
                                last_result = Some(ReachabilityResult::Unknown);
                                stack.pop();
                                continue;
                            }

                            stack.push(ReachFrame {
                                k: child_k,
                                formula: g.clone(),
                                versioned_formula: self.ts.send_through_time(&g, 1),
                                iterations: 0,
                                phase: ReachPhase::CheckFeasibility,
                            });
                            continue;
                        }
                        IncrementalCheckResult::Unknown => {
                            // SOUNDNESS FIX (#2659): Unknown must not be treated as Unsat.
                            last_result = Some(ReachabilityResult::Unknown);
                            stack.pop();
                            continue;
                        }
                        IncrementalCheckResult::Unsat => {}
                    }

                    // Formula is not reachable in k steps (Unsat confirmed).
                    // Compute interpolant.
                    let boundary_vars = self.ts.state_var_names_at(1);
                    let a_constraints: Vec<_> = if frame.k - 1 < self.lemmas.len() {
                        self.lemmas[frame.k - 1]
                            .iter()
                            .map(|l| self.ts.send_through_time(l, 0))
                            .chain(std::iter::once(self.one_step_transition.clone()))
                            .collect()
                    } else {
                        vec![self.one_step_transition.clone()]
                    };
                    let b_constraints = vec![frame.versioned_formula.clone()];

                    let unversioned_interp = if self.bv_to_bool_applied {
                        // Boolean state space (#5877 Wave 2): SAT-native core.
                        if let Some(interp_time1) = self.boolean_unsat_core_explanation(
                            &a_constraints,
                            &b_constraints,
                            &boundary_vars,
                        ) {
                            self.ts.shift_versioned_state_vars(&interp_time1, -1)
                        } else {
                            ChcExpr::not(frame.formula.clone())
                        }
                    } else {
                        // Arithmetic state space: interpolation cascade.
                        match interpolating_sat_constraints_until(
                            &a_constraints,
                            &b_constraints,
                            &boundary_vars,
                            self.interpolation_deadline(),
                        ) {
                            InterpolatingSatResult::Unsat(interp_time1) => {
                                self.ts.shift_versioned_state_vars(&interp_time1, -1)
                            }
                            InterpolatingSatResult::Unknown => ChcExpr::not(frame.formula.clone()),
                        }
                    };

                    // Combine with zero-step unreachability to strengthen the
                    // explanation lemma.
                    if let ReachabilityResult::Unreachable {
                        explanation: zero_expl,
                    } = self.zero_step_reachability(&frame.formula)
                    {
                        last_result = Some(ReachabilityResult::Unreachable {
                            explanation: ChcExpr::or(unversioned_interp, zero_expl),
                        });
                        stack.pop();
                        continue;
                    }

                    last_result = Some(ReachabilityResult::Unreachable {
                        explanation: unversioned_interp,
                    });
                    stack.pop();
                }
                ReachPhase::ProcessChildResult => {
                    let child_result = last_result.take().unwrap_or(ReachabilityResult::Unknown);
                    match child_result {
                        ReachabilityResult::Reachable { steps } => {
                            last_result = Some(ReachabilityResult::Reachable {
                                steps: steps.saturating_add(1),
                            });
                            stack.pop();
                        }
                        result @ ReachabilityResult::Unknown => {
                            last_result = Some(result);
                            stack.pop();
                        }
                        ReachabilityResult::Unreachable { explanation } => {
                            self.add_lemma(frame.k - 1, explanation);
                            frame.phase = ReachPhase::CheckFeasibility;
                        }
                    }
                }
            }
        }

        last_result.unwrap_or(ReachabilityResult::Unknown)
    }

    /// Check reachability from step `from` to step `to`
    pub(super) fn check_reachability(
        &mut self,
        from: usize,
        to: usize,
        formula: &ChcExpr,
    ) -> ReachabilityResult {
        let mut saw_unknown = false;
        for i in from..=to {
            if self.past_deadline() {
                return ReachabilityResult::Unknown;
            }
            match self.reachable(i, formula) {
                result @ ReachabilityResult::Reachable { .. } => return result,
                ReachabilityResult::Unknown => saw_unknown = true,
                unreachable @ ReachabilityResult::Unreachable { .. } => {
                    if i == to {
                        if saw_unknown {
                            return ReachabilityResult::Unknown;
                        }
                        return unreachable;
                    }
                }
            }
        }
        // SOUNDNESS FIX (#2652): If any iteration returned Unknown (including the
        // last one), we must propagate Unknown — not silently claim Unreachable.
        if saw_unknown {
            return ReachabilityResult::Unknown;
        }
        ReachabilityResult::Unreachable {
            explanation: ChcExpr::Bool(false),
        }
    }
}
