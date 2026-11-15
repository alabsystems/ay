// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! TPA solve-loop orchestration.

use crate::transition_system::TransitionSystem;
use crate::{ChcExpr, ChcVar, SmtResult};

use super::{ConcretePath, PowerKind, PowerResult, ReachResult, TpaResult, TpaSolver};
use crate::engine_result::skeleton_counterexample;
use crate::ground_derivation::linear_trace::{
    engine_trace_counterexample, LinearTrace, TraceEdgeHint,
};
use crate::pdr::Counterexample;

impl TpaSolver {
    /// Solve the CHC problem using TPA.
    pub(crate) fn solve(&mut self) -> TpaResult {
        if !self.ensure_transition_system() {
            return TpaResult::Unknown;
        }

        // Temporarily take the transition system out of self to split the borrow:
        // check_trivial and init_powers need &mut self and &TransitionSystem
        // simultaneously (#5574).
        let ts = self
            .transition_system
            .take()
            .expect("ensure_transition_system succeeded");
        let trivial = self.check_trivial(&ts);
        self.init_powers(&ts);
        self.transition_system = Some(ts);

        if let Some(result) = trivial {
            return result;
        }

        self.solve_powers()
    }

    /// Ensure the transition system is available, extracting it if needed.
    /// Returns true if the transition system is now available.
    fn ensure_transition_system(&mut self) -> bool {
        if self.transition_system.is_none() {
            match self.extract_transition_system() {
                Ok(ts) => self.transition_system = Some(ts),
                Err(e) => {
                    if self.config.verbose_level > 0 {
                        safe_eprintln!("TPA: Failed to extract transition system: {}", e);
                    }
                    return false;
                }
            }
        }
        true
    }

    /// Run the main TPA power-checking loop.
    fn solve_powers(&mut self) -> TpaResult {
        for power in 0..self.config.max_power {
            if self.is_cancelled() {
                if self.config.verbose_level > 0 {
                    safe_eprintln!("TPA: Cancelled at power {}", power);
                }
                return TpaResult::Unknown;
            }

            if self.config.verbose_level > 0 {
                safe_eprintln!(
                    "TPA: Checking power {} (up to 2^{} steps)",
                    power,
                    power + 1
                );
            }

            let power_start = ay_core::time::Instant::now();
            // `check_power` invokes interpolation helpers that contain plain
            // `check_sat` calls in addition to the explicitly timed TPA
            // queries. Keep every nested SMT call inside this power's declared
            // budget so exact arithmetic can observe the same hard deadline.
            let _power_deadline =
                crate::smt::ScopedSmtDeadline::install(self.config.timeout_per_power);
            let power_result = self.check_power(power);
            if self.config.verbose_level > 0 {
                safe_eprintln!("TPA: power {} took {:?}", power, power_start.elapsed());
            }

            match power_result {
                PowerResult::Safe => {
                    return TpaResult::Safe {
                        invariant: self.extract_invariant(),
                        power,
                    };
                }
                PowerResult::Unsafe { steps, path } => {
                    return TpaResult::Unsafe {
                        steps,
                        counterexample: self.unsafe_counterexample(steps, path),
                    };
                }
                PowerResult::Unknown => {
                    // If the conversion budget is exhausted, higher powers will
                    // only produce larger expressions that also exceed the budget.
                    // Bail early to free resources for other engines (#2472).
                    if self.smt.is_budget_exhausted() {
                        return TpaResult::Unknown;
                    }
                }
            }
        }

        if self.config.verbose_level > 0 {
            safe_eprintln!("TPA: Max power {} reached", self.config.max_power);
        }
        TpaResult::Unknown
    }

    /// Extract transition system from CHC problem.
    fn extract_transition_system(&mut self) -> Result<TransitionSystem, String> {
        let ts = TransitionSystem::from_chc_problem(&self.problem)?;
        self.ts_from_problem = true;
        Ok(ts)
    }

    /// The counterexample for an Unsafe verdict at `steps` transitions.
    fn unsafe_counterexample(&self, steps: u64, path: Option<ConcretePath>) -> Counterexample {
        match self.transition_system.as_ref() {
            Some(ts) => self.counterexample_for_path(ts, steps, path),
            None => skeleton_counterexample(&self.problem, Self::skeleton_depth(steps)),
        }
    }

    fn skeleton_depth(steps: u64) -> usize {
        usize::try_from(steps.min(100)).unwrap_or(100)
    }

    /// Ground-evidenced counterexample for `path` over this solver's
    /// problem, or a skeleton of `steps` when the path is missing, does not
    /// have `steps` transitions, belongs to a caller-supplied system, or does
    /// not ground-validate. Consumers re-validate either way.
    pub(super) fn counterexample_for_path(
        &self,
        ts: &TransitionSystem,
        steps: u64,
        path: Option<ConcretePath>,
    ) -> Counterexample {
        let skeleton = || skeleton_counterexample(&self.problem, Self::skeleton_depth(steps));
        let Some(path) = path.filter(|path| {
            self.ts_from_problem
                && path.states.len() <= ConcretePath::MAX_STEPS + 1
                && u64::try_from(path.states.len()).ok() == steps.checked_add(1)
                && path.transition_locals.len() + 1 == path.states.len()
        }) else {
            return skeleton();
        };
        let endpoint = TraceEdgeHint {
            ts_locals: path.endpoint_locals,
            ..TraceEdgeHint::default()
        };
        let mut edges = Vec::with_capacity(path.states.len() + 1);
        edges.push(endpoint.clone());
        edges.extend(
            path.transition_locals
                .into_iter()
                .map(|ts_locals| TraceEdgeHint {
                    ts_locals,
                    ..TraceEdgeHint::default()
                }),
        );
        edges.push(endpoint);
        let trace = LinearTrace {
            predicate: ts.predicate,
            states: path.states,
            edges,
        };
        engine_trace_counterexample(
            &self.problem,
            &trace,
            Self::skeleton_depth(steps),
            self.config.base.cancellation_token.as_ref(),
            "TPA",
        )
    }

    /// Check trivial unreachability cases.
    fn check_trivial(&mut self, ts: &TransitionSystem) -> Option<TpaResult> {
        // If query is false, trivially safe
        if ts.query == ChcExpr::Bool(false) {
            return Some(TpaResult::Safe {
                invariant: Some(ChcExpr::Bool(true)),
                power: 0,
            });
        }

        // If init is false, trivially safe
        if ts.init == ChcExpr::Bool(false) {
            return Some(TpaResult::Safe {
                invariant: Some(ChcExpr::Bool(true)),
                power: 0,
            });
        }

        // Check if init and query overlap (immediate counterexample)
        let init_and_query = ChcExpr::and(ts.init.clone(), ts.query.clone());
        match self
            .smt
            .check_sat_with_timeout(&init_and_query, self.config.timeout_per_power)
        {
            SmtResult::Sat(model) => {
                // Immediate counterexample: init state satisfies query
                let path = self.trivial_path(&model, ts);
                return Some(TpaResult::Unsafe {
                    steps: 0,
                    counterexample: self.counterexample_for_path(ts, 0, Some(path)),
                });
            }
            // SOUNDNESS NOTE (#2659): Unknown → fall through is conservative. We cannot
            // conclude immediate Unsafe, but TPA's power abstraction loop will still
            // find counterexamples through increasing transition powers.
            SmtResult::Unknown => {}
            _ => {}
        }

        None
    }

    /// Initialize power abstractions from transition system.
    ///
    /// Golem-style indexing (TPA.cc:resetPowers, line 846-851):
    /// - exact[0] = base transition T (represents exactly 2^0 = 1 step)
    /// - lt[0] = identity (represents less than 2^0 = less than 1 step = 0 steps)
    ///
    /// Higher levels are learned through interpolation, not pre-computed.
    /// This prevents geometric formula blowup from explicit power composition.
    pub(super) fn init_powers(&mut self, ts: &TransitionSystem) {
        self.exact_powers.clear();
        self.less_than_powers.clear();
        self.exact_query_cache.clear();
        self.state_invariants.clear();
        self.explanation = None;

        // exact[0] = base transition T (Golem: storeExactPower(0, transition))
        // Note: Must use transition_at(0), NOT ts.transition, because
        // ts.transition uses _next suffix while TPA uses numeric suffixes.
        self.exact_powers.push(Some(ts.transition_at(0)));

        // lt[0] = identity (Golem: lessThanPowers.push(identity))
        let identity = self.compute_identity(ts);
        self.less_than_powers.push(Some(identity));
    }

    /// Compute identity relation for state variables.
    ///
    /// Identity means: v_1 = v for all state variables (no change in one step).
    ///
    /// Uses numeric suffix convention (v, v_1) to be consistent with TPA's
    /// shift and rename operations which expect time-indexed variables.
    pub(in crate::tpa) fn compute_identity(&self, ts: &TransitionSystem) -> ChcExpr {
        let mut conjuncts = Vec::new();
        for var in ts.state_vars() {
            // Use numeric suffix (v_1) not _next to match TPA's variable naming
            let v1 = ChcVar::new(format!("{}_1", var.name), var.sort.clone());
            conjuncts.push(ChcExpr::eq(ChcExpr::var(v1), ChcExpr::var(var.clone())));
        }
        ChcExpr::and_all(conjuncts)
    }

    /// Check reachability at a given power level.
    pub(super) fn check_power(&mut self, power: u32) -> PowerResult {
        // Temporarily take the transition system out of self to split the borrow:
        // reachability functions need &mut self (for SMT queries) and &TransitionSystem
        // simultaneously. Extracting ts avoids cloning it on every call (#5574).
        let ts = self
            .transition_system
            .take()
            .expect("transition system set before solve");
        let init = ts.init.clone();
        let query = ts.query.clone();

        // First check less-than reachability: can we reach query in <2^{power+1} steps?
        let result = match self.reachability_less_than(&init, &query, power, &ts) {
            ReachResult::Reachable { steps, path, .. } => Some(PowerResult::Unsafe { steps, path }),
            ReachResult::Unreachable => {
                if self.config.verbose_level > 1 {
                    safe_eprintln!("TPA: System safe up to <2^{} steps", power + 1);
                }
                // Check for less-than fixed point only. The less-than fixed point
                // (T^{<n} ∘ T ⊆ T^{<n}) proves the power abstraction is closed
                // under one transition step, making it a proper inductive invariant
                // for full safety.
                //
                // SOUNDNESS (#7467): Do NOT check exact fixed point here. The exact
                // fixed point (T^{=n} ∘ T^{=n} ⊆ T^{=n}) only proves closure
                // under the specific power, not closure under arbitrary step counts.
                // Without building a safeTransitionInvariant from the combined
                // less-than and exact powers (as Golem TPA.cc:1080-1132 does),
                // accepting Safe from the exact fixed point alone is unsound.
                // Reference: Golem TPA.cc:checkLessThanFixedPoint (975-1078)
                if self.check_fixed_point(PowerKind::LessThan, power + 1, &ts) {
                    Some(PowerResult::Safe)
                } else {
                    None
                }
            }
            ReachResult::Unknown => {
                // Cannot determine less-than reachability; skip fixed point checks
                None
            }
        };

        if let Some(result) = result {
            self.transition_system = Some(ts);
            return result;
        }

        // Then check exact reachability: can we reach query in exactly 2^{power+1} steps?
        let result = match self.reachability_exact(&init, &query, power, &ts) {
            ReachResult::Reachable { steps, path, .. } => PowerResult::Unsafe { steps, path },
            ReachResult::Unreachable => {
                if self.config.verbose_level > 1 {
                    safe_eprintln!("TPA: System safe up to 2^{} steps", power + 1);
                }
                // SOUNDNESS (#7467): Do not accept Safe from exact fixed point.
                // Exact reachability unreachable only means the query is unreachable
                // in exactly 2^{power+1} steps. The exact fixed point would only
                // prove closure under multiples of that step count, not all steps.
                // Strengthening already happened inside reachability_exact above.
                PowerResult::Unknown
            }
            ReachResult::Unknown => {
                // Cannot determine exact reachability
                PowerResult::Unknown
            }
        };

        self.transition_system = Some(ts);
        result
    }
}
