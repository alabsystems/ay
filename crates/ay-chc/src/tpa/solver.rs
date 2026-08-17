// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! TPA solver implementation.
//!
//! Ported from Golem's TPA.cc (MIT license).

mod solve_loop;

use std::sync::Arc;
use std::time::Duration;

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

use crate::engine_config::ChcEngineConfig;
use crate::transition_system::TransitionSystem;
use crate::{ChcExpr, ChcOp, ChcProblem, SmtContext, SmtValue};

/// TPA solver configuration.
#[derive(Clone, Debug)]
pub struct TpaConfig {
    /// Common engine settings (verbose, cancellation).
    pub(crate) base: ChcEngineConfig,

    /// Maximum power level to check (default: 20, meaning up to 2^20 steps)
    pub(crate) max_power: u32,

    /// Timeout per power level check
    pub(crate) timeout_per_power: Duration,

    /// Verbosity level (0 = silent, 1 = basic, 2 = detailed).
    pub(crate) verbose_level: u8,
}

impl Default for TpaConfig {
    fn default() -> Self {
        Self {
            base: ChcEngineConfig::default(),
            max_power: 20,
            timeout_per_power: Duration::from_secs(30),
            verbose_level: 0,
        }
    }
}

impl TpaConfig {
    /// Create a TpaConfig with a custom max_power limit.
    #[cfg(test)]
    fn with_max_power(max_power: u32) -> Self {
        Self {
            max_power,
            ..Self::default()
        }
    }
}

/// Result of TPA solving.
#[derive(Debug, Clone)]
#[must_use = "TPA results must be checked — ignoring Safe/Unsafe loses correctness"]
pub enum TpaResult {
    /// System is safe - bad states unreachable
    Safe {
        /// Inductive invariant (if computed)
        invariant: Option<ChcExpr>,
        /// Power level at which safety was proven
        power: u32,
    },

    /// System is unsafe - bad states reachable
    Unsafe {
        /// Number of steps to reach bad state
        steps: u64,
        /// Counterexample trace: state assignments at each step boundary.
        ///
        /// Each entry maps state variable names to their values at that step.
        /// For TPA's power abstraction, intermediate states are extracted from
        /// the SAT model at times 0, 1, and 2 (where each "step" in the
        /// abstraction represents 2^power actual transitions).
        trace: Option<Vec<FxHashMap<String, SmtValue>>>,
    },

    /// Could not determine safety within limits
    Unknown,
}

impl std::fmt::Display for TpaResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Safe { power, .. } => write!(f, "safe (proven at power {power})"),
            Self::Unsafe { steps, .. } => {
                write!(f, "unsafe (counterexample at depth {steps})")
            }
            Self::Unknown => write!(f, "unknown (reached limits)"),
        }
    }
}

/// Whether we're working with exact (T^{=n}) or less-than (T^{<n}) power abstractions.
///
/// Used to dispatch between the two parallel power abstraction hierarchies
/// without duplicating strengthen/fixed-point logic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum PowerKind {
    /// Exact: T^{=n} represents exactly 2^n steps
    Exact,
    /// LessThan: T^{<n} represents less than 2^n steps
    LessThan,
}

/// Result of checking a power level.
pub(super) enum PowerResult {
    Safe,
    Unsafe {
        steps: u64,
        /// Model from SAT query (for trace extraction)
        model: FxHashMap<String, SmtValue>,
    },
    Unknown,
}

/// Records the 1-inductive state invariant a fixed-point exit certified.
///
/// AY's less-than power abstractions are learned as Craig interpolants over the
/// reached-state variables (time index 1), i.e. they are *state sets*
/// over-approximating the states reachable from init — not the two-copy
/// transition relations of Golem's `TPASplit`. The less-than fixed point is
/// therefore a standard 1-inductive state-invariant check, and the invariant it
/// certifies is stored directly here.
///
/// Every emitted invariant is independently re-checked by the portfolio's
/// `verify_model_per_rule` gate on the ORIGINAL clauses, so this metadata only
/// influences whether a conversion succeeds — never soundness.
#[derive(Debug, Clone)]
pub(super) struct SafetyExplanation {
    /// A 1-inductive safe state invariant `Inv(x)` over the base state vars:
    /// `init ⇒ Inv`, `Inv ∧ Tr ⇒ Inv'`, and `Inv ∧ query` UNSAT — all verified
    /// with the SMT backend before recording.
    pub(super) state_invariant: ChcExpr,
}

/// Result of reachability query.
pub(super) enum ReachResult {
    Reachable {
        steps: u64,
        /// Model from SAT query (for trace extraction)
        model: FxHashMap<String, SmtValue>,
        /// Refined target: the subset of the original target that is actually reachable.
        /// Used in recursive decomposition to pass verified intermediate states.
        refined_target: Option<ChcExpr>,
    },
    Unreachable,
    /// SMT solver returned Unknown; cannot determine reachability (#2654).
    Unknown,
}

/// Cache entry for exact reachability queries.
///
/// Mirrors Golem's `queryCache[level][(from, to)]` for exact queries:
/// fully verified Reachable/Unreachable answers can be reused across
/// recursive midpoint retries, while `Unknown` is intentionally never cached.
#[derive(Clone)]
pub(super) enum ExactQueryCacheEntry {
    Reachable {
        steps: u64,
        model: FxHashMap<String, SmtValue>,
        refined_target: Option<ChcExpr>,
    },
    Unreachable,
}

impl ExactQueryCacheEntry {
    fn into_reach_result(self) -> ReachResult {
        match self {
            Self::Reachable {
                steps,
                model,
                refined_target,
            } => ReachResult::Reachable {
                steps,
                model,
                refined_target,
            },
            Self::Unreachable => ReachResult::Unreachable,
        }
    }

    fn from_reach_result(result: &ReachResult) -> Option<Self> {
        match result {
            ReachResult::Reachable {
                steps,
                model,
                refined_target,
            } => Some(Self::Reachable {
                steps: *steps,
                model: model.clone(),
                refined_target: refined_target.clone(),
            }),
            ReachResult::Unreachable => Some(Self::Unreachable),
            ReachResult::Unknown => None,
        }
    }
}

/// TPA (Transition Power Abstraction) solver.
///
/// Solves linear CHC problems by computing power-of-two abstractions
/// of the transition relation.
pub(crate) struct TpaSolver {
    /// The CHC problem to solve
    pub(super) problem: ChcProblem,

    /// Solver configuration
    pub(super) config: TpaConfig,

    /// Extracted transition system
    pub(super) transition_system: Option<TransitionSystem>,

    /// Exact power abstractions: T^{=n} represents exactly 2^n steps
    pub(super) exact_powers: Vec<Option<ChcExpr>>,

    /// Less-than power abstractions: T^{<n} represents less than 2^n steps
    pub(super) less_than_powers: Vec<Option<ChcExpr>>,

    /// Exact reachability query cache keyed by `(from, to)` per power level.
    ///
    /// Ported from Golem's `queryCache` for `reachabilityQueryExact`.
    pub(super) exact_query_cache: Vec<FxHashMap<(ChcExpr, ChcExpr), ExactQueryCacheEntry>>,

    /// Persistent forward-inductive state-invariant conjuncts, accumulated by
    /// the Houdini pass across power levels (analogue of Golem's
    /// `rightInvariants`, but over a single state copy).
    ///
    /// Each surviving conjunct `c(x)` is jointly self-inductive within the
    /// converged set: `∧stateInvariants ∧ Tr(x, x') ⇒ c(x')`.
    pub(super) state_invariants: Vec<ChcExpr>,

    /// Safety explanation recorded when a fixed-point exit fires. Consumed by
    /// `extract_invariant` to emit the certified 1-inductive state invariant.
    pub(super) explanation: Option<SafetyExplanation>,

    /// SMT context for queries
    pub(super) smt: SmtContext,
}

impl Drop for TpaSolver {
    fn drop(&mut self) {
        std::mem::take(&mut self.problem).iterative_drop();
    }
}

impl TpaSolver {
    /// Create a new TPA solver for the given problem.
    pub(crate) fn new(problem: ChcProblem, config: TpaConfig) -> Self {
        let smt = problem.make_smt_context();
        Self {
            problem,
            config,
            transition_system: None,
            exact_powers: Vec::new(),
            less_than_powers: Vec::new(),
            exact_query_cache: Vec::new(),
            state_invariants: Vec::new(),
            explanation: None,
            smt,
        }
    }

    /// Set a pre-computed transition system, skipping extraction in `solve()`.
    ///
    /// Used by the portfolio to run TPA on multi-predicate problems via
    /// SingleLoopTransformation: the transformation produces a TransitionSystem
    /// that cannot be re-derived from the original multi-predicate ChcProblem.
    pub(crate) fn with_transition_system(mut self, ts: TransitionSystem) -> Self {
        self.transition_system = Some(ts);
        self
    }

    /// Return the certified 1-inductive state invariant recorded by the
    /// less-than fixed-point exit, if any.
    ///
    /// The invariant was already verified (`init ⇒ Inv`, `Inv ∧ Tr ⇒ Inv'`,
    /// `Inv ∧ query` UNSAT) before being recorded, so it is emitted directly.
    /// The portfolio's `verify_model_per_rule` gate re-checks it against the
    /// ORIGINAL clauses regardless; `None` yields an empty model that also fails
    /// validation (fail-closed).
    fn extract_invariant(&self) -> Option<ChcExpr> {
        let explanation = self.explanation.as_ref()?;
        Some(explanation.state_invariant.clone())
    }

    /// Check if solver has been cancelled (includes per-engine term memory budget #8600).
    pub(super) fn is_cancelled(&self) -> bool {
        self.config.base.is_cancelled() || self.smt.term_memory_exceeded()
    }

    /// Reuse a fully verified exact reachability query result.
    ///
    /// Golem caches exact `(from, to)` subqueries per level to avoid
    /// re-solving the same midpoint obligations after recursive refinement.
    pub(super) fn lookup_exact_query_cache(
        &self,
        power: u32,
        from: &ChcExpr,
        to: &ChcExpr,
    ) -> Option<ReachResult> {
        self.exact_query_cache
            .get(power as usize)
            .and_then(|cache| cache.get(&(from.clone(), to.clone())).cloned())
            .map(ExactQueryCacheEntry::into_reach_result)
    }

    /// Store a final exact reachability result.
    ///
    /// `Unknown` is skipped so later retries can still benefit from newly
    /// strengthened abstractions or a larger remaining budget.
    pub(super) fn store_exact_query_cache(
        &mut self,
        power: u32,
        from: &ChcExpr,
        to: &ChcExpr,
        result: &ReachResult,
    ) {
        let Some(entry) = ExactQueryCacheEntry::from_reach_result(result) else {
            return;
        };

        let idx = power as usize;
        if self.exact_query_cache.len() <= idx {
            self.exact_query_cache
                .resize_with(idx + 1, FxHashMap::default);
        }
        self.exact_query_cache[idx].insert((from.clone(), to.clone()), entry);
    }
}

/// Flatten an expression into a list of conjuncts for interpolation.
///
/// Uses memoization to avoid exponential blowup on DAGs. TPA builds power
/// abstractions by composition (T^{=k} = T^{=k-1} ∘ T^{=k-1}), which creates
/// DAGs with shared sub-expressions. Without memoization, flattening would
/// treat the DAG as a tree, producing O(2^k) constraints for power k.
///
/// With memoization, each unique Arc is visited once, giving O(power * N)
/// where N is the number of constraints in the base transition.
pub(super) fn flatten_to_constraints(expr: &ChcExpr) -> Vec<ChcExpr> {
    fn flatten_arc_memo(
        expr: &Arc<ChcExpr>,
        visited: &mut FxHashSet<usize>,
        result: &mut Vec<ChcExpr>,
    ) {
        // Use Arc pointer address for memoization - this tracks which
        // sub-expressions we've already processed
        let ptr = Arc::as_ptr(expr) as usize;
        if !visited.insert(ptr) {
            return; // Already visited this exact Arc
        }

        match expr.as_ref() {
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    flatten_arc_memo(arg, visited, result);
                }
            }
            ChcExpr::Bool(true) => {}
            other => {
                result.push(other.clone());
            }
        }
    }

    // Process the root expression - handle the top-level And specially
    // since we receive a &ChcExpr, not an Arc<ChcExpr>
    let mut visited = FxHashSet::default();
    let mut result = Vec::new();

    match expr {
        ChcExpr::Op(ChcOp::And, args) => {
            // For the children, we have Arc<ChcExpr> and can memoize
            for arg in args {
                flatten_arc_memo(arg, &mut visited, &mut result);
            }
        }
        ChcExpr::Bool(true) => {}
        other => {
            result.push(other.clone());
        }
    }
    result
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
#[path = "solver_tests.rs"]
mod tests;
