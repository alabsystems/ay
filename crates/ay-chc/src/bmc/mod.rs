// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded Model Checking (BMC) engine for CHC
//!
//! BMC unrolls the transition relation k times and checks if a bad state is reachable.
//! Unlike PDR which proves safety by finding inductive invariants, BMC is good for
//! finding bugs (SAT cases) by exhaustively searching bounded execution paths.
//!
//! # Algorithm (Level-Based Encoding)
//!
//! Based on Z3's `dl_bmc_engine.cpp` linear BMC class. For each level k:
//!
//! 1. Create level predicates `P#k` = "predicate P is reachable at level k"
//! 2. Create level arguments `P#k_i` = "argument i of P at level k"
//! 3. Create rule indicators `rule:P#k_i` = "rule i derives P at level k"
//!
//! Encoding:
//! - `P#k => rule:P#k_0 ∨ rule:P#k_1 ∨ ...` (at least one rule applies)
//! - `rule:P#k_i => body_constraints ∧ head_equalities ∧ body_predicates#(k-1)`
//! - At level 0, rules with body predicates are disabled
//!
//! # Complementarity with PDR
//!
//! - PDR: Good for proving safety (UNSAT/Safe cases)
//! - BMC: Good for finding bugs (SAT/Unsafe cases)
//!
//! A portfolio approach runs both in parallel, returning whichever finishes first.
//!
//! # Depth Scaling and K-Induction (#7969)
//!
//! For HWMCC benchmarks requiring depths 50-200+:
//! - Adaptive depth with time budgets and EMA-based scaling
//! - K-induction for shallow safety proofs on bounded-safe systems

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::bv_util::bv_mask;
use crate::cancellation::CancellationToken;
use crate::engine_config::ChcEngineConfig;
use crate::engine_result::ChcEngineResult;
use crate::expr::evaluate::evaluate_expr;
use crate::expr::MAX_PREPROCESSING_NODES;
use crate::ground_derivation::{GroundDerivation, GroundDerivationStep};
use crate::pdr::counterexample::{
    Counterexample, CounterexampleStep, DerivationWitness, DerivationWitnessEntry,
};
use crate::pdr::model::InvariantModel;
use crate::pdr::{CexVerificationResult, PdrConfig, PdrSolver};
use crate::smt::executor_adapter::{parse_model_into, quote_symbol, sort_to_smtlib};
use crate::smt::executor_sort_guard::unsupported_executor_expr_reason;
use crate::smt::{IncrementalQueryContext, SmtContext, SmtResult, SmtValue};
use crate::transition_system::TransitionSystem;
use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseHead, HornClause, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_frontend::{sexp::parse_sexp, SExpr};
use std::panic::AssertUnwindSafe;
use std::sync::Arc;

#[cfg(test)]
std::thread_local! {
    static TRACE_OBSERVATION_COMMAND_COUNT: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
}

#[cfg(test)]
fn record_trace_observation_commands_for_tests(count: usize) {
    TRACE_OBSERVATION_COMMAND_COUNT.with(|total| total.set(total.get().saturating_add(count)));
}

#[cfg(test)]
fn reset_trace_observation_commands_for_tests() {
    TRACE_OBSERVATION_COMMAND_COUNT.with(|total| total.set(0));
}

#[cfg(test)]
fn trace_observation_command_count_for_tests() -> usize {
    TRACE_OBSERVATION_COMMAND_COUNT.with(std::cell::Cell::get)
}

/// Exponential moving average smoothing factor for per-depth solve time.
const EMA_ALPHA: f64 = 0.3;

/// When a depth solves faster than this threshold (seconds), the depth is
/// considered "trivially easy" and adaptive stepping may skip ahead (#7969).
const TRIVIAL_DEPTH_THRESHOLD_SECS: f64 = 0.01;

/// Maximum adaptive step size (depth increment). Prevents skipping too far
/// ahead and missing a counterexample at a moderate depth.
const MAX_ADAPTIVE_STEP: usize = 16;

/// Hard work budget for observed values in the candidate-only nested-array
/// abstraction.
///
/// The CHC-COMP25 Solidity array-slice depth-16 window remains below this
/// bound, while 512 leaves prevent an unbounded candidate formula. Hitting the
/// cap remains a completeness-only `Unknown`; every SAT candidate below is
/// still accepted only after exact original-clause replay.
const MAX_NESTED_SELECT_CANDIDATE_ALIASES: usize = 512;

/// Hard work budget for scalar tokens replacing the remaining nested-array
/// state terms in a candidate formula.
///
/// Tokens are much cheaper than observations (they carry no finite cells), but
/// the cap still prevents a malformed depth formula from creating unbounded
/// declarations. Exceeding it only disables this incomplete candidate route.
const MAX_NESTED_ARRAY_CANDIDATE_TOKENS: usize = 4096;

/// Direct nested-array equality edges retained for finite model completion.
const MAX_NESTED_ARRAY_CANDIDATE_EQUALITIES: usize = 8192;

fn log_nested_array_candidate(args: std::fmt::Arguments<'_>) {
    if std::env::var("AY_CHC_BMC_NESTED_DEBUG").is_ok_and(|value| value != "0") {
        safe_eprintln!("BMC nested-array candidate: {args}");
    }
}

/// Minimum consecutive UNSAT depths before attempting k-induction.
const K_INDUCTION_MIN_CONSECUTIVE_UNSAT: usize = 3;
const CONCRETE_SCALAR_BMC_STATE_LIMIT: usize = 10_000;

/// Cap on the RAW assignment space swept by the concrete-scalar env
/// enumerations (`domain^unbound_vars`). The per-state limits above only
/// bound ACCEPTED states, so a sparse constraint over many unbound vars
/// (e.g. an inlined init chain after pc-directed location splitting) would
/// otherwise sweep billions of combinations with no budget check.
const CONCRETE_SCALAR_BMC_ENUM_LIMIT: u128 = 1_000_000;

/// Wall-clock slice for the PRE-executor concrete-scalar pass. Without it the
/// concrete enumeration consumed the whole lane budget and its `Some(Unknown)`
/// early-returned from `solve()`, so the symbolic executor path never ran on
/// cyclic systems (measured: `max_depth=0` after 22s on lustre error-mutants
/// golem closes at depth 1-4 in ~10ms). On slice expiry the pass yields `None`
/// so the dispatch falls through to the executor; the post-executor
/// confirmation calls (exact-acyclic mode) pass `None` for the slice and keep
/// full-budget semantics unchanged.
const CONCRETE_SCALAR_BMC_TIME_SLICE: std::time::Duration = std::time::Duration::from_millis(1500);
const ACYCLIC_REACH_DISTRIBUTION_CAP: usize = 4096;

/// Maximum nonnegative upper bound for replacing `p = x*x` with a finite LIA
/// envelope in the polynomial DAG encoder.  The model-checker-consumer accumulator blocker has
/// `0 <= n <= 100`, so this keeps the generated tangent set bounded while
/// avoiding a nonlinear integer query.
const DAG_BOUNDED_SQUARE_MAX_UPPER: i128 = 256;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct IntInterval {
    lower: Option<i128>,
    upper: Option<i128>,
}

impl IntInterval {
    fn top() -> Self {
        Self {
            lower: None,
            upper: None,
        }
    }

    fn exact(value: i128) -> Self {
        Self {
            lower: Some(value),
            upper: Some(value),
        }
    }

    fn lower(value: i128) -> Self {
        Self {
            lower: Some(value),
            upper: None,
        }
    }

    fn upper(value: i128) -> Self {
        Self {
            lower: None,
            upper: Some(value),
        }
    }

    fn has_bound(self) -> bool {
        self.lower.is_some() || self.upper.is_some()
    }

    fn is_empty(self) -> bool {
        matches!((self.lower, self.upper), (Some(lo), Some(hi)) if lo > hi)
    }

    fn join(self, other: Self) -> Self {
        Self {
            lower: match (self.lower, other.lower) {
                (Some(a), Some(b)) => Some(a.min(b)),
                _ => None,
            },
            upper: match (self.upper, other.upper) {
                (Some(a), Some(b)) => Some(a.max(b)),
                _ => None,
            },
        }
    }

    fn intersect(self, other: Self) -> Self {
        Self {
            lower: match (self.lower, other.lower) {
                (Some(a), Some(b)) => Some(a.max(b)),
                (Some(a), None) | (None, Some(a)) => Some(a),
                (None, None) => None,
            },
            upper: match (self.upper, other.upper) {
                (Some(a), Some(b)) => Some(a.min(b)),
                (Some(a), None) | (None, Some(a)) => Some(a),
                (None, None) => None,
            },
        }
    }

    fn checked_add(self, other: Self) -> Self {
        Self {
            lower: match (self.lower, other.lower) {
                (Some(a), Some(b)) => a.checked_add(b),
                _ => None,
            },
            upper: match (self.upper, other.upper) {
                (Some(a), Some(b)) => a.checked_add(b),
                _ => None,
            },
        }
    }

    fn checked_neg(self) -> Self {
        Self {
            lower: self.upper.and_then(i128::checked_neg),
            upper: self.lower.and_then(i128::checked_neg),
        }
    }

    fn checked_sub(self, other: Self) -> Self {
        self.checked_add(other.checked_neg())
    }

    fn checked_scale(self, factor: i128) -> Self {
        if factor == 0 {
            return Self::exact(0);
        }
        let scaled_lower = self.lower.and_then(|value| value.checked_mul(factor));
        let scaled_upper = self.upper.and_then(|value| value.checked_mul(factor));
        if factor > 0 {
            Self {
                lower: scaled_lower,
                upper: scaled_upper,
            }
        } else {
            Self {
                lower: scaled_upper,
                upper: scaled_lower,
            }
        }
    }

    fn bounded_nonnegative_square_domain(self) -> Option<(i128, i128)> {
        let lower = self.lower?;
        let upper = self.upper?;
        if lower < 0
            || upper < lower
            || upper > DAG_BOUNDED_SQUARE_MAX_UPPER
            || upper - lower > DAG_BOUNDED_SQUARE_MAX_UPPER
        {
            return None;
        }
        Some((lower, upper))
    }
}

#[derive(Debug, Clone)]
struct BoundedSquareDefinition {
    product: ChcVar,
    input: ChcVar,
    square: ChcExpr,
    interval: IntInterval,
}

/// Deadline-expiry marker for the acyclic polynomial-DAG encoding helpers
/// (model-checker-consumer wishlist item 3, budget compliance).
///
/// Kept DISTINCT from an infeasibility answer (`Ok(false)` / `Ok(None)`) so
/// that a budget expiry can never be mistaken for a proof fact: the interval
/// fixpoints' intermediate bounds are joins-in-progress and can be too
/// NARROW — asserting them (`push_acyclic_dag_arg_bound_conjuncts`) or
/// treating an expiry as "clause infeasible" could yield a false Safe. On
/// expiry the lane must bail to `ChcEngineResult::Unknown` with
/// `stats.budget_exhausted = true` (mapped by `classify_bmc_only_unknown` to
/// the Unknown-budget verdict).
#[derive(Debug, Clone, Copy)]
struct DagBudgetExpired;

/// True when `deadline` (if any) has passed. Free-standing variant for the
/// static encoding helpers that have no `&self` (cancellation is polled by
/// the instance-level `BmcSolver::dag_deadline_expired` at outer loops).
fn dag_deadline_passed(deadline: Option<ay_core::time::Instant>) -> bool {
    deadline.is_some_and(|deadline| ay_core::time::Instant::now() >= deadline)
}

/// BMC run statistics for diagnosis and progress tracking (#7969).
#[derive(Debug, Clone, Default)]
pub(crate) struct BmcStats {
    /// Maximum depth reached during the BMC run.
    pub(crate) max_depth_reached: usize,
    /// Number of SAT checks performed.
    pub(crate) num_checks: usize,
    /// Number of k-induction attempts.
    pub(crate) num_k_induction_attempts: usize,
    /// Whether k-induction proved safety.
    pub(crate) k_induction_proved: bool,
    /// The k value at which k-induction succeeded (if any).
    pub(crate) k_induction_k: Option<usize>,
    /// Total wall-clock time.
    pub(crate) total_time_secs: f64,
    /// EMA of per-depth solve time at termination.
    pub(crate) final_ema_secs: f64,
    /// Whether the run was stopped by time budget.
    pub(crate) budget_exhausted: bool,
    /// Whether BMC definitively discharged the bounded search through
    /// `config.max_depth` without budget exhaustion, skipped depths, or
    /// any remaining `unknown` checks.
    pub(crate) exhausted_search: bool,
    /// Whether adaptive stepping was used.
    pub(crate) used_adaptive_stepping: bool,
    /// Whether the per-depth fresh Executor path produced the final result
    /// (#7982/#7983). Mutually exclusive with `used_legacy_fallback`.
    pub(crate) used_executor_path: bool,
    /// Whether the legacy `IncrementalQueryContext` path produced the final
    /// result because the executor path returned `None` (#8822 telemetry).
    pub(crate) used_legacy_fallback: bool,
    /// Acyclic polynomial-DAG lane: number of predicates in the query
    /// dependency cone (item 5 observability; previously verbose-log-only).
    /// 0 when the DAG lane did not run.
    pub(crate) cone_size: usize,
    /// Acyclic polynomial-DAG lane: number of rules compiled over the cone
    /// (item 5 observability). Partial when the lane bailed on budget;
    /// 0 when the DAG lane did not run.
    pub(crate) rule_count: usize,
}

/// BMC solver configuration
#[derive(Debug, Clone)]
pub struct BmcConfig {
    /// Common engine settings (verbose, cancellation).
    pub(crate) base: ChcEngineConfig,
    /// Maximum unrolling depth (number of transitions)
    pub(crate) max_depth: usize,
    /// When true, BMC returns Safe (not Unknown) if max_depth is exhausted
    /// without finding a counterexample. Sound ONLY for acyclic CHC problems
    /// where no execution path can exceed `max_depth` transitions.
    pub(crate) acyclic_safe: bool,
    /// Prefer exact acyclic path expansion even for small predicate graphs.
    ///
    /// This is intended for preprocessed proof lanes where level-style BMC
    /// duplicates large arithmetic encodings and exact branch expansion lets
    /// simplification discharge impossible branches before DPLL(T).
    pub(crate) prefer_exact_acyclic_first: bool,
    /// Per-depth SMT query timeout. When `Some`, each depth's `check_sat` call
    /// is bounded. This prevents BV bitblasting at deep unrolling depths from
    /// consuming the entire portfolio budget on a single query (#5877).
    /// When `None` (default), individual depth queries run unbounded.
    pub(crate) per_depth_timeout: Option<std::time::Duration>,
    /// Overall time budget for the BMC run (#7969). When `Some`, the solver
    /// stops exploring deeper depths once the budget is exhausted.
    pub(crate) time_budget: Option<std::time::Duration>,
    /// Enable k-induction check after consecutive UNSAT depths (#7969).
    /// When enabled, after seeing k consecutive UNSAT depths, BMC attempts
    /// a forward k-induction check to prove safety.
    pub(crate) enable_k_induction: bool,
    /// Enable adaptive depth stepping (#7969).
    ///
    /// When enabled, BMC monitors the EMA of per-depth solve time and skips
    /// ahead when depths are trivially fast (below `TRIVIAL_DEPTH_THRESHOLD_SECS`).
    /// The step size grows exponentially (1, 2, 4, 8, 16) but caps at
    /// `MAX_ADAPTIVE_STEP`. When a depth becomes non-trivial, stepping resets
    /// to 1 to ensure no counterexample is missed.
    ///
    /// Sound because: if we skip from depth k to depth k+s and find SAT at k+s,
    /// we report the counterexample at k+s. If we find UNSAT at k+s, it does NOT
    /// imply UNSAT at k+1..k+s-1 (BMC is monotonically weaker with deeper bounds).
    /// However, for BUG FINDING (the primary BMC use case), skipping to deeper
    /// depths faster is strictly beneficial. For k-induction safety proofs,
    /// the consecutive UNSAT counter is adjusted to account for skipped depths.
    pub(crate) enable_adaptive_stepping: bool,
    /// This BMC run is being used only to refute a separate proof result.
    /// In this mode, an untrusted false `Unsafe` is worse than `Unknown`
    /// because downstream consumers fail closed by demoting valid proofs.
    pub(crate) proof_cross_check: bool,
    /// Inc-16 S1b probe clamp `(min_depth, after)`, applied ONLY in the
    /// single-predicate transition-system incremental lane: once depth
    /// `min_depth` has been verified cex-free AND `after` wall-clock has
    /// elapsed, stop the search and return Unknown (budget-exhausted exit).
    ///
    /// Rationale (front-probe attribution): on the sat lustre residuals the
    /// front BMC probe burns its full ~24%-of-wall budget reaching only
    /// depth 2-12 with no counterexample, starving the invariant routes.
    /// Unsafe single-pred TS instances have shallow cexs (typically depth
    /// ≤ 2 found in <1s), so deep-no-cex + slow depth checks is strong
    /// sat-likely evidence. The clamp is conservative: fast-progress
    /// searches (cheap depth checks — the unsat-likely shape) pass depth
    /// `min_depth` long before `after` elapses and keep their full budget;
    /// the multipred SingleLoop lane (inc-9) is untouched. `None` (default)
    /// = no clamp anywhere; only the front probe sets this.
    pub(crate) ts_probe_clamp: Option<(usize, std::time::Duration)>,
    /// Sweep past spurious / non-strictly-confirmable shallow SATs to reach
    /// the real deeper counterexample (#chc25-bmc-sweep). Correct default for
    /// counterexample hunting. Set `false` for proof CROSS-CHECK roles
    /// ([`BmcConfig::cross_check`]): on a problem another engine just proved
    /// Safe no witness can ever strictly validate, so the sweep's flat fresh
    /// re-solves from k+2..max_depth are pure wasted budget (model-checker-consumer #39
    /// bisect: 0.4s -> 10-15s per cross-check on safe datatype+BV contract
    /// CHCs). With it `false` the first unvalidated SAT reports Unknown
    /// immediately — verdict-identical either way, only faster; the sweep can
    /// only find MORE counterexamples, never change a verdict's direction.
    pub(crate) sweep_past_spurious_sat: bool,
}

impl Default for BmcConfig {
    fn default() -> Self {
        Self {
            base: ChcEngineConfig::default(),
            max_depth: 200,
            acyclic_safe: false,
            prefer_exact_acyclic_first: false,
            per_depth_timeout: None,
            time_budget: None,
            enable_k_induction: false,
            enable_adaptive_stepping: false,
            proof_cross_check: false,
            ts_probe_clamp: None,
            sweep_past_spurious_sat: true,
        }
    }
}

impl BmcConfig {
    /// Create config with verbose and cancellation token (convenience for callers).
    pub fn with_engine_config(
        max_depth: usize,
        verbose: bool,
        cancellation_token: Option<CancellationToken>,
    ) -> Self {
        Self {
            base: ChcEngineConfig {
                verbose,
                cancellation_token,
            },
            max_depth,
            acyclic_safe: false,
            prefer_exact_acyclic_first: false,
            per_depth_timeout: None,
            time_budget: None,
            enable_k_induction: false,
            enable_adaptive_stepping: false,
            proof_cross_check: false,
            ts_probe_clamp: None,
            sweep_past_spurious_sat: true,
        }
    }

    /// Preset for HWMCC benchmarks: deep search with time budget,
    /// k-induction, and adaptive stepping (#7969).
    pub fn hwmcc() -> Self {
        Self {
            base: ChcEngineConfig::default(),
            max_depth: 500,
            acyclic_safe: false,
            prefer_exact_acyclic_first: false,
            per_depth_timeout: None,
            time_budget: Some(std::time::Duration::from_mins(2)),
            enable_k_induction: true,
            enable_adaptive_stepping: true,
            proof_cross_check: false,
            ts_probe_clamp: None,
            sweep_past_spurious_sat: true,
        }
    }

    /// Preset for deep bug finding: aggressive depth search with adaptive
    /// stepping and generous budget. No k-induction (pure counterexample search).
    pub fn deep_bug_finding() -> Self {
        Self {
            base: ChcEngineConfig::default(),
            max_depth: 300,
            acyclic_safe: false,
            prefer_exact_acyclic_first: false,
            per_depth_timeout: None,
            time_budget: Some(std::time::Duration::from_mins(1)),
            enable_k_induction: false,
            enable_adaptive_stepping: true,
            proof_cross_check: false,
            ts_probe_clamp: None,
            sweep_past_spurious_sat: true,
        }
    }

    /// Preset for proof cross-checking (model-checker-consumer use case, #8412).
    ///
    /// Designed for re-checking a CHC PROOF result: run BMC independently to
    /// search for counterexamples that would contradict a claimed PROOF. Uses
    /// a 30-second time budget (matching the adaptive solver's total budget),
    /// depth 200 (sufficient for most program verification counterexamples),
    /// adaptive stepping for fast depth traversal, and no k-induction (pure
    /// counterexample search -- we don't want BMC to also claim Safe).
    ///
    /// Returns `Unsafe` if a counterexample is found (proof contradicted),
    /// or `Unknown` if max depth/time exhausted (proof not contradicted).
    pub fn cross_check() -> Self {
        Self {
            base: ChcEngineConfig::default(),
            max_depth: 200,
            acyclic_safe: false,
            prefer_exact_acyclic_first: false,
            per_depth_timeout: None,
            time_budget: Some(std::time::Duration::from_secs(30)),
            enable_k_induction: false,
            enable_adaptive_stepping: true,
            proof_cross_check: true,
            ts_probe_clamp: None,
            // Cross-check semantics: only a strictly-validated counterexample
            // matters, and the problem was just proved Safe by another engine
            // — no witness can ever validate, so sweeping past the first
            // unvalidated SAT is 100% wasted budget (model-checker-consumer #39/#42).
            sweep_past_spurious_sat: false,
        }
    }

    /// Builder: set the maximum unrolling depth.
    #[must_use]
    pub fn with_max_depth(mut self, max_depth: usize) -> Self {
        self.max_depth = max_depth;
        self
    }

    /// Builder: set the overall time budget for the BMC run.
    ///
    /// When set, BMC stops exploring deeper depths once the budget is exhausted.
    #[must_use]
    pub fn with_time_budget(mut self, budget: std::time::Duration) -> Self {
        self.time_budget = Some(budget);
        self
    }

    /// Builder: set per-depth SMT query timeout.
    ///
    /// Bounds each individual depth's `check_sat` call to prevent BV
    /// bitblasting at deep unrolling depths from consuming the entire budget.
    #[must_use]
    pub fn with_per_depth_timeout(mut self, timeout: std::time::Duration) -> Self {
        self.per_depth_timeout = Some(timeout);
        self
    }

    /// Builder: set verbose output.
    #[must_use]
    pub fn with_verbose(mut self, verbose: bool) -> Self {
        self.base.verbose = verbose;
        self
    }

    /// Builder: enable k-induction check (#7969).
    ///
    /// When enabled, after seeing k consecutive UNSAT depths, BMC attempts
    /// a forward k-induction check to prove safety.
    #[must_use]
    pub fn with_k_induction(mut self, enable: bool) -> Self {
        self.enable_k_induction = enable;
        self
    }

    /// Builder: set acyclic-safe mode.
    ///
    /// When true, BMC returns Safe (not Unknown) if max_depth is exhausted
    /// without finding a counterexample. Sound ONLY for acyclic problems.
    #[must_use]
    pub fn with_acyclic_safe(mut self, acyclic: bool) -> Self {
        self.acyclic_safe = acyclic;
        self
    }

    /// Builder: enable adaptive depth stepping (#7969).
    ///
    /// When enabled, BMC skips ahead when depths are trivially fast,
    /// reaching deeper depths faster for bug finding.
    #[must_use]
    pub fn with_adaptive_stepping(mut self, enable: bool) -> Self {
        self.enable_adaptive_stepping = enable;
        self
    }

    /// Builder: set a cancellation token for cooperative early termination.
    ///
    /// The BMC solver checks this token periodically and returns `Unknown`
    /// if cancellation is requested. Useful when running BMC from a thread
    /// that may need to be stopped (e.g., model-checker-consumer's cross-check timeout).
    #[must_use]
    pub fn with_cancellation(mut self, token: CancellationToken) -> Self {
        self.base.cancellation_token = Some(token);
        self
    }
}

#[derive(Debug, Clone)]
enum BmcTraceValue {
    Var(ChcVar),
    /// A scalar-valued read through one or more nested arrays.
    ///
    /// Keeping the whole path matters for arrays indexed by arrays. The
    /// executor can assign exact values to the scalar leaves while its
    /// printable array model collapses two distinct array-valued indices to
    /// the same default-only `const` array. Reconstructing every observed cell
    /// below preserves the finite part of the model that the BMC witness
    /// actually used.
    ArraySelectPath {
        array: ChcVar,
        indices: Vec<(ChcExpr, ChcSort)>,
        value_sort: ChcSort,
    },
}

impl BmcTraceValue {
    fn sort(&self) -> &ChcSort {
        match self {
            Self::Var(var) => &var.sort,
            Self::ArraySelectPath { value_sort, .. } => value_sort,
        }
    }

    fn term(&self) -> ChcExpr {
        match self {
            Self::Var(var) => ChcExpr::var(var.clone()),
            Self::ArraySelectPath { array, indices, .. } => indices
                .iter()
                .fold(ChcExpr::var(array.clone()), |read, (index, _)| {
                    ChcExpr::select(read, index.clone())
                }),
        }
    }
}

#[derive(Debug, Clone)]
struct BmcArrayObservation {
    array: ChcVar,
    indices: Vec<(ChcExpr, ChcSort)>,
    value: SmtValue,
}

/// One non-nested value read from nested-array state and replaced by a fresh
/// candidate variable.
///
/// The abstraction is used only after the exact Executor returned `unknown`.
/// The value may itself be a flat array. A SAT assignment supplies a finite
/// observation for model completion; it is never itself a verdict. The
/// completed model must still reconstruct and ground-replay a derivation over
/// the original CHC clauses.
#[derive(Debug, Clone)]
struct BmcNestedSelectAlias {
    original: ChcExpr,
    alias: ChcVar,
    array: ChcVar,
    indices: Vec<(ChcExpr, ChcSort)>,
    value_sort: ChcSort,
}

/// One remaining nested-array-valued term replaced by a fresh scalar token.
///
/// This preserves equality/disequality structure needed to select a candidate
/// branch while deliberately forgetting nested-array theory. Token values are
/// never interpreted as arrays and never participate in the final verdict.
#[derive(Debug, Clone)]
struct BmcNestedArrayTokenAlias {
    original: ChcExpr,
    alias: ChcVar,
}

/// Directly equal nested-array variables in the original depth formula.
///
/// The relaxed scalar tokens choose a branch, but exact witness replay still
/// needs finite array values for level-to-rule plumbing. Observations are
/// copied across these components before replay. Collecting equalities from an
/// inactive branch can only over-constrain and reject a candidate; it cannot
/// validate a false derivation because original-clause replay remains final.
#[derive(Debug, Clone)]
struct BmcNestedArrayEquivalence {
    variables: Vec<ChcVar>,
}

#[derive(Debug, Clone)]
struct BmcNestedArrayCandidateFormula {
    prefix_conjuncts: Vec<ChcExpr>,
    query_groups: Vec<Vec<ChcExpr>>,
    select_aliases: Vec<BmcNestedSelectAlias>,
    state_tokens: Vec<BmcNestedArrayTokenAlias>,
    equal_state: Vec<BmcNestedArrayEquivalence>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BmcNestedArrayCandidateAbort {
    NodeBudgetOrDeadline,
    ObservationCap,
    StateTokenCap,
    EqualityCap,
    UnsupportedNestedBoundary,
}

struct BmcNestedArrayTraversalBudget {
    remaining_nodes: usize,
    nodes_until_deadline_check: usize,
    deadline: Option<ay_core::time::Instant>,
}

impl BmcNestedArrayTraversalBudget {
    fn new(remaining_nodes: usize, deadline: Option<ay_core::time::Instant>) -> Self {
        Self {
            remaining_nodes,
            nodes_until_deadline_check: 0,
            deadline,
        }
    }

    fn consume(&mut self) -> Result<(), BmcNestedArrayCandidateAbort> {
        self.remaining_nodes = self
            .remaining_nodes
            .checked_sub(1)
            .ok_or(BmcNestedArrayCandidateAbort::NodeBudgetOrDeadline)?;
        if self.nodes_until_deadline_check == 0 {
            if self
                .deadline
                .is_some_and(|limit| ay_core::time::Instant::now() >= limit)
            {
                return Err(BmcNestedArrayCandidateAbort::NodeBudgetOrDeadline);
            }
            self.nodes_until_deadline_check = 1023;
        } else {
            self.nodes_until_deadline_check -= 1;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ConcreteBmcState {
    predicate: PredicateId,
    values: Vec<i128>,
    incoming_clause: Option<usize>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConcreteConjunctResult {
    Satisfied,
    Progress,
    Unresolved,
    Conflict,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConcreteConstraintResult {
    Satisfied,
    Unsatisfied,
    Unresolved,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ConcreteStateResult {
    State(ConcreteBmcState),
    Infeasible,
    Incomplete,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConcreteMatchResult {
    Matched,
    Mismatch,
    Incomplete,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ConcreteTransitionResult {
    State(ConcreteBmcState),
    NotApplicable,
    Infeasible,
    Incomplete,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConcreteQueryResult {
    Hit,
    Miss,
    Incomplete,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ConcreteBackwardPredecessors {
    Fact,
    States(Vec<ConcreteBmcState>),
}

/// One expanded predicate instance on an exact acyclic path.
#[derive(Debug, Clone)]
struct AcyclicPathNode {
    /// The expanded predicate.
    predicate: PredicateId,
    /// Instantiated argument expressions (over branch variables).
    args: Vec<ChcExpr>,
    /// Clause used to derive this instance (its head is `predicate`).
    clause_idx: usize,
    /// Renaming from the deriving clause's variable names to the fresh
    /// branch variables minted for this expansion.
    clause_var_renaming: FxHashMap<String, ChcExpr>,
}

#[derive(Debug)]
enum AcyclicBranchEnumeration {
    Completed,
    Stopped,
    TimedOut,
    Unsupported,
    /// A SAT branch produced a replay-validated counterexample.
    Unsafe(Box<Counterexample>),
}

/// Outcome of one bounded-BMC replay attempt at a fixed depth in
/// `replay_confirm_unsafe_on_problem`'s iterative-deepening loop.
enum ReplayConfirmAttempt {
    /// Witness found and strictly replay-verified on the problem clauses.
    Confirmed(Counterexample),
    /// No confirmed witness at this depth; deepening may still find one.
    NotConfirmed,
    /// The attempt ran out of time budget; deepening is pointless.
    BudgetExhausted,
    /// Acyclic-exhaustive Safe: every DAG path was covered, so no deeper
    /// bound can find a counterexample. Deepening is pointless.
    DefinitivelySafe,
}

/// BMC solver for CHC problems
pub struct BmcSolver {
    problem: ChcProblem,
    config: BmcConfig,
    stats: std::cell::RefCell<BmcStats>,
    /// Absolute wall-clock deadline computed from `config.time_budget` at the
    /// start of `solve()` (inc-12). Threaded into per-depth executor deadlines
    /// and the legacy per-check timeout so a single depth check can never run
    /// past the overall budget. Previously the budget was only checked BETWEEN
    /// depths, letting front-probe configs overstay their budget 1.5-1.75x
    /// (a depth check started near the end of the budget could still run a
    /// full per-depth timeout more). Timing-only: it never changes a verdict,
    /// it only converts overstayed work into Unknown earlier.
    solve_deadline: std::cell::Cell<Option<ay_core::time::Instant>>,
}

#[derive(Debug)]
enum SingleExecutorOutcome {
    Solved(ChcEngineResult),
    RetryFresh {
        start_depth: usize,
        consecutive_unsat: usize,
    },
}

enum DepthCheckOutcome {
    Solved(ChcEngineResult),
    ContinueUnsat,
    ContinueUnknown,
}

/// Decision for a flat-BMC SAT at some depth under the sweep-past-spurious-SAT
/// policy (#chc25-bmc-sweep).
///
/// Historically a SAT at the FIRST depth where the executor answered `sat`
/// terminated the whole depth sweep, even when that SAT was spurious (e.g. the
/// degenerate flat level-0 array encoding, which the AUFLIA executor answers
/// `sat` on although the level really is UNSAT) or the witness only replays
/// against a preprocessed encoding rather than the original clauses. The real,
/// deeper counterexample was then never reached and the whole problem went
/// Unknown. `Advance` lets the caller keep sweeping instead of giving up.
enum FlatSatOutcome {
    /// A strictly-validated counterexample (its witness replays as Valid on the
    /// original clauses): stop the sweep and report it.
    Confirmed(ChcEngineResult),
    /// The SAT did not yield a validated counterexample at this depth (spurious
    /// executor SAT or an unreconstructable witness). The caller must advance
    /// the sweep to a deeper depth rather than terminating with this shallow
    /// result.
    Advance,
}

impl Drop for BmcSolver {
    fn drop(&mut self) {
        std::mem::take(&mut self.problem).iterative_drop();
    }
}

impl BmcSolver {
    /// Create a new BMC solver
    pub(crate) fn new(problem: ChcProblem, config: BmcConfig) -> Self {
        Self {
            problem,
            config,
            stats: std::cell::RefCell::new(BmcStats::default()),
            solve_deadline: std::cell::Cell::new(None),
        }
    }

    /// Get a snapshot of the current BMC stats (for diagnosis).
    pub(crate) fn stats(&self) -> BmcStats {
        self.stats.borrow().clone()
    }

    /// Update stats with depth and timing info.
    fn record_depth(&self, depth: usize, ema: f64) {
        let mut stats = self.stats.borrow_mut();
        stats.max_depth_reached = depth;
        stats.num_checks += 1;
        stats.final_ema_secs = ema;
    }

    /// Mark that the bounded search up to `max_depth` was fully discharged.
    fn mark_exhausted_search(&self) {
        self.stats.borrow_mut().exhausted_search = true;
    }

    /// Finalize a sequential bounded search that reached `max_depth`.
    ///
    /// `Safe` is only sound when every depth was discharged and no timeout /
    /// SMT `unknown` was seen along the way.
    fn finalize_bounded_search(&self, encountered_unknown: bool) -> ChcEngineResult {
        if encountered_unknown {
            return ChcEngineResult::Unknown;
        }

        self.mark_exhausted_search();
        if self.config.acyclic_safe {
            ChcEngineResult::Safe(InvariantModel::default())
        } else {
            ChcEngineResult::Unknown
        }
    }

    /// Whether any clause body applies the same predicate more than once.
    ///
    /// [`Self::level_arg`] names a level argument by `(predicate, level, index)`
    /// only, so every occurrence of a predicate within one body is equated to
    /// the *same* argument tuple. A body with `N > 1` occurrences of one
    /// predicate is therefore encoded as "all `N` premise tuples are
    /// identical", which is strictly stronger than the clause it stands for.
    ///
    /// The consequence is that per-depth UNSAT becomes vacuous: it can hold
    /// because the collapsed encoding is self-contradictory rather than because
    /// no counterexample exists. Depth exhaustion then proves nothing, so an
    /// `acyclic_safe` run must not report `Safe`.
    ///
    /// [`Self::solve_bounded_tree_refutation`] carries the exact encoding for
    /// these bodies, but is not reachable from [`Self::solve`].
    fn has_repeated_body_predicate(&self) -> bool {
        self.problem.clauses().iter().any(|clause| {
            let body = &clause.body.predicates;
            body.iter().enumerate().any(|(index, (predicate, _))| {
                body[index + 1..]
                    .iter()
                    .any(|(other, _)| other == predicate)
            })
        })
    }

    /// Fail closed on a `Safe` the level-flat encoding cannot justify.
    ///
    /// Applied at every [`Self::solve`] exit so no internal path can publish a
    /// `Safe` that rests on a collapsed body (see
    /// [`Self::has_repeated_body_predicate`]). Without this,
    /// `P(0). P(1). false :- P(x), P(y), x != y.` — plainly unsafe — is
    /// reported `Safe`, because the shared level argument forces `x == y` and
    /// makes every depth UNSAT.
    ///
    /// Only `Safe` is affected. `Unsafe` still rests on its own witness replay
    /// and is untouched.
    fn reject_unrepresentable_safe(&self, result: ChcEngineResult) -> ChcEngineResult {
        if matches!(result, ChcEngineResult::Safe(_)) && self.has_repeated_body_predicate() {
            tracing::warn!(
                "BMC: downgrading Safe to Unknown — a clause body applies one predicate \
                 more than once, which the level-flat encoding collapses into a single \
                 shared argument tuple, so depth exhaustion does not prove safety"
            );
            return ChcEngineResult::Unknown;
        }
        result
    }

    /// Finalize the persistent executor path after it reaches `max_depth`.
    ///
    /// When adaptive stepping skipped any intermediate bounds, `acyclic_safe`
    /// must fall back to the sequential fresh-executor path to discharge those
    /// depths before claiming `Safe`.
    fn finalize_single_executor_completion(
        &self,
        first_unchecked_depth: Option<usize>,
    ) -> SingleExecutorOutcome {
        if let Some(start_depth) = first_unchecked_depth {
            if self.config.acyclic_safe {
                tracing::debug!(
                    "BMC-single: acyclic_safe requires discharging skipped depths, \
                     resuming fresh fallback from {}",
                    start_depth
                );
                return SingleExecutorOutcome::RetryFresh {
                    start_depth,
                    consecutive_unsat: 0,
                };
            }
            return SingleExecutorOutcome::Solved(ChcEngineResult::Unknown);
        }

        SingleExecutorOutcome::Solved(self.finalize_bounded_search(false))
    }

    /// Log final stats at BMC termination.
    fn log_stats(&self, result_name: &str) {
        let stats = self.stats.borrow();
        // #8822: `path` distinguishes the per-depth fresh Executor
        // (#7982/#7983) from the legacy `IncrementalQueryContext` fallback so
        // field diagnostics can tell which code path produced a verdict.
        let path = if stats.used_executor_path {
            "executor"
        } else if stats.used_legacy_fallback {
            "legacy_fallback"
        } else {
            "none"
        };
        tracing::info!(
            "BMC stats: result={} path={} max_depth={} checks={} k_ind_attempts={} \
             k_ind_proved={} ema={:.3}s total={:.3}s budget_exhausted={} \
             exhausted_search={} adaptive={}",
            result_name,
            path,
            stats.max_depth_reached,
            stats.num_checks,
            stats.num_k_induction_attempts,
            stats.k_induction_proved,
            stats.final_ema_secs,
            stats.total_time_secs,
            stats.budget_exhausted,
            stats.exhausted_search,
            stats.used_adaptive_stepping,
        );
    }

    /// Check if overall time budget has been exceeded.
    ///
    /// In addition to the caller-relative `start` check, this consults the
    /// absolute solve deadline set at `solve()` entry (inc-12). Inner lanes
    /// (`solve_per_depth_fresh` confirmation re-solves, `RetryFresh` resumes)
    /// restart their own `start` clocks; without the absolute deadline each
    /// lane transition silently granted the budget again.
    fn is_over_budget(&self, start: &ay_core::time::Instant) -> bool {
        if let Some(budget) = self.config.time_budget {
            if start.elapsed() >= budget {
                return true;
            }
        }
        matches!(self.solve_deadline.get(), Some(d) if ay_core::time::Instant::now() >= d)
    }

    /// Stop signal for the per-SAT-model derivation extraction / validation
    /// loops, which run OUTSIDE any per-depth timer.
    ///
    /// Extraction of one lane is a bounded DFS, but the loops walk up to
    /// `MAX_ROOT_QUERY_CANDIDATES` lanes and `expand_nullary_fail_queries`
    /// inflates the lane count by design (one `(query error)` becomes one query
    /// per `body => error` clause). Both loops therefore poll cancellation and
    /// the absolute solve deadline so a wide expansion cannot spend the whole
    /// budget reshaping witnesses. Stopping early only costs completeness.
    fn model_extraction_should_stop(&self) -> bool {
        self.config.base.is_cancelled()
            || matches!(self.solve_deadline.get(), Some(deadline) if ay_core::time::Instant::now() >= deadline)
    }

    /// Check whether to continue to the next depth based on cancellation and budget.
    fn should_continue_depth(&self, start: &ay_core::time::Instant) -> bool {
        !self.config.base.is_cancelled() && !self.is_over_budget(start)
    }

    /// Solve using bounded model checking.
    ///
    /// Returns `Unsafe` if a counterexample is found within `max_depth` steps,
    /// `Safe` if `acyclic_safe` is set and all depths are exhausted without
    /// counterexample (sound for acyclic problems where paths are bounded),
    /// or `Unknown` otherwise.
    ///
    /// Tries the per-depth fresh Executor path first (#7982/#7983), which uses
    /// ay-dpll's full DPLL(T) executor with cached SMT prefix. Falls back to
    /// the legacy IncrementalQueryContext path if the executor fails.
    pub fn solve(&self) -> ChcEngineResult {
        let overall_start = ay_core::time::Instant::now();
        // inc-12: pin the absolute deadline so per-depth/per-check timeouts
        // are clamped to the remaining overall budget (probe overstay fix).
        self.solve_deadline
            .set(self.config.time_budget.map(|b| overall_start + b));
        // Budget compliance (model-checker-consumer wishlist item 3): install the
        // thread-local SMT deadline for the whole run so SMT-side
        // preprocessing (Tseitin/bit-blast) is clamped too, not just the
        // DPLL(T) search — the BMC-only entry (`engines::solve_bmc_only`)
        // previously had NO thread-local SMT deadline at all (the adaptive
        // front probe installs one at its call site; mirror that here).
        // Nested installs keep the tighter enclosing deadline (see
        // `smt/deadline.rs`), so adaptive callers are unaffected. An expired
        // deadline makes SMT checks return `Unknown`, which every caller
        // treats as a sound give-up signal — never as UNSAT/Safe.
        let _smt_deadline_guard = self
            .config
            .time_budget
            .map(|b| crate::smt::ScopedSmtDeadline::install_until(overall_start + b));

        tracing::debug!(
            "BMC: Starting with max_depth={}, acyclic_safe={}, time_budget={:?}, \
             k_induction={}, adaptive_stepping={}",
            self.config.max_depth,
            self.config.acyclic_safe,
            self.config.time_budget,
            self.config.enable_k_induction,
            self.config.enable_adaptive_stepping,
        );

        if self.problem.predicates().is_empty() {
            return ChcEngineResult::Unknown;
        }
        let queries: Vec<_> = self.problem.queries().collect();
        if queries.is_empty() {
            return ChcEngineResult::Unknown;
        }
        if self.config.base.is_cancelled() {
            let mut stats = self.stats.borrow_mut();
            stats.total_time_secs = overall_start.elapsed().as_secs_f64();
            return ChcEngineResult::Unknown;
        }
        if self.problem.has_complex_query_only_vacuous_safety_shape() {
            if self.config.base.verbose {
                safe_eprintln!(
                    "BMC: complex query-only problem has only unsatisfiable facts; demoting vacuous Safe proof to Unknown"
                );
            }
            let mut stats = self.stats.borrow_mut();
            stats.total_time_secs = overall_start.elapsed().as_secs_f64();
            return ChcEngineResult::Unknown;
        }

        let exact_acyclic_first = self.prefer_exact_acyclic_executor_first();
        if !exact_acyclic_first {
            if let Some(result) = self.solve_concrete_scalar_bmc(
                &queries,
                &overall_start,
                Some(CONCRETE_SCALAR_BMC_TIME_SLICE),
            ) {
                {
                    let mut stats = self.stats.borrow_mut();
                    stats.used_legacy_fallback = true;
                    stats.total_time_secs = overall_start.elapsed().as_secs_f64();
                }
                let result_name = match &result {
                    ChcEngineResult::Safe(_) => "Safe",
                    ChcEngineResult::Unsafe(_) => "Unsafe",
                    ChcEngineResult::Unknown => "Unknown",
                    ChcEngineResult::NotApplicable => "NotApplicable",
                };
                self.log_stats(result_name);
                return self.reject_unrepresentable_safe(result);
            }
        }

        // Per-depth fresh Executor (#7982/#7983): for each depth k, build
        // the complete BMC formula and run one check-sat. Avoids the legacy
        // path's O(n) fresh LiaSolver creation per DPLL(T) iteration.
        //
        // Telemetry (#8822): record which path produced the result so
        // `--verbose`/stats can distinguish executor vs legacy-fallback runs.
        let mut result = match self.solve_via_executor(&queries) {
            Some(result) => {
                self.stats.borrow_mut().used_executor_path = true;
                result
            }
            None => {
                tracing::debug!("BMC: Executor path failed, falling back to legacy");
                self.stats.borrow_mut().used_legacy_fallback = true;
                self.solve_legacy(&queries)
            }
        };

        if exact_acyclic_first
            && matches!(result, ChcEngineResult::Safe(_))
            && !self.stats.borrow().budget_exhausted
            && !self.is_over_budget(&overall_start)
            && !self.config.base.is_cancelled()
        {
            if let Some(concrete_result) =
                self.solve_concrete_scalar_bmc(&queries, &overall_start, None)
            {
                match concrete_result {
                    ChcEngineResult::Unsafe(_) | ChcEngineResult::Unknown => {
                        result = concrete_result;
                        self.stats.borrow_mut().used_legacy_fallback = true;
                    }
                    ChcEngineResult::Safe(_) | ChcEngineResult::NotApplicable => {}
                }
            }
        }

        if exact_acyclic_first
            && matches!(result, ChcEngineResult::Unknown)
            && !self.stats.borrow().budget_exhausted
            && !self.is_over_budget(&overall_start)
            && !self.config.base.is_cancelled()
        {
            if let Some(concrete_result) =
                self.solve_concrete_scalar_bmc(&queries, &overall_start, None)
            {
                result = concrete_result;
                self.stats.borrow_mut().used_legacy_fallback = true;
            }
        }

        if matches!(result, ChcEngineResult::Unsafe(_))
            && self.stats.borrow().used_legacy_fallback
            && self.problem_uses_datatype_features()
        {
            tracing::warn!(
                "BMC: downgrading legacy-fallback Unsafe to Unknown for problem with \
                 datatype features"
            );
            result = ChcEngineResult::Unknown;
        }

        // Record total time and log stats.
        {
            let mut stats = self.stats.borrow_mut();
            stats.total_time_secs = overall_start.elapsed().as_secs_f64();
        }
        let result_name = match &result {
            ChcEngineResult::Safe(_) => "Safe",
            ChcEngineResult::Unsafe(_) => "Unsafe",
            ChcEngineResult::Unknown => "Unknown",
            ChcEngineResult::NotApplicable => "NotApplicable",
        };
        self.log_stats(result_name);

        self.reject_unrepresentable_safe(result)
    }

    fn prefer_exact_acyclic_executor_first(&self) -> bool {
        self.config.acyclic_safe
            && !self.config.enable_adaptive_stepping
            && !self.config.enable_k_induction
            && (self.config.prefer_exact_acyclic_first || self.problem.predicates().len() > 128)
    }

    fn solve_concrete_scalar_bmc(
        &self,
        queries: &[&HornClause],
        overall_start: &ay_core::time::Instant,
        slice: Option<std::time::Duration>,
    ) -> Option<ChcEngineResult> {
        if !self.concrete_scalar_bmc_applicable(queries) {
            return None;
        }

        let mut current: Vec<(ConcreteBmcState, Vec<ConcreteBmcState>)> = Vec::new();
        let mut seen: FxHashSet<(PredicateId, Vec<i128>)> = FxHashSet::default();

        for query in queries {
            match Self::concrete_bodyless_query_result(query) {
                ConcreteQueryResult::Hit => {
                    return Some(self.concrete_trace_result(&[], self.query_clause_index(query)));
                }
                ConcreteQueryResult::Miss => {}
                ConcreteQueryResult::Incomplete => return None,
            }
        }

        for query in queries {
            if let Some(targets) = self.concrete_query_target_states(query) {
                for target in targets {
                    let mut visiting = FxHashSet::default();
                    if let Some(trace) = self.concrete_backward_trace(
                        target,
                        self.config.max_depth + 1,
                        &mut visiting,
                        overall_start,
                        slice,
                    ) {
                        return Some(
                            self.concrete_trace_result(&trace, self.query_clause_index(query)),
                        );
                    }
                }
            }
        }

        for (clause_idx, clause) in self.problem.clauses().iter().enumerate() {
            if !clause.body.predicates.is_empty() {
                continue;
            }
            let states = self.concrete_fact_head_states(clause_idx, clause)?;
            for state in states {
                {
                    if seen.insert((state.predicate, state.values.clone())) {
                        current.push((state.clone(), vec![state]));
                    }
                }
            }
        }

        for depth in 0..=self.config.max_depth {
            if self.config.base.is_cancelled() {
                return Some(ChcEngineResult::Unknown);
            }
            if self.is_over_budget(overall_start) {
                self.stats.borrow_mut().budget_exhausted = true;
                return Some(ChcEngineResult::Unknown);
            }
            if slice.is_some_and(|s| overall_start.elapsed() >= s) {
                // Concrete slice spent without a verdict: yield the remaining
                // lane budget to the symbolic executor path (`None` falls
                // through in `solve()`), instead of burning it all here.
                return None;
            }
            self.record_depth(depth, 0.0);
            for (state, trace) in &current {
                for query in queries {
                    match self.concrete_state_hits_query(state, query) {
                        ConcreteQueryResult::Hit => {
                            return Some(
                                self.concrete_trace_result(trace, self.query_clause_index(query)),
                            );
                        }
                        ConcreteQueryResult::Miss => {}
                        ConcreteQueryResult::Incomplete => return None,
                    }
                }
            }
            if depth == self.config.max_depth || current.is_empty() {
                return self.concrete_exhausted_result();
            }
            if current.len() > CONCRETE_SCALAR_BMC_STATE_LIMIT {
                return None;
            }

            let mut next = Vec::new();
            for (state, trace) in &current {
                for (clause_idx, clause) in self.problem.clauses().iter().enumerate() {
                    match self.concrete_transition_successor(clause_idx, clause, state) {
                        ConcreteTransitionResult::State(next_state) => {
                            if seen.insert((next_state.predicate, next_state.values.clone())) {
                                let mut next_trace = trace.clone();
                                next_trace.push(next_state.clone());
                                next.push((next_state, next_trace));
                                if next.len() > CONCRETE_SCALAR_BMC_STATE_LIMIT {
                                    return None;
                                }
                            }
                        }
                        ConcreteTransitionResult::NotApplicable
                        | ConcreteTransitionResult::Infeasible => {}
                        ConcreteTransitionResult::Incomplete => return None,
                    }
                }
            }
            current = next;
        }

        None
    }

    fn concrete_query_target_states(&self, query: &HornClause) -> Option<Vec<ConcreteBmcState>> {
        let [(body_pred, body_args)] = query.body.predicates.as_slice() else {
            return None;
        };
        let pred = self.problem.get_predicate(*body_pred)?;
        if pred.arg_sorts.len() != body_args.len() {
            return None;
        }
        let mut env = FxHashMap::default();
        if let Some(constraint) = &query.body.constraint {
            if matches!(
                Self::concrete_apply_constraint_result(constraint, &mut env),
                ConcreteConstraintResult::Unsatisfied
            ) {
                return Some(Vec::new());
            }
        }
        let vars = Self::concrete_vars_from_exprs(
            body_args.iter().chain(query.body.constraint.iter()),
            &env,
        );
        if !self.concrete_enumeration_tractable(&vars) {
            return None;
        }
        let mut states = Vec::new();
        self.enumerate_concrete_envs(&vars, 0, &mut env, &mut |env| {
            if let Some(constraint) = &query.body.constraint {
                match Self::concrete_apply_constraint_result(constraint, env) {
                    ConcreteConstraintResult::Satisfied => {}
                    ConcreteConstraintResult::Unsatisfied => return Some(()),
                    ConcreteConstraintResult::Unresolved => return None,
                }
            }
            let values = body_args
                .iter()
                .zip(&pred.arg_sorts)
                .map(|(arg, sort)| Self::concrete_eval_for_sort(arg, sort, env))
                .collect::<Option<Vec<_>>>()?;
            states.push(ConcreteBmcState {
                predicate: *body_pred,
                values,
                incoming_clause: None,
            });
            (states.len() <= CONCRETE_SCALAR_BMC_STATE_LIMIT).then_some(())
        })?;
        Some(states)
    }

    fn concrete_backward_trace(
        &self,
        target: ConcreteBmcState,
        remaining_states: usize,
        visiting: &mut FxHashSet<(PredicateId, Vec<i128>)>,
        overall_start: &ay_core::time::Instant,
        slice: Option<std::time::Duration>,
    ) -> Option<Vec<ConcreteBmcState>> {
        if remaining_states == 0
            || self.config.base.is_cancelled()
            || self.is_over_budget(overall_start)
            || slice.is_some_and(|s| overall_start.elapsed() >= s)
        {
            return None;
        }
        if !visiting.insert((target.predicate, target.values.clone())) {
            return None;
        }

        let result = self.concrete_backward_trace_inner(
            target.clone(),
            remaining_states,
            visiting,
            overall_start,
            slice,
        );
        visiting.remove(&(target.predicate, target.values));
        result
    }

    fn concrete_backward_trace_inner(
        &self,
        target: ConcreteBmcState,
        remaining_states: usize,
        visiting: &mut FxHashSet<(PredicateId, Vec<i128>)>,
        overall_start: &ay_core::time::Instant,
        slice: Option<std::time::Duration>,
    ) -> Option<Vec<ConcreteBmcState>> {
        for (clause_idx, clause) in self.problem.clauses().iter().enumerate() {
            let ClauseHead::Predicate(head_pred, _) = &clause.head else {
                continue;
            };
            if *head_pred != target.predicate {
                continue;
            }

            let mut target_with_clause = target.clone();
            target_with_clause.incoming_clause = Some(clause_idx);

            match self.concrete_backward_predecessors(clause, &target_with_clause)? {
                ConcreteBackwardPredecessors::Fact => {
                    return Some(vec![target_with_clause]);
                }
                ConcreteBackwardPredecessors::States(predecessors) => {
                    if remaining_states <= 1 {
                        continue;
                    }
                    for predecessor in predecessors {
                        if let Some(mut trace) = self.concrete_backward_trace(
                            predecessor,
                            remaining_states - 1,
                            visiting,
                            overall_start,
                            slice,
                        ) {
                            trace.push(target_with_clause);
                            return Some(trace);
                        }
                    }
                }
            }
        }
        None
    }

    fn concrete_backward_predecessors(
        &self,
        clause: &HornClause,
        target: &ConcreteBmcState,
    ) -> Option<ConcreteBackwardPredecessors> {
        let ClauseHead::Predicate(head_pred, head_args) = &clause.head else {
            return None;
        };
        if *head_pred != target.predicate {
            return Some(ConcreteBackwardPredecessors::States(Vec::new()));
        }
        let pred = self.problem.get_predicate(*head_pred)?;
        if pred.arg_sorts.len() != head_args.len() || pred.arg_sorts.len() != target.values.len() {
            return None;
        }

        let mut env = FxHashMap::default();
        for ((arg, sort), value) in head_args
            .iter()
            .zip(&pred.arg_sorts)
            .zip(target.values.iter())
        {
            match sort {
                ChcSort::Bool => {
                    match Self::concrete_match_bool_expr_to_value(arg, *value != 0, &mut env) {
                        ConcreteMatchResult::Matched => {}
                        ConcreteMatchResult::Mismatch => {
                            return Some(ConcreteBackwardPredecessors::States(Vec::new()));
                        }
                        ConcreteMatchResult::Incomplete => return None,
                    }
                }
                _ => match Self::concrete_match_expr_to_value(arg, *value, &mut env) {
                    ConcreteMatchResult::Matched => {}
                    ConcreteMatchResult::Mismatch => {
                        return Some(ConcreteBackwardPredecessors::States(Vec::new()));
                    }
                    ConcreteMatchResult::Incomplete => return None,
                },
            }
        }

        if let Some(constraint) = &clause.body.constraint {
            if matches!(
                Self::concrete_apply_constraint_result(constraint, &mut env),
                ConcreteConstraintResult::Unsatisfied
            ) {
                return Some(ConcreteBackwardPredecessors::States(Vec::new()));
            }
        }

        let vars = Self::concrete_vars_from_exprs(
            clause
                .body
                .predicates
                .iter()
                .flat_map(|(_, args)| args.iter())
                .chain(clause.body.constraint.iter()),
            &env,
        );
        if !self.concrete_enumeration_tractable(&vars) {
            return None;
        }
        let mut predecessors = Vec::new();
        let mut fact_hit = false;
        self.enumerate_concrete_envs(&vars, 0, &mut env, &mut |env| {
            if let Some(constraint) = &clause.body.constraint {
                match Self::concrete_apply_constraint_result(constraint, env) {
                    ConcreteConstraintResult::Satisfied => {}
                    ConcreteConstraintResult::Unsatisfied => return Some(()),
                    ConcreteConstraintResult::Unresolved => return None,
                }
            }

            match clause.body.predicates.as_slice() {
                [] => {
                    fact_hit = true;
                    Some(())
                }
                [(body_pred, body_args)] => {
                    let body_info = self.problem.get_predicate(*body_pred)?;
                    if body_info.arg_sorts.len() != body_args.len() {
                        return None;
                    }
                    let values = body_args
                        .iter()
                        .zip(&body_info.arg_sorts)
                        .map(|(arg, sort)| Self::concrete_eval_for_sort(arg, sort, env))
                        .collect::<Option<Vec<_>>>()?;
                    predecessors.push(ConcreteBmcState {
                        predicate: *body_pred,
                        values,
                        incoming_clause: None,
                    });
                    (predecessors.len() <= CONCRETE_SCALAR_BMC_STATE_LIMIT).then_some(())
                }
                _ => None,
            }
        })?;
        if fact_hit {
            Some(ConcreteBackwardPredecessors::Fact)
        } else {
            Some(ConcreteBackwardPredecessors::States(predecessors))
        }
    }

    fn concrete_vars_from_exprs<'a>(
        exprs: impl Iterator<Item = &'a ChcExpr>,
        env: &FxHashMap<String, i128>,
    ) -> Vec<ChcVar> {
        let mut vars = FxHashMap::default();
        for expr in exprs {
            for var in expr.vars() {
                vars.entry(var.name.clone()).or_insert(var.sort);
            }
        }
        let mut vars: Vec<_> = vars
            .into_iter()
            .filter(|(name, _)| !env.contains_key(name))
            .map(|(name, sort)| ChcVar::new(name, sort))
            .collect();
        vars.sort_by(|a, b| a.name.cmp(&b.name));
        vars
    }

    fn enumerate_concrete_envs<F>(
        &self,
        vars: &[ChcVar],
        idx: usize,
        env: &mut FxHashMap<String, i128>,
        sink: &mut F,
    ) -> Option<()>
    where
        F: FnMut(&mut FxHashMap<String, i128>) -> Option<()>,
    {
        if let Some(var) = vars.get(idx) {
            let domain = self.concrete_fact_seed_domain(&var.sort)?;
            for value in domain {
                env.insert(var.name.clone(), value);
                self.enumerate_concrete_envs(vars, idx + 1, env, sink)?;
            }
            env.remove(&var.name);
            return Some(());
        }
        sink(env)
    }

    fn concrete_fact_head_states(
        &self,
        clause_idx: usize,
        clause: &HornClause,
    ) -> Option<Vec<ConcreteBmcState>> {
        if !clause.body.predicates.is_empty() {
            return None;
        }
        let ClauseHead::Predicate(head_pred, head_args) = &clause.head else {
            return Some(Vec::new());
        };
        let pred = self.problem.get_predicate(*head_pred)?;
        if pred.arg_sorts.len() != head_args.len() {
            return None;
        }

        let mut env = FxHashMap::default();
        if let Some(constraint) = &clause.body.constraint {
            if matches!(
                Self::concrete_apply_constraint_result(constraint, &mut env),
                ConcreteConstraintResult::Unsatisfied
            ) {
                return Some(Vec::new());
            }
        }

        let mut vars = FxHashMap::default();
        for arg in head_args {
            for var in arg.vars() {
                vars.entry(var.name.clone()).or_insert(var.sort);
            }
        }
        if let Some(constraint) = &clause.body.constraint {
            for var in constraint.vars() {
                vars.entry(var.name.clone()).or_insert(var.sort);
            }
        }
        let mut unbound: Vec<_> = vars
            .into_iter()
            .filter(|(name, _)| !env.contains_key(name))
            .map(|(name, sort)| ChcVar::new(name, sort))
            .collect();
        unbound.sort_by(|a, b| a.name.cmp(&b.name));
        if !self.concrete_enumeration_tractable(&unbound) {
            return None;
        }

        let mut states = Vec::new();
        if !self.enumerate_concrete_fact_envs(
            &unbound,
            0,
            &mut env,
            clause,
            *head_pred,
            head_args,
            clause_idx,
            &mut states,
        ) {
            return None;
        }
        Some(states)
    }

    fn enumerate_concrete_fact_envs(
        &self,
        vars: &[ChcVar],
        idx: usize,
        env: &mut FxHashMap<String, i128>,
        clause: &HornClause,
        head_pred: PredicateId,
        head_args: &[ChcExpr],
        clause_idx: usize,
        states: &mut Vec<ConcreteBmcState>,
    ) -> bool {
        if states.len() > CONCRETE_SCALAR_BMC_STATE_LIMIT {
            return false;
        }
        if let Some(var) = vars.get(idx) {
            let Some(domain) = self.concrete_fact_seed_domain(&var.sort) else {
                return false;
            };
            for value in domain {
                env.insert(var.name.clone(), value);
                if !self.enumerate_concrete_fact_envs(
                    vars,
                    idx + 1,
                    env,
                    clause,
                    head_pred,
                    head_args,
                    clause_idx,
                    states,
                ) {
                    env.remove(&var.name);
                    return false;
                }
            }
            env.remove(&var.name);
            return true;
        }

        let mut checked_env = env.clone();
        if let Some(constraint) = &clause.body.constraint {
            match Self::concrete_apply_constraint_result(constraint, &mut checked_env) {
                ConcreteConstraintResult::Satisfied => {}
                ConcreteConstraintResult::Unsatisfied => return true,
                ConcreteConstraintResult::Unresolved => return false,
            }
        }
        let Some(pred) = self.problem.get_predicate(head_pred) else {
            return false;
        };
        let Some(values) = head_args
            .iter()
            .zip(&pred.arg_sorts)
            .map(|(arg, sort)| Self::concrete_eval_for_sort(arg, sort, &checked_env))
            .collect::<Option<Vec<_>>>()
        else {
            return false;
        };
        states.push(ConcreteBmcState {
            predicate: head_pred,
            values,
            incoming_clause: Some(clause_idx),
        });
        states.len() <= CONCRETE_SCALAR_BMC_STATE_LIMIT
    }

    /// Whether sweeping `domain^vars` concrete assignments is tractable.
    /// Bails (false) on unsupported sorts or when the raw combination count
    /// exceeds [`CONCRETE_SCALAR_BMC_ENUM_LIMIT`] — the callers then yield
    /// the concrete lane to the symbolic executor paths.
    fn concrete_enumeration_tractable(&self, vars: &[ChcVar]) -> bool {
        let mut combinations: u128 = 1;
        for var in vars {
            let Some(domain) = self.concrete_fact_seed_domain(&var.sort) else {
                return false;
            };
            combinations = combinations.saturating_mul(domain.len() as u128);
            if combinations > CONCRETE_SCALAR_BMC_ENUM_LIMIT {
                return false;
            }
        }
        true
    }

    fn concrete_fact_seed_domain(&self, sort: &ChcSort) -> Option<Vec<i128>> {
        match sort {
            ChcSort::Bool => Some(vec![0, 1]),
            ChcSort::Int => {
                let bound = (self.config.max_depth as i128 + 1).clamp(1, 32);
                Some((0..=bound).collect())
            }
            _ => None,
        }
    }

    fn concrete_scalar_bmc_applicable(&self, queries: &[&HornClause]) -> bool {
        if self.config.per_depth_timeout.is_some() || self.config.base.is_cancelled() {
            return false;
        }
        if self.problem.has_bv_sorts()
            || self.problem.has_array_sorts()
            || self.problem.has_real_sorts()
            || self.problem.has_datatype_sorts()
        {
            return false;
        }
        if self.problem.predicates().iter().any(|pred| {
            pred.arg_sorts
                .iter()
                .any(|sort| !matches!(sort, ChcSort::Int | ChcSort::Bool))
        }) {
            return false;
        }
        queries.iter().all(|query| query.body.predicates.len() <= 1)
            && self.problem.clauses().iter().all(|clause| {
                clause.body.predicates.len() <= 1
                    && matches!(
                        &clause.head,
                        ClauseHead::Predicate(_, _) | ClauseHead::False
                    )
            })
    }

    fn concrete_trace_result(
        &self,
        trace: &[ConcreteBmcState],
        query_idx: Option<usize>,
    ) -> ChcEngineResult {
        let Some(witness) = self.concrete_derivation_witness(trace, query_idx) else {
            tracing::debug!(
                "BMC: concrete scalar SAT trace has no complete derivation witness; returning Unknown"
            );
            return ChcEngineResult::Unknown;
        };
        self.verified_unsafe_from_witness(witness, "concrete scalar BMC")
    }

    fn concrete_derivation_witness(
        &self,
        trace: &[ConcreteBmcState],
        query_idx: Option<usize>,
    ) -> Option<DerivationWitness> {
        if trace.is_empty() {
            return None;
        }

        let mut entries = Vec::with_capacity(trace.len());
        for (entry_idx, state) in trace.iter().rev().enumerate() {
            let level = trace.len() - 1 - entry_idx;
            let trace_idx = trace.len() - 1 - entry_idx;
            let premise = trace_idx.checked_sub(1).and_then(|idx| trace.get(idx));
            let (instances, state_expr) =
                self.concrete_state_witness(state.predicate, &state.values)?;
            let mut instances = instances;
            if let Some(local_instances) =
                self.concrete_clause_instances_for_trace_entry(state, premise)
            {
                for (name, value) in local_instances {
                    instances.entry(name).or_insert(value);
                }
            }
            let premises = if entry_idx + 1 < trace.len() {
                vec![entry_idx + 1]
            } else {
                Vec::new()
            };
            entries.push(DerivationWitnessEntry {
                predicate: state.predicate,
                level,
                state: state_expr,
                incoming_clause: state.incoming_clause,
                premises,
                instances,
            });
        }

        Some(DerivationWitness {
            query_clause: query_idx,
            root: 0,
            entries,
        })
    }

    fn concrete_clause_instances_for_trace_entry(
        &self,
        state: &ConcreteBmcState,
        premise: Option<&ConcreteBmcState>,
    ) -> Option<FxHashMap<String, SmtValue>> {
        let clause_idx = state.incoming_clause?;
        let clause = self.problem.clauses().get(clause_idx)?;
        let ClauseHead::Predicate(head_pred, head_args) = &clause.head else {
            return None;
        };
        if *head_pred != state.predicate {
            return None;
        }

        let mut env = FxHashMap::default();
        match clause.body.predicates.as_slice() {
            [] => {
                if premise.is_some() {
                    return None;
                }
            }
            [(body_pred, body_args)] => {
                let premise = premise?;
                if premise.predicate != *body_pred {
                    return None;
                }
                let body_info = self.problem.get_predicate(*body_pred)?;
                if body_info.arg_sorts.len() != body_args.len()
                    || body_args.len() != premise.values.len()
                {
                    return None;
                }
                for ((arg, sort), value) in body_args
                    .iter()
                    .zip(&body_info.arg_sorts)
                    .zip(premise.values.iter())
                {
                    Self::concrete_match_expr_for_sort(arg, sort, *value, &mut env)?;
                }
            }
            _ => return None,
        }

        let head_info = self.problem.get_predicate(*head_pred)?;
        if head_info.arg_sorts.len() != head_args.len() || head_args.len() != state.values.len() {
            return None;
        }
        for ((arg, sort), value) in head_args
            .iter()
            .zip(&head_info.arg_sorts)
            .zip(state.values.iter())
        {
            Self::concrete_match_expr_for_sort(arg, sort, *value, &mut env)?;
        }

        let vars = Self::concrete_vars_from_exprs(
            clause
                .body
                .predicates
                .iter()
                .flat_map(|(_, args)| args.iter())
                .chain(clause.body.constraint.iter())
                .chain(head_args.iter()),
            &env,
        );
        if !self.concrete_enumeration_tractable(&vars) {
            return None;
        }
        let mut instances = None;
        self.enumerate_concrete_envs(&vars, 0, &mut env, &mut |env| {
            if let Some(constraint) = &clause.body.constraint {
                match Self::concrete_apply_constraint_result(constraint, env) {
                    ConcreteConstraintResult::Satisfied => {}
                    ConcreteConstraintResult::Unsatisfied => return Some(()),
                    ConcreteConstraintResult::Unresolved => return None,
                }
            }

            let mut local = FxHashMap::default();
            for var in clause.vars() {
                let Some(value) = env.get(&var.name).copied() else {
                    continue;
                };
                let Some(value) = Self::concrete_value_smt(&var.sort, value) else {
                    return None;
                };
                local.insert(var.name, value);
            }
            instances.get_or_insert(local);
            Some(())
        })?;
        Some(instances.unwrap_or_default())
    }

    fn concrete_match_expr_for_sort(
        expr: &ChcExpr,
        sort: &ChcSort,
        value: i128,
        env: &mut FxHashMap<String, i128>,
    ) -> Option<()> {
        let result = match sort {
            ChcSort::Bool => Self::concrete_match_bool_expr_to_value(expr, value != 0, env),
            _ => Self::concrete_match_expr_to_value(expr, value, env),
        };
        matches!(result, ConcreteMatchResult::Matched).then_some(())
    }

    fn concrete_state_witness(
        &self,
        predicate: PredicateId,
        values: &[i128],
    ) -> Option<(FxHashMap<String, SmtValue>, ChcExpr)> {
        let pred = self.problem.get_predicate(predicate)?;
        if pred.arg_sorts.len() != values.len() {
            return None;
        }

        let mut instances = FxHashMap::default();
        let mut conjuncts = Vec::with_capacity(values.len());
        for (idx, (sort, value)) in pred.arg_sorts.iter().zip(values.iter()).enumerate() {
            let var = ChcVar::new(format!("__p{}_a{}", predicate.index(), idx), sort.clone());
            let value_expr = Self::concrete_value_expr(sort, *value)?;
            let value_smt = Self::concrete_value_smt(sort, *value)?;
            instances.insert(var.name.clone(), value_smt);
            conjuncts.push(ChcExpr::eq(ChcExpr::var(var), value_expr));
        }

        Some((instances, ChcExpr::and_all(conjuncts)))
    }

    fn concrete_state_witness_smt(
        &self,
        predicate: PredicateId,
        values: &[SmtValue],
    ) -> Option<(FxHashMap<String, SmtValue>, ChcExpr)> {
        let pred = self.problem.get_predicate(predicate)?;
        if pred.arg_sorts.len() != values.len() {
            return None;
        }

        let mut instances = FxHashMap::default();
        let mut conjuncts = Vec::with_capacity(values.len());
        for (idx, (sort, value)) in pred.arg_sorts.iter().zip(values.iter()).enumerate() {
            let var = ChcVar::new(format!("__p{}_a{}", predicate.index(), idx), sort.clone());
            let value_expr = Self::smt_value_expr_for_sort(value, sort)?;
            instances.insert(var.name.clone(), value.clone());
            conjuncts.push(ChcExpr::eq(ChcExpr::var(var), value_expr));
        }

        Some((instances, ChcExpr::and_all(conjuncts)))
    }

    fn concrete_value_expr(sort: &ChcSort, value: i128) -> Option<ChcExpr> {
        match sort {
            ChcSort::Int => Some(ChcExpr::int(value)),
            ChcSort::Bool => Some(ChcExpr::bool_const(value != 0)),
            ChcSort::BitVec(width) => Some(ChcExpr::BitVec(
                Self::concrete_bitvec_value(*width, value)?,
                *width,
            )),
            _ => None,
        }
    }

    fn smt_value_expr_for_sort(value: &SmtValue, sort: &ChcSort) -> Option<ChcExpr> {
        match (sort, value) {
            (ChcSort::Int, SmtValue::Int(value)) => Some(ChcExpr::int(*value)),
            (ChcSort::Bool, SmtValue::Bool(value)) => Some(ChcExpr::bool_const(*value)),
            (ChcSort::Bool, SmtValue::Int(value)) => Some(ChcExpr::bool_const(*value != 0)),
            (ChcSort::BitVec(width), SmtValue::BitVec(value, value_width))
                if width == value_width =>
            {
                Some(ChcExpr::BitVec(*value, *width))
            }
            (ChcSort::BitVec(width), SmtValue::Int(value)) => Some(ChcExpr::BitVec(
                Self::concrete_bitvec_value(*width, *value)?,
                *width,
            )),
            (ChcSort::Array(index_sort, element_sort), SmtValue::ConstArray(default)) => {
                Some(ChcExpr::ConstArray(
                    index_sort.as_ref().clone(),
                    Arc::new(Self::smt_value_expr_for_sort(
                        default,
                        element_sort.as_ref(),
                    )?),
                ))
            }
            (ChcSort::Array(index_sort, element_sort), SmtValue::ArrayMap { default, entries }) => {
                let mut array = ChcExpr::ConstArray(
                    index_sort.as_ref().clone(),
                    Arc::new(Self::smt_value_expr_for_sort(
                        default,
                        element_sort.as_ref(),
                    )?),
                );
                for (idx, val) in entries {
                    array = ChcExpr::store(
                        array,
                        Self::smt_value_expr_for_sort(idx, index_sort.as_ref())?,
                        Self::smt_value_expr_for_sort(val, element_sort.as_ref())?,
                    );
                }
                Some(array)
            }
            // Datatype constructor value: rebuild the constructor-application
            // expression `(ctor field0 field1 ...)` so the witness state
            // asserts a concrete ADT term. Field sorts come from the
            // constructor definition; a recursive field (self-referential
            // datatype, stored as an `Uninterpreted` back-edge by the parser)
            // is canonicalized back to the full datatype sort so nested
            // constructor values keep their `ChcSort::Datatype` sort. Nullary
            // constructors produce a zero-argument `FuncApp`.
            (ChcSort::Datatype { .. }, SmtValue::Datatype(ctor, fields)) => {
                let mut field_exprs: Vec<Arc<ChcExpr>> = Vec::with_capacity(fields.len());
                for (i, field) in fields.iter().enumerate() {
                    let field_sort = Self::canonical_dt_field_sort(sort, ctor, i)?;
                    field_exprs.push(Arc::new(Self::smt_value_expr_for_sort(field, &field_sort)?));
                }
                Some(ChcExpr::FuncApp(ctor.clone(), sort.clone(), field_exprs))
            }
            (_, SmtValue::Opaque(name)) => {
                Some(ChcExpr::var(ChcVar::new(name.clone(), sort.clone())))
            }
            _ => None,
        }
    }

    /// Field sort of a datatype constructor's `field_index`-th selector, with
    /// the self-referential back-edge canonicalized to the full parent datatype
    /// sort. Mirrors `pdr::verification::canonical_datatype_field_sort`: the
    /// parser stores a recursive field as `Uninterpreted(name)` (or a
    /// same-name `Datatype`) to avoid an infinitely nested sort, so nested
    /// constructor values must be reinterpreted against the full parent sort.
    fn canonical_dt_field_sort(
        parent_sort: &ChcSort,
        ctor: &str,
        field_index: usize,
    ) -> Option<ChcSort> {
        let ChcSort::Datatype {
            name: parent_name,
            constructors,
        } = parent_sort
        else {
            return None;
        };
        let field_sort = constructors
            .iter()
            .find(|c| c.name == ctor)
            .and_then(|c| c.selectors.get(field_index))
            .map(|sel| sel.sort.clone())?;
        match &field_sort {
            ChcSort::Uninterpreted(name) | ChcSort::Datatype { name, .. }
                if name == parent_name =>
            {
                Some(parent_sort.clone())
            }
            _ => Some(field_sort),
        }
    }

    fn concrete_value_smt(sort: &ChcSort, value: i128) -> Option<SmtValue> {
        match sort {
            ChcSort::Int => Some(SmtValue::Int(value)),
            ChcSort::Bool => Some(SmtValue::Bool(value != 0)),
            ChcSort::BitVec(width) => Some(SmtValue::BitVec(
                Self::concrete_bitvec_value(*width, value)?,
                *width,
            )),
            _ => None,
        }
    }

    fn concrete_bitvec_value(width: u32, value: i128) -> Option<u128> {
        let value = u128::try_from(value).ok()?;
        if width < 128 && value > bv_mask(width) {
            return None;
        }
        Some(value & bv_mask(width))
    }

    fn query_clause_index(&self, query: &HornClause) -> Option<usize> {
        self.problem
            .clauses()
            .iter()
            .position(|clause| std::ptr::eq(clause, query))
    }

    fn concrete_exhausted_result(&self) -> Option<ChcEngineResult> {
        if self.config.acyclic_safe
            || self.config.enable_k_induction
            || self.config.time_budget.is_some()
        {
            None
        } else {
            {
                let mut stats = self.stats.borrow_mut();
                stats.max_depth_reached = self.config.max_depth;
                stats.num_checks = stats.num_checks.max(self.config.max_depth + 1);
            }
            self.mark_exhausted_search();
            Some(ChcEngineResult::Unknown)
        }
    }

    fn concrete_head_state(
        &self,
        clause: &HornClause,
        base_env: &FxHashMap<String, i128>,
        incoming_clause: Option<usize>,
    ) -> ConcreteStateResult {
        let ClauseHead::Predicate(head_pred, head_args) = &clause.head else {
            return ConcreteStateResult::Infeasible;
        };
        let mut env = base_env.clone();
        if let Some(constraint) = &clause.body.constraint {
            match Self::concrete_apply_constraint_result(constraint, &mut env) {
                ConcreteConstraintResult::Satisfied => {}
                ConcreteConstraintResult::Unsatisfied => return ConcreteStateResult::Infeasible,
                ConcreteConstraintResult::Unresolved => return ConcreteStateResult::Incomplete,
            }
        }
        let Some(pred) = self.problem.get_predicate(*head_pred) else {
            return ConcreteStateResult::Incomplete;
        };
        if pred.arg_sorts.len() != head_args.len() {
            return ConcreteStateResult::Incomplete;
        }
        let Some(values) = head_args
            .iter()
            .zip(&pred.arg_sorts)
            .map(|(arg, sort)| Self::concrete_eval_for_sort(arg, sort, &env))
            .collect::<Option<Vec<_>>>()
        else {
            return ConcreteStateResult::Incomplete;
        };
        ConcreteStateResult::State(ConcreteBmcState {
            predicate: *head_pred,
            values,
            incoming_clause,
        })
    }

    fn concrete_transition_successor(
        &self,
        clause_idx: usize,
        clause: &HornClause,
        state: &ConcreteBmcState,
    ) -> ConcreteTransitionResult {
        let [(body_pred, body_args)] = clause.body.predicates.as_slice() else {
            return ConcreteTransitionResult::NotApplicable;
        };
        if *body_pred != state.predicate || body_args.len() != state.values.len() {
            return ConcreteTransitionResult::NotApplicable;
        }
        if !matches!(&clause.head, ClauseHead::Predicate(_, _)) {
            return ConcreteTransitionResult::NotApplicable;
        }
        let mut env = FxHashMap::default();
        for (arg, value) in body_args.iter().zip(&state.values) {
            match Self::concrete_match_expr_to_value(arg, *value, &mut env) {
                ConcreteMatchResult::Matched => {}
                ConcreteMatchResult::Mismatch => return ConcreteTransitionResult::NotApplicable,
                ConcreteMatchResult::Incomplete => return ConcreteTransitionResult::Incomplete,
            }
        }
        match self.concrete_head_state(clause, &env, Some(clause_idx)) {
            ConcreteStateResult::State(state) => ConcreteTransitionResult::State(state),
            ConcreteStateResult::Infeasible => ConcreteTransitionResult::Infeasible,
            ConcreteStateResult::Incomplete => ConcreteTransitionResult::Incomplete,
        }
    }

    fn concrete_bodyless_query_result(query: &HornClause) -> ConcreteQueryResult {
        if !query.body.predicates.is_empty() {
            return ConcreteQueryResult::Miss;
        }
        if !matches!(&query.head, ClauseHead::False) {
            return ConcreteQueryResult::Miss;
        }
        let mut env = FxHashMap::default();
        match query.body.constraint.as_ref() {
            Some(constraint) => {
                match Self::concrete_apply_constraint_result(constraint, &mut env) {
                    ConcreteConstraintResult::Satisfied => ConcreteQueryResult::Hit,
                    ConcreteConstraintResult::Unsatisfied => ConcreteQueryResult::Miss,
                    ConcreteConstraintResult::Unresolved => ConcreteQueryResult::Incomplete,
                }
            }
            None => ConcreteQueryResult::Hit,
        }
    }

    fn concrete_state_hits_query(
        &self,
        state: &ConcreteBmcState,
        query: &HornClause,
    ) -> ConcreteQueryResult {
        let [(body_pred, body_args)] = query.body.predicates.as_slice() else {
            return ConcreteQueryResult::Miss;
        };
        if *body_pred != state.predicate || body_args.len() != state.values.len() {
            return ConcreteQueryResult::Miss;
        }
        let mut env = FxHashMap::default();
        for (arg, value) in body_args.iter().zip(&state.values) {
            match Self::concrete_match_expr_to_value(arg, *value, &mut env) {
                ConcreteMatchResult::Matched => {}
                ConcreteMatchResult::Mismatch => return ConcreteQueryResult::Miss,
                ConcreteMatchResult::Incomplete => return ConcreteQueryResult::Incomplete,
            }
        }
        match query.body.constraint.as_ref() {
            Some(constraint) => {
                match Self::concrete_apply_constraint_result(constraint, &mut env) {
                    ConcreteConstraintResult::Satisfied => ConcreteQueryResult::Hit,
                    ConcreteConstraintResult::Unsatisfied => ConcreteQueryResult::Miss,
                    ConcreteConstraintResult::Unresolved => ConcreteQueryResult::Incomplete,
                }
            }
            None => ConcreteQueryResult::Hit,
        }
    }

    fn concrete_apply_constraint_result(
        expr: &ChcExpr,
        env: &mut FxHashMap<String, i128>,
    ) -> ConcreteConstraintResult {
        let conjuncts = expr.collect_conjuncts_nontrivial();
        if conjuncts.iter().any(|c| matches!(c, ChcExpr::Bool(false))) {
            return ConcreteConstraintResult::Unsatisfied;
        }

        for _ in 0..=conjuncts.len() {
            let mut progress = false;
            let mut unresolved = false;
            for conjunct in &conjuncts {
                match Self::concrete_apply_conjunct(conjunct, env) {
                    ConcreteConjunctResult::Conflict => {
                        return ConcreteConstraintResult::Unsatisfied;
                    }
                    ConcreteConjunctResult::Progress => progress = true,
                    ConcreteConjunctResult::Unresolved => unresolved = true,
                    ConcreteConjunctResult::Satisfied => {}
                }
            }
            if !progress {
                return if unresolved {
                    ConcreteConstraintResult::Unresolved
                } else {
                    ConcreteConstraintResult::Satisfied
                };
            }
        }

        let mut saw_unresolved = false;
        for conjunct in &conjuncts {
            match Self::concrete_eval_bool(conjunct, env) {
                Some(true) => {}
                Some(false) => return ConcreteConstraintResult::Unsatisfied,
                None => saw_unresolved = true,
            }
        }
        if saw_unresolved {
            ConcreteConstraintResult::Unresolved
        } else {
            ConcreteConstraintResult::Satisfied
        }
    }

    fn concrete_apply_conjunct(
        expr: &ChcExpr,
        env: &mut FxHashMap<String, i128>,
    ) -> ConcreteConjunctResult {
        if let Some(value) = Self::concrete_eval_bool(expr, env) {
            return if value {
                ConcreteConjunctResult::Satisfied
            } else {
                ConcreteConjunctResult::Conflict
            };
        }

        let ChcExpr::Op(ChcOp::Eq, args) = expr else {
            return ConcreteConjunctResult::Unresolved;
        };
        if args.len() != 2 {
            return ConcreteConjunctResult::Unresolved;
        }
        Self::concrete_bind_equality(args[0].as_ref(), args[1].as_ref(), env)
    }

    fn concrete_bind_equality(
        lhs: &ChcExpr,
        rhs: &ChcExpr,
        env: &mut FxHashMap<String, i128>,
    ) -> ConcreteConjunctResult {
        if let (Some(a), Some(b)) = (
            Self::concrete_eval_bool(lhs, env),
            Self::concrete_eval_bool(rhs, env),
        ) {
            return if a == b {
                ConcreteConjunctResult::Satisfied
            } else {
                ConcreteConjunctResult::Conflict
            };
        }

        if let (Some(a), Some(b)) = (
            Self::concrete_eval_int(lhs, env),
            Self::concrete_eval_int(rhs, env),
        ) {
            return if a == b {
                ConcreteConjunctResult::Satisfied
            } else {
                ConcreteConjunctResult::Conflict
            };
        }

        if Self::concrete_bind_var_to_expr(lhs, rhs, env)
            || Self::concrete_bind_var_to_expr(rhs, lhs, env)
        {
            return ConcreteConjunctResult::Progress;
        }
        ConcreteConjunctResult::Unresolved
    }

    fn concrete_bind_var_to_expr(
        lhs: &ChcExpr,
        rhs: &ChcExpr,
        env: &mut FxHashMap<String, i128>,
    ) -> bool {
        let ChcExpr::Var(var) = lhs else {
            return false;
        };
        if env.contains_key(&var.name) {
            return false;
        }
        match var.sort {
            ChcSort::Bool => {
                let Some(value) = Self::concrete_eval_bool(rhs, env) else {
                    return false;
                };
                env.insert(var.name.clone(), i128::from(value));
                true
            }
            _ => {
                let Some(value) = Self::concrete_eval_int(rhs, env) else {
                    return false;
                };
                env.insert(var.name.clone(), value);
                true
            }
        }
    }

    fn concrete_match_expr_to_value(
        expr: &ChcExpr,
        value: i128,
        env: &mut FxHashMap<String, i128>,
    ) -> ConcreteMatchResult {
        match expr {
            ChcExpr::Var(var) => match env.get(&var.name) {
                Some(current) if *current == value => ConcreteMatchResult::Matched,
                Some(_) => ConcreteMatchResult::Mismatch,
                None => {
                    env.insert(var.name.clone(), value);
                    ConcreteMatchResult::Matched
                }
            },
            other => match Self::concrete_eval_int(other, env)
                .or_else(|| Self::concrete_eval_bool(other, env).map(i128::from))
            {
                Some(current) if current == value => ConcreteMatchResult::Matched,
                Some(_) => ConcreteMatchResult::Mismatch,
                None => ConcreteMatchResult::Incomplete,
            },
        }
    }

    fn concrete_match_bool_expr_to_value(
        expr: &ChcExpr,
        value: bool,
        env: &mut FxHashMap<String, i128>,
    ) -> ConcreteMatchResult {
        match expr {
            ChcExpr::Var(var) if var.sort == ChcSort::Bool => match env.get(&var.name) {
                Some(current) if (*current != 0) == value => ConcreteMatchResult::Matched,
                Some(_) => ConcreteMatchResult::Mismatch,
                None => {
                    env.insert(var.name.clone(), i128::from(value));
                    ConcreteMatchResult::Matched
                }
            },
            other => match Self::concrete_eval_bool(other, env) {
                Some(current) if current == value => ConcreteMatchResult::Matched,
                Some(_) => ConcreteMatchResult::Mismatch,
                None => ConcreteMatchResult::Incomplete,
            },
        }
    }

    fn concrete_eval_for_sort(
        expr: &ChcExpr,
        sort: &ChcSort,
        env: &FxHashMap<String, i128>,
    ) -> Option<i128> {
        match sort {
            ChcSort::Bool => Self::concrete_eval_bool(expr, env).map(i128::from),
            ChcSort::Int => Self::concrete_eval_int(expr, env),
            _ => None,
        }
    }

    fn concrete_eval_int(expr: &ChcExpr, env: &FxHashMap<String, i128>) -> Option<i128> {
        match expr {
            ChcExpr::Int(value) => Some(*value),
            ChcExpr::Bool(value) => Some(i128::from(*value)),
            ChcExpr::Var(var) => env.get(&var.name).copied(),
            ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                Self::concrete_eval_int(args[0].as_ref(), env)?.checked_neg()
            }
            ChcExpr::Op(ChcOp::Add, args) => {
                let mut sum = 0i128;
                for arg in args {
                    sum = sum.checked_add(Self::concrete_eval_int(arg.as_ref(), env)?)?;
                }
                Some(sum)
            }
            ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
                let mut iter = args.iter();
                let first = Self::concrete_eval_int(iter.next()?.as_ref(), env)?;
                if args.len() == 1 {
                    return first.checked_neg();
                }
                let mut value = first;
                for arg in iter {
                    value = value.checked_sub(Self::concrete_eval_int(arg.as_ref(), env)?)?;
                }
                Some(value)
            }
            ChcExpr::Op(ChcOp::Mul, args) => {
                let mut product = 1i128;
                for arg in args {
                    product = product.checked_mul(Self::concrete_eval_int(arg.as_ref(), env)?)?;
                }
                Some(product)
            }
            ChcExpr::Op(ChcOp::Div, args) if args.len() == 2 => {
                let rhs = Self::concrete_eval_int(args[1].as_ref(), env)?;
                if rhs == 0 {
                    return None;
                }
                Self::concrete_eval_int(args[0].as_ref(), env)?.checked_div(rhs)
            }
            ChcExpr::Op(ChcOp::Mod, args) if args.len() == 2 => {
                let rhs = Self::concrete_eval_int(args[1].as_ref(), env)?;
                if rhs == 0 {
                    return None;
                }
                Self::concrete_eval_int(args[0].as_ref(), env)?.checked_rem(rhs)
            }
            ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
                if Self::concrete_eval_bool(args[0].as_ref(), env)? {
                    Self::concrete_eval_int(args[1].as_ref(), env)
                } else {
                    Self::concrete_eval_int(args[2].as_ref(), env)
                }
            }
            _ => expr.as_i128(),
        }
    }

    fn concrete_eval_bool(expr: &ChcExpr, env: &FxHashMap<String, i128>) -> Option<bool> {
        match expr {
            ChcExpr::Bool(value) => Some(*value),
            ChcExpr::Var(var) if var.sort == ChcSort::Bool => {
                env.get(&var.name).map(|value| *value != 0)
            }
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                Some(!Self::concrete_eval_bool(args[0].as_ref(), env)?)
            }
            ChcExpr::Op(ChcOp::And, args) => {
                let mut saw_unknown = false;
                for arg in args {
                    match Self::concrete_eval_bool(arg.as_ref(), env) {
                        Some(false) => return Some(false),
                        Some(true) => {}
                        None => saw_unknown = true,
                    }
                }
                (!saw_unknown).then_some(true)
            }
            ChcExpr::Op(ChcOp::Or, args) => {
                let mut saw_unknown = false;
                for arg in args {
                    match Self::concrete_eval_bool(arg.as_ref(), env) {
                        Some(true) => return Some(true),
                        Some(false) => {}
                        None => saw_unknown = true,
                    }
                }
                (!saw_unknown).then_some(false)
            }
            ChcExpr::Op(ChcOp::Implies, args) if args.len() == 2 => {
                let lhs = Self::concrete_eval_bool(args[0].as_ref(), env)?;
                if lhs {
                    Self::concrete_eval_bool(args[1].as_ref(), env)
                } else {
                    Some(true)
                }
            }
            ChcExpr::Op(op, args)
                if matches!(
                    op,
                    ChcOp::Eq | ChcOp::Ne | ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge
                ) && args.len() == 2 =>
            {
                if matches!(op, ChcOp::Eq | ChcOp::Ne) {
                    if let (Some(lhs), Some(rhs)) = (
                        Self::concrete_eval_bool(args[0].as_ref(), env),
                        Self::concrete_eval_bool(args[1].as_ref(), env),
                    ) {
                        return Some(match op {
                            ChcOp::Eq => lhs == rhs,
                            ChcOp::Ne => lhs != rhs,
                            _ => unreachable!(),
                        });
                    }
                }
                let lhs = Self::concrete_eval_int(args[0].as_ref(), env)?;
                let rhs = Self::concrete_eval_int(args[1].as_ref(), env)?;
                Some(match op {
                    ChcOp::Eq => lhs == rhs,
                    ChcOp::Ne => lhs != rhs,
                    ChcOp::Lt => lhs < rhs,
                    ChcOp::Le => lhs <= rhs,
                    ChcOp::Gt => lhs > rhs,
                    ChcOp::Ge => lhs >= rhs,
                    _ => unreachable!(),
                })
            }
            ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
                if Self::concrete_eval_bool(args[0].as_ref(), env)? {
                    Self::concrete_eval_bool(args[1].as_ref(), env)
                } else {
                    Self::concrete_eval_bool(args[2].as_ref(), env)
                }
            }
            _ => None,
        }
    }

    /// Whether BMC's encoded problem contains Array features.
    fn problem_uses_array_features(&self) -> bool {
        self.problem
            .predicates()
            .iter()
            .any(|pred| pred.arg_sorts.iter().any(Self::sort_contains_array))
            || self
                .problem
                .clauses()
                .iter()
                .any(Self::clause_uses_array_features)
    }

    fn clause_uses_array_features(clause: &HornClause) -> bool {
        clause
            .body
            .constraint
            .as_ref()
            .is_some_and(Self::expr_uses_array_features)
            || clause
                .body
                .predicates
                .iter()
                .flat_map(|(_, args)| args)
                .any(Self::expr_uses_array_features)
            || match &clause.head {
                ClauseHead::Predicate(_, args) => args.iter().any(Self::expr_uses_array_features),
                ClauseHead::False => false,
            }
    }

    fn expr_uses_array_features(expr: &ChcExpr) -> bool {
        match expr {
            ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _) => {
                false
            }
            ChcExpr::Var(var) => Self::sort_contains_array(&var.sort),
            ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) => {
                args.iter().any(|arg| Self::expr_uses_array_features(arg))
            }
            ChcExpr::FuncApp(_, sort, args) => {
                Self::sort_contains_array(sort)
                    || args.iter().any(|arg| Self::expr_uses_array_features(arg))
            }
            ChcExpr::ConstArrayMarker(_) | ChcExpr::ConstArray(_, _) => true,
            ChcExpr::IsTesterMarker(_) => false,
        }
    }

    fn sort_contains_array(sort: &ChcSort) -> bool {
        match sort {
            ChcSort::Array(_, _) => true,
            ChcSort::Datatype { .. }
            | ChcSort::Bool
            | ChcSort::Int
            | ChcSort::Real
            | ChcSort::BitVec(_)
            | ChcSort::Uninterpreted(_) => false,
        }
    }

    /// Whether BMC's encoded problem contains datatype features that make the
    /// legacy fallback's SAT/Unsafe result unsafe to trust.
    fn problem_uses_datatype_features(&self) -> bool {
        if self.problem.datatype_defs().is_empty() {
            return false;
        }

        if self.problem.has_datatype_sorts() {
            return true;
        }

        let datatype_function_names = self.datatype_function_names();
        self.problem
            .clauses()
            .iter()
            .any(|clause| Self::clause_uses_datatype_features(clause, &datatype_function_names))
    }

    fn datatype_function_names(&self) -> FxHashSet<String> {
        let mut names = FxHashSet::default();
        for constructors in self.problem.datatype_defs().values() {
            for (ctor_name, selectors) in constructors {
                names.insert(ctor_name.clone());
                names.insert(format!("is-{ctor_name}"));
                for (selector_name, _) in selectors {
                    names.insert(selector_name.clone());
                }
            }
        }
        names
    }

    fn clause_uses_datatype_features(
        clause: &HornClause,
        datatype_function_names: &FxHashSet<String>,
    ) -> bool {
        clause
            .body
            .constraint
            .as_ref()
            .is_some_and(|expr| Self::expr_uses_datatype_features(expr, datatype_function_names))
            || clause
                .body
                .predicates
                .iter()
                .flat_map(|(_, args)| args)
                .any(|expr| Self::expr_uses_datatype_features(expr, datatype_function_names))
            || match &clause.head {
                ClauseHead::Predicate(_, args) => args
                    .iter()
                    .any(|expr| Self::expr_uses_datatype_features(expr, datatype_function_names)),
                ClauseHead::False => false,
            }
    }

    fn expr_uses_datatype_features(
        expr: &ChcExpr,
        datatype_function_names: &FxHashSet<String>,
    ) -> bool {
        match expr {
            ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _) => {
                false
            }
            ChcExpr::Var(var) => Self::sort_contains_datatype(&var.sort),
            ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) => args
                .iter()
                .any(|arg| Self::expr_uses_datatype_features(arg, datatype_function_names)),
            ChcExpr::FuncApp(name, sort, args) => {
                datatype_function_names.contains(name)
                    || Self::sort_contains_datatype(sort)
                    || args
                        .iter()
                        .any(|arg| Self::expr_uses_datatype_features(arg, datatype_function_names))
            }
            ChcExpr::ConstArrayMarker(sort) => Self::sort_contains_datatype(sort),
            ChcExpr::IsTesterMarker(_) => true,
            ChcExpr::ConstArray(key_sort, value) => {
                // ChcExpr::ConstArray stores the key sort; the element sort is
                // recovered from the VALUE expression itself, so a
                // datatype-valued array constant is detected precisely. The
                // previous blanket `!datatype_function_names.is_empty()` guard
                // armed on ANY declared datatype, which made every model-checker-consumer
                // system (they always declare Option/Tuple/... even when
                // unused) downgrade legacy-fallback Unsafe verdicts to
                // Unknown despite purely scalar const arrays.
                Self::sort_contains_datatype(key_sort)
                    || Self::sort_contains_datatype(&value.sort())
                    || Self::expr_uses_datatype_features(value, datatype_function_names)
            }
        }
    }

    fn sort_contains_datatype(sort: &ChcSort) -> bool {
        match sort {
            ChcSort::Datatype { .. } => true,
            ChcSort::Array(key, value) => {
                Self::sort_contains_datatype(key) || Self::sort_contains_datatype(value)
            }
            _ => false,
        }
    }

    fn executor_conjuncts_supported(&self, conjuncts: &[ChcExpr], phase: &str) -> bool {
        if let Some(reason) = conjuncts.iter().find_map(unsupported_executor_expr_reason) {
            tracing::debug!(
                "BMC-exec: unsupported SMT-LIB executor term in {phase}: {reason}; returning Unknown"
            );
            return false;
        }
        true
    }

    /// Legacy BMC solve using IncrementalQueryContext (non-incremental theory solver).
    ///
    /// Kept as fallback when the executor path fails.
    fn solve_legacy(&self, queries: &[&HornClause]) -> ChcEngineResult {
        let start = ay_core::time::Instant::now();
        let mut smt = self.problem.make_smt_context();
        let mut inc = IncrementalQueryContext::new();
        let mut encountered_unknown = false;

        // Assert level 0 constraints as background (fact clauses only).
        let mut level0_conjuncts = Vec::new();
        self.compile_level(0, &mut level0_conjuncts);
        let level0_formula = ChcExpr::and_all(level0_conjuncts.iter().cloned());
        inc.assert_background(&level0_formula, &mut smt);
        inc.finalize_background(&smt);

        for k in 0..=self.config.max_depth {
            if !self.should_continue_depth(&start) {
                tracing::debug!("BMC: Stopped at depth {} (cancelled or over budget)", k);
                return ChcEngineResult::Unknown;
            }
            match self.check_depth(k, queries, &mut smt, &mut inc) {
                DepthCheckOutcome::Solved(result) => return result,
                DepthCheckOutcome::ContinueUnsat => {}
                DepthCheckOutcome::ContinueUnknown => encountered_unknown = true,
            }
        }

        tracing::debug!(
            "BMC: Bounded search through depth {} completed (encountered_unknown={})",
            self.config.max_depth,
            encountered_unknown
        );
        self.finalize_bounded_search(encountered_unknown)
    }

    /// Check a single BMC depth. Returns `Some(result)` if a counterexample is
    /// found or an early-exit condition is met, `None` to continue to next depth.
    fn check_depth(
        &self,
        k: usize,
        queries: &[&HornClause],
        smt: &mut SmtContext,
        inc: &mut IncrementalQueryContext,
    ) -> DepthCheckOutcome {
        tracing::debug!("BMC: Checking depth k={}", k);
        // For k > 0, add level k constraints permanently.
        if k > 0 {
            let mut level_conjuncts = Vec::new();
            self.compile_level(k, &mut level_conjuncts);
            let level_formula = ChcExpr::and_all(level_conjuncts.iter().cloned());
            inc.assert_permanent(&level_formula, smt);
            inc.refresh_var_map(smt);
        }

        // Build query at level k (temporary — different for each depth).
        // Several queries are alternatives, not a conjunction: see
        // `compile_query_groups`.
        let query_groups = self.compile_query_groups(queries, k);
        let query_formula = Self::query_groups_formula(&query_groups);

        // inc-12: per-check timeout = min(per-depth timeout, remaining overall
        // budget). Previously the overall budget was only checked between
        // depths, so the final check could overstay by a full per-depth slot.
        let remaining_overall = self
            .solve_deadline
            .get()
            .map(|d| d.saturating_duration_since(ay_core::time::Instant::now()));
        let timeout = match (self.config.per_depth_timeout, remaining_overall) {
            (Some(t), Some(r)) => Some(t.min(r)),
            (t, r) => t.or(r),
        };
        // #5877: Set per-depth timeout on the SmtContext so BV bitblasting
        // and Tseitin encoding can check it (not just the DPLL(T) solve loop).
        let _timeout_guard = timeout.map(|t| smt.scoped_check_timeout(Some(t)));
        let result = inc.check_sat_incremental(std::slice::from_ref(&query_formula), smt, timeout);

        match result {
            crate::smt::IncrementalCheckResult::Sat(model) => {
                tracing::debug!("BMC: Found counterexample at depth {}", k);
                DepthCheckOutcome::Solved(self.bmc_sat_result(&model, k, queries))
            }
            crate::smt::IncrementalCheckResult::Unsat => {
                tracing::debug!("BMC: No counterexample at depth {}", k);
                DepthCheckOutcome::ContinueUnsat
            }
            crate::smt::IncrementalCheckResult::Unknown => {
                tracing::debug!("BMC: SMT unknown at depth {}, continuing", k);
                DepthCheckOutcome::ContinueUnknown
            }
        }
    }

    // ============ Per-Depth Fresh Executor (#7982/#7983) ============

    /// Solve BMC via per-depth fresh Executor with cached SMT prefix.
    ///
    /// For each depth k, builds the complete BMC formula (levels 0..k + query
    /// at k) and runs ONE check-sat on a fresh Executor. The SMT prefix
    /// (declarations + level assertions) is cached and extended incrementally
    /// to avoid O(k^2) re-serialization.
    ///
    /// Returns `Some(result)` on success, `None` if the executor path fails
    /// (caller falls back to legacy path).
    fn solve_via_executor(&self, queries: &[&HornClause]) -> Option<ChcEngineResult> {
        if self.prefer_exact_acyclic_executor_first() {
            if self
                .config
                .per_depth_timeout
                .is_some_and(|timeout| timeout.is_zero())
            {
                self.stats.borrow_mut().budget_exhausted = true;
                return Some(ChcEngineResult::Unknown);
            }
            return Some(self.solve_acyclic_safe_first_once(queries, self.config.max_depth));
        }

        if self.config.acyclic_safe
            && !self.config.enable_adaptive_stepping
            && !self.config.enable_k_induction
        {
            if self
                .config
                .per_depth_timeout
                .is_some_and(|timeout| timeout.is_zero())
            {
                self.stats.borrow_mut().budget_exhausted = true;
                return Some(ChcEngineResult::Unknown);
            }
            return self.solve_acyclic_exhaustive_once(queries, self.config.max_depth);
        }

        if self.config.proof_cross_check && self.problem_uses_array_features() {
            tracing::debug!("BMC: proof cross-check on Array CHC uses per-depth fresh executor");
            return self.solve_per_depth_fresh(queries, self.config.max_depth, 0, 0, false);
        }

        // Phase 3 Layer B: golem-style persistent-executor BMC for
        // single-predicate transition systems (the lustre shape). One
        // executor lives across all depth checks; each depth only adds the
        // new transition/query formulas (push query / check / pop / assert
        // transition) instead of rebuilding the full setup per check.
        match self.solve_transition_system_incremental(queries, self.config.max_depth) {
            Some(SingleExecutorOutcome::Solved(result)) => return Some(result),
            Some(SingleExecutorOutcome::RetryFresh {
                start_depth,
                consecutive_unsat,
            }) => {
                return self.solve_per_depth_fresh(
                    queries,
                    self.config.max_depth,
                    start_depth,
                    consecutive_unsat,
                    false,
                );
            }
            None => {}
        }

        // inc-9: golem-style persistent-executor BMC for linear MULTIPRED
        // problems via the SingleLoop location encoding. Replaces the
        // 4-6s/check fresh flat path for the common case; SAT depths are
        // still confirmed on the flat path (witness + replay validation).
        match self.solve_multipred_ts_incremental(queries, self.config.max_depth) {
            Some(SingleExecutorOutcome::Solved(result)) => return Some(result),
            Some(SingleExecutorOutcome::RetryFresh {
                start_depth,
                consecutive_unsat,
            }) => {
                return self.solve_per_depth_fresh(
                    queries,
                    self.config.max_depth,
                    start_depth,
                    consecutive_unsat,
                    false,
                );
            }
            None => {}
        }

        // Try single-executor with activation literals first (#7983).
        // Transitions accumulate as permanent assertions; only the per-depth
        // query uses an activation literal via check-sat-assuming. Learned
        // clauses from depth k persist and help solve depth k+1.
        match self.solve_single_executor(queries, self.config.max_depth) {
            Some(SingleExecutorOutcome::Solved(result)) => return Some(result),
            Some(SingleExecutorOutcome::RetryFresh {
                start_depth,
                consecutive_unsat,
            }) => {
                return self.solve_per_depth_fresh(
                    queries,
                    self.config.max_depth,
                    start_depth,
                    consecutive_unsat,
                    false,
                );
            }
            None => {}
        }
        // Fallback: per-depth fresh executor (always works, but discards
        // learned clauses between depths).
        self.solve_per_depth_fresh(queries, self.config.max_depth, 0, 0, false)
    }

    /// Safe-first exact acyclic DAG reachability for large native BV+array CHCs.
    ///
    /// This expands the predicate DAG directly, freshening clause variables per
    /// expansion occurrence, then asks the native CHC SMT context whether any
    /// query is reachable. Only UNSAT is trusted as a safety proof; SAT/Unknown
    /// are deliberately reported as Unknown.
    fn solve_acyclic_safe_first_once(
        &self,
        queries: &[&HornClause],
        max_depth: usize,
    ) -> ChcEngineResult {
        let start = ay_core::time::Instant::now();
        if self
            .config
            .per_depth_timeout
            .is_some_and(|timeout| timeout.is_zero())
        {
            self.stats.borrow_mut().budget_exhausted = true;
            return ChcEngineResult::Unknown;
        }
        let timeout = self
            .config
            .time_budget
            .unwrap_or_else(|| std::time::Duration::from_secs(30));
        let deadline = self.lane_deadline(start, timeout);
        let defs_by_head = self.defs_by_head();
        const ACYCLIC_EXACT_PATH_EXPANSION_CAP: u128 = 1024;
        const ACYCLIC_EXACT_PATH_POLYNOMIAL_PREFERRED_MIN: u128 = 1024;
        if let Some(path_count) =
            self.capped_query_path_count(queries, &defs_by_head, ACYCLIC_EXACT_PATH_EXPANSION_CAP)
        {
            if path_count >= ACYCLIC_EXACT_PATH_POLYNOMIAL_PREFERRED_MIN {
                if self.config.base.verbose {
                    safe_eprintln!(
                        "BMC: exact acyclic path expansion has {path_count} paths; using polynomial DAG encoding"
                    );
                }
                return self.solve_acyclic_polynomial_dag_once(queries, max_depth, &defs_by_head);
            }
            if self.config.base.verbose {
                safe_eprintln!("BMC: exact acyclic path expansion within cap (paths={path_count})");
            }
        } else {
            if self.config.base.verbose {
                safe_eprintln!(
                    "BMC: exact acyclic path expansion over cap; using polynomial DAG encoding"
                );
            }
            return self.solve_acyclic_polynomial_dag_once(queries, max_depth, &defs_by_head);
        }

        if let Some(result) = self.solve_acyclic_safe_first_streaming_once(
            queries,
            max_depth,
            &defs_by_head,
            deadline,
            start,
        ) {
            return result;
        }

        let mut visiting = FxHashSet::default();
        let mut fresh_counter = 0usize;
        let mut query_disjuncts = Vec::new();

        for query in queries {
            if ay_core::time::Instant::now() >= deadline || self.config.base.is_cancelled() {
                self.stats.borrow_mut().budget_exhausted = true;
                return ChcEngineResult::Unknown;
            }

            let mut branch_conjuncts = vec![Vec::new()];
            for (pred, args) in &query.body.predicates {
                let Some(reach) = self.acyclic_reach_instance(
                    *pred,
                    args,
                    &defs_by_head,
                    &mut visiting,
                    &mut fresh_counter,
                    deadline,
                ) else {
                    return ChcEngineResult::Unknown;
                };
                let alternatives = Self::collect_disjuncts_nontrivial(reach);
                if alternatives.is_empty() {
                    branch_conjuncts.clear();
                    break;
                }
                let combined_len = branch_conjuncts.len().saturating_mul(alternatives.len());
                if combined_len > ACYCLIC_REACH_DISTRIBUTION_CAP {
                    if self.config.base.verbose {
                        safe_eprintln!(
                            "BMC: exact acyclic query branch distribution over cap; \
                             using polynomial DAG encoding"
                        );
                    }
                    return self.solve_acyclic_polynomial_dag_once(
                        queries,
                        max_depth,
                        &defs_by_head,
                    );
                }
                let old = std::mem::take(&mut branch_conjuncts);
                let mut expanded = Vec::with_capacity(combined_len);
                for conjuncts in old {
                    for alternative in &alternatives {
                        let mut branch = conjuncts.clone();
                        branch.push(alternative.clone());
                        expanded.push(branch);
                    }
                }
                branch_conjuncts = expanded;
            }
            if let Some(constraint) = &query.body.constraint {
                for conjuncts in &mut branch_conjuncts {
                    conjuncts.push(constraint.clone());
                }
            }
            for mut conjuncts in branch_conjuncts {
                if conjuncts.is_empty() {
                    conjuncts.push(ChcExpr::Bool(true));
                }
                query_disjuncts.push(Self::simplify_exact_acyclic_conjuncts(conjuncts));
            }
        }

        if query_disjuncts.is_empty() {
            self.mark_acyclic_exhaustive_stats(max_depth, start.elapsed().as_secs_f64());
            return ChcEngineResult::Safe(InvariantModel::default());
        }

        let query = if query_disjuncts.len() == 1 {
            query_disjuncts.remove(0)
        } else {
            ChcExpr::or_all(query_disjuncts)
        };
        if matches!(query, ChcExpr::Bool(false)) {
            self.mark_acyclic_exhaustive_stats(max_depth, start.elapsed().as_secs_f64());
            return ChcEngineResult::Safe(InvariantModel::default());
        }
        let branch_disjuncts = Self::collect_disjuncts_nontrivial(query.clone());
        if self.config.base.verbose {
            safe_eprintln!(
                "BMC: exact acyclic path expansion produced {} branch formulas",
                branch_disjuncts.len()
            );
        }
        if branch_disjuncts.len() > 1
            && self.executor_conjuncts_supported(&branch_disjuncts, "acyclic-safe-first-branches")
        {
            if self.config.base.verbose {
                safe_eprintln!(
                    "BMC: exact acyclic path expansion checking {} branches independently",
                    branch_disjuncts.len()
                );
            }
            for (branch_idx, branch) in branch_disjuncts.into_iter().enumerate() {
                if ay_core::time::Instant::now() >= deadline || self.config.base.is_cancelled() {
                    self.stats.borrow_mut().budget_exhausted = true;
                    return ChcEngineResult::Unknown;
                }
                let remaining = deadline.saturating_duration_since(ay_core::time::Instant::now());
                if remaining.is_zero() {
                    self.stats.borrow_mut().budget_exhausted = true;
                    return ChcEngineResult::Unknown;
                }
                let mut smt = self.problem.make_smt_context();
                match smt.check_sat_with_executor_fallback_timeout(&branch, remaining) {
                    result if result.is_unsat() => {}
                    SmtResult::Sat(model) => {
                        // A SAT branch of the EXACT acyclic expansion is a
                        // counterexample candidate. Only a replay-validated
                        // witness is trusted as Unsafe (bmc_sat_result routes
                        // through verified_unsafe_from_witness); extraction or
                        // replay failure keeps the historical Unknown.
                        let verdict = self.bmc_sat_result(&model, max_depth, queries);
                        if matches!(verdict, ChcEngineResult::Unsafe(_)) {
                            self.record_depth(max_depth, start.elapsed().as_secs_f64());
                            return verdict;
                        }
                        if self.config.base.verbose {
                            safe_eprintln!(
                                "BMC: exact acyclic branch {branch_idx} was not discharged"
                            );
                        }
                        self.record_depth(max_depth, start.elapsed().as_secs_f64());
                        return ChcEngineResult::Unknown;
                    }
                    SmtResult::Unknown => {
                        if self.config.base.verbose {
                            safe_eprintln!(
                                "BMC: exact acyclic branch {branch_idx} was not discharged"
                            );
                        }
                        self.record_depth(max_depth, start.elapsed().as_secs_f64());
                        return ChcEngineResult::Unknown;
                    }
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {
                        unreachable!("handled by is_unsat guard")
                    }
                }
            }
            self.mark_acyclic_exhaustive_stats(max_depth, start.elapsed().as_secs_f64());
            return ChcEngineResult::Safe(InvariantModel::default());
        }
        if !self.executor_conjuncts_supported(std::slice::from_ref(&query), "acyclic-safe-first") {
            if self.config.base.verbose {
                safe_eprintln!(
                    "BMC: exact acyclic path expansion unsupported after simplification; \
                     using polynomial DAG encoding"
                );
            }
            return self.solve_acyclic_polynomial_dag_once(queries, max_depth, &defs_by_head);
        }

        let remaining = deadline.saturating_duration_since(ay_core::time::Instant::now());
        if remaining.is_zero() {
            self.stats.borrow_mut().budget_exhausted = true;
            return ChcEngineResult::Unknown;
        }

        let mut smt = self.problem.make_smt_context();
        match smt.check_sat_with_executor_fallback_timeout(&query, remaining) {
            result if result.is_unsat() => {
                self.mark_acyclic_exhaustive_stats(max_depth, start.elapsed().as_secs_f64());
                ChcEngineResult::Safe(InvariantModel::default())
            }
            SmtResult::Sat(model) => {
                // Counterexample candidate — trusted only after replay
                // validation (see the branch-wise arm above).
                let verdict = self.bmc_sat_result(&model, max_depth, queries);
                self.record_depth(max_depth, start.elapsed().as_secs_f64());
                if matches!(verdict, ChcEngineResult::Unsafe(_)) {
                    verdict
                } else {
                    ChcEngineResult::Unknown
                }
            }
            SmtResult::Unknown => {
                self.record_depth(max_depth, start.elapsed().as_secs_f64());
                ChcEngineResult::Unknown
            }
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                unreachable!("handled by is_unsat guard")
            }
        }
    }

    fn solve_acyclic_safe_first_streaming_once(
        &self,
        queries: &[&HornClause],
        max_depth: usize,
        defs_by_head: &FxHashMap<PredicateId, Vec<usize>>,
        deadline: ay_core::time::Instant,
        start: ay_core::time::Instant,
    ) -> Option<ChcEngineResult> {
        if self.config.base.verbose {
            safe_eprintln!(
                "BMC: exact acyclic path expansion checking branches independently (streaming)"
            );
        }

        let mut visiting = FxHashSet::default();
        let mut fresh_counter = 0usize;
        let mut branch = Vec::new();
        let mut path: Vec<AcyclicPathNode> = Vec::new();
        let mut checked_branches = 0usize;
        let mut stop_result = None;

        for query in queries {
            let query_clause_idx = self.query_clause_index(query);
            let mark = branch.len();
            if let Some(constraint) = &query.body.constraint {
                branch.push(constraint.clone());
            }

            let outcome = match query.body.predicates.as_slice() {
                [] => {
                    checked_branches += 1;
                    self.check_acyclic_safe_first_branch(
                        &branch,
                        checked_branches - 1,
                        max_depth,
                        deadline,
                        start,
                        queries,
                        &[],
                        query_clause_idx,
                    )
                }
                [(pred, args)] => self.enumerate_acyclic_linear_pred_branches(
                    *pred,
                    args,
                    defs_by_head,
                    &mut visiting,
                    &mut fresh_counter,
                    deadline,
                    &mut branch,
                    &mut path,
                    &mut |branch, path| {
                        checked_branches += 1;
                        match self.check_acyclic_safe_first_branch(
                            branch,
                            checked_branches - 1,
                            max_depth,
                            deadline,
                            start,
                            queries,
                            path,
                            query_clause_idx,
                        ) {
                            AcyclicBranchEnumeration::Completed => true,
                            other => {
                                stop_result = Some(other);
                                false
                            }
                        }
                    },
                ),
                _ => AcyclicBranchEnumeration::Unsupported,
            };
            branch.truncate(mark);

            // A sink-initiated stop surfaces as `Stopped` from the
            // enumeration (the sink returns false); the REAL verdict (e.g.
            // Unsafe with a replay-validated counterexample) is parked in
            // `stop_result` and must take precedence.
            let outcome = stop_result.take().unwrap_or(outcome);
            match outcome {
                AcyclicBranchEnumeration::Completed => {}
                AcyclicBranchEnumeration::Unsafe(cex) => {
                    return Some(ChcEngineResult::Unsafe(*cex));
                }
                AcyclicBranchEnumeration::Stopped => {
                    self.record_depth(max_depth, start.elapsed().as_secs_f64());
                    return Some(ChcEngineResult::Unknown);
                }
                AcyclicBranchEnumeration::TimedOut => {
                    self.stats.borrow_mut().budget_exhausted = true;
                    return Some(ChcEngineResult::Unknown);
                }
                AcyclicBranchEnumeration::Unsupported => return None,
            }
        }

        if self.config.base.verbose {
            safe_eprintln!(
                "BMC: exact acyclic path expansion discharged {checked_branches} branches independently"
            );
        }
        self.mark_acyclic_exhaustive_stats(max_depth, start.elapsed().as_secs_f64());
        Some(ChcEngineResult::Safe(InvariantModel::default()))
    }

    fn check_acyclic_safe_first_branch(
        &self,
        raw_conjuncts: &[ChcExpr],
        branch_idx: usize,
        max_depth: usize,
        deadline: ay_core::time::Instant,
        start: ay_core::time::Instant,
        queries: &[&HornClause],
        path: &[AcyclicPathNode],
        query_clause: Option<usize>,
    ) -> AcyclicBranchEnumeration {
        if ay_core::time::Instant::now() >= deadline || self.config.base.is_cancelled() {
            return AcyclicBranchEnumeration::TimedOut;
        }
        let mut ordered_conjuncts = raw_conjuncts.to_vec();
        ordered_conjuncts.reverse();
        let branch = Self::simplify_exact_acyclic_conjuncts(ordered_conjuncts);
        if matches!(branch, ChcExpr::Bool(false)) {
            return AcyclicBranchEnumeration::Completed;
        }
        if !self.executor_conjuncts_supported(
            std::slice::from_ref(&branch),
            "acyclic-safe-first-branch",
        ) {
            return AcyclicBranchEnumeration::Unsupported;
        }

        let remaining = deadline.saturating_duration_since(ay_core::time::Instant::now());
        if remaining.is_zero() {
            return AcyclicBranchEnumeration::TimedOut;
        }
        let mut smt = self.problem.make_smt_context();
        match smt.check_sat_with_executor_fallback_timeout(&branch, remaining) {
            result if result.is_unsat() => AcyclicBranchEnumeration::Completed,
            SmtResult::Sat(model) => {
                // Counterexample candidate — trusted only after replay
                // validation. First try the path-aware witness built from the
                // recorded predicate instances (the branch model's per-path
                // fresh naming is invisible to the level-based extraction),
                // then fall back to the level-based bmc_sat_result.
                if !path.is_empty() {
                    // Pre-solve simplification substitutes variables away, so
                    // the model omits them. Re-check the UNSIMPLIFIED branch
                    // (already known SAT — one cheap query on the rare unsafe
                    // path) to obtain values for every original variable, then
                    // forward-propagate the branch equalities for any residue.
                    let mut ordered_conjuncts = raw_conjuncts.to_vec();
                    ordered_conjuncts.reverse();
                    let full_model = {
                        let remaining =
                            deadline.saturating_duration_since(ay_core::time::Instant::now());
                        if remaining.is_zero() {
                            model.clone()
                        } else {
                            let mut smt = self.problem.make_smt_context();
                            match smt.check_sat_with_executor_fallback_timeout(
                                &ChcExpr::and_all(ordered_conjuncts),
                                remaining,
                            ) {
                                SmtResult::Sat(full) => full,
                                _ => model.clone(),
                            }
                        }
                    };
                    // Variables referenced only by the witness path (predicate
                    // arg expressions and clause_var_renaming values) must be
                    // grounded too: the simplifier eliminates don't-cares from
                    // the solved branch, so they are invisible in
                    // raw_conjuncts yet needed to evaluate witness args.
                    let witness_vars: Vec<ChcVar> = path
                        .iter()
                        .flat_map(|node| {
                            node.args
                                .iter()
                                .chain(node.clause_var_renaming.values())
                                .flat_map(|expr| expr.vars())
                        })
                        .collect();
                    let extended = Self::extend_model_via_branch_equalities(
                        raw_conjuncts,
                        &witness_vars,
                        &full_model,
                    );
                    if let Some(witness) =
                        self.acyclic_branch_witness(&extended, path, query_clause)
                    {
                        if let ChcEngineResult::Unsafe(cex) =
                            self.verified_unsafe_from_witness(witness, "exact-acyclic branch")
                        {
                            self.record_depth(max_depth, start.elapsed().as_secs_f64());
                            return AcyclicBranchEnumeration::Unsafe(Box::new(cex));
                        }
                    }
                }
                if let ChcEngineResult::Unsafe(cex) =
                    self.bmc_sat_result(&model, max_depth, queries)
                {
                    self.record_depth(max_depth, start.elapsed().as_secs_f64());
                    return AcyclicBranchEnumeration::Unsafe(Box::new(cex));
                }
                if self.config.base.verbose {
                    safe_eprintln!("BMC: exact acyclic branch {branch_idx} was not discharged");
                }
                self.record_depth(max_depth, start.elapsed().as_secs_f64());
                AcyclicBranchEnumeration::Stopped
            }
            SmtResult::Unknown => {
                if self.config.base.verbose {
                    safe_eprintln!("BMC: exact acyclic branch {branch_idx} was not discharged");
                }
                self.record_depth(max_depth, start.elapsed().as_secs_f64());
                AcyclicBranchEnumeration::Stopped
            }
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                unreachable!("handled by is_unsat guard")
            }
        }
    }

    fn enumerate_acyclic_linear_pred_branches<F>(
        &self,
        pred: PredicateId,
        args: &[ChcExpr],
        defs_by_head: &FxHashMap<PredicateId, Vec<usize>>,
        visiting: &mut FxHashSet<PredicateId>,
        fresh_counter: &mut usize,
        deadline: ay_core::time::Instant,
        branch: &mut Vec<ChcExpr>,
        path: &mut Vec<AcyclicPathNode>,
        sink: &mut F,
    ) -> AcyclicBranchEnumeration
    where
        F: FnMut(&[ChcExpr], &[AcyclicPathNode]) -> bool,
    {
        if ay_core::time::Instant::now() >= deadline || self.config.base.is_cancelled() {
            return AcyclicBranchEnumeration::TimedOut;
        }
        if !visiting.insert(pred) {
            return AcyclicBranchEnumeration::Unsupported;
        }

        let outcome = (|| {
            for clause_idx in defs_by_head.get(&pred).into_iter().flatten() {
                if ay_core::time::Instant::now() >= deadline || self.config.base.is_cancelled() {
                    return AcyclicBranchEnumeration::TimedOut;
                }
                let clause = &self.problem.clauses()[*clause_idx];
                if clause.body.predicates.len() > 1 {
                    return AcyclicBranchEnumeration::Unsupported;
                }

                let expansion_id = *fresh_counter;
                *fresh_counter += 1;
                let mut subst = FxHashMap::default();
                for (var_idx, var) in clause.vars().into_iter().enumerate() {
                    subst.insert(
                        var.name.clone(),
                        ChcExpr::Var(ChcVar::new(
                            format!("__bmc_dag_e{expansion_id}_v{var_idx}"),
                            var.sort,
                        )),
                    );
                }

                let mark = branch.len();
                let path_mark = path.len();
                path.push(AcyclicPathNode {
                    predicate: pred,
                    args: args.to_vec(),
                    clause_idx: *clause_idx,
                    clause_var_renaming: subst.clone(),
                });
                if let ClauseHead::Predicate(_, head_args) = &clause.head {
                    for (arg_idx, head_arg) in head_args.iter().enumerate() {
                        let Some(actual) = args.get(arg_idx) else {
                            branch.truncate(mark);
                            path.truncate(path_mark);
                            return AcyclicBranchEnumeration::Unsupported;
                        };
                        branch.push(ChcExpr::eq(
                            actual.clone(),
                            head_arg.substitute_name_map(&subst),
                        ));
                    }
                }
                if let Some(constraint) = &clause.body.constraint {
                    branch.push(constraint.substitute_name_map(&subst));
                }

                let clause_outcome = match clause.body.predicates.as_slice() {
                    [] => {
                        if sink(branch, path) {
                            AcyclicBranchEnumeration::Completed
                        } else {
                            AcyclicBranchEnumeration::Stopped
                        }
                    }
                    [(body_pred, body_args)] => {
                        let instantiated_args: Vec<_> = body_args
                            .iter()
                            .map(|arg| arg.substitute_name_map(&subst))
                            .collect();
                        self.enumerate_acyclic_linear_pred_branches(
                            *body_pred,
                            &instantiated_args,
                            defs_by_head,
                            visiting,
                            fresh_counter,
                            deadline,
                            branch,
                            path,
                            sink,
                        )
                    }
                    _ => AcyclicBranchEnumeration::Unsupported,
                };
                branch.truncate(mark);
                path.truncate(path_mark);
                match clause_outcome {
                    AcyclicBranchEnumeration::Completed => {}
                    other => return other,
                }
            }
            AcyclicBranchEnumeration::Completed
        })();

        visiting.remove(&pred);
        outcome
    }

    fn defs_by_head(&self) -> FxHashMap<PredicateId, Vec<usize>> {
        let mut defs: FxHashMap<PredicateId, Vec<usize>> = FxHashMap::default();
        for (idx, clause) in self.problem.clauses().iter().enumerate() {
            if let ClauseHead::Predicate(pred, _) = &clause.head {
                defs.entry(*pred).or_default().push(idx);
            }
        }
        defs
    }

    fn capped_query_path_count(
        &self,
        queries: &[&HornClause],
        defs_by_head: &FxHashMap<PredicateId, Vec<usize>>,
        cap: u128,
    ) -> Option<u128> {
        let mut memo = FxHashMap::default();
        let mut total = 0u128;
        for query in queries {
            let mut product = 1u128;
            for (pred, _) in &query.body.predicates {
                let mut visiting = FxHashSet::default();
                let count = self.capped_pred_path_count(
                    *pred,
                    defs_by_head,
                    &mut memo,
                    &mut visiting,
                    cap,
                )?;
                product = product.checked_mul(count)?;
                if product > cap {
                    return None;
                }
            }
            total = total.checked_add(product)?;
            if total > cap {
                return None;
            }
        }
        Some(total)
    }

    fn capped_pred_path_count(
        &self,
        pred: PredicateId,
        defs_by_head: &FxHashMap<PredicateId, Vec<usize>>,
        memo: &mut FxHashMap<PredicateId, u128>,
        visiting: &mut FxHashSet<PredicateId>,
        cap: u128,
    ) -> Option<u128> {
        if let Some(count) = memo.get(&pred) {
            return Some(*count);
        }

        if !visiting.insert(pred) {
            return None;
        }

        let result = (|| {
            let mut total = 0u128;
            for clause_idx in defs_by_head.get(&pred).into_iter().flatten() {
                let clause = &self.problem.clauses()[*clause_idx];
                let mut product = 1u128;
                for (body_pred, _) in &clause.body.predicates {
                    let count =
                        self.capped_pred_path_count(*body_pred, defs_by_head, memo, visiting, cap)?;
                    product = product.checked_mul(count)?;
                    if product > cap {
                        return None;
                    }
                }
                total = total.checked_add(product)?;
                if total > cap {
                    return None;
                }
            }
            Some(total)
        })();

        visiting.remove(&pred);
        if let Some(total) = result {
            memo.insert(pred, total);
        }
        result
    }

    /// Lane-entry deadline: `timeout` from lane entry, clamped to the
    /// solve-wide deadline pinned by `solve()` (model-checker-consumer wishlist item 3).
    /// Without the clamp a lane entered late in the budget restarts the
    /// clock and can overstay the whole solve budget by a full lane timeout.
    fn lane_deadline(
        &self,
        start: ay_core::time::Instant,
        timeout: std::time::Duration,
    ) -> ay_core::time::Instant {
        let deadline = start + timeout;
        match self.solve_deadline.get() {
            Some(solve_deadline) => deadline.min(solve_deadline),
            None => deadline,
        }
    }

    /// Deadline/cancellation poll for the acyclic encoding loops.
    fn dag_deadline_expired(&self, deadline: ay_core::time::Instant) -> bool {
        ay_core::time::Instant::now() >= deadline || self.config.base.is_cancelled()
    }

    fn solve_acyclic_polynomial_dag_once(
        &self,
        queries: &[&HornClause],
        max_depth: usize,
        defs_by_head: &FxHashMap<PredicateId, Vec<usize>>,
    ) -> ChcEngineResult {
        let start = ay_core::time::Instant::now();
        let timeout = self
            .config
            .time_budget
            .unwrap_or_else(|| std::time::Duration::from_secs(30));
        let deadline = self.lane_deadline(start, timeout);

        let cone = self.query_dependency_cone(queries, defs_by_head);
        if cone.is_empty() && queries.is_empty() {
            self.mark_acyclic_exhaustive_stats(max_depth, start.elapsed().as_secs_f64());
            return ChcEngineResult::Safe(InvariantModel::default());
        }

        if !self.acyclic_dag_encoding_applicable(queries, &cone, defs_by_head) {
            if self.config.base.verbose {
                safe_eprintln!(
                    "BMC: polynomial DAG encoding skipped for non-linear acyclic cone; using level-flat fallback"
                );
            }
            return self.solve_acyclic_cone_level_flat_once(queries, max_depth, defs_by_head);
        }

        let mut conjuncts = Vec::new();
        let mut rule_count = 0usize;
        let mut ordered_cone: Vec<_> = cone.iter().copied().collect();
        ordered_cone.sort_by_key(|pred| pred.index());
        // Item 5 observability: record the cone size up front so even a
        // budget bail-out reports how heavy the encoding was.
        self.stats.borrow_mut().cone_size = ordered_cone.len();
        // Budget compliance (model-checker-consumer wishlist item 3): both inference
        // fixpoints and the per-clause compile loops below poll `deadline`
        // internally and bail — previously they ran unbounded (>150s on
        // coroutine-shaped cones) before the first per-pred poll fired.
        let Ok(dag_arg_constants) =
            self.infer_acyclic_dag_arg_constants(&ordered_cone, defs_by_head, deadline)
        else {
            self.stats.borrow_mut().budget_exhausted = true;
            return ChcEngineResult::Unknown;
        };
        let Ok(dag_arg_bounds) = self.infer_acyclic_dag_arg_bounds(
            &ordered_cone,
            defs_by_head,
            &dag_arg_constants,
            deadline,
        ) else {
            self.stats.borrow_mut().budget_exhausted = true;
            return ChcEngineResult::Unknown;
        };
        let bound_conjunct_count = self.push_acyclic_dag_arg_bound_conjuncts(
            &ordered_cone,
            &dag_arg_bounds,
            &dag_arg_constants,
            &mut conjuncts,
        );
        let mut linearized_square_count = 0usize;
        let mut interval_simplified_count = 0usize;

        for pred in &ordered_cone {
            if self.dag_deadline_expired(deadline) {
                let mut stats = self.stats.borrow_mut();
                stats.budget_exhausted = true;
                stats.rule_count = rule_count;
                return ChcEngineResult::Unknown;
            }
            let Some(pred_rule_count) = self.compile_acyclic_dag_definition(
                *pred,
                defs_by_head,
                &dag_arg_constants,
                &dag_arg_bounds,
                &mut linearized_square_count,
                &mut interval_simplified_count,
                &mut conjuncts,
                deadline,
            ) else {
                self.stats.borrow_mut().budget_exhausted = true;
                return ChcEngineResult::Unknown;
            };
            rule_count += pred_rule_count;
        }
        // Item 5 observability: rule count over the cone (previously only in
        // the verbose "exact polynomial DAG encoding" log line).
        self.stats.borrow_mut().rule_count = rule_count;

        let mut query_disjuncts = Vec::new();
        for (query_idx, query) in queries.iter().enumerate() {
            if self.dag_deadline_expired(deadline) {
                self.stats.borrow_mut().budget_exhausted = true;
                return ChcEngineResult::Unknown;
            }
            let Some(query_disjunct) = self.compile_acyclic_dag_query(
                query,
                query_idx,
                &dag_arg_constants,
                &dag_arg_bounds,
                &mut linearized_square_count,
                &mut interval_simplified_count,
                deadline,
            ) else {
                self.stats.borrow_mut().budget_exhausted = true;
                return ChcEngineResult::Unknown;
            };
            query_disjuncts.push(query_disjunct);
        }

        if query_disjuncts.is_empty() {
            self.mark_acyclic_exhaustive_stats(max_depth, start.elapsed().as_secs_f64());
            return ChcEngineResult::Safe(InvariantModel::default());
        }

        conjuncts.push(if query_disjuncts.len() == 1 {
            query_disjuncts.remove(0)
        } else {
            ChcExpr::or_all(query_disjuncts)
        });

        if self.config.base.verbose {
            safe_eprintln!(
                "BMC: exact polynomial DAG encoding cone={}, rules={}, conjuncts={}, timeout={:.1}s",
                ordered_cone.len(),
                rule_count,
                conjuncts.len(),
                deadline
                    .saturating_duration_since(ay_core::time::Instant::now())
                    .as_secs_f64()
            );
            if bound_conjunct_count > 0
                || linearized_square_count > 0
                || interval_simplified_count > 0
            {
                safe_eprintln!(
                    "BMC: polynomial DAG range strengthening bounds={}, bounded_squares={}, interval_simplified={}",
                    bound_conjunct_count,
                    linearized_square_count,
                    interval_simplified_count
                );
            }
        }

        if !self.executor_conjuncts_supported(&conjuncts, "acyclic-polynomial-dag") {
            return ChcEngineResult::Unknown;
        }

        let formula = ChcExpr::and_all(conjuncts);
        let remaining = deadline.saturating_duration_since(ay_core::time::Instant::now());
        if remaining.is_zero() {
            self.stats.borrow_mut().budget_exhausted = true;
            return ChcEngineResult::Unknown;
        }

        let smt = self.problem.make_smt_context();
        let propagated_model = FxHashMap::default();
        match smt.check_sat_via_executor(&formula, &propagated_model, remaining) {
            result if result.is_unsat() => {
                self.mark_acyclic_exhaustive_stats(max_depth, start.elapsed().as_secs_f64());
                ChcEngineResult::Safe(InvariantModel::default())
            }
            SmtResult::Sat(model) => {
                self.record_depth(max_depth, start.elapsed().as_secs_f64());
                if let Some(witness) = self.acyclic_dag_model_derivation_witness(
                    &model,
                    queries,
                    defs_by_head,
                    &dag_arg_constants,
                ) {
                    self.verified_unsafe_from_witness(witness, "acyclic polynomial DAG BMC")
                } else {
                    tracing::debug!(
                        "BMC: acyclic polynomial DAG SAT model has no complete derivation witness; returning Unknown"
                    );
                    ChcEngineResult::Unknown
                }
            }
            SmtResult::Unknown => {
                self.record_depth(max_depth, start.elapsed().as_secs_f64());
                ChcEngineResult::Unknown
            }
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                unreachable!("handled by is_unsat guard")
            }
        }
    }

    fn acyclic_dag_model_derivation_witness(
        &self,
        model: &FxHashMap<String, SmtValue>,
        queries: &[&HornClause],
        defs_by_head: &FxHashMap<PredicateId, Vec<usize>>,
        dag_arg_constants: &FxHashMap<(PredicateId, usize), ChcExpr>,
    ) -> Option<DerivationWitness> {
        let env = Self::model_i128_env(model);
        let (query_clause, root_pred, query_instances) =
            self.acyclic_dag_root_query(model, &env, queries, dag_arg_constants)?;
        let mut entries = Vec::new();
        let mut visiting = FxHashSet::default();
        let root = self.acyclic_dag_derivation_entry(
            root_pred,
            model,
            &env,
            defs_by_head,
            dag_arg_constants,
            &mut entries,
            &mut visiting,
        )?;
        for (name, value) in query_instances {
            entries[root].instances.entry(name).or_insert(value);
        }
        Self::assign_derivation_levels(&mut entries, root);
        Some(DerivationWitness {
            query_clause,
            root,
            entries,
        })
    }

    fn acyclic_dag_root_query(
        &self,
        model: &FxHashMap<String, SmtValue>,
        env: &FxHashMap<String, i128>,
        queries: &[&HornClause],
        dag_arg_constants: &FxHashMap<(PredicateId, usize), ChcExpr>,
    ) -> Option<(Option<usize>, PredicateId, FxHashMap<String, SmtValue>)> {
        for (query_idx, query) in queries.iter().enumerate() {
            let [(body_pred, _)] = query.body.predicates.as_slice() else {
                continue;
            };
            let conjuncts = self.acyclic_dag_query_conjuncts(query, query_idx, dag_arg_constants);
            if !Self::model_conjuncts_satisfied(&conjuncts, model, env) {
                continue;
            }
            let instances = self.acyclic_dag_query_instances(query, query_idx, env);
            return Some((self.query_clause_index(query), *body_pred, instances));
        }
        for query in queries {
            let [(body_pred, _)] = query.body.predicates.as_slice() else {
                continue;
            };
            if Self::model_bool_expr(model, &self.dag_predicate(*body_pred)) == Some(true) {
                return Some((
                    self.query_clause_index(query),
                    *body_pred,
                    FxHashMap::default(),
                ));
            }
        }
        None
    }

    fn acyclic_dag_query_conjuncts(
        &self,
        query: &HornClause,
        query_idx: usize,
        dag_arg_constants: &FxHashMap<(PredicateId, usize), ChcExpr>,
    ) -> Vec<ChcExpr> {
        let subst = self.mk_dag_query_vars(query, query_idx);
        let mut conjuncts = Vec::new();
        for (body_pred, body_args) in &query.body.predicates {
            conjuncts.push(self.dag_predicate(*body_pred));
            for (arg_idx, body_arg) in body_args.iter().enumerate() {
                conjuncts.push(Self::simplify_bmc_expr(ChcExpr::eq(
                    self.dag_arg_with_constants(*body_pred, arg_idx, dag_arg_constants),
                    Self::simplify_bmc_expr(body_arg.substitute_name_map(&subst)),
                )));
            }
        }
        if let Some(constraint) = &query.body.constraint {
            conjuncts.push(Self::simplify_bmc_expr(
                constraint.substitute_name_map(&subst),
            ));
        }
        conjuncts
    }

    fn acyclic_dag_query_instances(
        &self,
        query: &HornClause,
        query_idx: usize,
        env: &FxHashMap<String, i128>,
    ) -> FxHashMap<String, SmtValue> {
        let subst = self.mk_dag_query_vars(query, query_idx);
        let mut instances = FxHashMap::default();
        for var in query.vars() {
            let Some(expr) = subst.get(&var.name) else {
                continue;
            };
            let Some(value) = Self::concrete_eval_for_sort(expr, &var.sort, env) else {
                continue;
            };
            if let Some(value) = Self::concrete_value_smt(&var.sort, value) {
                instances.insert(var.name.clone(), value);
            }
        }
        instances
    }

    fn acyclic_dag_derivation_entry(
        &self,
        pred: PredicateId,
        model: &FxHashMap<String, SmtValue>,
        env: &FxHashMap<String, i128>,
        defs_by_head: &FxHashMap<PredicateId, Vec<usize>>,
        dag_arg_constants: &FxHashMap<(PredicateId, usize), ChcExpr>,
        entries: &mut Vec<DerivationWitnessEntry>,
        visiting: &mut FxHashSet<PredicateId>,
    ) -> Option<usize> {
        if !visiting.insert(pred) {
            return None;
        }

        let result = self.acyclic_dag_derivation_entry_inner(
            pred,
            model,
            env,
            defs_by_head,
            dag_arg_constants,
            entries,
            visiting,
        );
        visiting.remove(&pred);
        result
    }

    fn acyclic_dag_derivation_entry_inner(
        &self,
        pred: PredicateId,
        model: &FxHashMap<String, SmtValue>,
        env: &FxHashMap<String, i128>,
        defs_by_head: &FxHashMap<PredicateId, Vec<usize>>,
        dag_arg_constants: &FxHashMap<(PredicateId, usize), ChcExpr>,
        entries: &mut Vec<DerivationWitnessEntry>,
        visiting: &mut FxHashSet<PredicateId>,
    ) -> Option<usize> {
        let values = self.acyclic_dag_pred_values(pred, env, dag_arg_constants)?;
        let (instances, state_expr) = self.concrete_state_witness(pred, &values)?;
        let entry_idx = entries.len();
        entries.push(DerivationWitnessEntry {
            predicate: pred,
            level: 0,
            state: state_expr,
            incoming_clause: None,
            premises: Vec::new(),
            instances,
        });

        for clause_idx in defs_by_head.get(&pred).into_iter().flatten() {
            if Self::model_bool_expr(model, &self.dag_rule_indicator(pred, *clause_idx))
                != Some(true)
            {
                continue;
            }
            let clause = &self.problem.clauses()[*clause_idx];
            let before_premises = entries.len();
            let mut premises = Vec::new();
            let mut ok = true;
            for (body_pred, _) in &clause.body.predicates {
                match self.acyclic_dag_derivation_entry(
                    *body_pred,
                    model,
                    env,
                    defs_by_head,
                    dag_arg_constants,
                    entries,
                    visiting,
                ) {
                    Some(premise_idx) => premises.push(premise_idx),
                    None => {
                        ok = false;
                        break;
                    }
                }
            }

            if ok {
                let local_instances =
                    self.acyclic_dag_clause_instances(pred, *clause_idx, clause, env);
                for (name, value) in local_instances {
                    entries[entry_idx].instances.entry(name).or_insert(value);
                }
                entries[entry_idx].incoming_clause = Some(*clause_idx);
                entries[entry_idx].premises = premises;
                return Some(entry_idx);
            }
            entries.truncate(before_premises);
        }

        entries.pop();
        None
    }

    fn acyclic_dag_pred_values(
        &self,
        pred: PredicateId,
        env: &FxHashMap<String, i128>,
        dag_arg_constants: &FxHashMap<(PredicateId, usize), ChcExpr>,
    ) -> Option<Vec<i128>> {
        let pred_info = self.problem.get_predicate(pred)?;
        pred_info
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(idx, sort)| {
                let expr = self.dag_arg_with_constants(pred, idx, dag_arg_constants);
                Self::concrete_eval_for_sort(&expr, sort, env)
            })
            .collect()
    }

    fn acyclic_dag_clause_instances(
        &self,
        pred: PredicateId,
        clause_idx: usize,
        clause: &HornClause,
        env: &FxHashMap<String, i128>,
    ) -> FxHashMap<String, SmtValue> {
        let subst = self.mk_dag_clause_vars(clause, pred, clause_idx);
        let mut instances = FxHashMap::default();
        for var in clause.vars() {
            let Some(expr) = subst.get(&var.name) else {
                continue;
            };
            let Some(value) = Self::concrete_eval_for_sort(expr, &var.sort, env) else {
                continue;
            };
            if let Some(value) = Self::concrete_value_smt(&var.sort, value) {
                instances.insert(var.name.clone(), value);
            }
        }
        instances
    }

    fn assign_derivation_levels(entries: &mut [DerivationWitnessEntry], root: usize) -> usize {
        let premises = entries
            .get(root)
            .map(|entry| entry.premises.clone())
            .unwrap_or_default();
        let level = premises
            .into_iter()
            .map(|premise| Self::assign_derivation_levels(entries, premise) + 1)
            .max()
            .unwrap_or(0);
        if let Some(entry) = entries.get_mut(root) {
            entry.level = level;
        }
        level
    }

    fn acyclic_dag_encoding_applicable(
        &self,
        queries: &[&HornClause],
        cone: &FxHashSet<PredicateId>,
        defs_by_head: &FxHashMap<PredicateId, Vec<usize>>,
    ) -> bool {
        if queries.iter().any(|query| query.body.predicates.len() > 1) {
            return false;
        }

        for pred in cone {
            for clause_idx in defs_by_head.get(pred).into_iter().flatten() {
                if self.problem.clauses()[*clause_idx].body.predicates.len() > 1 {
                    return false;
                }
            }
        }
        true
    }

    /// Returns `None` when `deadline` expires mid-compile (model-checker-consumer wishlist
    /// item 3); the caller must set `stats.budget_exhausted` and bail to
    /// `Unknown` — the partially pushed `conjuncts` are discarded with it.
    #[allow(clippy::too_many_arguments)]
    fn compile_acyclic_dag_definition(
        &self,
        pred: PredicateId,
        defs_by_head: &FxHashMap<PredicateId, Vec<usize>>,
        dag_arg_constants: &FxHashMap<(PredicateId, usize), ChcExpr>,
        dag_arg_bounds: &FxHashMap<(PredicateId, usize), IntInterval>,
        linearized_square_count: &mut usize,
        interval_simplified_count: &mut usize,
        conjuncts: &mut Vec<ChcExpr>,
        deadline: ay_core::time::Instant,
    ) -> Option<usize> {
        let mut rule_indicators = Vec::new();
        let mut rule_count = 0usize;

        for clause_idx in defs_by_head.get(&pred).into_iter().flatten() {
            // Budget compliance: poll once per clause — each clause emits
            // ~2×arity simplified equality conjuncts plus the interval
            // fixpoints below, so per-pred polling alone is too coarse.
            if self.dag_deadline_expired(deadline) {
                return None;
            }
            let clause = &self.problem.clauses()[*clause_idx];
            let rule_ind = self.dag_rule_indicator(pred, *clause_idx);
            rule_indicators.push(rule_ind.clone());
            let subst = self.mk_dag_clause_vars(clause, pred, *clause_idx);
            let protected_vars = self.rule_interface_var_names(clause);
            let mut rule_conjuncts = Vec::new();
            rule_count += 1;

            if let ClauseHead::Predicate(_, head_args) = &clause.head {
                for (arg_idx, head_arg) in head_args.iter().enumerate() {
                    rule_conjuncts.push(Self::simplify_bmc_expr(ChcExpr::eq(
                        self.dag_arg_with_constants(pred, arg_idx, dag_arg_constants),
                        Self::simplify_bmc_expr(head_arg.substitute_name_map(&subst)),
                    )));
                }
            }

            for (body_pred, body_args) in &clause.body.predicates {
                rule_conjuncts.push(self.dag_predicate(*body_pred));
                for (arg_idx, body_arg) in body_args.iter().enumerate() {
                    rule_conjuncts.push(Self::simplify_bmc_expr(ChcExpr::eq(
                        self.dag_arg_with_constants(*body_pred, arg_idx, dag_arg_constants),
                        Self::simplify_bmc_expr(body_arg.substitute_name_map(&subst)),
                    )));
                }
            }

            self.push_sliced_constraint_conjuncts(
                clause.body.constraint.as_ref(),
                &subst,
                &protected_vars,
                &mut rule_conjuncts,
            );
            // Item 4c: the interval/bool machinery tracks only Int variables
            // (`bind_expr_interval`), so Array/BV-only clauses get zero
            // strengthening from it yet pay its full
            // O(rounds × conjuncts × tree-rewrite) cost — skip them.
            if self.clause_interval_machinery_relevant(clause) {
                if let Some(mut interval_env) = self
                    .dag_clause_interval_env(
                        clause,
                        &subst,
                        dag_arg_constants,
                        dag_arg_bounds,
                        deadline,
                    )
                    .ok()?
                {
                    let local_bool_vars = Self::bool_var_names_from_subst(&subst);
                    if Self::collect_conjunct_interval_bounds(
                        &rule_conjuncts,
                        &mut interval_env,
                        Some(deadline),
                    )
                    .ok()?
                    {
                        *linearized_square_count += Self::linearize_bounded_squares_in_conjuncts(
                            &mut rule_conjuncts,
                            &interval_env,
                        );
                        if Self::collect_conjunct_interval_bounds(
                            &rule_conjuncts,
                            &mut interval_env,
                            Some(deadline),
                        )
                        .ok()?
                        {
                            *interval_simplified_count +=
                                Self::simplify_conjuncts_with_intervals_and_bools(
                                    &mut rule_conjuncts,
                                    &mut interval_env,
                                    &local_bool_vars,
                                    Some(deadline),
                                );
                        }
                    }
                }
            }
            conjuncts.push(ChcExpr::implies(rule_ind, ChcExpr::and_all(rule_conjuncts)));
        }

        let reach = self.dag_predicate(pred);
        if rule_indicators.is_empty() {
            conjuncts.push(ChcExpr::not(reach));
        } else if rule_indicators.len() == 1 {
            conjuncts.push(ChcExpr::implies(reach, rule_indicators.remove(0)));
        } else {
            conjuncts.push(ChcExpr::implies(reach, ChcExpr::or_all(rule_indicators)));
        }
        Some(rule_count)
    }

    /// Returns `None` when `deadline` expires mid-compile (model-checker-consumer wishlist
    /// item 3); the caller must set `stats.budget_exhausted` and bail to
    /// `Unknown`.
    #[allow(clippy::too_many_arguments)]
    fn compile_acyclic_dag_query(
        &self,
        query: &HornClause,
        query_idx: usize,
        dag_arg_constants: &FxHashMap<(PredicateId, usize), ChcExpr>,
        dag_arg_bounds: &FxHashMap<(PredicateId, usize), IntInterval>,
        linearized_square_count: &mut usize,
        interval_simplified_count: &mut usize,
        deadline: ay_core::time::Instant,
    ) -> Option<ChcExpr> {
        let subst = self.mk_dag_query_vars(query, query_idx);
        let mut conjuncts = Vec::new();

        for (body_pred, body_args) in &query.body.predicates {
            conjuncts.push(self.dag_predicate(*body_pred));
            for (arg_idx, body_arg) in body_args.iter().enumerate() {
                conjuncts.push(Self::simplify_bmc_expr(ChcExpr::eq(
                    self.dag_arg_with_constants(*body_pred, arg_idx, dag_arg_constants),
                    Self::simplify_bmc_expr(body_arg.substitute_name_map(&subst)),
                )));
            }
        }

        if let Some(constraint) = &query.body.constraint {
            conjuncts.push(Self::simplify_bmc_expr(
                constraint.substitute_name_map(&subst),
            ));
        }

        // Budget compliance: poll between conjunct construction and the
        // interval machinery (each phase pays per-conjunct tree rewrites).
        if self.dag_deadline_expired(deadline) {
            return None;
        }
        // Item 4c: skip the Int-interval machinery for Int-free queries
        // (see compile_acyclic_dag_definition).
        if self.clause_interval_machinery_relevant(query) {
            if let Some(mut interval_env) = self
                .dag_query_interval_env(query, &subst, dag_arg_constants, dag_arg_bounds, deadline)
                .ok()?
            {
                let local_bool_vars = Self::bool_var_names_from_subst(&subst);
                if Self::collect_conjunct_interval_bounds(
                    &conjuncts,
                    &mut interval_env,
                    Some(deadline),
                )
                .ok()?
                {
                    *linearized_square_count +=
                        Self::linearize_bounded_squares_in_conjuncts(&mut conjuncts, &interval_env);
                    if Self::collect_conjunct_interval_bounds(
                        &conjuncts,
                        &mut interval_env,
                        Some(deadline),
                    )
                    .ok()?
                    {
                        *interval_simplified_count +=
                            Self::simplify_conjuncts_with_intervals_and_bools(
                                &mut conjuncts,
                                &mut interval_env,
                                &local_bool_vars,
                                Some(deadline),
                            );
                    }
                }
            }
        }

        Some(ChcExpr::and_all(conjuncts))
    }

    /// True when the interval/bool simplification machinery can possibly help
    /// this clause: some head/body predicate interface argument is Int-sorted,
    /// or the clause constraint mentions an Int-sorted variable. The interval
    /// env only ever binds Int variables (`bind_expr_interval` /
    /// `collect_conjunct_interval_bound`), so for clauses failing this test
    /// the machinery provably derives nothing (item 4c: Array-of-BV clauses
    /// previously paid the full O(rounds × conjuncts × tree-rewrite) cost for
    /// zero benefit). Erring on the side of `true` is always safe — it merely
    /// re-enables the (semantics-preserving) simplifier.
    fn clause_interval_machinery_relevant(&self, clause: &HornClause) -> bool {
        let pred_has_int_arg = |pred: PredicateId| {
            self.problem
                .get_predicate(pred)
                .is_some_and(|info| info.arg_sorts.iter().any(|sort| *sort == ChcSort::Int))
        };
        if let ClauseHead::Predicate(head_pred, _) = &clause.head {
            if pred_has_int_arg(*head_pred) {
                return true;
            }
        }
        if clause
            .body
            .predicates
            .iter()
            .any(|(body_pred, _)| pred_has_int_arg(*body_pred))
        {
            return true;
        }
        clause
            .body
            .constraint
            .as_ref()
            .is_some_and(|constraint| Self::expr_mentions_int_var(constraint, 0))
    }

    /// Early-exit walk: does `expr` mention any Int-sorted variable?
    ///
    /// Returns `true` (conservative: "machinery may be relevant") when the
    /// recursion depth cap is hit, so pathological trees keep today's
    /// behavior.
    fn expr_mentions_int_var(expr: &ChcExpr, depth: usize) -> bool {
        if depth >= crate::expr::MAX_EXPR_RECURSION_DEPTH {
            return true;
        }
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Var(var) => var.sort == ChcSort::Int,
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => args
                .iter()
                .any(|arg| Self::expr_mentions_int_var(arg, depth + 1)),
            ChcExpr::ConstArray(_, value) => Self::expr_mentions_int_var(value, depth + 1),
            _ => false,
        })
    }

    fn rule_interface_var_names(&self, clause: &HornClause) -> FxHashSet<String> {
        let mut names = FxHashSet::default();
        if let ClauseHead::Predicate(_, head_args) = &clause.head {
            for arg in head_args {
                for var in arg.vars() {
                    names.insert(var.name);
                }
            }
        }
        for (_, body_args) in &clause.body.predicates {
            for arg in body_args {
                for var in arg.vars() {
                    names.insert(var.name);
                }
            }
        }
        names
    }

    fn push_sliced_constraint_conjuncts(
        &self,
        constraint: Option<&ChcExpr>,
        subst: &FxHashMap<String, ChcExpr>,
        protected_vars: &FxHashSet<String>,
        out: &mut Vec<ChcExpr>,
    ) {
        let Some(constraint) = constraint else {
            return;
        };
        let mut conjuncts = constraint.collect_conjuncts_nontrivial();
        loop {
            let var_counts = Self::constraint_var_counts(&conjuncts);
            let before = conjuncts.len();
            conjuncts.retain(|conjunct| {
                !Self::is_dead_single_use_definition(conjunct, protected_vars, &var_counts)
            });
            if conjuncts.len() == before {
                break;
            }
        }

        out.extend(
            conjuncts
                .into_iter()
                .map(|conjunct| Self::simplify_bmc_expr(conjunct.substitute_name_map(subst))),
        );
    }

    fn simplify_bmc_expr(expr: ChcExpr) -> ChcExpr {
        let expr = Self::simplify_dt_selector_apps(expr)
            .simplify_array_ops()
            .simplify_constants();
        Self::simplify_bv_identities(expr).simplify_constants()
    }

    fn simplify_bv_identities(expr: ChcExpr) -> ChcExpr {
        match &expr {
            ChcExpr::Op(op, args) => {
                let args: Vec<_> = args
                    .iter()
                    .map(|arg| Arc::new(Self::simplify_bv_identities(arg.as_ref().clone())))
                    .collect();
                let expr = ChcExpr::Op(*op, args).simplify_constants();
                let ChcExpr::Op(op, args) = &expr else {
                    return expr;
                };

                match op {
                    ChcOp::BvAdd if args.len() == 2 => {
                        if Self::is_bv_zero(args[0].as_ref()) {
                            return args[1].as_ref().clone();
                        }
                        if Self::is_bv_zero(args[1].as_ref()) {
                            return args[0].as_ref().clone();
                        }
                    }
                    ChcOp::BvSub if args.len() == 2 => {
                        if Self::is_bv_zero(args[1].as_ref()) {
                            return args[0].as_ref().clone();
                        }
                        if args[0] == args[1] {
                            if let Some(width) = Self::bv_width(args[0].as_ref()) {
                                return ChcExpr::BitVec(0, width);
                            }
                        }
                        if let Some(stripped) =
                            Self::strip_matching_bv_add_const(args[0].as_ref(), args[1].as_ref())
                        {
                            return stripped;
                        }
                    }
                    ChcOp::BvMul if args.len() == 2 => {
                        if Self::is_bv_zero(args[0].as_ref()) {
                            return args[0].as_ref().clone();
                        }
                        if Self::is_bv_zero(args[1].as_ref()) {
                            if let Some(width) = Self::bv_width(args[0].as_ref()) {
                                return ChcExpr::BitVec(0, width);
                            }
                        }
                        if Self::is_bv_one(args[0].as_ref()) {
                            return args[1].as_ref().clone();
                        }
                        if Self::is_bv_one(args[1].as_ref()) {
                            return args[0].as_ref().clone();
                        }
                    }
                    ChcOp::BvUDiv | ChcOp::BvSDiv
                        if args.len() == 2 && Self::is_bv_one(args[1].as_ref()) =>
                    {
                        return args[0].as_ref().clone();
                    }
                    ChcOp::BvExtract(hi, lo) if args.len() == 1 => {
                        if let Some(extracted) =
                            Self::extract_from_bv_concat(args[0].as_ref(), *hi, *lo)
                        {
                            return extracted;
                        }
                    }
                    _ => {}
                }

                ChcExpr::Op(*op, args.clone())
            }
            ChcExpr::PredicateApp(name, pred, args) => ChcExpr::PredicateApp(
                name.clone(),
                *pred,
                args.iter()
                    .map(|arg| Arc::new(Self::simplify_bv_identities(arg.as_ref().clone())))
                    .collect(),
            ),
            ChcExpr::FuncApp(name, sort, args) => ChcExpr::FuncApp(
                name.clone(),
                sort.clone(),
                args.iter()
                    .map(|arg| Arc::new(Self::simplify_bv_identities(arg.as_ref().clone())))
                    .collect(),
            ),
            ChcExpr::ConstArray(key_sort, value) => ChcExpr::ConstArray(
                key_sort.clone(),
                Arc::new(Self::simplify_bv_identities(value.as_ref().clone())),
            ),
            other => other.clone(),
        }
    }

    fn strip_matching_bv_add_const(sum: &ChcExpr, subtrahend: &ChcExpr) -> Option<ChcExpr> {
        let ChcExpr::Op(ChcOp::BvAdd, args) = sum else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }
        if args[0].as_ref() == subtrahend {
            return Some(args[1].as_ref().clone());
        }
        if args[1].as_ref() == subtrahend {
            return Some(args[0].as_ref().clone());
        }
        None
    }

    fn extract_from_bv_concat(expr: &ChcExpr, hi: u32, lo: u32) -> Option<ChcExpr> {
        let ChcExpr::Op(ChcOp::BvConcat, args) = expr else {
            return None;
        };
        if args.len() != 2 || hi < lo {
            return None;
        }
        let high = args[0].as_ref();
        let low = args[1].as_ref();
        let high_width = Self::bv_width(high)?;
        let low_width = Self::bv_width(low)?;
        let total_width = high_width.checked_add(low_width)?;
        if hi >= total_width {
            return None;
        }

        if hi < low_width {
            return Some(Self::extract_or_identity(low.clone(), hi, lo));
        }
        if lo >= low_width {
            return Some(Self::extract_or_identity(
                high.clone(),
                hi - low_width,
                lo - low_width,
            ));
        }
        None
    }

    fn extract_or_identity(expr: ChcExpr, hi: u32, lo: u32) -> ChcExpr {
        if let Some(width) = Self::bv_width(&expr) {
            if lo == 0 && hi + 1 == width {
                return expr;
            }
        }
        Self::simplify_bv_identities(ChcExpr::Op(ChcOp::BvExtract(hi, lo), vec![Arc::new(expr)]))
            .simplify_constants()
    }

    fn bv_width(expr: &ChcExpr) -> Option<u32> {
        match expr.sort() {
            ChcSort::BitVec(width) => Some(width),
            _ => None,
        }
    }

    fn is_bv_zero(expr: &ChcExpr) -> bool {
        matches!(expr, ChcExpr::BitVec(value, _) if *value == 0)
    }

    fn is_bv_one(expr: &ChcExpr) -> bool {
        matches!(expr, ChcExpr::BitVec(value, _) if *value == 1)
    }

    fn simplify_dt_selector_apps(expr: ChcExpr) -> ChcExpr {
        match &expr {
            ChcExpr::Op(op, args) => ChcExpr::Op(
                *op,
                args.iter()
                    .map(|arg| Arc::new(Self::simplify_dt_selector_apps(arg.as_ref().clone())))
                    .collect(),
            ),
            ChcExpr::PredicateApp(name, pred, args) => ChcExpr::PredicateApp(
                name.clone(),
                *pred,
                args.iter()
                    .map(|arg| Arc::new(Self::simplify_dt_selector_apps(arg.as_ref().clone())))
                    .collect(),
            ),
            ChcExpr::FuncApp(name, sort, args) => {
                let simplified_args: Vec<_> = args
                    .iter()
                    .map(|arg| Arc::new(Self::simplify_dt_selector_apps(arg.as_ref().clone())))
                    .collect();
                if simplified_args.len() == 1 {
                    if let ChcExpr::FuncApp(
                        ctor_name,
                        ChcSort::Datatype { constructors, .. },
                        ctor_args,
                    ) = simplified_args[0].as_ref()
                    {
                        for ctor in constructors.iter() {
                            if ctor.name != *ctor_name {
                                continue;
                            }
                            for (selector_idx, selector) in ctor.selectors.iter().enumerate() {
                                if selector.name == *name {
                                    if let Some(value) = ctor_args.get(selector_idx) {
                                        return value.as_ref().clone();
                                    }
                                }
                            }
                        }
                    }
                }
                ChcExpr::FuncApp(name.clone(), sort.clone(), simplified_args)
            }
            ChcExpr::ConstArray(key_sort, value) => ChcExpr::ConstArray(
                key_sort.clone(),
                Arc::new(Self::simplify_dt_selector_apps(value.as_ref().clone())),
            ),
            other => other.clone(),
        }
    }

    fn constraint_var_counts(conjuncts: &[ChcExpr]) -> FxHashMap<String, usize> {
        let mut counts = FxHashMap::default();
        for conjunct in conjuncts {
            for var in conjunct.vars() {
                *counts.entry(var.name).or_insert(0) += 1;
            }
        }
        counts
    }

    fn is_dead_single_use_definition(
        conjunct: &ChcExpr,
        protected_vars: &FxHashSet<String>,
        var_counts: &FxHashMap<String, usize>,
    ) -> bool {
        let ChcExpr::Op(crate::ChcOp::Eq, args) = conjunct else {
            return false;
        };
        if args.len() != 2 {
            return false;
        }

        Self::dead_definition_side(
            args[0].as_ref(),
            args[1].as_ref(),
            protected_vars,
            var_counts,
        ) || Self::dead_definition_side(
            args[1].as_ref(),
            args[0].as_ref(),
            protected_vars,
            var_counts,
        )
    }

    fn dead_definition_side(
        candidate: &ChcExpr,
        other: &ChcExpr,
        protected_vars: &FxHashSet<String>,
        var_counts: &FxHashMap<String, usize>,
    ) -> bool {
        let ChcExpr::Var(var) = candidate else {
            return false;
        };
        if protected_vars.contains(&var.name)
            || var_counts.get(&var.name).copied().unwrap_or(0) != 1
        {
            return false;
        }
        !other
            .vars()
            .into_iter()
            .any(|other_var| other_var.name == var.name)
    }

    fn mk_dag_clause_vars(
        &self,
        clause: &HornClause,
        pred: PredicateId,
        clause_idx: usize,
    ) -> FxHashMap<String, ChcExpr> {
        let mut subst = FxHashMap::default();
        for (var_idx, var) in clause.vars().into_iter().enumerate() {
            subst.insert(
                var.name.clone(),
                ChcExpr::Var(ChcVar::new(
                    format!("__bmc_poly_p{}_c{}_v{}", pred.index(), clause_idx, var_idx),
                    var.sort,
                )),
            );
        }
        subst
    }

    fn mk_dag_query_vars(
        &self,
        query: &HornClause,
        query_idx: usize,
    ) -> FxHashMap<String, ChcExpr> {
        let mut subst = FxHashMap::default();
        for (var_idx, var) in query.vars().into_iter().enumerate() {
            subst.insert(
                var.name.clone(),
                ChcExpr::Var(ChcVar::new(
                    format!("__bmc_poly_q{}_v{}", query_idx, var_idx),
                    var.sort,
                )),
            );
        }
        subst
    }

    fn dag_predicate(&self, pred: PredicateId) -> ChcExpr {
        ChcExpr::Var(ChcVar::new(
            format!("__bmc_poly_p{}_reach", pred.index()),
            ChcSort::Bool,
        ))
    }

    fn dag_rule_indicator(&self, pred: PredicateId, clause_idx: usize) -> ChcExpr {
        ChcExpr::Var(ChcVar::new(
            format!("__bmc_poly_p{}_r{}", pred.index(), clause_idx),
            ChcSort::Bool,
        ))
    }

    fn dag_arg(&self, pred: PredicateId, idx: usize) -> ChcExpr {
        let pred_info = self
            .problem
            .get_predicate(pred)
            .expect("BmcSolver: predicate ID from problem should be valid");
        let sort = pred_info
            .arg_sorts
            .get(idx)
            .expect("BmcSolver: argument index should be within predicate arity")
            .clone();
        ChcExpr::Var(ChcVar::new(
            format!("__bmc_poly_p{}_a{}", pred.index(), idx),
            sort,
        ))
    }

    fn dag_arg_with_constants(
        &self,
        pred: PredicateId,
        idx: usize,
        constants: &FxHashMap<(PredicateId, usize), ChcExpr>,
    ) -> ChcExpr {
        constants
            .get(&(pred, idx))
            .cloned()
            .unwrap_or_else(|| self.dag_arg(pred, idx))
    }

    fn push_acyclic_dag_arg_bound_conjuncts(
        &self,
        ordered_cone: &[PredicateId],
        bounds: &FxHashMap<(PredicateId, usize), IntInterval>,
        constants: &FxHashMap<(PredicateId, usize), ChcExpr>,
        conjuncts: &mut Vec<ChcExpr>,
    ) -> usize {
        let mut count = 0usize;
        for pred in ordered_cone {
            let Some(pred_info) = self.problem.get_predicate(*pred) else {
                continue;
            };
            for (arg_idx, sort) in pred_info.arg_sorts.iter().enumerate() {
                if !matches!(sort, ChcSort::Int) {
                    continue;
                }
                let Some(interval) = bounds.get(&(*pred, arg_idx)).copied() else {
                    continue;
                };
                if !interval.has_bound() || interval.is_empty() {
                    continue;
                }
                let arg = self.dag_arg_with_constants(*pred, arg_idx, constants);
                let mut arg_bounds = Vec::new();
                if let Some(lower) = interval.lower {
                    arg_bounds.push(Self::simplify_bmc_expr(ChcExpr::ge(
                        arg.clone(),
                        ChcExpr::int(lower),
                    )));
                }
                if let Some(upper) = interval.upper {
                    arg_bounds.push(Self::simplify_bmc_expr(ChcExpr::le(
                        arg.clone(),
                        ChcExpr::int(upper),
                    )));
                }
                let bound = ChcExpr::and_all(arg_bounds);
                if !matches!(bound, ChcExpr::Bool(true)) {
                    conjuncts.push(ChcExpr::implies(self.dag_predicate(*pred), bound));
                    count += 1;
                }
            }
        }
        count
    }

    /// Returns `Err(DagBudgetExpired)` when `deadline` expires mid-fixpoint.
    /// The caller MUST bail to `Unknown` and never use a partial result: the
    /// intermediate `bounds` are joins-in-progress and can be too NARROW —
    /// `push_acyclic_dag_arg_bound_conjuncts` would assert them as facts,
    /// risking a false Safe (model-checker-consumer wishlist item 3 soundness caution).
    fn infer_acyclic_dag_arg_bounds(
        &self,
        ordered_cone: &[PredicateId],
        defs_by_head: &FxHashMap<PredicateId, Vec<usize>>,
        constants: &FxHashMap<(PredicateId, usize), ChcExpr>,
        deadline: ay_core::time::Instant,
    ) -> Result<FxHashMap<(PredicateId, usize), IntInterval>, DagBudgetExpired> {
        let mut reachable = FxHashSet::default();
        let mut bounds: FxHashMap<(PredicateId, usize), IntInterval> = FxHashMap::default();
        let max_iterations = self.problem.clauses().len().max(ordered_cone.len()) + 1;
        // Item 4c: the Int-relevance of a clause is invariant across rounds;
        // cache it so the fixpoint does not re-walk constraints every round.
        let mut relevance_cache: FxHashMap<usize, bool> = FxHashMap::default();

        for _ in 0..max_iterations {
            // Budget compliance (model-checker-consumer wishlist item 3): poll once per
            // fixpoint round (the per-clause interval-env construction below
            // also polls via its threaded deadline).
            if self.dag_deadline_expired(deadline) {
                return Err(DagBudgetExpired);
            }
            let mut changed = false;
            for pred in ordered_cone {
                for clause_idx in defs_by_head.get(pred).into_iter().flatten() {
                    let clause = &self.problem.clauses()[*clause_idx];
                    let ClauseHead::Predicate(head_pred, head_args) = &clause.head else {
                        continue;
                    };
                    if !clause
                        .body
                        .predicates
                        .iter()
                        .all(|(body_pred, _)| reachable.contains(body_pred))
                    {
                        continue;
                    }
                    let relevant = *relevance_cache
                        .entry(*clause_idx)
                        .or_insert_with(|| self.clause_interval_machinery_relevant(clause));
                    if !relevant {
                        // Item 4c fast path: with no Int-sorted interface args
                        // and no Int variables, the interval env can neither
                        // prune this clause (feasibility checks only constrain
                        // Int terms, so `dag_clause_interval_env` cannot
                        // return `None`) nor produce head-arg bounds (the
                        // Int-sort filter below skips every arg). Marking
                        // reachability is the only remaining effect —
                        // behaviorally identical, minus the per-round
                        // constraint re-simplification.
                        if reachable.insert(*head_pred) {
                            changed = true;
                        }
                        continue;
                    }
                    let Some(mut env) = self.dag_clause_interval_env(
                        clause,
                        &FxHashMap::default(),
                        constants,
                        &bounds,
                        deadline,
                    )?
                    else {
                        continue;
                    };
                    if let Some(constraint) = &clause.body.constraint {
                        let constraint = Self::simplify_bmc_expr(constraint.clone());
                        if !Self::collect_conjunct_interval_bounds(
                            &constraint.collect_conjuncts_nontrivial(),
                            &mut env,
                            Some(deadline),
                        )? {
                            continue;
                        }
                    }

                    if reachable.insert(*head_pred) {
                        changed = true;
                    }

                    let Some(pred_info) = self.problem.get_predicate(*head_pred) else {
                        continue;
                    };
                    for (arg_idx, head_arg) in head_args.iter().enumerate() {
                        if pred_info
                            .arg_sorts
                            .get(arg_idx)
                            .is_none_or(|sort| sort != &ChcSort::Int)
                        {
                            continue;
                        }
                        let interval = Self::expr_int_interval(head_arg, &env)
                            .unwrap_or_else(IntInterval::top);
                        let key = (*head_pred, arg_idx);
                        let joined = bounds
                            .get(&key)
                            .copied()
                            .map_or(interval, |current| current.join(interval));
                        if bounds.get(&key).copied() != Some(joined) {
                            bounds.insert(key, joined);
                            changed = true;
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }

        Ok(bounds)
    }

    /// `Ok(None)` = clause body provably infeasible (skip the machinery);
    /// `Err(DagBudgetExpired)` = deadline expired (caller must bail, NOT
    /// treat as infeasible — see `DagBudgetExpired`).
    fn dag_clause_interval_env(
        &self,
        clause: &HornClause,
        subst: &FxHashMap<String, ChcExpr>,
        constants: &FxHashMap<(PredicateId, usize), ChcExpr>,
        bounds: &FxHashMap<(PredicateId, usize), IntInterval>,
        deadline: ay_core::time::Instant,
    ) -> Result<Option<FxHashMap<String, IntInterval>>, DagBudgetExpired> {
        let mut env = FxHashMap::default();
        for (body_pred, body_args) in &clause.body.predicates {
            for (arg_idx, body_arg) in body_args.iter().enumerate() {
                let interval = constants
                    .get(&(*body_pred, arg_idx))
                    .and_then(Self::expr_literal_int_interval)
                    .or_else(|| bounds.get(&(*body_pred, arg_idx)).copied())
                    .unwrap_or_else(IntInterval::top);
                let body_arg = body_arg.substitute_name_map(subst);
                if !Self::bind_expr_interval(&body_arg, interval, &mut env) {
                    return Ok(None);
                }
            }
        }
        if let Some(constraint) = &clause.body.constraint {
            let substituted = Self::simplify_bmc_expr(constraint.substitute_name_map(subst));
            if !Self::collect_conjunct_interval_bounds(
                &substituted.collect_conjuncts_nontrivial(),
                &mut env,
                Some(deadline),
            )? {
                return Ok(None);
            }
        }
        Ok(Some(env))
    }

    /// `Ok(None)` = query body provably infeasible; `Err(DagBudgetExpired)` =
    /// deadline expired (caller must bail, NOT treat as infeasible).
    fn dag_query_interval_env(
        &self,
        query: &HornClause,
        subst: &FxHashMap<String, ChcExpr>,
        constants: &FxHashMap<(PredicateId, usize), ChcExpr>,
        bounds: &FxHashMap<(PredicateId, usize), IntInterval>,
        deadline: ay_core::time::Instant,
    ) -> Result<Option<FxHashMap<String, IntInterval>>, DagBudgetExpired> {
        let mut env = FxHashMap::default();
        for (body_pred, body_args) in &query.body.predicates {
            for (arg_idx, body_arg) in body_args.iter().enumerate() {
                let interval = constants
                    .get(&(*body_pred, arg_idx))
                    .and_then(Self::expr_literal_int_interval)
                    .or_else(|| bounds.get(&(*body_pred, arg_idx)).copied())
                    .unwrap_or_else(IntInterval::top);
                let body_arg = body_arg.substitute_name_map(subst);
                if !Self::bind_expr_interval(&body_arg, interval, &mut env) {
                    return Ok(None);
                }
            }
        }
        if let Some(constraint) = &query.body.constraint {
            let substituted = Self::simplify_bmc_expr(constraint.substitute_name_map(subst));
            if !Self::collect_conjunct_interval_bounds(
                &substituted.collect_conjuncts_nontrivial(),
                &mut env,
                Some(deadline),
            )? {
                return Ok(None);
            }
        }
        Ok(Some(env))
    }

    fn bind_expr_interval(
        expr: &ChcExpr,
        interval: IntInterval,
        env: &mut FxHashMap<String, IntInterval>,
    ) -> bool {
        match expr {
            ChcExpr::Var(var) if var.sort == ChcSort::Int => {
                Self::add_interval_bound(env, &var.name, interval)
            }
            ChcExpr::Int(value) => !IntInterval::exact(*value).intersect(interval).is_empty(),
            _ => true,
        }
    }

    fn bool_var_names_from_subst(subst: &FxHashMap<String, ChcExpr>) -> FxHashSet<String> {
        subst
            .values()
            .filter_map(|expr| {
                if let ChcExpr::Var(var) = expr {
                    if var.sort == ChcSort::Bool {
                        return Some(var.name.clone());
                    }
                }
                None
            })
            .collect()
    }

    /// `Ok(false)` = a conjunct is provably infeasible under the collected
    /// intervals; `Ok(true)` = bounds collected (possibly a fixpoint).
    /// `Err(DagBudgetExpired)` = `deadline` passed mid-collection — callers
    /// MUST treat that as "give up" (bail / stop simplifying), never as an
    /// infeasibility answer (model-checker-consumer wishlist item 3).
    fn collect_conjunct_interval_bounds(
        conjuncts: &[ChcExpr],
        env: &mut FxHashMap<String, IntInterval>,
        deadline: Option<ay_core::time::Instant>,
    ) -> Result<bool, DagBudgetExpired> {
        // `simplify_bmc_expr` is a pure, deterministic rewrite of an immutable
        // conjunct: its result is independent of `env` and identical on every
        // round. Precompute it once instead of paying two full tree rewrites
        // per conjunct *per round* (up to 32 rounds) inside the loop below —
        // both `collect_int_var_equality` and `collect_conjunct_interval_bound`
        // previously recomputed the same simplification. Byte-identical: the
        // simplified value drives exactly the same equality/bound extraction.
        let mut simplified = Vec::with_capacity(conjuncts.len());
        for (conjunct_idx, conjunct) in conjuncts.iter().enumerate() {
            // Poll every 64 conjuncts: each pays a full `simplify_bmc_expr`
            // tree rewrite.
            if conjunct_idx % 64 == 0 && dag_deadline_passed(deadline) {
                return Err(DagBudgetExpired);
            }
            simplified.push(Self::simplify_bmc_expr(conjunct.clone()));
        }

        let mut equalities = Vec::new();
        let max_rounds = conjuncts.len().saturating_add(4).clamp(1, 32);
        for _ in 0..max_rounds {
            let before = env.clone();
            equalities.clear();
            for (conjunct_idx, simplified_conjunct) in simplified.iter().enumerate() {
                if conjunct_idx % 64 == 0 && dag_deadline_passed(deadline) {
                    return Err(DagBudgetExpired);
                }
                if let Some(equality) = Self::collect_int_var_equality(simplified_conjunct) {
                    equalities.push(equality);
                }
                if !Self::collect_conjunct_interval_bound(simplified_conjunct, env) {
                    return Ok(false);
                }
            }
            if !Self::propagate_int_var_equality_bounds(&equalities, env) {
                return Ok(false);
            }
            if *env == before {
                return Ok(true);
            }
        }
        Ok(true)
    }

    /// `simplified` must already be `simplify_bmc_expr`-normalized (the caller
    /// precomputes it once per conjunct and reuses it across rounds).
    fn collect_int_var_equality(simplified: &ChcExpr) -> Option<(String, String)> {
        let ChcExpr::Op(ChcOp::Eq, args) = simplified else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }
        let lhs = Self::int_var_name(args[0].as_ref())?;
        let rhs = Self::int_var_name(args[1].as_ref())?;
        (lhs != rhs).then(|| (lhs.to_string(), rhs.to_string()))
    }

    fn propagate_int_var_equality_bounds(
        equalities: &[(String, String)],
        env: &mut FxHashMap<String, IntInterval>,
    ) -> bool {
        for _ in 0..=equalities.len() {
            let mut changed = false;
            for (lhs, rhs) in equalities {
                let lhs_interval = env.get(lhs).copied();
                let rhs_interval = env.get(rhs).copied();
                match (lhs_interval, rhs_interval) {
                    (Some(lhs_interval), Some(rhs_interval)) => {
                        let merged = lhs_interval.intersect(rhs_interval);
                        if merged.is_empty() {
                            return false;
                        }
                        changed |=
                            Self::add_interval_bound_changed(env, lhs, merged).unwrap_or(false);
                        changed |=
                            Self::add_interval_bound_changed(env, rhs, merged).unwrap_or(false);
                    }
                    (Some(interval), None) if interval.has_bound() => {
                        changed |=
                            Self::add_interval_bound_changed(env, rhs, interval).unwrap_or(false);
                    }
                    (None, Some(interval)) if interval.has_bound() => {
                        changed |=
                            Self::add_interval_bound_changed(env, lhs, interval).unwrap_or(false);
                    }
                    _ => {}
                }
            }
            if !changed {
                return true;
            }
        }
        true
    }

    /// `simplified` must already be `simplify_bmc_expr`-normalized (the caller
    /// precomputes it once per conjunct and reuses it across rounds).
    fn collect_conjunct_interval_bound(
        simplified: &ChcExpr,
        env: &mut FxHashMap<String, IntInterval>,
    ) -> bool {
        if let Some((op, lhs, rhs)) = Self::interval_comparison_atom(simplified) {
            return Self::collect_direct_interval_bound(op, lhs, rhs, env);
        }

        if let ChcExpr::Op(ChcOp::Not, args) = simplified {
            if args.len() == 1 {
                if let Some((op, lhs, rhs)) = Self::interval_comparison_atom(args[0].as_ref()) {
                    return Self::collect_direct_interval_bound(
                        Self::negated_interval_comparison(op),
                        lhs,
                        rhs,
                        env,
                    );
                }
            }
        }

        true
    }

    fn interval_comparison_atom(expr: &ChcExpr) -> Option<(ChcOp, &ChcExpr, &ChcExpr)> {
        let ChcExpr::Op(op @ (ChcOp::Eq | ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge), args) =
            expr
        else {
            return None;
        };
        if args.len() == 2 {
            Some((*op, args[0].as_ref(), args[1].as_ref()))
        } else {
            None
        }
    }

    fn negated_interval_comparison(op: ChcOp) -> ChcOp {
        match op {
            ChcOp::Lt => ChcOp::Ge,
            ChcOp::Le => ChcOp::Gt,
            ChcOp::Gt => ChcOp::Le,
            ChcOp::Ge => ChcOp::Lt,
            ChcOp::Eq => ChcOp::Ne,
            other => other,
        }
    }

    fn collect_direct_interval_bound(
        op: ChcOp,
        lhs: &ChcExpr,
        rhs: &ChcExpr,
        env: &mut FxHashMap<String, IntInterval>,
    ) -> bool {
        match op {
            ChcOp::Eq => {
                if let (Some(name), Some(value)) = (Self::int_var_name(lhs), rhs.as_i128()) {
                    return Self::add_interval_bound(env, name, IntInterval::exact(value));
                }
                if let (Some(value), Some(name)) = (lhs.as_i128(), Self::int_var_name(rhs)) {
                    return Self::add_interval_bound(env, name, IntInterval::exact(value));
                }
                if let Some(name) = Self::int_var_name(lhs) {
                    if let Some(interval) = Self::expr_int_interval(rhs, env) {
                        if interval.has_bound() {
                            return Self::add_interval_bound(env, name, interval);
                        }
                    }
                }
                if let Some(name) = Self::int_var_name(rhs) {
                    if let Some(interval) = Self::expr_int_interval(lhs, env) {
                        if interval.has_bound() {
                            return Self::add_interval_bound(env, name, interval);
                        }
                    }
                }
            }
            ChcOp::Le => {
                if let (Some(name), Some(value)) = (Self::int_var_name(lhs), rhs.as_i128()) {
                    return Self::add_interval_bound(env, name, IntInterval::upper(value));
                }
                if let (Some(value), Some(name)) = (lhs.as_i128(), Self::int_var_name(rhs)) {
                    return Self::add_interval_bound(env, name, IntInterval::lower(value));
                }
            }
            ChcOp::Lt => {
                if let (Some(name), Some(value)) = (Self::int_var_name(lhs), rhs.as_i128()) {
                    if let Some(upper) = value.checked_sub(1) {
                        return Self::add_interval_bound(env, name, IntInterval::upper(upper));
                    }
                }
                if let (Some(value), Some(name)) = (lhs.as_i128(), Self::int_var_name(rhs)) {
                    if let Some(lower) = value.checked_add(1) {
                        return Self::add_interval_bound(env, name, IntInterval::lower(lower));
                    }
                }
            }
            ChcOp::Ge => {
                return Self::collect_direct_interval_bound(ChcOp::Le, rhs, lhs, env);
            }
            ChcOp::Gt => {
                return Self::collect_direct_interval_bound(ChcOp::Lt, rhs, lhs, env);
            }
            _ => {}
        }
        true
    }

    fn add_interval_bound(
        env: &mut FxHashMap<String, IntInterval>,
        name: &str,
        interval: IntInterval,
    ) -> bool {
        Self::add_interval_bound_changed(env, name, interval).is_some()
    }

    fn add_interval_bound_changed(
        env: &mut FxHashMap<String, IntInterval>,
        name: &str,
        interval: IntInterval,
    ) -> Option<bool> {
        let merged = env
            .get(name)
            .copied()
            .map_or(interval, |current| current.intersect(interval));
        if merged.is_empty() {
            return None;
        }
        if env.get(name).copied() == Some(merged) {
            return Some(false);
        }
        env.insert(name.to_string(), merged);
        Some(true)
    }

    fn int_var_name(expr: &ChcExpr) -> Option<&str> {
        match expr {
            ChcExpr::Var(var) if var.sort == ChcSort::Int => Some(var.name.as_str()),
            _ => None,
        }
    }

    fn expr_literal_int_interval(expr: &ChcExpr) -> Option<IntInterval> {
        expr.as_i128().map(IntInterval::exact)
    }

    fn expr_int_interval(
        expr: &ChcExpr,
        env: &FxHashMap<String, IntInterval>,
    ) -> Option<IntInterval> {
        match expr {
            ChcExpr::Int(value) => Some(IntInterval::exact(*value)),
            ChcExpr::Var(var) if var.sort == ChcSort::Int => {
                Some(env.get(&var.name).copied().unwrap_or_else(IntInterval::top))
            }
            ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                Some(Self::expr_int_interval(args[0].as_ref(), env)?.checked_neg())
            }
            ChcExpr::Op(ChcOp::Add, args) if !args.is_empty() => {
                let mut interval = IntInterval::exact(0);
                for arg in args {
                    interval = interval.checked_add(Self::expr_int_interval(arg.as_ref(), env)?);
                }
                Some(interval)
            }
            ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
                let mut iter = args.iter();
                let first = Self::expr_int_interval(iter.next()?.as_ref(), env)?;
                if args.len() == 1 {
                    return Some(first.checked_neg());
                }
                let mut interval = first;
                for arg in iter {
                    interval = interval.checked_sub(Self::expr_int_interval(arg.as_ref(), env)?);
                }
                Some(interval)
            }
            ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
                if let Some(factor) = args[0].as_i128() {
                    return Some(
                        Self::expr_int_interval(args[1].as_ref(), env)?.checked_scale(factor),
                    );
                }
                if let Some(factor) = args[1].as_i128() {
                    return Some(
                        Self::expr_int_interval(args[0].as_ref(), env)?.checked_scale(factor),
                    );
                }
                Some(IntInterval::top())
            }
            _ if matches!(expr.sort(), ChcSort::Int) => Some(IntInterval::top()),
            _ => None,
        }
    }

    fn linearize_bounded_squares_in_conjuncts(
        conjuncts: &mut Vec<ChcExpr>,
        env: &FxHashMap<String, IntInterval>,
    ) -> usize {
        let square_defs: Vec<_> = conjuncts
            .iter()
            .filter_map(|conjunct| Self::bounded_square_definition(conjunct, env))
            .collect();
        let mut replacements = FxHashMap::default();
        for square_def in &square_defs {
            replacements.insert(
                square_def.square.clone(),
                ChcExpr::var(square_def.product.clone()),
            );
        }

        let mut standalone_square_defs = Vec::new();
        let existing_vars: FxHashSet<_> = conjuncts
            .iter()
            .flat_map(ChcExpr::vars)
            .map(|var| var.name)
            .collect();
        let mut seen_standalone = FxHashSet::default();
        for conjunct in conjuncts.iter() {
            Self::collect_bounded_square_terms(conjunct, env, &mut seen_standalone);
        }
        let mut aux_idx = 0usize;
        for square in seen_standalone {
            if replacements.contains_key(&square) {
                continue;
            }
            let Some(input) = Self::square_input_var(&square) else {
                continue;
            };
            let Some(interval) = env.get(&input.name).copied() else {
                continue;
            };
            if interval.bounded_nonnegative_square_domain().is_none() {
                continue;
            }
            let product = loop {
                let name = format!("__bmc_square_lia_aux_{aux_idx}");
                aux_idx += 1;
                if !existing_vars.contains(&name) {
                    break ChcVar::new(name, ChcSort::Int);
                }
            };
            replacements.insert(square.clone(), ChcExpr::var(product.clone()));
            standalone_square_defs.push(BoundedSquareDefinition {
                product,
                input,
                square,
                interval,
            });
        }

        if square_defs.is_empty() && standalone_square_defs.is_empty() {
            return 0;
        }

        let old = std::mem::take(conjuncts);
        let mut out =
            Vec::with_capacity(old.len() + square_defs.len() + standalone_square_defs.len());
        for square_def in &standalone_square_defs {
            out.extend(Self::bounded_square_lia_envelope(square_def));
        }
        let mut count = 0usize;
        for conjunct in old {
            if let Some(square_def) = Self::bounded_square_definition(&conjunct, env) {
                out.extend(Self::bounded_square_lia_envelope(&square_def));
                count += 1;
            } else {
                out.push(Self::simplify_bmc_expr(Self::replace_exprs(
                    &conjunct,
                    &replacements,
                )));
            }
        }
        *conjuncts = out;
        count + standalone_square_defs.len()
    }

    fn simplify_exact_acyclic_conjuncts(conjuncts: Vec<ChcExpr>) -> ChcExpr {
        // Exact-path lane: no deadline threaded here (`None` can never yield
        // `Err`), so only a definitive `Ok(false)` infeasibility answer may
        // poison the conjuncts to `false`.
        let infeasible = |conjuncts: &[ChcExpr], env: &mut FxHashMap<String, IntInterval>| {
            matches!(
                Self::collect_conjunct_interval_bounds(conjuncts, env, None),
                Ok(false)
            )
        };
        let mut conjuncts = ChcExpr::and_all(conjuncts)
            .propagate_equalities()
            .collect_conjuncts_nontrivial();
        let mut interval_env = FxHashMap::default();
        if infeasible(&conjuncts, &mut interval_env) {
            return ChcExpr::Bool(false);
        }
        let _ = Self::substitute_exact_interval_values(&mut conjuncts, &interval_env);
        if infeasible(&conjuncts, &mut interval_env) {
            return ChcExpr::Bool(false);
        }

        let _ = Self::linearize_bounded_squares_in_conjuncts(&mut conjuncts, &interval_env);
        if infeasible(&conjuncts, &mut interval_env) {
            return ChcExpr::Bool(false);
        }
        let _ = Self::substitute_exact_interval_values(&mut conjuncts, &interval_env);
        if infeasible(&conjuncts, &mut interval_env) {
            return ChcExpr::Bool(false);
        }

        let local_bool_vars = conjuncts
            .iter()
            .flat_map(ChcExpr::vars)
            .filter(|var| var.sort == ChcSort::Bool)
            .map(|var| var.name)
            .collect();
        let _ = Self::simplify_conjuncts_with_intervals_and_bools(
            &mut conjuncts,
            &mut interval_env,
            &local_bool_vars,
            None,
        );
        let _ = Self::substitute_exact_interval_values(&mut conjuncts, &interval_env);
        if conjuncts.len() <= 512 {
            let _ = Self::substitute_definitional_equalities(&mut conjuncts);
        }
        ChcExpr::and_all(conjuncts).propagate_equalities()
    }

    fn substitute_exact_interval_values(
        conjuncts: &mut Vec<ChcExpr>,
        env: &FxHashMap<String, IntInterval>,
    ) -> usize {
        let subst: FxHashMap<String, ChcExpr> = env
            .iter()
            .filter_map(|(name, interval)| match (interval.lower, interval.upper) {
                (Some(lower), Some(upper)) if lower == upper => {
                    Some((name.clone(), ChcExpr::Int(lower)))
                }
                _ => None,
            })
            .collect();
        if subst.is_empty() {
            return 0;
        }

        let old = std::mem::take(conjuncts);
        let mut changed = 0usize;
        let mut out = Vec::with_capacity(old.len());
        for conjunct in old {
            let simplified = Self::simplify_bmc_expr(conjunct.substitute_name_map(&subst));
            if simplified != conjunct {
                changed += 1;
            }
            match simplified {
                ChcExpr::Bool(true) => {}
                ChcExpr::Bool(false) => {
                    conjuncts.clear();
                    conjuncts.push(ChcExpr::Bool(false));
                    return changed;
                }
                other => out.push(other),
            }
        }
        *conjuncts = out;
        changed
    }

    fn substitute_definitional_equalities(conjuncts: &mut Vec<ChcExpr>) -> usize {
        let max_rounds = conjuncts.len().saturating_add(1).min(1024);
        let mut total_changed = 0usize;

        for _ in 0..max_rounds {
            let subst = Self::collect_definitional_substitutions(conjuncts);
            if subst.is_empty() {
                break;
            }

            let old = std::mem::take(conjuncts);
            let mut out = Vec::with_capacity(old.len());
            let mut changed = false;
            for conjunct in old {
                let substituted = Self::simplify_bmc_expr(conjunct.substitute_name_map(&subst));
                if substituted != conjunct {
                    changed = true;
                    total_changed += 1;
                }
                match substituted {
                    ChcExpr::Bool(true) => {}
                    ChcExpr::Bool(false) => {
                        conjuncts.clear();
                        conjuncts.push(ChcExpr::Bool(false));
                        return total_changed;
                    }
                    other => out.push(other),
                }
            }
            *conjuncts = out;
            if !changed {
                break;
            }
        }

        total_changed
    }

    fn collect_definitional_substitutions(conjuncts: &[ChcExpr]) -> FxHashMap<String, ChcExpr> {
        let mut candidates: FxHashMap<String, Option<ChcExpr>> = FxHashMap::default();

        for conjunct in conjuncts {
            let simplified = Self::simplify_bmc_expr(conjunct.clone());
            let ChcExpr::Op(ChcOp::Eq, args) = &simplified else {
                continue;
            };
            if args.len() != 2 {
                continue;
            }
            let Some((name, expr)) =
                Self::orient_definitional_equality(args[0].as_ref(), args[1].as_ref())
            else {
                continue;
            };
            if Self::expr_mentions_var(&expr, &name) || expr.node_count(4096) >= 4096 {
                continue;
            }
            match candidates.get_mut(&name) {
                Some(slot) if slot.as_ref() == Some(&expr) => {}
                Some(slot) => *slot = None,
                None => {
                    candidates.insert(name, Some(expr));
                }
            }
        }

        let mut subst: FxHashMap<String, ChcExpr> = candidates
            .into_iter()
            .filter_map(|(name, expr)| expr.map(|expr| (name, expr)))
            .collect();
        let keys: Vec<_> = subst.keys().cloned().collect();
        for name in keys {
            let remove = subst
                .get(&name)
                .is_some_and(|expr| Self::substitution_depends_on(&name, expr, &subst));
            if remove {
                subst.remove(&name);
            }
        }
        subst
    }

    fn orient_definitional_equality(lhs: &ChcExpr, rhs: &ChcExpr) -> Option<(String, ChcExpr)> {
        match (lhs, rhs) {
            (ChcExpr::Var(lhs_var), ChcExpr::Var(rhs_var)) if lhs_var.sort == rhs_var.sort => {
                if lhs_var.name == rhs_var.name {
                    None
                } else {
                    let (name, expr) = Self::orient_var_var_definition(lhs_var, rhs_var)?;
                    Some((name, expr))
                }
            }
            (ChcExpr::Var(var), other)
                if var.sort == other.sort() && Self::can_orient_var_to_expr(var, other) =>
            {
                Some((var.name.clone(), other.clone()))
            }
            (other, ChcExpr::Var(var))
                if var.sort == other.sort() && Self::can_orient_var_to_expr(var, other) =>
            {
                Some((var.name.clone(), other.clone()))
            }
            _ => None,
        }
    }

    fn orient_var_var_definition(lhs: &ChcVar, rhs: &ChcVar) -> Option<(String, ChcExpr)> {
        match (
            Self::fresh_expansion_id(&lhs.name),
            Self::fresh_expansion_id(&rhs.name),
        ) {
            (Some(lhs_id), Some(rhs_id)) if lhs_id > rhs_id => {
                Some((lhs.name.clone(), ChcExpr::var(rhs.clone())))
            }
            (Some(lhs_id), Some(rhs_id)) if rhs_id > lhs_id => {
                Some((rhs.name.clone(), ChcExpr::var(lhs.clone())))
            }
            (Some(_), None) => Some((lhs.name.clone(), ChcExpr::var(rhs.clone()))),
            (None, Some(_)) => Some((rhs.name.clone(), ChcExpr::var(lhs.clone()))),
            _ if lhs.name > rhs.name => Some((lhs.name.clone(), ChcExpr::var(rhs.clone()))),
            _ if rhs.name > lhs.name => Some((rhs.name.clone(), ChcExpr::var(lhs.clone()))),
            _ => None,
        }
    }

    fn can_orient_var_to_expr(var: &ChcVar, expr: &ChcExpr) -> bool {
        let var_id = Self::fresh_expansion_id(&var.name);
        for dep in expr.vars() {
            if dep.name == var.name {
                return false;
            }
            let dep_id = Self::fresh_expansion_id(&dep.name);
            match (var_id, dep_id) {
                (Some(var_id), Some(dep_id)) if dep_id > var_id => return false,
                (None, Some(_)) => return false,
                _ => {}
            }
        }
        true
    }

    fn fresh_expansion_id(name: &str) -> Option<usize> {
        let rest = name.strip_prefix("__bmc_dag_e")?;
        let (id, _) = rest.split_once("_v")?;
        id.parse().ok()
    }

    fn expr_mentions_var(expr: &ChcExpr, name: &str) -> bool {
        expr.vars().iter().any(|var| var.name == name)
    }

    fn substitution_depends_on(
        name: &str,
        expr: &ChcExpr,
        subst: &FxHashMap<String, ChcExpr>,
    ) -> bool {
        let mut visiting = FxHashSet::default();
        Self::substitution_depends_on_inner(name, expr, subst, &mut visiting)
    }

    fn substitution_depends_on_inner(
        name: &str,
        expr: &ChcExpr,
        subst: &FxHashMap<String, ChcExpr>,
        visiting: &mut FxHashSet<String>,
    ) -> bool {
        for var in expr.vars() {
            if var.name == name {
                return true;
            }
            if let Some(next) = subst.get(&var.name) {
                if visiting.insert(var.name.clone()) {
                    if Self::substitution_depends_on_inner(name, next, subst, visiting) {
                        return true;
                    }
                    visiting.remove(&var.name);
                }
            }
        }
        false
    }

    /// Pure fixpoint simplifier: every completed rewrite is
    /// semantics-preserving, so on `deadline` expiry it simply stops early
    /// and returns — the current conjunct set is valid as-is (model-checker-consumer
    /// wishlist item 3). Expiry is never treated as infeasibility.
    fn simplify_conjuncts_with_intervals_and_bools(
        conjuncts: &mut Vec<ChcExpr>,
        env: &mut FxHashMap<String, IntInterval>,
        local_bool_vars: &FxHashSet<String>,
        deadline: Option<ay_core::time::Instant>,
    ) -> usize {
        let mut bool_values = FxHashMap::default();
        let mut total_changed = 0usize;
        // Constant round cap (model-checker-consumer wishlist item 3), mirroring
        // `collect_conjunct_interval_bounds`: the previous
        // `conjuncts.len() + 4` bound made this loop O(n²) in conjuncts —
        // the single worst unbounded phase of the polynomial-DAG encoding.
        // Semantics-preserving: the loop is a pure simplifier with a
        // fixpoint break; fewer rounds only leave conjuncts less simplified.
        let max_rounds = conjuncts.len().saturating_add(4).clamp(1, 32);

        for _ in 0..max_rounds {
            if dag_deadline_passed(deadline) {
                break;
            }
            if !Self::collect_bool_constants(conjuncts, local_bool_vars, &mut bool_values) {
                conjuncts.clear();
                conjuncts.push(ChcExpr::Bool(false));
                return total_changed + 1;
            }

            let subst: FxHashMap<String, ChcExpr> = bool_values
                .iter()
                .map(|(name, value)| (name.clone(), ChcExpr::Bool(*value)))
                .collect();
            let old = std::mem::take(conjuncts);
            let mut out = Vec::with_capacity(old.len());
            let mut round_changed = false;

            for conjunct in old {
                let substituted = if subst.is_empty() {
                    conjunct.clone()
                } else {
                    conjunct.substitute_name_map(&subst)
                };
                let simplified = Self::simplify_interval_expr(&substituted, env);
                if simplified != conjunct {
                    total_changed += 1;
                    round_changed = true;
                }
                match simplified {
                    ChcExpr::Bool(false) => {
                        conjuncts.clear();
                        conjuncts.push(ChcExpr::Bool(false));
                        return total_changed;
                    }
                    ChcExpr::Bool(true) => {
                        round_changed = true;
                    }
                    other => out.push(other),
                }
            }

            *conjuncts = out;
            match Self::collect_conjunct_interval_bounds(conjuncts, env, deadline) {
                // Deadline expired mid-collection: stop simplifying with the
                // current (valid) conjunct set — never poison on expiry.
                Err(DagBudgetExpired) => break,
                Ok(false) => {
                    conjuncts.clear();
                    conjuncts.push(ChcExpr::Bool(false));
                    return total_changed + 1;
                }
                Ok(true) => {}
            }
            let before_bool_count = bool_values.len();
            if !Self::collect_bool_constants(conjuncts, local_bool_vars, &mut bool_values) {
                conjuncts.clear();
                conjuncts.push(ChcExpr::Bool(false));
                return total_changed + 1;
            }
            if !round_changed && bool_values.len() == before_bool_count {
                break;
            }
        }

        total_changed
    }

    fn collect_bool_constants(
        conjuncts: &[ChcExpr],
        local_bool_vars: &FxHashSet<String>,
        values: &mut FxHashMap<String, bool>,
    ) -> bool {
        for conjunct in conjuncts {
            if !Self::collect_bool_constant(conjunct, local_bool_vars, values) {
                return false;
            }
        }
        true
    }

    fn collect_bool_constant(
        conjunct: &ChcExpr,
        local_bool_vars: &FxHashSet<String>,
        values: &mut FxHashMap<String, bool>,
    ) -> bool {
        match conjunct {
            ChcExpr::Var(var)
                if var.sort == ChcSort::Bool && local_bool_vars.contains(&var.name) =>
            {
                Self::add_bool_constant(values, &var.name, true)
            }
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                if let ChcExpr::Var(var) = args[0].as_ref() {
                    if var.sort == ChcSort::Bool && local_bool_vars.contains(&var.name) {
                        return Self::add_bool_constant(values, &var.name, false);
                    }
                }
                true
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                Self::collect_bool_constant_equality(
                    args[0].as_ref(),
                    args[1].as_ref(),
                    local_bool_vars,
                    values,
                ) && Self::collect_bool_constant_equality(
                    args[1].as_ref(),
                    args[0].as_ref(),
                    local_bool_vars,
                    values,
                )
            }
            _ => true,
        }
    }

    fn collect_bool_constant_equality(
        candidate: &ChcExpr,
        other: &ChcExpr,
        local_bool_vars: &FxHashSet<String>,
        values: &mut FxHashMap<String, bool>,
    ) -> bool {
        let ChcExpr::Var(var) = candidate else {
            return true;
        };
        if var.sort != ChcSort::Bool || !local_bool_vars.contains(&var.name) {
            return true;
        }
        let ChcExpr::Bool(value) = other else {
            return true;
        };
        Self::add_bool_constant(values, &var.name, *value)
    }

    fn add_bool_constant(values: &mut FxHashMap<String, bool>, name: &str, value: bool) -> bool {
        match values.get(name) {
            Some(current) => *current == value,
            None => {
                values.insert(name.to_string(), value);
                true
            }
        }
    }

    fn simplify_interval_expr(expr: &ChcExpr, env: &FxHashMap<String, IntInterval>) -> ChcExpr {
        match expr {
            ChcExpr::Op(op, args) => {
                let simplified_args: Vec<_> = args
                    .iter()
                    .map(|arg| Self::simplify_interval_expr(arg.as_ref(), env))
                    .collect();

                match op {
                    ChcOp::Not if simplified_args.len() == 1 => match &simplified_args[0] {
                        ChcExpr::Bool(value) => ChcExpr::Bool(!value),
                        other => Self::simplify_bmc_expr(ChcExpr::not(other.clone())),
                    },
                    ChcOp::And => ChcExpr::and_all(simplified_args),
                    ChcOp::Or => ChcExpr::or_all(simplified_args),
                    ChcOp::Implies if simplified_args.len() == 2 => {
                        Self::simplify_bmc_expr(ChcExpr::or(
                            ChcExpr::not(simplified_args[0].clone()),
                            simplified_args[1].clone(),
                        ))
                    }
                    ChcOp::Eq if simplified_args.len() == 2 => {
                        if let Some(value) = Self::interval_compare_result(
                            ChcOp::Eq,
                            &simplified_args[0],
                            &simplified_args[1],
                            env,
                        ) {
                            return ChcExpr::Bool(value);
                        }
                        Self::simplify_bool_equality(
                            simplified_args[0].clone(),
                            simplified_args[1].clone(),
                            false,
                        )
                    }
                    ChcOp::Ne if simplified_args.len() == 2 => {
                        if let Some(value) = Self::interval_compare_result(
                            ChcOp::Ne,
                            &simplified_args[0],
                            &simplified_args[1],
                            env,
                        ) {
                            return ChcExpr::Bool(value);
                        }
                        Self::simplify_bool_equality(
                            simplified_args[0].clone(),
                            simplified_args[1].clone(),
                            true,
                        )
                    }
                    ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge if simplified_args.len() == 2 => {
                        if let Some(value) = Self::interval_compare_result(
                            *op,
                            &simplified_args[0],
                            &simplified_args[1],
                            env,
                        ) {
                            ChcExpr::Bool(value)
                        } else {
                            Self::simplify_bmc_expr(ChcExpr::Op(
                                *op,
                                simplified_args.into_iter().map(Arc::new).collect(),
                            ))
                        }
                    }
                    ChcOp::Ite if simplified_args.len() == 3 => match &simplified_args[0] {
                        ChcExpr::Bool(true) => simplified_args[1].clone(),
                        ChcExpr::Bool(false) => simplified_args[2].clone(),
                        _ => Self::simplify_bmc_expr(ChcExpr::Op(
                            *op,
                            simplified_args.into_iter().map(Arc::new).collect(),
                        )),
                    },
                    _ => Self::simplify_bmc_expr(ChcExpr::Op(
                        *op,
                        simplified_args.into_iter().map(Arc::new).collect(),
                    )),
                }
            }
            ChcExpr::PredicateApp(name, pred, args) => ChcExpr::PredicateApp(
                name.clone(),
                *pred,
                args.iter()
                    .map(|arg| Arc::new(Self::simplify_interval_expr(arg.as_ref(), env)))
                    .collect(),
            ),
            ChcExpr::FuncApp(name, sort, args) => ChcExpr::FuncApp(
                name.clone(),
                sort.clone(),
                args.iter()
                    .map(|arg| Arc::new(Self::simplify_interval_expr(arg.as_ref(), env)))
                    .collect(),
            ),
            ChcExpr::ConstArray(key_sort, value) => ChcExpr::ConstArray(
                key_sort.clone(),
                Arc::new(Self::simplify_interval_expr(value.as_ref(), env)),
            ),
            other => other.clone(),
        }
    }

    fn simplify_bool_equality(lhs: ChcExpr, rhs: ChcExpr, negated: bool) -> ChcExpr {
        let result = match (lhs, rhs) {
            (ChcExpr::Bool(a), ChcExpr::Bool(b)) => ChcExpr::Bool(a == b),
            (ChcExpr::Bool(true), other) | (other, ChcExpr::Bool(true)) => other,
            (ChcExpr::Bool(false), other) | (other, ChcExpr::Bool(false)) => ChcExpr::not(other),
            (a, b) => Self::simplify_bmc_expr(ChcExpr::eq(a, b)),
        };
        if negated {
            Self::simplify_bmc_expr(ChcExpr::not(result))
        } else {
            Self::simplify_bmc_expr(result)
        }
    }

    fn interval_compare_result(
        op: ChcOp,
        lhs: &ChcExpr,
        rhs: &ChcExpr,
        env: &FxHashMap<String, IntInterval>,
    ) -> Option<bool> {
        let lhs_interval = Self::expr_int_interval(lhs, env)?;
        let rhs_interval = Self::expr_int_interval(rhs, env)?;
        match op {
            ChcOp::Lt => {
                if lhs_interval.upper? < rhs_interval.lower? {
                    Some(true)
                } else if lhs_interval.lower? >= rhs_interval.upper? {
                    Some(false)
                } else {
                    None
                }
            }
            ChcOp::Le => {
                if lhs_interval.upper? <= rhs_interval.lower? {
                    Some(true)
                } else if lhs_interval.lower? > rhs_interval.upper? {
                    Some(false)
                } else {
                    None
                }
            }
            ChcOp::Gt => {
                if lhs_interval.lower? > rhs_interval.upper? {
                    Some(true)
                } else if lhs_interval.upper? <= rhs_interval.lower? {
                    Some(false)
                } else {
                    None
                }
            }
            ChcOp::Ge => {
                if lhs_interval.lower? >= rhs_interval.upper? {
                    Some(true)
                } else if lhs_interval.upper? < rhs_interval.lower? {
                    Some(false)
                } else {
                    None
                }
            }
            ChcOp::Eq => {
                if lhs_interval.lower == lhs_interval.upper
                    && lhs_interval.lower == rhs_interval.lower
                    && rhs_interval.lower == rhs_interval.upper
                {
                    Some(true)
                } else if lhs_interval.upper? < rhs_interval.lower?
                    || rhs_interval.upper? < lhs_interval.lower?
                {
                    Some(false)
                } else {
                    None
                }
            }
            ChcOp::Ne => {
                if lhs_interval.lower == lhs_interval.upper
                    && lhs_interval.lower == rhs_interval.lower
                    && rhs_interval.lower == rhs_interval.upper
                {
                    Some(false)
                } else if lhs_interval.upper? < rhs_interval.lower?
                    || rhs_interval.upper? < lhs_interval.lower?
                {
                    Some(true)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn collect_bounded_square_terms(
        expr: &ChcExpr,
        env: &FxHashMap<String, IntInterval>,
        out: &mut FxHashSet<ChcExpr>,
    ) {
        if let Some(input) = Self::square_input_var(expr) {
            if env
                .get(&input.name)
                .copied()
                .and_then(IntInterval::bounded_nonnegative_square_domain)
                .is_some()
            {
                out.insert(expr.clone());
                return;
            }
        }

        match expr {
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => {
                for arg in args {
                    Self::collect_bounded_square_terms(arg.as_ref(), env, out);
                }
            }
            ChcExpr::ConstArray(_, value) => {
                Self::collect_bounded_square_terms(value.as_ref(), env, out);
            }
            _ => {}
        }
    }

    fn bounded_square_definition(
        conjunct: &ChcExpr,
        env: &FxHashMap<String, IntInterval>,
    ) -> Option<BoundedSquareDefinition> {
        let ChcExpr::Op(ChcOp::Eq, args) = conjunct else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }
        Self::bounded_square_definition_sides(args[0].as_ref(), args[1].as_ref(), env).or_else(
            || Self::bounded_square_definition_sides(args[1].as_ref(), args[0].as_ref(), env),
        )
    }

    fn bounded_square_definition_sides(
        product: &ChcExpr,
        square: &ChcExpr,
        env: &FxHashMap<String, IntInterval>,
    ) -> Option<BoundedSquareDefinition> {
        let ChcExpr::Var(product_var) = product else {
            return None;
        };
        if product_var.sort != ChcSort::Int {
            return None;
        }
        let input = Self::square_input_var(square)?;
        let interval = env.get(&input.name).copied()?;
        interval.bounded_nonnegative_square_domain()?;
        Some(BoundedSquareDefinition {
            product: product_var.clone(),
            input,
            square: square.clone(),
            interval,
        })
    }

    fn square_input_var(expr: &ChcExpr) -> Option<ChcVar> {
        let ChcExpr::Op(ChcOp::Mul, args) = expr else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }
        let (ChcExpr::Var(lhs), ChcExpr::Var(rhs)) = (args[0].as_ref(), args[1].as_ref()) else {
            return None;
        };
        if lhs == rhs && lhs.sort == ChcSort::Int {
            Some(lhs.clone())
        } else {
            None
        }
    }

    fn bounded_square_lia_envelope(square_def: &BoundedSquareDefinition) -> Vec<ChcExpr> {
        let (lower, upper) = square_def
            .interval
            .bounded_nonnegative_square_domain()
            .expect("bounded square definition should have a finite nonnegative interval");
        let product = ChcExpr::var(square_def.product.clone());
        let input = ChcExpr::var(square_def.input.clone());
        let mut constraints = Vec::with_capacity((upper - lower + 3) as usize);
        constraints.push(ChcExpr::ge(product.clone(), ChcExpr::int(0)));
        constraints.push(ChcExpr::le(
            product.clone(),
            ChcExpr::int(upper.saturating_mul(upper)),
        ));
        for tangent in lower..=upper {
            let slope = tangent.saturating_mul(2);
            let intercept = tangent.saturating_mul(tangent);
            let tangent_expr = ChcExpr::sub(
                ChcExpr::mul(ChcExpr::int(slope), input.clone()),
                ChcExpr::int(intercept),
            );
            constraints.push(ChcExpr::ge(product.clone(), tangent_expr));
        }
        constraints
            .into_iter()
            .map(Self::simplify_bmc_expr)
            .collect()
    }

    fn replace_exprs(expr: &ChcExpr, replacements: &FxHashMap<ChcExpr, ChcExpr>) -> ChcExpr {
        if let Some(replacement) = replacements.get(expr) {
            return replacement.clone();
        }
        match expr {
            ChcExpr::Op(op, args) => ChcExpr::Op(
                *op,
                args.iter()
                    .map(|arg| Arc::new(Self::replace_exprs(arg.as_ref(), replacements)))
                    .collect(),
            ),
            ChcExpr::PredicateApp(name, pred, args) => ChcExpr::PredicateApp(
                name.clone(),
                *pred,
                args.iter()
                    .map(|arg| Arc::new(Self::replace_exprs(arg.as_ref(), replacements)))
                    .collect(),
            ),
            ChcExpr::FuncApp(name, sort, args) => ChcExpr::FuncApp(
                name.clone(),
                sort.clone(),
                args.iter()
                    .map(|arg| Arc::new(Self::replace_exprs(arg.as_ref(), replacements)))
                    .collect(),
            ),
            ChcExpr::ConstArray(key_sort, value) => ChcExpr::ConstArray(
                key_sort.clone(),
                Arc::new(Self::replace_exprs(value.as_ref(), replacements)),
            ),
            other => other.clone(),
        }
    }

    #[cfg(test)]
    pub(crate) fn linearize_bounded_square_conjuncts_for_test(
        conjuncts: &mut Vec<ChcExpr>,
        bounds: &[(&str, i128, i128)],
    ) -> usize {
        let mut env = FxHashMap::default();
        for (name, lower, upper) in bounds {
            env.insert(
                (*name).to_string(),
                IntInterval {
                    lower: Some(*lower),
                    upper: Some(*upper),
                },
            );
        }
        Self::linearize_bounded_squares_in_conjuncts(conjuncts, &env)
    }

    #[cfg(test)]
    pub(crate) fn linearize_and_simplify_bounded_square_conjuncts_for_test(
        conjuncts: &mut Vec<ChcExpr>,
        bounds: &[(&str, i128, i128)],
    ) -> (usize, usize) {
        let mut env = FxHashMap::default();
        for (name, lower, upper) in bounds {
            env.insert(
                (*name).to_string(),
                IntInterval {
                    lower: Some(*lower),
                    upper: Some(*upper),
                },
            );
        }
        let linearized = Self::linearize_bounded_squares_in_conjuncts(conjuncts, &env);
        let _ = Self::collect_conjunct_interval_bounds(conjuncts, &mut env, None);
        let local_bool_vars = conjuncts
            .iter()
            .flat_map(ChcExpr::vars)
            .filter(|var| var.sort == ChcSort::Bool)
            .map(|var| var.name)
            .collect();
        let simplified = Self::simplify_conjuncts_with_intervals_and_bools(
            conjuncts,
            &mut env,
            &local_bool_vars,
            None,
        );
        (linearized, simplified)
    }

    /// Returns `Err(DagBudgetExpired)` when `deadline` expires mid-fixpoint;
    /// the caller must bail to `Unknown` (model-checker-consumer wishlist item 3). Partial
    /// entries are individually justified, but bailing uniformly is simpler
    /// and obviously sound.
    fn infer_acyclic_dag_arg_constants(
        &self,
        ordered_cone: &[PredicateId],
        defs_by_head: &FxHashMap<PredicateId, Vec<usize>>,
        deadline: ay_core::time::Instant,
    ) -> Result<FxHashMap<(PredicateId, usize), ChcExpr>, DagBudgetExpired> {
        let mut constants: FxHashMap<(PredicateId, usize), ChcExpr> = FxHashMap::default();

        for _ in 0..=ordered_cone.len() {
            let mut changed = false;
            for pred in ordered_cone {
                // Budget compliance: poll once per predicate per round —
                // each cell below substitutes + simplifies every defining
                // clause's head arg.
                if self.dag_deadline_expired(deadline) {
                    return Err(DagBudgetExpired);
                }
                let Some(pred_info) = self.problem.get_predicate(*pred) else {
                    continue;
                };
                for arg_idx in 0..pred_info.arg_sorts.len() {
                    let Some(candidate) =
                        self.infer_pred_arg_constant(*pred, arg_idx, defs_by_head, &constants)
                    else {
                        continue;
                    };
                    if constants.get(&(*pred, arg_idx)) != Some(&candidate) {
                        constants.insert((*pred, arg_idx), candidate);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }

        Ok(constants)
    }

    fn infer_pred_arg_constant(
        &self,
        pred: PredicateId,
        arg_idx: usize,
        defs_by_head: &FxHashMap<PredicateId, Vec<usize>>,
        constants: &FxHashMap<(PredicateId, usize), ChcExpr>,
    ) -> Option<ChcExpr> {
        let mut candidate: Option<ChcExpr> = None;
        let mut saw_definition = false;

        for clause_idx in defs_by_head.get(&pred).into_iter().flatten() {
            let clause = &self.problem.clauses()[*clause_idx];
            let ClauseHead::Predicate(_, head_args) = &clause.head else {
                continue;
            };
            let head_arg = head_args.get(arg_idx)?;
            let mut subst = Self::local_ground_equalities(clause.body.constraint.as_ref());
            for (body_pred, body_args) in &clause.body.predicates {
                for (body_arg_idx, body_arg) in body_args.iter().enumerate() {
                    let Some(value) = constants.get(&(*body_pred, body_arg_idx)) else {
                        continue;
                    };
                    if let ChcExpr::Var(var) = body_arg {
                        subst
                            .entry(var.name.clone())
                            .or_insert_with(|| value.clone());
                    }
                }
            }

            let value = Self::simplify_bmc_expr(head_arg.substitute_name_map(&subst));
            if !value.vars().is_empty() {
                return None;
            }
            if candidate.as_ref().is_some_and(|current| current != &value) {
                return None;
            }
            candidate = Some(value);
            saw_definition = true;
        }

        saw_definition.then_some(candidate).flatten()
    }

    fn local_ground_equalities(constraint: Option<&ChcExpr>) -> FxHashMap<String, ChcExpr> {
        let mut equalities = FxHashMap::default();
        let Some(constraint) = constraint else {
            return equalities;
        };
        for conjunct in constraint.collect_conjuncts_nontrivial() {
            if let Some((name, value)) = Self::ground_var_equality(&conjunct) {
                equalities.entry(name).or_insert(value);
            }
        }
        equalities
    }

    fn ground_var_equality(expr: &ChcExpr) -> Option<(String, ChcExpr)> {
        let ChcExpr::Op(crate::ChcOp::Eq, args) = expr else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }
        Self::ground_var_equality_side(args[0].as_ref(), args[1].as_ref())
            .or_else(|| Self::ground_var_equality_side(args[1].as_ref(), args[0].as_ref()))
    }

    fn ground_var_equality_side(candidate: &ChcExpr, other: &ChcExpr) -> Option<(String, ChcExpr)> {
        let ChcExpr::Var(var) = candidate else {
            return None;
        };
        let value = Self::simplify_bmc_expr(other.clone());
        value.vars().is_empty().then(|| (var.name.clone(), value))
    }

    fn solve_acyclic_cone_level_flat_once(
        &self,
        queries: &[&HornClause],
        max_depth: usize,
        defs_by_head: &FxHashMap<PredicateId, Vec<usize>>,
    ) -> ChcEngineResult {
        let start = ay_core::time::Instant::now();
        let timeout = self
            .config
            .time_budget
            .unwrap_or_else(|| std::time::Duration::from_secs(30));
        let deadline = self.lane_deadline(start, timeout);

        let cone = self.query_dependency_cone(queries, defs_by_head);
        if cone.is_empty() {
            self.mark_acyclic_exhaustive_stats(max_depth, start.elapsed().as_secs_f64());
            return ChcEngineResult::Safe(InvariantModel::default());
        }
        let reachable_levels = self.reachable_levels_by_pred(max_depth, &cone, defs_by_head);

        let mut conjuncts = Vec::new();
        for level in 0..=max_depth {
            if ay_core::time::Instant::now() >= deadline || self.config.base.is_cancelled() {
                self.stats.borrow_mut().budget_exhausted = true;
                return ChcEngineResult::Unknown;
            }
            self.compile_level_flat_cone(
                level,
                &cone,
                &reachable_levels,
                defs_by_head,
                &mut conjuncts,
            );
        }

        let mut query_disjuncts = Vec::new();
        for level in 0..=max_depth {
            for query in queries {
                if !query.body.predicates.iter().all(|(pred, _)| {
                    reachable_levels
                        .get(pred)
                        .is_some_and(|levels| levels.contains(&level))
                }) {
                    continue;
                }
                let mut query_conjuncts = Vec::new();
                self.compile_query(query, level, &mut query_conjuncts);
                if !query_conjuncts.is_empty() {
                    query_disjuncts.push(ChcExpr::and_all(query_conjuncts));
                }
            }
        }
        if query_disjuncts.is_empty() {
            self.mark_acyclic_exhaustive_stats(max_depth, start.elapsed().as_secs_f64());
            return ChcEngineResult::Safe(InvariantModel::default());
        }
        conjuncts.push(if query_disjuncts.len() == 1 {
            query_disjuncts.remove(0)
        } else {
            ChcExpr::or_all(query_disjuncts)
        });

        let formula = ChcExpr::and_all(conjuncts);
        let remaining = deadline.saturating_duration_since(ay_core::time::Instant::now());
        if remaining.is_zero() {
            self.stats.borrow_mut().budget_exhausted = true;
            return ChcEngineResult::Unknown;
        }
        let mut smt = self.problem.make_smt_context();
        match smt.check_sat_with_timeout(&formula, remaining) {
            result if result.is_unsat() => {
                self.mark_acyclic_exhaustive_stats(max_depth, start.elapsed().as_secs_f64());
                ChcEngineResult::Safe(InvariantModel::default())
            }
            SmtResult::Sat(_) | SmtResult::Unknown => {
                self.record_depth(max_depth, start.elapsed().as_secs_f64());
                ChcEngineResult::Unknown
            }
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                unreachable!("handled by is_unsat guard")
            }
        }
    }

    fn query_dependency_cone(
        &self,
        queries: &[&HornClause],
        defs_by_head: &FxHashMap<PredicateId, Vec<usize>>,
    ) -> FxHashSet<PredicateId> {
        let mut cone = FxHashSet::default();
        let mut stack = Vec::new();
        for query in queries {
            for (pred, _) in &query.body.predicates {
                stack.push(*pred);
            }
        }
        while let Some(pred) = stack.pop() {
            if !cone.insert(pred) {
                continue;
            }
            for clause_idx in defs_by_head.get(&pred).into_iter().flatten() {
                for (body_pred, _) in &self.problem.clauses()[*clause_idx].body.predicates {
                    stack.push(*body_pred);
                }
            }
        }
        cone
    }

    fn reachable_levels_by_pred(
        &self,
        max_depth: usize,
        cone: &FxHashSet<PredicateId>,
        defs_by_head: &FxHashMap<PredicateId, Vec<usize>>,
    ) -> FxHashMap<PredicateId, FxHashSet<usize>> {
        let mut levels: FxHashMap<PredicateId, FxHashSet<usize>> = FxHashMap::default();
        for depth in 0..=max_depth {
            let mut changed = false;
            for pred in cone {
                for clause_idx in defs_by_head.get(pred).into_iter().flatten() {
                    let clause = &self.problem.clauses()[*clause_idx];
                    let reachable = if clause.body.predicates.is_empty() {
                        depth == 0
                    } else if depth == 0 {
                        false
                    } else {
                        clause.body.predicates.iter().all(|(body_pred, _)| {
                            levels
                                .get(body_pred)
                                .is_some_and(|body_levels| body_levels.contains(&(depth - 1)))
                        })
                    };
                    if reachable && levels.entry(*pred).or_default().insert(depth) {
                        changed = true;
                    }
                }
            }
            if !changed && depth > 0 {
                let any_future_body = cone.iter().any(|pred| {
                    levels
                        .get(pred)
                        .is_some_and(|pred_levels| pred_levels.contains(&depth))
                });
                if !any_future_body {
                    break;
                }
            }
        }
        levels
    }

    fn compile_level_flat_cone(
        &self,
        level: usize,
        cone: &FxHashSet<PredicateId>,
        reachable_levels: &FxHashMap<PredicateId, FxHashSet<usize>>,
        defs_by_head: &FxHashMap<PredicateId, Vec<usize>>,
        conjuncts: &mut Vec<ChcExpr>,
    ) {
        for pred in cone {
            if !reachable_levels
                .get(pred)
                .is_some_and(|levels| levels.contains(&level))
            {
                continue;
            }
            let mut rule_disjuncts = Vec::new();
            for clause_idx in defs_by_head.get(pred).into_iter().flatten() {
                let clause = &self.problem.clauses()[*clause_idx];
                if level == 0 && !clause.body.predicates.is_empty() {
                    continue;
                }
                if level > 0
                    && !clause.body.predicates.iter().all(|(body_pred, _)| {
                        reachable_levels
                            .get(body_pred)
                            .is_some_and(|levels| levels.contains(&(level - 1)))
                    })
                {
                    continue;
                }

                let mut rule_conjuncts = Vec::new();
                let subst = self.mk_rule_vars(clause, *pred, *clause_idx, level);

                if let ClauseHead::Predicate(_, head_args) = &clause.head {
                    for (arg_idx, head_arg) in head_args.iter().enumerate() {
                        let level_arg = self.level_arg(*pred, arg_idx, level);
                        rule_conjuncts
                            .push(ChcExpr::eq(level_arg, head_arg.substitute_name_map(&subst)));
                    }
                }

                for (body_pred, body_args) in &clause.body.predicates {
                    if !cone.contains(body_pred) {
                        continue;
                    }
                    rule_conjuncts.push(self.level_predicate(*body_pred, level - 1));
                    for (arg_idx, body_arg) in body_args.iter().enumerate() {
                        let level_arg = self.level_arg(*body_pred, arg_idx, level - 1);
                        rule_conjuncts
                            .push(ChcExpr::eq(level_arg, body_arg.substitute_name_map(&subst)));
                    }
                }

                if let Some(constraint) = &clause.body.constraint {
                    rule_conjuncts.push(constraint.substitute_name_map(&subst));
                }
                if !rule_conjuncts.is_empty() {
                    rule_disjuncts.push(ChcExpr::and_all(rule_conjuncts));
                }
            }

            let level_pred = self.level_predicate(*pred, level);
            if rule_disjuncts.is_empty() {
                conjuncts.push(ChcExpr::not(level_pred));
            } else if rule_disjuncts.len() == 1 {
                conjuncts.push(ChcExpr::implies(level_pred, rule_disjuncts.remove(0)));
            } else {
                conjuncts.push(ChcExpr::implies(
                    level_pred,
                    ChcExpr::or_all(rule_disjuncts),
                ));
            }
        }
    }

    fn acyclic_reach_instance(
        &self,
        pred: PredicateId,
        args: &[ChcExpr],
        defs_by_head: &FxHashMap<PredicateId, Vec<usize>>,
        visiting: &mut FxHashSet<PredicateId>,
        fresh_counter: &mut usize,
        deadline: ay_core::time::Instant,
    ) -> Option<ChcExpr> {
        if ay_core::time::Instant::now() >= deadline || self.config.base.is_cancelled() {
            self.stats.borrow_mut().budget_exhausted = true;
            return None;
        }
        if !visiting.insert(pred) {
            return None;
        }

        let mut disjuncts = Vec::new();
        for clause_idx in defs_by_head.get(&pred).into_iter().flatten() {
            let clause = &self.problem.clauses()[*clause_idx];
            let expansion_id = *fresh_counter;
            *fresh_counter += 1;
            let mut subst = FxHashMap::default();
            for (var_idx, var) in clause.vars().into_iter().enumerate() {
                subst.insert(
                    var.name.clone(),
                    ChcExpr::Var(ChcVar::new(
                        format!("__bmc_dag_e{expansion_id}_v{var_idx}"),
                        var.sort,
                    )),
                );
            }

            let mut branch_conjuncts = vec![Vec::new()];
            if let ClauseHead::Predicate(_, head_args) = &clause.head {
                for (arg_idx, head_arg) in head_args.iter().enumerate() {
                    let Some(actual) = args.get(arg_idx) else {
                        visiting.remove(&pred);
                        return None;
                    };
                    let equality =
                        ChcExpr::eq(actual.clone(), head_arg.substitute_name_map(&subst));
                    for conjuncts in &mut branch_conjuncts {
                        conjuncts.push(equality.clone());
                    }
                }
            }

            for (body_pred, body_args) in &clause.body.predicates {
                let instantiated_args: Vec<_> = body_args
                    .iter()
                    .map(|arg| arg.substitute_name_map(&subst))
                    .collect();
                let body_reach = self.acyclic_reach_instance(
                    *body_pred,
                    &instantiated_args,
                    defs_by_head,
                    visiting,
                    fresh_counter,
                    deadline,
                )?;
                let alternatives = Self::collect_disjuncts_nontrivial(body_reach);
                if alternatives.is_empty() {
                    branch_conjuncts.clear();
                    break;
                }
                let combined_len = branch_conjuncts.len().saturating_mul(alternatives.len());
                if combined_len > ACYCLIC_REACH_DISTRIBUTION_CAP {
                    visiting.remove(&pred);
                    return None;
                }
                let old = std::mem::take(&mut branch_conjuncts);
                let mut expanded = Vec::with_capacity(combined_len);
                for conjuncts in old {
                    for alternative in &alternatives {
                        let mut branch = conjuncts.clone();
                        branch.push(alternative.clone());
                        expanded.push(branch);
                    }
                }
                branch_conjuncts = expanded;
            }

            if let Some(constraint) = &clause.body.constraint {
                let constraint = constraint.substitute_name_map(&subst);
                for conjuncts in &mut branch_conjuncts {
                    conjuncts.push(constraint.clone());
                }
            }
            for mut conjuncts in branch_conjuncts {
                if conjuncts.is_empty() {
                    conjuncts.push(ChcExpr::Bool(true));
                }
                disjuncts.push(ChcExpr::and_all(conjuncts));
            }
        }

        visiting.remove(&pred);
        Some(if disjuncts.is_empty() {
            ChcExpr::Bool(false)
        } else if disjuncts.len() == 1 {
            disjuncts.remove(0)
        } else {
            ChcExpr::or_all(disjuncts)
        })
    }

    fn collect_disjuncts_nontrivial(expr: ChcExpr) -> Vec<ChcExpr> {
        let mut result = Vec::new();
        Self::collect_disjuncts_nontrivial_into(&expr, &mut result);
        result
    }

    fn collect_disjuncts_nontrivial_into(expr: &ChcExpr, out: &mut Vec<ChcExpr>) {
        match expr {
            ChcExpr::Bool(false) => {}
            ChcExpr::Op(ChcOp::Or, args) => {
                for arg in args {
                    Self::collect_disjuncts_nontrivial_into(arg.as_ref(), out);
                }
            }
            other => out.push(other.clone()),
        }
    }

    /// Exact acyclic BMC query: assert every level up to `max_depth`, then ask
    /// whether any query is reachable at any level. For an acyclic predicate
    /// DAG, UNSAT is an exhaustive safety proof through the complete DAG bound.
    fn solve_acyclic_exhaustive_once(
        &self,
        queries: &[&HornClause],
        max_depth: usize,
    ) -> Option<ChcEngineResult> {
        if let Some(result) = self.solve_acyclic_symbolic_reachability_once(queries, max_depth) {
            if !matches!(result, ChcEngineResult::Unknown) {
                return Some(result);
            }
        }

        let start = ay_core::time::Instant::now();
        let deadline = self.config.time_budget.map(|budget| start + budget);
        let logic = self.detect_bmc_logic();
        let mut smt = format!("(set-logic {logic})\n(set-option :produce-models true)\n");
        let mut declared_vars: FxHashSet<String> = FxHashSet::default();
        let mut query_parts = Vec::new();
        let mut trace_query_conjuncts = Vec::new();

        for level in 0..=max_depth {
            if !self.should_continue_depth(&start) {
                self.stats.borrow_mut().budget_exhausted = true;
                return Some(ChcEngineResult::Unknown);
            }

            let mut level_conjuncts = Vec::new();
            self.compile_level_flat(level, &mut level_conjuncts);
            if !self.executor_conjuncts_supported(&level_conjuncts, "acyclic-exhaustive level") {
                return Some(ChcEngineResult::Unknown);
            }
            for conjunct in &level_conjuncts {
                for var in &conjunct.vars() {
                    if declared_vars.insert(var.name.clone()) {
                        let sort_str = sort_to_smtlib(&var.sort);
                        let name = quote_symbol(&var.name);
                        smt.push_str(&format!("(declare-const {name} {sort_str})\n"));
                    }
                }
                let s = InvariantModel::expr_to_smtlib(conjunct);
                smt.push_str(&format!("(assert {s})\n"));
            }

            for query in queries {
                let mut query_conjuncts = Vec::new();
                self.compile_query(query, level, &mut query_conjuncts);
                if !self.executor_conjuncts_supported(&query_conjuncts, "acyclic-exhaustive query")
                {
                    return Some(ChcEngineResult::Unknown);
                }
                if query_conjuncts.is_empty() {
                    continue;
                }
                for conjunct in &query_conjuncts {
                    for var in &conjunct.vars() {
                        if declared_vars.insert(var.name.clone()) {
                            let sort_str = sort_to_smtlib(&var.sort);
                            let name = quote_symbol(&var.name);
                            smt.push_str(&format!("(declare-const {name} {sort_str})\n"));
                        }
                    }
                }
                trace_query_conjuncts.extend(query_conjuncts.iter().cloned());
                let part = ChcExpr::and_all(query_conjuncts);
                query_parts.push(InvariantModel::expr_to_smtlib(&part));
            }
        }

        if query_parts.is_empty() {
            self.mark_acyclic_exhaustive_stats(max_depth, start.elapsed().as_secs_f64());
            return Some(ChcEngineResult::Safe(InvariantModel::default()));
        }

        let query_body = if query_parts.len() == 1 {
            query_parts[0].clone()
        } else {
            format!("(or {})", query_parts.join(" "))
        };
        smt.push_str(&format!("(assert {query_body})\n"));
        smt.push_str("(check-sat)\n");

        let commands = ay_frontend::parse(&smt).ok()?;
        let mut exec = ay_dpll::Executor::new();
        let outputs = Self::exec_commands_with_deadline(&mut exec, &commands, deadline)?;
        let result_str = outputs.first().map(String::as_str).unwrap_or("unknown");
        let elapsed = start.elapsed().as_secs_f64();

        match result_str.trim() {
            "sat" => {
                let model = self.observe_bmc_sat_model(
                    &mut exec,
                    max_depth,
                    &trace_query_conjuncts,
                    &[&declared_vars],
                    deadline,
                )?;
                self.record_depth(max_depth, elapsed);
                // Fix 1b: the query above is asserted as a disjunction over
                // levels `0..=max_depth` (`(or query_parts...)`), so a SAT
                // model may satisfy the query at a SHALLOWER level than
                // `max_depth`. Reconstruct at the level the model actually
                // satisfies; otherwise `{pred}#{max_depth}` is false and the
                // derivation collapses to `None` (a spurious Unknown).
                let reconstruct_level = self
                    .acyclic_satisfied_query_level(&model, queries, max_depth)
                    .unwrap_or(max_depth);
                Some(self.bmc_sat_result(&model, reconstruct_level, queries))
            }
            "unsat" => {
                self.mark_acyclic_exhaustive_stats(max_depth, elapsed);
                Some(ChcEngineResult::Safe(InvariantModel::default()))
            }
            _ => {
                self.record_depth(max_depth, elapsed);
                Some(ChcEngineResult::Unknown)
            }
        }
    }

    /// Fix 1b: find the level at which the SAT model satisfies some query.
    ///
    /// `solve_acyclic_exhaustive_once` asserts the query as a disjunction over
    /// levels `0..=max_depth`, so the counterexample may fire shallower than
    /// `max_depth`. Returns the smallest such level, using the SAME model
    /// satisfaction check as `model_root_query` (sort-independent). Only
    /// reached on SAT; if no level satisfies the query the caller falls back
    /// to the fail-closed `max_depth` reconstruction (yielding Unknown).
    fn acyclic_satisfied_query_level(
        &self,
        model: &FxHashMap<String, SmtValue>,
        queries: &[&HornClause],
        max_depth: usize,
    ) -> Option<usize> {
        let env = Self::model_i128_env(model);
        for level in 0..=max_depth {
            for query in queries {
                let mut query_conjuncts = Vec::new();
                self.compile_query(query, level, &mut query_conjuncts);
                if query_conjuncts.is_empty() {
                    continue;
                }
                if Self::model_conjuncts_satisfied(&query_conjuncts, model, &env) {
                    return Some(level);
                }
            }
        }
        None
    }

    /// Exact acyclic reachability query without level duplication.
    ///
    /// For a predicate DAG, each predicate's reachable-state formula can be
    /// computed once from its defining clauses and then instantiated at query
    /// sites. This is equivalent to exhaustive acyclic BMC, but it avoids
    /// copying every remaining clause at every level after preprocessing has
    /// already collapsed the generated graph.
    fn solve_acyclic_symbolic_reachability_once(
        &self,
        queries: &[&HornClause],
        max_depth: usize,
    ) -> Option<ChcEngineResult> {
        let start = ay_core::time::Instant::now();
        let deadline = self.config.time_budget.map(|budget| start + budget);
        let mut fresh_id = 0usize;
        let mut visiting = FxHashSet::default();
        let mut query_disjuncts = Vec::new();

        for query in queries {
            if !self.should_continue_depth(&start) {
                self.stats.borrow_mut().budget_exhausted = true;
                return Some(ChcEngineResult::Unknown);
            }

            let mut conjuncts = Vec::new();
            for (pred, args) in &query.body.predicates {
                let reach =
                    self.acyclic_reach_formula_fresh(*pred, &mut fresh_id, &mut visiting)?;
                conjuncts.push(self.instantiate_reach_formula(*pred, &reach, args));
            }
            if let Some(constraint) = &query.body.constraint {
                conjuncts.push(constraint.clone());
            }
            if conjuncts.is_empty() {
                conjuncts.push(ChcExpr::Bool(true));
            }
            query_disjuncts.push(Self::simplify_exact_acyclic_conjuncts(conjuncts));
        }

        if query_disjuncts.is_empty() {
            self.mark_acyclic_exhaustive_stats(max_depth, start.elapsed().as_secs_f64());
            return Some(ChcEngineResult::Safe(InvariantModel::default()));
        }

        let query_formula = if query_disjuncts.len() == 1 {
            query_disjuncts.remove(0)
        } else {
            ChcExpr::or_all(query_disjuncts)
        };
        let elapsed = start.elapsed().as_secs_f64();
        match self.check_symbolic_formula(&query_formula, deadline)? {
            Some(false) => {
                self.mark_acyclic_exhaustive_stats(max_depth, elapsed);
                Some(ChcEngineResult::Safe(InvariantModel::default()))
            }
            Some(true) => {
                self.record_depth(max_depth, elapsed);
                Some(ChcEngineResult::Unknown)
            }
            None => {
                self.record_depth(max_depth, elapsed);
                Some(ChcEngineResult::Unknown)
            }
        }
    }

    fn check_symbolic_formula(
        &self,
        formula: &ChcExpr,
        deadline: Option<ay_core::time::Instant>,
    ) -> Option<Option<bool>> {
        let timeout = deadline
            .and_then(|d| d.checked_duration_since(ay_core::time::Instant::now()))
            .unwrap_or_else(|| std::time::Duration::from_secs(30));
        if timeout.is_zero() {
            return Some(None);
        }

        let mut smt = self.problem.make_smt_context();
        Some(match smt.check_sat_with_timeout(formula, timeout) {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                Some(false)
            }
            SmtResult::Sat(_) => Some(true),
            SmtResult::Unknown => None,
        })
    }

    fn acyclic_reach_formula_fresh(
        &self,
        pred: PredicateId,
        fresh_id: &mut usize,
        visiting: &mut FxHashSet<PredicateId>,
    ) -> Option<ChcExpr> {
        if !visiting.insert(pred) {
            return None;
        }

        let mut disjuncts = Vec::new();
        for (rule_idx, clause) in self.problem.clauses_defining_with_index(pred) {
            let instance = *fresh_id;
            *fresh_id += 1;
            // Budget compliance: path expansion is worst-case exponential in
            // the DAG branching, and a single un-polled construction could
            // hold the probe far past its stage budget (observed on the
            // condensed iterator_count DAG). Poll the solve deadline every
            // 64 fresh rule instances; a `None` here degrades exactly like
            // the existing unsupported-shape bail (caller falls back /
            // returns Unknown — never a verdict).
            if instance.is_multiple_of(64)
                && matches!(
                    self.solve_deadline.get(),
                    Some(d) if ay_core::time::Instant::now() >= d
                )
            {
                visiting.remove(&pred);
                return None;
            }
            let subst = self.mk_fresh_rule_vars(clause, pred, rule_idx, instance);
            let mut conjuncts = Vec::new();

            if let ClauseHead::Predicate(_, head_args) = &clause.head {
                for (arg_idx, head_arg) in head_args.iter().enumerate() {
                    let reach_arg = self.reach_arg(pred, arg_idx);
                    conjuncts.push(ChcExpr::eq(reach_arg, head_arg.substitute_name_map(&subst)));
                }
            }

            if let Some(constraint) = &clause.body.constraint {
                conjuncts.push(constraint.substitute_name_map(&subst));
            }

            for (body_pred, body_args) in &clause.body.predicates {
                let body_reach =
                    self.acyclic_reach_formula_fresh(*body_pred, fresh_id, visiting)?;
                let body_args: Vec<_> = body_args
                    .iter()
                    .map(|arg| arg.substitute_name_map(&subst))
                    .collect();
                conjuncts.push(self.instantiate_reach_formula(*body_pred, &body_reach, &body_args));
            }

            if conjuncts.is_empty() {
                conjuncts.push(ChcExpr::Bool(true));
            }
            disjuncts.push(ChcExpr::and_all(conjuncts));
        }

        visiting.remove(&pred);
        Some(if disjuncts.is_empty() {
            ChcExpr::Bool(false)
        } else if disjuncts.len() == 1 {
            disjuncts.remove(0)
        } else {
            ChcExpr::or_all(disjuncts)
        })
    }

    fn mk_fresh_rule_vars(
        &self,
        clause: &HornClause,
        pred: PredicateId,
        rule_idx: usize,
        instance: usize,
    ) -> FxHashMap<String, ChcExpr> {
        let mut subst = FxHashMap::default();
        for var in clause.vars() {
            let name = format!(
                "__bmc_dag_p{}_r{}_i{}_{}",
                pred.index(),
                rule_idx,
                instance,
                var.name
            );
            subst.insert(var.name.clone(), ChcExpr::Var(ChcVar::new(name, var.sort)));
        }
        subst
    }

    fn instantiate_reach_formula(
        &self,
        pred: PredicateId,
        formula: &ChcExpr,
        args: &[ChcExpr],
    ) -> ChcExpr {
        let mut subst = FxHashMap::default();
        for (arg_idx, arg) in args.iter().enumerate() {
            let reach_arg = self.reach_arg(pred, arg_idx);
            if let ChcExpr::Var(var) = &reach_arg {
                subst.insert(var.name.clone(), arg.clone());
            }
        }
        formula.substitute_name_map(&subst)
    }

    fn reach_arg(&self, pred: PredicateId, idx: usize) -> ChcExpr {
        let pred_info = self
            .problem
            .predicates()
            .iter()
            .find(|p| p.id == pred)
            .expect("predicate id exists");
        let sort = pred_info.arg_sorts[idx].clone();
        ChcExpr::Var(ChcVar::new(
            format!("__bmc_reach_p{}_a{}", pred.index(), idx),
            sort,
        ))
    }

    fn mark_acyclic_exhaustive_stats(&self, max_depth: usize, elapsed_secs: f64) {
        let mut stats = self.stats.borrow_mut();
        stats.max_depth_reached = max_depth;
        stats.num_checks = max_depth + 1;
        stats.final_ema_secs = elapsed_secs;
        stats.exhausted_search = true;
    }

    /// Compute the next depth to check given adaptive stepping settings.
    ///
    /// When adaptive stepping is disabled, always returns `current + 1`.
    /// When enabled, monitors the EMA of per-depth solve time and skips
    /// ahead when depths are trivially fast. The step size grows as a
    /// doubling sequence (1, 2, 4, 8, 16) capped at `MAX_ADAPTIVE_STEP`.
    /// When a depth becomes non-trivial, the step size resets to 1.
    ///
    /// Returns `(next_depth, new_adaptive_step)`.
    fn next_depth(
        &self,
        current: usize,
        ema: f64,
        adaptive_step: usize,
        max_depth: usize,
    ) -> (usize, usize) {
        if !self.config.enable_adaptive_stepping {
            return (current + 1, 1);
        }

        if ema < TRIVIAL_DEPTH_THRESHOLD_SECS && current > 2 {
            // Depths are trivially fast — increase step size.
            let new_step = (adaptive_step * 2).min(MAX_ADAPTIVE_STEP);
            let next = (current + new_step).min(max_depth);
            (next, new_step)
        } else {
            // Non-trivial depth — reset to sequential stepping.
            (current + 1, 1)
        }
    }

    /// Add transition constraints for all levels from `from_level` to `to_level`
    /// (inclusive) to the executor. Used by adaptive stepping when skipping
    /// multiple levels at once.
    fn add_levels_to_executor(
        &self,
        exec: &mut ay_dpll::Executor,
        declared_vars: &mut FxHashSet<String>,
        from_level: usize,
        to_level: usize,
        deadline: Option<ay_core::time::Instant>,
    ) -> Option<()> {
        for level in from_level..=to_level {
            let mut level_smt = String::new();
            let mut level_conjuncts = Vec::new();
            self.compile_level_flat(level, &mut level_conjuncts);
            if !self.executor_conjuncts_supported(&level_conjuncts, "single-executor levels") {
                return None;
            }
            for conjunct in &level_conjuncts {
                for var in &conjunct.vars() {
                    if declared_vars.insert(var.name.clone()) {
                        let sort_str = sort_to_smtlib(&var.sort);
                        let name = quote_symbol(&var.name);
                        level_smt.push_str(&format!("(declare-const {name} {sort_str})\n"));
                    }
                }
                let s = InvariantModel::expr_to_smtlib(conjunct);
                level_smt.push_str(&format!("(assert {s})\n"));
            }
            if !level_smt.is_empty() {
                let cmds = ay_frontend::parse(&level_smt).ok()?;
                Self::exec_commands_with_deadline(exec, &cmds, deadline)?;
            }
        }
        Some(())
    }

    // ============ Persistent-Executor Transition-System BMC (Phase 3 Layer B) ============

    /// Kill switch for the persistent-executor transition-system BMC path
    /// (Phase 3 Layer B). Default ON; set `AY_CHC_BMC_TS_INCREMENTAL=0` to
    /// fall back to the previous activation-literal/fresh-executor routes.
    fn ts_incremental_enabled() -> bool {
        static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        *ENABLED
            .get_or_init(|| std::env::var("AY_CHC_BMC_TS_INCREMENTAL").map_or(true, |v| v != "0"))
    }

    /// Whether THIS run sweeps past a spurious / non-strictly-confirmable
    /// shallow BMC SAT to reach the real deeper counterexample
    /// (#chc25-bmc-sweep).
    ///
    /// Primary mechanism: `BmcConfig::sweep_past_spurious_sat` (default ON
    /// for counterexample hunting; OFF in [`BmcConfig::cross_check`], where
    /// the sweep is pure wasted budget — model-checker-consumer #39/#42). Diagnostic
    /// override: `AY_CHC_BMC_SWEEP_PAST_SPURIOUS_SAT` forces it either way
    /// when set (`0` = off, anything else = on). Purely
    /// completeness-affecting: with it OFF the sweep can only find FEWER
    /// counterexamples, never a wrong verdict either way.
    fn sweep_past_spurious_sat(&self) -> bool {
        static OVERRIDE: std::sync::OnceLock<Option<bool>> = std::sync::OnceLock::new();
        OVERRIDE
            .get_or_init(|| {
                std::env::var("AY_CHC_BMC_SWEEP_PAST_SPURIOUS_SAT")
                    .ok()
                    .map(|v| v != "0")
            })
            .unwrap_or(self.config.sweep_past_spurious_sat)
    }

    /// Classify a flat-BMC SAT model at depth `k` into either a
    /// strictly-validated counterexample or an instruction to advance the sweep
    /// (#chc25-bmc-sweep).
    ///
    /// The strict check is exactly `bmc_sat_result`: it extracts the derivation
    /// witness and replays it against the ORIGINAL clauses via
    /// `verified_unsafe_from_witness` (a `PdrSolver` witness replay — the same
    /// verification `replay_confirm_unsafe_at_depth` uses as its acceptance
    /// gate). It yields `Unsafe` ONLY for a witness that replays as Valid, which
    /// fails closed on safe problems (see the axiom-only / cyclic
    /// self-justification adversarial tests). Consequences:
    ///
    /// * SOUNDNESS: on a SAFE problem no witness replays as Valid, so every
    ///   depth classifies as `Advance` and the sweep can NEVER manufacture an
    ///   `Unsafe` — an unvalidated SAT never becomes a wrong `unsat`.
    /// * COMPLETENESS: a genuine counterexample of ANY depth is trusted
    ///   directly. We deliberately do NOT gate it behind the witness-free
    ///   `replay_confirm_unsafe_on_problem` re-derivation, whose 64-level clamp
    ///   would spuriously reject validated deep counterexamples (e.g. a
    ///   depth-70 BV-linear trace).
    /// * NO RECURSION: because the strict check is the already-present,
    ///   non-recursive `bmc_sat_result`, the SAT arm launches no nested BMC —
    ///   the sweep cannot loop BMC→confirm→BMC.
    fn classify_flat_sat(
        &self,
        model: &FxHashMap<String, SmtValue>,
        k: usize,
        queries: &[&HornClause],
    ) -> FlatSatOutcome {
        match self.bmc_sat_result(model, k, queries) {
            unsafe_result @ ChcEngineResult::Unsafe(_) => FlatSatOutcome::Confirmed(unsafe_result),
            _ => {
                // Unknown: spurious executor SAT or an unreconstructable witness
                // (e.g. the degenerate flat level-0 array encoding). Do not
                // trust it as a verdict; advance the sweep to a deeper depth.
                tracing::debug!(
                    "BMC: SAT at depth {k} did not yield a validated counterexample; \
                     advancing sweep"
                );
                FlatSatOutcome::Advance
            }
        }
    }

    /// Extend the persistent transition-system unrolling from depth `k` to
    /// `k+1`: pop the depth-`k` query frame and assert transition `k` as a
    /// permanent constraint. Returns `false` if the extension could not be
    /// applied (unsupported sort, parse failure, or executor cut-off), in which
    /// case the caller should resume the fresh fallback.
    ///
    /// Shared by the UNSAT arm and the sweep-past-spurious-SAT arm
    /// (#chc25-bmc-sweep): a shallow TS SAT that no bounded confirmation could
    /// validate continues the FAST transition-system sweep to the next depth
    /// (rather than the flat re-solve, which livelocks on the degenerate array
    /// encoding), keeping the search on the encoding that answers each depth in
    /// well under a second.
    fn ts_extend_unrolling(
        &self,
        exec: &mut ay_dpll::Executor,
        ts: &TransitionSystem,
        declared: &mut FxHashSet<String>,
        k: usize,
        depth_deadline: Option<ay_core::time::Instant>,
    ) -> bool {
        let transition_k = ts.transition_at(k);
        if !self.executor_conjuncts_supported(
            std::slice::from_ref(&transition_k),
            "ts-incremental transition",
        ) {
            return false;
        }
        let mut extend_script = String::from("(pop 1)\n");
        Self::append_ts_decls_and_asserts(&mut extend_script, &transition_k, declared, true);
        let Ok(cmds) = ay_frontend::parse(&extend_script) else {
            return false;
        };
        if Self::exec_commands_with_deadline(exec, &cmds, depth_deadline).is_none() {
            tracing::debug!("BMC-ts: transition extension failed at depth {k}");
            return false;
        }
        true
    }

    /// Append `(declare-const ...)` lines for variables of `expr` missing from
    /// `declared`, plus one `(assert ...)` per top-level conjunct, to `script`.
    ///
    /// When `permanent` is false the new names are NOT recorded in `declared`:
    /// used for declarations made inside a `(push 1)` frame, which vanish at
    /// the matching `(pop 1)` (e.g. per-depth query locals).
    fn append_ts_decls_and_asserts(
        script: &mut String,
        expr: &ChcExpr,
        declared: &mut FxHashSet<String>,
        permanent: bool,
    ) {
        let mut frame_local: FxHashSet<String> = FxHashSet::default();
        for conjunct in expr.conjuncts() {
            for var in &conjunct.vars() {
                if declared.contains(&var.name) || !frame_local.insert(var.name.clone()) {
                    continue;
                }
                if permanent {
                    declared.insert(var.name.clone());
                }
                let sort_str = sort_to_smtlib(&var.sort);
                let name = quote_symbol(&var.name);
                script.push_str(&format!("(declare-const {name} {sort_str})\n"));
            }
            let s = InvariantModel::expr_to_smtlib(conjunct);
            script.push_str(&format!("(assert {s})\n"));
        }
    }

    /// Test support (Bench-1, lia-hot-loop plan): build the exact SMT-LIB
    /// script segments that `solve_transition_system_incremental` feeds one
    /// persistent `ay_dpll::Executor` for depths `0..=depth`.
    ///
    /// Segment layout (one entry per executor round-trip):
    /// - `[0]`: `(set-logic ..)` + init@0 decls/asserts (asserted once);
    /// - then alternating, for k in `0..=depth`:
    ///   `(push 1)` + query@k decls/asserts + `(check-sat)`, and (for
    ///   `k < depth`) `(pop 1)` + transition@k decls/asserts.
    ///
    /// Returns `None` when the problem is not a supported transition system
    /// (mirrors the production path's gates).
    #[doc(hidden)]
    pub fn ts_incremental_script_segments_for_test(
        problem: ChcProblem,
        depth: usize,
    ) -> Option<Vec<String>> {
        let solver = Self::new(problem, BmcConfig::default());
        let ts = TransitionSystem::from_chc_problem(&solver.problem).ok()?;
        if ts.find_unsupported_transition_state_sort().is_some() {
            return None;
        }
        let logic = solver.detect_bmc_logic();
        let mut declared: FxHashSet<String> = FxHashSet::default();
        let mut segments = Vec::new();

        let init0 = ts.init_at(0);
        let mut script = format!("(set-logic {logic})\n");
        Self::append_ts_decls_and_asserts(&mut script, &init0, &mut declared, true);
        segments.push(script);

        for k in 0..=depth {
            let query_k = ts.query_at(k);
            let mut depth_script = String::from("(push 1)\n");
            Self::append_ts_decls_and_asserts(&mut depth_script, &query_k, &mut declared, false);
            depth_script.push_str("(check-sat)\n");
            segments.push(depth_script);

            if k < depth {
                let transition_k = ts.transition_at(k);
                let mut extend_script = String::from("(pop 1)\n");
                Self::append_ts_decls_and_asserts(
                    &mut extend_script,
                    &transition_k,
                    &mut declared,
                    true,
                );
                segments.push(extend_script);
            }
        }
        Some(segments)
    }

    /// Golem-style persistent-executor BMC for single-predicate transition
    /// systems (Phase 3 Layer B; reference: golem `engine/Bmc.cc`
    /// `solveTransitionSystemInternal`).
    ///
    /// One `ay_dpll::Executor` lives across ALL depth checks:
    ///   - `init@0` is asserted once;
    ///   - at depth k: `(push 1)`, assert `query@k` (conjunct-split),
    ///     check-sat, `(pop 1)`, then assert `transition@k` (k → k+1)
    ///     permanently.
    ///
    /// Per-check setup (atom registration, bound-axiom generation, Tseitin
    /// encoding, theory-solver construction) is incremental in the NEW
    /// formula at depth k instead of being rebuilt from scratch each depth
    /// (the per-depth fresh path) or hidden behind an activation-literal
    /// implication that defeats conjunct-level preprocessing (the
    /// single-executor path).
    ///
    /// Soundness: this path never produces a verdict by itself.
    ///   - SAT at depth k only triggers re-solving depth k on the existing
    ///     per-depth fresh flat path (`solve_per_depth_fresh`), whose model →
    ///     derivation-witness → `PdrSolver::try_verify_counterexample`
    ///     pipeline is unchanged. (A path of exactly k transitions is also a
    ///     path of length ≤ k in the flat level encoding.)
    ///   - UNSAT at depth k means "no counterexample of exactly k
    ///     transitions"; the loop checks every depth 0..=max_depth
    ///     sequentially (adaptive skipping is gated off), so the union over
    ///     visited depths covers all paths of length ≤ k, matching the flat
    ///     encoding's per-depth coverage. Exhausting all depths yields
    ///     Unknown (acyclic_safe configs are gated off this path).
    ///   - unknown / executor failure abandons the persistent executor and
    ///     resumes the existing routes (`RetryFresh`).
    ///
    /// Returns `None` when the problem is not a supported transition system,
    /// so `solve_via_executor` falls through to the existing paths.
    fn solve_transition_system_incremental(
        &self,
        queries: &[&HornClause],
        max_depth: usize,
    ) -> Option<SingleExecutorOutcome> {
        if !Self::ts_incremental_enabled() {
            return None;
        }
        // Exact-depth queries are incompatible with adaptive depth skipping,
        // and this path never claims Safe, so acyclic-safe configs (which
        // expect Safe on exhaustion) keep their existing routes.
        if self.config.enable_adaptive_stepping || self.config.acyclic_safe {
            return None;
        }
        let ts = TransitionSystem::from_chc_problem(&self.problem).ok()?;
        if ts.find_unsupported_transition_state_sort().is_some() {
            return None;
        }

        let start = ay_core::time::Instant::now();
        let logic = self.detect_bmc_logic();
        let mut declared: FxHashSet<String> = FxHashSet::default();

        let init0 = ts.init_at(0);
        if !self.executor_conjuncts_supported(std::slice::from_ref(&init0), "ts-incremental init") {
            return None;
        }
        let mut script = format!("(set-logic {logic})\n");
        Self::append_ts_decls_and_asserts(&mut script, &init0, &mut declared, true);

        let commands = ay_frontend::parse(&script).ok()?;
        let mut exec = ay_dpll::Executor::new();
        // Fix 1 (sat-side-model-search diagnosis): disable LRA theory
        // propagation for this lane's QF_LIA solves. DRAGON-class sat-type
        // counterexample queries livelock under BCP-time implied-bounds
        // propagation (weak learned clauses + unstable theory-hinted phases:
        // >300s on queries z3 answers in 9ms); with propagation off the same
        // depth checks answer in ~1s with identical verdicts. Scoped to the
        // transition-system BMC lane only — every other lane keeps default
        // propagation (the #9505 adaptive-mode beneficiaries are untouched).
        exec.set_no_lra_theory_propagation(true);
        Self::exec_commands(&mut exec, &commands)?;

        let mut ema_depth_time: f64 = 0.0;
        let mut consecutive_unsat: usize = 0;

        for k in 0..=max_depth {
            if !self.should_continue_depth(&start) {
                tracing::debug!("BMC-ts: Stopped at depth {} (budget/cancel)", k);
                self.stats.borrow_mut().budget_exhausted = true;
                return Some(SingleExecutorOutcome::Solved(ChcEngineResult::Unknown));
            }

            let depth_start = ay_core::time::Instant::now();
            let mut depth_deadline = self.per_depth_deadline(depth_start);
            // Budget insurance: a stalled persistent check must leave room
            // for the fresh fallback (`RetryFresh`), so cap each TS depth
            // check at half the remaining overall budget.
            if let Some(budget) = self.config.time_budget {
                let remaining = budget.saturating_sub(start.elapsed());
                let cap = depth_start
                    + (remaining.div_f64(2.0)).max(std::time::Duration::from_millis(50));
                depth_deadline = Some(depth_deadline.map_or(cap, |d| d.min(cap)));
            }

            let query_k = ts.query_at(k);
            if !self.executor_conjuncts_supported(
                std::slice::from_ref(&query_k),
                "ts-incremental query",
            ) {
                return Some(SingleExecutorOutcome::RetryFresh {
                    start_depth: k,
                    consecutive_unsat,
                });
            }

            let mut depth_script = String::from("(push 1)\n");
            Self::append_ts_decls_and_asserts(&mut depth_script, &query_k, &mut declared, false);
            depth_script.push_str("(check-sat)\n");

            let Ok(cmds) = ay_frontend::parse(&depth_script) else {
                return Some(SingleExecutorOutcome::RetryFresh {
                    start_depth: k,
                    consecutive_unsat,
                });
            };
            let Some(outputs) = Self::exec_commands_with_deadline(&mut exec, &cmds, depth_deadline)
            else {
                tracing::debug!("BMC-ts: executor failure at depth {k}; resuming fresh fallback");
                return Some(SingleExecutorOutcome::RetryFresh {
                    start_depth: k,
                    consecutive_unsat,
                });
            };
            let result_str = outputs
                .iter()
                .map(|s| s.trim())
                .find(|s| matches!(*s, "sat" | "unsat" | "unknown"))
                .unwrap_or("unknown");

            let depth_elapsed = depth_start.elapsed().as_secs_f64();
            ema_depth_time = EMA_ALPHA * depth_elapsed + (1.0 - EMA_ALPHA) * ema_depth_time;
            self.record_depth(k, ema_depth_time);
            tracing::debug!(
                "BMC-ts: depth={} result={} time={:.3}s ema={:.3}s",
                k,
                result_str,
                depth_elapsed,
                ema_depth_time,
            );

            match result_str {
                "sat" => {
                    // Confirm on the existing per-depth fresh flat path: model
                    // parsing, witness extraction, and counterexample
                    // validation are unchanged from the non-incremental route.
                    tracing::debug!("BMC-ts: SAT at depth {k}; confirming on per-depth fresh path");
                    // The confirmation re-solve keeps LRA propagation off
                    // (Fix 1): the flat depth-k sat-type query is exactly the
                    // DRAGON-class shape that livelocks under propagation.
                    if self.sweep_past_spurious_sat() {
                        // #chc25-bmc-sweep: confirm this depth's SAT on the flat
                        // fresh path (witness extraction + original-clause
                        // replay). A genuine counterexample of ANY depth returns
                        // Unsafe and is reported. When confirmation yields a
                        // validated Unsafe we stop; otherwise the SAT is
                        // spurious / unreconstructable (e.g. the degenerate
                        // level-0 array encoding), so keep sweeping on the FAST
                        // transition-system encoding (each TS depth answers in
                        // well under a second) instead of terminating the lane
                        // at this shallow SAT.
                        if let Some(ChcEngineResult::Unsafe(cex)) =
                            self.solve_per_depth_fresh(queries, k, k, 0, true)
                        {
                            return Some(SingleExecutorOutcome::Solved(ChcEngineResult::Unsafe(
                                cex,
                            )));
                        }
                        if k == max_depth {
                            break;
                        }
                        tracing::debug!(
                            "BMC-ts: depth {k} SAT not confirmed Unsafe; continuing TS sweep to {}",
                            k + 1
                        );
                        if !self.ts_extend_unrolling(
                            &mut exec,
                            &ts,
                            &mut declared,
                            k,
                            depth_deadline,
                        ) {
                            return Some(SingleExecutorOutcome::RetryFresh {
                                start_depth: k + 1,
                                consecutive_unsat,
                            });
                        }
                        continue;
                    }
                    return self
                        .solve_per_depth_fresh(queries, k, k, 0, true)
                        .map(SingleExecutorOutcome::Solved);
                }
                "unsat" => {
                    consecutive_unsat += 1;
                    // Inc-16 S1b probe clamp: depth `min_depth` verified
                    // cex-free AND `after` wall-clock elapsed → stop early
                    // (Unknown). Only the front BMC probe sets this; see
                    // `BmcConfig::ts_probe_clamp` for the rationale.
                    if let Some((min_depth, after)) = self.config.ts_probe_clamp {
                        if k >= min_depth && start.elapsed() >= after {
                            tracing::debug!(
                                "BMC-ts: probe clamp at depth {} ({:.1}s, no cex)",
                                k,
                                start.elapsed().as_secs_f64()
                            );
                            self.stats.borrow_mut().budget_exhausted = true;
                            return Some(SingleExecutorOutcome::Solved(ChcEngineResult::Unknown));
                        }
                    }
                    // Try k-induction after consecutive UNSAT depths (#7969);
                    // identical preconditions to the single-executor path.
                    if self.config.enable_k_induction
                        && consecutive_unsat >= K_INDUCTION_MIN_CONSECUTIVE_UNSAT
                        && k >= K_INDUCTION_MIN_CONSECUTIVE_UNSAT
                    {
                        self.stats.borrow_mut().num_k_induction_attempts += 1;
                        if let Some(safe_result) = self.try_k_induction_check(consecutive_unsat) {
                            {
                                let mut stats = self.stats.borrow_mut();
                                stats.k_induction_proved = true;
                                stats.k_induction_k = Some(consecutive_unsat);
                            }
                            return Some(SingleExecutorOutcome::Solved(safe_result));
                        }
                    }
                    if k == max_depth {
                        break;
                    }
                    // Pop the query frame, then extend the unrolling: assert
                    // transition k → k+1 permanently (outside any frame).
                    if !self.ts_extend_unrolling(&mut exec, &ts, &mut declared, k, depth_deadline) {
                        return Some(SingleExecutorOutcome::RetryFresh {
                            start_depth: k + 1,
                            consecutive_unsat,
                        });
                    }
                }
                _ => {
                    tracing::debug!("BMC-ts: unknown at depth {k}; resuming fresh fallback");
                    return Some(SingleExecutorOutcome::RetryFresh {
                        start_depth: k,
                        consecutive_unsat,
                    });
                }
            }
        }

        Some(self.finalize_single_executor_completion(None))
    }

    /// Kill switch for the multipred SingleLoop persistent-executor BMC lane
    /// (inc-9). Default ON; set `AY_CHC_BMC_MULTIPRED_TS=0` to fall back to
    /// the activation-literal/fresh-executor routes for multipred problems.
    fn multipred_ts_incremental_enabled() -> bool {
        static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        *ENABLED.get_or_init(|| std::env::var("AY_CHC_BMC_MULTIPRED_TS").map_or(true, |v| v != "0"))
    }

    /// Build a synthetic single-predicate transition system for a LINEAR
    /// multi-predicate problem (golem's SingleLoopTransformation / Horn2VMT
    /// location encoding): one Int location variable per predicate plus the
    /// union of per-predicate argument slots; each clause becomes one
    /// transition disjunct selecting source/target locations.
    ///
    /// Returns `None` when the problem is single-predicate (the existing TS
    /// lane handles it), non-linear, or uses state sorts the executor lane
    /// does not support.
    fn multipred_singleloop_ts(&self) -> Option<(TransitionSystem, &'static str)> {
        if self.problem.predicates().len() < 2 {
            return None;
        }
        let mut tx = crate::single_loop::SingleLoopTransformation::new(self.problem.clone());
        let sys = tx.transform()?;
        let synthetic = sys.to_chc_problem();
        let logic = Self::detect_bmc_logic_for(&synthetic);
        let ts = TransitionSystem::from_chc_problem(&synthetic).ok()?;
        if ts.find_unsupported_transition_state_sort().is_some() {
            return None;
        }
        Some((ts, logic))
    }

    /// Golem-style persistent-executor BMC for LINEAR MULTI-PREDICATE CHC
    /// (inc-9; reference: golem's TransformationPipeline, which linearizes any
    /// linear system into a single transition system before its BMC engine).
    /// The problem is linearized via `SingleLoopTransformation` and solved
    /// with the same persistent-executor push/pop-per-depth loop as
    /// `solve_transition_system_incremental`.
    ///
    /// Depth correspondence: the SingleLoop init state is "no predicate
    /// derived yet" (all locations 0), so TS depth k = a derivation of k
    /// clause applications (one fact + k-1 rules); the flat level encoding
    /// covers the same derivation at level k-1 (facts sit at level 0, and a
    /// fact disjunct exists at EVERY level, so level L covers all derivations
    /// of height ≤ L).
    ///
    /// Soundness: this lane never produces a verdict by itself.
    ///   - SAT at TS depth k re-solves on the flat per-depth fresh path at
    ///     levels k-1..=k+1, whose model → derivation-witness →
    ///     `PdrSolver::try_verify_counterexample` replay pipeline is
    ///     unchanged. No flat confirmation → no Unsafe (fail closed).
    ///   - UNSAT at TS depth k means "no derivation of exactly k clause
    ///     applications"; sweeping k = 0..=max_depth+1 discharges every
    ///     derivation the flat path would cover through level max_depth, but
    ///     exhaustion still returns Unknown — never Safe: `acyclic_safe`
    ///     configs are gated off this lane, and `exhausted_search` is NOT
    ///     marked (conservative; this lane makes no completeness claim).
    ///   - unknown / executor failure resumes the flat fresh path from the
    ///     deepest flat level not yet covered (`RetryFresh`).
    fn solve_multipred_ts_incremental(
        &self,
        queries: &[&HornClause],
        max_depth: usize,
    ) -> Option<SingleExecutorOutcome> {
        if !Self::ts_incremental_enabled() || !Self::multipred_ts_incremental_enabled() {
            return None;
        }
        // Exact-depth queries are incompatible with adaptive depth skipping,
        // and this lane never claims Safe, so acyclic-safe configs (which
        // expect Safe on exhaustion) keep their existing routes.
        if self.config.enable_adaptive_stepping || self.config.acyclic_safe {
            return None;
        }
        // Scope: the LIA/Bool family this lane is built and measured for
        // (eldarica reve/llreve class). The flat-confirmation witness
        // pipeline has no Real/datatype model extraction
        // (`model_derivation_witnesses` bails), BV problems would mix Int
        // location variables into a QF_BV script, and array transitions are
        // better served by the existing routes (the dedicated cyclic-array
        // BMC lineup keeps its flat path).
        if self.problem.has_real_sorts()
            || self.problem.has_datatype_sorts()
            || self.problem.has_bv_sorts()
            || self.problem.has_array_sorts()
        {
            return None;
        }
        let (ts, logic) = self.multipred_singleloop_ts()?;

        let start = ay_core::time::Instant::now();
        let mut declared: FxHashSet<String> = FxHashSet::default();

        let init0 = ts.init_at(0);
        if !self.executor_conjuncts_supported(std::slice::from_ref(&init0), "mp-ts init") {
            return None;
        }
        let mut script = format!("(set-logic {logic})\n");
        Self::append_ts_decls_and_asserts(&mut script, &init0, &mut declared, true);

        let commands = ay_frontend::parse(&script).ok()?;
        let mut exec = ay_dpll::Executor::new();
        // Same policy as the single-predicate TS lane (Fix 1): LRA theory
        // propagation off for this lane's QF_LIA solves; sat-type depth
        // queries livelock under BCP-time implied-bounds propagation.
        exec.set_no_lra_theory_propagation(true);
        Self::exec_commands(&mut exec, &commands)?;

        let mut ema_depth_time: f64 = 0.0;

        // `max_depth` is a FLAT level bound; flat level L covers derivations
        // of ≤ L+1 clause applications while TS depth k covers exactly k, so
        // sweep one extra TS depth to match the flat path's coverage.
        let ts_max_depth = max_depth.saturating_add(1);
        for k in 0..=ts_max_depth {
            if !self.should_continue_depth(&start) {
                tracing::debug!("BMC-mp-ts: Stopped at depth {} (budget/cancel)", k);
                self.stats.borrow_mut().budget_exhausted = true;
                return Some(SingleExecutorOutcome::Solved(ChcEngineResult::Unknown));
            }

            let depth_start = ay_core::time::Instant::now();
            let mut depth_deadline = self.per_depth_deadline(depth_start);
            // Budget insurance (mirrors the single-pred TS lane): a stalled
            // persistent check must leave room for the fresh fallback.
            if let Some(budget) = self.config.time_budget {
                let remaining = budget.saturating_sub(start.elapsed());
                let cap = depth_start
                    + (remaining.div_f64(2.0)).max(std::time::Duration::from_millis(50));
                depth_deadline = Some(depth_deadline.map_or(cap, |d| d.min(cap)));
            }

            // TS depths 0..k-1 are discharged ⇒ flat levels ≤ k-2 are covered;
            // any abort at TS depth k resumes the flat path at level k-1.
            let resume_level = k.saturating_sub(1);

            let query_k = ts.query_at(k);
            if !self.executor_conjuncts_supported(std::slice::from_ref(&query_k), "mp-ts query") {
                return Some(SingleExecutorOutcome::RetryFresh {
                    start_depth: resume_level,
                    consecutive_unsat: 0,
                });
            }

            let mut depth_script = String::from("(push 1)\n");
            Self::append_ts_decls_and_asserts(&mut depth_script, &query_k, &mut declared, false);
            depth_script.push_str("(check-sat)\n");

            let Ok(cmds) = ay_frontend::parse(&depth_script) else {
                return Some(SingleExecutorOutcome::RetryFresh {
                    start_depth: resume_level,
                    consecutive_unsat: 0,
                });
            };
            let Some(outputs) = Self::exec_commands_with_deadline(&mut exec, &cmds, depth_deadline)
            else {
                tracing::debug!(
                    "BMC-mp-ts: executor failure at depth {k}; resuming fresh fallback"
                );
                return Some(SingleExecutorOutcome::RetryFresh {
                    start_depth: resume_level,
                    consecutive_unsat: 0,
                });
            };
            let result_str = outputs
                .iter()
                .map(|s| s.trim())
                .find(|s| matches!(*s, "sat" | "unsat" | "unknown"))
                .unwrap_or("unknown");

            let depth_elapsed = depth_start.elapsed().as_secs_f64();
            ema_depth_time = EMA_ALPHA * depth_elapsed + (1.0 - EMA_ALPHA) * ema_depth_time;
            self.record_depth(k, ema_depth_time);
            tracing::debug!(
                "BMC-mp-ts: depth={} result={} time={:.3}s ema={:.3}s",
                k,
                result_str,
                depth_elapsed,
                ema_depth_time,
            );

            match result_str {
                "sat" => {
                    // Confirm on the flat per-depth fresh path: level k-1
                    // covers the TS-depth-k derivation; +1 slack tolerates
                    // encoding boundary differences. Model parsing, witness
                    // extraction, and counterexample replay validation are
                    // unchanged from the non-incremental route — without a
                    // verified flat confirmation there is NO Unsafe verdict.
                    tracing::debug!("BMC-mp-ts: SAT at depth {k}; confirming on flat fresh path");
                    if self.sweep_past_spurious_sat() {
                        // #chc25-bmc-sweep: confirm the flat window k-1..=k+1; if
                        // it yields a validated Unsafe, report it. Otherwise the
                        // shallow SAT is spurious — resume the flat fresh sweep
                        // one level past the confirmed window rather than giving
                        // up at this shallow SAT.
                        if let Some(ChcEngineResult::Unsafe(cex)) =
                            self.solve_per_depth_fresh(queries, k + 1, k.saturating_sub(1), 0, true)
                        {
                            return Some(SingleExecutorOutcome::Solved(ChcEngineResult::Unsafe(
                                cex,
                            )));
                        }
                        tracing::debug!(
                            "BMC-mp-ts: depth {k} SAT not confirmed Unsafe; resuming fresh sweep from {}",
                            k + 2
                        );
                        // Resume the flat fresh sweep past the confirmed window,
                        // LRA propagation OFF (see the single-predicate lane for
                        // the DRAGON-class rationale).
                        return self
                            .solve_per_depth_fresh(queries, max_depth, k + 2, 0, true)
                            .map(SingleExecutorOutcome::Solved);
                    }
                    return self
                        .solve_per_depth_fresh(queries, k + 1, k.saturating_sub(1), 0, true)
                        .map(SingleExecutorOutcome::Solved);
                }
                "unsat" => {
                    if k == ts_max_depth {
                        break;
                    }
                    // Pop the query frame, then extend the unrolling: assert
                    // transition k → k+1 permanently (outside any frame).
                    let transition_k = ts.transition_at(k);
                    if !self.executor_conjuncts_supported(
                        std::slice::from_ref(&transition_k),
                        "mp-ts transition",
                    ) {
                        return Some(SingleExecutorOutcome::RetryFresh {
                            start_depth: k,
                            consecutive_unsat: 0,
                        });
                    }
                    let mut extend_script = String::from("(pop 1)\n");
                    Self::append_ts_decls_and_asserts(
                        &mut extend_script,
                        &transition_k,
                        &mut declared,
                        true,
                    );
                    let Ok(cmds) = ay_frontend::parse(&extend_script) else {
                        return Some(SingleExecutorOutcome::RetryFresh {
                            start_depth: k,
                            consecutive_unsat: 0,
                        });
                    };
                    if Self::exec_commands_with_deadline(&mut exec, &cmds, depth_deadline).is_none()
                    {
                        tracing::debug!("BMC-mp-ts: transition extension failed at depth {k}");
                        return Some(SingleExecutorOutcome::RetryFresh {
                            start_depth: k,
                            consecutive_unsat: 0,
                        });
                    }
                }
                _ => {
                    tracing::debug!("BMC-mp-ts: unknown at depth {k}; resuming fresh fallback");
                    return Some(SingleExecutorOutcome::RetryFresh {
                        start_depth: resume_level,
                        consecutive_unsat: 0,
                    });
                }
            }
        }

        // TS depths 0..=max_depth+1 discharged. Conservative: return Unknown
        // without marking `exhausted_search` — this lane makes no
        // completeness claim (see doc comment).
        Some(SingleExecutorOutcome::Solved(ChcEngineResult::Unknown))
    }

    /// Replay-confirm an engine-claimed Unsafe by bounded BMC on `problem`
    /// (inc-9 cex replay verifier; the multipred analog of the trivial-unsafe
    /// confirmation in `portfolio::trivial::confirm_trivial_unsafe_on_original`).
    ///
    /// Runs bounded BMC starting at `depth_hint` + slack (clamped to
    /// [8, 64]), iteratively deepening (doubling, capped at 64) while budget
    /// remains: the hint comes from the TRANSFORMED/inlined witness length
    /// and can under-shoot the depth needed in original clause space (a
    /// verified Unsafe at original depth ~43 was rejected when the hint
    /// clamped to 18). Returns `Some(verified_cex)` ONLY when BMC finds a
    /// counterexample whose derivation witness ADDITIONALLY passes a fresh
    /// strict `PdrSolver::try_verify_counterexample` replay against
    /// `problem`'s clauses — i.e. acceptance requires a complete, verified
    /// derivation of false reachable at bounded depth on those clauses.
    /// Every other outcome (no cex within bound, budget/depth exhaustion,
    /// missing witness, verification failure or unknown) returns `None`, so
    /// callers keep their fail-closed behavior. The engine counterexample
    /// itself is never trusted — callers pass only its DEPTH as a hint.
    pub(crate) fn replay_confirm_unsafe_on_problem(
        problem: &ChcProblem,
        depth_hint: usize,
        budget: std::time::Duration,
        cancellation_token: Option<CancellationToken>,
        verbose: bool,
    ) -> Option<Counterexample> {
        if budget < std::time::Duration::from_millis(250) {
            return None;
        }
        if problem.predicates().is_empty() || problem.queries().next().is_none() {
            return None;
        }
        // Linear problems only: the SingleLoop lane and the flat-level replay
        // are exercised and measured for linear CHC; keep the scope tight.
        if problem
            .clauses()
            .iter()
            .any(|clause| clause.body.predicates.len() > 1)
        {
            return None;
        }
        const REPLAY_DEPTH_CLAMP: usize = 64;
        // Acyclic problems get the exact-acyclic lane: path expansion is
        // exhaustive over the clause DAG, so it both finds the witness far
        // faster than the level-by-level search and makes a Safe exhaustion
        // definitive (no deeper retry can succeed).
        let acyclic = {
            let features = crate::classifier::ProblemClassifier::classify(problem);
            !features.has_cycles && features.num_predicates > 0
        };
        let deadline = ay_core::time::Instant::now() + budget;
        // Acyclic problems: the path length is bounded by the predicate
        // count, so the cyclic-deepening clamp must not truncate a finite
        // DAG whose witness the caller already located deeper than 64
        // (item 4 Stage 4: the scalarized iterator_count witness replays at
        // original depth ~324). Still hard-capped for cost.
        let depth_clamp = if acyclic {
            REPLAY_DEPTH_CLAMP
                .max(problem.predicates().len().saturating_add(4))
                .min(512)
        } else {
            REPLAY_DEPTH_CLAMP
        };
        let mut max_depth = depth_hint.saturating_add(4).clamp(8, depth_clamp);
        loop {
            let remaining = deadline.saturating_duration_since(ay_core::time::Instant::now());
            if remaining < std::time::Duration::from_millis(250) {
                return None;
            }
            if cancellation_token
                .as_ref()
                .is_some_and(CancellationToken::is_cancelled)
            {
                return None;
            }
            match Self::replay_confirm_unsafe_at_depth(
                problem,
                max_depth,
                acyclic,
                remaining,
                cancellation_token.clone(),
                verbose,
            ) {
                ReplayConfirmAttempt::Confirmed(cex) => return Some(cex),
                ReplayConfirmAttempt::BudgetExhausted => return None,
                ReplayConfirmAttempt::DefinitivelySafe => return None,
                ReplayConfirmAttempt::NotConfirmed => {}
            }
            if max_depth >= depth_clamp {
                return None;
            }
            let next_depth = max_depth.saturating_mul(2).min(depth_clamp);
            if verbose {
                safe_eprintln!(
                    "cex-replay: no confirmed witness at depth {max_depth}; \
                     deepening to {next_depth}"
                );
            }
            max_depth = next_depth;
        }
    }

    /// One bounded-BMC replay attempt at a fixed `max_depth`; see
    /// `replay_confirm_unsafe_on_problem` for the acceptance contract.
    fn replay_confirm_unsafe_at_depth(
        problem: &ChcProblem,
        max_depth: usize,
        acyclic: bool,
        budget: std::time::Duration,
        cancellation_token: Option<CancellationToken>,
        verbose: bool,
    ) -> ReplayConfirmAttempt {
        let config = BmcConfig {
            base: ChcEngineConfig {
                verbose,
                cancellation_token: cancellation_token.clone(),
            },
            max_depth,
            acyclic_safe: acyclic,
            prefer_exact_acyclic_first: acyclic,
            per_depth_timeout: Some(budget),
            time_budget: Some(budget),
            enable_k_induction: false,
            enable_adaptive_stepping: false,
            proof_cross_check: false,
            ts_probe_clamp: None,
            sweep_past_spurious_sat: true,
        };
        let solver = Self::new(problem.clone(), config);
        let result = solver.solve();
        let budget_exhausted = solver.stats().budget_exhausted;
        if verbose {
            let stats = solver.stats();
            safe_eprintln!(
                "cex-replay: bounded BMC (max_depth={max_depth}) finished: {} \
                 (depth_reached={} checks={} executor={} legacy={} budget_exhausted={})",
                match &result {
                    ChcEngineResult::Safe(_) => "Safe",
                    ChcEngineResult::Unsafe(_) => "Unsafe",
                    ChcEngineResult::Unknown => "Unknown",
                    ChcEngineResult::NotApplicable => "NotApplicable",
                },
                stats.max_depth_reached,
                stats.num_checks,
                stats.used_executor_path,
                stats.used_legacy_fallback,
                stats.budget_exhausted,
            );
        }
        let not_confirmed = || {
            if budget_exhausted {
                ReplayConfirmAttempt::BudgetExhausted
            } else {
                ReplayConfirmAttempt::NotConfirmed
            }
        };
        // An acyclic-exhaustive Safe covers every path through the clause
        // DAG, so no deeper bound can produce a counterexample.
        if acyclic && !budget_exhausted && matches!(result, ChcEngineResult::Safe(_)) {
            return ReplayConfirmAttempt::DefinitivelySafe;
        }
        let ChcEngineResult::Unsafe(cex) = result else {
            return not_confirmed();
        };
        // Acceptance requires a complete witness replay on `problem` inside
        // THIS helper, independent of which internal BMC path produced the
        // result: a witness-free Unsafe is rejected (fail closed).
        if cex
            .witness
            .as_ref()
            .is_none_or(|witness| witness.entries.is_empty())
        {
            tracing::debug!("cex-replay: BMC Unsafe lacks a derivation witness; rejecting");
            return not_confirmed();
        }
        let verify_config = PdrConfig {
            verbose,
            cancellation_token,
            solve_timeout: Some(std::time::Duration::from_secs(10)),
            strict_proofs: true,
            disable_array_scalarization: true,
            preserve_original_clauses: true,
            disable_cex_replay: true,
            ..PdrConfig::default()
        };
        let mut verifier = PdrSolver::new(problem.clone(), verify_config);
        match verifier.try_verify_counterexample(&cex) {
            Ok(CexVerificationResult::Valid) => ReplayConfirmAttempt::Confirmed(cex),
            other => {
                tracing::debug!(
                    "cex-replay: witness replay on problem clauses did not verify ({other:?}); rejecting"
                );
                not_confirmed()
            }
        }
    }

    /// Single persistent Executor with activation literals for per-depth queries.
    ///
    /// Transition constraints accumulate as permanent assertions (monotonic).
    /// The query at each depth is guarded by an activation literal:
    ///   `(assert (=> _bmc_qact_k query_k))`
    /// and solved via `(check-sat-assuming (_bmc_qact_k))`.
    ///
    /// Learned clauses persist across depths, helping deeper queries.
    /// Returns `RetryFresh` if check-sat-assuming returns unknown so the
    /// per-depth fresh path can resume at the unresolved depth.
    ///
    /// Features (#7969):
    /// - EMA tracking of per-depth solve time
    /// - Adaptive depth stepping (skip trivially fast depths)
    /// - K-induction attempts after consecutive UNSAT depths
    /// - Statistics tracking for diagnosis
    fn solve_single_executor(
        &self,
        queries: &[&HornClause],
        max_depth: usize,
    ) -> Option<SingleExecutorOutcome> {
        let start = ay_core::time::Instant::now();
        let logic = self.detect_bmc_logic();
        let mut smt_cmds = format!("(set-logic {logic})\n(set-option :produce-models true)\n");
        let mut declared_vars: FxHashSet<String> = FxHashSet::default();

        // Build level 0 constraints + declarations
        let mut level0_conjuncts = Vec::new();
        self.compile_level_flat(0, &mut level0_conjuncts);
        if !self.executor_conjuncts_supported(&level0_conjuncts, "single-executor level 0") {
            return Some(SingleExecutorOutcome::Solved(ChcEngineResult::Unknown));
        }
        for conjunct in &level0_conjuncts {
            for var in &conjunct.vars() {
                if declared_vars.insert(var.name.clone()) {
                    let sort_str = sort_to_smtlib(&var.sort);
                    let name = quote_symbol(&var.name);
                    smt_cmds.push_str(&format!("(declare-const {name} {sort_str})\n"));
                }
            }
            let s = InvariantModel::expr_to_smtlib(conjunct);
            smt_cmds.push_str(&format!("(assert {s})\n"));
        }

        // Parse and create executor with level 0 assertions
        let commands = ay_frontend::parse(&smt_cmds).ok()?;
        let mut exec = ay_dpll::Executor::new();
        Self::exec_commands(&mut exec, &commands)?;

        let mut ema_depth_time: f64 = 0.0;
        let mut consecutive_unsat: usize = 0;
        let mut adaptive_step: usize = 1;
        let mut first_unchecked_depth: Option<usize> = None;
        let mut last_added_level: usize = 0; // Track the highest level whose constraints are in the executor.

        // Depth iteration: uses adaptive stepping when enabled.
        let mut k: usize = 0;
        while k <= max_depth {
            if !self.should_continue_depth(&start) {
                tracing::debug!("BMC-single: Stopped at depth {} (budget/cancel)", k);
                self.stats.borrow_mut().budget_exhausted = true;
                return Some(SingleExecutorOutcome::Solved(ChcEngineResult::Unknown));
            }

            let depth_start = ay_core::time::Instant::now();
            let depth_deadline = self.per_depth_deadline(depth_start);

            // Add all levels from last_added_level+1 to k (handles adaptive skipping).
            if k > 0 && k > last_added_level {
                let from = last_added_level + 1;
                self.add_levels_to_executor(
                    &mut exec,
                    &mut declared_vars,
                    from,
                    k,
                    depth_deadline,
                )?;
                last_added_level = k;
            }

            // Build query at depth k. Several queries are alternatives, not a
            // conjunction: see `compile_query_groups`.
            let query_groups = self.compile_query_groups(queries, k);
            let query_conjuncts: Vec<ChcExpr> = query_groups.iter().flatten().cloned().collect();
            if !self.executor_conjuncts_supported(&query_conjuncts, "single-executor query") {
                return Some(SingleExecutorOutcome::Solved(ChcEngineResult::Unknown));
            }
            if query_conjuncts.is_empty() {
                let (next_k, next_step) =
                    self.next_depth(k, ema_depth_time, adaptive_step, max_depth);
                if next_k > k + 1 {
                    first_unchecked_depth.get_or_insert(k + 1);
                }
                k = next_k;
                adaptive_step = next_step;
                continue;
            }

            // Declare query variables + activation literal
            let act_name = format!("_bmc_qact_{k}");
            let mut query_smt = format!("(declare-const {act_name} Bool)\n");
            let mut query_declared: FxHashSet<String> = FxHashSet::default();
            for conjunct in &query_conjuncts {
                for var in &conjunct.vars() {
                    if !declared_vars.contains(&var.name) && query_declared.insert(var.name.clone())
                    {
                        let sort_str = sort_to_smtlib(&var.sort);
                        let name = quote_symbol(&var.name);
                        query_smt.push_str(&format!("(declare-const {name} {sort_str})\n"));
                    }
                }
            }

            // Assert (=> act_k <query condition>) as permanent assertion. One
            // query keeps the historical conjunction verbatim; several become
            // a disjunction of per-query conjunctions.
            let query_body =
                InvariantModel::expr_to_smtlib(&Self::query_groups_formula(&query_groups));
            query_smt.push_str(&format!("(assert (=> {act_name} {query_body}))\n"));

            // check-sat-assuming with only the bare activation literal
            query_smt.push_str(&format!("(check-sat-assuming ({act_name}))\n"));
            let cmds = ay_frontend::parse(&query_smt).ok()?;
            let outputs = Self::exec_commands_with_deadline(&mut exec, &cmds, depth_deadline)?;

            // The `(declare-const ...)` commands just emitted are PERMANENT in the
            // persistent executor, but `query_declared` is per-iteration. Without
            // folding them back, `add_levels_to_executor` re-declares the same names
            // at the next level, the elaborator rejects the duplicate, and this whole
            // lane bails to the non-incremental `solve_per_depth_fresh` fallback —
            // which restarts at depth 0 and never reaches the depths this shard needs.
            declared_vars.extend(query_declared.iter().cloned());

            // Find the check-sat result
            let result_str = outputs
                .iter()
                .find(|s| {
                    let t = s.trim();
                    t == "sat" || t == "unsat" || t == "unknown"
                })
                .map(String::as_str)
                .unwrap_or("unknown");

            // Update EMA and stats
            let depth_elapsed = depth_start.elapsed().as_secs_f64();
            ema_depth_time = EMA_ALPHA * depth_elapsed + (1.0 - EMA_ALPHA) * ema_depth_time;
            self.record_depth(k, ema_depth_time);

            tracing::debug!(
                "BMC-single: depth={} result={} time={:.3}s ema={:.3}s step={}",
                k,
                result_str,
                depth_elapsed,
                ema_depth_time,
                adaptive_step,
            );

            match result_str.trim() {
                "sat" => {
                    let model = self.observe_bmc_sat_model(
                        &mut exec,
                        k,
                        &query_conjuncts,
                        &[&declared_vars, &query_declared],
                        depth_deadline,
                    )?;
                    if !self.sweep_past_spurious_sat() {
                        // Kill switch: original give-up-after-shallow-SAT.
                        return Some(SingleExecutorOutcome::Solved(
                            self.bmc_sat_result(&model, k, queries),
                        ));
                    }
                    match self.classify_flat_sat(&model, k, queries) {
                        FlatSatOutcome::Confirmed(result) => {
                            return Some(SingleExecutorOutcome::Solved(result));
                        }
                        FlatSatOutcome::Advance => {
                            // #chc25-bmc-sweep: this shallow SAT was spurious /
                            // not strictly confirmable. Do not terminate the
                            // sweep — advance to a deeper depth to reach the
                            // real counterexample. Mark depth k as not
                            // definitively resolved so an `acyclic_safe`
                            // exhaustion never mistakes a skipped SAT for a
                            // Safe proof (fail closed).
                            first_unchecked_depth.get_or_insert(k);
                            consecutive_unsat = 0;
                            let (next_k, next_step) =
                                self.next_depth(k, ema_depth_time, adaptive_step, max_depth);
                            if next_k > k + 1 {
                                first_unchecked_depth.get_or_insert(k + 1);
                            }
                            k = next_k;
                            adaptive_step = next_step;
                            continue;
                        }
                    }
                }
                "unsat" => {
                    consecutive_unsat += 1;
                    // Try k-induction after consecutive UNSAT depths (#7969).
                    // Only attempt when: (a) k-induction is enabled, (b) enough
                    // consecutive UNSAT depths, (c) at least some non-trivial
                    // depth has been solved (don't waste time on k-induction at
                    // depth 2).
                    if self.config.enable_k_induction
                        && consecutive_unsat >= K_INDUCTION_MIN_CONSECUTIVE_UNSAT
                        && k >= K_INDUCTION_MIN_CONSECUTIVE_UNSAT
                    {
                        self.stats.borrow_mut().num_k_induction_attempts += 1;
                        if let Some(safe_result) = self.try_k_induction_check(consecutive_unsat) {
                            {
                                let mut stats = self.stats.borrow_mut();
                                stats.k_induction_proved = true;
                                stats.k_induction_k = Some(consecutive_unsat);
                            }
                            return Some(SingleExecutorOutcome::Solved(safe_result));
                        }
                    }
                    // Compute next depth
                    let (next_k, next_step) =
                        self.next_depth(k, ema_depth_time, adaptive_step, max_depth);
                    if next_k > k + 1 {
                        first_unchecked_depth.get_or_insert(k + 1);
                    }
                    if next_step > 1 {
                        self.stats.borrow_mut().used_adaptive_stepping = true;
                    }
                    k = next_k;
                    adaptive_step = next_step;
                    continue;
                }
                _ => {
                    // Unknown — re-check with a fresh executor, but skip only
                    // the prefix whose depths were all individually checked.
                    let start_depth = first_unchecked_depth.unwrap_or(k);
                    let consecutive_unsat = if first_unchecked_depth.is_some() {
                        0
                    } else {
                        consecutive_unsat
                    };
                    tracing::debug!(
                        "BMC-single: unknown at depth {}, resuming fresh fallback from {}",
                        k,
                        start_depth,
                    );
                    return Some(SingleExecutorOutcome::RetryFresh {
                        start_depth,
                        consecutive_unsat,
                    });
                }
            }
        }

        Some(self.finalize_single_executor_completion(first_unchecked_depth))
    }

    /// Per-depth fresh-executor: one check-sat per depth with cached prefix.
    ///
    /// Tracks EMA of per-depth solve time for adaptive budget stops (#7969).
    /// When `start_depth > 0`, rebuilds only the prefix for already-proved
    /// earlier levels and resumes solving at `start_depth`.
    /// `disable_lra_propagation`: when true, each per-depth executor runs
    /// with LRA theory propagation off (Fix 1, sat-side-model-search
    /// diagnosis). Passed as `true` ONLY by the transition-system lane's SAT
    /// confirmation re-solve — the flat depth-k query there has exactly the
    /// DRAGON-class shape that livelocks under propagation. All other
    /// callers pass `false` (default solver behavior).
    fn solve_per_depth_fresh(
        &self,
        queries: &[&HornClause],
        max_depth: usize,
        start_depth: usize,
        initial_consecutive_unsat: usize,
        disable_lra_propagation: bool,
    ) -> Option<ChcEngineResult> {
        let start = ay_core::time::Instant::now();
        let logic = self.detect_bmc_logic();
        let mut smt_prefix = format!("(set-logic {logic})\n(set-option :produce-models true)\n");
        let mut declared_vars: FxHashSet<String> = FxHashSet::default();
        let mut prefix_conjuncts = Vec::new();
        let mut ema_depth_time: f64 = 0.0;
        let mut consecutive_unsat: usize = initial_consecutive_unsat;
        let mut encountered_unknown = false;

        // If the single-executor path already proved depths 0..start_depth-1
        // UNSAT, rebuild only the SMT prefix for those levels and resume SAT
        // checks at `start_depth`.
        for level in 0..start_depth {
            let mut level_conjuncts = Vec::new();
            self.compile_level_flat(level, &mut level_conjuncts);
            if !self.executor_conjuncts_supported(&level_conjuncts, "fresh-executor prefix") {
                return Some(ChcEngineResult::Unknown);
            }
            for conjunct in &level_conjuncts {
                for var in &conjunct.vars() {
                    if declared_vars.insert(var.name.clone()) {
                        let sort_str = sort_to_smtlib(&var.sort);
                        let name = quote_symbol(&var.name);
                        smt_prefix.push_str(&format!("(declare-const {name} {sort_str})\n"));
                    }
                }
                let s = InvariantModel::expr_to_smtlib(conjunct);
                smt_prefix.push_str(&format!("(assert {s})\n"));
            }
            prefix_conjuncts.extend(level_conjuncts);
        }

        for k in start_depth..=max_depth {
            if !self.should_continue_depth(&start) {
                tracing::debug!("BMC-exec: Stopped at depth {} (budget/cancel)", k);
                self.stats.borrow_mut().budget_exhausted = true;
                return Some(ChcEngineResult::Unknown);
            }

            let depth_start = ay_core::time::Instant::now();
            let depth_deadline = self.per_depth_deadline(depth_start);

            // Append level k constraints to cached prefix.
            let mut level_conjuncts = Vec::new();
            self.compile_level_flat(k, &mut level_conjuncts);
            if !self.executor_conjuncts_supported(&level_conjuncts, "fresh-executor level") {
                return Some(ChcEngineResult::Unknown);
            }
            for conjunct in &level_conjuncts {
                for var in &conjunct.vars() {
                    if declared_vars.insert(var.name.clone()) {
                        let sort_str = sort_to_smtlib(&var.sort);
                        let name = quote_symbol(&var.name);
                        smt_prefix.push_str(&format!("(declare-const {name} {sort_str})\n"));
                    }
                }
                let s = InvariantModel::expr_to_smtlib(conjunct);
                smt_prefix.push_str(&format!("(assert {s})\n"));
            }
            prefix_conjuncts.extend(level_conjuncts);

            // Build query at depth k. Several queries are alternatives, not a
            // conjunction: see `compile_query_groups`.
            let query_groups = self.compile_query_groups(queries, k);
            let query_conjuncts: Vec<ChcExpr> = query_groups.iter().flatten().cloned().collect();
            if !self.executor_conjuncts_supported(&query_conjuncts, "fresh-executor query") {
                return Some(ChcEngineResult::Unknown);
            }
            if query_conjuncts.is_empty() {
                continue;
            }

            let mut smt = smt_prefix.clone();
            // #8782: Track query-local variable declarations to prevent
            // duplicate declare-const for the same variable name.
            let mut query_declared: FxHashSet<String> = FxHashSet::default();
            for conjunct in &query_conjuncts {
                for var in &conjunct.vars() {
                    if !declared_vars.contains(&var.name) && query_declared.insert(var.name.clone())
                    {
                        let sort_str = sort_to_smtlib(&var.sort);
                        let name = quote_symbol(&var.name);
                        smt.push_str(&format!("(declare-const {name} {sort_str})\n"));
                    }
                }
            }
            if query_groups.len() > 1 {
                // Alternatives: assert the disjunction of per-query
                // conjunctions rather than every conjunct at once.
                let disjunction =
                    InvariantModel::expr_to_smtlib(&Self::query_groups_formula(&query_groups));
                smt.push_str(&format!("(assert {disjunction})\n"));
            } else {
                for conjunct in &query_conjuncts {
                    let s = InvariantModel::expr_to_smtlib(conjunct);
                    smt.push_str(&format!("(assert {s})\n"));
                }
            }
            smt.push_str("(check-sat)\n");

            let commands = ay_frontend::parse(&smt).ok()?;
            let mut exec = ay_dpll::Executor::new();
            if disable_lra_propagation {
                // TS-lane confirmation re-solve: see the doc comment above.
                exec.set_no_lra_theory_propagation(true);
            }
            let outputs = Self::exec_commands_with_deadline(&mut exec, &commands, depth_deadline)?;

            let result_str = outputs.first().map(String::as_str).unwrap_or("unknown");

            // Update EMA and stats
            let depth_elapsed = depth_start.elapsed().as_secs_f64();
            ema_depth_time = EMA_ALPHA * depth_elapsed + (1.0 - EMA_ALPHA) * ema_depth_time;
            self.record_depth(k, ema_depth_time);

            tracing::debug!(
                "BMC-exec: depth={} result={} time={:.3}s ema={:.3}s",
                k,
                result_str,
                depth_elapsed,
                ema_depth_time
            );

            if result_str == "sat" {
                let model = self.observe_bmc_sat_model(
                    &mut exec,
                    k,
                    &query_conjuncts,
                    &[&declared_vars, &query_declared],
                    depth_deadline,
                )?;
                if !self.sweep_past_spurious_sat() {
                    // Kill switch: original give-up-after-shallow-SAT.
                    return Some(self.bmc_sat_result(&model, k, queries));
                }
                match self.classify_flat_sat(&model, k, queries) {
                    FlatSatOutcome::Confirmed(result) => return Some(result),
                    FlatSatOutcome::Advance => {
                        // #chc25-bmc-sweep: shallow SAT spurious / not strictly
                        // confirmable — keep sweeping deeper instead of giving
                        // up. Mark the run inconclusive so an `acyclic_safe`
                        // exhaustion cannot mistake the skipped SAT for a Safe
                        // proof (fail closed).
                        encountered_unknown = true;
                        consecutive_unsat = 0;
                        continue;
                    }
                }
            } else if result_str == "unsat" {
                consecutive_unsat += 1;
                // Try k-induction after consecutive UNSAT depths (#7969)
                if self.config.enable_k_induction
                    && consecutive_unsat >= K_INDUCTION_MIN_CONSECUTIVE_UNSAT
                    && k >= K_INDUCTION_MIN_CONSECUTIVE_UNSAT
                {
                    self.stats.borrow_mut().num_k_induction_attempts += 1;
                    if let Some(safe_result) = self.try_k_induction_check(consecutive_unsat) {
                        {
                            let mut stats = self.stats.borrow_mut();
                            stats.k_induction_proved = true;
                            stats.k_induction_k = Some(consecutive_unsat);
                        }
                        return Some(safe_result);
                    }
                }
            } else {
                if let Some(model) = self.try_nested_select_observation_candidate(
                    &prefix_conjuncts,
                    &query_groups,
                    k,
                    disable_lra_propagation,
                    depth_deadline,
                ) {
                    if !self.sweep_past_spurious_sat() {
                        // The compatibility kill switch may stop the sweep,
                        // but the relaxed assignment still passes through the
                        // unchanged original-clause replay in `bmc_sat_result`.
                        return Some(self.bmc_sat_result(&model, k, queries));
                    }
                    if let FlatSatOutcome::Confirmed(result) =
                        self.classify_flat_sat(&model, k, queries)
                    {
                        return Some(result);
                    }
                }
                encountered_unknown = true;
                consecutive_unsat = 0;
            }
        }

        Some(self.finalize_bounded_search(encountered_unknown))
    }

    // ============ K-Induction (#7969) ============

    /// Attempt forward k-induction to prove safety.
    ///
    /// Forward k-induction check for step k:
    ///   NOT_Q(x_0) AND Tr(x_0,x_1) AND NOT_Q(x_1) AND ... AND Tr(x_{k-1},x_k) => NOT_Q(x_k)
    ///
    /// Equivalently, check UNSAT of:
    ///   NOT_Q(x_0) AND Tr(x_0,x_1) AND ... AND NOT_Q(x_{k-1}) AND Tr(x_{k-1},x_k) AND Q(x_k)
    ///
    /// If UNSAT, the property is k-inductive and the system is Safe.
    fn try_k_induction_check(&self, k: usize) -> Option<ChcEngineResult> {
        let ts = match TransitionSystem::from_chc_problem(&self.problem) {
            Ok(ts) => ts,
            Err(_) => return None,
        };
        let check_start = ay_core::time::Instant::now();
        let check_deadline = self.per_depth_deadline(check_start);

        // Build: NOT_Q(x_0) AND Tr(x_0,x_1) AND NOT_Q(x_1) AND ... AND Q(x_k)
        let mut conjuncts = Vec::new();

        // For steps 0..k-1: NOT_Q(x_i) AND Tr(x_i, x_{i+1})
        for i in 0..k {
            conjuncts.push(ts.neg_query_at(i));
            conjuncts.push(ts.transition_at(i));
        }
        // Final step: Q(x_k) (the negation of what we want to prove)
        conjuncts.push(ts.query_at(k));

        let formula = ChcExpr::and_all(conjuncts);
        if !self.executor_conjuncts_supported(std::slice::from_ref(&formula), "k-induction") {
            return None;
        }

        // Serialize and check
        let logic = self.detect_bmc_logic();
        let mut smt = format!("(set-logic {logic})\n");

        // Declare all variables
        let mut declared: FxHashSet<String> = FxHashSet::default();
        for var in &formula.vars() {
            if declared.insert(var.name.clone()) {
                let sort_str = sort_to_smtlib(&var.sort);
                let name = quote_symbol(&var.name);
                smt.push_str(&format!("(declare-const {name} {sort_str})\n"));
            }
        }

        let s = InvariantModel::expr_to_smtlib(&formula);
        smt.push_str(&format!("(assert {s})\n(check-sat)\n"));

        let commands = ay_frontend::parse(&smt).ok()?;
        let mut exec = ay_dpll::Executor::new();
        let outputs = Self::exec_commands_with_deadline(&mut exec, &commands, check_deadline)?;

        let result_str = outputs.first().map(String::as_str).unwrap_or("unknown");
        tracing::debug!("BMC k-induction: k={} result={}", k, result_str);

        if result_str.trim() == "unsat" {
            tracing::debug!("BMC: k-induction proved safety at k={}", k);
            Some(ChcEngineResult::Safe(InvariantModel::default()))
        } else {
            None
        }
    }

    /// Detect the SMT-LIB logic for this BMC problem based on sorts used.
    fn detect_bmc_logic(&self) -> &'static str {
        Self::detect_bmc_logic_for(&self.problem)
    }

    /// Detect the SMT-LIB logic for an arbitrary problem based on sorts used.
    ///
    /// The multipred SingleLoop lane (inc-9) computes the logic from its
    /// SYNTHETIC problem: the location encoding adds Int state variables, so
    /// e.g. a pure-Bool original still needs an Int-capable logic.
    fn detect_bmc_logic_for(problem: &ChcProblem) -> &'static str {
        let mut has_bv = false;
        let mut has_real = false;
        let mut has_array = false;
        for pred in problem.predicates() {
            for sort in &pred.arg_sorts {
                match sort {
                    ChcSort::BitVec(_) => has_bv = true,
                    ChcSort::Real => has_real = true,
                    ChcSort::Array(_, _) => has_array = true,
                    _ => {}
                }
            }
        }
        if has_array {
            if has_bv {
                "QF_ABV"
            } else {
                "QF_AUFLIA"
            }
        } else if has_bv {
            "QF_BV"
        } else if has_real {
            "QF_LIRA"
        } else {
            "QF_LIA"
        }
    }

    /// Execute commands via the executor with panic safety.
    /// Returns `Some(outputs)` on success, `None` on failure.
    fn exec_commands(
        exec: &mut ay_dpll::Executor,
        commands: &[ay_frontend::Command],
    ) -> Option<Vec<String>> {
        ay_core::catch_ay_panics(
            AssertUnwindSafe(|| match exec.execute_all(commands) {
                Ok(out) => Ok(out),
                Err(e) => {
                    tracing::debug!("BMC-exec: executor error: {e}");
                    Err(())
                }
            }),
            |reason| {
                tracing::debug!("BMC-exec: ay panic: {reason}");
                Err(())
            },
        )
        .ok()
    }

    /// Execute commands with an optional per-batch executor deadline.
    fn exec_commands_with_deadline(
        exec: &mut ay_dpll::Executor,
        commands: &[ay_frontend::Command],
        deadline: Option<ay_core::time::Instant>,
    ) -> Option<Vec<String>> {
        exec.set_deadline(deadline);
        let result = Self::exec_commands(exec, commands);
        exec.set_deadline(None);
        result
    }

    /// Convert the configured per-depth timeout into an absolute deadline.
    ///
    /// inc-12: clamped to the overall solve deadline. The per-depth timeout is
    /// typically the FULL lane budget (e.g. the front BMC probe sets
    /// `per_depth_timeout == time_budget`), so a depth check started late in
    /// the budget used to get a whole extra budget worth of executor time.
    fn per_depth_deadline(
        &self,
        started_at: ay_core::time::Instant,
    ) -> Option<ay_core::time::Instant> {
        let per_depth = self
            .config
            .per_depth_timeout
            .map(|timeout| started_at + timeout);
        match (per_depth, self.solve_deadline.get()) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        }
    }

    // ============ Level-Based Encoding Helpers ============
    // Based on Z3's dl_bmc_engine.cpp linear BMC class

    /// Create level predicate: `P#level` (boolean)
    ///
    /// This represents "predicate P is reachable at level"
    fn level_predicate(&self, pred: PredicateId, level: usize) -> ChcExpr {
        let pred_info = self
            .problem
            .get_predicate(pred)
            .expect("BmcSolver: predicate ID from problem should be valid");
        let name = format!("{}#{}", pred_info.name, level);
        ChcExpr::Var(ChcVar::new(name, ChcSort::Bool))
    }

    /// Create level argument: `P#level_idx` (appropriate sort)
    ///
    /// This represents "argument idx of predicate P at level"
    fn level_arg(&self, pred: PredicateId, idx: usize, level: usize) -> ChcExpr {
        let pred_info = self
            .problem
            .get_predicate(pred)
            .expect("BmcSolver: predicate ID from problem should be valid");
        let name = format!("{}#{}_{}", pred_info.name, level, idx);
        let sort = pred_info
            .arg_sorts
            .get(idx)
            .expect("BmcSolver: argument index should be within predicate arity")
            .clone();
        ChcExpr::Var(ChcVar::new(name, sort))
    }

    /// Create rule indicator: `rule:P#level_rule_idx` (boolean)
    ///
    /// This represents "rule rule_idx was used to derive P at level"
    fn rule_indicator(&self, pred: PredicateId, rule_idx: usize, level: usize) -> ChcExpr {
        let pred_info = self
            .problem
            .get_predicate(pred)
            .expect("BmcSolver: predicate ID from problem should be valid");
        let name = format!("rule:{}#{}_{}", pred_info.name, level, rule_idx);
        ChcExpr::Var(ChcVar::new(name, ChcSort::Bool))
    }

    /// Create level variable: `P#level_rule_idx_var_idx` (appropriate sort)
    ///
    /// This represents internal variables used in a rule at a specific level
    fn level_var(
        &self,
        pred: PredicateId,
        rule_idx: usize,
        var_idx: usize,
        level: usize,
        sort: ChcSort,
    ) -> ChcExpr {
        let pred_info = self
            .problem
            .get_predicate(pred)
            .expect("BmcSolver: predicate ID from problem should be valid");
        let name = format!("{}#{}_{}_{}", pred_info.name, level, rule_idx, var_idx);
        ChcExpr::Var(ChcVar::new(name, sort))
    }

    /// Build variable substitution for a rule at a level
    ///
    /// Following Z3's mk_rule_vars approach:
    /// 1. Head arguments map to level arguments
    /// 2. Body predicate arguments map to level-1 arguments
    /// 3. Remaining variables get unique level-specific names
    fn mk_rule_vars(
        &self,
        clause: &HornClause,
        head_pred: PredicateId,
        rule_idx: usize,
        level: usize,
    ) -> FxHashMap<String, ChcExpr> {
        let mut subst: FxHashMap<String, ChcExpr> = FxHashMap::default();

        // 1. Map head argument variables to level arguments.
        if let ClauseHead::Predicate(_, head_args) = &clause.head {
            for (k, arg) in head_args.iter().enumerate() {
                if let ChcExpr::Var(v) = arg {
                    if !subst.contains_key(&v.name) {
                        subst.insert(v.name.clone(), self.level_arg(head_pred, k, level));
                    }
                }
            }
        }

        // 2. Map body predicate argument variables to (level-1) arguments.
        if level > 0 {
            for (body_pred, body_args) in &clause.body.predicates {
                for (k, arg) in body_args.iter().enumerate() {
                    if let ChcExpr::Var(v) = arg {
                        if !subst.contains_key(&v.name) {
                            subst.insert(v.name.clone(), self.level_arg(*body_pred, k, level - 1));
                        }
                    }
                }
            }
        }

        // 3. Map remaining variables to level-specific variables
        let mut var_idx = 0;
        let body_vars = clause.body.vars();
        for v in body_vars {
            if !subst.contains_key(&v.name) {
                subst.insert(
                    v.name.clone(),
                    self.level_var(head_pred, rule_idx, var_idx, level, v.sort.clone()),
                );
                var_idx += 1;
            }
        }

        subst
    }

    /// Compile level constraints for a single level
    fn compile_level(&self, level: usize, conjuncts: &mut Vec<ChcExpr>) {
        for pred in self.problem.predicates() {
            let rules: Vec<_> = self.problem.clauses_defining_with_index(pred.id).collect();
            if rules.is_empty() {
                // A predicate with NO defining clause is empty in the least
                // model — it can never be derived at any level. Pinning its
                // flag to false is EXACT, not an approximation, and it is
                // load-bearing once `expand_nullary_fail_queries` splits one
                // `(query error)` into per-lane queries: leaving the flag FREE
                // made a query over such a "dead lane" trivially satisfiable at
                // every depth, so the query disjunction was always SAT with no
                // extractable derivation and every depth degraded to Unknown —
                // masking a real counterexample in another lane.
                conjuncts.push(ChcExpr::not(self.level_predicate(pred.id, level)));
                continue;
            }

            let mut rule_indicators = Vec::new();

            for (rule_idx, clause) in &rules {
                let rule_ind = self.rule_indicator(pred.id, *rule_idx, level);
                rule_indicators.push(rule_ind.clone());

                if level == 0 && !clause.body.predicates.is_empty() {
                    conjuncts.push(ChcExpr::not(rule_ind));
                    continue;
                }

                let mut rule_conjuncts = Vec::new();
                let subst = self.mk_rule_vars(clause, pred.id, *rule_idx, level);

                if let ClauseHead::Predicate(_, head_args) = &clause.head {
                    for (arg_idx, head_arg) in head_args.iter().enumerate() {
                        let level_arg = self.level_arg(pred.id, arg_idx, level);
                        let substituted_arg = head_arg.substitute_name_map(&subst);
                        rule_conjuncts.push(ChcExpr::eq(level_arg, substituted_arg));
                    }
                }

                for (body_pred, body_args) in &clause.body.predicates {
                    debug_assert!(level > 0, "Body predicate at level 0 should be disabled");
                    rule_conjuncts.push(self.level_predicate(*body_pred, level - 1));
                    for (arg_idx, body_arg) in body_args.iter().enumerate() {
                        let level_arg = self.level_arg(*body_pred, arg_idx, level - 1);
                        let substituted_arg = body_arg.substitute_name_map(&subst);
                        rule_conjuncts.push(ChcExpr::eq(level_arg, substituted_arg));
                    }
                }

                if let Some(constraint) = &clause.body.constraint {
                    let substituted = constraint.substitute_name_map(&subst);
                    rule_conjuncts.push(substituted);
                }

                if !rule_conjuncts.is_empty() {
                    let body = ChcExpr::and_all(rule_conjuncts.iter().cloned());
                    conjuncts.push(ChcExpr::implies(rule_ind, body));
                }
            }

            if !rule_indicators.is_empty() {
                let level_pred = self.level_predicate(pred.id, level);
                let or_rules = ChcExpr::or_all(rule_indicators);
                conjuncts.push(ChcExpr::implies(level_pred, or_rules));
            }
        }
    }

    /// Compile EVERY query clause at `level`, keeping one conjunct group per
    /// query.
    ///
    /// A CHC problem is violated when ANY query fires, so the level-BMC query
    /// condition is the DISJUNCTION over queries — never their conjunction.
    /// The distinction is invisible for the classic single nullary
    /// `(query error)` shape, but `ChcProblem::expand_nullary_fail_queries`
    /// rewrites that shape into ONE query per `body => error` clause, whose
    /// bodies mention DIFFERENT predicates ("lanes"). Conjoining those made
    /// every depth demand that all lanes fire simultaneously at the SAME
    /// level, which is essentially never satisfiable, so the level loop
    /// reported Unknown on problems it converts fine before expansion.
    ///
    /// Groups share the level-argument variables (`P#k_i`), which is exactly
    /// right: each disjunct constrains the single modeled level-`k` state, so
    /// a satisfying model exhibits one genuinely reachable query. Empty groups
    /// (a query that compiles to nothing at this level) are dropped, matching
    /// the acyclic-exhaustive lane's existing per-query disjunction.
    fn compile_query_groups(&self, queries: &[&HornClause], level: usize) -> Vec<Vec<ChcExpr>> {
        let mut groups = Vec::with_capacity(queries.len());
        for query in queries {
            let mut group = Vec::new();
            self.compile_query(query, level, &mut group);
            if !group.is_empty() {
                groups.push(group);
            }
        }
        groups
    }

    /// Fold per-query conjunct groups into the level's query condition.
    ///
    /// Zero or one group reproduces the historical `and_all` formula exactly;
    /// several groups become a disjunction of per-query conjunctions.
    fn query_groups_formula(groups: &[Vec<ChcExpr>]) -> ChcExpr {
        if groups.len() > 1 {
            ChcExpr::or_all(
                groups
                    .iter()
                    .map(|group| ChcExpr::and_all(group.iter().cloned())),
            )
        } else {
            ChcExpr::and_all(groups.iter().flatten().cloned())
        }
    }

    /// Compile a query clause at a specific level
    fn compile_query(&self, query: &HornClause, level: usize, conjuncts: &mut Vec<ChcExpr>) {
        let mut subst: FxHashMap<String, ChcExpr> = FxHashMap::default();
        let mut deferred_equalities: Vec<(ChcExpr, ChcExpr)> = Vec::new();

        for (body_pred, body_args) in &query.body.predicates {
            conjuncts.push(self.level_predicate(*body_pred, level));

            for (arg_idx, body_arg) in body_args.iter().enumerate() {
                let level_var = self.level_arg(*body_pred, arg_idx, level);
                if let ChcExpr::Var(v) = body_arg {
                    if !subst.contains_key(&v.name) {
                        subst.insert(v.name.clone(), level_var);
                    } else {
                        conjuncts.push(ChcExpr::eq(level_var, subst[&v.name].clone()));
                    }
                } else {
                    deferred_equalities.push((level_var, body_arg.clone()));
                }
            }
        }

        for (level_var, raw_expr) in deferred_equalities {
            let substituted_arg = raw_expr.substitute_name_map(&subst);
            conjuncts.push(ChcExpr::eq(level_var, substituted_arg));
        }

        if let Some(constraint) = &query.body.constraint {
            let substituted = constraint.substitute_name_map(&subst);
            conjuncts.push(substituted);
        }
    }

    fn bmc_trace_values(
        &self,
        max_depth: usize,
        query_conjuncts: &[ChcExpr],
    ) -> Vec<BmcTraceValue> {
        let mut values = Vec::new();
        let mut seen_vars = FxHashSet::default();
        for level in 0..=max_depth {
            for predicate in self.problem.predicates() {
                for (idx, sort) in predicate.arg_sorts.iter().enumerate() {
                    if !Self::trace_assignment_sort_supported(sort) {
                        continue;
                    }
                    let level_arg = self.level_arg(predicate.id, idx, level);
                    let ChcExpr::Var(var) = &level_arg else {
                        continue;
                    };
                    if seen_vars.insert(var.name.clone()) {
                        values.push(BmcTraceValue::Var(var.clone()));
                    }
                }
            }
        }

        // `get-model` may fail as a whole when even one declared array lacks a
        // printable total interpretation.  Keep witness reconstruction
        // independent of that command by explicitly querying every scalar
        // variable used by the flattened levels and query: reachability flags,
        // rule-local variables, and predicate arguments alike.
        for level in 0..=max_depth {
            let mut level_conjuncts = Vec::new();
            self.compile_level_flat(level, &mut level_conjuncts);
            for conjunct in &level_conjuncts {
                Self::collect_trace_scalar_vars(conjunct, &mut values, &mut seen_vars);
            }
        }
        for conjunct in query_conjuncts {
            Self::collect_trace_scalar_vars(conjunct, &mut values, &mut seen_vars);
        }

        if self.problem.has_array_sorts() {
            let mut seen = FxHashSet::default();
            for level in 0..=max_depth {
                let mut level_conjuncts = Vec::new();
                self.compile_level_flat(level, &mut level_conjuncts);
                for conjunct in &level_conjuncts {
                    Self::collect_trace_array_selects(conjunct, &mut values, &mut seen);
                }
            }
            for conjunct in query_conjuncts {
                Self::collect_trace_array_selects(conjunct, &mut values, &mut seen);
            }
        }

        values
    }

    fn collect_trace_scalar_vars(
        expr: &ChcExpr,
        values: &mut Vec<BmcTraceValue>,
        seen: &mut FxHashSet<String>,
    ) {
        for var in expr.vars() {
            if Self::trace_assignment_sort_supported(&var.sort) && seen.insert(var.name.clone()) {
                values.push(BmcTraceValue::Var(var));
            }
        }
    }

    fn trace_assignment_sort_supported(sort: &ChcSort) -> bool {
        matches!(sort, ChcSort::Bool | ChcSort::Int | ChcSort::BitVec(_))
    }

    /// Keep only trace values whose terms reference DECLARED symbols (inc-9).
    ///
    /// `bmc_trace_values` enumerates level-arg variables for every predicate
    /// at every level, but `compile_level_flat` only declares variables that
    /// appear in some emitted conjunct. A predicate with no fact clause has
    /// no argument variables at level 0 (its level constraint is just
    /// `(not pred@0)`), so the `(get-value ...)` command referenced undefined
    /// symbols and the WHOLE executor run failed with an elaboration error —
    /// silently knocking every multipred problem with a fact-free predicate
    /// (the llreve family shape) off the executor path onto the legacy
    /// fallback (4-6s/check).
    fn retain_declared_trace_values(
        values: &mut Vec<BmcTraceValue>,
        declared: &[&FxHashSet<String>],
    ) {
        values.retain(|value| {
            value
                .term()
                .vars()
                .iter()
                .all(|var| declared.iter().any(|set| set.contains(&var.name)))
        });
    }

    fn collect_trace_array_selects(
        expr: &ChcExpr,
        values: &mut Vec<BmcTraceValue>,
        seen: &mut FxHashSet<String>,
    ) {
        match expr {
            ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
                if let Some((array, indices, value_sort)) =
                    Self::trace_scalar_array_select_path(expr)
                {
                    let key = format!("{expr:?}");
                    if seen.insert(key) {
                        values.push(BmcTraceValue::ArraySelectPath {
                            array,
                            indices,
                            value_sort,
                        });
                    }
                }
                for arg in args {
                    Self::collect_trace_array_selects(arg.as_ref(), values, seen);
                }
            }
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => {
                for arg in args {
                    Self::collect_trace_array_selects(arg.as_ref(), values, seen);
                }
            }
            ChcExpr::ConstArray(_, value) => {
                Self::collect_trace_array_selects(value.as_ref(), values, seen);
            }
            ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::Var(_)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => {}
        }
    }

    /// Decompose a scalar-valued nested select into its base variable and
    /// outer-to-inner index path.
    ///
    /// For example, `(select (select F P) 0)` becomes
    /// `F, [(P, Array Int Int), (0, Int)]`. The old trace collector only kept
    /// `(select A i)` when BOTH `A` and `i` were scalar-addressed, so it missed
    /// exactly these array-indexed Solidity reads.
    fn trace_scalar_array_select_path(
        expr: &ChcExpr,
    ) -> Option<(ChcVar, Vec<(ChcExpr, ChcSort)>, ChcSort)> {
        let (array, indices, value_sort) = Self::trace_array_select_path(expr)?;
        if !Self::trace_assignment_sort_supported(&value_sort) {
            return None;
        }
        Some((array, indices, value_sort))
    }

    /// Decompose any concretely modelable select chain. Unlike
    /// `trace_scalar_array_select_path`, this also accepts an array-valued
    /// result so a collided composite key such as `(select^4 C h)` can be
    /// completed at its finite base-array path.
    fn trace_array_select_path(
        expr: &ChcExpr,
    ) -> Option<(ChcVar, Vec<(ChcExpr, ChcSort)>, ChcSort)> {
        let value_sort = expr.sort();
        if !Self::trace_model_sort_supported(&value_sort) {
            return None;
        }
        let mut current = expr;
        let mut reversed = Vec::new();
        loop {
            let ChcExpr::Op(ChcOp::Select, args) = current else {
                break;
            };
            let [array_expr, index_expr] = args.as_slice() else {
                return None;
            };
            let ChcSort::Array(index_sort, _) = array_expr.sort() else {
                return None;
            };
            if !Self::trace_model_sort_supported(&index_sort) {
                return None;
            }
            reversed.push((index_expr.as_ref().clone(), index_sort.as_ref().clone()));
            current = array_expr.as_ref();
        }

        let ChcExpr::Var(array) = current else {
            return None;
        };
        if reversed.is_empty() || !Self::trace_model_sort_supported(&array.sort) {
            return None;
        }
        reversed.reverse();
        Some((array.clone(), reversed, value_sort))
    }

    fn trace_model_sort_supported(sort: &ChcSort) -> bool {
        match sort {
            ChcSort::Bool | ChcSort::Int | ChcSort::BitVec(_) => true,
            ChcSort::Array(index, value) => {
                Self::trace_model_sort_supported(index) && Self::trace_model_sort_supported(value)
            }
            ChcSort::Real | ChcSort::Uninterpreted(_) | ChcSort::Datatype { .. } => false,
        }
    }

    fn sort_mentions_array_deep(sort: &ChcSort) -> bool {
        fn visit(sort: &ChcSort, visiting_datatypes: &mut FxHashSet<String>) -> bool {
            match sort {
                ChcSort::Array(_, _) => true,
                ChcSort::Datatype { name, constructors } => {
                    if !visiting_datatypes.insert(name.clone()) {
                        return false;
                    }
                    let contains = constructors.iter().any(|constructor| {
                        constructor
                            .selectors
                            .iter()
                            .any(|selector| visit(&selector.sort, visiting_datatypes))
                    });
                    visiting_datatypes.remove(name);
                    contains
                }
                ChcSort::Bool
                | ChcSort::Int
                | ChcSort::Real
                | ChcSort::BitVec(_)
                | ChcSort::Uninterpreted(_) => false,
            }
        }

        visit(sort, &mut FxHashSet::default())
    }

    /// Match the same sort shape that the public Executor's nested-array
    /// UNSAT quarantine recognizes: an array whose index or element sort
    /// itself contains an array.
    fn is_nested_array_sort(sort: &ChcSort) -> bool {
        let ChcSort::Array(index, value) = sort else {
            return false;
        };
        Self::sort_mentions_array_deep(index) || Self::sort_mentions_array_deep(value)
    }

    fn push_nested_candidate_children<'a>(expr: &'a ChcExpr, stack: &mut Vec<&'a ChcExpr>) {
        match expr {
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => {
                stack.extend(args.iter().rev().map(AsRef::as_ref));
            }
            ChcExpr::ConstArray(_, value) => stack.push(value.as_ref()),
            ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::Var(_)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => {}
        }
    }

    /// Collect maximal non-nested values read from nested-array state.
    ///
    /// This includes flat-array-valued reads such as
    /// `(select (select C key) field) : (Array Int Int)`. Identical reads are
    /// recorded once so congruent occurrences share one abstraction variable.
    fn collect_nested_select_alias_terms(
        expr: &ChcExpr,
        leaves: &mut Vec<(ChcExpr, ChcVar, Vec<(ChcExpr, ChcSort)>, ChcSort)>,
        seen: &mut FxHashSet<ChcExpr>,
        budget: &mut BmcNestedArrayTraversalBudget,
    ) -> Result<(), BmcNestedArrayCandidateAbort> {
        let mut stack = vec![expr];
        while let Some(current) = stack.pop() {
            budget.consume()?;
            if let Some((array, indices, value_sort)) = Self::trace_array_select_path(current) {
                if Self::is_nested_array_sort(&array.sort)
                    && !Self::is_nested_array_sort(&value_sort)
                {
                    if seen.insert(current.clone()) {
                        leaves.push((current.clone(), array, indices, value_sort));
                        if leaves.len() > MAX_NESTED_SELECT_CANDIDATE_ALIASES {
                            return Err(BmcNestedArrayCandidateAbort::ObservationCap);
                        }
                    }
                    continue;
                }
            }
            Self::push_nested_candidate_children(current, &mut stack);
        }
        Ok(())
    }

    /// Collect maximal terms whose values still have nested-array sort.
    ///
    /// These are candidate state-plumbing terms, normally level arguments,
    /// rule-local variables, or a complete `store`/`ite` term. Stopping at the
    /// maximal term keeps the later Int substitution well-sorted at equality
    /// boundaries instead of substituting an Int into the middle of an array
    /// operation.
    fn collect_nested_array_token_terms(
        expr: &ChcExpr,
        terms: &mut Vec<ChcExpr>,
        seen: &mut FxHashSet<ChcExpr>,
        budget: &mut BmcNestedArrayTraversalBudget,
    ) -> Result<(), BmcNestedArrayCandidateAbort> {
        let mut stack = vec![expr];
        while let Some(current) = stack.pop() {
            budget.consume()?;
            if Self::is_nested_array_sort(&current.sort()) {
                if seen.insert(current.clone()) {
                    terms.push(current.clone());
                    if terms.len() > MAX_NESTED_ARRAY_CANDIDATE_TOKENS {
                        return Err(BmcNestedArrayCandidateAbort::StateTokenCap);
                    }
                }
                continue;
            }
            Self::push_nested_candidate_children(current, &mut stack);
        }
        Ok(())
    }

    fn expr_contains_nested_array_sort(
        expr: &ChcExpr,
        budget: &mut BmcNestedArrayTraversalBudget,
    ) -> Result<bool, BmcNestedArrayCandidateAbort> {
        let mut stack = vec![expr];
        while let Some(current) = stack.pop() {
            budget.consume()?;
            if Self::is_nested_array_sort(&current.sort()) {
                return Ok(true);
            }
            Self::push_nested_candidate_children(current, &mut stack);
        }
        Ok(false)
    }

    /// Reject any non-nested parent that would receive an Int token where its
    /// original child sort was nested-array. Equality/disequality are the only
    /// supported boundaries: replacing both same-sorted operands with Int
    /// preserves their Boolean structure. A surviving `select(store(...), i)`
    /// or nested-array UF argument would otherwise serialize as ill-typed SMT.
    fn validate_nested_array_token_boundaries(
        expr: &ChcExpr,
        budget: &mut BmcNestedArrayTraversalBudget,
    ) -> Result<(), BmcNestedArrayCandidateAbort> {
        let mut stack = vec![expr];
        while let Some(current) = stack.pop() {
            budget.consume()?;
            if Self::is_nested_array_sort(&current.sort()) {
                continue;
            }
            match current {
                ChcExpr::Op(ChcOp::Eq | ChcOp::Ne, args) => {
                    let nested_children = args
                        .iter()
                        .filter(|arg| Self::is_nested_array_sort(&arg.sort()))
                        .count();
                    if nested_children != 0 {
                        if args.len() != 2 || nested_children != 2 {
                            return Err(BmcNestedArrayCandidateAbort::UnsupportedNestedBoundary);
                        }
                        continue;
                    }
                    stack.extend(args.iter().rev().map(AsRef::as_ref));
                }
                ChcExpr::Op(_, args)
                | ChcExpr::PredicateApp(_, _, args)
                | ChcExpr::FuncApp(_, _, args) => {
                    if args
                        .iter()
                        .any(|arg| Self::is_nested_array_sort(&arg.sort()))
                    {
                        return Err(BmcNestedArrayCandidateAbort::UnsupportedNestedBoundary);
                    }
                    stack.extend(args.iter().rev().map(AsRef::as_ref));
                }
                ChcExpr::ConstArray(_, value) => {
                    if Self::is_nested_array_sort(&value.sort()) {
                        return Err(BmcNestedArrayCandidateAbort::UnsupportedNestedBoundary);
                    }
                    stack.push(value.as_ref());
                }
                ChcExpr::Bool(_)
                | ChcExpr::Int(_)
                | ChcExpr::Real(_, _)
                | ChcExpr::BitVec(_, _)
                | ChcExpr::Var(_)
                | ChcExpr::ConstArrayMarker(_)
                | ChcExpr::IsTesterMarker(_) => {}
            }
        }
        Ok(())
    }

    fn collect_nested_array_var_equalities(
        expr: &ChcExpr,
        adjacency: &mut FxHashMap<ChcVar, FxHashSet<ChcVar>>,
        equality_count: &mut usize,
        budget: &mut BmcNestedArrayTraversalBudget,
    ) -> Result<(), BmcNestedArrayCandidateAbort> {
        let mut stack = vec![expr];
        while let Some(current) = stack.pop() {
            budget.consume()?;
            if let ChcExpr::Op(ChcOp::Eq, args) = current {
                if let [lhs, rhs] = args.as_slice() {
                    if let (ChcExpr::Var(lhs), ChcExpr::Var(rhs)) = (lhs.as_ref(), rhs.as_ref()) {
                        if lhs != rhs
                            && lhs.sort == rhs.sort
                            && Self::is_nested_array_sort(&lhs.sort)
                        {
                            let inserted = adjacency
                                .entry(lhs.clone())
                                .or_default()
                                .insert(rhs.clone());
                            adjacency
                                .entry(rhs.clone())
                                .or_default()
                                .insert(lhs.clone());
                            if inserted {
                                *equality_count = (*equality_count).saturating_add(1);
                                if *equality_count > MAX_NESTED_ARRAY_CANDIDATE_EQUALITIES {
                                    return Err(BmcNestedArrayCandidateAbort::EqualityCap);
                                }
                            }
                        }
                    }
                }
            }
            Self::push_nested_candidate_children(current, &mut stack);
        }
        Ok(())
    }

    fn nested_array_var_equivalences<'a>(
        exprs: impl IntoIterator<Item = &'a ChcExpr>,
        budget: &mut BmcNestedArrayTraversalBudget,
    ) -> Result<Vec<BmcNestedArrayEquivalence>, BmcNestedArrayCandidateAbort> {
        let mut adjacency: FxHashMap<ChcVar, FxHashSet<ChcVar>> = FxHashMap::default();
        let mut equality_count = 0usize;
        for expr in exprs {
            Self::collect_nested_array_var_equalities(
                expr,
                &mut adjacency,
                &mut equality_count,
                budget,
            )?;
        }

        let mut roots: Vec<ChcVar> = adjacency.keys().cloned().collect();
        roots.sort();
        let mut visited = FxHashSet::default();
        let mut components = Vec::new();
        for root in roots {
            if !visited.insert(root.clone()) {
                continue;
            }
            let mut stack = vec![root];
            let mut variables = Vec::new();
            while let Some(variable) = stack.pop() {
                variables.push(variable.clone());
                for neighbor in adjacency.get(&variable).into_iter().flatten() {
                    if visited.insert(neighbor.clone()) {
                        stack.push(neighbor.clone());
                    }
                }
            }
            variables.sort();
            if variables.len() > 1 {
                components.push(BmcNestedArrayEquivalence { variables });
            }
        }
        components.sort_by(|left, right| left.variables[0].cmp(&right.variables[0]));
        Ok(components)
    }

    /// Relax nested reads and state plumbing across one complete depth formula.
    ///
    /// This is a candidate generator, not an equisatisfiable transform:
    /// observation aliases and scalar state tokens are intentionally
    /// unconstrained beyond the surrounding formula. Consequently only a SAT
    /// model is useful; abstraction UNSAT/Unknown is ignored.
    fn abstract_nested_select_formula(
        prefix_conjuncts: &[ChcExpr],
        query_groups: &[Vec<ChcExpr>],
        depth: usize,
        reserved_names: &FxHashSet<String>,
        deadline: Option<ay_core::time::Instant>,
    ) -> Option<BmcNestedArrayCandidateFormula> {
        let mut budget = BmcNestedArrayTraversalBudget::new(MAX_PREPROCESSING_NODES, deadline);
        let mut leaves = Vec::new();
        let mut seen_leaves = FxHashSet::default();
        for expr in prefix_conjuncts.iter().chain(query_groups.iter().flatten()) {
            if let Err(abort) = Self::collect_nested_select_alias_terms(
                expr,
                &mut leaves,
                &mut seen_leaves,
                &mut budget,
            ) {
                log_nested_array_candidate(format_args!(
                    "depth={depth} skipped during observation collection: {abort:?}"
                ));
                return None;
            }
        }

        let mut used_names = reserved_names.clone();
        for var in prefix_conjuncts
            .iter()
            .chain(query_groups.iter().flatten())
            .flat_map(|expr| expr.vars())
        {
            used_names.insert(var.name);
        }
        let mut aliases = Vec::with_capacity(leaves.len());
        for (index, (original, array, indices, value_sort)) in leaves.into_iter().enumerate() {
            let mut nonce = index;
            let alias = loop {
                let name = format!("__bmc_nested_obs_{depth}_{nonce}");
                if used_names.insert(name.clone()) {
                    break ChcVar::new(name, value_sort.clone());
                }
                nonce = nonce.saturating_add(1);
            };
            aliases.push(BmcNestedSelectAlias {
                original,
                alias,
                array,
                indices,
                value_sort,
            });
        }

        let select_replacements: Vec<(ChcExpr, ChcExpr)> = aliases
            .iter()
            .map(|entry| (entry.original.clone(), ChcExpr::var(entry.alias.clone())))
            .collect();
        let select_prefix: Vec<ChcExpr> = prefix_conjuncts
            .iter()
            .map(|expr| expr.substitute_expr_pairs(&select_replacements))
            .collect();
        let select_groups: Vec<Vec<ChcExpr>> = query_groups
            .iter()
            .map(|group| {
                group
                    .iter()
                    .map(|expr| expr.substitute_expr_pairs(&select_replacements))
                    .collect()
            })
            .collect();

        for expr in select_prefix.iter().chain(select_groups.iter().flatten()) {
            if let Err(abort) = Self::validate_nested_array_token_boundaries(expr, &mut budget) {
                log_nested_array_candidate(format_args!(
                    "depth={depth} skipped during token-boundary validation: {abort:?}"
                ));
                return None;
            }
        }

        let mut state_terms = Vec::new();
        let mut seen_state_terms = FxHashSet::default();
        for expr in select_prefix.iter().chain(select_groups.iter().flatten()) {
            if let Err(abort) = Self::collect_nested_array_token_terms(
                expr,
                &mut state_terms,
                &mut seen_state_terms,
                &mut budget,
            ) {
                log_nested_array_candidate(format_args!(
                    "depth={depth} skipped during state-token collection: {abort:?}"
                ));
                return None;
            }
        }
        if aliases.is_empty() && state_terms.is_empty() {
            log_nested_array_candidate(format_args!(
                "depth={depth} skipped: no nested reads or state"
            ));
            return None;
        }

        let mut state_tokens = Vec::with_capacity(state_terms.len());
        for (index, original) in state_terms.into_iter().enumerate() {
            let mut nonce = index;
            let alias = loop {
                let name = format!("__bmc_nested_state_{depth}_{nonce}");
                if used_names.insert(name.clone()) {
                    break ChcVar::new(name, ChcSort::Int);
                }
                nonce = nonce.saturating_add(1);
            };
            state_tokens.push(BmcNestedArrayTokenAlias { original, alias });
        }

        let state_replacements: Vec<(ChcExpr, ChcExpr)> = state_tokens
            .iter()
            .map(|entry| (entry.original.clone(), ChcExpr::var(entry.alias.clone())))
            .collect();
        let rewritten_prefix: Vec<ChcExpr> = select_prefix
            .iter()
            .map(|expr| expr.substitute_expr_pairs(&state_replacements))
            .collect();
        let rewritten_groups: Vec<Vec<ChcExpr>> = select_groups
            .iter()
            .map(|group| {
                group
                    .iter()
                    .map(|expr| expr.substitute_expr_pairs(&state_replacements))
                    .collect()
            })
            .collect();

        for expr in rewritten_prefix
            .iter()
            .chain(rewritten_groups.iter().flatten())
        {
            match Self::expr_contains_nested_array_sort(expr, &mut budget) {
                Ok(false) => {}
                Ok(true) => {
                    log_nested_array_candidate(format_args!(
                        "depth={depth} skipped: nested-array root remained after {} observations and {} tokens",
                        aliases.len(),
                        state_tokens.len()
                    ));
                    tracing::debug!(
                        "BMC nested-array candidate at depth {depth} retained a nested-array root; \
                         failing closed"
                    );
                    return None;
                }
                Err(abort) => {
                    log_nested_array_candidate(format_args!(
                        "depth={depth} skipped during residual-root validation: {abort:?}"
                    ));
                    return None;
                }
            }
        }

        let equal_state = match Self::nested_array_var_equivalences(
            prefix_conjuncts.iter().chain(query_groups.iter().flatten()),
            &mut budget,
        ) {
            Ok(equal_state) => equal_state,
            Err(abort) => {
                log_nested_array_candidate(format_args!(
                    "depth={depth} skipped during equality collection: {abort:?}"
                ));
                return None;
            }
        };
        log_nested_array_candidate(format_args!(
            "depth={depth} abstracted: observations={} state_tokens={} equality_components={}",
            aliases.len(),
            state_tokens.len(),
            equal_state.len()
        ));
        Some(BmcNestedArrayCandidateFormula {
            prefix_conjuncts: rewritten_prefix,
            query_groups: rewritten_groups,
            select_aliases: aliases,
            state_tokens,
            equal_state,
        })
    }

    /// Turn abstraction-variable values into finite nested-array cells.
    ///
    /// These cells are still only a candidate model. No caller may accept it
    /// without the ordinary original-clause ground derivation replay.
    fn reconstruct_nested_select_aliases(
        model: &mut FxHashMap<String, SmtValue>,
        aliases: &[BmcNestedSelectAlias],
        state_tokens: &[BmcNestedArrayTokenAlias],
        equal_state: &[BmcNestedArrayEquivalence],
    ) -> usize {
        let observations: Vec<BmcArrayObservation> = aliases
            .iter()
            .filter_map(|entry| {
                let value = model
                    .get(&entry.alias.name)
                    .and_then(|value| Self::model_smt_value_for_sort(value, &entry.value_sort))?;
                Some(BmcArrayObservation {
                    array: entry.array.clone(),
                    indices: entry.indices.clone(),
                    value,
                })
            })
            .collect();
        let completed = observations.len();

        // Candidate tokens sever nested state from the SMT formula. Start its
        // finite reconstruction from deterministic defaults, not from any
        // arbitrary printable values the relaxed model happened to assign.
        let mut state_variables: FxHashMap<String, ChcVar> = FxHashMap::default();
        for observation in &observations {
            state_variables.insert(observation.array.name.clone(), observation.array.clone());
        }
        for token in state_tokens {
            for variable in token.original.vars() {
                if Self::is_nested_array_sort(&variable.sort) {
                    state_variables.insert(variable.name.clone(), variable);
                }
            }
        }
        for component in equal_state {
            for variable in &component.variables {
                state_variables.insert(variable.name.clone(), variable.clone());
            }
        }
        for variable in state_variables.values() {
            if let Some(default) = Self::default_smt_value_for_sort(&variable.sort) {
                model.insert(variable.name.clone(), default);
            }
        }

        let mut component_by_name = FxHashMap::default();
        for (index, component) in equal_state.iter().enumerate() {
            for variable in &component.variables {
                component_by_name.insert(variable.name.clone(), index);
            }
        }
        let mut canonical_observations = Vec::new();
        for observation in observations {
            if let Some(index) = component_by_name.get(&observation.array.name) {
                let component = &equal_state[*index];
                if let Some(canonical) = component
                    .variables
                    .iter()
                    .find(|variable| variable.sort == observation.array.sort)
                {
                    canonical_observations.push(BmcArrayObservation {
                        array: canonical.clone(),
                        indices: observation.indices,
                        value: observation.value,
                    });
                }
            } else {
                canonical_observations.push(observation);
            }
        }
        Self::reconstruct_trace_array_observations(model, &canonical_observations);

        // All observations for a component were installed on its canonical
        // member above. Copy that finite value to every member so the original
        // level-to-rule array equalities hold during exact replay.
        for component in equal_state {
            let Some(first) = component.variables.first() else {
                continue;
            };
            let canonical = model
                .get(&first.name)
                .and_then(|value| Self::model_smt_value_for_sort(value, &first.sort))
                .or_else(|| Self::default_smt_value_for_sort(&first.sort));
            let Some(canonical) = canonical else {
                continue;
            };
            for variable in &component.variables {
                model.insert(variable.name.clone(), canonical.clone());
            }
        }
        for entry in aliases {
            model.remove(&entry.alias.name);
        }
        for entry in state_tokens {
            model.remove(&entry.alias.name);
        }
        completed
    }

    /// After an exact depth query returned `unknown`, ask a relaxed copy of
    /// that complete prefix-plus-query formula for one finite candidate model.
    ///
    /// Abstraction UNSAT/Unknown has no meaning here and returns `None`.
    /// Abstraction SAT is likewise not a verdict: the caller must pass the
    /// reconstructed model through `classify_flat_sat`, whose only accepting
    /// arm is unchanged original-clause ground replay.
    fn try_nested_select_observation_candidate(
        &self,
        prefix_conjuncts: &[ChcExpr],
        query_groups: &[Vec<ChcExpr>],
        depth: usize,
        disable_lra_propagation: bool,
        deadline: Option<ay_core::time::Instant>,
    ) -> Option<FxHashMap<String, SmtValue>> {
        let Some(candidate) = Self::abstract_nested_select_formula(
            prefix_conjuncts,
            query_groups,
            depth,
            &FxHashSet::default(),
            deadline,
        ) else {
            return None;
        };
        let BmcNestedArrayCandidateFormula {
            prefix_conjuncts: abstract_prefix,
            query_groups: abstract_groups,
            select_aliases: aliases,
            state_tokens,
            equal_state,
        } = candidate;
        let abstract_conjuncts: Vec<ChcExpr> = abstract_groups.iter().flatten().cloned().collect();
        let mut smt = format!(
            "(set-logic {})\n(set-option :produce-models true)\n",
            self.detect_bmc_logic()
        );
        let mut declared_vars = FxHashSet::default();
        for conjunct in prefix_conjuncts
            .iter()
            .chain(query_groups.iter().flatten())
            .chain(abstract_prefix.iter())
            .chain(abstract_conjuncts.iter())
        {
            for var in &conjunct.vars() {
                if declared_vars.insert(var.name.clone()) {
                    smt.push_str(&format!(
                        "(declare-const {} {})\n",
                        quote_symbol(&var.name),
                        sort_to_smtlib(&var.sort),
                    ));
                }
            }
        }
        for conjunct in &abstract_prefix {
            smt.push_str(&format!(
                "(assert {})\n",
                InvariantModel::expr_to_smtlib(conjunct)
            ));
        }
        if abstract_groups.len() > 1 {
            let formula =
                InvariantModel::expr_to_smtlib(&Self::query_groups_formula(&abstract_groups));
            smt.push_str(&format!("(assert {formula})\n"));
        } else {
            for conjunct in &abstract_conjuncts {
                smt.push_str(&format!(
                    "(assert {})\n",
                    InvariantModel::expr_to_smtlib(conjunct)
                ));
            }
        }
        smt.push_str("(check-sat)\n");

        tracing::debug!(
            "BMC nested-array candidate depth={depth}: observations={}, state_tokens={}, \
             equality_components={}, prefix_conjuncts={}, query_conjuncts={}, declared={}, \
             smt_bytes={}",
            aliases.len(),
            state_tokens.len(),
            equal_state.len(),
            prefix_conjuncts.len(),
            abstract_conjuncts.len(),
            declared_vars.len(),
            smt.len()
        );
        log_nested_array_candidate(format_args!(
            "depth={depth} solving: observations={} state_tokens={} equality_components={} \
             prefix={} query={} declared={} smt_bytes={}",
            aliases.len(),
            state_tokens.len(),
            equal_state.len(),
            prefix_conjuncts.len(),
            abstract_conjuncts.len(),
            declared_vars.len(),
            smt.len()
        ));
        let Ok(commands) = ay_frontend::parse(&smt) else {
            log_nested_array_candidate(format_args!("depth={depth} candidate SMT parse failed"));
            tracing::debug!("BMC nested-array candidate at depth {depth} failed to parse");
            return None;
        };
        let mut exec = ay_dpll::Executor::new();
        if disable_lra_propagation {
            exec.set_no_lra_theory_propagation(true);
        }
        let Some(outputs) = Self::exec_commands_with_deadline(&mut exec, &commands, deadline)
        else {
            log_nested_array_candidate(format_args!(
                "depth={depth} candidate executor/deadline failed"
            ));
            tracing::debug!("BMC nested-array candidate at depth {depth} did not execute");
            return None;
        };
        let result = outputs.first().map_or("<no-output>", String::as_str);
        log_nested_array_candidate(format_args!("depth={depth} relaxed_result={result}"));
        tracing::debug!("BMC nested-array candidate at depth {depth} returned {result}");
        if result != "sat" {
            return None;
        }

        // Exact nested reads and nested state terms are deliberately absent
        // from the relaxed candidate formula. Do not ask the Executor to
        // evaluate the reads again: their alias values below are the finite
        // observations. Scalar variables and all non-abstracted flat-array
        // reads remain observed by the ordinary path.
        let mut observation_conjuncts: Vec<ChcExpr> =
            query_groups.iter().flatten().cloned().collect();
        observation_conjuncts.extend(
            aliases
                .iter()
                .map(|entry| ChcExpr::var(entry.alias.clone())),
        );
        let excluded_terms: Vec<ChcExpr> =
            aliases.iter().map(|entry| entry.original.clone()).collect();
        let Some(mut model) = self.observe_bmc_sat_model_excluding_array_terms(
            &mut exec,
            depth,
            &observation_conjuncts,
            &[&declared_vars],
            &excluded_terms,
            deadline,
        ) else {
            log_nested_array_candidate(format_args!(
                "depth={depth} candidate observation batch failed"
            ));
            tracing::debug!("BMC nested-array candidate observation failed at depth {depth}");
            return None;
        };
        let missing_scalar = aliases
            .iter()
            .filter(|entry| {
                Self::trace_assignment_sort_supported(&entry.value_sort)
                    && !model.contains_key(&entry.alias.name)
            })
            .count();
        let missing_array = aliases
            .iter()
            .filter(|entry| {
                matches!(&entry.value_sort, ChcSort::Array(_, _))
                    && !model.contains_key(&entry.alias.name)
            })
            .count();
        log_nested_array_candidate(format_args!(
            "depth={depth} observed_model_entries={} missing_scalar_aliases={} \
             missing_array_aliases={}",
            model.len(),
            missing_scalar,
            missing_array
        ));
        let observed = Self::reconstruct_nested_select_aliases(
            &mut model,
            &aliases,
            &state_tokens,
            &equal_state,
        );
        if observed != aliases.len() {
            log_nested_array_candidate(format_args!(
                "depth={depth} reconstruction incomplete: {observed}/{}",
                aliases.len()
            ));
            tracing::debug!(
                "BMC nested-array observation candidate incomplete: {observed}/{} aliases",
                aliases.len()
            );
            return None;
        }
        log_nested_array_candidate(format_args!(
            "depth={depth} reconstruction complete: {observed}; exact replay next"
        ));
        tracing::debug!(
            "BMC nested-array observation abstraction supplied {} finite values at depth {depth}; replaying original clauses",
            aliases.len()
        );
        Some(model)
    }

    fn append_trace_get_value_commands(smt: &mut String, values: &[BmcTraceValue]) {
        // Query each observation independently.  AY deliberately fails closed
        // when a term has no committed model value; one unavailable inactive
        // array/select must not erase every otherwise exact trace observation
        // by aborting a single batched `get-value` command.
        for value in values {
            smt.push_str("(get-value (");
            smt.push_str(&InvariantModel::expr_to_smtlib(&value.term()));
            smt.push_str("))\n");
        }
    }

    /// Read the model and trace observations after a flat BMC query returned
    /// SAT. Keeping this as a second executor batch is important: UNSAT and
    /// Unknown depths must not elaborate or execute thousands of model queries
    /// that cannot possibly produce values. It also delays rebuilding all
    /// flattened level expressions until a model actually needs a witness.
    fn observe_bmc_sat_model(
        &self,
        exec: &mut ay_dpll::Executor,
        max_depth: usize,
        query_conjuncts: &[ChcExpr],
        declared: &[&FxHashSet<String>],
        deadline: Option<ay_core::time::Instant>,
    ) -> Option<FxHashMap<String, SmtValue>> {
        self.observe_bmc_sat_model_excluding_array_terms(
            exec,
            max_depth,
            query_conjuncts,
            declared,
            &[],
            deadline,
        )
    }

    /// Candidate-only observation variant. Each excluded exact array term has
    /// a scalar alias whose value is reconstructed before original-clause
    /// replay, so querying the unsupported exact term again would only repeat
    /// the `unknown` that triggered this fallback.
    fn observe_bmc_sat_model_excluding_array_terms(
        &self,
        exec: &mut ay_dpll::Executor,
        max_depth: usize,
        query_conjuncts: &[ChcExpr],
        declared: &[&FxHashSet<String>],
        excluded_array_terms: &[ChcExpr],
        deadline: Option<ay_core::time::Instant>,
    ) -> Option<FxHashMap<String, SmtValue>> {
        if deadline.is_some_and(|limit| ay_core::time::Instant::now() >= limit) {
            return None;
        }

        let mut trace_values = self.bmc_trace_values(max_depth, query_conjuncts);
        trace_values.retain(|value| {
            !matches!(
                value,
                BmcTraceValue::ArraySelectPath { .. }
                    if excluded_array_terms.contains(&value.term())
            )
        });
        Self::retain_declared_trace_values(&mut trace_values, declared);

        let mut smt = String::from("(get-model)\n");
        Self::append_trace_get_value_commands(&mut smt, &trace_values);
        #[cfg(test)]
        record_trace_observation_commands_for_tests(1usize.saturating_add(trace_values.len()));

        let commands = ay_frontend::parse(&smt).ok()?;
        let outputs = Self::exec_commands_with_deadline(exec, &commands, deadline)?;
        let mut model = FxHashMap::default();
        let dt_ctor_names = FxHashSet::default();
        parse_model_into(&mut model, Self::model_output(&outputs), &dt_ctor_names);
        Self::parse_trace_get_value_outputs_into_model(&mut model, &trace_values, &outputs);
        Some(model)
    }

    fn model_output(outputs: &[String]) -> &str {
        outputs
            .iter()
            .rev()
            .find(|output| output.trim_start().starts_with("(model"))
            .map(String::as_str)
            .unwrap_or("")
    }

    /// Parse the value half of one singleton `(get-value (term))` response.
    ///
    /// AY's output renderer currently prints generated CHC names such as
    /// `Init#0` without SMT-LIB quoting.  The ordinary S-expression lexer
    /// therefore cannot parse the whole pair (`#` starts a literal token), but
    /// trace reconstruction does not need to parse the echoed term: the query
    /// and response are already associated positionally.  Skip that term with
    /// a balanced scanner and parse only the scalar value, whose syntax is
    /// canonical SMT-LIB.
    fn singleton_get_value_rhs(output: &str) -> Option<SExpr> {
        fn skip_ws(bytes: &[u8], pos: &mut usize) {
            while bytes.get(*pos).is_some_and(u8::is_ascii_whitespace) {
                *pos += 1;
            }
        }

        fn skip_sexpr(bytes: &[u8], pos: &mut usize) -> Option<()> {
            skip_ws(bytes, pos);
            match *bytes.get(*pos)? {
                b'(' => {
                    let mut depth = 0usize;
                    let mut quoted_symbol = false;
                    let mut string = false;
                    while let Some(&byte) = bytes.get(*pos) {
                        *pos += 1;
                        if quoted_symbol {
                            if byte == b'|' {
                                quoted_symbol = false;
                            }
                            continue;
                        }
                        if string {
                            if byte == b'"' {
                                if bytes.get(*pos) == Some(&b'"') {
                                    *pos += 1;
                                } else {
                                    string = false;
                                }
                            }
                            continue;
                        }
                        match byte {
                            b'|' => quoted_symbol = true,
                            b'"' => string = true,
                            b'(' => depth = depth.checked_add(1)?,
                            b')' => {
                                depth = depth.checked_sub(1)?;
                                if depth == 0 {
                                    return Some(());
                                }
                            }
                            _ => {}
                        }
                    }
                    None
                }
                b'|' => {
                    *pos += 1;
                    while let Some(&byte) = bytes.get(*pos) {
                        *pos += 1;
                        if byte == b'|' {
                            return Some(());
                        }
                    }
                    None
                }
                b'"' => {
                    *pos += 1;
                    while let Some(&byte) = bytes.get(*pos) {
                        *pos += 1;
                        if byte == b'"' {
                            if bytes.get(*pos) == Some(&b'"') {
                                *pos += 1;
                            } else {
                                return Some(());
                            }
                        }
                    }
                    None
                }
                b')' => None,
                _ => {
                    let start = *pos;
                    while bytes.get(*pos).is_some_and(|byte| {
                        !byte.is_ascii_whitespace() && *byte != b'(' && *byte != b')'
                    }) {
                        *pos += 1;
                    }
                    (*pos > start).then_some(())
                }
            }
        }

        let bytes = output.as_bytes();
        let mut pos = 0usize;
        skip_ws(bytes, &mut pos);
        if bytes.get(pos) != Some(&b'(') {
            return None;
        }
        pos += 1;
        skip_ws(bytes, &mut pos);
        if bytes.get(pos) != Some(&b'(') {
            return None;
        }
        pos += 1;
        skip_sexpr(bytes, &mut pos)?;
        skip_ws(bytes, &mut pos);
        let value_start = pos;
        skip_sexpr(bytes, &mut pos)?;
        let value_end = pos;
        skip_ws(bytes, &mut pos);
        if bytes.get(pos) != Some(&b')') {
            return None;
        }
        pos += 1;
        skip_ws(bytes, &mut pos);
        if bytes.get(pos) != Some(&b')') {
            return None;
        }
        pos += 1;
        skip_ws(bytes, &mut pos);
        if pos != bytes.len() {
            return None;
        }
        parse_sexp(output.get(value_start..value_end)?).ok()
    }

    fn parse_trace_get_value_outputs_into_model(
        model: &mut FxHashMap<String, SmtValue>,
        values: &[BmcTraceValue],
        outputs: &[String],
    ) {
        if values.is_empty() || outputs.len() < values.len() {
            return;
        }

        // The trace commands are emitted last and each produces exactly one
        // output (either a singleton value-pair or an error).  Preserve the
        // positional association so an error is skipped locally instead of
        // shifting later values onto the wrong trace term.
        let trace_outputs = &outputs[outputs.len() - values.len()..];
        let parsed: Vec<Option<SmtValue>> = trace_outputs
            .iter()
            .zip(values)
            .map(|(output, trace_value)| {
                let value_expr = Self::singleton_get_value_rhs(output)?;
                Self::trace_get_value_smt_value(&value_expr, trace_value.sort())
            })
            .collect();

        // Variables first, regardless of command order: array path indices can
        // mention a scalar whose observation happened to be emitted later.
        for (trace_value, value) in values.iter().zip(&parsed) {
            if let (BmcTraceValue::Var(var), Some(value)) = (trace_value, value) {
                model.insert(var.name.clone(), value.clone());
            }
        }

        let observations: Vec<BmcArrayObservation> = values
            .iter()
            .zip(parsed)
            .filter_map(|(trace_value, value)| match (trace_value, value) {
                (BmcTraceValue::ArraySelectPath { array, indices, .. }, Some(value)) => {
                    Some(BmcArrayObservation {
                        array: array.clone(),
                        indices: indices.clone(),
                        value,
                    })
                }
                _ => None,
            })
            .collect();
        Self::reconstruct_trace_array_observations(model, &observations);
    }

    /// Materialize the finite nested-array cells returned by trace
    /// `(get-value ...)` commands.
    ///
    /// The scalar leaf values are exact observations from the SAT model. Array
    /// values printed by the executor are less expressive: two distinct
    /// array-valued indices can both render as the same default-only constant
    /// array, even when differing leaf reads prove they cannot be equal. Before
    /// installing cells, separate ONLY those collided array keys that are
    /// forced apart by incompatible observed leaves. The completed model still
    /// decides nothing by itself; `validate_ground_derivation` re-evaluates
    /// every clause and premise link before Unsafe can be returned.
    fn reconstruct_trace_array_observations(
        model: &mut FxHashMap<String, SmtValue>,
        observations: &[BmcArrayObservation],
    ) {
        // A path may use another reconstructed array as its index:
        // `F[E][0]`, with a separate observation that later refines `E[5]`.
        // One source-order pass would install the outer `F` cell under E's OLD
        // concrete value and then change the lookup key. Iterate to a semantic
        // fixpoint so dependencies settle regardless of observation order.
        //
        // The cap is a completeness bound only. A non-convergent or longer
        // dependency chain leaves an incomplete model which the unchanged
        // ground validator rejects; it can never manufacture Unsafe.
        const MAX_RECONSTRUCTION_ROUNDS: usize = 32;
        let rounds = observations
            .len()
            .saturating_add(1)
            .min(MAX_RECONSTRUCTION_ROUNDS);
        for _ in 0..rounds {
            let mut changed = Self::separate_colliding_trace_array_keys(model, observations);
            for observation in observations {
                changed |= Self::insert_trace_array_observation(model, observation);
            }
            if !changed {
                break;
            }
        }
    }

    /// Repair the executor renderer's one lossy case needed by nested reads:
    /// syntactically different ARRAY-SORTED index variables rendered to one
    /// concrete value while exact scalar observations at the resulting full
    /// path disagree.
    ///
    /// A conflicting pair is a proof that the two keys cannot denote the same
    /// array in the SAT model (array congruence would make the leaves equal).
    /// Give one key expression a fresh finite concrete array and rebuild all
    /// observations against it. A direct variable is replaced in the model;
    /// a composite select such as `(select^4 C h)` is completed by installing
    /// the fresh value at that finite path in `C`. Equal-valued observations
    /// and scalar key collisions are left untouched and fail closed later if
    /// the printable model remains insufficient.
    fn separate_colliding_trace_array_keys(
        model: &mut FxHashMap<String, SmtValue>,
        observations: &[BmcArrayObservation],
    ) -> bool {
        let mut nonce = 0usize;
        let mut changed = false;
        for _ in 0..observations.len().saturating_mul(2).max(1) {
            let mut repair: Option<(ChcVar, Vec<(ChcExpr, ChcSort)>, ChcSort)> = None;
            let mut paths: FxHashMap<String, (usize, Vec<SmtValue>)> = FxHashMap::default();
            for (right_index, right) in observations.iter().enumerate() {
                let Some(right_values) = Self::trace_observation_indices(right, model) else {
                    continue;
                };
                let Some(path_key) = Self::trace_values_semantic_key(&right_values) else {
                    continue;
                };
                let key = format!("{:?}::{path_key:?}", right.array.name);
                let Some((left_index, left_values)) = paths.get(&key) else {
                    paths.insert(key, (right_index, right_values));
                    continue;
                };
                let left = &observations[*left_index];
                if left.array.name != right.array.name
                    || Self::trace_values_semantically_equal(
                        std::slice::from_ref(&left.value),
                        std::slice::from_ref(&right.value),
                    ) == Some(true)
                    || Self::trace_values_semantically_equal(left_values, &right_values)
                        != Some(true)
                {
                    continue;
                }

                for (((left_expr, left_sort), (right_expr, right_sort)), (lv, rv)) in left
                    .indices
                    .iter()
                    .zip(&right.indices)
                    .zip(left_values.iter().zip(&right_values))
                {
                    if left_expr == right_expr
                        || left_sort != right_sort
                        || Self::trace_values_semantically_equal(
                            std::slice::from_ref(lv),
                            std::slice::from_ref(rv),
                        ) != Some(true)
                        || !matches!(right_sort, ChcSort::Array(_, _))
                    {
                        continue;
                    }
                    let target = match right_expr {
                        ChcExpr::Var(var) => Some((var.clone(), Vec::new(), right_sort.clone())),
                        _ => Self::trace_array_select_path(right_expr),
                    };
                    let Some((array, indices, value_sort)) = target else {
                        continue;
                    };
                    if &value_sort != right_sort {
                        continue;
                    }
                    repair = Some((array, indices, value_sort));
                    break;
                }
                if repair.is_some() {
                    break;
                }
            }

            let Some((array, indices, value_sort)) = repair else {
                break;
            };
            let path_values: Vec<SmtValue> = observations
                .iter()
                .filter_map(|observation| Self::trace_observation_indices(observation, model))
                .flatten()
                .collect();
            let mut replacement = None;
            for _ in 0..128 {
                nonce = nonce.saturating_add(1);
                let Some(candidate) = Self::fresh_trace_array_key(&value_sort, nonce) else {
                    break;
                };
                let Some(candidate_key) = Self::trace_value_semantic_key(&candidate) else {
                    break;
                };
                let used_by_model = model.values().any(|value| {
                    Self::trace_value_semantic_key(value)
                        .is_some_and(|value_key| value_key == candidate_key)
                });
                let used_by_path = path_values.iter().any(|value| {
                    Self::trace_value_semantic_key(value)
                        .is_some_and(|value_key| value_key == candidate_key)
                });
                if !used_by_model && !used_by_path {
                    replacement = Some(candidate);
                    break;
                }
            }
            let Some(replacement) = replacement else {
                break;
            };
            let repaired = if indices.is_empty() {
                model.insert(array.name, replacement);
                true
            } else {
                Self::insert_trace_array_observation(
                    model,
                    &BmcArrayObservation {
                        array,
                        indices,
                        value: replacement,
                    },
                )
            };
            if !repaired {
                break;
            }
            changed = true;
        }
        changed
    }

    fn trace_observation_indices(
        observation: &BmcArrayObservation,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<Vec<SmtValue>> {
        let env = Self::model_i128_env(model);
        observation
            .indices
            .iter()
            .map(|(index, sort)| Self::model_expr_smt_value_for_sort(index, sort, model, &env))
            .collect()
    }

    /// Canonical finite value key using the same extensional interpretation as
    /// ground array evaluation.
    ///
    /// `ArrayMap(default=0, [5 -> 0])` and `ConstArray(0)` intentionally share
    /// a key; store order and shadowed writes are normalized away. An Opaque
    /// component has no concrete extensional meaning and returns `None`, so it
    /// can never justify separating two rendered keys.
    fn trace_value_semantic_key(value: &SmtValue) -> Option<String> {
        match value {
            SmtValue::Bool(value) => Some(format!("bool:{value}")),
            SmtValue::Int(value) => Some(format!("int:{value}")),
            SmtValue::BigInt(value) => Some(format!("bigint:{value}")),
            SmtValue::Real(value) => Some(format!("real:{value}")),
            SmtValue::BitVec(value, width) => Some(format!("bv:{width}:{value}")),
            SmtValue::Opaque(_) => None,
            SmtValue::ConstArray(default) => {
                let default = Self::trace_value_semantic_key(default)?;
                Some(format!("array:{default:?}:[]"))
            }
            SmtValue::ArrayMap { default, entries } => {
                let default = Self::trace_value_semantic_key(default)?;
                let mut normalized: Vec<(String, String)> = Vec::new();
                for (index, value) in entries {
                    let index = Self::trace_value_semantic_key(index)?;
                    let value = Self::trace_value_semantic_key(value)?;
                    normalized.retain(|(stored_index, _)| stored_index != &index);
                    if value != default {
                        normalized.push((index, value));
                    }
                }
                normalized.sort();
                Some(format!("array:{default:?}:{normalized:?}"))
            }
            SmtValue::Datatype(constructor, fields) => {
                let fields: Option<Vec<String>> =
                    fields.iter().map(Self::trace_value_semantic_key).collect();
                Some(format!("datatype:{constructor:?}:{:?}", fields?))
            }
        }
    }

    fn trace_values_semantic_key(values: &[SmtValue]) -> Option<Vec<String>> {
        values.iter().map(Self::trace_value_semantic_key).collect()
    }

    fn trace_values_semantically_equal(left: &[SmtValue], right: &[SmtValue]) -> Option<bool> {
        if left.len() != right.len() {
            return Some(false);
        }
        for (left, right) in left.iter().zip(right) {
            match (left, right) {
                (SmtValue::Opaque(left), SmtValue::Opaque(right)) if left == right => continue,
                (SmtValue::Opaque(_), _) | (_, SmtValue::Opaque(_)) => return None,
                _ => {}
            }
            let (Some(left), Some(right)) = (
                Self::trace_value_semantic_key(left),
                Self::trace_value_semantic_key(right),
            ) else {
                return None;
            };
            if left != right {
                return Some(false);
            }
        }
        Some(true)
    }

    /// A finite array value distinct from the default-only renderer output.
    ///
    /// The point index varies with `nonce`, so integer/bitvector-indexed arrays
    /// admit many deterministic fingerprints. Unsupported or finite-exhausted
    /// sorts simply return `None`; witness reconstruction then remains
    /// incomplete and validation rejects it.
    fn fresh_trace_array_key(sort: &ChcSort, nonce: usize) -> Option<SmtValue> {
        let ChcSort::Array(index_sort, value_sort) = sort else {
            return None;
        };
        let default = Self::default_smt_value_for_sort(value_sort)?;
        let index = Self::trace_fingerprint_value(index_sort, nonce)?;
        let value = Self::trace_nondefault_value(value_sort, nonce)?;
        if value == default {
            return None;
        }
        Some(SmtValue::ArrayMap {
            default: Box::new(default),
            entries: vec![(index, value)],
        })
    }

    fn trace_fingerprint_value(sort: &ChcSort, nonce: usize) -> Option<SmtValue> {
        let n = i128::try_from(nonce).ok()?;
        match sort {
            ChcSort::Bool => Some(SmtValue::Bool(nonce % 2 != 0)),
            ChcSort::Int => Some(SmtValue::Int(n.checked_neg()?.checked_sub(1)?)),
            ChcSort::BitVec(width) if *width != 0 => {
                Some(SmtValue::BitVec((nonce as u128) & bv_mask(*width), *width))
            }
            ChcSort::Array(_, _) => Self::fresh_trace_array_key(sort, nonce),
            ChcSort::BitVec(_)
            | ChcSort::Real
            | ChcSort::Uninterpreted(_)
            | ChcSort::Datatype { .. } => None,
        }
    }

    fn trace_nondefault_value(sort: &ChcSort, nonce: usize) -> Option<SmtValue> {
        let n = i128::try_from(nonce).ok()?;
        match sort {
            ChcSort::Bool => Some(SmtValue::Bool(true)),
            ChcSort::Int => Some(SmtValue::Int(n.checked_add(1)?)),
            ChcSort::BitVec(width) if *width != 0 => {
                let value = ((nonce as u128) & bv_mask(*width)).max(1);
                Some(SmtValue::BitVec(value, *width))
            }
            ChcSort::Array(_, _) => Self::fresh_trace_array_key(sort, nonce),
            ChcSort::BitVec(_)
            | ChcSort::Real
            | ChcSort::Uninterpreted(_)
            | ChcSort::Datatype { .. } => None,
        }
    }

    fn insert_trace_array_observation(
        model: &mut FxHashMap<String, SmtValue>,
        observation: &BmcArrayObservation,
    ) -> bool {
        let Some(indices) = Self::trace_observation_indices(observation, model) else {
            return false;
        };
        let existing = model
            .get(&observation.array.name)
            .and_then(|value| Self::model_smt_value_for_sort(value, &observation.array.sort))
            .or_else(|| Self::default_smt_value_for_sort(&observation.array.sort));
        let Some(existing) = existing else {
            return false;
        };
        let old_key = Self::trace_value_semantic_key(&existing);
        let Some(updated) = Self::trace_array_value_with_observation(
            existing,
            &observation.array.sort,
            &indices,
            observation.value.clone(),
        ) else {
            return false;
        };
        let new_key = Self::trace_value_semantic_key(&updated);
        model.insert(observation.array.name.clone(), updated);
        old_key != new_key
    }

    fn trace_array_value_with_observation(
        array: SmtValue,
        sort: &ChcSort,
        indices: &[SmtValue],
        value: SmtValue,
    ) -> Option<SmtValue> {
        let (index, remaining) = indices.split_first()?;
        let ChcSort::Array(_, element_sort) = sort else {
            return None;
        };
        let array = match array {
            value @ (SmtValue::ConstArray(_) | SmtValue::ArrayMap { .. }) => value,
            _ => Self::default_smt_value_for_sort(sort)?,
        };
        let child = crate::expr::eval_array_select(&array, index)
            .and_then(|value| Self::model_smt_value_for_sort(&value, element_sort))
            .or_else(|| Self::default_smt_value_for_sort(element_sort))?;
        let child = if remaining.is_empty() {
            Self::model_smt_value_for_sort(&value, element_sort)?
        } else {
            Self::trace_array_value_with_observation(child, element_sort, remaining, value)?
        };
        Some(Self::trace_array_point_override(
            array,
            index.clone(),
            child,
        ))
    }

    fn trace_array_point_override(array: SmtValue, index: SmtValue, value: SmtValue) -> SmtValue {
        match array {
            SmtValue::ConstArray(default) => SmtValue::ArrayMap {
                default,
                entries: vec![(index, value)],
            },
            SmtValue::ArrayMap {
                default,
                mut entries,
            } => {
                entries.retain(|(stored_index, _)| {
                    Self::trace_values_semantically_equal(
                        std::slice::from_ref(stored_index),
                        std::slice::from_ref(&index),
                    ) != Some(true)
                });
                entries.push((index, value));
                SmtValue::ArrayMap { default, entries }
            }
            other => other,
        }
    }

    fn default_smt_value_for_sort(sort: &ChcSort) -> Option<SmtValue> {
        match sort {
            ChcSort::Bool => Some(SmtValue::Bool(false)),
            ChcSort::Int => Some(SmtValue::Int(0)),
            ChcSort::BitVec(width) => Some(SmtValue::BitVec(0, *width)),
            ChcSort::Array(_, value_sort) => Some(SmtValue::ConstArray(Box::new(
                Self::default_smt_value_for_sort(value_sort)?,
            ))),
            ChcSort::Real | ChcSort::Uninterpreted(_) | ChcSort::Datatype { .. } => None,
        }
    }

    fn trace_get_value_smt_value(value: &SExpr, sort: &ChcSort) -> Option<SmtValue> {
        match sort {
            ChcSort::Bool => match value {
                SExpr::True => Some(SmtValue::Bool(true)),
                SExpr::False => Some(SmtValue::Bool(false)),
                _ => None,
            },
            ChcSort::Int => Self::trace_get_value_i128(value).map(SmtValue::Int),
            ChcSort::BitVec(width) => {
                let value = match value {
                    SExpr::Hexadecimal(literal) => {
                        u128::from_str_radix(literal.strip_prefix("#x")?, 16).ok()?
                    }
                    SExpr::Binary(literal) => {
                        u128::from_str_radix(literal.strip_prefix("#b")?, 2).ok()?
                    }
                    SExpr::Numeral(literal) => literal.parse::<u128>().ok()?,
                    SExpr::List(items) => Self::trace_get_value_indexed_bitvec(items, *width)?,
                    _ => return None,
                };
                if *width < 128 && value > bv_mask(*width) {
                    return None;
                }
                Some(SmtValue::BitVec(value & bv_mask(*width), *width))
            }
            _ => None,
        }
    }

    fn trace_get_value_i128(value: &SExpr) -> Option<i128> {
        match value {
            SExpr::Numeral(literal) => literal.parse().ok(),
            SExpr::List(items) => {
                let [SExpr::Symbol(op), SExpr::Numeral(literal)] = items.as_slice() else {
                    return None;
                };
                if op != "-" {
                    return None;
                }
                literal.parse::<i128>().ok()?.checked_neg()
            }
            _ => None,
        }
    }

    fn trace_get_value_indexed_bitvec(items: &[SExpr], width: u32) -> Option<u128> {
        let [SExpr::Symbol(underscore), SExpr::Symbol(value), SExpr::Numeral(value_width)] = items
        else {
            return None;
        };
        if underscore != "_" || value_width.parse::<u32>().ok()? != width {
            return None;
        }
        let digits = value.strip_prefix("bv")?;
        digits.parse().ok()
    }

    fn bmc_sat_result(
        &self,
        model: &FxHashMap<String, SmtValue>,
        k: usize,
        queries: &[&HornClause],
    ) -> ChcEngineResult {
        if self.config.proof_cross_check && self.problem_uses_array_features() {
            tracing::debug!(
                "BMC: array-bearing proof cross-check SAT at depth {k} is not a trusted proof contradiction; returning Unknown"
            );
            return ChcEngineResult::Unknown;
        }

        let mut candidates = self.model_derivation_witnesses(model, k, queries);
        if candidates.is_empty() {
            crate::ground_derivation::log_ground_translation_detail(format_args!(
                "level-model BMC at depth {k}: derivation witness extraction returned nothing"
            ));
            tracing::debug!(
                "BMC: SAT at depth {k} but derivation witness extraction was incomplete; \
                 returning Unknown"
            );
            return ChcEngineResult::Unknown;
        }

        // Ground-witness path: reshape a witness into a fully-ground derivation
        // over THIS problem's clauses. When it validates by pure evaluation the
        // Unsafe verdict is decided outright, which matters beyond speed — the
        // SMT witness validator below returns Unknown on exactly the
        // DT+array+BV shapes preprocessing was introduced to avoid, discarding
        // a counterexample it cannot refute. The derivation also rides along on
        // the counterexample so an enclosing transform lane can back-translate
        // it to ORIGINAL clauses.
        //
        // EVERY extracted lane gets a turn: a lane whose derivation does not
        // validate must not mask a later lane whose derivation does.
        if crate::ground_derivation::ground_backtranslation_enabled() {
            // Give this back-translation its own witness-solve chain budget.
            let _witness_budget =
                crate::ground_derivation::witness::ScopedWitnessChainBudget::new();
            for index in 0..candidates.len() {
                // Reshaping + validating a lane is pure evaluation, but it runs
                // once per lane; keep the whole walk inside the solve budget.
                if self.model_extraction_should_stop() {
                    tracing::debug!(
                        "BMC: stopping level-model ground validation after {index} lane(s) \
                         (deadline/cancellation)"
                    );
                    break;
                }
                let ground = self
                    .ground_derivation_from_witness(&candidates[index], model, k)
                    .or_else(|| {
                        crate::ground_derivation::log_ground_translation_detail(format_args!(
                            "level-model BMC witness ({} entries, query_clause={:?}) could not be \
                             reshaped into a ground derivation",
                            candidates[index].witness.entries.len(),
                            candidates[index].witness.query_clause
                        ));
                        None
                    })
                    .filter(|derivation| {
                        crate::ground_derivation::validate_ground_derivation(
                            &self.problem,
                            derivation,
                        )
                        .inspect_err(|err| {
                            crate::ground_derivation::log_ground_translation_detail(format_args!(
                                "level-model BMC derivation rejected on its own problem: {err}"
                            ));
                        })
                        .is_ok()
                    });
                if let Some(derivation) = ground {
                    let witness = candidates.swap_remove(index).witness;
                    let steps = self.steps_from_derivation_witness(&witness);
                    let cex = Counterexample::with_witness(steps, witness)
                        .with_ground_derivation(derivation);
                    if self.config.base.verbose {
                        safe_eprintln!(
                            "BMC: level-model derivation ground-validated on its own clauses \
                             ({} steps); Unsafe decided without SMT replay",
                            cex.ground_derivation
                                .as_ref()
                                .map_or(0, crate::ground_derivation::GroundDerivation::len)
                        );
                    }
                    return ChcEngineResult::Unsafe(cex);
                }
            }
        }

        // SMT-replay fallback. It is built around the witness's SINGLE linear
        // premise chain (`steps_from_derivation_witness` follows one premise per
        // entry), so it would be handed an incomplete picture of a query that
        // joins several predicates. Such queries are therefore promoted ONLY by
        // `validate_ground_derivation` above; here we fall through to the first
        // single-rooted lane, which is exactly the pre-existing behaviour.
        let Some(single_rooted) = candidates
            .into_iter()
            .find(|candidate| candidate.query_roots.len() == 1)
        else {
            tracing::debug!(
                "BMC: only multi-body-predicate query witnesses at depth {k} and none \
                 ground-validated; returning Unknown rather than replaying a partial chain"
            );
            return ChcEngineResult::Unknown;
        };
        self.verified_unsafe_from_witness(single_rooted.witness, "level-model BMC")
    }

    fn verified_unsafe_from_witness(
        &self,
        witness: DerivationWitness,
        source: &str,
    ) -> ChcEngineResult {
        let steps = self.steps_from_derivation_witness(&witness);
        let cex = Counterexample::with_witness(steps, witness);
        let mut validation_config = PdrConfig::default()
            .with_verbose(self.config.base.verbose)
            .with_cancellation_token(self.config.base.cancellation_token.clone());
        validation_config.disable_array_scalarization = true;
        validation_config.preserve_original_clauses = true;
        validation_config.strict_proofs = true;
        // Validation context: never recurse into the bounded-BMC cex replay
        // (inc-9) — this verification IS the replay's trust anchor.
        validation_config.disable_cex_replay = true;
        let mut verifier = PdrSolver::new(self.problem.clone(), validation_config);
        match verifier.try_verify_counterexample(&cex) {
            Ok(CexVerificationResult::Valid) => ChcEngineResult::Unsafe(cex),
            Ok(CexVerificationResult::Spurious) => {
                tracing::warn!(
                    "BMC: {source} witness failed original CHC replay as spurious; returning Unknown"
                );
                ChcEngineResult::Unknown
            }
            Ok(CexVerificationResult::Unknown) => {
                tracing::debug!(
                    "BMC: {source} witness replay on original CHC was inconclusive; returning Unknown"
                );
                ChcEngineResult::Unknown
            }
            Err(err) => {
                tracing::warn!(
                    "BMC: {source} witness replay on original CHC failed ({err}); returning Unknown"
                );
                ChcEngineResult::Unknown
            }
        }
    }

    /// Extends a branch SAT model with values for variables the pre-solve
    /// simplification substituted away, by forward-propagating equality
    /// conjuncts of the UNSIMPLIFIED branch to a fixpoint, then grounding any
    /// remaining unconstrained variables to sort defaults one at a time
    /// (re-propagating after each) so mutually-referential don't-care
    /// clusters (`x == y` with neither in the model) stay internally
    /// consistent. A wrong or missing value can only lead to a witness the
    /// replay gate rejects.
    ///
    /// `witness_vars` widens the grounding scan beyond `raw_conjuncts`: bare
    /// variables that appear ONLY in the witness path (predicate-instance arg
    /// expressions or `clause_var_renaming` values, e.g. `__bmc_dag_e*_v*`
    /// don't-cares the simplifier eliminated) previously stayed unbound, so
    /// `acyclic_branch_witness` failed closed with "arg N ... not evaluable"
    /// and the SAT branch degraded to Unknown. They are sort-zero-defaulted
    /// into the SAME grounded model through the identical
    /// one-var-then-re-propagate loop.
    fn extend_model_via_branch_equalities(
        raw_conjuncts: &[ChcExpr],
        witness_vars: &[ChcVar],
        model: &FxHashMap<String, SmtValue>,
    ) -> FxHashMap<String, SmtValue> {
        // Flatten nested conjunctions first: each expanded clause pushes its
        // WHOLE constraint as a single (possibly deeply nested) `and`
        // conjunct, so its equalities were invisible to the top-level `Eq`
        // match below. Missing them let sort-zero defaulting contradict a
        // constraint equality (e.g. an out-var pinned by the clause while its
        // partner free var got defaulted to 0), producing a witness the
        // replay gate rejects as spurious.
        let raw_conjuncts: Vec<ChcExpr> = raw_conjuncts
            .iter()
            .flat_map(ChcExpr::collect_conjuncts_nontrivial)
            .collect();
        let raw_conjuncts = raw_conjuncts.as_slice();
        let mut extended = model.clone();
        let mut undefaultable: FxHashSet<String> = FxHashSet::default();
        loop {
            for _round in 0..=raw_conjuncts.len() {
                let mut changed = false;
                let env = Self::model_i128_env(&extended);
                for conjunct in raw_conjuncts {
                    let ChcExpr::Op(ChcOp::Eq, args) = conjunct else {
                        continue;
                    };
                    let [lhs, rhs] = args.as_slice() else {
                        continue;
                    };
                    for (var_side, expr_side) in [(lhs, rhs), (rhs, lhs)] {
                        let ChcExpr::Var(var) = var_side.as_ref() else {
                            continue;
                        };
                        if extended.contains_key(&var.name) {
                            continue;
                        }
                        if let Some(value) = Self::model_expr_smt_value_for_sort(
                            expr_side.as_ref(),
                            &var.sort,
                            &extended,
                            &env,
                        ) {
                            extended.insert(var.name.clone(), value);
                            changed = true;
                        }
                    }
                }
                if !changed {
                    break;
                }
            }
            // Ground ONE still-unbound variable, then re-propagate: the
            // pre-solve simplification dropped it as unconstrained, so any
            // value satisfies the branch, but variables tied to it by
            // equalities must receive the SAME value. Witness-referenced
            // variables (path args / clause_var_renaming values) join the
            // scan after the conjunct variables so equality-connected
            // clusters are preferred as propagation seeds.
            let next_unbound = raw_conjuncts
                .iter()
                .flat_map(|conjunct| conjunct.vars())
                .chain(witness_vars.iter().cloned())
                .find(|var| {
                    !extended.contains_key(&var.name) && !undefaultable.contains(&var.name)
                });
            let Some(var) = next_unbound else {
                break;
            };
            match Self::concrete_value_smt(&var.sort, 0) {
                Some(value) => {
                    tracing::debug!(
                        "BMC: branch var {} unconstrained after equality propagation; defaulting to sort zero",
                        var.name
                    );
                    extended.insert(var.name.clone(), value);
                }
                None => {
                    undefaultable.insert(var.name.clone());
                }
            }
        }
        extended
    }

    /// Builds a derivation witness from a SAT model of an exact acyclic
    /// branch, using the recorded expansion path instead of level-based
    /// variable naming (the branch formula renames clause variables per
    /// expansion, so `model_level_smt_values` cannot see them).
    ///
    /// `path[0]` is the query's body predicate instance; the last node is
    /// the fact-clause expansion. Each node's argument expressions are
    /// evaluated under the branch model to concrete values; failure at any
    /// node returns None (the caller keeps its fail-closed Unknown).
    fn acyclic_branch_witness(
        &self,
        model: &FxHashMap<String, SmtValue>,
        path: &[AcyclicPathNode],
        query_clause: Option<usize>,
    ) -> Option<DerivationWitness> {
        if path.is_empty() {
            return None;
        }
        let env = Self::model_i128_env(model);
        let mut entries: Vec<DerivationWitnessEntry> = Vec::with_capacity(path.len());
        let mut prev_idx: Option<usize> = None;
        // Deepest node (fact clause) first: level 0, no premises.
        for (depth_from_root, node) in path.iter().enumerate().rev() {
            let pred = node.predicate;
            let pred_info = self.problem.get_predicate(pred)?;
            if pred_info.arg_sorts.len() != node.args.len() {
                tracing::debug!(
                    "BMC: acyclic branch witness: arity mismatch for {pred:?} at depth {depth_from_root}"
                );
                return None;
            }
            let values: Vec<SmtValue> = match node
                .args
                .iter()
                .zip(pred_info.arg_sorts.iter())
                .enumerate()
                .map(|(arg_idx, (expr, sort))| {
                    let value = Self::model_expr_smt_value_for_sort(expr, sort, model, &env);
                    if value.is_none() {
                        tracing::debug!(
                            "BMC: acyclic branch witness: arg {arg_idx} of {pred:?} at depth {depth_from_root} not evaluable under the branch model ({expr:?})"
                        );
                    }
                    value
                })
                .collect::<Option<Vec<_>>>()
            {
                Some(values) => values,
                None => return None,
            };
            let Some((mut instances, state)) = self.concrete_state_witness_smt(pred, &values)
            else {
                tracing::debug!(
                    "BMC: acyclic branch witness: concrete state build failed for {pred:?} at depth {depth_from_root}"
                );
                return None;
            };
            // Clause-local instances: the replay's premise/head alignment
            // evaluates the deriving clause's HEAD argument expressions from
            // this entry's instances, so the clause's own variable names must
            // be pinned to their branch-model values (mirrors
            // `model_clause_instances` in the level-based producer). Canonical
            // argument names take precedence on collision.
            let clause = self.problem.clauses().get(node.clause_idx)?;
            for var in clause.vars() {
                let Some(renamed) = node.clause_var_renaming.get(&var.name) else {
                    continue;
                };
                let Some(value) =
                    Self::model_expr_smt_value_for_sort(renamed, &var.sort, model, &env)
                else {
                    tracing::debug!(
                        "BMC: acyclic branch witness: clause-local var {} of clause {} not evaluable under the branch model",
                        var.name,
                        node.clause_idx
                    );
                    continue;
                };
                instances.entry(var.name).or_insert(value);
            }
            let level = path.len() - 1 - depth_from_root;
            let entry_idx = entries.len();
            entries.push(DerivationWitnessEntry {
                predicate: pred,
                level,
                state,
                incoming_clause: Some(node.clause_idx),
                premises: prev_idx.into_iter().collect(),
                instances,
            });
            prev_idx = Some(entry_idx);
        }
        Some(DerivationWitness {
            query_clause,
            root: prev_idx?,
            entries,
        })
    }

    /// A level-BMC derivation witness together with the entry index of EVERY
    /// body predicate of the violated query, in body order.
    ///
    /// `DerivationWitness` carries a single `root`, which is all a
    /// single-body-predicate query needs. A query joining several predicates
    /// has one derived fact per body predicate, and the ground reshaping needs
    /// all of them to give the query step its premises.
    fn model_derivation_witnesses(
        &self,
        model: &FxHashMap<String, SmtValue>,
        k: usize,
        queries: &[&HornClause],
    ) -> Vec<LevelDerivationWitness> {
        if self.problem.has_real_sorts() || self.problem.has_datatype_sorts() {
            return Vec::new();
        }

        let env = Self::model_i128_env(model);
        // Extract EVERY candidate lane that can be extracted, not just the
        // first: a lane whose derivation cannot be read off this model must not
        // mask a lane whose derivation can, AND a lane that extracts but whose
        // derivation does not ground-validate must not mask a later lane that
        // would. The caller walks this list in order.
        //
        // Each attempt is a bounded DFS, but the NUMBER of attempts is
        // `queries.len()` — and `expand_nullary_fail_queries` is exactly what
        // makes that large. Cap the attempts and honour cancellation so a wide
        // expansion cannot turn a single SAT model into an unbounded stall.
        let mut witnesses = Vec::new();
        for (attempt, (query_clause, body_preds)) in self
            .model_root_query_candidates(model, &env, k, queries)
            .into_iter()
            .enumerate()
        {
            if attempt >= MAX_ROOT_QUERY_CANDIDATES || self.model_extraction_should_stop() {
                tracing::debug!(
                    "BMC: stopping level-model witness extraction after {attempt} lane(s) \
                     (cap/deadline/cancellation)"
                );
                break;
            }
            let mut entries = Vec::new();
            let mut visiting = FxHashSet::default();
            let mut query_roots = Vec::with_capacity(body_preds.len());
            for body_pred in &body_preds {
                let Some(entry) = self.model_derivation_entry(
                    *body_pred,
                    k,
                    model,
                    &env,
                    &mut entries,
                    &mut visiting,
                ) else {
                    query_roots.clear();
                    break;
                };
                query_roots.push(entry);
            }
            if query_roots.len() != body_preds.len() {
                continue;
            }
            let Some(&root) = query_roots.first() else {
                continue;
            };
            witnesses.push(LevelDerivationWitness {
                witness: DerivationWitness {
                    query_clause,
                    root,
                    entries,
                },
                query_roots,
            });
        }
        witnesses
    }

    /// Build a fully-ground derivation over `self.problem`'s clauses from a
    /// level-BMC model and the derivation witness extracted from it.
    ///
    /// The witness already names the fired clause per derived fact and pins
    /// every one of that clause's variables (`model_clause_instances`), so this
    /// is a re-shaping rather than a re-derivation: entries become steps in
    /// TOPOLOGICAL order (the witness DFS emits consumers before premises), and
    /// a final step is appended for the violated query clause.
    ///
    /// Returns `None` whenever the witness is not fully indexed or the query
    /// clause's own variables cannot be read off the model — the result is only
    /// useful if it validates, so an incomplete reconstruction is dropped here
    /// rather than passed on.
    fn ground_derivation_from_witness(
        &self,
        level_witness: &LevelDerivationWitness,
        model: &FxHashMap<String, SmtValue>,
        k: usize,
    ) -> Option<GroundDerivation> {
        let LevelDerivationWitness {
            witness,
            query_roots,
        } = level_witness;
        let query_idx = witness.query_clause?;
        let query_clause = self.problem.clauses().get(query_idx)?;
        // One witness root per query body predicate — a query joining several
        // predicates gets one premise each. The validator enforces the same
        // arity (`PremiseArityMismatch`), so a mismatch here is a reshaping bug
        // and is failed closed rather than handed on.
        if !query_clause.is_query() || query_roots.len() != query_clause.body.predicates.len() {
            return None;
        }
        if query_roots
            .iter()
            .any(|&root| root >= witness.entries.len())
        {
            return None;
        }

        // Post-order DFS from every root so premises land before consumers,
        // which is what `GroundDerivation`'s structural well-foundedness check
        // wants. Roots are seeded in reverse so the first one is expanded (and
        // fully finished, along with its subtree) before the next is popped —
        // which is what keeps the `on_path` cycle check balanced across roots.
        //
        // Note that `mapped` does NOT merge a fact shared by two roots:
        // `model_derivation_witnesses` gives each root its own
        // `model_derivation_entry` call, so root subtrees occupy disjoint entry
        // ranges. Duplicated steps validate fine (each is reachable from the
        // query step), they are just not deduplicated.
        let mut mapped: FxHashMap<usize, usize> = FxHashMap::default();
        let mut steps: Vec<GroundDerivationStep> = Vec::new();
        let mut stack: Vec<(usize, bool)> = query_roots
            .iter()
            .rev()
            .map(|&root| (root, false))
            .collect();
        let mut on_path: FxHashSet<usize> = FxHashSet::default();
        while let Some((entry_idx, expanded)) = stack.pop() {
            if mapped.contains_key(&entry_idx) {
                continue;
            }
            let entry = witness.entries.get(entry_idx)?;
            if !expanded {
                // A repeated index on the current path is a cyclic witness;
                // fail closed instead of emitting an ill-founded derivation.
                if !on_path.insert(entry_idx) {
                    return None;
                }
                stack.push((entry_idx, true));
                for &premise in &entry.premises {
                    if !mapped.contains_key(&premise) {
                        stack.push((premise, false));
                    }
                }
                continue;
            }
            on_path.remove(&entry_idx);
            let clause_index = entry.incoming_clause?;
            let mut premises = Vec::with_capacity(entry.premises.len());
            for premise in &entry.premises {
                premises.push(*mapped.get(premise)?);
            }
            mapped.insert(entry_idx, steps.len());
            steps.push(GroundDerivationStep {
                clause_index,
                env: entry.instances.clone(),
                premises,
            });
        }

        let mut root_steps = Vec::with_capacity(query_roots.len());
        for root in query_roots {
            root_steps.push(*mapped.get(root)?);
        }
        let query_env = self.query_clause_instances(query_clause, k, model)?;
        let query_step = steps.len();
        steps.push(GroundDerivationStep {
            clause_index: query_idx,
            env: query_env,
            premises: root_steps,
        });

        Some(GroundDerivation { steps, query_step })
    }

    /// Read concrete values for every variable of a QUERY clause off the model.
    ///
    /// Mirrors `compile_query`'s variable handling: a query body-predicate
    /// argument that is a bare variable is encoded as that predicate's level
    /// argument at `level`, and every other query variable is emitted into the
    /// SMT formula under its own name.
    fn query_clause_instances(
        &self,
        query: &HornClause,
        level: usize,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<FxHashMap<String, SmtValue>> {
        let mut subst: FxHashMap<String, ChcExpr> = FxHashMap::default();
        for (body_pred, body_args) in &query.body.predicates {
            for (arg_idx, body_arg) in body_args.iter().enumerate() {
                if let ChcExpr::Var(v) = body_arg {
                    subst
                        .entry(v.name.clone())
                        .or_insert_with(|| self.level_arg(*body_pred, arg_idx, level));
                }
            }
        }
        let env = Self::model_i128_env(model);
        let mut instances = FxHashMap::default();
        for var in query.body.vars() {
            let value = match subst.get(&var.name) {
                Some(ChcExpr::Var(mapped)) => model
                    .get(&mapped.name)
                    .and_then(|value| Self::model_smt_value_for_sort(value, &var.sort)),
                Some(other) => Self::model_expr_smt_value_for_sort(other, &var.sort, model, &env),
                None => model
                    .get(&var.name)
                    .and_then(|value| Self::model_smt_value_for_sort(value, &var.sort)),
            };
            // A query variable with no model value cannot be pinned, so the
            // derivation would not ground-evaluate; drop it now.
            instances.insert(var.name.clone(), value?);
        }
        Some(instances)
    }

    /// Root candidates for a level-`k` model, best first, as
    /// `(query clause index, body predicates in body order)`.
    ///
    /// Two properties matter here, both of them completeness properties that
    /// the per-lane query expansion (`expand_nullary_fail_queries`) made
    /// reachable on real input:
    ///
    /// * EVERY query is a candidate, not just the first satisfied one. Root
    ///   identification is only a guess about which lane the model exhibits;
    ///   when extraction fails for one lane the caller must be able to try the
    ///   next, otherwise a lane whose derivation cannot be read off the model
    ///   masks a genuine counterexample sitting in another lane.
    /// * Queries with MORE THAN ONE body predicate are candidates too. They
    ///   were skipped outright, which silently discarded every counterexample
    ///   whose violated query joins several predicates — a shape the expansion
    ///   emits directly.
    ///
    /// Ordering is by evidence strength: queries whose compiled conjuncts the
    /// model satisfies outright, then queries all of whose body-predicate level
    /// flags hold. The first query is kept as a LAST-RESORT candidate (and only
    /// when nothing matched) because `model_conjuncts_satisfied` is itself
    /// partial — it reports "not satisfied" for conjuncts it cannot evaluate,
    /// so a genuinely violated query can fail to match. A wrong guess cannot
    /// produce a wrong verdict: promotion still goes exclusively through
    /// `validate_ground_derivation` on the ORIGINAL clauses.
    fn model_root_query_candidates(
        &self,
        model: &FxHashMap<String, SmtValue>,
        env: &FxHashMap<String, i128>,
        k: usize,
        queries: &[&HornClause],
    ) -> Vec<(Option<usize>, Vec<PredicateId>)> {
        let mut satisfied = Vec::new();
        let mut flags_only = Vec::new();
        let mut fallback = None;
        for query in queries {
            if query.body.predicates.is_empty() {
                continue;
            }
            let body_preds: Vec<PredicateId> = query
                .body
                .predicates
                .iter()
                .map(|(body_pred, _)| *body_pred)
                .collect();
            let query_idx = self.query_clause_index(query);
            if fallback.is_none() {
                fallback = Some((query_idx, body_preds.clone()));
            }

            let mut query_conjuncts = Vec::new();
            self.compile_query(query, k, &mut query_conjuncts);
            if Self::model_conjuncts_satisfied(&query_conjuncts, model, env) {
                satisfied.push((query_idx, body_preds));
                continue;
            }

            if body_preds.iter().all(|body_pred| {
                Self::model_bool_expr(model, &self.level_predicate(*body_pred, k)) == Some(true)
            }) {
                flags_only.push((query_idx, body_preds));
            }
        }
        satisfied.append(&mut flags_only);
        if satisfied.is_empty() {
            satisfied.extend(fallback);
        }
        satisfied
    }

    fn model_derivation_entry(
        &self,
        pred: PredicateId,
        level: usize,
        model: &FxHashMap<String, SmtValue>,
        env: &FxHashMap<String, i128>,
        entries: &mut Vec<DerivationWitnessEntry>,
        visiting: &mut FxHashSet<(PredicateId, usize)>,
    ) -> Option<usize> {
        if !visiting.insert((pred, level)) {
            return None;
        }

        let result = self.model_derivation_entry_inner(pred, level, model, env, entries, visiting);
        visiting.remove(&(pred, level));
        result
    }

    fn model_derivation_entry_inner(
        &self,
        pred: PredicateId,
        level: usize,
        model: &FxHashMap<String, SmtValue>,
        env: &FxHashMap<String, i128>,
        entries: &mut Vec<DerivationWitnessEntry>,
        visiting: &mut FxHashSet<(PredicateId, usize)>,
    ) -> Option<usize> {
        let values = self.model_level_smt_values(pred, level, model)?;
        let (instances, state_expr) = self.concrete_state_witness_smt(pred, &values)?;
        let entry_idx = entries.len();
        entries.push(DerivationWitnessEntry {
            predicate: pred,
            level,
            state: state_expr,
            incoming_clause: None,
            premises: Vec::new(),
            instances,
        });

        for (clause_idx, clause) in self.problem.clauses_defining_with_index(pred) {
            if !self.model_flat_rule_satisfied(pred, clause_idx, clause, level, model, env) {
                continue;
            }

            let before_premises = entries.len();
            let mut premises = Vec::new();
            let mut ok = true;
            for (body_pred, _) in &clause.body.predicates {
                if level == 0 {
                    ok = false;
                    break;
                }
                match self.model_derivation_entry(
                    *body_pred,
                    level - 1,
                    model,
                    env,
                    entries,
                    visiting,
                ) {
                    Some(premise_idx) => premises.push(premise_idx),
                    None => {
                        ok = false;
                        break;
                    }
                }
            }

            if ok {
                let local_instances =
                    self.model_clause_instances(pred, clause_idx, clause, level, model, env);
                for (name, value) in local_instances {
                    entries[entry_idx].instances.entry(name).or_insert(value);
                }
                entries[entry_idx].incoming_clause = Some(clause_idx);
                entries[entry_idx].premises = premises;
                return Some(entry_idx);
            }
            entries.truncate(before_premises);
        }

        entries.pop();
        None
    }

    fn model_flat_rule_satisfied(
        &self,
        pred: PredicateId,
        clause_idx: usize,
        clause: &HornClause,
        level: usize,
        model: &FxHashMap<String, SmtValue>,
        env: &FxHashMap<String, i128>,
    ) -> bool {
        if level == 0 && !clause.body.predicates.is_empty() {
            return false;
        }

        let subst = self.mk_rule_vars(clause, pred, clause_idx, level);
        let mut conjuncts = Vec::new();

        if let ClauseHead::Predicate(_, head_args) = &clause.head {
            for (arg_idx, head_arg) in head_args.iter().enumerate() {
                let level_arg = self.level_arg(pred, arg_idx, level);
                let substituted_arg = head_arg.substitute_name_map(&subst);
                conjuncts.push(ChcExpr::eq(level_arg, substituted_arg));
            }
        }

        for (body_pred, body_args) in &clause.body.predicates {
            if level == 0 {
                return false;
            }
            conjuncts.push(self.level_predicate(*body_pred, level - 1));
            for (arg_idx, body_arg) in body_args.iter().enumerate() {
                let level_arg = self.level_arg(*body_pred, arg_idx, level - 1);
                let substituted_arg = body_arg.substitute_name_map(&subst);
                conjuncts.push(ChcExpr::eq(level_arg, substituted_arg));
            }
        }

        if let Some(constraint) = &clause.body.constraint {
            conjuncts.push(constraint.substitute_name_map(&subst));
        }

        Self::model_conjuncts_satisfied(&conjuncts, model, env)
    }

    fn model_clause_instances(
        &self,
        pred: PredicateId,
        clause_idx: usize,
        clause: &HornClause,
        level: usize,
        model: &FxHashMap<String, SmtValue>,
        env: &FxHashMap<String, i128>,
    ) -> FxHashMap<String, SmtValue> {
        let subst = self.mk_rule_vars(clause, pred, clause_idx, level);
        let mut instances = FxHashMap::default();

        for var in clause.vars() {
            let Some(expr) = subst.get(&var.name) else {
                continue;
            };
            let value = match expr {
                ChcExpr::Var(mapped) => model
                    .get(&mapped.name)
                    .and_then(|value| Self::model_smt_value_for_sort(value, &var.sort)),
                other => Self::model_expr_smt_value_for_sort(other, &var.sort, model, env),
            };
            let Some(value) = value else {
                continue;
            };
            instances.insert(var.name.clone(), value);
        }

        instances
    }

    fn model_conjuncts_satisfied(
        conjuncts: &[ChcExpr],
        model: &FxHashMap<String, SmtValue>,
        env: &FxHashMap<String, i128>,
    ) -> bool {
        conjuncts
            .iter()
            .all(|conjunct| match evaluate_expr(conjunct, model) {
                Some(SmtValue::Bool(value)) => value,
                _ => Self::concrete_eval_bool(conjunct, env) == Some(true),
            })
    }

    fn model_level_smt_values(
        &self,
        pred: PredicateId,
        level: usize,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<Vec<SmtValue>> {
        let pred_info = self.problem.get_predicate(pred)?;
        pred_info
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(idx, sort)| {
                let level_arg = self.level_arg(pred, idx, level);
                let ChcExpr::Var(var) = &level_arg else {
                    return None;
                };
                model
                    .get(&var.name)
                    .and_then(|value| Self::model_smt_value_for_sort(value, sort))
            })
            .collect()
    }

    fn model_expr_smt_value_for_sort(
        expr: &ChcExpr,
        sort: &ChcSort,
        model: &FxHashMap<String, SmtValue>,
        env: &FxHashMap<String, i128>,
    ) -> Option<SmtValue> {
        if let Some(value) = evaluate_expr(expr, model)
            .and_then(|value| Self::model_smt_value_for_sort(&value, sort))
        {
            return Some(value);
        }
        Self::concrete_eval_for_sort(expr, sort, env)
            .and_then(|value| Self::concrete_value_smt(sort, value))
    }

    fn model_value_for_sort(value: &SmtValue, sort: &ChcSort) -> Option<i128> {
        match (sort, value) {
            (ChcSort::Int, SmtValue::Int(value)) => Some(*value),
            (ChcSort::Bool, SmtValue::Bool(value)) => Some(i128::from(*value)),
            (ChcSort::Bool, SmtValue::Int(value)) => Some(i128::from(*value != 0)),
            (ChcSort::BitVec(width), SmtValue::BitVec(value, value_width))
                if width == value_width =>
            {
                i128::try_from(*value).ok()
            }
            _ => None,
        }
    }

    fn model_smt_value_for_sort(value: &SmtValue, sort: &ChcSort) -> Option<SmtValue> {
        match sort {
            ChcSort::Int | ChcSort::Bool => {
                let scalar = Self::model_value_for_sort(value, sort)?;
                Self::concrete_value_smt(sort, scalar)
            }
            // BitVec stays native over SmtValue/u128: funnelling through the
            // i64 scalar path (`model_value_for_sort` -> `i64::try_from`)
            // dropped every BV64 value >= 2^63 — ubiquitous for pointer-like
            // encodings with obj_id in the high lane — making witness arg
            // evaluation fail closed on genuine counterexamples.
            ChcSort::BitVec(width) => match value {
                SmtValue::BitVec(value, value_width) if width == value_width => {
                    Some(SmtValue::BitVec(*value & bv_mask(*width), *width))
                }
                SmtValue::Int(value) => Some(SmtValue::BitVec(
                    Self::concrete_bitvec_value(*width, *value)?,
                    *width,
                )),
                _ => None,
            },
            ChcSort::Array(index_sort, element_sort) => match value {
                SmtValue::ConstArray(default) => Some(SmtValue::ConstArray(Box::new(
                    Self::model_smt_value_for_sort(default, element_sort.as_ref())?,
                ))),
                SmtValue::ArrayMap { default, entries } => {
                    let default = Box::new(Self::model_smt_value_for_sort(
                        default,
                        element_sort.as_ref(),
                    )?);
                    let mut normalized_entries = Vec::with_capacity(entries.len());
                    for (idx, val) in entries {
                        normalized_entries.push((
                            Self::model_smt_value_for_sort(idx, index_sort.as_ref())?,
                            Self::model_smt_value_for_sort(val, element_sort.as_ref())?,
                        ));
                    }
                    Some(SmtValue::ArrayMap {
                        default,
                        entries: normalized_entries,
                    })
                }
                SmtValue::Opaque(name) => Some(SmtValue::Opaque(name.clone())),
                _ => None,
            },
            // Datatype model value: validate the constructor against the sort's
            // definition and recursively normalize each field against its
            // (back-edge-canonicalized) field sort. A well-formed
            // `SmtValue::Datatype` from the executor's total model round-trips;
            // a malformed one (wrong ctor, arity mismatch, un-normalizable
            // field) fails closed to None, which makes the witness incomplete
            // and the caller degrade to Unknown — never a wrong answer.
            ChcSort::Datatype { constructors, .. } => match value {
                SmtValue::Datatype(ctor, fields) => {
                    let cons = constructors.iter().find(|c| &c.name == ctor)?;
                    if cons.selectors.len() != fields.len() {
                        return None;
                    }
                    let mut normalized = Vec::with_capacity(fields.len());
                    for (i, field) in fields.iter().enumerate() {
                        let field_sort = Self::canonical_dt_field_sort(sort, ctor, i)?;
                        normalized.push(Self::model_smt_value_for_sort(field, &field_sort)?);
                    }
                    Some(SmtValue::Datatype(ctor.clone(), normalized))
                }
                _ => None,
            },
            ChcSort::Real | ChcSort::Uninterpreted(_) => None,
        }
    }

    fn model_i128_env(model: &FxHashMap<String, SmtValue>) -> FxHashMap<String, i128> {
        model
            .iter()
            .filter_map(|(name, value)| match value {
                SmtValue::Int(value) => Some((name.clone(), *value)),
                SmtValue::Bool(value) => Some((name.clone(), i128::from(*value))),
                SmtValue::BitVec(value, _) => i128::try_from(*value)
                    .ok()
                    .map(|value| (name.clone(), value)),
                _ => None,
            })
            .collect()
    }

    fn model_bool_expr(model: &FxHashMap<String, SmtValue>, expr: &ChcExpr) -> Option<bool> {
        let ChcExpr::Var(var) = expr else {
            return None;
        };
        match model.get(&var.name)? {
            SmtValue::Bool(value) => Some(*value),
            SmtValue::Int(value) => Some(*value != 0),
            _ => None,
        }
    }

    fn steps_from_derivation_witness(
        &self,
        witness: &DerivationWitness,
    ) -> Vec<CounterexampleStep> {
        let mut chain = Vec::new();
        let mut current = witness.root;
        let mut seen = FxHashSet::default();

        while let Some(entry) = witness.entries.get(current) {
            if !seen.insert(current) {
                break;
            }
            chain.push(current);
            let [next] = entry.premises.as_slice() else {
                break;
            };
            current = *next;
        }
        chain.reverse();

        chain
            .into_iter()
            .filter_map(|idx| {
                let entry = witness.entries.get(idx)?;
                let predicate = self.problem.get_predicate(entry.predicate)?;
                let assignments = predicate
                    .arg_sorts
                    .iter()
                    .enumerate()
                    .filter_map(|(arg_idx, _)| {
                        let name = crate::lemma_hints::canonical_var_name(entry.predicate, arg_idx);
                        let value = entry.instances.get(&name)?;
                        match value {
                            // i128-lockstep: pdr::CounterexampleStep assignments
                            // are an i64 boundary; drop (fail closed) witness
                            // values outside i64 instead of truncating, matching
                            // the existing BitVec fail-closed arm below.
                            SmtValue::Int(value) => {
                                i64::try_from(*value).ok().map(|value| (name, value))
                            }
                            SmtValue::Bool(value) => Some((name, i64::from(*value))),
                            SmtValue::BitVec(value, _) => {
                                i64::try_from(*value).ok().map(|value| (name, value))
                            }
                            _ => None,
                        }
                    })
                    .collect();
                let step = CounterexampleStep::new(entry.predicate, assignments);
                Some(match entry.incoming_clause {
                    Some(clause_idx) => step.with_clause(clause_idx),
                    None => step,
                })
            })
            .collect()
    }

    // ============ Direct Flat Encoding (#7983) ============

    /// Compile level constraints using a direct flat encoding (no rule indicators).
    fn compile_level_flat(&self, level: usize, conjuncts: &mut Vec<ChcExpr>) {
        for pred in self.problem.predicates() {
            let rules: Vec<_> = self.problem.clauses_defining_with_index(pred.id).collect();
            if rules.is_empty() {
                // Same exact dead-lane pin as `compile_level`: no defining
                // clause means the predicate is empty in the least model, so
                // its level flag is false at every level. This matches the
                // `rule_disjuncts.is_empty()` arm below (which already emits
                // `(not pred@k)` for the level-0-with-body-predicates case).
                conjuncts.push(ChcExpr::not(self.level_predicate(pred.id, level)));
                continue;
            }

            let mut rule_disjuncts = Vec::new();

            for (rule_idx, clause) in &rules {
                if level == 0 && !clause.body.predicates.is_empty() {
                    continue;
                }

                let mut rule_conjuncts = Vec::new();
                let subst = self.mk_rule_vars(clause, pred.id, *rule_idx, level);

                if let ClauseHead::Predicate(_, head_args) = &clause.head {
                    for (arg_idx, head_arg) in head_args.iter().enumerate() {
                        let level_arg = self.level_arg(pred.id, arg_idx, level);
                        let substituted_arg = head_arg.substitute_name_map(&subst);
                        rule_conjuncts.push(ChcExpr::eq(level_arg, substituted_arg));
                    }
                }

                for (body_pred, body_args) in &clause.body.predicates {
                    debug_assert!(level > 0);
                    rule_conjuncts.push(self.level_predicate(*body_pred, level - 1));
                    for (arg_idx, body_arg) in body_args.iter().enumerate() {
                        let level_arg = self.level_arg(*body_pred, arg_idx, level - 1);
                        let substituted_arg = body_arg.substitute_name_map(&subst);
                        rule_conjuncts.push(ChcExpr::eq(level_arg, substituted_arg));
                    }
                }

                if let Some(constraint) = &clause.body.constraint {
                    rule_conjuncts.push(constraint.substitute_name_map(&subst));
                }

                if !rule_conjuncts.is_empty() {
                    rule_disjuncts.push(ChcExpr::and_all(rule_conjuncts.iter().cloned()));
                }
            }

            let level_pred = self.level_predicate(pred.id, level);
            if !rule_disjuncts.is_empty() {
                let body = if rule_disjuncts.len() == 1 {
                    rule_disjuncts.remove(0)
                } else {
                    ChcExpr::or_all(rule_disjuncts)
                };
                conjuncts.push(ChcExpr::implies(level_pred, body));
            } else {
                conjuncts.push(ChcExpr::not(level_pred));
            }
        }
    }
}

/// A level-BMC derivation witness plus the entry index of each body predicate
/// of the violated query, in body order.
///
/// `DerivationWitness::root` names a single derived fact, which is exactly what
/// a single-body-predicate query needs and what the counterexample-step chain
/// consumes. A query joining SEVERAL predicates is rooted in one derived fact
/// per body predicate, and the ground reshaping must give the query step a
/// premise for each — so the extra roots ride alongside rather than forcing a
/// shape change on the shared witness type.
struct LevelDerivationWitness {
    witness: DerivationWitness,
    /// Entry index in `witness.entries` per query body predicate, in body
    /// order. Always non-empty; length one for the classic query shape.
    query_roots: Vec<usize>,
}

/// Cap on how many query lanes one SAT model's derivation extraction will try.
///
/// Extraction per lane is a bounded DFS, but the number of LANES is
/// `queries.len()`, which `expand_nullary_fail_queries` inflates by design.
/// Without a cap a wide expansion could turn a single SAT model into a long
/// stall. Exceeding the cap only costs completeness (an unexplored lane), never
/// soundness.
const MAX_ROOT_QUERY_CANDIDATES: usize = 16;

/// One node of a bounded derivation-TREE unfolding (see
/// [`BmcSolver::solve_bounded_tree_refutation`]). Unlike the level-flat
/// encoding, every node has its OWN fresh argument variables, so two
/// applications of the same predicate in a single rule body get independent
/// instances — which is exactly what a branching (nonlinear) counterexample
/// needs, and what the level-flat encoding collapses.
struct TreeNode {
    pred: PredicateId,
    /// Candidate clauses that could derive this node. A per-clause boolean
    /// indicator lets the SAT model pick which one fired (reconstructable).
    choices: Vec<TreeChoice>,
}

struct TreeChoice {
    clause_idx: usize,
    indicator: String,
    child_nodes: Vec<usize>,
    /// This clause's head arguments under the node's fresh substitution — i.e.
    /// expressions over `__tree_c*` clause vars (which survive in the SAT model,
    /// unlike the equality-eliminated node arg vars). Evaluating these gives the
    /// node's concrete predicate-argument values when this clause fired.
    head_arg_exprs: Vec<ChcExpr>,
    /// The clause's ORIGINAL variable names paired with the fresh
    /// (`__tree_c*`) variable they were renamed to, so the reconstruction can
    /// read each original clause variable's concrete value out of the SAT model.
    /// These enrich the witness entry's `instances` with the clause-local names
    /// (e.g. `F`) the counterexample verifier substitutes into the ORIGINAL
    /// clause's head/body arguments — without them, a head argument that is a
    /// pass-through local variable stays symbolic and the (genuine) witness is
    /// wrongly rejected as spurious on wide predicates.
    clause_vars: Vec<(String, ChcVar)>,
}

/// Cap on tree nodes to keep the monolithic unfolding tractable (aborts to
/// Unknown past this — e.g. wide 90-predicate problems).
const TREE_REFUTATION_NODE_CAP: usize = 6000;

/// Per-depth check-sat cap for the datatype bounded refutation lane
/// ([`BmcSolver::solve_datatype_bounded_refutation`]). ay-dpll's datatype+LIA
/// solver can livelock on a single deep unfolding, so each depth is bounded to
/// this slice and iterative deepening covers more depths.
const DT_BMC_PER_DEPTH_CAP: std::time::Duration = std::time::Duration::from_secs(4);

/// Consecutive per-depth executor `unknown`s after which the datatype bounded
/// refutation lane gives up: if ay-dpll cannot decide the unfolding at several
/// successive depths it will not decide the (larger) deeper ones either, so the
/// lane bails to leave budget for the safety routes rather than grind on.
const DT_BMC_MAX_CONSEC_UNKNOWN: usize = 3;

/// Cap on committed clause SELECTIONS the datatype bounded refutation lane
/// enumerates per depth (see [`BmcSolver::enumerate_committed_selections`]).
/// ay-dpll's executor decides a pure datatype+LIA conjunction but returns
/// `unknown` on the indicator-gated DISJUNCTION the tree encoding emits, so the
/// lane resolves the disjunction itself by trying committed conjunctions. This
/// bounds that search: a high-branching unfolding tries a bounded subset and
/// otherwise fail-closes to Unknown (never unsound — every candidate is
/// replayed against the original clauses).
const DT_BMC_MAX_COMMITTED: usize = 256;

/// Per committed-conjunction check-sat cap for the datatype bounded refutation
/// lane. Committed conjunctions decide quickly; this only guards a pathological
/// single check from consuming the whole per-depth slice.
const DT_BMC_PER_COMMIT_CAP: std::time::Duration = std::time::Duration::from_secs(3);

/// Options controlling how [`BmcSolver::build_tree_node`] unfolds a derivation.
struct TreeBuildOpts<'a> {
    /// Cap on tree nodes for this build (see [`TREE_REFUTATION_NODE_CAP`] for
    /// the probe default; competition budgets pass a larger cap — the reve
    /// branching counterexamples are chains deeper than the probe cap reaches,
    /// #chc25-lever-6).
    node_cap: usize,
    /// Skip branching (≥2 body-predicate) clauses, keeping the unfolding a thin
    /// chain (set alongside `committed` by
    /// [`BmcSolver::solve_committed_chain_refutation`]).
    linear_only: bool,
    /// When set, expand ONLY the committed clause for each predicate — the
    /// pre-computed minimal-node derivation clause. This collapses the
    /// disjunctive unfolding to a single deterministic chain (a near-conjunctive
    /// formula the internal SMT can actually solve at the depths these
    /// straight-line program counterexamples require). See
    /// [`BmcSolver::solve_committed_chain_refutation`].
    committed: Option<&'a FxHashMap<PredicateId, usize>>,
}

impl BmcSolver {
    /// Bounded nonlinear derivation-TREE unfolding refutation for cyclic
    /// multi-predicate problems whose counterexample is a *branching* tree —
    /// a rule body with two applications of the same predicate (e.g. reve's
    /// `REC_f_ … REC_f_ …`). The level-flat BMC encoding cannot represent this
    /// (it shares `level_arg` across occurrences of a predicate), so those
    /// counterexamples are missed. This path unfolds the query to a bounded
    /// tree depth, giving every node fresh variables and a rule indicator, then
    /// reconstructs the fired derivation from the SAT model.
    ///
    /// SOUND BY CONSTRUCTION: the reconstructed witness is replayed against the
    /// original CHC by [`Self::verified_unsafe_from_witness`] (a spurious
    /// witness ⇒ `Unknown`); this method only ever returns `Unsafe` or
    /// `Unknown`, never `Safe`.
    pub(crate) fn solve_bounded_tree_refutation(
        &self,
        max_tree_depth: usize,
        budget: std::time::Duration,
        node_cap: usize,
    ) -> ChcEngineResult {
        if self.problem.has_real_sorts() || self.problem.has_datatype_sorts() {
            return ChcEngineResult::Unknown;
        }
        let queries: Vec<_> = self.problem.queries().collect();
        let deadline = ay_core::time::Instant::now() + budget;

        for query in &queries {
            // Only single-body-predicate queries: the witness root is one
            // derived "bad" fact. Other shapes fall through unchanged.
            let [(body_pred, body_args)] = query.body.predicates.as_slice() else {
                continue;
            };
            if ay_core::time::Instant::now() >= deadline || self.config.base.is_cancelled() {
                return ChcEngineResult::Unknown;
            }

            let mut qsubst: FxHashMap<String, ChcExpr> = FxHashMap::default();
            for var in query.vars() {
                qsubst.insert(
                    var.name.clone(),
                    ChcExpr::Var(ChcVar::new(
                        format!("__tree_q_{}", var.name),
                        var.sort.clone(),
                    )),
                );
            }
            let inst_args: Vec<ChcExpr> = body_args
                .iter()
                .map(|a| a.substitute_name_map(&qsubst))
                .collect();

            // Iterative deepening: try shallow trees first, so a shallow
            // branching counterexample is found with a small (sub-cap)
            // unfolding rather than being lost to the node cap at large depth.
            let opts = TreeBuildOpts {
                node_cap,
                linear_only: false,
                committed: None,
            };
            for depth in 2..=max_tree_depth {
                if ay_core::time::Instant::now() >= deadline || self.config.base.is_cancelled() {
                    return ChcEngineResult::Unknown;
                }
                let mut nodes: Vec<TreeNode> = Vec::new();
                let mut fresh: usize = 0;
                let mut global: Vec<ChcExpr> = Vec::new();
                let Some((root_node, root_derivable)) = self.build_tree_node(
                    *body_pred,
                    &inst_args,
                    depth,
                    &opts,
                    &mut nodes,
                    &mut fresh,
                    &mut global,
                ) else {
                    // Node cap hit; deeper unfoldings are only larger.
                    break;
                };
                // formula = all node/clause implications + links (global) ∧ the
                // query's body predicate is derivable ∧ the query constraint.
                let mut root_conj = global;
                root_conj.push(root_derivable);
                if let Some(c) = &query.body.constraint {
                    root_conj.push(c.substitute_name_map(&qsubst));
                }
                let formula = ChcExpr::and_all(root_conj);

                let remaining = deadline.saturating_duration_since(ay_core::time::Instant::now());
                if remaining.is_zero() {
                    return ChcEngineResult::Unknown;
                }
                let mut smt = self.problem.make_smt_context();
                let model = match smt.check_sat_with_timeout(&formula, remaining) {
                    SmtResult::Sat(model) => model,
                    // UNSAT / Unknown at this depth: try a deeper unfolding.
                    _ => continue,
                };

                let mut entries: Vec<DerivationWitnessEntry> = Vec::new();
                if let Some(root_idx) =
                    self.tree_reconstruct(root_node, &nodes, &model, &mut entries)
                {
                    Self::assign_derivation_levels(&mut entries, root_idx);
                    let witness = DerivationWitness {
                        query_clause: self.query_clause_index(query),
                        root: root_idx,
                        entries,
                    };
                    if let ChcEngineResult::Unsafe(cex) =
                        self.verified_unsafe_from_witness(witness, "bounded tree refutation")
                    {
                        return ChcEngineResult::Unsafe(cex);
                    }
                    // Witness failed original-CHC replay at this depth: deepen.
                }
            }
        }
        ChcEngineResult::Unknown
    }

    /// Kill switch for the datatype-aware bounded BMC refutation lane
    /// ([`Self::solve_datatype_bounded_refutation`]). Enabled by default;
    /// `AY_CHC_DISABLE_DT_BMC` set (to any value) disables it.
    fn dt_bmc_refutation_enabled() -> bool {
        std::env::var_os("AY_CHC_DISABLE_DT_BMC").is_none()
    }

    /// Bounded datatype-aware derivation-TREE refutation for CHC problems over
    /// algebraic datatypes (the CHC-COMP ADT-LIA family). The flat/level BMC
    /// encoding bails on datatype sorts (it cannot size/encode ADT args), so
    /// ADT counterexamples — a finite constructor term reaching a bad state —
    /// were never found and every unsafe ADT instance degraded to Unknown.
    ///
    /// This lane reuses the sort-agnostic tree unfolding
    /// ([`Self::build_tree_node`]): it unfolds every query body predicate to a
    /// bounded tree depth (fresh vars + a rule indicator per node) and keeps ADT
    /// arguments as FIRST-CLASS SMT datatype terms (constructor / selector /
    /// tester). `ay-dpll`'s executor has a native datatype theory with TOTAL
    /// model construction and reliably decides pure datatype+LIA conjunctions.
    /// Historically it returned `unknown` on the indicator-gated DISJUNCTION
    /// emitted by the tree encoding. Model-completion improvements can now
    /// decide some raw disjunctions, but not every ADT shape, and a raw model
    /// does not directly identify the fired clause at each tree node.
    ///
    /// This lane therefore RESOLVES the disjunction explicitly: at each depth it
    /// enumerates committed clause selections (one clause per active node,
    /// [`Self::enumerate_committed_selections`]); substitutes each selection's
    /// indicators to collapse the formula to a conjunction; ELIMINATES the
    /// intermediate equality-defined node-arg vars
    /// ([`Self::eliminate_dt_bmc_intermediate_defs`], recovering them into the
    /// model for reconstruction); and hands that conjunction to the
    /// executor-first check-sat. The fired clause per node is the selection, so
    /// the fired derivation (including concrete ADT values) reconstructs
    /// directly ([`Self::tree_reconstruct`]). Iterative deepening `0..=max`;
    /// selections bounded by [`DT_BMC_MAX_COMMITTED`].
    ///
    /// SOUND BY CONSTRUCTION: the reconstructed witness is replayed against the
    /// ORIGINAL CHC by [`Self::verified_unsafe_from_witness`] (a spurious or
    /// un-reconstructable witness ⇒ `Unknown`); this method only ever returns
    /// `Unsafe` (replay-validated) or `Unknown`, never `Safe`. If the executor
    /// cannot decide a depth's committed conjunctions it deepens or gives up —
    /// it never guesses.
    pub(crate) fn solve_datatype_bounded_refutation(
        &self,
        max_tree_depth: usize,
        budget: std::time::Duration,
        node_cap: usize,
    ) -> ChcEngineResult {
        if !Self::dt_bmc_refutation_enabled() {
            return ChcEngineResult::Unknown;
        }
        // Scope: datatype-bearing problems. Reals have no witness-model
        // extraction (`smt_value_expr_for_sort` / `model_smt_value_for_sort`
        // bail), so a mixed ADT+Real problem stays on the existing routes.
        if !self.problem.has_datatype_sorts() || self.problem.has_real_sorts() {
            return ChcEngineResult::Unknown;
        }
        let queries: Vec<_> = self.problem.queries().collect();
        let deadline = ay_core::time::Instant::now() + budget;

        for query in &queries {
            let body_preds = query.body.predicates.clone();
            if body_preds.is_empty() {
                continue;
            }
            if ay_core::time::Instant::now() >= deadline || self.config.base.is_cancelled() {
                return ChcEngineResult::Unknown;
            }

            // Fresh-rename the query's variables so the unfolded body-predicate
            // instances and the query constraint share one namespace.
            let mut qsubst: FxHashMap<String, ChcExpr> = FxHashMap::default();
            for var in query.vars() {
                qsubst.insert(
                    var.name.clone(),
                    ChcExpr::Var(ChcVar::new(
                        format!("__dt_q_{}", var.name),
                        var.sort.clone(),
                    )),
                );
            }

            let opts = TreeBuildOpts {
                node_cap,
                linear_only: false,
                committed: None,
            };
            // Iterative deepening from depth 0: at depth 0 every node may fire
            // only FACT clauses (no recursive unfolding), so a base-case-only
            // ADT counterexample (e.g. drop_inj1's `drop nil 0 nil ∧ drop nil 1
            // nil`) yields a SMALL, recursion-free formula — no free
            // recursive-datatype variables from un-fired branches — that
            // ay-dpll's datatype theory can actually decide. Deeper unfoldings
            // (with the disjunctive recursive branches) are attempted only if
            // the shallow ones are UNSAT.
            let mut consec_unknown = 0usize;
            // PERF (PERF-3 residue): iterative deepening re-derives many
            // committed selections that are TEXTUALLY IDENTICAL to selections
            // already decided UNSAT at a shallower depth (a selection firing
            // its facts at level j is unchanged by growing the unfired tail —
            // the committed indicators collapse it to the same conjunction).
            // Skipping an exact re-run of a definitively-UNSAT formula is
            // sound: UNSAT is budget-independent and deterministic. SAT and
            // Unknown outcomes are never memoized (fail-open).
            let mut unsat_selection_memo: FxHashSet<String> = FxHashSet::default();
            for depth in 0..=max_tree_depth {
                if ay_core::time::Instant::now() >= deadline || self.config.base.is_cancelled() {
                    return ChcEngineResult::Unknown;
                }
                let mut nodes: Vec<TreeNode> = Vec::new();
                let mut fresh: usize = 0;
                let mut global: Vec<ChcExpr> = Vec::new();
                // Unfold EVERY body predicate of the query. ADT-LIA queries are
                // typically multi-body hyperedges (e.g. drop∧drop∧drop∧diseq ⇒
                // false); the shared, fresh-renamed query variables tie the
                // sub-derivations together in ONE SAT solve, so a model assigns
                // globally consistent constructor values across all premises.
                let mut root_nodes: Vec<usize> = Vec::with_capacity(body_preds.len());
                let mut derivables: Vec<ChcExpr> = Vec::with_capacity(body_preds.len());
                let mut capped = false;
                for (bp, bargs) in &body_preds {
                    let inst: Vec<ChcExpr> = bargs
                        .iter()
                        .map(|a| a.substitute_name_map(&qsubst))
                        .collect();
                    match self.build_tree_node(
                        *bp,
                        &inst,
                        depth,
                        &opts,
                        &mut nodes,
                        &mut fresh,
                        &mut global,
                    ) {
                        Some((nid, derivable)) => {
                            root_nodes.push(nid);
                            derivables.push(derivable);
                        }
                        None => {
                            capped = true;
                            break;
                        }
                    }
                }
                let trace = std::env::var_os("AY_DT_BMC_TRACE").is_some();
                if capped {
                    // Node cap hit; deeper unfoldings are only larger.
                    if trace {
                        safe_eprintln!(
                            "[DT-BMC] depth={depth} node cap hit ({} nodes); stop deepening",
                            nodes.len()
                        );
                    }
                    break;
                }
                let mut root_conj = global;
                root_conj.extend(derivables);
                if let Some(c) = &query.body.constraint {
                    root_conj.push(c.substitute_name_map(&qsubst));
                }
                // Flatten to top-level conjuncts once; the raw disjunctive set
                // is retained and specialized per committed selection below.
                let raw_conjuncts: Vec<ChcExpr> = root_conj
                    .iter()
                    .flat_map(ChcExpr::collect_conjuncts_nontrivial)
                    .collect();

                let remaining = deadline.saturating_duration_since(ay_core::time::Instant::now());
                if remaining.is_zero() {
                    return ChcEngineResult::Unknown;
                }
                // Bound each depth to a small slice and let iterative deepening
                // cover more depths rather than burn the whole budget at one.
                let depth_deadline =
                    ay_core::time::Instant::now() + remaining.min(DT_BMC_PER_DEPTH_CAP);

                // Resolve the indicator-gated disjunction HERE: enumerate
                // committed clause selections (one clause per active node),
                // substitute each selection's indicators to collapse the formula
                // to a conjunction, and ELIMINATE the intermediate node-arg vars
                // (the equality-defined variables — inlined at their uses, with
                // the substitution recovered into the SAT model for witness
                // reconstruction). This remains a completeness fallback for raw
                // disjunctions the executor cannot decide and makes the fired
                // clause per node explicit even when it can. Bounded by
                // DT_BMC_MAX_COMMITTED; SOUND regardless — every candidate is
                // replayed against the ORIGINAL clauses by the gate.
                let selections =
                    Self::enumerate_committed_selections(&root_nodes, &nodes, DT_BMC_MAX_COMMITTED);
                let all_indicators: Vec<String> = nodes
                    .iter()
                    .flat_map(|n| n.choices.iter().map(|c| c.indicator.clone()))
                    .collect();
                if trace {
                    safe_eprintln!(
                        "[DT-BMC] depth={depth} nodes={} bodies={} raw_conj={} committed_selections={}",
                        nodes.len(),
                        body_preds.len(),
                        raw_conjuncts.len(),
                        selections.len(),
                    );
                }
                let mut any_decided = false;
                for sel in &selections {
                    if ay_core::time::Instant::now() >= depth_deadline
                        || self.config.base.is_cancelled()
                    {
                        break;
                    }
                    // Collapse the disjunction to this selection's conjunction.
                    let ind_map: FxHashMap<String, ChcExpr> = all_indicators
                        .iter()
                        .map(|n| (n.clone(), ChcExpr::Bool(sel.contains(n))))
                        .collect();
                    let committed_flat: Vec<ChcExpr> = raw_conjuncts
                        .iter()
                        .flat_map(|c| {
                            Self::simplify_bmc_expr(c.substitute_name_map(&ind_map))
                                .collect_conjuncts_nontrivial()
                        })
                        .collect();
                    // Inconsistent selection (some constraint simplified to
                    // false): skip without a solver call. Counts as "decided".
                    if committed_flat
                        .iter()
                        .any(|c| matches!(c, ChcExpr::Bool(false)))
                    {
                        any_decided = true;
                        continue;
                    }
                    // Eliminate the intermediate equality-defined node-arg vars
                    // (fail-closed; see `eliminate_dt_bmc_intermediate_defs`).
                    let (committed, elim_vars) = if Self::dt_bmc_elim_enabled() {
                        Self::eliminate_dt_bmc_intermediate_defs(&committed_flat)
                    } else {
                        (ChcExpr::and_all(committed_flat.clone()), Vec::new())
                    };
                    let per_check = depth_deadline
                        .saturating_duration_since(ay_core::time::Instant::now())
                        .min(DT_BMC_PER_COMMIT_CAP);
                    if per_check.is_zero() {
                        break;
                    }
                    // Canonical-text memo hit: this committed conjunction was
                    // already decided UNSAT at a shallower depth. The key
                    // strips reflexive `(= x x)` residue conjuncts (left by
                    // unfired branches of the deeper tree) — dropping a
                    // tautology never changes sat/unsat, so two selections
                    // with equal keys are equisatisfiable.
                    let committed_key = committed
                        .collect_conjuncts_nontrivial()
                        .iter()
                        .filter(|c| {
                            !matches!(
                                c,
                                ChcExpr::Op(ChcOp::Eq, args)
                                    if args.len() == 2 && args[0] == args[1]
                            )
                        })
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join("\n");
                    if unsat_selection_memo.contains(&committed_key) {
                        any_decided = true;
                        continue;
                    }
                    // Ground definitional fold (PERF-3 residue): committed
                    // selections whose variables chain-resolve to GROUND
                    // constructor terms often fold to a literal `false`
                    // (e.g. `t = leaf 42 ∧ val(t) < 0`); deciding that here
                    // skips a full fresh-Executor SMT solve. Fail-open: any
                    // non-`false` fold falls through to the solver unchanged.
                    if Self::dt_bmc_ground_fold_is_false(&committed) {
                        any_decided = true;
                        unsat_selection_memo.insert(committed_key);
                        continue;
                    }
                    let mut smt = self.problem.make_smt_context();
                    // Force the datatype-capable executor first: the native
                    // DPLL(T) slice has no ADT decision procedure.
                    smt.set_executor_first_check_sat(true);
                    let model = match smt.check_sat_with_timeout(&committed, per_check) {
                        SmtResult::Sat(model) => {
                            any_decided = true;
                            model
                        }
                        // Executor could not decide this committed conjunction
                        // (rare — a pure conjunction): try the next selection.
                        SmtResult::Unknown => continue,
                        // UNSAT: this committed selection has no counterexample.
                        _ => {
                            any_decided = true;
                            unsat_selection_memo.insert(committed_key);
                            continue;
                        }
                    };
                    // Reconstruct the eliminated node-arg vars from the retained
                    // linking equalities so the witness carries the intermediate
                    // datatype values, and inject the selection's indicator truth
                    // values so the shared `tree_reconstruct` (which reads the
                    // fired indicator per node) recovers this committed
                    // derivation. A missing/defaulted value can only make the
                    // witness fail replay (⇒ Unknown), never a wrong answer.
                    let mut fullmodel = if elim_vars.is_empty() {
                        model
                    } else {
                        Self::extend_model_via_branch_equalities(
                            &committed_flat,
                            &elim_vars,
                            &model,
                        )
                    };
                    for n in &all_indicators {
                        fullmodel.insert(n.clone(), SmtValue::Bool(sel.contains(n)));
                    }
                    if let Some(cex) = self.dt_reconstruct_and_replay(
                        &root_nodes,
                        &nodes,
                        &fullmodel,
                        query,
                        depth,
                        trace,
                    ) {
                        return ChcEngineResult::Unsafe(cex);
                    }
                    // SAT but spurious/unreconstructable: try the next selection.
                }
                // Deepen unless the executor could not decide ANY committed
                // conjunction across several successive depths (then bail to
                // free budget for the safety routes). A depth with no committed
                // selections (no derivation) or at least one decided check is
                // progress, not an executor failure.
                if selections.is_empty() || any_decided {
                    consec_unknown = 0;
                } else {
                    consec_unknown += 1;
                    if consec_unknown >= DT_BMC_MAX_CONSEC_UNKNOWN {
                        if trace {
                            safe_eprintln!(
                                "[DT-BMC] {consec_unknown} consecutive undecidable depths; \
                                 bailing lane (executor cannot decide these ADT conjunctions)"
                            );
                        }
                        break;
                    }
                }
            }
        }
        ChcEngineResult::Unknown
    }

    /// Kill switch for the datatype-BMC lane's intermediate-variable elimination
    /// pass ([`Self::eliminate_dt_bmc_intermediate_defs`]). Enabled by default;
    /// `AY_DT_BMC_NO_ELIM` set (to any value) sends the raw (un-eliminated)
    /// committed formula to check-sat, isolating the pass in bisection. Depending
    /// on executor capability this may lose completeness, but never soundness.
    fn dt_bmc_elim_enabled() -> bool {
        std::env::var_os("AY_DT_BMC_NO_ELIM").is_none()
    }

    /// True for the datatype-BMC tree encoding's node-argument variables
    /// (`__tree_n{node}_a{k}`, minted in [`Self::build_tree_node`]). These are
    /// the intermediate equality-defined vars the elimination pass removes; the
    /// `__tree_c*` clause vars and `__tree_ind_*` indicators the witness
    /// reconstruction reads are deliberately NOT matched here, so they survive
    /// in the SAT model.
    fn is_dt_bmc_node_arg_var(name: &str) -> bool {
        name.starts_with("__tree_n")
    }

    /// Cheap ground definitional fold for a committed DT-BMC conjunction:
    /// returns `true` iff the formula PROVABLY simplifies to `false` after
    /// substituting variables that are equality-defined by GROUND terms.
    ///
    /// `F ≡ (x = g) ∧ G(x)` with ground `g` is satisfiable iff `G(g)` is, so
    /// iterating the substitution and constant-folding (which already decides
    /// testers/selectors on constructor terms and arithmetic on literals)
    /// preserves satisfiability exactly; a fold to a `false` conjunct is a
    /// definitive UNSAT. Conflicting ground definitions are handled naturally:
    /// the second equality folds to `g1 = g2` which constant-folds to `false`
    /// for distinct constructors. Any other outcome falls through to the SMT
    /// solver (fail-open) — this is a fast path, never a verdict source for
    /// SAT. Iteration is bounded to keep the pass linear in practice.
    fn dt_bmc_ground_fold_is_false(committed: &ChcExpr) -> bool {
        // Budget bound: the fold is worth at most one saved SMT solve, so a
        // huge committed conjunction (deep trees near the node cap) skips the
        // pass entirely rather than paying O(rounds x formula) rewriting.
        const DT_BMC_GROUND_FOLD_MAX_CONJUNCTS: usize = 512;
        if committed.collect_conjuncts_nontrivial().len() > DT_BMC_GROUND_FOLD_MAX_CONJUNCTS {
            return false;
        }
        // Each round advances every ground-definition frontier by one hop and
        // the loop exits at fixpoint, so the cap only guards pathological
        // formulas; equality chains grow with the unfolding depth, so give
        // enough rounds to drain them.
        let mut current = committed.clone();
        for _round in 0..64 {
            if matches!(current, ChcExpr::Bool(false)) {
                return true;
            }
            let conjuncts = current.collect_conjuncts_nontrivial();
            if conjuncts.iter().any(|c| matches!(c, ChcExpr::Bool(false))) {
                return true;
            }
            // Gather var := ground-term definitions (first definition wins;
            // later conflicting equalities stay in the formula and fold).
            let mut ground_defs: FxHashMap<String, ChcExpr> = FxHashMap::default();
            for conjunct in &conjuncts {
                let ChcExpr::Op(ChcOp::Eq, args) = conjunct else {
                    continue;
                };
                let [lhs, rhs] = args.as_slice() else {
                    continue;
                };
                for (var_side, expr_side) in [(lhs, rhs), (rhs, lhs)] {
                    let ChcExpr::Var(var) = var_side.as_ref() else {
                        continue;
                    };
                    if ground_defs.contains_key(&var.name) {
                        continue;
                    }
                    if expr_side.vars().is_empty() {
                        ground_defs.insert(var.name.clone(), expr_side.as_ref().clone());
                    }
                }
            }
            if ground_defs.is_empty() {
                return false;
            }
            let next = Self::simplify_bmc_expr(current.substitute_name_map(&ground_defs));
            if next == current {
                return false;
            }
            current = next;
        }
        matches!(current, ChcExpr::Bool(false))
            || current
                .collect_conjuncts_nontrivial()
                .iter()
                .any(|c| matches!(c, ChcExpr::Bool(false)))
    }

    /// Eliminate the datatype-BMC lane's intermediate node-argument variables
    /// (`__tree_n{node}_a{k}`) from the check-sat formula by definitional
    /// substitution. Each such variable is EQUALITY-DEFINED by a single
    /// top-level *linking* equality `<incoming-expr> == __tree_n..._a..` that
    /// [`Self::build_tree_node`] pushes to tie a node's predicate application to
    /// its caller's argument expression. The defining `<incoming-expr>` is
    /// always over the caller's clause/query variables (`__tree_c*` / `__dt_q*`)
    /// — never another node-arg var — so the substitution is ACYCLIC and one
    /// pass fully eliminates the node-arg vars, inlining each at its uses inside
    /// the indicator-gated implications.
    ///
    /// ay-dpll's executor returns `unknown` on the raw chained equalities but
    /// decides the SAME formula once these definitional vars are gone (z3
    /// decides both). Returns the simplified formula and the list of eliminated
    /// variables (name + sort) so a SAT model can be extended back to them for
    /// witness reconstruction.
    ///
    /// FAIL-CLOSED: a candidate whose def is self-referential, mentions another
    /// node-arg var, or is contradicted by a second (conflicting) definition is
    /// left in place. The result is always logically equivalent to the input
    /// (pure definitional substitution), so a wrong or skipped elimination only
    /// changes whether the executor decides — the replay gate still rejects any
    /// spurious witness. Only variables named `__tree_n*` are removed.
    fn eliminate_dt_bmc_intermediate_defs(raw_conjuncts: &[ChcExpr]) -> (ChcExpr, Vec<ChcVar>) {
        let mut subst: FxHashMap<String, ChcExpr> = FxHashMap::default();
        let mut eliminated: FxHashMap<String, ChcVar> = FxHashMap::default();
        let mut poisoned: FxHashSet<String> = FxHashSet::default();
        for conjunct in raw_conjuncts {
            let ChcExpr::Op(ChcOp::Eq, args) = conjunct else {
                continue;
            };
            let [lhs, rhs] = args.as_slice() else {
                continue;
            };
            for (var_side, expr_side) in [(lhs, rhs), (rhs, lhs)] {
                let ChcExpr::Var(var) = var_side.as_ref() else {
                    continue;
                };
                if !Self::is_dt_bmc_node_arg_var(&var.name) || poisoned.contains(&var.name) {
                    continue;
                }
                let expr = expr_side.as_ref();
                // Fail-closed: skip a self-referential def, or one over another
                // node-arg var (which would require a fixpoint — by construction
                // this never happens, but keep the single-pass invariant safe).
                if expr
                    .vars()
                    .iter()
                    .any(|v| v.name == var.name || Self::is_dt_bmc_node_arg_var(&v.name))
                {
                    continue;
                }
                match subst.get(&var.name) {
                    Some(existing) if existing == expr => {}
                    Some(_) => {
                        // Two conflicting definitions for the same var: keep it
                        // (drop from the map) and never re-add — fail-closed.
                        subst.remove(&var.name);
                        eliminated.remove(&var.name);
                        poisoned.insert(var.name.clone());
                    }
                    None => {
                        subst.insert(var.name.clone(), expr.clone());
                        eliminated.insert(var.name.clone(), var.clone());
                    }
                }
            }
        }
        if subst.is_empty() {
            return (ChcExpr::and_all(raw_conjuncts.to_vec()), Vec::new());
        }
        let simplified: Vec<ChcExpr> = raw_conjuncts
            .iter()
            .map(|c| c.substitute_name_map(&subst))
            .collect();
        (
            ChcExpr::and_all(simplified),
            eliminated.into_values().collect(),
        )
    }

    /// Enumerate committed clause SELECTIONS for the datatype-BMC tree: each
    /// selection picks exactly one clause (choice) at every ACTIVE node — the
    /// query's `roots` and, transitively, the child nodes of each chosen clause.
    /// A selection is returned as the SET of chosen rule-indicator names (every
    /// other indicator is inactive, i.e. false). Substituting a selection's
    /// indicators into the disjunctive formula collapses it to a pure
    /// datatype+LIA CONJUNCTION, which ay-dpll's executor decides (it cannot
    /// decide the raw indicator-gated disjunction).
    ///
    /// Bounded by `cap`: the breadth-first product is truncated to the first
    /// `cap` selections, so a high-branching unfolding tries a bounded subset
    /// and otherwise fail-closes to Unknown — never unsound (the replay gate
    /// re-checks every candidate).
    fn enumerate_committed_selections(
        roots: &[usize],
        nodes: &[TreeNode],
        cap: usize,
    ) -> Vec<FxHashSet<String>> {
        fn node_selections(
            node_id: usize,
            nodes: &[TreeNode],
            cap: usize,
        ) -> Vec<FxHashSet<String>> {
            let node = &nodes[node_id];
            let mut out: Vec<FxHashSet<String>> = Vec::new();
            for choice in &node.choices {
                let seed: FxHashSet<String> = std::iter::once(choice.indicator.clone()).collect();
                let mut combos: Vec<FxHashSet<String>> = vec![seed];
                for &child in &choice.child_nodes {
                    let child_sels = node_selections(child, nodes, cap);
                    let mut next: Vec<FxHashSet<String>> = Vec::new();
                    'outer: for base in &combos {
                        for cs in &child_sels {
                            let mut merged = base.clone();
                            merged.extend(cs.iter().cloned());
                            next.push(merged);
                            if next.len() >= cap {
                                break 'outer;
                            }
                        }
                    }
                    combos = next;
                    // A child with no derivation kills this choice (empty combos).
                    if combos.is_empty() {
                        break;
                    }
                }
                out.extend(combos);
                if out.len() >= cap {
                    out.truncate(cap);
                    break;
                }
            }
            out
        }

        // Cartesian product across the (independent) root sub-trees.
        let mut all: Vec<FxHashSet<String>> = vec![FxHashSet::default()];
        for &r in roots {
            let sels = node_selections(r, nodes, cap);
            if sels.is_empty() {
                // A body predicate with no derivation at this depth: no
                // committed selection covers the whole query.
                return Vec::new();
            }
            let mut next: Vec<FxHashSet<String>> = Vec::new();
            'outer: for base in &all {
                for s in &sels {
                    let mut merged = base.clone();
                    merged.extend(s.iter().cloned());
                    next.push(merged);
                    if next.len() >= cap {
                        break 'outer;
                    }
                }
            }
            all = next;
        }
        all
    }

    /// Reconstruct the committed datatype-BMC derivation from `model` (which
    /// must pin every rule indicator — e.g. injected from a committed
    /// selection) and replay each candidate root against the ORIGINAL clauses.
    /// Returns a replay-validated counterexample, or `None`
    /// (spurious/unreconstructable — the caller keeps searching). Soundness is
    /// the replay gate's ([`Self::verified_unsafe_from_witness`]), not ours.
    fn dt_reconstruct_and_replay(
        &self,
        roots: &[usize],
        nodes: &[TreeNode],
        model: &FxHashMap<String, SmtValue>,
        query: &HornClause,
        depth: usize,
        trace: bool,
    ) -> Option<Counterexample> {
        let mut entries: Vec<DerivationWitnessEntry> = Vec::new();
        let mut premise_roots: Vec<usize> = Vec::with_capacity(roots.len());
        for nid in roots {
            match self.tree_reconstruct(*nid, nodes, model, &mut entries) {
                Some(ridx) => premise_roots.push(ridx),
                None => return None,
            }
        }
        for &ridx in &premise_roots {
            Self::assign_derivation_levels(&mut entries, ridx);
        }
        // The witness `root` pins the query clause (the verifier resolves a
        // False-head clause referencing the root's predicate). Try each
        // body-predicate sub-tree as the root: whichever the verifier can link
        // to the query and replay Valid yields the Unsafe.
        let query_clause = self.query_clause_index(query);
        for &root_idx in &premise_roots {
            let witness = DerivationWitness {
                query_clause,
                root: root_idx,
                entries: entries.clone(),
            };
            let replay =
                self.verified_unsafe_from_witness(witness, "datatype committed refutation");
            if trace {
                safe_eprintln!(
                    "[DT-BMC] depth={depth} root={root_idx} replay={}",
                    match &replay {
                        ChcEngineResult::Unsafe(_) => "UNSAFE",
                        ChcEngineResult::Unknown => "unknown",
                        _ => "other",
                    }
                );
            }
            if let ChcEngineResult::Unsafe(cex) = replay {
                return Some(cex);
            }
        }
        None
    }

    /// Diagnostic-only: build the datatype-BMC per-depth top-level conjuncts for
    /// the FIRST query at `depth` (mirrors the inner build of
    /// [`Self::solve_datatype_bounded_refutation`]). Used by tests to probe
    /// which formula form ay-dpll's executor decides.
    #[cfg(test)]
    pub(crate) fn dt_bmc_debug_raw_conjuncts(&self, depth: usize) -> Vec<ChcExpr> {
        let query = self.problem.queries().next().expect("a query clause");
        let body_preds = query.body.predicates.clone();
        let mut qsubst: FxHashMap<String, ChcExpr> = FxHashMap::default();
        for var in query.vars() {
            qsubst.insert(
                var.name.clone(),
                ChcExpr::Var(ChcVar::new(
                    format!("__dt_q_{}", var.name),
                    var.sort.clone(),
                )),
            );
        }
        let opts = TreeBuildOpts {
            node_cap: 6000,
            linear_only: false,
            committed: None,
        };
        let mut nodes: Vec<TreeNode> = Vec::new();
        let mut fresh: usize = 0;
        let mut global: Vec<ChcExpr> = Vec::new();
        let mut derivables: Vec<ChcExpr> = Vec::new();
        for (bp, bargs) in &body_preds {
            let inst: Vec<ChcExpr> = bargs
                .iter()
                .map(|a| a.substitute_name_map(&qsubst))
                .collect();
            let (_nid, der) = self
                .build_tree_node(
                    *bp,
                    &inst,
                    depth,
                    &opts,
                    &mut nodes,
                    &mut fresh,
                    &mut global,
                )
                .expect("build_tree_node");
            derivables.push(der);
        }
        let mut root_conj = global;
        root_conj.extend(derivables);
        if let Some(c) = &query.body.constraint {
            root_conj.push(c.substitute_name_map(&qsubst));
        }
        root_conj
            .iter()
            .flat_map(ChcExpr::collect_conjuncts_nontrivial)
            .collect()
    }

    /// For every predicate that has a *linear* (≤1-body-predicate) derivation
    /// bottoming out at a fact, the minimal-NODE such derivation: `(size,
    /// clause_idx)` where `size` is the node count of that derivation and
    /// `clause_idx` is the defining clause it starts with. A fact clause has
    /// size 1. Computed by a shortest-derivation fixpoint (Bellman-Ford-style
    /// relaxation), bounded by the predicate count.
    ///
    /// Used by [`Self::solve_committed_chain_refutation`] to commit to one
    /// deterministic chain instead of the full disjunctive unfolding.
    fn min_node_derivation(&self) -> FxHashMap<PredicateId, (usize, usize)> {
        let preds: Vec<PredicateId> = self.problem.predicates().iter().map(|p| p.id).collect();
        let mut best: FxHashMap<PredicateId, (usize, usize)> = FxHashMap::default();
        // Relax until fixpoint. Each round can only lower a size, and a shortest
        // derivation uses at most `#predicates` distinct steps, so that many
        // rounds suffice.
        for _ in 0..=preds.len() {
            let mut changed = false;
            for &p in &preds {
                for (cidx, clause) in self.problem.clauses_defining_with_index(p) {
                    if clause.body.predicates.len() >= 2 {
                        continue;
                    }
                    let mut total = 1usize;
                    let mut ok = true;
                    for (bp, _) in &clause.body.predicates {
                        match best.get(bp) {
                            Some((s, _)) => total = total.saturating_add(*s),
                            None => {
                                ok = false;
                                break;
                            }
                        }
                    }
                    if !ok {
                        continue;
                    }
                    if best.get(&p).is_none_or(|(cur, _)| total < *cur) {
                        best.insert(p, (total, cidx));
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        best
    }

    /// Bounded COMMITTED-CHAIN refutation for cyclic multi-predicate problems
    /// whose counterexample is a single deep straight-line derivation — the
    /// IntDualyzer BV programs (quicksort / SOR / LU) whose asserted-failure
    /// path is a ~10–27-step base-case execution with NO function-call
    /// branching. The bounded tree / linear unfoldings DO reach that depth, but
    /// their disjunctive "pick any clause at every node" encoding balloons to
    /// hundreds of nodes (thousands of AST nodes) that the internal BV SMT
    /// cannot decide at the counterexample depth.
    ///
    /// This path instead commits to the pre-computed minimal-node derivation
    /// clause at each predicate ([`Self::min_node_derivation`]) and unfolds only
    /// that single chain — a near-conjunctive formula the internal SMT solves
    /// directly. A counterexample whose shortest linear derivation is spurious
    /// (or which genuinely needs branching / a non-minimal chain) is simply not
    /// found here (⇒ `Unknown`); the other refutation lanes cover those shapes.
    ///
    /// SOUND BY CONSTRUCTION: the reconstructed chain is replayed against the
    /// ORIGINAL CHC by [`Self::verified_unsafe_from_witness`] (a spurious
    /// witness ⇒ `Unknown`); returns only `Unsafe` (validated) or `Unknown`,
    /// never `Safe`.
    pub(crate) fn solve_committed_chain_refutation(
        &self,
        budget: std::time::Duration,
    ) -> ChcEngineResult {
        if self.problem.has_real_sorts() || self.problem.has_datatype_sorts() {
            return ChcEngineResult::Unknown;
        }
        let deadline = ay_core::time::Instant::now() + budget;
        let min_deriv = self.min_node_derivation();
        if min_deriv.is_empty() {
            return ChcEngineResult::Unknown;
        }
        let committed: FxHashMap<PredicateId, usize> =
            min_deriv.iter().map(|(p, (_, c))| (*p, *c)).collect();
        let opts = TreeBuildOpts {
            node_cap: TREE_REFUTATION_NODE_CAP,
            linear_only: true,
            committed: Some(&committed),
        };

        let queries: Vec<_> = self.problem.queries().collect();
        for query in &queries {
            // Single-body-predicate queries only: the witness root is one
            // derived "bad" fact (the shape of every IntDualyzer assert query).
            let [(body_pred, body_args)] = query.body.predicates.as_slice() else {
                continue;
            };
            // Only try when the query's bad predicate has a linear
            // derivation-to-fact at all.
            let Some((chain_size, _)) = min_deriv.get(body_pred).copied() else {
                continue;
            };
            if ay_core::time::Instant::now() >= deadline || self.config.base.is_cancelled() {
                return ChcEngineResult::Unknown;
            }

            let mut qsubst: FxHashMap<String, ChcExpr> = FxHashMap::default();
            for var in query.vars() {
                qsubst.insert(
                    var.name.clone(),
                    ChcExpr::Var(ChcVar::new(
                        format!("__tree_q_{}", var.name),
                        var.sort.clone(),
                    )),
                );
            }
            let inst_args: Vec<ChcExpr> = body_args
                .iter()
                .map(|a| a.substitute_name_map(&qsubst))
                .collect();

            // The committed chain self-terminates at a fact (its node size
            // strictly decreases along body predicates), so a depth just past
            // the chain length captures it exactly. The node cap still guards.
            let depth = chain_size.saturating_add(2).min(TREE_REFUTATION_NODE_CAP);
            let mut nodes: Vec<TreeNode> = Vec::new();
            let mut fresh: usize = 0;
            let mut global: Vec<ChcExpr> = Vec::new();
            let Some((root_node, root_derivable)) = self.build_tree_node(
                *body_pred,
                &inst_args,
                depth,
                &opts,
                &mut nodes,
                &mut fresh,
                &mut global,
            ) else {
                continue;
            };
            let mut root_conj = global;
            root_conj.push(root_derivable);
            if let Some(c) = &query.body.constraint {
                root_conj.push(c.substitute_name_map(&qsubst));
            }
            let formula = ChcExpr::and_all(root_conj);

            let remaining = deadline.saturating_duration_since(ay_core::time::Instant::now());
            if remaining.is_zero() {
                return ChcEngineResult::Unknown;
            }
            let mut smt = self.problem.make_smt_context();
            let model = match smt.check_sat_with_timeout(&formula, remaining) {
                SmtResult::Sat(model) => model,
                _ => continue,
            };

            let mut entries: Vec<DerivationWitnessEntry> = Vec::new();
            if let Some(root_idx) = self.tree_reconstruct(root_node, &nodes, &model, &mut entries) {
                Self::assign_derivation_levels(&mut entries, root_idx);
                let witness = DerivationWitness {
                    query_clause: self.query_clause_index(query),
                    root: root_idx,
                    entries,
                };
                if let ChcEngineResult::Unsafe(cex) =
                    self.verified_unsafe_from_witness(witness, "committed chain refutation")
                {
                    return ChcEngineResult::Unsafe(cex);
                }
            }
        }
        ChcEngineResult::Unknown
    }

    /// Build the derivation-tree formula for `pred(incoming_args)` derivable
    /// within `depth` steps, appending fresh nodes to `nodes`. Returns the node
    /// id and the formula, or `None` if the node cap is exceeded.
    fn build_tree_node(
        &self,
        pred: PredicateId,
        incoming_args: &[ChcExpr],
        depth: usize,
        opts: &TreeBuildOpts<'_>,
        nodes: &mut Vec<TreeNode>,
        fresh: &mut usize,
        global: &mut Vec<ChcExpr>,
    ) -> Option<(usize, ChcExpr)> {
        if nodes.len() >= opts.node_cap {
            return None;
        }
        let arg_sorts = self.problem.get_predicate(pred)?.arg_sorts.clone();
        let node_id = nodes.len();
        let arg_vars: Vec<String> = (0..arg_sorts.len())
            .map(|k| format!("__tree_n{node_id}_a{k}"))
            .collect();
        let arg_var_exprs: Vec<ChcExpr> = arg_sorts
            .iter()
            .zip(&arg_vars)
            .map(|(s, n)| ChcExpr::Var(ChcVar::new(n.clone(), s.clone())))
            .collect();
        nodes.push(TreeNode {
            pred,
            choices: Vec::new(),
        });

        // Link the caller's argument expressions to this node's own arg vars
        // (always required — the node IS this predicate application).
        for (k, inc) in incoming_args.iter().enumerate() {
            if let Some(av) = arg_var_exprs.get(k) {
                global.push(ChcExpr::eq(inc.clone(), av.clone()));
            }
        }

        // Own the defining clauses so the recursive calls can re-borrow self.
        let clauses: Vec<(usize, HornClause)> = self
            .problem
            .clauses_defining_with_index(pred)
            .map(|(i, c)| (i, c.clone()))
            .collect();

        let mut indicators: Vec<ChcExpr> = Vec::new();
        let mut choices: Vec<TreeChoice> = Vec::new();
        for (clause_idx, clause) in &clauses {
            if depth == 0 && !clause.body.predicates.is_empty() {
                continue;
            }
            // Linear mode: skip branching (≥2 body-predicate) clauses so the
            // unfolding stays a thin chain. A branching counterexample is not
            // representable here (⇒ Unknown, never a wrong Unsafe).
            if opts.linear_only && clause.body.predicates.len() >= 2 {
                continue;
            }
            // Committed mode: expand ONLY the single minimal-node clause chosen
            // for this predicate — collapses the disjunctive unfolding to one
            // deterministic chain. Predicates absent from the map (unreachable to
            // a fact) get no clause ⇒ `der = false` ⇒ that branch is dead.
            if let Some(committed) = opts.committed {
                if committed.get(&pred) != Some(clause_idx) {
                    continue;
                }
            }
            let cid = *fresh;
            *fresh += 1;
            let indicator = format!("__tree_ind_{cid}");
            let ind = ChcExpr::Var(ChcVar::new(indicator.clone(), ChcSort::Bool));

            let mut subst: FxHashMap<String, ChcExpr> = FxHashMap::default();
            let mut clause_vars: Vec<(String, ChcVar)> = Vec::new();
            for (vi, var) in clause.vars().into_iter().enumerate() {
                let renamed = ChcVar::new(format!("__tree_c{cid}_v{vi}"), var.sort.clone());
                subst.insert(var.name.clone(), ChcExpr::Var(renamed.clone()));
                // Remember original-name → fresh-var so the reconstruction can
                // read the concrete value of each clause-local variable.
                clause_vars.push((var.name.clone(), renamed));
            }

            // Conditions that must hold IF this clause fired (`ind_C => conj`).
            let mut conj: Vec<ChcExpr> = Vec::new();
            let mut head_arg_exprs: Vec<ChcExpr> = Vec::new();
            if let ClauseHead::Predicate(_, head_args) = &clause.head {
                for (k, ha) in head_args.iter().enumerate() {
                    let sub = ha.substitute_name_map(&subst);
                    if let Some(av) = arg_var_exprs.get(k) {
                        conj.push(ChcExpr::eq(av.clone(), sub.clone()));
                    }
                    head_arg_exprs.push(sub);
                }
            }
            if let Some(c) = &clause.body.constraint {
                conj.push(c.substitute_name_map(&subst));
            }

            let mut child_nodes: Vec<usize> = Vec::new();
            let mut ok = true;
            for (bp, bargs) in &clause.body.predicates {
                let binst: Vec<ChcExpr> = bargs
                    .iter()
                    .map(|a| a.substitute_name_map(&subst))
                    .collect();
                match self.build_tree_node(*bp, &binst, depth - 1, opts, nodes, fresh, global) {
                    Some((child_id, child_derivable)) => {
                        child_nodes.push(child_id);
                        // If this clause fired, the body predicate must itself
                        // be derivable within the remaining depth.
                        conj.push(child_derivable);
                    }
                    None => {
                        ok = false;
                        break;
                    }
                }
            }
            if !ok {
                // node cap hit somewhere below: abort this whole build.
                if nodes.len() >= opts.node_cap {
                    return None;
                }
                continue;
            }
            // `ind_C => (head-eqs ∧ constraint ∧ each body pred derivable)`.
            global.push(ChcExpr::implies(ind.clone(), ChcExpr::and_all(conj)));
            choices.push(TreeChoice {
                clause_idx: *clause_idx,
                indicator,
                child_nodes,
                head_arg_exprs,
                clause_vars,
            });
            indicators.push(ind);
        }

        nodes[node_id].choices = choices;
        // The node is derivable iff at least one of its clauses fired.
        let derivable = if indicators.is_empty() {
            ChcExpr::Bool(false)
        } else {
            ChcExpr::or_all(indicators)
        };
        Some((node_id, derivable))
    }

    /// Reconstruct a `DerivationWitnessEntry` sub-tree rooted at `node_id` from
    /// the SAT `model`, following the rule indicator that fired at each node.
    fn tree_reconstruct(
        &self,
        node_id: usize,
        nodes: &[TreeNode],
        model: &FxHashMap<String, SmtValue>,
        entries: &mut Vec<DerivationWitnessEntry>,
    ) -> Option<usize> {
        let node = &nodes[node_id];
        let arg_sorts = self.problem.get_predicate(node.pred)?.arg_sorts.clone();

        // Which clause fired at this node (its rule indicator is true).
        let fired = node.choices.iter().find(|c| {
            let ind = ChcExpr::Var(ChcVar::new(c.indicator.clone(), ChcSort::Bool));
            Self::model_bool_expr(model, &ind) == Some(true)
        });

        // Concrete predicate-argument values: evaluate the fired clause's head
        // argument expressions in the model (the node's own arg vars are
        // equality-eliminated and absent from the model). Fall back to a default
        // only when nothing constrains a slot — a wrong guess merely makes the
        // witness fail replay (⇒ Unknown), never a wrong answer.
        let mut values: Vec<SmtValue> = Vec::with_capacity(arg_sorts.len());
        for (k, sort) in arg_sorts.iter().enumerate() {
            let v = fired
                .and_then(|c| c.head_arg_exprs.get(k))
                .and_then(|e| crate::expr::evaluate::evaluate_expr(e, model))
                .and_then(|val| Self::model_smt_value_for_sort(&val, sort))
                .or_else(|| Self::default_smt_value_for_sort(sort))?;
            values.push(v);
        }
        let (mut instances, state_expr) = self.concrete_state_witness_smt(node.pred, &values)?;
        // Enrich instances with the fired clause's ORIGINAL-named local variable
        // values (read from the model via the fresh `__tree_c*` renaming). The
        // counterexample verifier substitutes these clause-local names into the
        // ORIGINAL clause's head/body arguments; without them a pass-through
        // head argument (a bare local variable this clause neither constrains
        // nor the immediate premise pins) stays symbolic and the genuine
        // witness is rejected as spurious. Values that cannot be read stay
        // absent (the verifier then falls back to its own constraint solve).
        if let Some(choice) = fired {
            for (orig_name, renamed) in &choice.clause_vars {
                if instances.contains_key(orig_name) {
                    continue;
                }
                let renamed_expr = ChcExpr::Var(renamed.clone());
                if let Some(v) = crate::expr::evaluate::evaluate_expr(&renamed_expr, model)
                    .and_then(|val| Self::model_smt_value_for_sort(&val, &renamed.sort))
                {
                    instances.insert(orig_name.clone(), v);
                }
            }
        }
        let entry_idx = entries.len();
        entries.push(DerivationWitnessEntry {
            predicate: node.pred,
            level: 0,
            state: state_expr,
            incoming_clause: None,
            premises: Vec::new(),
            instances,
        });

        if let Some(choice) = fired {
            let before = entries.len();
            let mut premises = Vec::new();
            let mut ok = true;
            for &child in &choice.child_nodes {
                match self.tree_reconstruct(child, nodes, model, entries) {
                    Some(pi) => premises.push(pi),
                    None => {
                        ok = false;
                        break;
                    }
                }
            }
            if ok {
                entries[entry_idx].incoming_clause = Some(choice.clause_idx);
                entries[entry_idx].premises = premises;
            } else {
                entries.truncate(before);
            }
        }
        // If no clause fired (or children were incomplete) the entry stays
        // axiom-like (incoming_clause = None); the witness verifier decides
        // whether it replays as a genuine fact.
        Some(entry_idx)
    }
}

#[cfg(test)]
mod tests;
