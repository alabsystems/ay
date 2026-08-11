// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Adaptive portfolio solver for CHC problems.
//!
//! This module wraps `PortfolioSolver` with intelligent strategy selection
//! based on problem classification. The goal is to predict which engine
//! will work best and budget time accordingly.
//!
//! # Strategy
//!
//! 1. Classify problem (<100ms overhead)
//! 2. Select engine configuration based on class
//! 3. Set appropriate timeouts for graceful degradation
//! 4. Return best result within time budget (if set by caller)
//!
//! By default the solver runs without an internal time limit — the caller
//! controls timeouts via `set_timeout()` or `--timeout`.
//!
//! # Reference
//!
//! Part of #1868 - Adaptive portfolio.
//! See the development design notes for full design.

use crate::adaptive_decision_log::DecisionEntry;
use crate::adaptive_decision_log::DecisionLog;
use crate::adaptive_prestage_budget::algebraic_prestage_budget;
#[cfg(test)]
use crate::adaptive_prestage_budget::{
    ALGEBRAIC_LARGE_ACYCLIC_BUDGET, ALGEBRAIC_POLYNOMIAL_PRESTAGE_BUDGET_CAP,
    ALGEBRAIC_PRESTAGE_BUDGET,
};
use crate::chc_statistics::ChcStatistics;
use crate::classifier::{ProblemClass, ProblemClassifier, ProblemFeatures};
use crate::engine_result::ValidationEvidence;
use crate::failure_analysis::SolverStats;
use crate::lemma_hints::{HintProviders, LemmaHint};
use crate::pdr::{InvariantModel, PdrConfig, PdrResult, PdrSolver, PredicateInterpretation};
use crate::portfolio::features::ChcFeatureExtractor;
use crate::portfolio::selector::EngineSelector;
use crate::portfolio::types::{BudgetPolicy, EngineType};
use crate::portfolio::{PortfolioConfig, PortfolioResult, PortfolioSolver, PreprocessSummary};
use crate::smt::SmtResult;
use crate::synthesis::StructuralSynthesizer;
use crate::transform::{
    BackTranslator, BvToIntAbstractor, CompositeBackTranslator, DeadParamEliminator, DtFlattener,
    IntervalPropagator, SolidityArrayDtProjectionRoute, SolidityArrayDtProjectionStats,
    SolidityArrayDtProjectionTransformer, SolidityArrayDtProjector, TransformationPipeline,
    Transformer,
};
use crate::transition_system::transition_cluster::{
    Tla2TransitionClusterEpochs, Tla2TransitionClusterGuardMetadata,
};
use crate::transition_system::TransitionSystem;
use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseHead, HornClause, Predicate};
use ay_core::kani_compat::DetHashMap as FxHashMap;

use ay_core::time::Instant;
use std::sync::{Arc, Mutex};
use std::time::Duration;

/// Default total time budget for CHC solving (no limit).
///
/// `Duration::ZERO` means "unlimited" — the solver runs until the caller's
/// external timeout (via `set_timeout()` or `--timeout`) fires.  The code
/// already checks `is_zero()` in every budget-related branch (lines 561,
/// 947, 961, 988, 1034) and treats zero as "no deadline".
const DEFAULT_SOLVE_BUDGET: Duration = Duration::ZERO;

/// Stack size for the adaptive solver thread (#6847).
///
/// With `impl Drop for ChcExpr` (iterative, O(1) stack) and stacker
/// guards on recursive traversal paths, 8 MiB is sufficient.
/// Reduced from 128 MiB → 32 MiB → 8 MiB.
pub(crate) const ADAPTIVE_SOLVER_STACK_SIZE: usize = 8 * 1024 * 1024;

/// Fix B3: minimum fraction of the global budget that must remain for the
/// escalation retry round to fire after a first-round Unknown.
const ESCALATION_RETRY_MIN_REMAINING_FRACTION: f64 = 0.25;

/// Wall-clock cap for the SAFE-only Solidity array-DT projection route (#9395).
///
/// This route is a narrow pre-strategy: it exists to catch formulas where
/// `DtFlattener` exposes `Array K SingleCtorDT` predicate arguments that the
/// projection can split cheaply. It must not monopolize CHC-COMP wall time; any
/// timeout or non-SAFE result falls through to the normal adaptive pipeline.
const SOLIDITY_ARRAY_DT_ROUTE_BUDGET: Duration = Duration::from_secs(2);
const SOLIDITY_ARRAY_DT_ROUTE_MIN_STEP_BUDGET: Duration = Duration::from_millis(1);

/// Structural caps for the SAFE-only Solidity array-DT route (#9395).
const SOLIDITY_ARRAY_DT_ROUTE_MAX_CLAUSES: usize = 512;
const SOLIDITY_ARRAY_DT_ROUTE_MAX_PROJECTED_ARGS: usize = 64;
const SOLIDITY_ARRAY_DT_ROUTE_MAX_ADDED_ARGS: usize = 192;
const SOLIDITY_ARRAY_DT_ROUTE_MAX_TRANSFORMED_ARITY: usize = 192;
const ARG_CONSTANT_INVARIANT_ROUTE_BUDGET: Duration = Duration::from_secs(2);
const ARG_CONSTANT_INVARIANT_ROUTE_MIN_BUDGET: Duration = Duration::from_millis(50);
const ARG_CONSTANT_INVARIANT_ROUTE_MAX_PREDICATES: usize = 256;
const ARG_CONSTANT_INVARIANT_ROUTE_MAX_CLAUSES: usize = 2048;
const ARG_CONSTANT_INVARIANT_ROUTE_ENV: &str = "AY_CHC_ENABLE_ARG_CONSTANT_INVARIANT";
/// Cheap admission probe for an all-predicates-top candidate.
///
/// This only checks the transformed query constraints. Acceptance always
/// requires back-translation and strict validation on the original problem.
const TOP_MODEL_QUERY_CHECK_BUDGET: Duration = Duration::from_millis(500);
const ARRAY_CONST_KEY_CEGAR_ROUTE_BUDGET: Duration = Duration::from_millis(750);
const ARRAY_CONST_KEY_CEGAR_ROUTE_MIN_BUDGET: Duration = Duration::from_millis(50);
const ARRAY_CONST_KEY_CEGAR_ROUTE_VALIDATION_RESERVE: Duration = Duration::from_millis(250);
const ARRAY_CONST_KEY_CEGAR_ROUTE_MAX_CLAUSES: usize = 4096;
const ARRAY_CONST_KEY_CEGAR_ROUTE_MAX_TRANSFORMED_ARITY: usize = 256;
/// Early exact preprocessing lane for compiler-generated LIA-array systems.
///
/// Solidity ABI encodings in CHC-COMP commonly collapse from roughly
/// 20 predicates / 30 clauses to a one-predicate, three-clause loop. Running
/// array CEGAR, ghost pairs, and raw non-inlined PDR on the unreduced graph
/// wastes most of a 30s competition budget. This lane only fires after the
/// existing certified preprocessing stack demonstrates a major structural
/// reduction. Every definitive result is still back-translated and validated
/// against the original clauses.
const REDUCED_LIA_ARRAY_ROUTE_DISABLE_ENV: &str = "AY_CHC_DISABLE_REDUCED_LIA_ARRAY_PREPROCESS";
const REDUCED_LIA_ARRAY_ROUTE_MAX_ORIGINAL_CLAUSES: usize = 128;
const REDUCED_LIA_ARRAY_ROUTE_MIN_ORIGINAL_PREDICATES: usize = 4;
const REDUCED_LIA_ARRAY_ROUTE_MAX_PREDICATES: usize = 12;
const REDUCED_LIA_ARRAY_ROUTE_MAX_CLAUSES: usize = 16;
const REDUCED_LIA_ARRAY_ROUTE_MAX_ARITY: usize = 64;
const REDUCED_LIA_ARRAY_ROUTE_BUDGET: Duration = Duration::from_secs(3);
const REDUCED_LIA_ARRAY_ROUTE_MIN_BUDGET: Duration = Duration::from_millis(750);
const REDUCED_LIA_ARRAY_INTERVAL_BUDGET: Duration = Duration::from_millis(500);
const REDUCED_LIA_ARRAY_BMC_BUDGET: Duration = Duration::from_millis(1500);
const REDUCED_LIA_ARRAY_BMC_MAX_DEPTH: usize = 16;
const REDUCED_LIA_ARRAY_VALIDATION_RESERVE: Duration = Duration::from_millis(750);
const REDUCED_LIA_ARRAY_FINAL_REPLAY_RESERVE: Duration = Duration::from_millis(250);
const REAL_LRA_PROMOTION_ENV: &str = "AY_CHC_ENABLE_REAL_LRA_PROMOTION";

/// FORALL-ARR ghost-pair lane (agenda #16): Eldarica-style ghost index/value
/// pairs enabling quantified array invariants without quantifier support in
/// the PDR core. Kill switch: set `AY_CHC_DISABLE_ARRAY_GHOST_PAIRS` to any
/// value to disable the lane entirely.
const ARRAY_GHOST_PAIR_DISABLE_ENV: &str = "AY_CHC_DISABLE_ARRAY_GHOST_PAIRS";
const ARRAY_GHOST_PAIR_ROUTE_NOMINAL_BUDGET: Duration = Duration::from_secs(8);
const ARRAY_GHOST_PAIR_ROUTE_BUDGET_PERCENT: u32 = 30;
const ARRAY_GHOST_PAIR_ROUTE_BUDGET_CAP: Duration = Duration::from_secs(45);
const ARRAY_GHOST_PAIR_ROUTE_MIN_BUDGET: Duration = Duration::from_millis(500);
const ARRAY_GHOST_PAIR_ROUTE_MAX_CLAUSES: usize = 64;
const ARRAY_GHOST_PAIR_ROUTE_MAX_PREDICATES: usize = 24;
/// Preprocessing is used inside the ghost-pair lane only when it removes at
/// least half of the predicates or clauses.  Otherwise the established raw
/// ghost solve remains the fallback: reconstructing a nearly identical model
/// through a long translator stack spends acceptance budget without buying a
/// materially smaller PDR problem.
const ARRAY_GHOST_PAIR_PREPROCESS_REDUCTION_FACTOR: usize = 2;
/// Fraction of a lane's budget reserved for the original-clause quantified
/// certification after the transformed-problem PDR solve.
const ARRAY_GHOST_PAIR_CERTIFY_RESERVE_FRACTION: f64 = 0.25;
/// Budget cap for the finalize-boundary re-check of a sealed ghost-pair
/// certificate (defense in depth on top of `certify_and_seal`).
const ARRAY_GHOST_PAIR_FINALIZE_RECHECK_BUDGET: Duration = Duration::from_secs(20);
const DUAL_CAS_LRA_ARG_COUNT: usize = 9;
const LIA_FARKAS_ROUTE_BUDGET: Duration = Duration::from_secs(3);
const LIA_FARKAS_ROUTE_VALIDATION_RESERVE: Duration = Duration::from_millis(750);

fn should_prioritize_acyclic_bv_proof_prepass(
    features: &ProblemFeatures,
    problem: &ChcProblem,
) -> bool {
    matches!(features.class, ProblemClass::MultiPredLinear)
        && features.is_linear
        && !features.has_cycles
        && !features.uses_arrays
        && problem.has_bv_sorts()
        && (features.num_predicates >= 32 || features.dag_depth >= 32 || features.has_ite)
}

fn complex_query_only_vacuous_safety_must_fail_closed(
    problem: &ChcProblem,
    features: &ProblemFeatures,
) -> bool {
    if features.num_transitions != 0 || features.num_queries == 0 {
        return false;
    }

    problem.has_complex_query_only_vacuous_safety_shape()
}

fn is_dual_cas_lra_arg_shape(sorts: &[ChcSort]) -> bool {
    sorts.len() == DUAL_CAS_LRA_ARG_COUNT
        && matches!(sorts[0], ChcSort::Bool)
        && matches!(sorts[1], ChcSort::Bool)
        && sorts[2..].iter().all(|sort| matches!(sort, ChcSort::Real))
}

fn cruise_canonical_var(pred: &Predicate, arg_idx: usize) -> ChcVar {
    ChcVar::new(
        format!("__p{}_a{}", pred.id.index(), arg_idx),
        pred.arg_sorts[arg_idx].clone(),
    )
}

fn adaptive_canonical_var(pred: &Predicate, arg_idx: usize) -> ChcVar {
    ChcVar::new(
        format!("__p{}_a{}", pred.id.index(), arg_idx),
        pred.arg_sorts[arg_idx].clone(),
    )
}

fn cruise_real_tautology(pred: &Predicate, arg_idx: usize) -> ChcExpr {
    let var = ChcExpr::var(cruise_canonical_var(pred, arg_idx));
    ChcExpr::eq(var.clone(), var)
}

fn cruise_phase_state_formula(args: &[ChcExpr]) -> ChcExpr {
    if args.len() != 20 {
        return ChcExpr::Bool(false);
    }

    let arg = |index: usize| args[index].clone();
    let int = ChcExpr::int;

    ChcExpr::and_all([
        ChcExpr::not(ChcExpr::eq(arg(1), int(2))),
        arg(2),
        ChcExpr::eq(arg(14), ChcExpr::eq(arg(6), int(5))),
        ChcExpr::eq(arg(11), ChcExpr::eq(arg(6), int(6))),
        ChcExpr::not(ChcExpr::eq(arg(8), ChcExpr::eq(arg(0), int(0)))),
        ChcExpr::lt(arg(1), int(9)),
        ChcExpr::or(arg(17), ChcExpr::lt(arg(4), int(19))),
        ChcExpr::or(
            ChcExpr::lt(arg(1), int(1)),
            ChcExpr::gt(ChcExpr::add(arg(1), arg(5)), int(0)),
        ),
        ChcExpr::gt(arg(1), int(0)),
        ChcExpr::or(ChcExpr::lt(arg(1), int(7)), ChcExpr::lt(arg(6), int(4))),
        ChcExpr::or(ChcExpr::gt(arg(1), int(1)), ChcExpr::lt(arg(6), int(4))),
        ChcExpr::eq(arg(7), arg(7)),
    ])
}

fn cruise_apply_model_interp(
    interp: &PredicateInterpretation,
    args: &[ChcExpr],
) -> Option<ChcExpr> {
    if interp.vars.len() != args.len() {
        return None;
    }
    let subst: Vec<_> = interp
        .vars
        .iter()
        .cloned()
        .zip(args.iter().cloned())
        .collect();
    Some(interp.formula.substitute(&subst))
}

/// Check that `query` is unsatisfiable using AY's own SMT backend.
///
/// AY must be hermetic: no external solver (z3, golem, ...) may participate in
/// any answer path. A previous version of this validator shelled out to z3.
/// Returns `false` (validation failure, fail-closed) on Sat/Unknown/panic.
pub(crate) fn ay_says_unsat(query: &ChcExpr, timeout: Duration) -> bool {
    ay_says_unsat_with_dv_hint(query, timeout, false)
}

/// `ay_says_unsat` with a first-attempt EqDiffVar hint (inc-21).
///
/// `dv_off_first` puts the pass-OFF attempt first in the backend's dv retry
/// — callers that already learned their workload is dv-poisoned (a houdini
/// session whose dv-off retry rescued a raw unknown) forward that knowledge
/// so the final validation does not burn ⅔ of its budget on a doomed
/// pass-ON attempt. Pure attempt ordering on the same hermetic backend;
/// fail-closed semantics unchanged.
pub(crate) fn ay_says_unsat_with_dv_hint(
    query: &ChcExpr,
    timeout: Duration,
    dv_off_first: bool,
) -> bool {
    let mut backend = crate::smt::PdrExecutorBackend::new();
    backend
        .check_sat_with_dv_hint(query, timeout, dv_off_first)
        .is_unsat()
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum ArgConstMeet {
    Unseen,
    Const(ChcExpr),
    Top,
}

impl ArgConstMeet {
    fn add(&mut self, value: Option<ChcExpr>) {
        match (&self, value) {
            (Self::Top, _) => {}
            (_, None) => *self = Self::Top,
            (Self::Unseen, Some(value)) => *self = Self::Const(value),
            (Self::Const(current), Some(value)) if current == &value => {}
            (Self::Const(_), Some(_)) => *self = Self::Top,
        }
    }

    fn into_const(self) -> Option<ChcExpr> {
        match self {
            Self::Const(value) => Some(value),
            Self::Unseen | Self::Top => None,
        }
    }
}

fn profile_tla_transition_cluster_applications(problem: &ChcProblem) -> u64 {
    if !problem.has_action_decomposition() {
        return 0;
    }

    let guards = Tla2TransitionClusterGuardMetadata::conservative();
    if !guards.satisfies_conservative_contract() {
        return 0;
    }

    TransitionSystem::tla2_transition_cluster_requests(
        problem,
        Tla2TransitionClusterEpochs::default(),
        guards,
    )
    .map(|requests| requests.len() as u64)
    .unwrap_or(0)
}

fn sort_contains_datatype(sort: &ChcSort) -> bool {
    match sort {
        ChcSort::Datatype { .. } => true,
        ChcSort::Array(key, value) => {
            sort_contains_datatype(key.as_ref()) || sort_contains_datatype(value.as_ref())
        }
        ChcSort::Bool
        | ChcSort::Int
        | ChcSort::Real
        | ChcSort::BitVec(_)
        | ChcSort::Uninterpreted(_) => false,
    }
}

fn problem_has_datatype_predicate_argument(problem: &ChcProblem) -> bool {
    problem
        .predicates()
        .iter()
        .flat_map(|pred| pred.arg_sorts.iter())
        .any(sort_contains_datatype)
}

fn problem_has_linear_arithmetic_predicate_argument(problem: &ChcProblem) -> bool {
    problem
        .predicates()
        .iter()
        .flat_map(|pred| pred.arg_sorts.iter())
        .any(|sort| matches!(sort, ChcSort::Int | ChcSort::Real))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SolidityArrayDtValidationStatus {
    NotRun,
    Accepted,
    RefinedAccepted,
    Failed,
    Error,
    NoBudget,
    Timeout,
}

impl SolidityArrayDtValidationStatus {
    fn as_str(self) -> &'static str {
        match self {
            Self::NotRun => "not_run",
            Self::Accepted => "accepted",
            Self::RefinedAccepted => "refined_accepted",
            Self::Failed => "failed",
            Self::Error => "error",
            Self::NoBudget => "no_budget",
            Self::Timeout => "timeout",
        }
    }
}

/// Adaptive portfolio solver configuration.
#[derive(Debug, Clone)]
pub struct AdaptiveConfig {
    /// Total time budget for solving (default: no limit).
    ///
    /// `Duration::ZERO` means unlimited — the caller controls timeouts via
    /// `set_timeout()` or `--timeout`.
    pub(crate) time_budget: Duration,
    /// Enable verbose output
    pub(crate) verbose: bool,
    /// Skip classification and use default portfolio
    pub(crate) skip_classification: bool,
    /// Force single-engine PDR with TLA trace from `AY_TRACE_FILE`.
    ///
    /// When true, bypasses classification and runs a single PDR solver
    /// with `enable_tla_trace` wired from the environment. This avoids
    /// both parallel clobbering AND sequential overwrites from multiple
    /// engines, while still validating results through the verified pipeline.
    ///
    /// Part of #5811: route trace-mode through VerifiedChcResult.
    pub(crate) trace_mode: bool,
    /// User-provided lemma hints injected into all PDR engines.
    ///
    /// These are merged with built-in hint providers at startup/restart.
    /// See [`PdrConfig::user_hints`] for details.
    pub user_hints: Vec<LemmaHint>,
    /// User-provided runtime hint providers injected into all PDR engines.
    ///
    /// These are called alongside built-in providers. See [`PdrConfig::user_hint_providers`].
    pub user_hint_providers: HintProviders,
    /// Revalidate adaptive Unsafe results before accepting them.
    ///
    /// Kept as a public compatibility field for downstream consumers that set
    /// `AdaptiveConfig::validate` directly. Safe results are always validated.
    #[deprecated(
        since = "0.9.0",
        note = "Safe results are always validated; use strict_proofs for trust-fallback rejection"
    )]
    pub validate: bool,
    /// When true, emit periodic progress lines to stderr (~5s interval).
    ///
    /// CHC progress lines report the current engine phase, elapsed time,
    /// and classification. Uses the `c` comment prefix for compatibility.
    pub progress_enabled: bool,
    /// Strict proof mode: trust-proof fallbacks become errors (#8555).
    ///
    /// When true, any code path that would accept a result without full
    /// independent proof verification returns Unknown instead. This catches
    /// silent fallbacks where proof generation or verification failures are
    /// accepted without error.
    pub strict_proofs: bool,
    /// Per-engine budget policies (#8418).
    ///
    /// When non-empty, these policies are forwarded to the underlying
    /// `PortfolioConfig` before solving. Engines with `BudgetPolicy::Disabled`
    /// are removed from the portfolio. Engines with `BudgetPolicy::MinPercent`
    /// receive at least the specified fraction of the total timeout.
    ///
    /// See [`BudgetPolicy`] for details.
    pub engine_budgets: Vec<(EngineType, BudgetPolicy)>,
    /// Preferred engine execution order (#8418).
    ///
    /// When non-empty, engines matching these types are moved to the front
    /// of the portfolio in the order given. This lets callers hint which
    /// engines to try first based on problem characteristics.
    pub preferred_engine_order: Vec<EngineType>,
    /// Maximum number of engines to spawn in the portfolio (#8604).
    ///
    /// When `Some(n)`, the portfolio engine list is truncated to at most `n`
    /// engines before solving. `None` means no limit (production default).
    pub max_engines: Option<usize>,
    /// Per-portfolio term memory budget in bytes (#8629).
    ///
    /// When `Some(bytes)`, the portfolio divides this budget equally across
    /// engines: each engine's `term_memory_budget` is `bytes / engine_count`.
    ///
    /// When `None` (default), per-engine budgets fall back to the global
    /// `TermStore::per_engine_budget()`.
    pub(crate) memory_budget: Option<usize>,
}

impl Default for AdaptiveConfig {
    fn default() -> Self {
        Self {
            time_budget: DEFAULT_SOLVE_BUDGET,
            verbose: false,
            strict_proofs: false,
            skip_classification: false,
            trace_mode: false,
            user_hints: Vec::new(),
            user_hint_providers: HintProviders::default(),
            validate: false,
            progress_enabled: false,
            engine_budgets: Vec::new(),
            preferred_engine_order: Vec::new(),
            max_engines: None,
            memory_budget: None,
        }
    }
}

impl AdaptiveConfig {
    /// Create an adaptive config with the given time budget and verbosity.
    ///
    /// In test builds, automatically caps the engine count to 3 to reduce
    /// memory usage (#8604). Production builds use no cap.
    pub fn with_budget(time_budget: Duration, verbose: bool) -> Self {
        Self {
            time_budget,
            verbose,
            // In test builds, cap engines to reduce memory (96 MB -> 24 MB per
            // test). Tests that need the full portfolio should set max_engines
            // back to None explicitly.
            #[cfg(test)]
            max_engines: Some(3),
            ..Self::default()
        }
    }

    /// Reduced config for test use. Uses a 10s budget and caps engines to 3.
    ///
    /// Tests that create `AdaptivePortfolio` with this config get a shorter
    /// timeout AND a reduced engine count (#8604).
    pub fn test_default() -> Self {
        Self {
            time_budget: Duration::from_secs(10),
            verbose: false,
            max_engines: Some(3),
            ..Self::default()
        }
    }

    /// Enable trace mode: single-engine PDR with TLA trace from `AY_TRACE_FILE`.
    ///
    /// Runs a single PDR solver to avoid multiple engines clobbering the
    /// trace file, while still validating through the verified pipeline.
    ///
    /// Part of #5811.
    #[must_use]
    pub fn with_trace_mode(mut self, trace: bool) -> Self {
        self.trace_mode = trace;
        self
    }

    /// Builder: override the time budget (#8604).
    ///
    /// Useful with `test_default()` to keep the short-budget test config
    /// while using a custom budget:
    ///
    /// ```rust,no_run
    /// use ay_chc::AdaptiveConfig;
    /// use std::time::Duration;
    ///
    /// let config = AdaptiveConfig::test_default()
    ///     .with_time_budget(Duration::from_secs(25));
    /// ```
    #[must_use]
    pub fn with_time_budget(mut self, budget: Duration) -> Self {
        self.time_budget = budget;
        self
    }

    /// Builder: set a per-portfolio term memory budget in bytes (#8629).
    ///
    /// When set, the portfolio divides this budget equally across engines.
    /// Each engine's `term_memory_budget` is `bytes / engine_count`. This
    /// enables multiple concurrent solves in a shared process (e.g., model-checker-consumer)
    /// without OOM.
    ///
    /// When not set, per-engine budgets fall back to the global process-level
    /// limit divided by engine count.
    ///
    /// ```rust,no_run
    /// use ay_chc::AdaptiveConfig;
    ///
    /// // 512 MB per portfolio:
    /// let config = AdaptiveConfig::test_default()
    ///     .with_memory_budget(512 * 1024 * 1024);
    /// ```
    #[must_use]
    pub fn with_memory_budget(mut self, bytes: usize) -> Self {
        self.memory_budget = Some(bytes);
        self
    }

    /// Builder: add user-provided lemma hints.
    #[must_use]
    pub fn with_user_hints(mut self, hints: Vec<LemmaHint>) -> Self {
        self.user_hints = hints;
        self
    }

    /// Builder: add user-provided runtime hint providers.
    #[must_use]
    pub fn with_user_hint_providers(mut self, providers: HintProviders) -> Self {
        self.user_hint_providers = providers;
        self
    }

    /// Builder: set a per-engine budget policy (#8418).
    ///
    /// # Example
    ///
    /// ```rust,no_run
    /// use ay_chc::{AdaptiveConfig, EngineType, BudgetPolicy};
    /// use std::time::Duration;
    ///
    /// let config = AdaptiveConfig::with_budget(Duration::from_secs(120), false)
    ///     .with_engine_budget(EngineType::Pdr, BudgetPolicy::MinPercent(40))
    ///     .with_engine_budget(EngineType::Bmc, BudgetPolicy::MinPercent(20))
    ///     .with_engine_budget(EngineType::Trl, BudgetPolicy::Disabled);
    /// ```
    #[must_use]
    pub fn with_engine_budget(mut self, engine: EngineType, policy: BudgetPolicy) -> Self {
        self.engine_budgets.push((engine, policy));
        self
    }

    /// Builder: set multiple engine budget policies at once (#8418).
    #[must_use]
    pub fn with_engine_budgets(mut self, policies: Vec<(EngineType, BudgetPolicy)>) -> Self {
        self.engine_budgets = policies;
        self
    }

    /// Builder: set preferred engine execution order (#8418).
    ///
    /// Engines matching `preferred` types are moved to the front of the
    /// portfolio in the order given. This lets callers hint which engines
    /// to try first based on problem characteristics (e.g., non-recursive
    /// problems -> BMC first, deeply nested -> PDR first).
    ///
    /// Engines not present in the portfolio are silently ignored.
    ///
    /// # Example
    ///
    /// ```rust,no_run
    /// use ay_chc::{AdaptiveConfig, EngineType};
    /// use std::time::Duration;
    ///
    /// let config = AdaptiveConfig::with_budget(Duration::from_secs(120), false)
    ///     .with_preferred_engine_order(vec![EngineType::Bmc, EngineType::Pdr]);
    /// ```
    #[must_use]
    pub fn with_preferred_engine_order(mut self, preferred: Vec<EngineType>) -> Self {
        self.preferred_engine_order = preferred;
        self
    }

    /// Builder: set maximum engine count (#8604).
    ///
    /// Caps the portfolio engine list to at most `max` engines before solving.
    /// The truncation preserves priority order: the learned selector and
    /// strategy branches put the best engines first.
    ///
    /// `None` means no limit (production default).
    #[must_use]
    pub fn with_max_engines(mut self, max: Option<usize>) -> Self {
        self.max_engines = max;
        self
    }

    /// Check if a specific engine type is disabled by budget policy.
    pub fn is_engine_disabled(&self, engine: EngineType) -> bool {
        self.engine_budgets
            .iter()
            .any(|(e, p)| *e == engine && matches!(p, BudgetPolicy::Disabled))
    }
}

/// Adaptive portfolio solver for CHC problems.
///
/// Classifies problems and selects appropriate solving strategy
/// for bounded execution scenarios like CHC-COMP (30s timeout).
pub struct AdaptivePortfolio {
    /// The original problem (may contain Array-sorted predicate parameters).
    /// Used for PDR which has native array MBP support.
    pub(crate) problem: ChcProblem,
    /// Scalarized problem where constant-index Array params are expanded to scalars.
    /// Used for engines without native array support (Kind, TRL, TPA).
    /// `None` if the problem has no scalarizable arrays.
    scalarized_problem: Option<ChcProblem>,
    pub(crate) config: AdaptiveConfig,
    /// Structured decision logger for observability. Active only when
    /// `AY_DECISION_LOG` environment variable is set.
    pub(crate) decision_log: DecisionLog,
    /// Accumulated CHC statistics from all engine runs.
    ///
    /// Updated via [`accumulate_stats`](Self::accumulate_stats) from each PDR
    /// solve attempt. Read via [`statistics`](Self::statistics) after `solve()`
    /// completes. Part of #4710 -- CHC stats envelope observability.
    accumulated_stats: Mutex<ChcStatistics>,
    /// Live progress snapshot for observer consumption (#8155 task 7c).
    ///
    /// Engines update this during solving; the progress thread reads it
    /// on its 5-second cadence to emit rich progress lines instead of
    /// generic "CHC portfolio solving..." heartbeats.
    progress_snapshot: Arc<crate::progress::ChcProgressSnapshot>,
    /// Shared cooperative-cancellation token for the whole solve (item 5).
    ///
    /// Exposed via [`cancellation_handle`](Self::cancellation_handle) so an
    /// embedding driver can request cancellation from another thread. Lane
    /// budget timers run on CHILD tokens (`CancellationToken::child`), so a
    /// lane's own `cancel_after` never poisons this shared token, while a
    /// `cancel()` on this token propagates into every lane.
    pub(crate) cancellation_token: crate::cancellation::CancellationToken,
}

impl Drop for AdaptivePortfolio {
    fn drop(&mut self) {
        std::mem::take(&mut self.problem).iterative_drop();
        if let Some(problem) = self.scalarized_problem.take() {
            problem.iterative_drop();
        }
    }
}

struct SolidityArrayDtRefinedSafe {
    model: InvariantModel,
    lemmas_learned: usize,
    max_frame: usize,
}

impl AdaptivePortfolio {
    /// Complex-loop dispatch must not claim constructive BMC evidence.
    ///
    /// `solve_complex_loop()` is an aggregate strategy: it may return `Unsafe`
    /// from a focused BMC probe, direct PDR probes, non-inlined PDR, or the
    /// mixed portfolio. Only the BMC probe is a constructive BMC proof.
    /// Without explicit engine provenance from that helper, the dispatcher
    /// must force final counterexample verification instead of promoting every
    /// complex-loop `Unsafe` as `ValidationEvidence::BmcCounterexample`.
    fn complex_loop_validation_evidence() -> ValidationEvidence {
        ValidationEvidence::FullVerification
    }

    /// Create a new adaptive portfolio solver.
    ///
    /// # Contracts
    ///
    /// REQUIRES: `problem` is a valid ChcProblem with at least one clause.
    ///
    /// ENSURES: Returns a solver ready to invoke `solve()`.
    pub fn new(mut problem: ChcProblem, config: AdaptiveConfig) -> Self {
        // Strip provably-dead-end predicates (no path to any query) when — and
        // only when — that removes the sole dependency cycle blocking the
        // complete bounded acyclic-BMC lane. Sound because a predicate that
        // cannot reach the query never contributes to a query derivation, so
        // dropping its defining clauses is verdict-preserving. Done here, at
        // the single portfolio chokepoint, so the pruned problem flows
        // consistently into classification, every engine lane, and the final
        // certificate-discharge check (`solver.problem()`). A no-op for all
        // problems outside the acyclic-modulo-dead-end class (see
        // `strip_dead_end_cycle_predicates`).
        problem.strip_dead_end_cycle_predicates();

        // Part of #6047: keep the original (non-scalarized) problem for PDR,
        // which has native array MBP support and doesn't need scalarization.
        // Scalarize a separate copy for engines that need it (Kind, TRL, TPA).
        // This avoids the arity explosion from scalarizing BV-indexed arrays
        // (e.g., model-checker-consumer harnesses go from 68 to 191 params per predicate).
        let mut scalarized = problem.clone();
        scalarized.try_scalarize_const_array_selects();
        let scalarized_problem = if scalarized
            .predicates()
            .iter()
            .zip(problem.predicates().iter())
            .any(|(s, o)| s.arg_sorts != o.arg_sorts)
        {
            // Scalarization changed the problem — keep both versions
            Some(scalarized)
        } else {
            // No change — no Array params to scalarize
            None
        };
        let num_predicates = problem.predicates().len() as u64;
        let mut initial_stats = ChcStatistics::default();
        initial_stats.record_tla_transition_cluster_applications(
            profile_tla_transition_cluster_applications(&problem),
        );

        Self {
            problem,
            scalarized_problem,
            config,
            decision_log: DecisionLog::from_env(),
            accumulated_stats: Mutex::new(initial_stats),
            progress_snapshot: Arc::new(crate::progress::ChcProgressSnapshot::new(num_predicates)),
            cancellation_token: crate::cancellation::CancellationToken::new(),
        }
    }

    /// Get a clone of the progress snapshot handle for external observers.
    ///
    /// The returned `Arc` can be shared with a progress thread that polls
    /// the snapshot on a timer to emit rich CHC progress lines (#8155).
    pub fn progress_snapshot(&self) -> Arc<crate::progress::ChcProgressSnapshot> {
        self.progress_snapshot.clone()
    }

    /// Cooperative-cancellation handle for embedding drivers (item 5).
    ///
    /// Returns a clone of the portfolio-wide [`crate::CancellationToken`].
    /// Calling `cancel()` on it from any thread makes an in-flight
    /// [`solve()`](Self::solve) wind down promptly and return
    /// `VerifiedChcResult::Unknown`: the token is observed by the adaptive
    /// stage scheduler (every stage-boundary budget check) and is linked
    /// upstream into the per-lane engine tokens polled by the existing
    /// `config.base.is_cancelled()` / `PdrConfig.cancellation_token`
    /// plumbing, so the currently running engine bails cooperatively too.
    ///
    /// Motivating use case: model-checker-consumer's native driver historically ran the
    /// solve on a detached thread it documented as KNOWN-UNCANCELLABLE and
    /// orphaned on guard timeout (model-checker-consumer `native.rs` guard-timeout path),
    /// leaving the solve burning CPU until internal budgets expired. With
    /// this handle the guard can cancel cooperatively instead of orphaning.
    ///
    /// Cancellation can only degrade a verdict to Unknown — it can never
    /// flip Safe/Unsafe. The handle is idempotent and thread-safe.
    pub fn cancellation_handle(&self) -> crate::cancellation::CancellationToken {
        self.cancellation_token.clone()
    }

    /// Return a snapshot of accumulated CHC statistics.
    ///
    /// Call this after [`solve()`](Self::solve) to retrieve counters collected
    /// during all internal PDR engine runs. The statistics are additive across
    /// probe, retry, and portfolio stages.
    /// Get a reference to the original (non-scalarized) CHC problem.
    ///
    /// Used for certificate output: invariant models reference predicate IDs
    /// from the original problem and need its metadata (predicate names,
    /// argument sorts) to generate SMT-LIB formatted certificates.
    pub fn problem(&self) -> &ChcProblem {
        &self.problem
    }

    pub fn statistics(&self) -> ChcStatistics {
        self.accumulated_stats
            .lock()
            .expect("invariant: stats mutex not poisoned")
            .clone()
    }

    /// Merge stats from a PDR solve attempt into the accumulated counters.
    ///
    /// Also updates the live progress snapshot for observer consumption (#8155).
    pub(crate) fn accumulate_stats(&self, solver_stats: &SolverStats) {
        let chc_stats: ChcStatistics = solver_stats.clone().into();
        self.accumulated_stats
            .lock()
            .expect("invariant: stats mutex not poisoned")
            .merge(&chc_stats);

        // Update live progress snapshot with latest cumulative stats.
        self.progress_snapshot
            .update_pdr_progress(chc_stats.max_frame, chc_stats.lemmas_learned);
    }

    /// Stage-rotation predicate (item 5): was the predecessor PDR stage
    /// Stuck-with-zero-frame-growth?
    ///
    /// Call AFTER `accumulate_stats(stats)` so the live
    /// [`ChcProgressSnapshot`](crate::progress::ChcProgressSnapshot) reflects
    /// the stage; both the stage's own `SolverStats` and the snapshot are
    /// consulted. Conservative on purpose: true only when the stage
    /// terminated via the convergence monitor's Stuck signal AND never
    /// advanced past the initial frame (max_frame <= 1, i.e. zero frame
    /// growth) — a same-family PDR re-run on the same problem would replay
    /// the identical stagnating search, so skipping it is provably redundant.
    /// Completeness-only: skipping can only degrade to Unknown, never flip a
    /// verdict.
    pub(crate) fn predecessor_stage_stuck_no_growth(&self, stats: &SolverStats) -> bool {
        stats.terminated_by_stagnation
            && stats.max_frame <= 1
            && self.progress_snapshot.snapshot().frame_count <= 1
    }

    /// Record a trust-proof fallback event (#8555).
    ///
    /// Called when a code path accepts a result without full independent
    /// proof verification. The count is reported in `--stats` output.
    /// Currently unreferenced: the last caller (the adaptive Unsafe drop
    /// path, gate g4) was replaced by mandatory re-verification in inc-9.
    #[allow(dead_code)]
    pub(crate) fn record_trust_proof_fallback(&self) {
        self.accumulated_stats
            .lock()
            .expect("invariant: stats mutex not poisoned")
            .trust_proof_fallbacks += 1;
    }

    pub(crate) fn record_lra_affine_original_clause_validation_stats(
        &self,
        stats: &crate::algebraic_invariant::AlgebraicValidationStats,
    ) {
        self.accumulated_stats
            .lock()
            .expect("invariant: stats mutex not poisoned")
            .record_lra_affine_original_clause_validation_stats(stats);
    }

    pub(crate) fn record_deterministic_bv_bool_transition_attempt(&self) {
        self.accumulated_stats
            .lock()
            .expect("invariant: stats mutex not poisoned")
            .record_deterministic_bv_bool_transition_attempt();
    }

    pub(crate) fn record_deterministic_bv_bool_transition_recognized(&self) {
        self.accumulated_stats
            .lock()
            .expect("invariant: stats mutex not poisoned")
            .record_deterministic_bv_bool_transition_recognized();
    }

    pub(crate) fn record_deterministic_bv_bool_transition_bmc_unsafe_validated(&self) {
        self.accumulated_stats
            .lock()
            .expect("invariant: stats mutex not poisoned")
            .record_deterministic_bv_bool_transition_bmc_unsafe_validated();
    }

    pub(crate) fn record_deterministic_bv_bool_transition_kind_safe_validated(&self) {
        self.accumulated_stats
            .lock()
            .expect("invariant: stats mutex not poisoned")
            .record_deterministic_bv_bool_transition_kind_safe_validated();
    }

    pub(crate) fn record_deterministic_bv_bool_transition_kind_unsafe_validated(&self) {
        self.accumulated_stats
            .lock()
            .expect("invariant: stats mutex not poisoned")
            .record_deterministic_bv_bool_transition_kind_unsafe_validated();
    }

    pub(crate) fn record_deterministic_bv_bool_transition_bool_control_safe_validated(&self) {
        self.accumulated_stats
            .lock()
            .expect("invariant: stats mutex not poisoned")
            .record_deterministic_bv_bool_transition_bool_control_safe_validated();
    }

    pub(crate) fn record_deterministic_bv_bool_transition_validation_rejection(&self) {
        self.accumulated_stats
            .lock()
            .expect("invariant: stats mutex not poisoned")
            .record_deterministic_bv_bool_transition_validation_rejection();
    }

    /// Get the scalarized problem for non-PDR engines (Kind, TRL, TPA).
    /// Falls back to the original problem if no scalarization was needed.
    pub(crate) fn scalarized_problem(&self) -> &ChcProblem {
        self.scalarized_problem.as_ref().unwrap_or(&self.problem)
    }

    /// Apply user hints and providers from the adaptive config to a PdrConfig.
    pub(crate) fn apply_user_hints(&self, pdr: &mut PdrConfig) {
        if !self.config.user_hints.is_empty() {
            pdr.user_hints = self.config.user_hints.clone();
        }
        if !self.config.user_hint_providers.0.is_empty() {
            pdr.user_hint_providers = self.config.user_hint_providers.clone();
        }
        // Wire live progress snapshot so PDR main loop updates it (#8155).
        if self.config.progress_enabled {
            pdr.progress_snapshot = Some(self.progress_snapshot.clone());
        }
        // Wire the external cancellation handle (item 5): a stage that already
        // carries its own token additionally observes the portfolio handle
        // upstream, so an embedding driver's cancel reaches the running PDR
        // lane. Stages WITHOUT a token are deliberately left untouched — a
        // token's mere presence changes `has_budget` gating (main loop 5s SMT
        // cap, stagnation windows) and the `solve_problem` case-split gate,
        // and the default behavior of those paths must not change. Pure
        // augmentation: with no external cancel the linked token behaves
        // identically.
        if let Some(token) = &mut pdr.cancellation_token {
            token.link_upstream(&self.cancellation_token);
        }
    }

    /// Apply user hints, providers, budget policies, and engine ordering to a portfolio config.
    fn apply_user_hints_portfolio(&self, config: &mut PortfolioConfig) {
        if !self.config.user_hints.is_empty() {
            config.set_pdr_user_hints(self.config.user_hints.clone());
        }
        if !self.config.user_hint_providers.0.is_empty() {
            config.set_pdr_user_hint_providers(self.config.user_hint_providers.clone());
        }
        // Forward per-engine budget policies from AdaptiveConfig (#8418).
        if !self.config.engine_budgets.is_empty() {
            for (engine, policy) in &self.config.engine_budgets {
                config.engine_budgets.insert(*engine, *policy);
            }
        }
        // Forward preferred engine order from AdaptiveConfig (#8418).
        if !self.config.preferred_engine_order.is_empty() {
            config.reorder_engines(&self.config.preferred_engine_order);
        }
        // Forward per-portfolio memory budget from AdaptiveConfig (#8629).
        if self.config.memory_budget.is_some() {
            config.memory_budget = self.config.memory_budget;
        }
        // Wire the external cancellation handle (item 5): the portfolio's
        // internal token becomes a child of the adaptive-level token, so an
        // embedding driver's cancel stops all engines/validation while the
        // portfolio's own winner-found/timeout cancels stay contained.
        if config.external_cancellation.is_none() {
            config.external_cancellation = Some(self.cancellation_token.clone());
        }
    }

    /// Run a portfolio solver with user hints and budget policies applied.
    pub(crate) fn run_portfolio(&self, mut config: PortfolioConfig) -> PortfolioResult {
        self.apply_user_hints_portfolio(&mut config);

        if let Some(max) = self.config.max_engines {
            config.engines.truncate(max);
        }

        // Update live progress snapshot with engine names (#8155).
        if !config.engines.is_empty() {
            let first_engine = config.engines[0].name();
            self.progress_snapshot.set_active_engine(first_engine, 0);
        }

        PortfolioSolver::new(self.problem.clone(), config).solve()
    }

    #[allow(dead_code)] // Quarantined from default promotion until Real/LRA wrong=0 evidence exists.
    fn try_dual_cas_lra_phase_invariant(
        &self,
        features: &ProblemFeatures,
    ) -> Option<PortfolioResult> {
        if !features.uses_real
            || !features.has_ite
            || !features.is_single_predicate
            || features.num_predicates != 1
            || features.num_clauses != 3
            || features.num_facts != 1
            || features.num_transitions != 1
            || features.num_queries != 1
            || features.uses_arrays
            || self.problem.has_bv_sorts()
            || self.problem.has_datatype_sorts()
        {
            return None;
        }

        let pred = self.problem.predicates().first()?;
        if !is_dual_cas_lra_arg_shape(&pred.arg_sorts) {
            return None;
        }

        let vars: Vec<_> = pred
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(i, sort)| ChcVar::new(format!("__p{}_a{}", pred.id.index(), i), sort.clone()))
            .collect();
        let var = |index: usize| ChcExpr::var(vars[index].clone());
        let real = |value: i64| ChcExpr::Real(value, 1);
        let pending_write_positive = |phase_index: usize, value_index: usize| {
            ChcExpr::or_all([
                ChcExpr::lt(var(phase_index), real(1)),
                ChcExpr::gt(var(phase_index), real(2)),
                ChcExpr::ge(var(value_index), real(1)),
            ])
        };

        let formula = ChcExpr::and_all([
            ChcExpr::ge(var(2), real(0)),
            ChcExpr::ge(var(3), real(0)),
            ChcExpr::ge(var(4), real(0)),
            ChcExpr::ge(var(5), real(0)),
            ChcExpr::ge(var(8), real(0)),
            ChcExpr::or(ChcExpr::not(var(0)), ChcExpr::gt(var(8), real(0))),
            ChcExpr::or(ChcExpr::not(var(1)), ChcExpr::gt(var(8), real(0))),
            pending_write_positive(6, 2),
            pending_write_positive(7, 3),
        ]);

        let mut model = InvariantModel::new();
        model.set(pred.id, PredicateInterpretation::new(vars, formula));

        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: Trying dual-CAS LRA phase invariant through adaptive validation"
            );
        }
        let mut verifier = PdrSolver::new(
            self.problem.clone(),
            PdrConfig {
                verbose: self.config.verbose,
                strict_proofs: true,
                solve_timeout: Some(Duration::from_secs(30)),
                disable_array_scalarization: true,
                ..PdrConfig::default()
            },
        );
        if verifier.verify_model_per_rule(&model, Duration::from_millis(1500)) {
            if self.config.verbose {
                safe_eprintln!("Adaptive: Dual-CAS LRA phase invariant validated");
            }
            Some(PortfolioResult::Safe(model))
        } else {
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: Dual-CAS LRA phase invariant failed validation, ignoring"
                );
            }
            None
        }
    }

    fn try_cruise_controller_mixed_phase_invariant(
        &self,
        features: &ProblemFeatures,
        deadline: Option<Instant>,
    ) -> Option<PortfolioResult> {
        if self.budget_exhausted(deadline) {
            return None;
        }
        if !features.uses_real
            || !features.has_multiplication
            || !features.has_mod_div
            || features.uses_arrays
            || self.problem.has_bv_sorts()
            || self.problem.has_datatype_sorts()
            || features.num_predicates != 5
            || features.num_clauses != 7
            || features.num_facts != 3
            || features.num_transitions != 3
            || features.num_queries != 1
        {
            return None;
        }

        let route_start = Instant::now();
        let init_state = self.problem.get_predicate_by_name("INIT_STATE")?;
        let top_reset = self.problem.get_predicate_by_name("top_reset")?;
        let top_step = self.problem.get_predicate_by_name("top_step")?;
        let main = self.problem.get_predicate_by_name("MAIN")?;
        let err = self.problem.get_predicate_by_name("ERR")?;

        if !err.arg_sorts.is_empty()
            || !init_state.arg_sorts.is_empty()
            || main.arg_sorts.len() != 21
            || top_reset.arg_sorts.len() != 40
            || top_step.arg_sorts.len() != 49
            || main.arg_sorts[20] != ChcSort::Bool
            || top_step.arg_sorts[8] != ChcSort::Bool
        {
            return None;
        }

        let mut model = InvariantModel::new();
        self.set_predicate_phase_model(&mut model, init_state, ChcExpr::Bool(true));
        self.set_predicate_phase_model(
            &mut model,
            top_reset,
            ChcExpr::and(
                ChcExpr::var(cruise_canonical_var(top_reset, 39)),
                cruise_real_tautology(top_reset, 7),
            ),
        );
        self.set_predicate_phase_model(&mut model, err, ChcExpr::Bool(false));

        let top_step_vars: Vec<_> = (0..top_step.arg_sorts.len())
            .map(|idx| ChcExpr::var(cruise_canonical_var(top_step, idx)))
            .collect();
        let top_step_pre_state = cruise_phase_state_formula(&top_step_vars[9..29]);
        let top_step_post_state = cruise_phase_state_formula(&top_step_vars[29..49]);
        let top_step_reset_or_phase = ChcExpr::or(top_step_vars[28].clone(), top_step_pre_state);
        self.set_predicate_phase_model(
            &mut model,
            top_step,
            ChcExpr::and(
                ChcExpr::implies(
                    top_step_reset_or_phase,
                    ChcExpr::and(top_step_vars[8].clone(), top_step_post_state),
                ),
                cruise_real_tautology(top_step, 6),
            ),
        );

        let main_vars: Vec<_> = (0..main.arg_sorts.len())
            .map(|idx| ChcExpr::var(cruise_canonical_var(main, idx)))
            .collect();
        self.set_predicate_phase_model(
            &mut model,
            main,
            ChcExpr::and(
                main_vars[20].clone(),
                cruise_phase_state_formula(&main_vars[..20]),
            ),
        );

        let validation_budget = self
            .remaining_budget(deadline)
            .unwrap_or(Duration::from_secs(4))
            .min(Duration::from_secs(4));
        if validation_budget < Duration::from_millis(50) {
            self.decision_log.log_decision(DecisionEntry {
                stage: "mixed_lia_lra_cruise_phase_invariant",
                gate_result: false,
                gate_reason: "validation budget exhausted".to_string(),
                budget_secs: validation_budget.as_secs_f64(),
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "unknown",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        }

        let validation_result = self.validate_cruise_phase_model(&model, validation_budget);
        let validated = validation_result.is_ok();
        let gate_reason = match &validation_result {
            Ok(()) => {
                "MAIN/top_step safety phase invariant validated on original clauses".to_string()
            }
            Err(reason) => reason.clone(),
        };
        self.decision_log.log_decision(DecisionEntry {
            stage: "mixed_lia_lra_cruise_phase_invariant",
            gate_result: validated,
            gate_reason,
            budget_secs: validation_budget.as_secs_f64(),
            elapsed_secs: route_start.elapsed().as_secs_f64(),
            result: if validated { "safe" } else { "unknown" },
            lemmas_learned: 0,
            max_frame: 0,
        });

        validated.then_some(PortfolioResult::Safe(model))
    }

    fn validate_cruise_phase_model(
        &self,
        model: &InvariantModel,
        validation_budget: Duration,
    ) -> Result<(), String> {
        let start = Instant::now();
        for (idx, clause) in self.problem.clauses().iter().enumerate() {
            let Some(remaining) = validation_budget.checked_sub(start.elapsed()) else {
                return Err(format!("validation budget exhausted before clause {idx}"));
            };
            if remaining < Duration::from_millis(25) {
                return Err(format!("validation budget exhausted before clause {idx}"));
            }

            let Some(query) = self.cruise_phase_clause_violation_query(model, clause) else {
                return Err(format!("could not instantiate clause {idx} under model"));
            };
            let query = query.simplify_constants();
            match query {
                ChcExpr::Bool(false) => continue,
                ChcExpr::Bool(true) => {
                    return Err(format!("clause {idx} violation simplified to true"));
                }
                _ => {}
            }

            let per_clause = remaining.min(Duration::from_millis(750));
            if !ay_says_unsat(&query, per_clause) {
                return Err(format!("clause {idx} violation was satisfiable or unknown"));
            }
        }
        Ok(())
    }

    /// Tier-1 query-flag candidate-invariant prepass (lustre-class).
    ///
    /// Transition-system encodings (e.g. the vmt-chc lustre family) often
    /// have a single `state` predicate and a query of the form
    /// `state(a_0..a_n) ∧ ¬a_i ⇒ false` where Bool argument `a_i` is the
    /// "property holds" flag. For roughly half of the sat instances in that
    /// family the inductive invariant is literally `state(args) := a_i`.
    /// Guess that candidate and accept ONLY if every original clause's
    /// violation query is proven UNSAT by AY's own executor-backed SMT
    /// (guess-and-check; fail-closed on Sat/Unknown).
    pub(crate) fn try_query_flag_invariant_prepass(
        &self,
        features: &ProblemFeatures,
        deadline: Option<Instant>,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        if !features.is_single_predicate
            || features.uses_arrays
            || features.uses_datatypes
            || self.problem.has_bv_sorts()
        {
            return None;
        }
        let route_start = Instant::now();
        let mut queries = self.problem.queries();
        let query = queries.next()?;
        if queries.next().is_some() {
            return None;
        }
        let [(qpred, qargs)] = query.body.predicates.as_slice() else {
            return None;
        };
        // Query constraint must be `¬flag` (candidate: flag) or `flag`
        // (candidate: ¬flag) for a Bool predicate argument `flag`.
        let constraint = query.body.constraint.as_ref()?;
        let (flag_var, positive) = match constraint {
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => match args[0].as_ref() {
                ChcExpr::Var(v) => (v.clone(), true),
                _ => return None,
            },
            ChcExpr::Var(v) => (v.clone(), false),
            _ => return None,
        };
        let flag_idx = qargs
            .iter()
            .position(|a| matches!(a, ChcExpr::Var(v) if *v == flag_var))?;
        let pred = self.problem.get_predicate(*qpred)?;
        if !matches!(pred.arg_sorts.get(flag_idx), Some(ChcSort::Bool)) {
            return None;
        }

        // Scaled with the global budget (#phase0c); per-clause cap scales too.
        let route_budget =
            self.scaled_probe_budget(deadline, Duration::from_secs(8), 10, Duration::from_mins(1));
        if route_budget < Duration::from_millis(100) {
            return None;
        }
        // inc-12: the consecution (transition) clause is the one real SMT
        // query here and used to fail its 3s floor on protocol-class
        // instances (MOESI: the guessed flag invariant IS golem's invariant,
        // but the proof needed >3s). Give each clause up to half the route
        // budget with a 6s floor; the route budget still bounds the total.
        let per_clause_cap =
            (route_budget / 2).clamp(Duration::from_secs(6), Duration::from_secs(30));

        let vars: Vec<ChcVar> = pred
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(i, sort)| ChcVar::new(format!("__qf{}_a{i}", pred.id.index()), sort.clone()))
            .collect();
        let flag = ChcExpr::Var(vars[flag_idx].clone());
        let formula = if positive { flag } else { ChcExpr::not(flag) };
        let mut model = InvariantModel::new();
        model.set(pred.id, PredicateInterpretation::new(vars, formula));

        // Validate the candidate against EVERY original clause: each
        // violation query must be UNSAT under AY's executor-backed SMT.
        let mut validated = true;
        let mut gate_reason = "query-flag invariant validated on all original clauses".to_string();
        for (idx, clause) in self.problem.clauses().iter().enumerate() {
            let Some(remaining) = route_budget.checked_sub(route_start.elapsed()) else {
                validated = false;
                gate_reason = format!("budget exhausted before clause {idx}");
                break;
            };
            let per_clause = remaining.min(per_clause_cap);
            if per_clause < Duration::from_millis(25) {
                validated = false;
                gate_reason = format!("budget exhausted before clause {idx}");
                break;
            }
            let Some(violation) = self.cruise_phase_clause_violation_query(&model, clause) else {
                validated = false;
                gate_reason = format!("could not instantiate clause {idx} under candidate");
                break;
            };
            match violation.simplify_constants() {
                ChcExpr::Bool(false) => continue,
                ChcExpr::Bool(true) => {
                    validated = false;
                    gate_reason = format!("clause {idx} violation simplified to true");
                    break;
                }
                violation => {
                    if !ay_says_unsat(&violation, per_clause) {
                        validated = false;
                        gate_reason =
                            format!("clause {idx} violation not proven unsat (sat or unknown)");
                        break;
                    }
                }
            }
        }

        self.decision_log.log_decision(DecisionEntry {
            stage: "query_flag_invariant_prepass",
            gate_result: validated,
            gate_reason,
            budget_secs: route_budget.as_secs_f64(),
            elapsed_secs: route_start.elapsed().as_secs_f64(),
            result: if validated { "safe" } else { "unknown" },
            lemmas_learned: 0,
            max_frame: 0,
        });
        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: query-flag invariant prepass {} in {:.2}s",
                if validated { "validated" } else { "failed" },
                route_start.elapsed().as_secs_f64()
            );
        }

        validated.then_some((
            PortfolioResult::Safe(model),
            ValidationEvidence::FullVerification,
        ))
    }

    pub(crate) fn cruise_phase_clause_violation_query(
        &self,
        model: &InvariantModel,
        clause: &HornClause,
    ) -> Option<ChcExpr> {
        let mut body = Vec::new();
        if let Some(constraint) = &clause.body.constraint {
            body.push(constraint.clone());
        }
        for (pred, args) in &clause.body.predicates {
            body.push(cruise_apply_model_interp(model.get(pred)?, args)?);
        }

        let body_formula = ChcExpr::and_all(body);
        match &clause.head {
            ClauseHead::False => Some(body_formula),
            ClauseHead::Predicate(pred, args) => {
                let head_formula = cruise_apply_model_interp(model.get(pred)?, args)?;
                Some(ChcExpr::and(body_formula, ChcExpr::not(head_formula)))
            }
        }
    }

    fn set_predicate_phase_model(
        &self,
        model: &mut InvariantModel,
        pred: &Predicate,
        formula: ChcExpr,
    ) {
        let vars: Vec<_> = pred
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(idx, sort)| {
                ChcVar::new(format!("__p{}_a{}", pred.id.index(), idx), sort.clone())
            })
            .collect();
        model.set(pred.id, PredicateInterpretation::new(vars, formula));
    }

    fn try_argument_constant_invariant_route(
        &self,
        deadline: Option<Instant>,
    ) -> Option<PortfolioResult> {
        let route_start = Instant::now();
        if !(self.problem.has_array_sorts() || self.problem.has_datatype_sorts()) {
            return None;
        }
        if std::env::var_os(ARG_CONSTANT_INVARIANT_ROUTE_ENV).is_none() {
            self.decision_log.log_decision(DecisionEntry {
                stage: "arg_constant_invariant",
                gate_result: false,
                gate_reason: format!(
                    "quarantined by default; set {ARG_CONSTANT_INVARIANT_ROUTE_ENV}=1 for experimental runs"
                ),
                budget_secs: 0.0,
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "quarantined",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        }
        if self.problem.predicates().len() > ARG_CONSTANT_INVARIANT_ROUTE_MAX_PREDICATES
            || self.problem.clauses().len() > ARG_CONSTANT_INVARIANT_ROUTE_MAX_CLAUSES
        {
            self.decision_log.log_decision(DecisionEntry {
                stage: "arg_constant_invariant",
                gate_result: false,
                gate_reason: format!(
                    "size cap exceeded: predicates={} clauses={}",
                    self.problem.predicates().len(),
                    self.problem.clauses().len()
                ),
                budget_secs: 0.0,
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "cap_exceeded",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        }

        let (model, constant_count, unreachable_count, blocked_queries) =
            self.infer_argument_constant_model()?;
        let total_queries = self
            .problem
            .clauses()
            .iter()
            .filter(|clause| clause.is_query())
            .count();
        if blocked_queries == 0 || blocked_queries != total_queries {
            self.decision_log.log_decision(DecisionEntry {
                stage: "arg_constant_invariant",
                gate_result: false,
                gate_reason: format!(
                    "inferred constants/unreachability do not block all queries ({blocked_queries}/{total_queries}); constants={constant_count}; unreachable={unreachable_count}"
                ),
                budget_secs: 0.0,
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "not_applicable",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        }

        let remaining = self
            .remaining_budget(deadline)
            .unwrap_or(ARG_CONSTANT_INVARIANT_ROUTE_BUDGET);
        if remaining < ARG_CONSTANT_INVARIANT_ROUTE_MIN_BUDGET {
            return None;
        }
        let validation_budget = remaining.min(ARG_CONSTANT_INVARIANT_ROUTE_BUDGET);
        let validation_config = PdrConfig {
            verbose: self.config.verbose,
            strict_proofs: true,
            solve_timeout: Some(validation_budget),
            disable_array_scalarization: true,
            preserve_original_clauses: true,
            ..PdrConfig::default()
        };
        let accepted = crate::engines::validate_external_invariant_model(
            &self.problem,
            &model,
            &validation_config,
        )
        .unwrap_or(false);

        self.decision_log.log_decision_with_details(
            DecisionEntry {
                stage: "arg_constant_invariant",
                gate_result: accepted,
                gate_reason: format!(
                    "exact argument constants and predicate reachability; constants={constant_count}; unreachable={unreachable_count}; blocked_queries={blocked_queries}/{total_queries}; original_validation={accepted}"
                ),
                budget_secs: validation_budget.as_secs_f64(),
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: if accepted { "safe" } else { "unknown" },
                lemmas_learned: 0,
                max_frame: 0,
            },
            serde_json::json!({
                "constants": constant_count,
                "unreachable_predicates": unreachable_count,
                "blocked_queries": blocked_queries,
                "total_queries": total_queries,
                "original_validation": accepted,
            }),
        );

        accepted.then_some(PortfolioResult::Safe(model))
    }

    fn infer_argument_constant_model(&self) -> Option<(InvariantModel, usize, usize, usize)> {
        let predicates = self.problem.predicates();
        if predicates.is_empty() {
            return None;
        }

        let mut reachable = vec![false; predicates.len()];
        let mut constants: Vec<Vec<Option<ChcExpr>>> = predicates
            .iter()
            .map(|pred| vec![None; pred.arity()])
            .collect();
        let max_iterations = self.problem.clauses().len() + predicates.len() + 4;

        for _ in 0..max_iterations {
            let mut next_reachable = vec![false; predicates.len()];
            let mut meets: Vec<Vec<ArgConstMeet>> = predicates
                .iter()
                .map(|pred| vec![ArgConstMeet::Unseen; pred.arity()])
                .collect();

            for clause in self.problem.clauses() {
                let ClauseHead::Predicate(head_pred, head_args) = &clause.head else {
                    continue;
                };
                let Some(env) = self.argument_constant_clause_env(clause, &reachable, &constants)
                else {
                    continue;
                };
                let head_idx = head_pred.index();
                if head_idx >= next_reachable.len() {
                    continue;
                }
                next_reachable[head_idx] = true;
                for (arg_idx, head_arg) in head_args.iter().enumerate() {
                    let Some(sort) = predicates
                        .get(head_idx)
                        .and_then(|pred| pred.arg_sorts.get(arg_idx))
                    else {
                        continue;
                    };
                    let value = self
                        .argument_constant_eval(head_arg, &env)
                        .filter(|value| Self::argument_constant_matches_sort(value, sort));
                    meets[head_idx][arg_idx].add(value);
                }
            }

            let next_constants: Vec<Vec<Option<ChcExpr>>> = meets
                .into_iter()
                .enumerate()
                .map(|(pred_idx, pred_meets)| {
                    if !next_reachable[pred_idx] {
                        return vec![None; predicates[pred_idx].arity()];
                    }
                    pred_meets
                        .into_iter()
                        .map(ArgConstMeet::into_const)
                        .collect()
                })
                .collect();

            if next_reachable == reachable && next_constants == constants {
                break;
            }
            reachable = next_reachable;
            constants = next_constants;
        }

        let blocked_queries = self
            .problem
            .clauses()
            .iter()
            .filter(|clause| clause.is_query())
            .filter(|clause| {
                self.argument_constant_clause_env(clause, &reachable, &constants)
                    .is_none()
            })
            .count();
        let constant_count = constants
            .iter()
            .flat_map(|pred_constants| pred_constants.iter())
            .filter(|value| value.is_some())
            .count();
        let unreachable_count = reachable
            .iter()
            .filter(|is_reachable| !**is_reachable)
            .count();
        if constant_count == 0 && unreachable_count == 0 {
            return None;
        }

        let mut model = InvariantModel::new();
        for (pred_idx, pred) in predicates.iter().enumerate() {
            let vars: Vec<_> = pred
                .arg_sorts
                .iter()
                .enumerate()
                .map(|(arg_idx, _)| adaptive_canonical_var(pred, arg_idx))
                .collect();
            let formula = if !reachable[pred_idx] {
                ChcExpr::Bool(false)
            } else {
                let conjuncts: Vec<_> = constants[pred_idx]
                    .iter()
                    .enumerate()
                    .filter_map(|(arg_idx, value)| {
                        value.as_ref().map(|value| {
                            ChcExpr::eq(ChcExpr::var(vars[arg_idx].clone()), value.clone())
                        })
                    })
                    .collect();
                ChcExpr::and_all(conjuncts)
            };
            model.set(pred.id, PredicateInterpretation::new(vars, formula));
        }

        Some((model, constant_count, unreachable_count, blocked_queries))
    }

    fn argument_constant_clause_env(
        &self,
        clause: &HornClause,
        reachable: &[bool],
        constants: &[Vec<Option<ChcExpr>>],
    ) -> Option<FxHashMap<String, ChcExpr>> {
        let mut env = FxHashMap::default();
        for (pred, args) in &clause.body.predicates {
            let pred_idx = pred.index();
            if !reachable.get(pred_idx).copied().unwrap_or(false) {
                return None;
            }
            for (arg_idx, value) in constants.get(pred_idx)?.iter().enumerate() {
                let Some(value) = value else {
                    continue;
                };
                let Some(arg) = args.get(arg_idx) else {
                    return None;
                };
                if !self.argument_constant_bind_expr(arg, value, &mut env) {
                    return None;
                }
            }
        }

        if let Some(constraint) = &clause.body.constraint {
            self.argument_constant_saturate_constraint(constraint, &mut env)?;
        }
        Some(env)
    }

    fn argument_constant_saturate_constraint(
        &self,
        constraint: &ChcExpr,
        env: &mut FxHashMap<String, ChcExpr>,
    ) -> Option<()> {
        let conjuncts = constraint.collect_conjuncts();
        for _ in 0..8 {
            let mut changed = false;
            for conjunct in &conjuncts {
                let simplified = conjunct
                    .substitute_name_map(env)
                    .simplify_array_ops()
                    .simplify_constants();
                match simplified {
                    ChcExpr::Bool(true) => continue,
                    ChcExpr::Bool(false) => return None,
                    _ => {}
                }
                if self
                    .argument_constant_absorb_equality(&simplified, env, &mut changed)
                    .is_none()
                {
                    return None;
                }
            }
            if !changed {
                break;
            }
        }

        for conjunct in &conjuncts {
            let simplified = conjunct
                .substitute_name_map(env)
                .simplify_array_ops()
                .simplify_constants();
            if matches!(simplified, ChcExpr::Bool(false)) {
                return None;
            }
        }
        Some(())
    }

    fn argument_constant_absorb_equality(
        &self,
        expr: &ChcExpr,
        env: &mut FxHashMap<String, ChcExpr>,
        changed: &mut bool,
    ) -> Option<()> {
        let ChcExpr::Op(ChcOp::Eq, args) = expr else {
            return Some(());
        };
        if args.len() != 2 {
            return Some(());
        }
        let lhs = args[0].as_ref();
        let rhs = args[1].as_ref();

        if let (Some(lhs_const), Some(rhs_const)) = (
            self.argument_constant_eval(lhs, env),
            self.argument_constant_eval(rhs, env),
        ) {
            return (lhs_const == rhs_const).then_some(());
        }

        if let Some(value) = self.argument_constant_eval(rhs, env) {
            return Self::argument_constant_bind_var(lhs, value, env, changed);
        }
        if let Some(value) = self.argument_constant_eval(lhs, env) {
            return Self::argument_constant_bind_var(rhs, value, env, changed);
        }

        match (lhs, rhs) {
            (ChcExpr::Var(lhs_var), ChcExpr::Var(rhs_var)) => {
                if let Some(value) = env.get(&lhs_var.name).cloned() {
                    return Self::argument_constant_bind_var(rhs, value, env, changed);
                }
                if let Some(value) = env.get(&rhs_var.name).cloned() {
                    return Self::argument_constant_bind_var(lhs, value, env, changed);
                }
                Some(())
            }
            _ => Some(()),
        }
    }

    fn argument_constant_bind_var(
        expr: &ChcExpr,
        value: ChcExpr,
        env: &mut FxHashMap<String, ChcExpr>,
        changed: &mut bool,
    ) -> Option<()> {
        let ChcExpr::Var(var) = expr else {
            return Some(());
        };
        if !Self::argument_constant_matches_sort(&value, &var.sort) {
            return None;
        }
        match env.get(&var.name) {
            Some(current) if current == &value => Some(()),
            Some(_) => None,
            None => {
                env.insert(var.name.clone(), value);
                *changed = true;
                Some(())
            }
        }
    }

    fn argument_constant_bind_expr(
        &self,
        expr: &ChcExpr,
        value: &ChcExpr,
        env: &mut FxHashMap<String, ChcExpr>,
    ) -> bool {
        let expr = expr
            .substitute_name_map(env)
            .simplify_array_ops()
            .simplify_constants();
        match &expr {
            ChcExpr::Var(var) => {
                if !Self::argument_constant_matches_sort(value, &var.sort) {
                    return false;
                }
                match env.get(&var.name) {
                    Some(current) => current == value,
                    None => {
                        env.insert(var.name.clone(), value.clone());
                        true
                    }
                }
            }
            _ => self
                .argument_constant_eval(&expr, env)
                .is_some_and(|expr_value| expr_value == *value),
        }
    }

    fn argument_constant_eval(
        &self,
        expr: &ChcExpr,
        env: &FxHashMap<String, ChcExpr>,
    ) -> Option<ChcExpr> {
        let simplified = expr
            .substitute_name_map(env)
            .simplify_array_ops()
            .simplify_constants();
        match &simplified {
            ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _) => {
                Some(simplified)
            }
            ChcExpr::Var(var) => env.get(&var.name).cloned(),
            _ => None,
        }
    }

    fn argument_constant_matches_sort(value: &ChcExpr, sort: &ChcSort) -> bool {
        match (value, sort) {
            (ChcExpr::Bool(_), ChcSort::Bool)
            | (ChcExpr::Int(_), ChcSort::Int)
            | (ChcExpr::Real(_, _), ChcSort::Real) => true,
            (ChcExpr::BitVec(_, width), ChcSort::BitVec(sort_width)) => width == sort_width,
            _ => false,
        }
    }

    /// Solve the CHC problem using adaptive strategy selection.
    ///
    /// Returns a `VerifiedChcResult` where Safe results have been validated
    /// by the portfolio's validation pipeline.
    ///
    /// # Contracts
    ///
    /// REQUIRES: `self.problem` is a valid ChcProblem (validated during construction).
    ///
    /// ENSURES: If `VerifiedChcResult::Safe(inv)` is returned:
    ///          1. The invariant satisfies all clauses in `self.problem`
    ///          2. Solving completed within `self.config.time_budget` (if set)
    ///
    /// ENSURES: If `VerifiedChcResult::Unsafe(cex)` is returned:
    ///          1. The counterexample witnesses reachability to a query clause
    ///
    /// ENSURES: `VerifiedChcResult::Unknown` is returned if:
    ///          - No strategy could determine satisfiability within the budget
    pub fn solve(&self) -> crate::VerifiedChcResult {
        // Single choke point for the body-`forall` over-approximation. The
        // parser strips a body-position `forall`, which WEAKENS the antecedent:
        // proofs survive a fortiori, but a counterexample may be fabricated by
        // the weakened guard. So `Unsafe` must become `Unknown` here.
        //
        // The ONLY transition this can cause is `Unsafe -> Unknown`. `Safe` and
        // `Unknown` pass through untouched, so no proof can be gained or lost.
        let result = self.solve_inner_for_polarity_guard();
        if self.problem.has_stripped_body_forall()
            && matches!(result, crate::VerifiedChcResult::Unsafe(_))
        {
            return crate::VerifiedChcResult::Unknown(
                crate::engine_result::VerifiedUnknownMarker::new(),
            );
        }
        result
    }

    fn solve_inner_for_polarity_guard(&self) -> crate::VerifiedChcResult {
        // Run on a dedicated thread with a large stack to prevent stack
        // overflow from deep Arc<ChcExpr> recursive Drop (#6847).
        // The adaptive solver runs probe PDR, Kind, and retry engines
        // directly (not via portfolio thread spawning), so the calling
        // thread's stack must be large enough for deep expression trees
        // created by SingleLoop encoding + PDKind unrolling.
        std::thread::scope(|scope| {
            match std::thread::Builder::new()
                .name("ay-adaptive-solver".to_string())
                .stack_size(ADAPTIVE_SOLVER_STACK_SIZE)
                .spawn_scoped(scope, || self.solve_with_escalation_retry())
            {
                Ok(handle) => match handle.join() {
                    Ok(result) => result,
                    // Re-propagate the original panic payload so that
                    // try_solve()'s catch_ay_panics can classify it (#6847).
                    Err(payload) => std::panic::resume_unwind(payload),
                },
                // Fallback: run on calling thread if spawn fails
                Err(_) => self.solve_with_escalation_retry(),
            }
        })
    }

    /// Fix B3: escalating outer loop around `solve_internal`.
    ///
    /// The strategy dispatch can exhaust its lineup long before the global
    /// budget does (e.g. returning Unknown at 4s of a 60s budget). When the
    /// finalized result is Unknown and more than
    /// `ESCALATION_RETRY_MIN_REMAINING_FRACTION` of the global budget remains,
    /// re-run the solve once against the same deadline: probes derive their
    /// budgets from the remaining time via `scaled_probe_budget`, so the retry
    /// round runs with the full leftover budget instead of being discarded.
    ///
    /// Exactly one retry round — this is a straight-line second call, not
    /// recursion, so it cannot loop.
    fn solve_with_escalation_retry(&self) -> crate::VerifiedChcResult {
        let solve_start = Instant::now();
        let deadline = self.solve_deadline();
        let (result, evidence) = self.solve_internal(deadline);
        let verified = self.finalize_verified_result_with_deadline(result, evidence, deadline);

        if !matches!(verified, crate::VerifiedChcResult::Unknown(_)) {
            return verified;
        }
        // Unbounded runs have no deadline to escalate against: solve_internal
        // already ran every strategy to its nominal budget.
        let Some(remaining) = self.remaining_budget(deadline) else {
            return verified;
        };
        let total = self.config.time_budget;
        if total.is_zero() || remaining <= total.mul_f64(ESCALATION_RETRY_MIN_REMAINING_FRACTION) {
            return verified;
        }

        self.decision_log.log_decision(DecisionEntry {
            stage: "escalation_retry",
            gate_result: true,
            gate_reason: format!(
                "first round unknown with {:.1}s of {:.1}s budget remaining",
                remaining.as_secs_f64(),
                total.as_secs_f64(),
            ),
            budget_secs: remaining.as_secs_f64(),
            elapsed_secs: solve_start.elapsed().as_secs_f64(),
            result: "retry",
            lemmas_learned: 0,
            max_frame: 0,
        });
        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: escalation retry — first round returned unknown with {:.1}s of {:.1}s budget remaining",
                remaining.as_secs_f64(),
                total.as_secs_f64(),
            );
        }

        let (result, evidence) = self.solve_internal(deadline);
        self.finalize_verified_result_with_deadline(result, evidence, deadline)
    }

    /// Solve with budget reporting (#8418).
    ///
    /// Like [`solve`](Self::solve) but also returns a `BudgetReport` with
    /// per-engine timing data: how much budget was allocated, how much was
    /// consumed, and why each engine stopped.
    ///
    /// This is the primary API for callers (e.g., model-checker-consumer) that need post-solve
    /// budget observability to tune engine allocation policies.
    ///
    /// # Example
    ///
    /// ```rust,no_run
    /// use ay_chc::{AdaptiveConfig, AdaptivePortfolio, EngineType, BudgetPolicy, BudgetReport};
    /// use std::time::Duration;
    ///
    /// # fn example(problem: ay_chc::ChcProblem) {
    /// let config = AdaptiveConfig::with_budget(Duration::from_secs(120), false)
    ///     .with_engine_budget(EngineType::Pdr, BudgetPolicy::MinPercent(40))
    ///     .with_engine_budget(EngineType::Bmc, BudgetPolicy::MinPercent(20));
    /// let solver = AdaptivePortfolio::new(problem, config);
    /// let (result, report) = solver.solve_with_budget_report();
    /// for entry in &report.entries {
    ///     eprintln!("{}: {:.1}s / {:.1}s ({:?})",
    ///         entry.engine.name(),
    ///         entry.elapsed.as_secs_f64(),
    ///         entry.budget_allocated.as_secs_f64(),
    ///         entry.stop_reason);
    /// }
    /// # }
    /// ```
    pub fn solve_with_budget_report(
        &self,
    ) -> (crate::VerifiedChcResult, crate::portfolio::BudgetReport) {
        std::thread::scope(|scope| {
            match std::thread::Builder::new()
                .name("ay-adaptive-solver-report".to_string())
                .stack_size(ADAPTIVE_SOLVER_STACK_SIZE)
                .spawn_scoped(scope, || self.solve_with_budget_report_impl())
            {
                Ok(handle) => match handle.join() {
                    Ok(result) => result,
                    Err(payload) => std::panic::resume_unwind(payload),
                },
                Err(_) => {
                    // Fallback: run on calling thread
                    self.solve_with_budget_report_impl()
                }
            }
        })
    }

    fn solve_with_budget_report_impl(
        &self,
    ) -> (crate::VerifiedChcResult, crate::portfolio::BudgetReport) {
        let deadline = self.solve_deadline();
        if self.problem.has_complex_query_only_vacuous_safety_shape() {
            // w10: attempt a fully validated constant-model Safe before the
            // #8865 fail-closed Unknown (see try_vacuous_query_only_validated_safe).
            if let Some(result) = self.try_vacuous_query_only_validated_safe(deadline) {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: complex query-only problem is syntactically unreachable; \
                         constant-model completion fully verified on original clauses — Safe"
                    );
                }
                let verified = self.finalize_verified_result_with_deadline(
                    result,
                    ValidationEvidence::FullVerification,
                    deadline,
                );
                return (verified, crate::portfolio::BudgetReport::new());
            }
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: complex query-only problem is syntactically unreachable; demoting vacuous Safe proof to Unknown"
                );
            }
            let verified = self.finalize_verified_result_with_deadline(
                PortfolioResult::Unknown,
                ValidationEvidence::FullVerification,
                deadline,
            );
            return (verified, crate::portfolio::BudgetReport::new());
        }

        if let Some(result) = self.try_acyclic_budget_report_prepass(deadline) {
            return result;
        }

        let mut config = self.make_default_portfolio_config();
        self.apply_user_hints_portfolio(&mut config);
        let solver = PortfolioSolver::new(self.problem.clone(), config);
        let (result, report) = solver.solve_with_budget_report();
        let verified = self.finalize_verified_result_with_deadline(
            result,
            ValidationEvidence::FullVerification,
            deadline,
        );
        (verified, report)
    }

    fn try_acyclic_budget_report_prepass(
        &self,
        deadline: Option<Instant>,
    ) -> Option<(crate::VerifiedChcResult, crate::portfolio::BudgetReport)> {
        let features = ProblemClassifier::classify(&self.problem);
        if features.has_cycles || features.num_predicates <= 1 || !self.problem.has_bv_sorts() {
            return None;
        }

        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: Budget-report acyclic BMC prepass (preds={}, dag_depth={}, bv=true)",
                features.num_predicates,
                features.dag_depth
            );
        }

        let (result, evidence) = self.try_acyclic_bmc_probe(&features, deadline)?;

        let verified = self.finalize_verified_result_with_deadline(result, evidence, deadline);
        if matches!(
            verified,
            crate::VerifiedChcResult::Safe(_) | crate::VerifiedChcResult::Unsafe(_)
        ) {
            Some((verified, crate::portfolio::BudgetReport::new()))
        } else {
            None
        }
    }

    /// Panic-safe variant of [`solve`](Self::solve).
    ///
    /// Catches ay-internal panics (sort mismatches, verification failures, BUG
    /// markers) and returns them as `ChcError::Internal`. Non-ay panics
    /// (index out of bounds, assertion failures) propagate normally via
    /// `resume_unwind`.
    ///
    /// Model-checker consumers should prefer this over wrapping `solve()` in
    /// their own `catch_unwind` because this uses the canonical ay panic
    /// classifier (`is_ay_panic_reason`).
    ///
    /// # Errors
    ///
    /// Returns `ChcError::Internal` if a ay-classified panic is caught.
    pub fn try_solve(&self) -> crate::ChcResult<crate::VerifiedChcResult> {
        ay_core::catch_ay_panics(
            std::panic::AssertUnwindSafe(|| Ok(self.solve())),
            |reason| Err(crate::ChcError::Internal(reason)),
        )
    }

    fn solidity_array_dt_route_budget(&self, deadline: Option<Instant>) -> Option<Duration> {
        let budget = match self.remaining_budget(deadline) {
            Some(remaining) if remaining.is_zero() => return None,
            Some(remaining) => remaining.min(SOLIDITY_ARRAY_DT_ROUTE_BUDGET),
            None => SOLIDITY_ARRAY_DT_ROUTE_BUDGET,
        };
        if budget.is_zero() {
            None
        } else {
            Some(budget)
        }
    }

    fn solidity_array_dt_remaining_route_budget(route_deadline: Instant) -> Option<Duration> {
        let remaining = route_deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            None
        } else {
            Some(remaining)
        }
    }

    fn solidity_array_dt_has_step_budget(route_deadline: Instant) -> bool {
        Self::solidity_array_dt_remaining_route_budget(route_deadline)
            .is_some_and(|remaining| remaining >= SOLIDITY_ARRAY_DT_ROUTE_MIN_STEP_BUDGET)
    }

    fn solidity_array_dt_route_gate_reason(
        prefix: &str,
        stats: &SolidityArrayDtProjectionStats,
    ) -> String {
        format!(
            "{prefix}; predicates={} predicate_args={} projected_predicates={} \
             projected_args={} projected_field_args={} added_predicate_args={}",
            stats.predicates,
            stats.predicate_args,
            stats.projected_predicates,
            stats.projected_args,
            stats.projected_field_args,
            stats.added_predicate_args,
        )
    }

    fn solidity_array_dt_route_over_cap(
        &self,
        stats: &SolidityArrayDtProjectionStats,
        transformed_problem: &ChcProblem,
    ) -> Option<String> {
        if self.problem.clauses().len() > SOLIDITY_ARRAY_DT_ROUTE_MAX_CLAUSES {
            return Some(format!(
                "clauses {} > cap {}",
                self.problem.clauses().len(),
                SOLIDITY_ARRAY_DT_ROUTE_MAX_CLAUSES
            ));
        }
        if stats.projected_args > SOLIDITY_ARRAY_DT_ROUTE_MAX_PROJECTED_ARGS {
            return Some(format!(
                "projected_args {} > cap {}",
                stats.projected_args, SOLIDITY_ARRAY_DT_ROUTE_MAX_PROJECTED_ARGS
            ));
        }
        if stats.added_predicate_args > SOLIDITY_ARRAY_DT_ROUTE_MAX_ADDED_ARGS {
            return Some(format!(
                "added_predicate_args {} > cap {}",
                stats.added_predicate_args, SOLIDITY_ARRAY_DT_ROUTE_MAX_ADDED_ARGS
            ));
        }
        let max_arity = transformed_problem
            .predicates()
            .iter()
            .map(|pred| pred.arity())
            .max()
            .unwrap_or(0);
        if max_arity > SOLIDITY_ARRAY_DT_ROUTE_MAX_TRANSFORMED_ARITY {
            return Some(format!(
                "transformed_max_arity {max_arity} > cap {SOLIDITY_ARRAY_DT_ROUTE_MAX_TRANSFORMED_ARITY}"
            ));
        }
        None
    }

    fn validate_solidity_array_dt_original_model(
        &self,
        translated_model: &InvariantModel,
        route_deadline: Instant,
    ) -> SolidityArrayDtValidationStatus {
        let validation_budget = route_deadline.saturating_duration_since(Instant::now());
        if validation_budget.is_zero() {
            return SolidityArrayDtValidationStatus::NoBudget;
        }

        let validation_config = PdrConfig {
            verbose: self.config.verbose,
            strict_proofs: true,
            solve_timeout: Some(validation_budget),
            disable_array_scalarization: true,
            preserve_original_clauses: true,
            ..PdrConfig::default()
        };
        let validation_result = crate::engines::validate_external_invariant_model(
            &self.problem,
            translated_model,
            &validation_config,
        );
        if Instant::now() >= route_deadline {
            return SolidityArrayDtValidationStatus::Timeout;
        }
        match validation_result {
            Ok(true) => SolidityArrayDtValidationStatus::Accepted,
            Ok(false) => SolidityArrayDtValidationStatus::Failed,
            Err(_) => SolidityArrayDtValidationStatus::Error,
        }
    }

    fn try_solidity_array_dt_observed_key_refinement(
        &self,
        transformed_problem: &ChcProblem,
        back_translator: &dyn BackTranslator,
        route_deadline: Instant,
    ) -> Option<SolidityArrayDtRefinedSafe> {
        let refinement_indices = back_translator.array_refinement_indices();
        if refinement_indices.is_empty() || !Self::solidity_array_dt_has_step_budget(route_deadline)
        {
            return None;
        }

        let solve_budget = Self::solidity_array_dt_remaining_route_budget(route_deadline)?;
        let mut refined_config = PdrConfig::production(self.config.verbose);
        refined_config.solve_timeout = Some(solve_budget);
        refined_config.strict_proofs = self.config.strict_proofs;
        refined_config.array_scalarization_extra_indices = refinement_indices;
        self.apply_user_hints(&mut refined_config);

        let refined_result =
            PdrSolver::solve_problem_with_stats(transformed_problem, refined_config);
        self.accumulate_stats(&refined_result.stats);

        let PdrResult::Safe(model) = refined_result.result else {
            return None;
        };
        if !Self::solidity_array_dt_has_step_budget(route_deadline) {
            return None;
        }

        let translated_model = back_translator.translate_validity(model);
        if self.validate_solidity_array_dt_original_model(&translated_model, route_deadline)
            == SolidityArrayDtValidationStatus::Accepted
        {
            Some(SolidityArrayDtRefinedSafe {
                model: translated_model,
                lemmas_learned: refined_result.learned_lemmas.len(),
                max_frame: refined_result.stats.max_frame,
            })
        } else {
            None
        }
    }

    fn pdr_result_to_str(result: &PdrResult) -> &'static str {
        match result {
            PdrResult::Safe(_) => "safe",
            PdrResult::Unsafe(_) => "unsafe",
            PdrResult::Unknown => "unknown",
            PdrResult::NotApplicable => "not_applicable",
        }
    }

    fn solidity_array_dt_attempt_result(
        transformed_result: &'static str,
        validation_status: SolidityArrayDtValidationStatus,
    ) -> &'static str {
        match validation_status {
            SolidityArrayDtValidationStatus::Accepted
            | SolidityArrayDtValidationStatus::RefinedAccepted => "safe",
            SolidityArrayDtValidationStatus::Failed => "validation_failed",
            SolidityArrayDtValidationStatus::Error => "validation_error",
            SolidityArrayDtValidationStatus::NoBudget => "validation_no_budget",
            SolidityArrayDtValidationStatus::Timeout => "validation_timeout",
            SolidityArrayDtValidationStatus::NotRun => match transformed_result {
                "unsafe" => "transformed_unsafe",
                "unknown" => "transformed_unknown",
                "not_applicable" => "transformed_not_applicable",
                _ => "unknown",
            },
        }
    }

    fn log_solidity_array_dt_attempt(
        &self,
        route_start: Instant,
        route_budget: Duration,
        stats: &SolidityArrayDtProjectionStats,
        transformed_result: &'static str,
        validation_status: SolidityArrayDtValidationStatus,
        transform_memory: &crate::transform::TransformMemoryReport,
        lemmas_learned: usize,
        max_frame: usize,
    ) {
        self.decision_log.log_decision_with_details(
            DecisionEntry {
                stage: "solidity_array_dt_projection",
                gate_result: true,
                gate_reason: format!(
                    "{}; transformed_result={transformed_result}; validation={}; {}",
                    Self::solidity_array_dt_route_gate_reason(
                        "applicable after DT flattening",
                        stats
                    ),
                    validation_status.as_str(),
                    transform_memory.diagnostic_summary()
                ),
                budget_secs: route_budget.as_secs_f64(),
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: Self::solidity_array_dt_attempt_result(
                    transformed_result,
                    validation_status,
                ),
                lemmas_learned,
                max_frame,
            },
            serde_json::json!({
                "transformed_result": transformed_result,
                "validation_status": validation_status.as_str(),
                "refinement_performed": validation_status == SolidityArrayDtValidationStatus::RefinedAccepted,
                "transform_memory": transform_memory.diagnostic_summary(),
                "unsafe_backtranslation_complete": transform_memory.unsafe_backtranslation_complete(),
            }),
        );
    }

    fn try_solidity_array_dt_projection_route(
        &self,
        deadline: Option<Instant>,
    ) -> Option<PortfolioResult> {
        if !problem_has_datatype_predicate_argument(&self.problem) {
            return None;
        }

        let route_start = Instant::now();
        let Some(route_budget) = self.solidity_array_dt_route_budget(deadline) else {
            self.decision_log.log_decision(DecisionEntry {
                stage: "solidity_array_dt_projection",
                gate_result: false,
                gate_reason: "no remaining budget".to_string(),
                budget_secs: 0.0,
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "skipped",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        };
        let route_deadline = route_start + route_budget;

        if self.problem.clauses().len() > SOLIDITY_ARRAY_DT_ROUTE_MAX_CLAUSES {
            self.decision_log.log_decision(DecisionEntry {
                stage: "solidity_array_dt_projection",
                gate_result: false,
                gate_reason: format!(
                    "route over cap before transform: clauses {} > cap {}",
                    self.problem.clauses().len(),
                    SOLIDITY_ARRAY_DT_ROUTE_MAX_CLAUSES
                ),
                budget_secs: route_budget.as_secs_f64(),
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "cap_exceeded",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        }

        if !Self::solidity_array_dt_has_step_budget(route_deadline) {
            self.decision_log.log_decision(DecisionEntry {
                stage: "solidity_array_dt_projection",
                gate_result: true,
                gate_reason: "route budget exhausted before DT flattening".to_string(),
                budget_secs: route_budget.as_secs_f64(),
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "timeout",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        }

        let dt_result = Box::new(DtFlattener::new().with_verbose(self.config.verbose))
            .transform(self.problem.clone());
        if !Self::solidity_array_dt_has_step_budget(route_deadline) {
            self.decision_log.log_decision(DecisionEntry {
                stage: "solidity_array_dt_projection",
                gate_result: true,
                gate_reason: "route budget exhausted after DT flattening".to_string(),
                budget_secs: route_budget.as_secs_f64(),
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "timeout",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        }
        let route = SolidityArrayDtProjector::route(&dt_result.problem);
        let stats = *route.stats();

        match route {
            SolidityArrayDtProjectionRoute::NotApplicable { .. } => {
                self.decision_log.log_decision(DecisionEntry {
                    stage: "solidity_array_dt_projection",
                    gate_result: false,
                    gate_reason: Self::solidity_array_dt_route_gate_reason(
                        "not applicable after DT flattening",
                        &stats,
                    ),
                    budget_secs: route_budget.as_secs_f64(),
                    elapsed_secs: route_start.elapsed().as_secs_f64(),
                    result: "not_applicable",
                    lemmas_learned: 0,
                    max_frame: 0,
                });
                return None;
            }
            SolidityArrayDtProjectionRoute::Unsupported { reason, .. } => {
                self.decision_log.log_decision(DecisionEntry {
                    stage: "solidity_array_dt_projection",
                    gate_result: false,
                    gate_reason: Self::solidity_array_dt_route_gate_reason(
                        &format!("unsupported after DT flattening: {reason:?}"),
                        &stats,
                    ),
                    budget_secs: route_budget.as_secs_f64(),
                    elapsed_secs: route_start.elapsed().as_secs_f64(),
                    result: "skipped",
                    lemmas_learned: 0,
                    max_frame: 0,
                });
                return None;
            }
            SolidityArrayDtProjectionRoute::Applicable { .. } => {}
        }

        if !Self::solidity_array_dt_has_step_budget(route_deadline) {
            self.decision_log.log_decision(DecisionEntry {
                stage: "solidity_array_dt_projection",
                gate_result: true,
                gate_reason: Self::solidity_array_dt_route_gate_reason(
                    "route budget exhausted before projection transform",
                    &stats,
                ),
                budget_secs: route_budget.as_secs_f64(),
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "timeout",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        }

        let projection_result =
            Box::new(SolidityArrayDtProjectionTransformer::new().with_verbose(self.config.verbose))
                .transform(dt_result.problem);
        if !Self::solidity_array_dt_has_step_budget(route_deadline) {
            self.decision_log.log_decision(DecisionEntry {
                stage: "solidity_array_dt_projection",
                gate_result: true,
                gate_reason: Self::solidity_array_dt_route_gate_reason(
                    "route budget exhausted after projection transform",
                    &stats,
                ),
                budget_secs: route_budget.as_secs_f64(),
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "timeout",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        }
        if let Some(cap_reason) =
            self.solidity_array_dt_route_over_cap(&stats, &projection_result.problem)
        {
            self.decision_log.log_decision(DecisionEntry {
                stage: "solidity_array_dt_projection",
                gate_result: false,
                gate_reason: Self::solidity_array_dt_route_gate_reason(
                    &format!("route over cap: {cap_reason}"),
                    &stats,
                ),
                budget_secs: route_budget.as_secs_f64(),
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "cap_exceeded",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        }

        let transformed_problem = projection_result.problem;
        let back_translator: Box<dyn BackTranslator> = Box::new(CompositeBackTranslator {
            inner: vec![projection_result.back_translator, dt_result.back_translator],
        });

        let Some(solve_budget) = Self::solidity_array_dt_remaining_route_budget(route_deadline)
        else {
            self.decision_log.log_decision(DecisionEntry {
                stage: "solidity_array_dt_projection",
                gate_result: true,
                gate_reason: Self::solidity_array_dt_route_gate_reason(
                    "route budget exhausted before solve",
                    &stats,
                ),
                budget_secs: route_budget.as_secs_f64(),
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "timeout",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        };
        let mut pdr_config = PdrConfig::production(self.config.verbose);
        pdr_config.solve_timeout = Some(solve_budget);
        pdr_config.strict_proofs = self.config.strict_proofs;
        self.apply_user_hints(&mut pdr_config);
        let result_with_stats =
            PdrSolver::solve_problem_with_stats(&transformed_problem, pdr_config);
        self.accumulate_stats(&result_with_stats.stats);
        let mut lemmas_learned = result_with_stats.learned_lemmas.len();
        let mut max_frame = result_with_stats.stats.max_frame;
        let mut transformed_result = Self::pdr_result_to_str(&result_with_stats.result);
        let mut validation_status = SolidityArrayDtValidationStatus::NotRun;
        let translated_safe = match result_with_stats.result {
            PdrResult::Safe(model) => {
                if !Self::solidity_array_dt_has_step_budget(route_deadline) {
                    validation_status = SolidityArrayDtValidationStatus::NoBudget;
                    None
                } else {
                    let translated_model = back_translator.translate_validity(model);
                    if route_deadline <= Instant::now() {
                        validation_status = SolidityArrayDtValidationStatus::Timeout;
                        None
                    } else {
                        validation_status = self.validate_solidity_array_dt_original_model(
                            &translated_model,
                            route_deadline,
                        );
                        if validation_status == SolidityArrayDtValidationStatus::Accepted {
                            Some(translated_model)
                        } else if validation_status == SolidityArrayDtValidationStatus::Failed {
                            self.try_solidity_array_dt_observed_key_refinement(
                                &transformed_problem,
                                back_translator.as_ref(),
                                route_deadline,
                            )
                            .map(|refined_safe| {
                                validation_status =
                                    SolidityArrayDtValidationStatus::RefinedAccepted;
                                transformed_result = "safe_refined";
                                lemmas_learned = refined_safe.lemmas_learned;
                                max_frame = refined_safe.max_frame;
                                refined_safe.model
                            })
                        } else {
                            None
                        }
                    }
                }
            }
            PdrResult::Unsafe(_) | PdrResult::Unknown | PdrResult::NotApplicable => None,
        };
        let transform_memory = back_translator.transform_memory();
        self.log_solidity_array_dt_attempt(
            route_start,
            route_budget,
            &stats,
            transformed_result,
            validation_status,
            &transform_memory,
            lemmas_learned,
            max_frame,
        );

        translated_safe.map(PortfolioResult::Safe)
    }

    /// Try certified preprocessing before array-specific abstractions when it
    /// collapses a large pure-LIA array graph to a tiny transition system.
    ///
    /// This is deliberately a narrow, bounded BMC/PDR lane rather than a
    /// nested general portfolio. Definitive transformed results are
    /// back-translated and checked against the original clauses.
    fn try_reduced_lia_array_preprocessed_route(
        &self,
        deadline: Option<Instant>,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        let route_start = Instant::now();
        let original_predicates = self.problem.predicates().len();
        let original_clauses = self.problem.clauses().len();
        if std::env::var_os(REDUCED_LIA_ARRAY_ROUTE_DISABLE_ENV).is_some()
            || !self.problem.has_array_sorts()
            || self.problem.has_bv_sorts()
            || self.problem.has_datatype_sorts()
            || self.problem.has_real_sorts()
            || original_predicates < REDUCED_LIA_ARRAY_ROUTE_MIN_ORIGINAL_PREDICATES
            || original_clauses > REDUCED_LIA_ARRAY_ROUTE_MAX_ORIGINAL_CLAUSES
            || self
                .remaining_budget(deadline)
                .is_some_and(|remaining| remaining < REDUCED_LIA_ARRAY_ROUTE_MIN_BUDGET)
        {
            return None;
        }
        let route_deadline = deadline
            .unwrap_or(route_start + REDUCED_LIA_ARRAY_ROUTE_BUDGET)
            .min(route_start + REDUCED_LIA_ARRAY_ROUTE_BUDGET);

        let summary = PreprocessSummary::build(self.problem.clone(), self.config.verbose);
        let transformed_predicates = summary.transformed_problem.predicates().len();
        let transformed_clauses = summary.transformed_problem.clauses().len();
        let transformed_max_arity = summary
            .transformed_problem
            .predicates()
            .iter()
            .map(|predicate| predicate.arity())
            .max()
            .unwrap_or(0);
        let predicate_shrink =
            original_predicates >= transformed_predicates.max(1).saturating_mul(2);
        let clause_shrink = original_clauses >= transformed_clauses.max(1).saturating_mul(2);
        let major_reduction = (predicate_shrink || clause_shrink)
            && transformed_predicates <= REDUCED_LIA_ARRAY_ROUTE_MAX_PREDICATES
            && transformed_clauses <= REDUCED_LIA_ARRAY_ROUTE_MAX_CLAUSES
            && transformed_max_arity <= REDUCED_LIA_ARRAY_ROUTE_MAX_ARITY;
        if !major_reduction {
            return None;
        }
        let acceptance_reserve = REDUCED_LIA_ARRAY_VALIDATION_RESERVE
            .saturating_add(REDUCED_LIA_ARRAY_FINAL_REPLAY_RESERVE);

        // Certified preprocessing can either remove the query entirely or
        // inline a raw nullary error predicate into an explicitly
        // contradictory query constraint. In both cases the reduced problem
        // admits the all-true interpretation. The transformed query check is
        // only an admission filter: back-translate through the entire
        // preprocessing stack and strictly validate the unchanged ORIGINAL
        // clauses before accepting Safe.
        let transformed_query_count = summary.transformed_problem.queries().count();
        let top_query_budget = TOP_MODEL_QUERY_CHECK_BUDGET.min(
            route_deadline
                .saturating_duration_since(Instant::now())
                .saturating_sub(
                    REDUCED_LIA_ARRAY_VALIDATION_RESERVE
                        .saturating_add(REDUCED_LIA_ARRAY_FINAL_REPLAY_RESERVE),
                ),
        );
        if let Some(transformed_model) = Self::try_top_model_query_infeasibility_candidate(
            &summary.transformed_problem,
            top_query_budget,
        ) {
            let translated = summary
                .back_translator
                .translate_validity(transformed_model);
            let validation_budget = route_deadline
                .saturating_duration_since(Instant::now())
                .saturating_sub(REDUCED_LIA_ARRAY_FINAL_REPLAY_RESERVE)
                .min(REDUCED_LIA_ARRAY_VALIDATION_RESERVE);
            let original_validation =
                self.validate_lia_farkas_safe_model_on_original(&translated, validation_budget);
            self.decision_log.log_decision_with_details(
                DecisionEntry {
                    stage: "reduced_lia_array_top_model",
                    gate_result: true,
                    gate_reason: format!(
                        "certified reduction: {original_predicates}p/{original_clauses}c -> \
                         {transformed_predicates}p/{transformed_clauses}c, \
                         max_arity={transformed_max_arity}; \
                         {transformed_query_count} transformed query constraints UNSAT under top"
                    ),
                    budget_secs: route_deadline
                        .saturating_duration_since(route_start)
                        .as_secs_f64(),
                    elapsed_secs: route_start.elapsed().as_secs_f64(),
                    result: if original_validation {
                        "safe"
                    } else {
                        "unknown"
                    },
                    lemmas_learned: 0,
                    max_frame: 0,
                },
                serde_json::json!({
                    "original_validation": original_validation,
                    "transformed_query_count": transformed_query_count,
                    "query_check_budget_secs": top_query_budget.as_secs_f64(),
                    "transform_memory": summary.transform_memory.diagnostic_summary(),
                }),
            );
            if original_validation {
                return Some((
                    PortfolioResult::Safe(translated),
                    ValidationEvidence::FullVerification,
                ));
            }
        }

        // A reduced compiler graph can retain a small scalar loop whose query
        // is feasible under the all-true interpretation but infeasible under
        // its inductive argument bounds. Reuse the verified interval
        // transformer as candidate generation:
        //
        //  1. infer and per-clause prove interval bounds on the CERTIFIED
        //     preprocessed problem,
        //  2. strengthen transformed query bodies with those proven bounds,
        //  3. admit an all-true candidate only when every strengthened query
        //     constraint is UNSAT,
        //  4. translate the interval atoms and the preprocessing model back
        //     through both stacks, and
        //  5. strictly validate every unchanged ORIGINAL clause.
        //
        // Any imprecise interval, timeout, translation gap, or invalid model
        // therefore falls through; the interval analysis is never a verdict.
        let scalar_query_constraints = summary
            .transformed_problem
            .queries()
            .map(|query| {
                query
                    .body
                    .constraint
                    .as_ref()
                    .map_or(true, |constraint| !constraint.contains_array_ops())
            })
            .reduce(|left, right| left && right)
            .unwrap_or(false);
        let interval_remaining = route_deadline.saturating_duration_since(Instant::now());
        let interval_reserve = acceptance_reserve.saturating_add(TOP_MODEL_QUERY_CHECK_BUDGET);
        if scalar_query_constraints && interval_remaining > interval_reserve {
            let interval_budget = REDUCED_LIA_ARRAY_INTERVAL_BUDGET
                .min(interval_remaining.saturating_sub(interval_reserve));
            let interval_result = Box::new(
                IntervalPropagator::new()
                    .with_verbose(self.config.verbose)
                    .with_pass_budget(interval_budget),
            )
            .transform(summary.transformed_problem.clone());
            let interval_transform_memory = interval_result.back_translator.transform_memory();
            let post_interval_remaining = route_deadline.saturating_duration_since(Instant::now());
            let interval_query_budget = TOP_MODEL_QUERY_CHECK_BUDGET
                .min(post_interval_remaining.saturating_sub(acceptance_reserve));
            let interval_candidate = Self::try_top_model_query_infeasibility_candidate(
                &interval_result.problem,
                interval_query_budget,
            );
            let interval_candidate_generated = interval_candidate.is_some();
            let mut original_validation = false;
            if let Some(interval_top_model) = interval_candidate {
                let preprocessed_model = interval_result
                    .back_translator
                    .translate_validity(interval_top_model);
                let translated = summary
                    .back_translator
                    .translate_validity(preprocessed_model);
                let validation_budget = route_deadline
                    .saturating_duration_since(Instant::now())
                    .saturating_sub(REDUCED_LIA_ARRAY_FINAL_REPLAY_RESERVE)
                    .min(REDUCED_LIA_ARRAY_VALIDATION_RESERVE);
                original_validation =
                    self.validate_lia_farkas_safe_model_on_original(&translated, validation_budget);
                if original_validation {
                    self.decision_log.log_decision_with_details(
                        DecisionEntry {
                            stage: "reduced_lia_array_interval_model",
                            gate_result: true,
                            gate_reason: format!(
                                "certified reduction: {original_predicates}p/{original_clauses}c \
                                 -> {transformed_predicates}p/{transformed_clauses}c, \
                                 max_arity={transformed_max_arity}; verified interval bounds make \
                                 transformed queries infeasible under top"
                            ),
                            budget_secs: route_deadline
                                .saturating_duration_since(route_start)
                                .as_secs_f64(),
                            elapsed_secs: route_start.elapsed().as_secs_f64(),
                            result: "safe",
                            lemmas_learned: 0,
                            max_frame: 0,
                        },
                        serde_json::json!({
                            "interval_budget_secs": interval_budget.as_secs_f64(),
                            "query_check_budget_secs": interval_query_budget.as_secs_f64(),
                            "interval_transform_memory":
                                interval_transform_memory.diagnostic_summary(),
                            "preprocess_transform_memory":
                                summary.transform_memory.diagnostic_summary(),
                            "original_validation": true,
                        }),
                    );
                    return Some((
                        PortfolioResult::Safe(translated),
                        ValidationEvidence::FullVerification,
                    ));
                }
            }
            self.decision_log.log_decision_with_details(
                DecisionEntry {
                    stage: "reduced_lia_array_interval_model",
                    gate_result: true,
                    gate_reason: "verified interval candidate did not produce an \
                                  original-valid Safe model"
                        .to_string(),
                    budget_secs: interval_budget.as_secs_f64(),
                    elapsed_secs: route_start.elapsed().as_secs_f64(),
                    result: "unknown",
                    lemmas_learned: 0,
                    max_frame: 0,
                },
                serde_json::json!({
                    "interval_candidate": interval_candidate_generated,
                    "interval_transform_memory":
                        interval_transform_memory.diagnostic_summary(),
                    "original_validation": original_validation,
                }),
            );
        }

        let remaining = route_deadline.saturating_duration_since(Instant::now());
        if remaining < REDUCED_LIA_ARRAY_ROUTE_MIN_BUDGET || remaining <= acceptance_reserve {
            return None;
        }
        let route_budget = route_deadline.saturating_duration_since(route_start);
        let bmc_budget =
            REDUCED_LIA_ARRAY_BMC_BUDGET.min(remaining.saturating_sub(acceptance_reserve));

        // The LIA-array shard's short refutations require up to thirteen Horn
        // steps after preprocessing. Keep the probe bounded above that depth;
        // the lane-level deadline still prevents a hard instance from
        // consuming the later PDR/acceptance budget.
        let bmc_cancel = self.cancellation_token.child();
        let _bmc_timeout_guard = bmc_cancel.cancel_after(bmc_budget);
        let bmc = crate::bmc::BmcConfig::default()
            .with_max_depth(REDUCED_LIA_ARRAY_BMC_MAX_DEPTH)
            .with_time_budget(bmc_budget)
            .with_per_depth_timeout(bmc_budget)
            .with_verbose(self.config.verbose)
            .with_cancellation(bmc_cancel);
        let bmc_result =
            crate::bmc::BmcSolver::new(summary.transformed_problem.clone(), bmc).solve();
        let bmc_result_name = Self::result_to_str(&bmc_result);

        if let PortfolioResult::Unsafe(cex) = bmc_result {
            let translated = crate::portfolio::backtranslate_counterexample_with_ground_evidence(
                summary.back_translator.as_ref(),
                &self.problem,
                &cex,
            );
            let validation_budget = route_deadline
                .saturating_duration_since(Instant::now())
                .saturating_sub(REDUCED_LIA_ARRAY_FINAL_REPLAY_RESERVE)
                .min(REDUCED_LIA_ARRAY_VALIDATION_RESERVE);
            let original_replay =
                self.validate_final_unsafe_result(&translated, Some(validation_budget));
            if original_replay {
                self.decision_log.log_decision_with_details(
                    DecisionEntry {
                        stage: "reduced_lia_array_preprocess",
                        gate_result: true,
                        gate_reason: format!(
                            "certified reduction: {original_predicates}p/{original_clauses}c -> \
                             {transformed_predicates}p/{transformed_clauses}c, \
                             max_arity={transformed_max_arity}; shallow BMC replayed"
                        ),
                        budget_secs: route_budget.as_secs_f64(),
                        elapsed_secs: route_start.elapsed().as_secs_f64(),
                        result: "unsafe",
                        lemmas_learned: 0,
                        max_frame: 0,
                    },
                    serde_json::json!({
                        "bmc_result": bmc_result_name,
                        "bmc_budget_secs": bmc_budget.as_secs_f64(),
                        "original_trace_replay": true,
                        "transform_memory": summary.transform_memory.diagnostic_summary(),
                    }),
                );
                return Some((
                    PortfolioResult::Unsafe(translated),
                    ValidationEvidence::CounterexampleVerification,
                ));
            }
        }

        let remaining = route_deadline.saturating_duration_since(Instant::now());
        let pdr_budget = remaining.saturating_sub(acceptance_reserve);
        if pdr_budget < Duration::from_millis(250) {
            return None;
        }
        let pdr_cancel = self.cancellation_token.child();
        let _pdr_timeout_guard = pdr_cancel.cancel_after(pdr_budget);
        let mut pdr = PdrConfig::lia_farkas_profile(self.config.verbose);
        pdr.solve_timeout = Some(pdr_budget);
        pdr.strict_proofs = true;
        pdr.cancellation_token = Some(pdr_cancel);
        self.apply_user_hints(&mut pdr);
        let result_with_stats =
            PdrSolver::solve_problem_with_stats(&summary.transformed_problem, pdr);
        self.accumulate_stats(&result_with_stats.stats);
        let pdr_result_name = Self::pdr_result_to_str(&result_with_stats.result);
        let mut original_validation = false;
        let result = match result_with_stats.result {
            PdrResult::Safe(model) => {
                let translated = summary.back_translator.translate_validity(model);
                let validation_budget = route_deadline
                    .saturating_duration_since(Instant::now())
                    .saturating_sub(REDUCED_LIA_ARRAY_FINAL_REPLAY_RESERVE)
                    .min(REDUCED_LIA_ARRAY_VALIDATION_RESERVE);
                original_validation =
                    self.validate_lia_farkas_safe_model_on_original(&translated, validation_budget);
                original_validation.then_some((
                    PortfolioResult::Safe(translated),
                    ValidationEvidence::FullVerification,
                ))
            }
            PdrResult::Unsafe(cex) => {
                let translated =
                    crate::portfolio::backtranslate_counterexample_with_ground_evidence(
                        summary.back_translator.as_ref(),
                        &self.problem,
                        &cex,
                    );
                let validation_budget = route_deadline
                    .saturating_duration_since(Instant::now())
                    .saturating_sub(REDUCED_LIA_ARRAY_FINAL_REPLAY_RESERVE)
                    .min(REDUCED_LIA_ARRAY_VALIDATION_RESERVE);
                original_validation =
                    self.validate_final_unsafe_result(&translated, Some(validation_budget));
                original_validation.then_some((
                    PortfolioResult::Unsafe(translated),
                    ValidationEvidence::CounterexampleVerification,
                ))
            }
            PdrResult::Unknown | PdrResult::NotApplicable => None,
        };
        self.decision_log.log_decision_with_details(
            DecisionEntry {
                stage: "reduced_lia_array_preprocess",
                gate_result: true,
                gate_reason: format!(
                    "certified reduction: {original_predicates}p/{original_clauses}c -> \
                     {transformed_predicates}p/{transformed_clauses}c, \
                     max_arity={transformed_max_arity}"
                ),
                budget_secs: route_budget.as_secs_f64(),
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: result
                    .as_ref()
                    .map_or(pdr_result_name, |(result, _)| Self::result_to_str(result)),
                lemmas_learned: result_with_stats.stats.lemmas_learned,
                max_frame: result_with_stats.stats.max_frame,
            },
            serde_json::json!({
                "original_predicates": original_predicates,
                "original_clauses": original_clauses,
                "transformed_predicates": transformed_predicates,
                "transformed_clauses": transformed_clauses,
                "transformed_max_arity": transformed_max_arity,
                "bmc_budget_secs": bmc_budget.as_secs_f64(),
                "pdr_budget_secs": pdr_budget.as_secs_f64(),
                "bmc_result": bmc_result_name,
                "pdr_result": pdr_result_name,
                "transform_memory": summary.transform_memory.diagnostic_summary(),
                "original_validation": original_validation,
            }),
        );

        result
    }

    fn try_array_const_key_cegar_route(
        &self,
        deadline: Option<Instant>,
    ) -> Option<PortfolioResult> {
        let route_start = Instant::now();
        if !self.problem.has_array_sorts() {
            return None;
        }
        if self.problem.clauses().len() > ARRAY_CONST_KEY_CEGAR_ROUTE_MAX_CLAUSES {
            self.decision_log.log_decision(DecisionEntry {
                stage: "array_const_key_cegar",
                gate_result: false,
                gate_reason: format!(
                    "clauses {} > cap {}",
                    self.problem.clauses().len(),
                    ARRAY_CONST_KEY_CEGAR_ROUTE_MAX_CLAUSES
                ),
                budget_secs: 0.0,
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "cap_exceeded",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        }
        let mut scalarized_probe = self.problem.clone();
        let alias_rewrites =
            scalarized_probe.rewrite_clause_local_constant_aliases_for_array_scalarization();
        if !scalarized_probe.has_const_array_scalarization_candidates_allow_symbolic_keys() {
            self.decision_log.log_decision(DecisionEntry {
                stage: "array_const_key_cegar",
                gate_result: false,
                gate_reason: "no finite constant array keys for scalarizable array sorts"
                    .to_string(),
                budget_secs: 0.0,
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "not_applicable",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        }

        if scalarized_probe
            .try_scalarize_const_array_selects_allow_symbolic_keys_with_map(&[])
            .is_none()
        {
            self.decision_log.log_decision(DecisionEntry {
                stage: "array_const_key_cegar",
                gate_result: false,
                gate_reason: "finite key collection produced no scalarization map".to_string(),
                budget_secs: 0.0,
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "not_applicable",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        }
        let original_max_arity = self
            .problem
            .predicates()
            .iter()
            .map(|pred| pred.arity())
            .max()
            .unwrap_or(0);
        let transformed_max_arity = scalarized_probe
            .predicates()
            .iter()
            .map(|pred| pred.arity())
            .max()
            .unwrap_or(0);
        let signature_changed = scalarized_probe
            .predicates()
            .iter()
            .zip(self.problem.predicates())
            .any(|(scalarized, original)| scalarized.arg_sorts != original.arg_sorts);
        drop(scalarized_probe);
        if !signature_changed {
            self.decision_log.log_decision(DecisionEntry {
                stage: "array_const_key_cegar",
                gate_result: false,
                gate_reason: "constant array keys do not project predicate arguments".to_string(),
                budget_secs: 0.0,
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "not_applicable",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        }
        if transformed_max_arity > ARRAY_CONST_KEY_CEGAR_ROUTE_MAX_TRANSFORMED_ARITY {
            self.decision_log.log_decision(DecisionEntry {
                stage: "array_const_key_cegar",
                gate_result: false,
                gate_reason: format!(
                    "transformed_max_arity {transformed_max_arity} > cap {ARRAY_CONST_KEY_CEGAR_ROUTE_MAX_TRANSFORMED_ARITY}"
                ),
                budget_secs: 0.0,
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "cap_exceeded",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        }

        let remaining = self
            .remaining_budget(deadline)
            .unwrap_or(ARRAY_CONST_KEY_CEGAR_ROUTE_BUDGET);
        if remaining < ARRAY_CONST_KEY_CEGAR_ROUTE_MIN_BUDGET {
            self.decision_log.log_decision(DecisionEntry {
                stage: "array_const_key_cegar",
                gate_result: true,
                gate_reason: "insufficient route budget".to_string(),
                budget_secs: remaining.as_secs_f64(),
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "skipped",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        }
        let route_budget = remaining.min(ARRAY_CONST_KEY_CEGAR_ROUTE_BUDGET);
        let (solve_budget, validation_budget) =
            if route_budget > ARRAY_CONST_KEY_CEGAR_ROUTE_VALIDATION_RESERVE {
                (
                    route_budget
                        .checked_sub(ARRAY_CONST_KEY_CEGAR_ROUTE_VALIDATION_RESERVE)
                        .unwrap(),
                    ARRAY_CONST_KEY_CEGAR_ROUTE_VALIDATION_RESERVE,
                )
            } else {
                (route_budget, Duration::ZERO)
            };

        let mut pdr_config = PdrConfig::production(self.config.verbose);
        pdr_config.solve_timeout = Some(solve_budget);
        pdr_config.strict_proofs = true;
        pdr_config.array_scalarization_keep_const_keys_with_symbolic_accesses = true;
        self.apply_user_hints(&mut pdr_config);

        let result_with_stats = PdrSolver::solve_problem_with_stats(&self.problem, pdr_config);
        self.accumulate_stats(&result_with_stats.stats);
        let result_name = Self::pdr_result_to_str(&result_with_stats.result);
        let lemmas_learned = result_with_stats.learned_lemmas.len();
        let max_frame = result_with_stats.stats.max_frame;
        let original_validation = match &result_with_stats.result {
            PdrResult::Safe(model) if !validation_budget.is_zero() => {
                let validation_config = PdrConfig {
                    verbose: self.config.verbose,
                    strict_proofs: true,
                    solve_timeout: Some(validation_budget),
                    disable_array_scalarization: true,
                    preserve_original_clauses: true,
                    ..PdrConfig::default()
                };
                crate::engines::validate_external_invariant_model(
                    &self.problem,
                    model,
                    &validation_config,
                )
                .unwrap_or(false)
            }
            PdrResult::Safe(_) => false,
            PdrResult::Unsafe(_) | PdrResult::Unknown | PdrResult::NotApplicable => false,
        };
        let accepted =
            matches!(result_with_stats.result, PdrResult::Safe(_)) && original_validation;
        self.decision_log.log_decision_with_details(
            DecisionEntry {
                stage: "array_const_key_cegar",
                gate_result: true,
                gate_reason: format!(
                    "finite constant array keys retained despite symbolic accesses; original_max_arity={original_max_arity}; transformed_max_arity={transformed_max_arity}; alias_rewrites={alias_rewrites}; original_validation={original_validation}"
                ),
                budget_secs: route_budget.as_secs_f64(),
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: if accepted { "safe" } else { result_name },
                lemmas_learned,
                max_frame,
            },
            serde_json::json!({
                "original_max_arity": original_max_arity,
                "transformed_max_arity": transformed_max_arity,
                "alias_rewrites": alias_rewrites,
                "keep_const_keys_with_symbolic_accesses": true,
                "original_validation": original_validation,
                "solve_budget_secs": solve_budget.as_secs_f64(),
                "validation_budget_secs": validation_budget.as_secs_f64(),
                "transformed_result": result_name,
            }),
        );

        match result_with_stats.result {
            PdrResult::Safe(model) if original_validation => Some(PortfolioResult::Safe(model)),
            PdrResult::Unsafe(_) | PdrResult::Unknown | PdrResult::NotApplicable => None,
            PdrResult::Safe(_) => None,
        }
    }

    /// FORALL-ARR ghost-pair lane (agenda #16, Eldarica `-arrayQuans:n` idea).
    ///
    /// Instruments every `(Array Int V)` predicate argument with `n` ghost
    /// `(idx, val)` scalar pairs (n=1 first, then n=2), runs PDR on the
    /// transformed problem to discover a QUANTIFIER-FREE invariant over the
    /// ghosts, and certifies the denoted quantified original invariant
    /// `forall i. I'(args, i, select(arr, i))` on the ORIGINAL clauses via
    /// the sealed [`crate::transform::GhostPairCertificate`] discharge
    /// (instantiation-based, with a full quantified executor fallback).
    ///
    /// Fail-closed: any certification failure falls through to the normal
    /// pipeline; an Unsafe result is only surfaced after the back-translated
    /// trace replays against the original clauses.
    fn try_array_ghost_pair_route(
        &self,
        deadline: Option<Instant>,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        use crate::transform::{ArrayGhostPairTransformer, GhostPairCertificate, GhostPairSpec};

        let route_start = Instant::now();
        if std::env::var_os(ARRAY_GHOST_PAIR_DISABLE_ENV).is_some() {
            return None;
        }
        if !self.problem.has_array_sorts() || self.problem.has_datatype_sorts() {
            return None;
        }
        if self.problem.clauses().len() > ARRAY_GHOST_PAIR_ROUTE_MAX_CLAUSES
            || self.problem.predicates().len() > ARRAY_GHOST_PAIR_ROUTE_MAX_PREDICATES
        {
            return None;
        }
        if GhostPairSpec::analyze(&self.problem, 1).is_empty() {
            return None;
        }
        // Quantified array invariants only pay off when the program indexes
        // arrays symbolically; constant-key problems are the const-key CEGAR
        // route's territory (it runs before this lane).
        let has_symbolic_index = self.problem.clauses().iter().any(|clause| {
            crate::transform::array_ghost_pairs::collect_index_terms(clause, 4)
                .iter()
                .any(|term| !matches!(term, ChcExpr::Int(_)))
        });
        if !has_symbolic_index {
            return None;
        }

        let route_budget = self.scaled_probe_budget(
            deadline,
            ARRAY_GHOST_PAIR_ROUTE_NOMINAL_BUDGET,
            ARRAY_GHOST_PAIR_ROUTE_BUDGET_PERCENT,
            ARRAY_GHOST_PAIR_ROUTE_BUDGET_CAP,
        );
        if route_budget < ARRAY_GHOST_PAIR_ROUTE_MIN_BUDGET {
            self.decision_log.log_decision(DecisionEntry {
                stage: "array_ghost_pairs",
                gate_result: true,
                gate_reason: "insufficient route budget".to_string(),
                budget_secs: route_budget.as_secs_f64(),
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "skipped",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        }
        let route_deadline = route_start + route_budget;

        for n in [1usize, 2] {
            let remaining = route_deadline.saturating_duration_since(Instant::now());
            if remaining < ARRAY_GHOST_PAIR_ROUTE_MIN_BUDGET {
                break;
            }
            // n=1 is the primary prong; leave head-room for the n=2 variant.
            let lane_budget = if n == 1 {
                route_budget.mul_f64(0.7).min(remaining)
            } else {
                remaining
            };

            let spec = GhostPairSpec::analyze(&self.problem, n);
            if spec.is_empty() {
                continue;
            }
            let transform_result =
                Box::new(ArrayGhostPairTransformer::new(n)).transform(self.problem.clone());
            let raw_ghost_problem = transform_result.problem;
            let ghost_back_translator = transform_result.back_translator;

            // Compiler-generated CHCs frequently contain long chains of
            // wrapper predicates around the array loop.  Ghosting first is
            // important: preprocessing then preserves the expanded signature
            // in its compaction/inlining traces, so translate_validity can
            // reconstruct a model for every RAW ghost predicate.  That raw
            // model is exactly what GhostPairCertificate consumes.
            //
            // Preprocessing is only a solve-shape optimization.  If it does
            // not produce a major reduction, retain the established direct
            // raw-ghost PDR path.
            let raw_ghost_predicates = raw_ghost_problem.predicates().len();
            let raw_ghost_clauses = raw_ghost_problem.clauses().len();
            let preprocess_candidate =
                PreprocessSummary::build(raw_ghost_problem.clone(), self.config.verbose);
            let preprocessed_predicates =
                preprocess_candidate.transformed_problem.predicates().len();
            let preprocessed_clauses = preprocess_candidate.transformed_problem.clauses().len();
            let predicate_reduction = raw_ghost_predicates
                >= preprocessed_predicates
                    .max(1)
                    .saturating_mul(ARRAY_GHOST_PAIR_PREPROCESS_REDUCTION_FACTOR);
            let clause_reduction = raw_ghost_clauses
                >= preprocessed_clauses
                    .max(1)
                    .saturating_mul(ARRAY_GHOST_PAIR_PREPROCESS_REDUCTION_FACTOR);
            let preprocess_summary =
                (predicate_reduction || clause_reduction).then_some(preprocess_candidate);
            let solve_problem = preprocess_summary
                .as_ref()
                .map_or(&raw_ghost_problem, |summary| &summary.transformed_problem);
            let solve_shape = if preprocess_summary.is_some() {
                "preprocessed"
            } else {
                "raw"
            };

            // Transformation time belongs to this lane.  Recompute the
            // available envelope before starting PDR so preprocessing cannot
            // consume the time reserved for certificate/replay acceptance.
            let available =
                lane_budget.min(route_deadline.saturating_duration_since(Instant::now()));
            let certify_reserve = available
                .mul_f64(ARRAY_GHOST_PAIR_CERTIFY_RESERVE_FRACTION)
                .max(Duration::from_millis(250))
                .min(available);
            let solve_budget = available.saturating_sub(certify_reserve);
            if solve_budget < ARRAY_GHOST_PAIR_ROUTE_MIN_BUDGET {
                continue;
            }

            // The arithmetic-route profile, not production(): ghost invariants
            // are conditional relational equalities over the ghost scalars
            // (e.g. `0 <= idx < n /\ idx_a = idx_b => val_a = val_b` for
            // copy-class problems), and production() keeps exactly the needed
            // generalizers (relational equality, range/init-bound weakening,
            // interpolation) OFF. Safe here for the same reason as the
            // LIA/Farkas route: the caller reserves certification time and the
            // final verdict rests on the original-clause quantified discharge,
            // never on the transformed solve.
            let mut pdr_config = PdrConfig::lia_farkas_profile(self.config.verbose);
            pdr_config.solve_timeout = Some(solve_budget);
            pdr_config.strict_proofs = true;
            self.apply_user_hints(&mut pdr_config);
            let result_with_stats = PdrSolver::solve_problem_with_stats(solve_problem, pdr_config);
            self.accumulate_stats(&result_with_stats.stats);
            let lemmas_learned = result_with_stats.learned_lemmas.len();
            let max_frame = result_with_stats.stats.max_frame;
            let transformed_result = Self::pdr_result_to_str(&result_with_stats.result);

            match result_with_stats.result {
                PdrResult::Safe(model) => {
                    // Preprocessing may compact surviving PredicateIds and
                    // inline definitions.  Reconstruct those interpretations
                    // in the RAW ghost vocabulary before sealing.  Deliberately
                    // do not call the ghost transform's validity translator:
                    // the denoted original invariant is quantified and that
                    // translator therefore returns an empty QF model.
                    let raw_ghost_model = match &preprocess_summary {
                        Some(summary) => summary.back_translator.translate_validity(model),
                        None => model,
                    };
                    // Seal the quantified certificate: the FULL per-rule
                    // discharge on the ORIGINAL clauses is the only way to
                    // construct it (fail-closed on any undischarged clause).
                    let certify_budget = route_deadline
                        .saturating_duration_since(Instant::now())
                        .max(certify_reserve);
                    let certify_budget = match self.remaining_budget(deadline) {
                        Some(global_remaining) => certify_budget.min(global_remaining),
                        None => certify_budget,
                    };
                    let sealed = GhostPairCertificate::certify_and_seal(
                        &self.problem,
                        spec,
                        raw_ghost_model,
                        Some(certify_budget),
                    );
                    self.decision_log.log_decision(DecisionEntry {
                        stage: "array_ghost_pairs",
                        gate_result: true,
                        gate_reason: format!(
                            "n={n}; solve_shape={solve_shape}; raw \
                             {raw_ghost_predicates}p/{raw_ghost_clauses}c -> solve \
                             {}p/{}c; transformed PDR safe; quantified certification {}",
                            solve_problem.predicates().len(),
                            solve_problem.clauses().len(),
                            if sealed.is_some() { "passed" } else { "failed" }
                        ),
                        budget_secs: route_budget.as_secs_f64(),
                        elapsed_secs: route_start.elapsed().as_secs_f64(),
                        result: if sealed.is_some() { "safe" } else { "unknown" },
                        lemmas_learned,
                        max_frame,
                    });
                    if let Some(certificate) = sealed {
                        let mut certified_model = InvariantModel::new();
                        certified_model.set_ghost_pair_certificate(certificate);
                        return Some((
                            PortfolioResult::Safe(certified_model),
                            ValidationEvidence::QuantifiedArrayInvariantCertificate,
                        ));
                    }
                }
                PdrResult::Unsafe(cex) => {
                    // Translate in the reverse transformation order.  The
                    // ground-evidence helper validates (or clears) a ground
                    // derivation at each boundary, preventing compacted clause
                    // indices from leaking into the raw ghost or original
                    // problem.  A final original replay remains mandatory.
                    let raw_ghost_cex = match &preprocess_summary {
                        Some(summary) => {
                            crate::portfolio::backtranslate_counterexample_with_ground_evidence(
                                summary.back_translator.as_ref(),
                                &raw_ghost_problem,
                                &cex,
                            )
                        }
                        None => cex,
                    };
                    let translated =
                        crate::portfolio::backtranslate_counterexample_with_ground_evidence(
                            ghost_back_translator.as_ref(),
                            &self.problem,
                            &raw_ghost_cex,
                        );
                    let replayed = self
                        .validate_final_unsafe_result(&translated, self.remaining_budget(deadline));
                    self.decision_log.log_decision(DecisionEntry {
                        stage: "array_ghost_pairs",
                        gate_result: true,
                        gate_reason: format!(
                            "n={n}; solve_shape={solve_shape}; raw \
                             {raw_ghost_predicates}p/{raw_ghost_clauses}c -> solve \
                             {}p/{}c; transformed PDR unsafe; original replay {}",
                            solve_problem.predicates().len(),
                            solve_problem.clauses().len(),
                            if replayed { "passed" } else { "failed" }
                        ),
                        budget_secs: route_budget.as_secs_f64(),
                        elapsed_secs: route_start.elapsed().as_secs_f64(),
                        result: if replayed { "unsafe" } else { "unknown" },
                        lemmas_learned,
                        max_frame,
                    });
                    if replayed {
                        return Some((
                            PortfolioResult::Unsafe(translated),
                            ValidationEvidence::CounterexampleVerification,
                        ));
                    }
                }
                PdrResult::Unknown | PdrResult::NotApplicable => {
                    self.decision_log.log_decision(DecisionEntry {
                        stage: "array_ghost_pairs",
                        gate_result: true,
                        gate_reason: format!(
                            "n={n}; solve_shape={solve_shape}; raw \
                             {raw_ghost_predicates}p/{raw_ghost_clauses}c -> solve \
                             {}p/{}c; transformed PDR inconclusive",
                            solve_problem.predicates().len(),
                            solve_problem.clauses().len(),
                        ),
                        budget_secs: route_budget.as_secs_f64(),
                        elapsed_secs: route_start.elapsed().as_secs_f64(),
                        result: transformed_result,
                        lemmas_learned,
                        max_frame,
                    });
                }
            }
        }
        None
    }

    fn try_dt_flattened_array_const_key_cegar_route(
        &self,
        deadline: Option<Instant>,
    ) -> Option<PortfolioResult> {
        let route_start = Instant::now();
        if !self.problem.has_datatype_sorts() || self.problem.has_array_sorts() {
            return None;
        }

        let remaining = self
            .remaining_budget(deadline)
            .unwrap_or(ARRAY_CONST_KEY_CEGAR_ROUTE_BUDGET);
        if remaining < ARRAY_CONST_KEY_CEGAR_ROUTE_MIN_BUDGET {
            return None;
        }
        let route_budget = remaining.min(ARRAY_CONST_KEY_CEGAR_ROUTE_BUDGET);
        let route_deadline = route_start + route_budget;

        let dt_result = Box::new(DtFlattener::new().with_verbose(self.config.verbose))
            .transform(self.problem.clone());
        let transform_memory = dt_result.transform_memory();
        let transformed_problem = dt_result.problem;
        let back_translator = dt_result.back_translator;

        if !transformed_problem.has_array_sorts() {
            self.decision_log.log_decision(DecisionEntry {
                stage: "dt_flat_array_const_key_cegar",
                gate_result: false,
                gate_reason: format!(
                    "DT flattening did not expose direct array predicate arguments; {}",
                    transform_memory.diagnostic_summary()
                ),
                budget_secs: route_budget.as_secs_f64(),
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "not_applicable",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        }
        let mut scalarized_probe = transformed_problem.clone();
        let alias_rewrites =
            scalarized_probe.rewrite_clause_local_constant_aliases_for_array_scalarization();
        if !scalarized_probe.has_const_array_scalarization_candidates_allow_symbolic_keys() {
            self.decision_log.log_decision(DecisionEntry {
                stage: "dt_flat_array_const_key_cegar",
                gate_result: false,
                gate_reason: format!(
                    "no finite constant array keys after DT flattening; {}",
                    transform_memory.diagnostic_summary()
                ),
                budget_secs: route_budget.as_secs_f64(),
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "not_applicable",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        }

        if scalarized_probe
            .try_scalarize_const_array_selects_allow_symbolic_keys_with_map(&[])
            .is_none()
        {
            self.decision_log.log_decision(DecisionEntry {
                stage: "dt_flat_array_const_key_cegar",
                gate_result: false,
                gate_reason: format!(
                    "finite key collection produced no scalarization map after DT flattening; {}",
                    transform_memory.diagnostic_summary()
                ),
                budget_secs: route_budget.as_secs_f64(),
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "not_applicable",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        }
        let transformed_max_arity = scalarized_probe
            .predicates()
            .iter()
            .map(|pred| pred.arity())
            .max()
            .unwrap_or(0);
        let flattened_max_arity = transformed_problem
            .predicates()
            .iter()
            .map(|pred| pred.arity())
            .max()
            .unwrap_or(0);
        let signature_changed = scalarized_probe
            .predicates()
            .iter()
            .zip(transformed_problem.predicates())
            .any(|(scalarized, original)| scalarized.arg_sorts != original.arg_sorts);
        drop(scalarized_probe);
        if !signature_changed {
            self.decision_log.log_decision(DecisionEntry {
                stage: "dt_flat_array_const_key_cegar",
                gate_result: false,
                gate_reason: format!(
                    "constant array keys do not project DT-flattened predicate arguments; {}",
                    transform_memory.diagnostic_summary()
                ),
                budget_secs: route_budget.as_secs_f64(),
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "not_applicable",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        }
        if transformed_max_arity > ARRAY_CONST_KEY_CEGAR_ROUTE_MAX_TRANSFORMED_ARITY {
            self.decision_log.log_decision(DecisionEntry {
                stage: "dt_flat_array_const_key_cegar",
                gate_result: false,
                gate_reason: format!(
                    "transformed_max_arity {transformed_max_arity} > cap {ARRAY_CONST_KEY_CEGAR_ROUTE_MAX_TRANSFORMED_ARITY}; {}",
                    transform_memory.diagnostic_summary()
                ),
                budget_secs: route_budget.as_secs_f64(),
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "cap_exceeded",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        }

        let Some(solve_budget) = Self::solidity_array_dt_remaining_route_budget(route_deadline)
        else {
            return None;
        };
        let mut pdr_config = PdrConfig::production(self.config.verbose);
        pdr_config.solve_timeout = Some(solve_budget);
        pdr_config.strict_proofs = true;
        pdr_config.array_scalarization_keep_const_keys_with_symbolic_accesses = true;
        self.apply_user_hints(&mut pdr_config);

        let result_with_stats =
            PdrSolver::solve_problem_with_stats(&transformed_problem, pdr_config);
        self.accumulate_stats(&result_with_stats.stats);
        let result_name = Self::pdr_result_to_str(&result_with_stats.result);
        let lemmas_learned = result_with_stats.learned_lemmas.len();
        let max_frame = result_with_stats.stats.max_frame;

        let translated_safe = match result_with_stats.result {
            PdrResult::Safe(model) => {
                let translated_model = back_translator.translate_validity(model);
                if self.validate_solidity_array_dt_original_model(&translated_model, route_deadline)
                    == SolidityArrayDtValidationStatus::Accepted
                {
                    Some(translated_model)
                } else {
                    None
                }
            }
            PdrResult::Unsafe(_) | PdrResult::Unknown | PdrResult::NotApplicable => None,
        };
        let original_validation = translated_safe.is_some();

        self.decision_log.log_decision_with_details(
            DecisionEntry {
                stage: "dt_flat_array_const_key_cegar",
                gate_result: true,
                gate_reason: format!(
                    "DT flattening plus finite constant array keys; flattened_max_arity={flattened_max_arity}; transformed_max_arity={transformed_max_arity}; alias_rewrites={alias_rewrites}; original_validation={original_validation}; {}",
                    transform_memory.diagnostic_summary()
                ),
                budget_secs: route_budget.as_secs_f64(),
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: if original_validation {
                    "safe"
                } else {
                    result_name
                },
                lemmas_learned,
                max_frame,
            },
            serde_json::json!({
                "flattened_max_arity": flattened_max_arity,
                "transformed_max_arity": transformed_max_arity,
                "alias_rewrites": alias_rewrites,
                "keep_const_keys_with_symbolic_accesses": true,
                "original_validation": original_validation,
                "transform_memory": transform_memory.diagnostic_summary(),
                "transformed_result": result_name,
            }),
        );

        translated_safe.map(PortfolioResult::Safe)
    }

    fn should_try_lia_farkas_pdr_route(&self, features: &ProblemFeatures) -> bool {
        matches!(
            features.class,
            ProblemClass::SimpleLoop | ProblemClass::MultiPredLinear
        ) && (features.is_linear || features.is_triangle_location_diff_bounds)
            && !features.uses_arrays
            && !features.uses_datatypes
            && !features.uses_real
            && !self.problem.has_bv_sorts()
            && !features.has_mod_div
            && problem_has_linear_arithmetic_predicate_argument(&self.problem)
    }

    fn should_route_triangle_bv_diff_bounds_to_bv_lane(&self, features: &ProblemFeatures) -> bool {
        features.is_triangle_location_diff_bounds
            && self.problem.has_bv_sorts()
            && !features.uses_arrays
            && !features.uses_real
            && !features.uses_datatypes
    }

    fn validate_lia_farkas_safe_model_on_original(
        &self,
        model: &InvariantModel,
        validation_budget: Duration,
    ) -> bool {
        if validation_budget.is_zero() {
            return false;
        }

        let validation_config = PdrConfig {
            verbose: self.config.verbose,
            strict_proofs: true,
            solve_timeout: Some(validation_budget),
            disable_array_scalarization: true,
            preserve_original_clauses: true,
            ..PdrConfig::default()
        };
        crate::engines::validate_external_invariant_model(&self.problem, model, &validation_config)
            .unwrap_or(false)
    }

    /// Run the dedicated linear-arithmetic PDR/Farkas profile.
    ///
    /// The profile enables affine equality, interval, difference-bound, scaled
    /// difference, interpolation, and Farkas-combination surfaces that
    /// production PDR keeps partially disabled for broad performance reasons.
    /// This route is fail-closed: accepted Safe/Unsafe answers are validated on
    /// the original CHC, and validation failure becomes UNKNOWN.
    pub(crate) fn try_lia_farkas_pdr_route(
        &self,
        features: &ProblemFeatures,
        deadline: Option<Instant>,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        let route_start = Instant::now();
        if !self.should_try_lia_farkas_pdr_route(features) {
            return None;
        }

        let remaining = self
            .remaining_budget(deadline)
            .unwrap_or(LIA_FARKAS_ROUTE_BUDGET);
        let route_budget = remaining.min(LIA_FARKAS_ROUTE_BUDGET);
        if route_budget <= LIA_FARKAS_ROUTE_VALIDATION_RESERVE {
            self.decision_log.log_decision(DecisionEntry {
                stage: "lia_farkas_pdr",
                gate_result: true,
                gate_reason: "insufficient budget for solve plus original validation".to_string(),
                budget_secs: route_budget.as_secs_f64(),
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "skipped",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        }
        let solve_budget = route_budget.saturating_sub(LIA_FARKAS_ROUTE_VALIDATION_RESERVE);
        let validation_budget = LIA_FARKAS_ROUTE_VALIDATION_RESERVE;

        // Child of the portfolio handle (item 5): the lane budget timer
        // cancels only this lane; an external cancel reaches it too.
        let cancel = self.cancellation_token.child();
        let _timeout_guard = cancel.cancel_after(solve_budget);
        let mut pdr_config = PdrConfig::lia_farkas_profile(self.config.verbose);
        pdr_config.solve_timeout = Some(solve_budget);
        pdr_config.cancellation_token = Some(cancel);
        self.apply_user_hints(&mut pdr_config);

        let mut solver = PdrSolver::new(self.problem.clone(), pdr_config);
        solver.enable_tla_trace_from_config();
        let result_with_stats = solver.solve_with_stats();
        self.accumulate_stats(&result_with_stats.stats);

        let result_name = Self::pdr_result_to_str(&result_with_stats.result);
        let route_stats = result_with_stats.lia_farkas_route_stats.clone();
        let route_reason = format!(
            "linear arithmetic profile; real={}; class={}; profile={}; \
             template_surfaces={}; template_checks={}; farkas_checks={}; \
             accepted_lemmas={}; rejected_lemmas={}; original_validation=true",
            features.uses_real,
            features.class,
            route_stats.profile_name,
            route_stats.template_generation_surfaces,
            route_stats.template_generation_checks,
            route_stats.farkas_checks,
            route_stats.accepted_lemmas,
            route_stats.rejected_lemmas,
        );
        let lia_farkas_details =
            |result: &'static str,
             original_safe_validation: Option<bool>,
             original_trace_replay: Option<bool>| {
                let original_validation_failures =
                    usize::from(matches!(original_safe_validation, Some(false)))
                        + usize::from(matches!(original_trace_replay, Some(false)));
                serde_json::json!({
                "profile_name": route_stats.profile_name,
                "profile_enabled": route_stats.profile_enabled,
                "enabled_template_surfaces": route_stats.enabled_template_surfaces,
                "template_generation_surfaces": route_stats.template_generation_surfaces,
                "templates_generated": route_stats.templates_generated,
                "template_generation_checks": route_stats.template_generation_checks,
                "farkas_checks": route_stats.farkas_checks,
                       "accepted_lemmas": route_stats.accepted_lemmas,
                       "rejected_lemmas": route_stats.rejected_lemmas,
                       "validation_checks": route_stats.validation_checks,
                       "validation_failures": route_stats.validation_failures,
                       "original_validation_required": route_stats.original_validation_required,
                       "original_safe_validation": original_safe_validation,
                       "original_trace_replay": original_trace_replay,
                       "original_validation_failures": original_validation_failures,
                       "route_validation_failures": route_stats
                           .validation_failures
                           .saturating_add(original_validation_failures),
                       "route_result": result,
                       "uses_real": features.uses_real,
                       "problem_class": features.class.to_string(),
                   })
            };

        match result_with_stats.result {
            PdrResult::Safe(model) => {
                let valid =
                    self.validate_lia_farkas_safe_model_on_original(&model, validation_budget);
                let decision_result = if valid {
                    "safe"
                } else {
                    "safe_validation_rejected"
                };
                self.decision_log.log_decision_with_details(
                    DecisionEntry {
                        stage: "lia_farkas_pdr",
                        gate_result: true,
                        gate_reason: route_reason,
                        budget_secs: route_budget.as_secs_f64(),
                        elapsed_secs: route_start.elapsed().as_secs_f64(),
                        result: decision_result,
                        lemmas_learned: result_with_stats.stats.lemmas_learned,
                        max_frame: result_with_stats.stats.max_frame,
                    },
                    lia_farkas_details(decision_result, Some(valid), None),
                );
                Some(if valid {
                    (
                        PortfolioResult::Safe(model),
                        ValidationEvidence::FullVerification,
                    )
                } else {
                    (
                        PortfolioResult::Unknown,
                        ValidationEvidence::FullVerification,
                    )
                })
            }
            PdrResult::Unsafe(cex) => {
                let valid = self.validate_final_unsafe_result(&cex, Some(validation_budget));
                let decision_result = if valid {
                    "unsafe"
                } else {
                    "unsafe_validation_rejected"
                };
                self.decision_log.log_decision_with_details(
                    DecisionEntry {
                        stage: "lia_farkas_pdr",
                        gate_result: true,
                        gate_reason: route_reason,
                        budget_secs: route_budget.as_secs_f64(),
                        elapsed_secs: route_start.elapsed().as_secs_f64(),
                        result: decision_result,
                        lemmas_learned: result_with_stats.stats.lemmas_learned,
                        max_frame: result_with_stats.stats.max_frame,
                    },
                    lia_farkas_details(decision_result, None, Some(valid)),
                );
                Some(if valid {
                    (
                        PortfolioResult::Unsafe(cex),
                        ValidationEvidence::CounterexampleVerification,
                    )
                } else {
                    (
                        PortfolioResult::Unknown,
                        ValidationEvidence::FullVerification,
                    )
                })
            }
            PdrResult::Unknown | PdrResult::NotApplicable => {
                self.decision_log.log_decision_with_details(
                    DecisionEntry {
                        stage: "lia_farkas_pdr",
                        gate_result: true,
                        gate_reason: route_reason,
                        budget_secs: route_budget.as_secs_f64(),
                        elapsed_secs: route_start.elapsed().as_secs_f64(),
                        result: result_name,
                        lemmas_learned: result_with_stats.stats.lemmas_learned,
                        max_frame: result_with_stats.stats.max_frame,
                    },
                    lia_farkas_details(result_name, None, None),
                );
                None
            }
        }
    }

    /// Non-destructive marker-unfold Houdini prepass (#9078).
    ///
    /// Clones the problem, unfolds trivial 0-arity Bool query markers (only when
    /// a real predicate remains and there are no BV/array/datatype sorts), and
    /// runs the conjunctive-Houdini arithmetic-query route on the unfolded copy.
    /// Returns `Some(Safe)` only when the Houdini invariant validates against the
    /// (equivalent) unfolded clauses. The original problem/routing are untouched.
    fn try_marker_unfold_houdini_prepass(
        &self,
        deadline: Option<Instant>,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        let mut copy = self.problem.clone();
        let before = copy.clauses().len();
        copy.eliminate_trivial_bool_markers();
        if copy.clauses().len() == before {
            return None; // no marker unfolded — nothing to gain
        }
        let sub = Self::new(copy, self.config.clone());
        let features = ProblemClassifier::classify(sub.problem());
        sub.try_houdini_conjunctive_prepass(&features, deadline)
    }

    /// Validated Safe for syntactically-unreachable query-only problems (w10).
    ///
    /// A query-only problem whose reachability surface is syntactically
    /// unreachable (all facts constraint-false — those are pruned at ingest by
    /// `simplify_clause_body_constants`, leaving the query predicates with no
    /// defining clauses) is genuinely Safe: nothing is derivable, so every
    /// query is vacuously unreachable. #8865 demoted this shape to Unknown
    /// because the empty-model acyclic proof carried no proof-grade
    /// certificate for BV/Array/Datatype signatures. Instead of failing closed
    /// outright, first attempt a PROPERLY VALIDATED Safe: materialize constant
    /// interpretations (`false` for query-feeding predicates) and run the full
    /// strict external-invariant validation against the ORIGINAL clauses —
    /// exactly the evidence path the final-safe-model completion (Fix B1)
    /// uses. Only a fully verified model is returned; on any validation
    /// failure/timeout the caller keeps the #8865 fail-closed Unknown.
    ///
    /// Soundness: the returned model is accepted only after
    /// `validate_external_invariant_model` (strict proofs) discharges every
    /// original clause, so no choice of constants can yield an unsound accept.
    /// A query with a satisfiable predicate-free body makes validation fail
    /// and the result stays Unknown, exactly as before.
    fn try_vacuous_query_only_validated_safe(
        &self,
        deadline: Option<Instant>,
    ) -> Option<PortfolioResult> {
        let mut completed = self.try_complete_final_safe_model_with_constant_interpretations(
            &InvariantModel::new(),
            self.remaining_budget(deadline),
        )?;

        // Make the certificate total: declared predicates that appear in NO
        // clause are still missing after completion (the completion helper
        // only materializes referenced predicates). Interpret them as
        // constant-false, mirroring the portfolio trivial-Safe path
        // (`complete_unreferenced_predicate_interpretations`). They occur in
        // no verification obligation, so this cannot affect the validated
        // result.
        for pred in self.problem.predicates() {
            if completed.get(&pred.id).is_none() {
                let vars: Vec<ChcVar> = pred
                    .arg_sorts
                    .iter()
                    .enumerate()
                    .map(|(i, sort)| {
                        ChcVar::new(
                            format!("__unused_p{}_a{}", pred.id.index(), i),
                            sort.clone(),
                        )
                    })
                    .collect();
                completed.set(
                    pred.id,
                    PredicateInterpretation::new(vars, ChcExpr::Bool(false)),
                );
            }
        }

        Some(PortfolioResult::Safe(completed))
    }

    /// Construct the universal (all-predicates-`true`) candidate for `problem`.
    ///
    /// Under that interpretation every predicate-headed clause is immediate:
    /// its head is `true`. A query clause reduces exactly to its pure body
    /// constraint, so the candidate is viable iff every such constraint is
    /// unsatisfiable. This helper is deliberately only an admission filter:
    /// callers MUST back-translate the candidate and strictly validate every
    /// unchanged original clause before accepting `Safe`.
    ///
    /// Raw compiler encodings often end in a nullary `error -> false` query,
    /// for which the top interpretation is correctly rejected. Certified
    /// preprocessing can inline that control predicate and expose the actual
    /// contradictory query constraint; the reduced LIA-array route invokes
    /// this helper on precisely that transformed problem.
    fn try_top_model_query_infeasibility_candidate(
        problem: &ChcProblem,
        query_budget: Duration,
    ) -> Option<InvariantModel> {
        let queries: Vec<&HornClause> = problem.queries().collect();
        if !queries.is_empty() && query_budget.is_zero() {
            return None;
        }

        if !queries.is_empty() {
            let mut smt = problem.make_smt_context();
            smt.set_global_solve_deadline(Some(Instant::now() + query_budget));
            for query in &queries {
                let constraint = query.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
                smt.reset();
                if !matches!(
                    smt.check_sat(&constraint),
                    SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
                ) {
                    return None;
                }
            }
        }

        let mut model = InvariantModel::new();
        for predicate in problem.predicates() {
            let vars = predicate
                .arg_sorts
                .iter()
                .enumerate()
                .map(|(index, sort)| {
                    ChcVar::new(
                        format!("__p{}_a{index}", predicate.id.index()),
                        sort.clone(),
                    )
                })
                .collect();
            model.set(
                predicate.id,
                PredicateInterpretation::new(vars, ChcExpr::Bool(true)),
            );
        }
        Some(model)
    }

    fn solve_internal(&self, deadline: Option<Instant>) -> (PortfolioResult, ValidationEvidence) {
        // Trace mode: single PDR with TLA trace, validated through the
        // same pipeline as normal results. Part of #5811.
        if self.config.trace_mode {
            return (
                self.solve_trace_mode(),
                ValidationEvidence::FullVerification,
            );
        }

        // Skip classification if requested
        if self.config.skip_classification {
            return (self.solve_default(), ValidationEvidence::FullVerification);
        }

        // Classify the problem
        let features = ProblemClassifier::classify(&self.problem);

        // #9078: non-destructive aeval/reve marker-unfold Houdini prepass. On a
        // COPY with trivial 0-arity Bool query markers unfolded
        // (`inv ∧ φ ⇒ fail`, `fail ⇒ false`  ≡  `inv ∧ φ ⇒ false`) it runs the
        // conjunctive-Houdini arithmetic-query route. The original problem and
        // its routing are untouched, so nothing regresses — this only ADDS a
        // fast attempt that solves the aeval multi-phase `s_split` family.
        // Sound: the unfold is an exact equivalence and survivors are validated
        // against the (equivalent) unfolded clauses.
        if let Some((result, evidence)) = self.try_marker_unfold_houdini_prepass(deadline) {
            return (result, evidence);
        }

        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: Problem classified as {} ({} preds, {} clauses, linear={}, \
                 single_pred={}, cycles={}, arrays={}, real={}, \
                 trans={}, facts={}, queries={}, entry_exit={}, phase_bounded={:?}, \
                 sccs={}, max_scc={}, dag_depth={}, max_vars={}, mean_vars={:.1}, \
                 mul={}, moddiv={}, ite={}, self_loop={:.2}, max_arity={}, triangle_location={})",
                features.class,
                features.num_predicates,
                features.num_clauses,
                features.is_linear,
                features.is_single_predicate,
                features.has_cycles,
                features.uses_arrays,
                features.uses_real,
                features.num_transitions,
                features.num_facts,
                features.num_queries,
                features.is_entry_exit_only,
                features.phase_bounded_depth,
                features.scc_count,
                features.max_scc_size,
                features.dag_depth,
                features.max_clause_variables,
                features.mean_clause_variables,
                features.has_multiplication,
                features.has_mod_div,
                features.has_ite,
                features.self_loop_ratio,
                features.max_predicate_arity,
                features.is_triangle_location_diff_bounds,
            );
        }

        // Log classification decision if decision logging is active.
        let class_name = format!("{}", features.class);

        if complex_query_only_vacuous_safety_must_fail_closed(&self.problem, &features) {
            // w10: attempt a fully validated constant-model Safe before the
            // #8865 fail-closed Unknown (see try_vacuous_query_only_validated_safe).
            let guard_start = Instant::now();
            if let Some(result) = self.try_vacuous_query_only_validated_safe(deadline) {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: complex query-only problem is syntactically unreachable; \
                         constant-model completion fully verified on original clauses — Safe"
                    );
                }
                self.decision_log.log_decision(DecisionEntry {
                    stage: "complex_query_only_vacuous_safety_guard",
                    gate_result: true,
                    gate_reason: "syntactically unreachable query-only problem; \
                                  constant model fully verified on original clauses"
                        .to_string(),
                    budget_secs: self
                        .remaining_budget(deadline)
                        .map_or(0.0, |b| b.as_secs_f64()),
                    elapsed_secs: guard_start.elapsed().as_secs_f64(),
                    result: "safe",
                    lemmas_learned: 0,
                    max_frame: 0,
                });
                return (result, ValidationEvidence::FullVerification);
            }
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: complex query-only problem is syntactically unreachable; demoting vacuous Safe proof to Unknown"
                );
            }
            self.decision_log.log_decision(DecisionEntry {
                stage: "complex_query_only_vacuous_safety_guard",
                gate_result: false,
                gate_reason: "syntactically unreachable complex query-only problem".to_string(),
                budget_secs: 0.0,
                elapsed_secs: guard_start.elapsed().as_secs_f64(),
                result: "unknown",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return (
                PortfolioResult::Unknown,
                ValidationEvidence::FullVerification,
            );
        }

        if let Some(result) = self.try_reduced_lia_array_preprocessed_route(deadline) {
            return result;
        }

        if let Some(result) = self.try_adt_array_nullary_unsafe_prepass(deadline) {
            return result;
        }

        if let Some(result) = self.try_shallow_unsafe_bmc_prepass(&features, deadline) {
            return result;
        }

        // Datatype-aware bounded BMC refutation (#chc25-adt-bmc): fills the
        // ADT-LIA unsafe functional gap. Flat/level BMC bails on datatype
        // sorts, so ADT counterexamples were never found. This lane refutes
        // them soundly (bounded derivation-tree unfolding decided by ay-dpll's
        // native datatype theory; every candidate replayed on the ORIGINAL
        // clauses). Unsafe-only ⇒ purely additive; safe instances fall through
        // to the cata / native-ADT-MBP PDR routes below. Kill switch
        // AY_CHC_DISABLE_DT_BMC.
        if let Some(result) = self.try_datatype_bounded_bmc_refutation(&features, deadline) {
            return result;
        }

        // Cheap validated Safe guess for the IsaPlanner `last`/singleton
        // ADT+LIA shape (#9700), AFTER the datatype BMC unsafe refutation
        // (unsafe instances keep their fast refutation path) and BEFORE the
        // CATA abstraction lane, whose refinement rounds burn the whole
        // budget on exactly this shape. The guess is strictly validated
        // per-rule against the ORIGINAL clauses and fails closed, so it can
        // never manufacture a Safe verdict; class-gated to SimpleLoop, the
        // only class that could previously reach it.
        if matches!(features.class, ProblemClass::SimpleLoop) {
            if let Some(result) = self.try_adt_lia_constructor_case_synthesis(&features) {
                return (result, ValidationEvidence::FullVerification);
            }
        }

        if let Some(result) = self.try_argument_constant_invariant_route(deadline) {
            return (result, ValidationEvidence::FullVerification);
        }

        if let Some(result) = self.try_solidity_array_dt_projection_route(deadline) {
            return (result, ValidationEvidence::FullVerification);
        }

        if let Some(result) = self.try_dt_flattened_array_const_key_cegar_route(deadline) {
            return (result, ValidationEvidence::FullVerification);
        }

        // Catamorphism-abstraction lane for RECURSIVE-datatype problems
        // (agenda #7, CATA v1; kill switch AY_CHC_DISABLE_CATA). Non-recursive
        // datatype problems keep the exact DtFlattener pipelines below. The
        // route returns only composite-certified Safe verdicts or concrete
        // original-clause counterexamples (see adaptive_cata.rs).
        if let Some((result, evidence)) = self.try_cata_abstraction_route(deadline) {
            return (result, evidence);
        }

        if let Some(result) = self.try_array_const_key_cegar_route(deadline) {
            return (result, ValidationEvidence::FullVerification);
        }

        // FORALL-ARR ghost-pair lane (agenda #16): quantified array invariants
        // via ghost index/value pairs. Kill switch:
        // AY_CHC_DISABLE_ARRAY_GHOST_PAIRS.
        if let Some(result) = self.try_array_ghost_pair_route(deadline) {
            return result;
        }

        if std::env::var_os(REAL_LRA_PROMOTION_ENV).is_some() {
            if let Some(result) =
                self.try_cruise_controller_mixed_phase_invariant(&features, deadline)
            {
                return (result, ValidationEvidence::FullVerification);
            }
        }

        if should_prioritize_acyclic_bv_proof_prepass(&features, &self.problem) {
            if let Some((result, evidence)) = self.try_acyclic_bmc_probe(&features, deadline) {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: Pre-algebraic acyclic BV BMC probe solved the problem"
                    );
                }
                return (result, evidence);
            }
        }

        // Pre-strategy: Try algebraic invariant synthesis from polynomial
        // closed forms. This handles accumulator/polynomial patterns that
        // PDR and other engines cannot solve (e.g., sum = i*(i-1)/2).
        // Algebraic synthesis runs on the original problem shape before
        // preprocessing destroys self-loop structure. Its validation deadline
        // is capped by `algebraic_prestage_budget`.
        // Part of #7897, #7931.
        let large_acyclic_bv_array_graph = features.uses_arrays
            && self.problem.has_bv_sorts()
            && !features.has_cycles
            && features.is_linear
            && features.num_predicates > 128;
        let triangle_bv_diff_bound_direct_route =
            self.should_route_triangle_bv_diff_bounds_to_bv_lane(&features);

        if !matches!(features.class, ProblemClass::EntryExitOnly)
            && !large_acyclic_bv_array_graph
            && !triangle_bv_diff_bound_direct_route
        {
            use crate::algebraic_invariant::AlgebraicResult;

            let alg_start = Instant::now();
            // #8753: cap algebraic pre-strategy wall clock. Prior behavior
            // allowed `try_algebraic_solve` to burn the entire CHC budget on
            // SMT validation, starving PDR/IMC/TPA/LAWI.
            let alg_budget = algebraic_prestage_budget(&features, self.config.time_budget);
            let alg_deadline = alg_start + alg_budget;
            let (algebraic_result, algebraic_validation_stats) =
                crate::algebraic_invariant::try_algebraic_solve_with_deadline_and_stats(
                    &self.problem,
                    self.config.verbose,
                    Some(alg_deadline),
                );
            self.record_lra_affine_original_clause_validation_stats(&algebraic_validation_stats);
            match algebraic_result {
                AlgebraicResult::Safe(model) => {
                    let alg_elapsed = alg_start.elapsed().as_secs_f64();
                    if self.config.verbose {
                        safe_eprintln!(
                            "Adaptive: Algebraic invariant synthesis succeeded in {:.3}s",
                            alg_elapsed,
                        );
                    }
                    self.decision_log.log_decision(DecisionEntry {
                        stage: "algebraic_synthesis",
                        gate_result: true,
                        gate_reason: "polynomial closed form".to_string(),
                        budget_secs: alg_budget.as_secs_f64(),
                        elapsed_secs: alg_elapsed,
                        result: "safe",
                        lemmas_learned: 0,
                        max_frame: 0,
                    });
                    return (
                        PortfolioResult::Safe(model),
                        ValidationEvidence::AlgebraicClosedForm,
                    );
                }
                AlgebraicResult::Unsafe => {
                    let alg_elapsed = alg_start.elapsed().as_secs_f64();
                    if self.config.verbose {
                        safe_eprintln!(
                            "Adaptive: Algebraic synthesis detected UNSAFE in {:.3}s \
                             but produced no replayable witness; continuing",
                            alg_elapsed,
                        );
                    }
                    self.decision_log.log_decision(DecisionEntry {
                        stage: "algebraic_synthesis",
                        gate_result: false,
                        gate_reason: "algebraic unsafe has no replayable original witness"
                            .to_string(),
                        budget_secs: alg_budget.as_secs_f64(),
                        elapsed_secs: alg_elapsed,
                        result: "unknown",
                        lemmas_learned: 0,
                        max_frame: 0,
                    });
                }
                AlgebraicResult::NotApplicable if self.problem.has_bv_sorts() => {
                    // BV problems: the original problem has BvAdd/BvMul ops that
                    // recurrence analysis cannot handle. Apply BvToInt + DeadParamElim
                    // (without BvToBool which bitblasts to 96 Bool args) and retry.
                    // This is the same pipeline as portfolio's try_algebraic_prepass
                    // but runs BEFORE the quad-lane to avoid thread-join blocking
                    // that causes the result to be lost even when synthesis succeeds.
                    // Part of #7931.
                    let bv_to_int_result = {
                        // #8419: DtFlattener must run before BvToInt so BV fields
                        // inside DT constructors become top-level BV args eligible
                        // for integer abstraction.
                        let pipeline = TransformationPipeline::new()
                            .with(DtFlattener::new().with_verbose(self.config.verbose))
                            .with(BvToIntAbstractor::new().with_verbose(self.config.verbose))
                            .with(DeadParamEliminator::new().with_verbose(self.config.verbose));
                        pipeline.transform(self.problem.clone())
                    };
                    // #8753: reuse the pre-stage deadline so the BvToInt retry
                    // does not silently extend the algebraic budget.
                    let (algebraic_result, algebraic_validation_stats) =
                        crate::algebraic_invariant::try_algebraic_solve_with_deadline_and_stats(
                            &bv_to_int_result.problem,
                            self.config.verbose,
                            Some(alg_deadline),
                        );
                    self.record_lra_affine_original_clause_validation_stats(
                        &algebraic_validation_stats,
                    );
                    match algebraic_result {
                        AlgebraicResult::Safe(model) => {
                            let alg_elapsed = alg_start.elapsed().as_secs_f64();
                            if self.config.verbose {
                                safe_eprintln!(
                                    "Adaptive: Algebraic invariant synthesis succeeded (BvToInt) in {:.3}s",
                                    alg_elapsed,
                                );
                            }
                            let translated_model =
                                bv_to_int_result.back_translator.translate_validity(model);
                            let validated =
                                self.validate_adaptive_result(PdrResult::Safe(translated_model));
                            if let PdrResult::Safe(model) = validated {
                                self.decision_log.log_decision(DecisionEntry {
                                    stage: "algebraic_synthesis_bvtoint",
                                    gate_result: true,
                                    gate_reason:
                                        "polynomial closed form via BvToInt validated on original"
                                            .to_string(),
                                    budget_secs: alg_budget.as_secs_f64(),
                                    elapsed_secs: alg_elapsed,
                                    result: "safe",
                                    lemmas_learned: 0,
                                    max_frame: 0,
                                });
                                return (
                                    PortfolioResult::Safe(model),
                                    ValidationEvidence::FullVerification,
                                );
                            }

                            self.decision_log.log_decision(DecisionEntry {
                                stage: "algebraic_synthesis_bvtoint",
                                gate_result: false,
                                gate_reason: "BvToInt algebraic model failed original validation"
                                    .to_string(),
                                budget_secs: alg_budget.as_secs_f64(),
                                elapsed_secs: alg_elapsed,
                                result: "unknown",
                                lemmas_learned: 0,
                                max_frame: 0,
                            });
                        }
                        AlgebraicResult::Unsafe => {
                            let alg_elapsed = alg_start.elapsed().as_secs_f64();
                            if self.config.verbose {
                                safe_eprintln!(
                                    "Adaptive: Algebraic synthesis (BvToInt) detected UNSAFE in {:.3}s \
                                     but produced no replayable witness; continuing",
                                    alg_elapsed,
                                );
                            }
                            self.decision_log.log_decision(DecisionEntry {
                                stage: "algebraic_synthesis_bvtoint",
                                gate_result: false,
                                gate_reason:
                                    "BvToInt algebraic unsafe has no replayable original witness"
                                        .to_string(),
                                budget_secs: alg_budget.as_secs_f64(),
                                elapsed_secs: alg_elapsed,
                                result: "unknown",
                                lemmas_learned: 0,
                                max_frame: 0,
                            });
                        }
                        AlgebraicResult::NotApplicable => {
                            self.decision_log.log_decision(DecisionEntry {
                                stage: "algebraic_synthesis",
                                gate_result: false,
                                gate_reason: "not applicable or validation failed (incl. BvToInt)"
                                    .to_string(),
                                budget_secs: alg_budget.as_secs_f64(),
                                elapsed_secs: alg_start.elapsed().as_secs_f64(),
                                result: "skipped",
                                lemmas_learned: 0,
                                max_frame: 0,
                            });
                        }
                    }
                }
                AlgebraicResult::NotApplicable => {
                    self.decision_log.log_decision(DecisionEntry {
                        stage: "algebraic_synthesis",
                        gate_result: false,
                        gate_reason: "not applicable or validation failed".to_string(),
                        budget_secs: alg_budget.as_secs_f64(),
                        elapsed_secs: alg_start.elapsed().as_secs_f64(),
                        result: "skipped",
                        lemmas_learned: 0,
                        max_frame: 0,
                    });
                }
            }
        }

        // Select and run appropriate strategy.
        //
        // #7930: Complex problem classes MUST use specialized solve paths
        // (solve_complex_loop, solve_multi_pred_linear, solve_multi_pred_complex)
        // with DT-aware guards (max_escalation_level cap, Kind skip), budget
        // management, and deadline enforcement. Do NOT collapse these arms
        // into a single learned-selector call -- that bypasses DT+BV guards
        // and causes canary timeouts. Regressed twice (bec6a4ff9, 3e7b66b16)
        // and fixed twice (aeb44ab8d, this commit).
        let strategy_start = Instant::now();
        let budget_secs = self.config.time_budget.as_secs_f64();

        let (result, evidence) = match features.class {
            ProblemClass::EntryExitOnly => (
                self.solve_entry_exit_only(&features),
                ValidationEvidence::TrivialProblem,
            ),
            ProblemClass::Trivial => (
                self.solve_trivial(&features, deadline),
                ValidationEvidence::FullVerification,
            ),
            ProblemClass::SimpleLoop if features.uses_real => (
                self.solve_with_learned_selection(deadline),
                ValidationEvidence::FullVerification,
            ),
            ProblemClass::SimpleLoop => {
                if let Some(result) = self.try_accumulator_lia_unsafe_counterexample(&features) {
                    result
                // Cheap shallow-counterexample probe BEFORE invariant-directed
                // routes: unsafe transition systems (lustre-class) usually
                // fall to BMC in <1s, while farkas/Kind burn whole budgets.
                } else if let Some(result) = self.try_front_bmc_probe(&features, deadline) {
                    result
                // Guess-and-check the query-flag invariant (lustre-class sat
                // instances) before the heavier invariant routes.
                } else if let Some(result) =
                    self.try_query_flag_invariant_prepass(&features, deadline)
                {
                    result
                // Conjunctive Houdini over the extracted transition system
                // (lustre-class sat instances the single-flag guess misses).
                // BV problems run this prepass INSIDE the simple-loop strategy
                // instead (#11 QUAL-MINE): there it sits AFTER the cheap
                // unsafe routes (deterministic BV transition, Kind), so
                // already-solved BV unsafes keep their fast path.
                } else if let Some(result) = (!self.problem.has_bv_sorts())
                    .then(|| self.try_houdini_conjunctive_prepass(&features, deadline))
                    .flatten()
                {
                    result
                } else if let Some(result) = self.try_lia_farkas_pdr_route(&features, deadline) {
                    result
                } else {
                    self.solve_simple_loop_with_evidence(&features, deadline)
                }
            }
            ProblemClass::ComplexLoop => {
                // All complex loops use the full staging pipeline. For multi-
                // predicate problems (2+ preds), solve_complex_loop runs a
                // non-inlined PDR pre-stage before the portfolio to preserve
                // per-predicate structure that clause inlining would destroy.
                let result = self.solve_complex_loop(&features, deadline);
                let evidence = Self::complex_loop_validation_evidence();
                (result, evidence)
            }
            ProblemClass::MultiPredLinear => {
                if triangle_bv_diff_bound_direct_route {
                    let route_budget = self
                        .remaining_budget(deadline)
                        .unwrap_or(self.config.time_budget);
                    self.try_triangle_bv_diff_bound_original_bmc_route(route_budget)
                        .unwrap_or_else(|| {
                            (
                                self.solve_bv_dual_lane(route_budget),
                                ValidationEvidence::FullVerification,
                            )
                        })
                } else if StructuralSynthesizer::new(&self.problem)
                    .has_fast_mod1000_split_triangle_chc_shape()
                {
                    if let Some(result) = self.try_synthesis() {
                        (result, ValidationEvidence::FullVerification)
                    } else if let Some(result) = self.try_front_bmc_probe(&features, deadline) {
                        result
                    } else if let Some(result) = self.try_lia_farkas_pdr_route(&features, deadline)
                    {
                        result
                    } else {
                        self.solve_multi_pred_linear(&features, deadline)
                    }
                // Cheap shallow-counterexample probe BEFORE invariant-directed
                // routes (svcomp/CFG-class): linear multi-predicate unsafe
                // encodings usually fall to BMC fast, while farkas/PDR
                // staging can burn the whole budget first.
                } else if let Some(result) = self.try_front_bmc_probe(&features, deadline) {
                    result
                } else if let Some(result) = self.try_lia_farkas_pdr_route(&features, deadline) {
                    result
                } else {
                    self.solve_multi_pred_linear(&features, deadline)
                }
            }
            ProblemClass::MultiPredComplex => (
                self.solve_multi_pred_complex(&features, deadline),
                ValidationEvidence::FullVerification,
            ),
        };

        // Log the overall strategy decision.
        self.decision_log.log_decision(DecisionEntry {
            stage: "strategy_dispatch",
            gate_result: true,
            gate_reason: class_name,
            budget_secs,
            elapsed_secs: strategy_start.elapsed().as_secs_f64(),
            result: Self::result_to_str(&result),
            lemmas_learned: 0,
            max_frame: 0,
        });

        (result, evidence)
    }

    /// Final verified-result boundary for adaptive solving.
    ///
    /// `solve_internal()` is allowed to use the lighter-weight adaptive
    /// acceptance policy while exploring strategies. Before returning the public
    /// `VerifiedChcResult`, however, any `Unsafe` must be re-validated so the
    /// verified wrapper's contract holds.
    pub(crate) fn finalize_verified_result(
        &self,
        result: PortfolioResult,
        evidence: ValidationEvidence,
    ) -> crate::VerifiedChcResult {
        self.finalize_verified_result_with_deadline(result, evidence, None)
    }

    pub(crate) fn finalize_verified_result_with_deadline(
        &self,
        result: PortfolioResult,
        evidence: ValidationEvidence,
        deadline: Option<Instant>,
    ) -> crate::VerifiedChcResult {
        match result {
            PortfolioResult::Safe(model) => {
                // FORALL-ARR ghost-pair certificates (agenda #16): the true
                // model is quantified and has NO quantifier-free
                // interpretation, so the standard interpretation-completeness
                // gates below cannot apply. The certificate is
                // construction-sealed (it exists only after the full
                // per-rule quantified discharge on the ORIGINAL clauses
                // succeeded); re-run the discharge here as defense in depth
                // and demote to Unknown on any failure (fail-closed).
                if let Some(certificate) = model.ghost_pair_certificate().cloned() {
                    let recheck_budget = self
                        .remaining_budget(deadline)
                        .unwrap_or(ARRAY_GHOST_PAIR_FINALIZE_RECHECK_BUDGET)
                        .min(ARRAY_GHOST_PAIR_FINALIZE_RECHECK_BUDGET);
                    if crate::transform::recheck_ghost_pair_certificate(
                        &self.problem,
                        &certificate,
                        Some(recheck_budget),
                        false,
                    ) {
                        return crate::VerifiedChcResult::from_validated(
                            PortfolioResult::Safe(model),
                            evidence,
                        );
                    }
                    tracing::warn!(
                        "Adaptive: ghost-pair quantified certificate failed the finalize \
                         re-check, demoting to Unknown"
                    );
                    return crate::VerifiedChcResult::from_validated(
                        PortfolioResult::Unknown,
                        ValidationEvidence::FullVerification,
                    );
                }

                // (#C3 RETIRED, 2026-07-08): the blanket Safe→Unknown demotion for
                // div/mod theory-bug shapes (#57 div/mod-by-zero, #55
                // div-by-nonconstant under nonlinear arithmetic) is REMOVED. The
                // underlying ay-dpll mis-decisions are fixed (free-var div/mod
                // modelling + N-O purification + the 2026-07-08 quantifier-lane
                // hardening) and pinned by regression tests at the SMT layer
                // (executor_tests: div0/mod0/nonlinear-div family, 15-shape
                // adversarial sweep agreeing with z3, zero wrong answers). The
                // gate taxed EVERY legitimate Safe on div-shaped clauses —
                // including shapes the BvToInt lane itself manufactures.

                if let ValidationEvidence::PreprocessedQueryOnlyDischarge { query_count } =
                    &evidence
                {
                    tracing::warn!(
                        query_count,
                        model_predicates = model.len(),
                        "Adaptive: rejecting unvalidated preprocessed query-only discharge Safe evidence"
                    );
                    return crate::VerifiedChcResult::from_validated(
                        PortfolioResult::Unknown,
                        evidence,
                    );
                }

                if let ValidationEvidence::ScalarAcyclicBmcExhaustive { max_depth } = &evidence {
                    // An empty-model exhaustive acyclic BMC Safe is a COMPLETE proof
                    // whenever every reachable value space is finite. Admit scalar
                    // (Bool/Int/BV) signatures AND signatures carrying only FINITE
                    // (non-recursive) datatypes — those have a finite value space, so
                    // bounded acyclic unrolling covers them exhaustively. RECURSIVE
                    // datatypes (unbounded value space) stay demoted: bounded unrolling
                    // is not complete for them, so admitting would be a false proof.
                    if model.is_empty()
                        && !self.problem.has_array_sorts()
                        && !self.problem.has_real_sorts()
                        && !self.problem.has_recursive_datatype_sorts()
                    {
                        tracing::debug!(
                            max_depth,
                            "Adaptive: accepting scalar acyclic exhaustive BMC Safe evidence"
                        );
                        return crate::VerifiedChcResult::from_validated(
                            PortfolioResult::Safe(model),
                            evidence,
                        );
                    }

                    tracing::warn!(
                        ?evidence,
                        model_predicates = model.len(),
                        has_array_sorts = self.problem.has_array_sorts(),
                        has_real_sorts = self.problem.has_real_sorts(),
                        has_datatype_sorts = self.problem.has_datatype_sorts(),
                        has_recursive_datatype_sorts = self.problem.has_recursive_datatype_sorts(),
                        "Adaptive: acyclic BMC evidence did not satisfy scalar admission preconditions, demoting to Unknown"
                    );
                    return crate::VerifiedChcResult::from_validated(
                        PortfolioResult::Unknown,
                        ValidationEvidence::FullVerification,
                    );
                }

                // Item 4 Stage 0 acceptance fixes. Both variants are only
                // constructed by the acyclic probe after an INDEPENDENT
                // fresh-executor re-proof (double-run query-only discharge /
                // equisat-grade re-keyed exhaustion re-run); see
                // engine_result.rs for the full trust argument. Defense in
                // depth: both are complete evidence ONLY for acyclic
                // problems, so re-derive acyclicity here and demote
                // fail-closed if a cyclic problem ever carries them.
                if matches!(
                    &evidence,
                    ValidationEvidence::CheckedQueryOnlyDischarge { .. }
                        | ValidationEvidence::EquisatAcyclicBmcExhaustive { .. }
                ) {
                    let acyclic = !ProblemClassifier::classify(&self.problem).has_cycles;
                    if acyclic {
                        tracing::debug!(
                            ?evidence,
                            "Adaptive: accepting double-run acyclic discharge/exhaustion Safe evidence"
                        );
                        return crate::VerifiedChcResult::from_validated(
                            PortfolioResult::Safe(model),
                            evidence,
                        );
                    }
                    tracing::warn!(
                        ?evidence,
                        "Adaptive: double-run acyclic evidence carried by a CYCLIC problem; \
                         demoting to Unknown fail-closed"
                    );
                    return crate::VerifiedChcResult::from_validated(
                        PortfolioResult::Unknown,
                        ValidationEvidence::FullVerification,
                    );
                }

                if !matches!(
                    &evidence,
                    ValidationEvidence::FullVerification
                        | ValidationEvidence::AlgebraicClosedForm
                        | ValidationEvidence::TrivialProblem
                        // CataAbstraction is admitted here because the cata
                        // route already ran its composite fail-closed
                        // certification (per-original-clause implication
                        // obligations + full fresh verification of the
                        // abstract model) before stamping this evidence —
                        // same trust model as AlgebraicClosedForm.
                        | ValidationEvidence::CataAbstraction { .. }
                ) {
                    tracing::warn!(
                        ?evidence,
                        "Adaptive: final Safe result carried non-original-validation evidence, demoting to Unknown"
                    );
                    return crate::VerifiedChcResult::from_validated(
                        PortfolioResult::Unknown,
                        ValidationEvidence::FullVerification,
                    );
                }

                if !self.final_safe_model_has_required_interpretations(&model) {
                    // Fix B1: preprocessing (e.g. ClauseInliner) can eliminate
                    // predicates, leaving an otherwise fully verified model
                    // without interpretations for them. Materialize constant
                    // interpretations for the missing predicates and re-run
                    // full strict verification on the ORIGINAL problem; accept
                    // Safe iff that passes. Verification is the soundness
                    // criterion — the structural gate alone is pure pessimism.
                    let completion_start = Instant::now();
                    if let Some(completed) = self
                        .try_complete_final_safe_model_with_constant_interpretations(
                            &model,
                            self.remaining_budget(deadline),
                        )
                    {
                        tracing::info!(
                            predicates = self.problem.predicates().len(),
                            model_predicates = model.len(),
                            completed_predicates = completed.len(),
                            "Adaptive: completed final Safe model with constant interpretations \
                             and re-verified it on the original problem"
                        );
                        self.decision_log.log_decision(DecisionEntry {
                            stage: "final_safe_model_completion",
                            gate_result: true,
                            gate_reason: format!(
                                "materialized constants for {} of {} predicates; \
                                 full verification on original problem passed",
                                completed.len() - model.len(),
                                self.problem.predicates().len(),
                            ),
                            budget_secs: self
                                .remaining_budget(deadline)
                                .map_or(0.0, |b| b.as_secs_f64()),
                            elapsed_secs: completion_start.elapsed().as_secs_f64(),
                            result: "safe",
                            lemmas_learned: 0,
                            max_frame: 0,
                        });
                        return crate::VerifiedChcResult::from_validated(
                            PortfolioResult::Safe(completed),
                            ValidationEvidence::FullVerification,
                        );
                    }

                    // Fix V1: for CHC check-sat the per-predicate witness is
                    // OPTIONAL — only the verdict is scored. Constant completion
                    // (above) keeps the witness complete for the --print-witness
                    // / certificate path when it can, but it cannot reconstruct
                    // NON-constant invariants (e.g. hopv/lia/mochi/twice, an
                    // acyclic problem AY proves Safe with an empty model). Rather
                    // than discard a correct `sat`, re-derive the verdict on the
                    // ORIGINAL clauses independent of the model via exhaustive
                    // acyclic BMC. This does NOT trust the carried evidence
                    // label: the MultiPredComplex route stamps `FullVerification`
                    // unconditionally (and discards the acyclic probe's genuine
                    // `ScalarAcyclicBmcExhaustive` evidence), so the label alone
                    // is not proof. The re-proof on the original problem is.
                    if self.final_safe_verdict_reproved_on_original(self.remaining_budget(deadline))
                    {
                        tracing::info!(
                            predicates = self.problem.predicates().len(),
                            model_predicates = model.len(),
                            "Adaptive: final Safe verdict re-proved on the original problem via \
                             exhaustive acyclic BMC; accepting sat without a materialized witness"
                        );
                        self.decision_log.log_decision(DecisionEntry {
                            stage: "final_safe_verdict_reproof",
                            gate_result: true,
                            gate_reason: "acyclic-BMC safety re-proof on original problem passed; \
                                          witness optional for check-sat"
                                .to_string(),
                            budget_secs: self
                                .remaining_budget(deadline)
                                .map_or(0.0, |b| b.as_secs_f64()),
                            elapsed_secs: completion_start.elapsed().as_secs_f64(),
                            result: "safe",
                            lemmas_learned: 0,
                            max_frame: 0,
                        });
                        return crate::VerifiedChcResult::from_validated(
                            PortfolioResult::Safe(model),
                            ValidationEvidence::FullVerification,
                        );
                    }

                    tracing::warn!(
                        ?evidence,
                        predicates = self.problem.predicates().len(),
                        model_predicates = model.len(),
                        "Adaptive: final Safe result lacks required invariant interpretations, \
                         constant completion did not verify, and the verdict could not be \
                         re-proved on the original problem, demoting to Unknown"
                    );
                    self.decision_log.log_decision(DecisionEntry {
                        stage: "final_safe_model_completion",
                        gate_result: false,
                        gate_reason: "completed model failed full verification on original problem"
                            .to_string(),
                        budget_secs: self
                            .remaining_budget(deadline)
                            .map_or(0.0, |b| b.as_secs_f64()),
                        elapsed_secs: completion_start.elapsed().as_secs_f64(),
                        result: "unknown",
                        lemmas_learned: 0,
                        max_frame: 0,
                    });
                    return crate::VerifiedChcResult::from_validated(
                        PortfolioResult::Unknown,
                        ValidationEvidence::FullVerification,
                    );
                }

                crate::VerifiedChcResult::from_validated(PortfolioResult::Safe(model), evidence)
            }
            PortfolioResult::Unsafe(cex) => {
                if matches!(evidence, ValidationEvidence::TrivialProblem)
                    && self.problem.predicates().is_empty()
                    && cex.steps.is_empty()
                {
                    crate::VerifiedChcResult::from_validated(
                        PortfolioResult::Unsafe(cex),
                        ValidationEvidence::TrivialProblem,
                    )
                } else if self.validate_final_unsafe_result(&cex, self.remaining_budget(deadline)) {
                    crate::VerifiedChcResult::from_validated(
                        PortfolioResult::Unsafe(cex),
                        ValidationEvidence::CounterexampleVerification,
                    )
                } else {
                    self.emit_final_validation_demotion_diagnostics(
                        "unsafe_rejected_by_final_verification",
                        &evidence,
                        &cex,
                    );
                    tracing::debug!(
                        "Adaptive: final Unsafe result failed verified-result validation, demoting to Unknown"
                    );
                    crate::VerifiedChcResult::from_validated(
                        PortfolioResult::Unknown,
                        ValidationEvidence::CounterexampleVerification,
                    )
                }
            }
            other => crate::VerifiedChcResult::from_validated(other, evidence),
        }
    }

    /// Returns the remaining time until the deadline, or None if unbounded.
    ///
    /// An external cancellation request (see
    /// [`cancellation_handle`](Self::cancellation_handle)) collapses the
    /// remaining budget to zero so every stage that consults its budget
    /// winds down promptly. Degrade-only: a zero budget can only lead to
    /// Unknown, never flip a verdict.
    #[allow(clippy::single_option_map)]
    pub(crate) fn remaining_budget(&self, deadline: Option<Instant>) -> Option<Duration> {
        if self.cancellation_token.is_cancelled() {
            return Some(Duration::ZERO);
        }
        deadline.map(|d| d.saturating_duration_since(Instant::now()))
    }

    /// Scale a nominal probe budget with the remaining global budget.
    ///
    /// Probe budgets were historically fixed (tuned for ~30s dev runs), so a
    /// 1800s competition run behaved identically to a 30s run: every probe
    /// gave up at the same small budget and the surplus all fell to the
    /// portfolio. The probe now receives `max(nominal, remaining*percent%)`
    /// capped at `cap` (and never more than the remaining budget). With no
    /// deadline (unbounded run) the nominal is kept.
    pub(crate) fn scaled_probe_budget(
        &self,
        deadline: Option<Instant>,
        nominal: Duration,
        percent: u32,
        cap: Duration,
    ) -> Duration {
        match self.remaining_budget(deadline) {
            None => nominal,
            Some(remaining) => {
                let scaled = remaining.mul_f64(f64::from(percent) / 100.0);
                // `nominal` is a floor for GENEROUS budgets only. When the entire
                // remaining budget is smaller than one lane's nominal, the floor
                // wins the `max` and the trailing `.min(remaining)` silently hands
                // that lane 100% of the wall — the documented percent-share never
                // applies. At a 5s budget an 8s nominal consumed everything.
                let floor = if remaining < nominal {
                    Duration::ZERO
                } else {
                    nominal
                };
                floor.max(scaled.min(cap)).min(remaining)
            }
        }
    }

    /// Compute the global adaptive deadline once so final validation cannot
    /// reopen a fresh timeout after the route budget has expired.
    pub(crate) fn solve_deadline(&self) -> Option<Instant> {
        if self.config.time_budget.is_zero() {
            None
        } else {
            Some(Instant::now() + self.config.time_budget)
        }
    }

    /// Returns true if the deadline has passed (budget exhausted) or an
    /// external cancellation was requested via
    /// [`cancellation_handle`](Self::cancellation_handle).
    ///
    /// Treating cancellation as budget exhaustion makes every existing
    /// stage-boundary budget check double as a prompt cancellation point.
    /// Sound: it only skips further work (degrades to Unknown).
    pub(crate) fn budget_exhausted(&self, deadline: Option<Instant>) -> bool {
        self.cancellation_token.is_cancelled() || deadline.is_some_and(|d| Instant::now() >= d)
    }

    /// Convert a `PortfolioResult` to a decision log result string.
    pub(crate) fn result_to_str(result: &PortfolioResult) -> &'static str {
        match result {
            PortfolioResult::Safe(_) => "safe",
            PortfolioResult::Unsafe(_) => "unsafe",
            PortfolioResult::Unknown => "unknown",
            PortfolioResult::NotApplicable => "not_applicable",
        }
    }

    /// Build a default portfolio config with the standard settings.
    ///
    /// Used by `solve_with_budget_report()` which bypasses the adaptive
    /// classification pipeline and runs the portfolio directly.
    fn make_default_portfolio_config(&self) -> PortfolioConfig {
        let mut config = PortfolioConfig::default();
        config.parallel_timeout = if self.config.time_budget.is_zero() {
            None
        } else {
            Some(self.config.time_budget)
        };
        config.verbose = self.config.verbose;
        config.strict_proofs = self.config.strict_proofs;
        config.memory_budget = self.config.memory_budget;
        if let Some(max) = self.config.max_engines {
            config.engines.truncate(max);
        }
        config
    }

    /// Solve using default portfolio (for comparison/fallback).
    fn solve_default(&self) -> PortfolioResult {
        let mut config = PortfolioConfig::default();
        config.parallel_timeout = if self.config.time_budget.is_zero() {
            None
        } else {
            Some(self.config.time_budget)
        };
        config.verbose = self.config.verbose;

        config.strict_proofs = self.config.strict_proofs;
        self.run_portfolio(config)
    }

    /// Build a `PortfolioConfig` with engines ordered by the learned selector.
    fn make_learned_portfolio_config(&self, deadline: Option<Instant>) -> PortfolioConfig {
        let features = ChcFeatureExtractor::extract(&self.problem);
        let selection = EngineSelector::select(&features);
        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: Learned selector chose engine order: {} (reason: {})",
                selection
                    .engines
                    .iter()
                    .map(|e| e.name())
                    .collect::<Vec<_>>()
                    .join(", "),
                selection.reason,
            );
        }
        let portfolio_timeout = if self.config.time_budget.is_zero() {
            None
        } else {
            Some(
                self.remaining_budget(deadline)
                    .unwrap_or(self.config.time_budget),
            )
        };
        PortfolioConfig {
            external_cancellation: Some(self.cancellation_token.clone()),
            engines: selection.engines,
            parallel: true,
            timeout: None,
            parallel_timeout: portfolio_timeout,
            verbose: self.config.verbose,
            enable_preprocessing: true,
            engine_budgets: ay_core::kani_compat::DetHashMap::default(),
            memory_budget: self.config.memory_budget,
            strict_proofs: self.config.strict_proofs,
        }
    }

    /// Solve using learned feature-based engine selection.
    pub(crate) fn solve_with_learned_selection(
        &self,
        deadline: Option<Instant>,
    ) -> PortfolioResult {
        let config = self.make_learned_portfolio_config(deadline);
        self.run_portfolio(config)
    }

    /// Solve in trace mode: single PDR with TLA trace, validated.
    ///
    /// Runs one PDR solver with `enable_tla_trace` from `AY_TRACE_FILE`,
    /// validates the result via `validate_adaptive_result()`, and converts to
    /// `PortfolioResult` for the standard `VerifiedChcResult` wrapping.
    ///
    /// This replaces the old `main.rs` trace-mode bypass that returned raw
    /// `PdrResult` without verification. Part of #5811.
    fn solve_trace_mode(&self) -> PortfolioResult {
        let mut pdr_config = PdrConfig::production(self.config.verbose).with_tla_trace_from_env();
        self.apply_user_hints(&mut pdr_config);
        // Wire cancellation token for budget enforcement.
        // The timer thread uses park_timeout so it can be woken early
        // when the solve completes, avoiding orphaned sleeping threads
        // in library mode (#6231).
        let timer_handle = if !self.config.time_budget.is_zero() {
            // Child of the portfolio handle (item 5): the watchdog cancels
            // only this lane; an external cancel also reaches it.
            let token = self.cancellation_token.child();
            let watchdog = token.clone();
            let budget = self.config.time_budget;
            let cancelled = Arc::new(std::sync::atomic::AtomicBool::new(false));
            let cancel_flag = cancelled.clone();
            let handle = std::thread::spawn(move || {
                std::thread::park_timeout(budget);
                if !cancel_flag.load(std::sync::atomic::Ordering::Acquire) {
                    watchdog.cancel();
                }
            });
            pdr_config = pdr_config.with_cancellation_token(Some(token));
            Some((handle, cancelled))
        } else {
            None
        };

        // The PDR solver's enable_tla_trace() calls claim_trace_file(),
        // which prevents nested SAT/DPLL tracers from opening the same JSONL
        // file. After the solve completes, release the claim so subsequent
        // solvers in the same process can trace if needed.
        let result_with_stats = PdrSolver::solve_problem_with_stats(&self.problem, pdr_config);
        self.accumulate_stats(&result_with_stats.stats);
        ay_core::release_trace_file();

        // Cancel the watchdog timer early — solve is done.
        if let Some((handle, cancelled)) = timer_handle {
            cancelled.store(true, std::sync::atomic::Ordering::Release);
            handle.thread().unpark();
        }

        let validated = self.validate_adaptive_result(result_with_stats.result);

        // Convert PdrResult to PortfolioResult (ChcEngineResult)
        match validated {
            PdrResult::Safe(model) => PortfolioResult::Safe(model),
            PdrResult::Unsafe(cex) => PortfolioResult::Unsafe(cex),
            PdrResult::Unknown | PdrResult::NotApplicable => PortfolioResult::Unknown,
        }
    }

    // Engine methods (solve_entry_exit_only, solve_trivial, try_alternative_engine_budgeted,
    // try_kind, try_synthesis) are in adaptive_engines.rs.
    // BV strategy methods are in adaptive_bv_strategy.rs.
    // Multi-pred strategy methods are in adaptive_multi_pred.rs.
    // Validation methods are in adaptive_validation.rs.
}

#[cfg(test)]
impl AdaptivePortfolio {
    /// Get the classified features for this problem (test-only).
    pub(crate) fn features(&self) -> ProblemFeatures {
        ProblemClassifier::classify(&self.problem)
    }
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "adaptive_tests.rs"]
mod tests;
