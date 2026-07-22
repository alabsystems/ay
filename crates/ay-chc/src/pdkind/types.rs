// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PDKIND type definitions: configuration, results, frame elements.

use crate::engine_config::ChcEngineConfig;
use crate::engine_result::ChcEngineResult;
use crate::ChcExpr;
use ay_core::kani_compat::DetHashSet as FxHashSet;

/// How the PDKIND solver manages incremental solving (#8161).
///
/// Replaces the boolean `skip_incremental` field to distinguish between
/// configuration intent (BV needs fresh solving) and runtime degradation
/// (false-UNSAT detected). SingleLoop LIA problems now use `Incremental`
/// instead of being unconditionally forced to `FreshOnly`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IncrementalMode {
    /// Normal incremental solving -- reuse persistent IncrementalQueryContext.
    Incremental,
    /// Always use fresh non-incremental solving (configuration-level).
    /// Reason string explains why (e.g., "BitVector state unsupported").
    FreshOnly(String),
    /// Was incremental, degraded due to runtime issue.
    /// Reason string explains what triggered it (e.g., "false-UNSAT detected").
    Degraded(String),
}

impl IncrementalMode {
    /// Whether this mode skips incremental solving (uses fresh per-query).
    pub(crate) fn skips_incremental(&self) -> bool {
        !matches!(self, Self::Incremental)
    }
}

/// PDKIND solver configuration.
///
/// Internal — only `Default::default()` is used in production.
#[derive(Debug, Clone)]
pub struct PdkindConfig {
    /// Common engine settings (verbose, cancellation).
    pub base: ChcEngineConfig,
    /// Maximum outer PDKIND iterations (default: 1000).
    pub max_iterations: usize,
    /// Maximum induction depth n (default: 100).
    pub max_n: usize,
    /// Maximum reachability unrolling depth (default: 100).
    pub max_reachability_depth: usize,
    /// Maximum reachability solver iterations (default: 1000).
    pub max_reachability_iterations: usize,
    /// Incremental solving mode for k-induction checks (#8161, #6692).
    ///
    /// Controls whether push() uses a persistent IncrementalQueryContext
    /// or creates fresh non-incremental solvers per obligation.
    ///
    /// - `Incremental` (default): reuse persistent solver.
    /// - `FreshOnly(reason)`: always fresh (e.g., BV state unsupported).
    /// - `Degraded(reason)`: was incremental, degraded at runtime after
    ///   false-UNSAT detection (#2675) or validation failure.
    pub incremental_mode: IncrementalMode,
    /// Per-obligation timeout in seconds for k-induction and CTI checks in push().
    /// Applied to both incremental and non-incremental solver paths.
    /// Default: 5s. SingleLoop-encoded problems need longer (60s) because their
    /// k-induction formulas include 10+ boolean location variables and large
    /// ITE expressions (#2765).
    pub per_obligation_timeout_secs: u64,
    /// Whether the problem was preprocessed by BvToBool bit-blasting (#5877).
    /// When true, Bool-sorted state variables are expected and PDKIND uses the
    /// relaxed sort guard (`find_unsupported_transition_state_sort`). When false,
    /// Bool state vars are rejected to prevent false-unsat from SingleLoop
    /// location variables on non-BV problems (#6500).
    pub bv_to_bool_applied: bool,
}

impl PdkindConfig {
    pub(super) const DEFAULT_PER_OBLIGATION_TIMEOUT_SECS: u64 = 5;
    pub(crate) const SINGLE_LOOP_PER_OBLIGATION_TIMEOUT_SECS: u64 = 10;
}

impl Default for PdkindConfig {
    fn default() -> Self {
        Self {
            base: ChcEngineConfig::default(),
            max_iterations: 1000,
            max_n: 100,
            max_reachability_depth: 100,
            max_reachability_iterations: 1000,
            incremental_mode: IncrementalMode::Incremental,
            per_obligation_timeout_secs: Self::DEFAULT_PER_OBLIGATION_TIMEOUT_SECS,
            bv_to_bool_applied: false,
        }
    }
}

/// Result of PDKIND solving — unified with all other CHC engines.
pub type PdkindResult = ChcEngineResult;

/// Internal result type used during PDKIND solving before conversion
/// to the unified `ChcEngineResult`. Only `portfolio::run_pdkind_with_singleloop`
/// uses this raw type for SingleLoop back-translation.
#[derive(Debug, Clone)]
pub(crate) enum RawPdkindResult {
    Safe(PdkindInvariant),
    Unsafe(PdkindCounterexample),
    Unknown,
}

impl std::fmt::Display for RawPdkindResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Safe(inv) => {
                write!(f, "safe ({}-inductive invariant)", inv.induction_depth)
            }
            Self::Unsafe(cex) => {
                write!(f, "unsafe (counterexample at depth {})", cex.steps)
            }
            Self::Unknown => write!(f, "unknown (could not determine)"),
        }
    }
}

/// A k-inductive invariant discovered by PDKIND (internal representation).
#[derive(Debug, Clone)]
pub(crate) struct PdkindInvariant {
    /// The invariant formula (conjunction of lemmas)
    pub formula: ChcExpr,
    /// The induction depth `k` for which this invariant is k-inductive.
    pub induction_depth: usize,
}

/// A counterexample discovered by PDKIND (internal representation).
#[derive(Debug, Clone)]
pub(crate) struct PdkindCounterexample {
    /// Number of steps to reach the bad state
    pub steps: usize,
}

/// Counterexample formula paired with the number of steps to reach it
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct CounterExample {
    /// The formula describing the counterexample states
    pub(super) formula: ChcExpr,
    /// Number of steps needed to reach this counterexample
    pub(super) num_of_steps: usize,
}

/// Element of the induction frame: lemma paired with counterexample
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct IFrameElement {
    /// The lemma (blocking formula)
    pub(super) lemma: ChcExpr,
    /// The counterexample that motivated this lemma
    pub(super) counter_example: CounterExample,
}

/// Induction frame - set of lemma/counterexample pairs
pub(super) type InductionFrame = FxHashSet<IFrameElement>;

/// Result of the PUSH operation
pub(super) struct PushResult {
    /// Updated induction frame
    pub(super) i_frame: InductionFrame,
    /// Newly added elements
    pub(super) new_i_frame: InductionFrame,
    /// Updated reachability bound n
    pub(super) n: usize,
    /// Whether a real counterexample was found
    pub(super) is_invalid: bool,
    /// Number of steps to the counterexample (if invalid)
    pub(super) steps_to_cex: usize,
    /// Whether this push could not complete (conservative Unknown).
    pub(super) is_unknown: bool,
    /// Whether any k-induction check returned Unknown while processing obligations.
    pub(super) has_unknown_kinduction: bool,
    /// Whether ALL k-induction checks timed out (none proved).
    /// When true, frame stability is an artifact of timeouts, not inductiveness.
    pub(super) kinduction_all_timed_out: bool,
}
