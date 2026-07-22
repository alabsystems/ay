// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PDR solver implementation.
//!
//! This is the main PDR (Property-Directed Reachability) / IC3 algorithm implementation.
//! The algorithm maintains frames (over-approximations of reachable states) and
//! refines them by blocking counterexample states using SMT queries.
//!
//! ## Lemma Generalization
//!
//! This implementation uses the "drop literal" technique for lemma generalization.
//! When blocking a state, instead of just negating the exact state formula, we try
//! to find a more general blocking clause by:
//! 1. Extracting conjuncts from the state formula
//! 2. Trying to drop each conjunct while maintaining inductiveness
//! 3. Using the most general lemma that doesn't block initial states

// Complex types for counterexample trace reconstruction
#![allow(clippy::type_complexity)]

/// Gate for incremental PDR (#6358: per-predicate prop_solver).
///
/// When `true` AND `problem_is_pure_lia`, blocking queries use the per-predicate
/// `PredicatePropSolver` (one persistent SAT solver per predicate, Z3 Spacer
/// pattern). Non-pure-LIA problems bypass incremental entirely — no double-solve.
///
/// Originally hardcoded to `false` per #6583: incremental PDR regressed LIA
/// from 39/55 to 28/55 SAT. The regression was LIA-specific (theory lemma
/// scope issues with push/pop in the LIA theory solver).
///
/// #8205: Re-enabled for BV-only problems. BV problems don't have the LIA
/// theory lemma scope issues that caused the original regression. The SAT
/// solver's incremental mode (push/pop) is well-tested for pure boolean +
/// bitvector reasoning, and reusing solver state between PDR queries avoids
/// redundant BV encoding work. This is critical for HWMCC benchmark perf.
mod algebraic;
mod blocking;
pub(super) mod caches;
pub(crate) mod convergence_monitor;
mod core;
mod cube_extraction;
mod diseq_swap;
mod edge_summary;
mod entry_failure;
mod expr;
mod helpers;
mod hyperedge;
pub(super) mod inductiveness;
mod invariant_check;
mod invariant_discovery;
mod invariants;
mod model;
mod model_building;
mod must_reachability;
pub(super) mod prop_solver;
mod solve;
mod startup;
mod stats;
mod strengthen;
mod tla_trace;

#[cfg(test)]
pub(in crate::pdr::solver) mod test_helpers;

use self::helpers::{
    build_canonical_predicate_vars, build_frame_predicate_lemma_counts, build_predicate_users,
    build_push_cache_deps, compute_push_cache_signature, compute_reachable_predicates,
    detect_triangular_pattern,
};

use crate::convex_closure::ConvexClosure;
use crate::farkas::compute_interpolant;
use crate::interpolation::{interpolating_sat_constraints, InterpolatingSatResult};
use crate::problem::{ArrayScalarizationMap, ArrayScalarizedArg};
use crate::proof_interpolation::{
    compute_interpolant_from_lia_farkas, extract_interpolant_from_precomputed_farkas,
};
use crate::smt::{
    PdrExecutorBackend, PersistentExecutorSmtContext, SmtContext, SmtResult, SmtValue,
};
use crate::transform::{TransformMemoryReport, TransformObligation};
use crate::{
    ChcExpr, ChcOp, ChcParser, ChcProblem, ChcResult, ChcSort, ChcVar, HornClause, PredicateId,
};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_sat::TlaTraceWriter;
use std::collections::{BinaryHeap, VecDeque};
use std::fs;
use std::path::Path;
use std::sync::Arc;

#[cfg(test)]
use self::invariants::parity_mod2_opposite_blocking;
use self::invariants::{extract_negated_parity_constraint, extract_parity_constraint};
use super::config::{luby, PdrConfig};
use super::counterexample::{
    Counterexample, CounterexampleStep, DerivationWitness, DerivationWitnessEntry, WitnessBuilder,
};
use super::cube;
use super::derivation::DerivationStore;
use super::frame::{Frame, Lemma, MustSummaries, PdrResult, MAX_GLOBAL_LEMMAS};
use super::generalize_adapter::PdrGeneralizerAdapter;
use super::interpolation_failure::{
    InterpolationDiagnostics, InterpolationFailure, InterpolationStats,
};
use super::lemma_cluster::{filter_out_lit, filter_out_lit_with_eq_retry};
use super::model::{InvariantModel, PredicateInterpretation};
use super::obligation::{PobKind, PriorityPob, ProofObligation};
use super::reach_fact::{ReachFact, ReachFactId, ReachFactStore};
use super::reach_solver::ReachSolverStore;
use super::scc::{tarjan_scc, SCCInfo};
use super::types::{
    BlockResult, BoundType, InitResult, PredecessorState, RelationType, StrengthenResult,
};
use super::verification::CexVerificationResult;
use crate::generalize::{
    ArrayEqualityDropGeneralizer, ArraySelectIndexGeneralizer,
    ArraySelectValueWeakeningGeneralizer, ArrayStoreProjectionGeneralizer,
    BoundExpansionGeneralizer, BvBitDecompositionGeneralizer, BvBitGroupGeneralizer,
    BvFlagGuardGeneralizer, BvMaskGeneralizer, BvPerBitReplacementGeneralizer,
    ConstantSumGeneralizer, DenominatorSimplificationGeneralizer, DropLiteralGeneralizer,
    FarkasGeneralizer, GeneralizerPipeline, ImplicationGeneralizer, InitBoundWeakeningGeneralizer,
    LemmaGeneralizer, LiteralWeakeningGeneralizer, RelationalEqualityGeneralizer,
    RelevantVariableProjectionGeneralizer, SingleVariableRangeGeneralizer, TemplateGeneralizer,
    UnsatCoreGeneralizer,
};

/// Result of checking if a candidate is self-inductive with model extraction.
enum InductiveCheckResult {
    Inductive,
    NotInductive(FxHashMap<String, SmtValue>),
    Unknown,
}

/// Result of attempting to discharge an entry SAT model (Entry-CEGAR).
///
/// Used by `is_entry_inductive` to distinguish:
/// - reachable predecessor states (true violation of entry-inductiveness)
/// - unreachable predecessor states (spurious; refine predecessor frames and retry)
/// - Unknown (conservative: reject)
enum EntryCegarDischarge {
    Reachable,
    Unreachable,
    Unknown,
}

/// Conservative failure classes from `is_entry_inductive`.
///
/// These are tracked as counters for Unknown triage and CHC local-maximum analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum EntryInductiveFailureReason {
    Cancelled,
    HeadInstantiationFailed,
    SatHyperedge,
    UnexpectedSelfEdge,
    CubeExtractionFailed,
    ReachFactIntersection,
    EntryCegarDisabled,
    EntryCegarBudgetExhausted,
    DischargeReachable,
    DischargeUnknown,
    SmtUnknownRejected,
    RefinementLimitExceeded,
}

impl std::fmt::Display for EntryInductiveFailureReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

impl EntryInductiveFailureReason {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Cancelled => "cancelled",
            Self::HeadInstantiationFailed => "head_instantiation_failed",
            Self::SatHyperedge => "sat_hyperedge",
            Self::UnexpectedSelfEdge => "unexpected_self_edge",
            Self::CubeExtractionFailed => "cube_extraction_failed",
            Self::ReachFactIntersection => "reach_fact_intersection",
            Self::EntryCegarDisabled => "entry_cegar_disabled",
            Self::EntryCegarBudgetExhausted => "entry_cegar_budget_exhausted",
            Self::DischargeReachable => "discharge_reachable",
            Self::DischargeUnknown => "discharge_unknown",
            Self::SmtUnknownRejected => "smt_unknown_rejected",
            Self::RefinementLimitExceeded => "refinement_limit_exceeded",
        }
    }
}

/// TLA2 trace-related state for runtime PDR validation.
///
/// Groups the 3 fields needed for TLA2 trace emission into a single struct,
/// reducing PdrSolver field count. Accessed from `tla_trace.rs`, `solve.rs`,
/// and `model.rs`.
#[derive(Default)]
pub(super) struct TracingState {
    /// Optional TLA2 trace writer for runtime validation of PDR transitions.
    pub tla_trace: Option<TlaTraceWriter>,
    /// Snapshot of the currently-active proof obligation's identity fields.
    pub active_pob: Option<(usize, usize, usize)>, // (predicate_index, level, depth)
    /// The current query level being strengthened by the main PDR loop.
    pub query_level: Option<usize>,
}

/// Restart-related state for Luby restarts (#1270).
///
/// Groups the 5 fields needed for the restart mechanism into a single struct,
/// reducing PdrSolver field count. Almost exclusively accessed from `solve.rs`.
pub(super) struct RestartState {
    /// Total lemmas learned since last restart (for Luby restart threshold).
    pub lemmas_since_restart: usize,
    /// Current restart threshold (Luby scaled).
    pub restart_threshold: usize,
    /// Current Luby index (0-indexed, incremented at each restart).
    pub luby_index: u32,
    /// Total restart count (for logging).
    pub restart_count: usize,
    /// Whether `apply_lemma_hints(HintStage::Stuck)` has been called (#2393).
    pub stuck_hints_applied: bool,
}

impl RestartState {
    fn new(restart_threshold_init: usize) -> Self {
        Self {
            lemmas_since_restart: 0,
            restart_threshold: restart_threshold_init,
            luby_index: 0,
            restart_count: 0,
            stuck_hints_applied: false,
        }
    }
}

/// Convergence monitor for detecting PDR stagnation.
///
/// Tracks per-iteration progress metrics (lemma velocity, frame advancement)
/// and detects when the solver is spending time without making progress. The
/// main loop can respond by escalating internal generalization modes before
/// eventually returning `Unknown` under a budget.
///
/// Reference: SATzilla (Xu et al. 2008), MachSMT (Scott et al. 2021) — feature-based
/// algorithm selection. This is the runtime convergence counterpart: instead of
/// selecting statically based on problem features, we monitor convergence during
/// solving and bail early when the current approach stalls.
pub(super) struct ConvergenceMonitor {
    /// Wall-clock time when the solve loop started.
    pub solve_start: ay_core::time::Instant,
    /// Wall-clock time of the most recent frame advancement (push_frame).
    pub last_frame_advance: ay_core::time::Instant,
    /// Total lemma count at the start of each window.
    pub window_lemma_count: usize,
    /// Iteration count at the start of each window.
    pub window_start_iteration: usize,
    /// Number of frames at the start of each window.
    pub window_frame_count: usize,
    /// Number of strengthen() calls that returned Safe or Continue (progress)
    /// in the current window.
    pub window_productive_strengthens: usize,
    /// Number of strengthen() calls total in the current window.
    pub window_total_strengthens: usize,
    /// Cumulative count of stagnation windows detected.
    /// The main loop uses this count for internal mode escalation and eventual
    /// bailout once all escalation levels are exhausted.
    pub consecutive_stagnant_windows: usize,
}

impl ConvergenceMonitor {
    /// Window size in iterations for measuring convergence rate.
    const WINDOW_SIZE: usize = 20;

    /// Maximum consecutive stagnant windows before the monitor reaches its
    /// bailout threshold. The main loop may spend these windows escalating
    /// internal modes before honoring the bailout.
    ///
    /// Raised from 3 to 8: the solve_timeout already enforces the total budget.
    /// Premature stagnation abort causes regressions under high system load
    /// where wall-clock stall detection fires before the solver has had enough
    /// CPU time. The convergence monitor should be a very loose heuristic.
    const MAX_STAGNANT_WINDOWS: usize = 8;

    /// Maximum wall-clock seconds without frame advancement before declaring stagnation.
    /// If PDR hasn't advanced a frame in this many seconds while iterating,
    /// it's likely stuck in a fruitless blocking/rejection cycle.
    ///
    /// Raised from 8 to 30: under high system load (4x CPU oversubscription),
    /// 8 wall-clock seconds may be only 2s of CPU time. PDR should be allowed
    /// to use its full solve_timeout budget. The frame stall is now a last-resort
    /// detector for truly stuck solvers, not a tight gate.
    const FRAME_STALL_SECS: u64 = 30;

    pub(super) fn new() -> Self {
        let now = ay_core::time::Instant::now();
        Self {
            solve_start: now,
            last_frame_advance: now,
            window_lemma_count: 0,
            window_start_iteration: 0,
            window_frame_count: 0,
            window_productive_strengthens: 0,
            window_total_strengthens: 0,
            consecutive_stagnant_windows: 0,
        }
    }

    /// Record a frame advancement event.
    pub(super) fn note_frame_advance(&mut self) {
        self.last_frame_advance = ay_core::time::Instant::now();
    }

    /// Record a strengthen() outcome.
    pub(super) fn note_strengthen(&mut self, productive: bool) {
        self.window_total_strengthens += 1;
        if productive {
            self.window_productive_strengthens += 1;
        }
    }

    /// Restart the active convergence window after an internal mode switch.
    ///
    /// Keeps the cumulative stagnant-window count intact so the main loop can
    /// still tell whether this was the first, second, or third escalation.
    pub(crate) fn note_generalization_escalation(
        &mut self,
        current_iteration: usize,
        current_lemma_count: usize,
        current_frame_count: usize,
    ) {
        self.last_frame_advance = ay_core::time::Instant::now();
        self.window_lemma_count = current_lemma_count;
        self.window_start_iteration = current_iteration;
        self.window_frame_count = current_frame_count;
        self.window_productive_strengthens = 0;
        self.window_total_strengthens = 0;
    }

    /// Elapsed wall-clock time since solve started.
    pub(super) fn elapsed(&self) -> std::time::Duration {
        self.solve_start.elapsed()
    }

    /// Time since last frame advancement.
    pub(super) fn time_since_frame_advance(&self) -> std::time::Duration {
        self.last_frame_advance.elapsed()
    }
}

/// Active generalization strategy controlling how aggressively the pipeline
/// drops conjuncts and applies weakening phases (#7911).
///
/// The strategy is selected by `escalate_generalization_strategy` /
/// `de_escalate_generalization_strategy` based on convergence progress.
/// Higher levels enable more pipeline stages and raise the drop-literal
/// failure limit, trading SMT query cost for stronger generalization.
///
/// Reference: Z3 Spacer uses a similar graduated approach where
/// generalization aggressiveness adapts based on solver progress
/// (`reference/z3/src/muz/spacer/spacer_generalizers.cpp`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum GeneralizationStrategy {
    /// Minimal pipeline: UnsatCore + DropLiteral only, failure_limit=5.
    Conservative,
    /// Standard pipeline: all Phase 0-2 generalizers, failure_limit=10.
    Default,
    /// Extended pipeline: standard + relational generalizers, failure_limit=20.
    Aggressive,
    /// Maximum pipeline: all generalizers, failure_limit=50, two fixpoint passes.
    MaxAggressive,
}

impl GeneralizationStrategy {
    pub(crate) fn drop_literal_failure_limit(self) -> usize {
        match self {
            Self::Conservative => 5,
            Self::Default => 10,
            Self::Aggressive => 20,
            Self::MaxAggressive => 50,
        }
    }
    pub(crate) fn use_early_aggressive_generalizers(self) -> bool {
        !matches!(self, Self::Conservative)
    }
    pub(crate) fn use_relational_generalizers(self) -> bool {
        matches!(self, Self::Aggressive | Self::MaxAggressive)
    }
    pub(crate) fn use_bound_expansion(self) -> bool {
        matches!(self, Self::Default | Self::Aggressive | Self::MaxAggressive)
    }
    pub(crate) fn fixpoint_passes(self) -> usize {
        match self {
            Self::MaxAggressive => 2,
            _ => 1,
        }
    }
    pub(crate) fn from_escalation_level(level: usize) -> Self {
        match level {
            0 => Self::Default,
            1 | 2 => Self::Aggressive,
            _ => Self::MaxAggressive,
        }
    }
}

impl std::fmt::Display for GeneralizationStrategy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Conservative => write!(f, "conservative"),
            Self::Default => write!(f, "default"),
            Self::Aggressive => write!(f, "aggressive"),
            Self::MaxAggressive => write!(f, "max-aggressive"),
        }
    }
}

/// A single strategy change event recorded for post-hoc analysis (#7918).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StrategyEvent {
    /// Solver iteration at which the strategy change occurred.
    pub iteration: usize,
    /// Strategy level *before* the change (0-3).
    pub from_level: usize,
    /// Strategy level *after* the change.
    pub to_level: usize,
    /// `true` for escalation, `false` for de-escalation.
    pub is_escalation: bool,
}

/// Aggregate telemetry for generalization strategy adaptation (#7918).
///
/// Tracks escalation/de-escalation events for data-driven threshold tuning.
#[derive(Debug, Clone, Default)]
pub(crate) struct StrategyTelemetry {
    /// Ordered log of all strategy change events during the solve.
    pub events: Vec<StrategyEvent>,
    /// Total number of escalations.
    pub escalation_count: usize,
    /// Total number of de-escalations.
    pub de_escalation_count: usize,
}

impl StrategyTelemetry {
    /// Record an escalation event.
    pub(crate) fn record_escalation(
        &mut self,
        iteration: usize,
        from_level: usize,
        to_level: usize,
    ) {
        self.escalation_count += 1;
        self.events.push(StrategyEvent {
            iteration,
            from_level,
            to_level,
            is_escalation: true,
        });
    }

    /// Record a de-escalation event.
    pub(crate) fn record_de_escalation(
        &mut self,
        iteration: usize,
        from_level: usize,
        to_level: usize,
    ) {
        self.de_escalation_count += 1;
        self.events.push(StrategyEvent {
            iteration,
            from_level,
            to_level,
            is_escalation: false,
        });
    }
}

/// Actual LIA/Farkas template and certificate admission telemetry.
///
/// These counters are updated at candidate admission and interpolation attempt
/// sites. They are deliberately separate from config booleans so route evidence
/// can distinguish "surface enabled" from "surface exercised".
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(super) struct LiaFarkasTemplateTelemetry {
    pub(super) affine_equalities: usize,
    pub(super) intervals: usize,
    pub(super) difference_bounds: usize,
    pub(super) scaled_linear_combinations: usize,
    pub(super) templates_generated: usize,
    pub(super) template_checks: usize,
    pub(super) farkas_checks: usize,
    pub(super) accepted_lemmas: usize,
    pub(super) rejected_lemmas: usize,
    pub(super) validation_failures: usize,
}

impl LiaFarkasTemplateTelemetry {
    pub(super) fn record_template_candidate(&mut self, kind: crate::farkas::LiaFarkasTemplateKind) {
        self.templates_generated = self.templates_generated.saturating_add(1);
        self.template_checks = self.template_checks.saturating_add(1);
        match kind {
            crate::farkas::LiaFarkasTemplateKind::AffineEquality => {
                self.affine_equalities = self.affine_equalities.saturating_add(1);
            }
            crate::farkas::LiaFarkasTemplateKind::Interval => {
                self.intervals = self.intervals.saturating_add(1);
            }
            crate::farkas::LiaFarkasTemplateKind::DifferenceBound => {
                self.difference_bounds = self.difference_bounds.saturating_add(1);
            }
            crate::farkas::LiaFarkasTemplateKind::ScaledLinearCombination => {
                self.scaled_linear_combinations = self.scaled_linear_combinations.saturating_add(1);
            }
        }
    }

    pub(super) fn record_farkas_check(&mut self) {
        self.farkas_checks = self.farkas_checks.saturating_add(1);
    }

    pub(super) fn record_template_accept(&mut self) {
        self.accepted_lemmas = self.accepted_lemmas.saturating_add(1);
    }

    pub(super) fn record_template_reject(&mut self, validation_failure: bool) {
        self.rejected_lemmas = self.rejected_lemmas.saturating_add(1);
        if validation_failure {
            self.validation_failures = self.validation_failures.saturating_add(1);
        }
    }

    pub(super) fn observed_surface_count(&self) -> usize {
        [
            self.affine_equalities,
            self.intervals,
            self.difference_bounds,
            self.scaled_linear_combinations,
        ]
        .into_iter()
        .filter(|count| *count > 0)
        .count()
    }
}

/// Telemetry counters for solver diagnostics and offline triage.
///
/// Groups write-mostly counters that track interpolation quality,
/// failure modes, and query counts. Reduces PdrSolver field count.
#[derive(Default)]
pub(super) struct PdrTelemetry {
    /// Aggregate success/failure counts for the 5-method interpolation cascade.
    /// Printed in verbose mode at solve end; used for diagnosing interpolation quality.
    pub interpolation_stats: InterpolationStats,
    /// Number of SAT predecessor queries where cube extraction failed.
    pub sat_no_cube_events: usize,
    /// Entry-inductiveness conservative-failure counters by reason class.
    pub entry_inductive_failure_counts: FxHashMap<EntryInductiveFailureReason, usize>,
    /// Counter for verification queries.
    pub verification_queries: usize,
    /// Counter for generalization attempts.
    pub generalization_attempts: usize,
    /// Actual LIA/Farkas template/certificate route counters.
    pub(super) lia_farkas_templates: LiaFarkasTemplateTelemetry,
    /// Entry CEGAR discharge outcomes: [reachable, unreachable, unknown].
    pub entry_cegar_discharge_outcomes: [usize; 3],
    /// Number of transition clauses skipped by BV soft degradation (#5643).
    /// Incremented when budget exhaustion causes a BV transition clause to be
    /// skipped instead of rejected. Non-zero means the model was not fully
    /// verified for inductiveness — only query clauses were hard-checked.
    pub bv_soft_degradation_skips: usize,
    /// Rotation counter for clause iteration order diversity (#5877).
    /// Incremented on each blocking call. Used to rotate the starting index
    /// of clause enumeration so that different transition branches fire across
    /// successive blocking attempts, preventing the "first SAT wins" bias.
    pub clause_rotation_counter: usize,
    /// Strategy adaptation telemetry for data-driven threshold tuning (#7918).
    pub strategy: StrategyTelemetry,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum SymbolicScalarizationIndexKey {
    IntAffine {
        var: ChcVar,
        coefficient: i128,
        offset: i128,
    },
    Raw(ChcExpr),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SimpleIntAffineScalarizationIndex {
    var: Option<ChcVar>,
    coefficient: i128,
    offset: i128,
}

impl SimpleIntAffineScalarizationIndex {
    fn constant(offset: i128) -> Self {
        Self {
            var: None,
            coefficient: 0,
            offset,
        }
    }

    fn variable(var: ChcVar) -> Self {
        Self {
            var: Some(var),
            coefficient: 1,
            offset: 0,
        }
    }

    fn add(self, other: Self) -> Option<Self> {
        self.combine(other, 1)
    }

    fn sub(self, other: Self) -> Option<Self> {
        self.combine(other, -1)
    }

    fn neg(self) -> Option<Self> {
        self.scale(-1)
    }

    fn scale(self, factor: i128) -> Option<Self> {
        Self {
            var: self.var,
            coefficient: self.coefficient.checked_mul(factor)?,
            offset: self.offset.checked_mul(factor)?,
        }
        .normalized()
    }

    fn combine(self, other: Self, other_sign: i128) -> Option<Self> {
        let other = other.scale(other_sign)?;
        let var = match (self.var, other.var) {
            (None, other) => other,
            (this, None) => this,
            (Some(this), Some(other)) if this == other => Some(this),
            (Some(_), Some(_)) => return None,
        };
        Self {
            var,
            coefficient: self.coefficient.checked_add(other.coefficient)?,
            offset: self.offset.checked_add(other.offset)?,
        }
        .normalized()
    }

    fn normalized(mut self) -> Option<Self> {
        if self.coefficient == 0 {
            self.var = None;
        }
        Some(self)
    }
}

/// Degradation counters for fixed-point verification failures.
///
/// Groups the counters and progress signature that track how close the solver
/// is to giving up on model verification. `consecutive_unlearnable` is reset
/// when learning progress changes between failures; the counters are then
/// checked against thresholds and reported
/// in stats/TLA+ traces. Primary consumer: `model.rs` (write),
/// `solve.rs` + `stats.rs` + `tla_trace.rs` (read).
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub(super) struct VerificationProgressSignature {
    /// Total learned lemmas across all frames.
    pub lemma_count: usize,
    /// Total must-summary entries across all levels/predicates.
    pub must_summary_count: usize,
    /// Total stored reach facts.
    pub reach_fact_count: usize,
}

#[derive(Default)]
pub(super) struct VerificationCounters {
    /// Consecutive fixed-point verification failures where we couldn't learn.
    /// Reset to 0 when the progress signature changes; threshold triggers give-up.
    pub consecutive_unlearnable: usize,
    /// Total verification UNKNOWN results (pre_state = Bool(false)).
    /// Never reset; threshold triggers give-up.
    pub total_unknowns: usize,
    /// Total model verification failures across all fixed-point attempts.
    /// Never reset; caps total work spent on model verification.
    pub total_model_failures: usize,
    /// Learning progress at the most recent model verification failure.
    pub last_unlearnable_progress: VerificationProgressSignature,
    /// Frame-1 lemma count at last failed direct safety proof attempt.
    /// Only retry when new lemmas discovered since last failure (#5480).
    pub last_direct_safety_lemma_count: usize,
}

/// Proof obligation queue management.
///
/// Groups the 5 fields for obligation scheduling and deduplication into a single
/// struct, reducing PdrSolver field count. Primary consumer: `core.rs` (enqueue/pop),
/// with `solve.rs` (restart cleanup), `model.rs` (dedup), `stats.rs` and
/// `tla_trace.rs` (size queries).
#[derive(Default)]
pub(super) struct ObligationQueue {
    /// Queue of proof obligations (DFS mode).
    pub deque: VecDeque<ProofObligation>,
    /// Priority queue of obligations (level-priority mode).
    pub heap: BinaryHeap<PriorityPob>,
    /// Monotonic counter for deterministic tie-breaking of obligations.
    pub next_id: u64,
    /// Set when a proof obligation enqueue is dropped due to queue capacity.
    ///
    /// This is a per-strengthen-call degradation signal: once set, the current
    /// strengthen attempt must not return `Safe`/`Continue`, because obligation
    /// exploration became incomplete.
    pub overflowed: bool,
    /// Dedup set for fixed-point verification obligations (#1293).
    /// Keys are (predicate, level, state_hash). Prevents re-queueing identical POBs
    /// when fixed-point verification fails and we enqueue the CEX for predecessor recursion.
    /// Cleared when frames change in a way that could make an obligation learnable.
    pub fixed_point_pob_seen: FxHashSet<(PredicateId, usize, u64)>,
    /// Dedup set for spawned MAY pobs (GSpacer global guidance, agenda #6).
    /// Keys are (predicate, kind, candidate state_hash). Prevents the global
    /// generalizer from re-posting the same subsume/conjecture candidate on
    /// every blocking iteration. Hash collisions are benign (a duplicate MAY
    /// pob is dropped → only completeness of a heuristic, never soundness).
    pub spawned_may_pobs: FxHashSet<(PredicateId, PobKind, u64)>,
}

/// Under-approximation (must-reachability) state for PDR.
///
/// Groups the 5 fields needed for must-reachability tracking: reach facts,
/// reach solvers, must summaries, and derivations. These fields are almost
/// always accessed together (e.g., `insert_reach_fact_bounded` → add to
/// `reach_solvers` → update `must_summaries`). Reduces PdrSolver field count.
///
/// Primary consumers: `must_reachability.rs`, `hyperedge.rs`, `solve.rs`,
/// `model.rs`, `blocking/utils.rs`, `inductiveness/mod.rs`, various
/// `invariant_discovery/` and `expr/sampling/` modules.
pub(super) struct ReachabilityState {
    /// Under-approximations (must summaries) with explicit provenance tracking.
    ///
    /// Stores two categories of entries:
    /// - **Backed**: proven reachable states with a corresponding `ReachFact` / witness chain
    /// - **Unbacked**: heuristic seeds (e.g., loop-closure enrichment) without proof
    ///
    /// Proof-critical consumers (hyperedge UNSAFE detection) use backed-only summaries.
    /// (Spacer technique for faster convergence - see #2247 for provenance design)
    pub must_summaries: MustSummaries,
    /// Concrete reachability facts with justification chains (Spacer reach_fact).
    pub reach_facts: ReachFactStore,
    /// Indicates reach-fact storage saturation; solver must degrade to `Unknown`.
    pub reach_facts_saturated: bool,
    /// Per-predicate incremental reach solvers for fast must-reachability intersection checks.
    /// See the development design notes.
    pub reach_solvers: ReachSolverStore,
    /// Derivation store for tracking multi-body clause progress (Spacer derivation).
    /// See the development design notes.
    pub derivations: DerivationStore,
}

impl ReachabilityState {
    pub(super) fn new() -> Self {
        Self {
            must_summaries: MustSummaries::new(),
            reach_facts: ReachFactStore::new(),
            reach_facts_saturated: false,
            reach_solvers: ReachSolverStore::new(),
            derivations: DerivationStore::new(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum ArraySessionKey {
    HeadFact {
        clause_index: usize,
    },
    SingleBody {
        clause_index: usize,
    },
    PrevLevelInit {
        clause_index: usize,
        fact_index: usize,
    },
}

/// PDR solver state
pub struct PdrSolver {
    /// The CHC problem being solved
    pub(super) problem: ChcProblem,
    /// Problem after query normalization but before PDR-local array scalarization.
    pub(super) model_problem: ChcProblem,
    /// Reversal maps for PDR-local array scalarization steps.
    pub(super) array_scalarization_maps: Vec<ArrayScalarizationMap>,
    /// Configuration
    pub(super) config: PdrConfig,
    /// Consolidated cache subsystem (static lookups + bounded dynamic caches, #3590).
    pub(super) caches: caches::PdrCacheStore,
    /// Frames F_0, F_1, ..., F_N (over-approximations / blocking lemmas)
    pub(super) frames: Vec<Frame>,
    // --- Obligation queue (#3301) ---
    pub(super) obligations: ObligationQueue,
    /// Number of iterations performed
    iterations: usize,
    /// SMT context for queries
    pub(super) smt: SmtContext,
    /// Clause-scoped persistent executor sessions for array-heavy blocking queries (#6047).
    /// LRU-bounded at `MAX_ARRAY_SESSIONS` entries (#6554).
    pub(super) array_clause_sessions:
        caches::LruSolverMap<ArraySessionKey, PersistentExecutorSmtContext>,
    /// Per-predicate lazy array-Skolem tracking state.
    pub(in crate::pdr::solver) array_skolem_state: blocking::ArraySkolemState,
    /// Persistent executor backend for integer-arithmetic PDR queries (#7984).
    /// Wraps `ay-dpll::Executor` with push/pop to maintain theory solver state
    /// across queries. Lazily initialized on first integer-arithmetic query.
    pub(super) executor_backend: Option<PdrExecutorBackend>,
    /// Model-based projection engine (for predecessor generalization)
    mbp: crate::mbp::Mbp,
    // --- Reachability state (must-summaries, reach facts, derivations, #3301) ---
    pub(super) reachability: ReachabilityState,
    // --- Verification degradation counters (#3301) ---
    pub(super) verification: VerificationCounters,
    /// Convex closure computation engine
    convex_closure_engine: ConvexClosure,
    /// SCC information for cyclic predicate handling
    scc_info: SCCInfo,

    // --- Restart state (#1270) ---
    pub(super) restart: RestartState,

    // --- Tracing state (TLA2 runtime validation, #3301) ---
    pub(super) tracing: TracingState,
    /// Deadline computed from `config.solve_timeout` at the start of `solve()`.
    pub(in crate::pdr) solve_deadline: Option<ay_core::time::Instant>,
    /// Total-startup-discovery deadline (inc-12). Set by
    /// `run_startup_discovery` for wide-var linear problem shapes
    /// (lustre-class transition systems), capping the fixpoint + nonfixpoint
    /// discovery passes at a fraction of the engine window so the main PDR
    /// blocking loop is guaranteed real budget. `None` = full discovery
    /// (algebraic/accumulator classes, unbounded solves).
    pub(in crate::pdr) startup_deadline: Option<ay_core::time::Instant>,

    // --- Telemetry counters (#2450, #3301) ---
    pub(super) telemetry: PdrTelemetry,

    // --- Convergence monitoring ---
    /// Tracks per-iteration progress metrics for stagnation detection.
    /// When the solver is running under a portfolio budget and progress stalls,
    /// the main loop can escalate internal modes before eventually returning
    /// `Unknown` so budget can be redirected.
    pub(super) convergence: ConvergenceMonitor,
    /// Current internal generalization escalation level (0-3).
    pub(crate) generalization_escalation_level: usize,
    /// Active generalization strategy (#7911).
    pub(crate) generalization_strategy: GeneralizationStrategy,
    /// Set when `solve()` exits because convergence stagnation exhausted all
    /// available internal mode escalations.
    pub(crate) terminated_by_stagnation: bool,
    /// Lemma quality metrics for convergence health assessment (#7906).
    pub(super) lemma_quality: convergence_monitor::LemmaQualityMetrics,
    /// Problem size hint for adaptive convergence thresholds (#7906).
    pub(super) problem_size_hint: convergence_monitor::ProblemSizeHint,

    // --- Per-predicate persistent solvers (#6358) ---
    /// One persistent incremental solver per predicate. Each `PredicatePropSolver`
    /// owns a single SAT solver with activation-guarded background segments for
    /// different query families (blocking, predecessor, inductiveness). This
    /// matches the Z3 Spacer `prop_solver` pattern: one solver per predicate,
    /// not per query lane.
    ///
    /// Gated by `self.incremental_pdr_enabled()`. When false, all queries go
    /// directly to the non-incremental `self.smt` path.
    /// LRU-bounded at `MAX_PROP_SOLVERS` entries (#6554).
    pub(super) prop_solvers: caches::LruSolverMap<PredicateId, prop_solver::PredicatePropSolver>,

    // --- Problem feature flags (#6366, #6480) ---
    /// Whether the problem has any Array-sorted predicate parameters.
    /// Computed once at construction from predicate sorts. When `false`, all
    /// array-specific overhead (scalarization, `contains_array_ops()` walks,
    /// array clause sessions) is bypassed.
    pub(super) uses_arrays: bool,
    /// Maximum number of Array-sorted parameters across all predicates (#8660).
    /// Used for scaling query timeouts and generalization aggressiveness.
    pub(super) max_array_params: usize,
    /// Property-relevant array indices extracted from query clauses (#8660).
    /// Only indices appearing in the property need to be tracked in blocking cubes.
    pub(in crate::pdr::solver) property_array_indices: blocking::PropertyArrayIndices,
    /// Whether all clause expressions are pure LIA (no ITE, mod, or div) after
    /// preprocessing such as OR/ITE splitting.
    /// When `true`, incremental SAT results from DPLL(T) are trustworthy
    /// for all blocking sites. When `false`, only Unsat is trusted (#6480).
    pub(super) problem_is_pure_lia: bool,
    /// Whether the problem is pure integer arithmetic (LIA + ITE + mod/div, no BV/arrays/UF).
    /// Weaker condition than `problem_is_pure_lia` that still enables incremental PDR.
    /// The original `problem_is_pure_lia` (no ITE/mod/div) was too conservative for
    /// benchmarks like dillig02_m, s_multipl_17, gj2007_m_1/2 where Z3 succeeds (#5970).
    pub(super) problem_is_integer_arithmetic: bool,
    /// Whether the problem uses only bitvector sorts (+ Bool) in predicate parameters
    /// and clause expressions, with no LIA/Real/Array/UF sorts. When `true`,
    /// incremental PDR is safe to use: the #6583 regression was LIA-specific
    /// (theory lemma scope issues), and BV reasoning in the SAT solver's push/pop
    /// incremental mode is well-tested. (#8205)
    pub(super) problem_is_bitvector_only: bool,

    /// Remaining budget for executor cross-checks (#5970 overhead regression).
    /// Cross-checks (#6787) prevent false-UNSAT but add ~50-100ms per query.
    /// Budget starts at 5s and is decremented on each cross-check call.
    /// When exhausted, verification proceeds without cross-checks.
    pub(super) cross_check_budget: std::time::Duration,

    /// True when the startup fixpoint loop detected convergence (frame[0] = frame[1]).
    /// Used by check_invariants_prove_safety to build convergence_proven models
    /// that skip the expensive inductiveness verification cascade. (#5970)
    pub(super) startup_converged: bool,

    /// Count of Safe candidates demoted by strict final validation this solve
    /// (#4751). Non-zero signals that frame[1] carries non-inductive lemmas;
    /// the startup tail then runs a Houdini prune before the main loop.
    pub(super) strict_validation_demotions: u32,

    /// Number of frame[1] lemmas at the moment the startup fixpoint converged.
    /// #4751: later discovery passes (affine kernel, entry-value bounds,
    /// parity) keep adding frame[1] lemmas AFTER convergence; the
    /// convergence_proven fast-path is only sound to claim while frame[1] is
    /// unchanged since the convergence snapshot, otherwise the safety check
    /// must run the full inductive-subset/cascade filtering.
    pub(super) startup_converged_frame1_len: Option<usize>,

    /// Number of frame[1] lemmas after the most recent Houdini prune sweep
    /// (#4751 gj2007_m_3 follow-up). The demotion-triggered prune+retry is
    /// skipped while frame[1] still has this many lemmas — nothing new was
    /// admitted since the last sweep, so re-pruning would only repeat the
    /// same per-lemma SMT checks.
    pub(super) houdini_pruned_frame1_len: Option<usize>,

    /// Invariants that failed entry-inductiveness but may pass after frame
    /// strengthening (#5970 deferred retry). Each entry:
    /// (predicate, formula, target_level, retry_count).
    /// Retried after invariant discovery when frames may have new lemmas.
    pub(super) deferred_entry_invariants: Vec<(PredicateId, ChcExpr, usize, u8)>,

    /// Invariants that failed self-inductiveness but may pass with frame-strengthened
    /// checks after the frame grows. Retried with frame context during startup fixpoint.
    /// Each entry: (predicate, formula, target_level, retry_count).
    pub(super) deferred_self_inductive_invariants: Vec<(PredicateId, ChcExpr, usize, u8)>,

    /// Cache of recently-rejected invariants to avoid rediscovering and re-checking
    /// the same formula that already failed init-validity or self-inductiveness.
    /// Key: (predicate, formula). Cleared on push_frame (level advance) since
    /// frame strengthening may make previously-rejected invariants valid.
    /// Bounded at 512 entries to prevent memory growth (#7006).
    pub(super) rejected_invariants: FxHashSet<(PredicateId, ChcExpr)>,
    /// Pre-elimination error clause constraints (#1362 phases_m).
    pub(super) original_error_constraints: FxHashMap<usize, ChcExpr>,

    /// Deepest depth at which the bounded-BMC cex replay (inc-9) failed for
    /// this solver instance. Witness-free cex verification skips replays at
    /// or below this depth: the replay is cex-content-independent (it only
    /// uses the depth bound), so a failed replay at depth D fails for every
    /// depth ≤ D until the problem or budget changes.
    pub(in crate::pdr) failed_replay_depth: Option<usize>,
}

impl PdrSolver {
    pub(crate) fn array_scalarization_memory_report(&self) -> TransformMemoryReport {
        if self.array_scalarization_maps.is_empty() {
            return TransformMemoryReport::identity();
        }

        let map_count = self.array_scalarization_maps.len();
        let predicate_maps = self
            .array_scalarization_maps
            .iter()
            .map(|map| map.pred_args.len())
            .sum::<usize>();
        let projected_args = self
            .array_scalarization_maps
            .iter()
            .flat_map(|map| map.pred_args.values())
            .flat_map(|args| args.iter())
            .filter(|arg| matches!(arg, ArrayScalarizedArg::Select { .. }))
            .count();
        let (projected_cells, multi_cell_args) = self.symbolic_scalarization_projection_counts();

        TransformMemoryReport::with_original_validation_obligations(
            format!(
                "pdr_array_scalarization(maps={map_count},predicate_maps={predicate_maps},projected_args={projected_args},projected_cells={projected_cells},multi_cell_args={multi_cell_args})"
            ),
            [
                TransformObligation::named("array-scalarization-map"),
                TransformObligation::named("array-key-projection-map"),
                TransformObligation::named("array-model-backtranslation"),
                TransformObligation::named("original-validation-on-safe"),
                TransformObligation::named("original-replay-on-unsafe"),
            ],
        )
        .with_incomplete_unsafe_backtranslation()
    }

    pub(crate) fn array_scalarization_memory_diagnostic(&self) -> Option<String> {
        if self.array_scalarization_maps.is_empty() {
            None
        } else {
            Some(
                self.array_scalarization_memory_report()
                    .diagnostic_summary(),
            )
        }
    }

    pub(crate) fn symbolic_scalarization_projection_counts(&self) -> (usize, usize) {
        let mut seen_cells: FxHashSet<(PredicateId, usize, SymbolicScalarizationIndexKey)> =
            FxHashSet::default();
        let mut per_arg: FxHashMap<(PredicateId, usize), usize> = FxHashMap::default();

        for map in &self.array_scalarization_maps {
            for (predicate, args) in &map.pred_args {
                for arg in args {
                    let ArrayScalarizedArg::Select {
                        original_arg,
                        index,
                    } = arg
                    else {
                        continue;
                    };
                    let Some(index_key) = Self::symbolic_scalarization_index_key(index) else {
                        continue;
                    };
                    let cell_key = (*predicate, *original_arg, index_key);
                    if !seen_cells.insert(cell_key) {
                        continue;
                    }
                    *per_arg.entry((*predicate, *original_arg)).or_default() += 1;
                }
            }
        }
        if seen_cells.is_empty() {
            self.collect_symbolic_projection_counts_from_problem(&mut seen_cells, &mut per_arg);
        }

        let multi_cell_args = per_arg.values().filter(|projected| **projected > 1).count();
        (seen_cells.len(), multi_cell_args)
    }

    fn collect_symbolic_projection_counts_from_problem(
        &self,
        seen_cells: &mut FxHashSet<(PredicateId, usize, SymbolicScalarizationIndexKey)>,
        per_arg: &mut FxHashMap<(PredicateId, usize), usize>,
    ) {
        for clause in self.model_problem.clauses() {
            if let Some(constraint) = &clause.body.constraint {
                for (predicate, args) in &clause.body.predicates {
                    self.collect_symbolic_projection_counts_for_predicate_args(
                        *predicate, args, constraint, seen_cells, per_arg,
                    );
                }
                if let crate::ClauseHead::Predicate(predicate, args) = &clause.head {
                    self.collect_symbolic_projection_counts_for_predicate_args(
                        *predicate, args, constraint, seen_cells, per_arg,
                    );
                }
            }
        }
    }

    fn collect_symbolic_projection_counts_for_predicate_args(
        &self,
        predicate: PredicateId,
        args: &[ChcExpr],
        constraint: &ChcExpr,
        seen_cells: &mut FxHashSet<(PredicateId, usize, SymbolicScalarizationIndexKey)>,
        per_arg: &mut FxHashMap<(PredicateId, usize), usize>,
    ) {
        let Some(predicate_decl) = self.model_problem.predicates().get(predicate.index()) else {
            return;
        };
        for (original_arg, (arg, sort)) in args.iter().zip(&predicate_decl.arg_sorts).enumerate() {
            if !matches!(sort, ChcSort::Array(_, _)) {
                continue;
            }
            let ChcExpr::Var(array_var) = arg else {
                continue;
            };
            Self::collect_symbolic_selects_for_array_arg(
                predicate,
                original_arg,
                array_var,
                constraint,
                seen_cells,
                per_arg,
            );
        }
    }

    fn collect_symbolic_selects_for_array_arg(
        predicate: PredicateId,
        original_arg: usize,
        array_var: &ChcVar,
        expr: &ChcExpr,
        seen_cells: &mut FxHashSet<(PredicateId, usize, SymbolicScalarizationIndexKey)>,
        per_arg: &mut FxHashMap<(PredicateId, usize), usize>,
    ) {
        match expr {
            ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
                if matches!(args[0].as_ref(), ChcExpr::Var(var) if var == array_var) {
                    if let Some(index_key) = Self::symbolic_scalarization_index_key(&args[1]) {
                        let cell_key = (predicate, original_arg, index_key);
                        if seen_cells.insert(cell_key) {
                            *per_arg.entry((predicate, original_arg)).or_default() += 1;
                        }
                    }
                }
                for arg in args {
                    Self::collect_symbolic_selects_for_array_arg(
                        predicate,
                        original_arg,
                        array_var,
                        arg,
                        seen_cells,
                        per_arg,
                    );
                }
            }
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => {
                for arg in args {
                    Self::collect_symbolic_selects_for_array_arg(
                        predicate,
                        original_arg,
                        array_var,
                        arg,
                        seen_cells,
                        per_arg,
                    );
                }
            }
            ChcExpr::ConstArray(_, value) => Self::collect_symbolic_selects_for_array_arg(
                predicate,
                original_arg,
                array_var,
                value,
                seen_cells,
                per_arg,
            ),
            ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::Var(_)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => {}
        }
    }

    fn symbolic_scalarization_index_key(index: &ChcExpr) -> Option<SymbolicScalarizationIndexKey> {
        if index.vars().is_empty() {
            return None;
        }
        if matches!(index.sort(), ChcSort::Int) {
            if let Some(affine) = Self::simple_int_symbolic_scalarization_index(index) {
                return affine
                    .var
                    .map(|var| SymbolicScalarizationIndexKey::IntAffine {
                        var,
                        coefficient: affine.coefficient,
                        offset: affine.offset,
                    });
            }
        }
        Some(SymbolicScalarizationIndexKey::Raw(index.clone()))
    }

    fn simple_int_symbolic_scalarization_index(
        index: &ChcExpr,
    ) -> Option<SimpleIntAffineScalarizationIndex> {
        match index {
            ChcExpr::Int(value) => Some(SimpleIntAffineScalarizationIndex::constant(*value)),
            ChcExpr::Var(v) if matches!(v.sort, ChcSort::Int) => {
                Some(SimpleIntAffineScalarizationIndex::variable(v.clone()))
            }
            ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                Self::simple_int_symbolic_scalarization_index(args[0].as_ref())?.neg()
            }
            ChcExpr::Op(ChcOp::Add, args) if !args.is_empty() => {
                let mut iter = args.iter();
                let first = Self::simple_int_symbolic_scalarization_index(iter.next()?.as_ref())?;
                iter.try_fold(first, |acc, arg| {
                    acc.add(Self::simple_int_symbolic_scalarization_index(arg.as_ref())?)
                })
            }
            ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
                let mut iter = args.iter();
                let first = Self::simple_int_symbolic_scalarization_index(iter.next()?.as_ref())?;
                iter.try_fold(first, |acc, arg| {
                    acc.sub(Self::simple_int_symbolic_scalarization_index(arg.as_ref())?)
                })
            }
            ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
                if let Some(constant) = Self::try_eval_int_scalarization_literal(args[0].as_ref()) {
                    return Self::simple_int_symbolic_scalarization_index(args[1].as_ref())?
                        .scale(constant);
                }
                if let Some(constant) = Self::try_eval_int_scalarization_literal(args[1].as_ref()) {
                    return Self::simple_int_symbolic_scalarization_index(args[0].as_ref())?
                        .scale(constant);
                }
                None
            }
            _ => None,
        }
    }

    fn try_eval_int_scalarization_literal(expr: &ChcExpr) -> Option<i128> {
        match expr {
            ChcExpr::Int(value) => Some(*value),
            ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                Self::try_eval_int_scalarization_literal(args[0].as_ref())?.checked_neg()
            }
            _ => None,
        }
    }

    /// Whether incremental PDR is enabled for this problem instance (#8205).
    ///
    /// Returns `true` for BV-only problems: the original #6583 regression that
    /// disabled incremental PDR was LIA-specific (theory lemma scope issues with
    /// push/pop). BV problems use pure boolean + bitvector SAT reasoning where
    /// incremental push/pop is well-tested, and reusing solver state between PDR
    /// queries avoids redundant BV encoding work.
    ///
    /// Returns `false` for LIA/mixed problems to preserve the #6583 regression fix.
    #[inline]
    pub(super) fn incremental_pdr_enabled(&self) -> bool {
        // Disabled: #8205 enabled incremental PDR for BV-only problems, but
        // the incremental prop_solver path has regressions that cause simple BV
        // counting loops to return Unknown instead of Safe. Reverting to the
        // non-incremental path until the prop_solver issues are fixed.
        false
    }

    /// Escalate the active generalization strategy after convergence stagnation.
    ///
    /// Level 0 is the baseline production profile. Each call moves to the next
    /// more aggressive internal mode and returns `true`. Returns `false` once
    /// the highest configured level has already been reached.
    pub(crate) fn escalate_generalization_strategy(&mut self) -> bool {
        // Respect max_escalation_level cap (#7930). For DT+BV problems,
        // escalation is unproductive — PDR should return Unknown quickly
        // so budget goes to engines better suited for these problems.
        if self.generalization_escalation_level >= self.config.max_escalation_level {
            return false;
        }
        let from_level = self.generalization_escalation_level;
        let next_level = match self.generalization_escalation_level {
            0 => {
                self.config.use_farkas_combination = true;
                self.config.use_range_weakening = true;
                1
            }
            1 => {
                self.config.use_relational_equality = true;
                self.config.use_convex_closure = true;
                2
            }
            2 => {
                self.config.use_negated_equality_splits = true;
                self.config.max_frames = self.config.max_frames.max(200);
                3
            }
            _ => return false,
        };

        self.generalization_escalation_level = next_level;
        self.generalization_strategy = GeneralizationStrategy::from_escalation_level(next_level);

        // Record telemetry (#7918).
        self.telemetry
            .strategy
            .record_escalation(self.iterations, from_level, next_level);

        if self.config.verbose {
            safe_eprintln!(
                "PDR: Escalating generalization strategy to level {} at iteration {} \
                 ({} stagnant windows, {}s since last frame advance): \
                 range_weakening={}, farkas={}, relational_equality={}, \
                 convex_closure={}, negated_equality_splits={}, max_frames={}",
                self.generalization_escalation_level,
                self.iterations,
                self.convergence.consecutive_stagnant_windows,
                self.convergence.time_since_frame_advance().as_secs(),
                self.config.use_range_weakening,
                self.config.use_farkas_combination,
                self.config.use_relational_equality,
                self.config.use_convex_closure,
                self.config.use_negated_equality_splits,
                self.config.max_frames,
            );
        }

        true
    }

    /// De-escalate generalization when near convergence (#7911).
    pub(crate) fn de_escalate_generalization_strategy(&mut self) -> bool {
        if self.generalization_strategy == GeneralizationStrategy::Conservative
            || self.generalization_strategy == GeneralizationStrategy::Default
        {
            return false;
        }
        let from_level = self.generalization_escalation_level;
        let new_level = from_level.saturating_sub(1);
        let new_strategy = if new_level == 0 {
            GeneralizationStrategy::Conservative
        } else {
            GeneralizationStrategy::from_escalation_level(new_level)
        };
        self.generalization_escalation_level = new_level;
        self.generalization_strategy = new_strategy;
        self.telemetry
            .strategy
            .record_de_escalation(self.iterations, from_level, new_level);
        if self.config.verbose {
            safe_eprintln!(
                "PDR: De-escalating generalization to {} (level {}) at iter {} (near-convergence)",
                self.generalization_strategy,
                self.generalization_escalation_level,
                self.iterations,
            );
        }
        true
    }
}

impl Drop for PdrSolver {
    fn drop(&mut self) {
        // Release the TLA trace file claim if we claimed it during
        // enable_tla_trace(). This is defense-in-depth — the adaptive
        // portfolio also releases after solve_problem() — but ensures
        // the claim is freed even on early return or panic (#8673).
        // release_trace_file() is idempotent (atomic store of false).
        if self.tracing.tla_trace.is_some() {
            ay_core::release_trace_file();
        }
        std::mem::take(&mut self.problem).iterative_drop();
        // Iteratively drop all fields that may contain deep ChcExpr trees.
        // original_error_constraints holds cloned error clause constraints
        // which can be as deep as the original problem (#6847).
        for (_, expr) in std::mem::take(&mut self.original_error_constraints) {
            ChcExpr::iterative_drop(expr);
        }
        for (_, expr, _, _) in std::mem::take(&mut self.deferred_entry_invariants) {
            ChcExpr::iterative_drop(expr);
        }
        for (_, expr, _, _) in std::mem::take(&mut self.deferred_self_inductive_invariants) {
            ChcExpr::iterative_drop(expr);
        }
        for (_, expr) in std::mem::take(&mut self.rejected_invariants) {
            ChcExpr::iterative_drop(expr);
        }
    }
}

/// Stub implementations for zone-merged observability methods.
impl PdrSolver {
    /// Emit a lemma lifecycle tracing event (stub).
    pub(super) fn emit_lemma_lifecycle_event(
        &mut self,
        _action: &str,
        _source: &str,
        _predicate: PredicateId,
        _level: usize,
        _formula: &ChcExpr,
    ) {
    }

    /// Try to concretize a proof obligation (stub — #4782).
    pub(super) fn try_concretize_pob(
        &mut self,
        _pob: &ProofObligation,
        _model: &Option<FxHashMap<String, SmtValue>>,
    ) -> bool {
        false
    }

    /// Record a point-block for concretize heuristic (stub — #4782).
    pub(super) fn record_point_block_for_concretize(
        &mut self,
        _predicate: PredicateId,
        _level: usize,
    ) {
    }
}

/// Persistent executor backend methods (#7984).
impl PdrSolver {
    /// Check satisfiability using the persistent executor backend when the problem
    /// is integer arithmetic. Falls back to non-incremental `SmtContext::check_sat()`
    /// for non-integer-arithmetic problems or when the executor returns Unknown.
    pub(super) fn check_sat_via_executor_backend(&mut self, expr: &ChcExpr) -> SmtResult {
        if !self.problem_is_integer_arithmetic {
            self.smt.reset();
            return self.smt.check_sat(expr);
        }
        let timeout = self
            .smt
            .current_timeout()
            .unwrap_or(std::time::Duration::from_secs(5));
        let backend = self
            .executor_backend
            .get_or_insert_with(PdrExecutorBackend::new);
        let result = backend.check_sat(expr, timeout);
        match &result {
            SmtResult::Unknown => {
                // Executor returned Unknown — fall back to fresh non-incremental solve.
                self.smt.reset();
                self.smt.check_sat(expr)
            }
            _ => result,
        }
    }
}

#[cfg(test)]
mod symbolic_scalarization_telemetry_tests {
    use super::*;

    fn solver_with_symbolic_projection_cells(cells: Vec<(usize, ChcExpr)>) -> PdrSolver {
        let mut problem = ChcProblem::new();
        let arr_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
        let inv = problem.declare_predicate("Inv", vec![arr_sort, ChcSort::Int]);
        let original_predicates = problem.predicates().to_vec();

        let mut arg_map: Vec<_> = cells
            .into_iter()
            .map(|(original_arg, index)| ArrayScalarizedArg::Select {
                original_arg,
                index,
            })
            .collect();
        arg_map.push(ArrayScalarizedArg::Original(1));
        let mut pred_args = FxHashMap::default();
        pred_args.insert(inv, arg_map);

        let mut solver = PdrSolver::new(problem, PdrConfig::default());
        solver.array_scalarization_maps = vec![ArrayScalarizationMap {
            original_predicates,
            pred_args,
        }];
        solver
    }

    #[test]
    fn symbolic_scalarization_projection_counts_deduplicate_duplicate_same_index() {
        let idx = ChcExpr::var(ChcVar::new("idx", ChcSort::Int));
        let solver = solver_with_symbolic_projection_cells(vec![(0, idx.clone()), (0, idx)]);

        assert_eq!(solver.symbolic_scalarization_projection_counts(), (1, 0));
    }

    #[test]
    fn symbolic_scalarization_projection_counts_deduplicate_affine_equivalent_indexes() {
        let idx = ChcExpr::var(ChcVar::new("idx", ChcSort::Int));
        let idx_plus_one = ChcExpr::add(idx.clone(), ChcExpr::Int(1));
        let one_plus_idx = ChcExpr::add(ChcExpr::Int(1), idx.clone());
        let two_idx_plus_three =
            ChcExpr::add(ChcExpr::mul(ChcExpr::Int(2), idx.clone()), ChcExpr::Int(3));
        let three_plus_idx_times_two =
            ChcExpr::add(ChcExpr::Int(3), ChcExpr::mul(idx.clone(), ChcExpr::Int(2)));
        let solver = solver_with_symbolic_projection_cells(vec![
            (0, idx),
            (0, idx_plus_one),
            (0, one_plus_idx),
            (0, two_idx_plus_three),
            (0, three_plus_idx_times_two),
        ]);

        assert_eq!(solver.symbolic_scalarization_projection_counts(), (3, 1));
    }
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "../solver_tests/mod.rs"]
mod tests;

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "../solver_tests_entry_domain.rs"]
mod entry_domain_tests;

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "../solver_spot_check_tests.rs"]
mod spot_check_tests;

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "../solver_solve_coverage_tests.rs"]
mod solve_coverage_tests;

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "../solver_entry_failure_stats_tests.rs"]
mod entry_failure_stats_tests;

#[cfg(test)]
mod generalization_strategy_tests {
    use super::GeneralizationStrategy;

    #[test]
    fn test_from_escalation_level() {
        assert_eq!(
            GeneralizationStrategy::from_escalation_level(0),
            GeneralizationStrategy::Default
        );
        assert_eq!(
            GeneralizationStrategy::from_escalation_level(1),
            GeneralizationStrategy::Aggressive
        );
        assert_eq!(
            GeneralizationStrategy::from_escalation_level(3),
            GeneralizationStrategy::MaxAggressive
        );
    }

    #[test]
    fn test_failure_limits_monotonic() {
        let c = GeneralizationStrategy::Conservative.drop_literal_failure_limit();
        let d = GeneralizationStrategy::Default.drop_literal_failure_limit();
        let a = GeneralizationStrategy::Aggressive.drop_literal_failure_limit();
        let m = GeneralizationStrategy::MaxAggressive.drop_literal_failure_limit();
        assert!(c < d && d < a && a < m);
    }

    #[test]
    fn test_pipeline_composition_flags() {
        assert!(!GeneralizationStrategy::Conservative.use_early_aggressive_generalizers());
        assert!(GeneralizationStrategy::Default.use_early_aggressive_generalizers());
        assert!(!GeneralizationStrategy::Conservative.use_relational_generalizers());
        assert!(!GeneralizationStrategy::Default.use_relational_generalizers());
        assert!(GeneralizationStrategy::Aggressive.use_relational_generalizers());
        assert!(!GeneralizationStrategy::Conservative.use_bound_expansion());
        assert!(GeneralizationStrategy::Default.use_bound_expansion());
    }

    #[test]
    fn test_fixpoint_passes() {
        assert_eq!(GeneralizationStrategy::Default.fixpoint_passes(), 1);
        assert_eq!(GeneralizationStrategy::MaxAggressive.fixpoint_passes(), 2);
    }

    #[test]
    fn test_display() {
        assert_eq!(
            format!("{}", GeneralizationStrategy::Conservative),
            "conservative"
        );
        assert_eq!(format!("{}", GeneralizationStrategy::Default), "default");
        assert_eq!(
            format!("{}", GeneralizationStrategy::Aggressive),
            "aggressive"
        );
        assert_eq!(
            format!("{}", GeneralizationStrategy::MaxAggressive),
            "max-aggressive"
        );
    }

    #[test]
    fn test_max_escalation_level_default() {
        use crate::pdr::PdrConfig;
        let config = PdrConfig::default();
        assert_eq!(
            config.max_escalation_level, 3,
            "default should allow all escalation levels"
        );
    }

    #[test]
    fn test_max_escalation_level_dt_cap() {
        use crate::pdr::PdrConfig;
        let config = PdrConfig {
            max_escalation_level: 0,
            ..PdrConfig::default()
        };
        assert_eq!(config.max_escalation_level, 0, "DT cap should be 0");
    }
}
