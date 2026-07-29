// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Main optimization driver for pseudo-Boolean minimization.
//!
//! Implements three optimization strategies:
//! - **Linear search**: iteratively tighten the objective bound (simple, anytime)
//! - **Core-guided**: use UNSAT cores to tighten the lower bound, then binary search
//! - **Binary search**: search the objective interval with monotone queries
//!
//! # References
//! - Fu & Malik, "On Solving the Partial MAX-SAT Problem", 2006
//! - Morgado et al., "Iterative and core-guided MaxSAT solving: A survey", 2013
//! - Niskanen et al., "PB-OLL-RS", PB solver description, 2025

pub(crate) mod am1_bound;
pub(crate) mod bipartite_vertex_cover;
pub(crate) mod bnn_feas;
pub(crate) mod branch_and_bound;
pub(crate) mod clique_certificate;
pub(crate) mod clique_coloring;
pub(crate) mod cutting_planes;
pub(crate) mod dominating_set;
pub(crate) mod farkas_cert;
pub(crate) mod gf2_parity;
pub(crate) mod grid_domination;
pub(crate) mod injcomp;
pub(crate) mod lns;
pub(crate) mod lns2;
pub(crate) mod lp_bound;
pub(crate) mod market_split;
pub(crate) mod matching_cardinality;
pub(crate) mod max_clique;
pub(crate) mod milp_lane;
pub(crate) mod native_oll;
pub(crate) mod pigeonhole;
pub(crate) mod safe_lp_bound;
pub(crate) mod score;
pub mod shared_bounds;
pub(crate) mod sls;
#[cfg(test)]
mod sls_sweep;
pub(crate) mod two_club;
/// Renamed from `score` on the verification branch to avoid colliding with the
/// OPT-NLC product-native primal that took the `score` module path on `main`.
/// This is the NuPBO incremental `Scorer` substrate for the unified linear SLS.
pub(crate) mod unified_score;
pub(crate) mod wbo;
pub(crate) mod wcsp_probe;

use std::collections::{BTreeMap as HashMap, BTreeSet as HashSet};

pub use max_clique::write_max_clique_conflict_row_import_map_csv;

/// Narrow public re-export of the LITERAL `sls::shortfall_for`, the function
/// carrying the `deductive-checks`-verified `ensures(ret >= 0)` contract. The sibling
/// crate `ay-pb-verified` uses it in a runtime smoke test that echoes the proven
/// postcondition on boundary inputs of the real function. `#[doc(hidden)]` keeps
/// it out of the public API surface; it is a zero-cost re-export and does not
/// affect the competition binary.
#[doc(hidden)]
pub use sls::shortfall_for as verified_shortfall_for;

use crate::cdcl::{
    PbCdclAssumptionResult, PbCdclOptimizationCoreEvidence, PbCdclOptimizationCoreProbeResult,
    PbCdclOptimizationCoreWeightedAssumption, PbCdclSolver,
};
use crate::encoding::{encode_totalizer_with_outputs_interruptible, CnfEncoder, EncodedCnf};
use crate::objective_bound::{objective_at_most_constraint, ObjectiveBoundError};
use crate::solver::{eval_objective, objective_range_fits_i64};
use crate::types::{PbConstraint, PbInstance, PbLit, PbObjective, PbRel, PbTerm};
use ay_sat::{AssumeResult, Literal, SatResult, Solver as SatSolver, Variable};

const MAX_CORE_TRIM_SIZE: usize = 128;
const MAX_CORE_TRIM_CHECKS: usize = 32;
const PERSISTENT_BOUND_MIN_TERMS: usize = 32;
const PERSISTENT_BOUND_MAX_TERMS: usize = 256;
const PERSISTENT_BOUND_MAX_TOTAL_WEIGHT: i128 = 4_096;
const PERSISTENT_BOUND_MAX_WORK: u64 = 262_144;
const PERSISTENT_UNIT_BOUND_MAX_CLAUSE_WORK: u64 = 147_456;
const PERSISTENT_BOUND_STOP_POLL_INTERVAL: usize = 64;

/// Percentage-of-memory-limit at which `OptimizationEngine::solve` declines the
/// SAT-encoded optimization *before* its first `clone_for_incremental`.
///
/// Cloning the imported base solver roughly doubles its resident footprint
/// (empirically ~1.8x: e.g. 7.2 GB → 12.8 GB live for the StableMatchings
/// `Init-x2` family), so any run already past ~half the budget would breach the
/// hard 95% guard the instant it clones. 53% is the largest pre-clone fraction
/// that keeps the projected post-clone footprint (`0.53 * 1.8 ≈ 0.95`) at or
/// under the hard guard, while staying a strict no-op for the common case where
/// the base solver is a small fraction of the budget. Soundness is unconditional:
/// declining only returns `Unknown` (the portfolio keeps any earlier incumbent),
/// never a fabricated verdict.
const PRE_CLONE_MEMORY_PERCENT: usize = 53;

/// Optimization strategy used by the driver.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OptStrategy {
    /// Repeatedly tighten the best-known upper bound by one.
    Linear,
    /// Extract disjoint unsatisfiable cores for unit-cost objectives, then refine.
    CoreGuided,
    /// Search the objective interval with monotone upper-bound queries.
    BinarySearch,
}

/// Result of an optimization run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OptResult {
    /// Global optimum proven.
    Optimal(Vec<bool>, i128),
    /// Feasible solution found, but optimality not proven.
    Satisfiable(Vec<bool>, i128),
    /// Base formula is infeasible.
    Infeasible,
    /// No feasible solution was found before interruption or unsupported encoding.
    Unknown,
}

/// Main optimization entry point for PBO/WBO solving.
pub struct OptimizationEngine<'a> {
    base_solver: SatSolver,
    objective: PbObjective,
    base_cnf: EncodedCnf,
    num_pb_vars: u32,
    should_stop: Box<dyn Fn() -> bool + 'a>,
    on_improve: Option<Box<dyn FnMut(i128) + 'a>>,
    last_reported_obj: Option<i128>,
    native_core_mode: NativeCoreMode,
    /// Original PB constraints, used to re-verify a claimed optimum before
    /// returning `OptResult::Optimal`, and to build the LP relaxation used for
    /// the sound LP objective lower bound. Empty when not supplied (verification
    /// is then skipped, since SAT models already satisfy the encoded hard CNF,
    /// and the LP lower bound is unavailable).
    original_constraints: Vec<PbConstraint>,
    /// Optional strategy override. When `Some`, `solve` runs the named strategy
    /// instead of the heuristic `select_strategy()`. Used by the parallel
    /// portfolio to run diverse optimization strategies concurrently. Each
    /// strategy is independently soundness-gated, so forcing one only changes
    /// search order, never the correctness of a reported optimum.
    forced_strategy: Option<OptStrategy>,
    /// Memoized sound LP-relaxation lower bound (in objective units). Computed at
    /// most once because it can be expensive.
    lp_lower_bound_cache: std::cell::RefCell<LpBoundCache>,
}

/// Memo state for the LP relaxation lower bound.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LpBoundCache {
    /// Not yet computed.
    Uncomputed,
    /// Computed; `None` means the LP soundly declined to produce a bound.
    Computed(Option<i128>),
}

#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
pub(crate) struct ObjectiveStats {
    pub(crate) term_count: usize,
    pub(crate) single_lit_terms: usize,
    pub(crate) unit_weight_terms: usize,
    pub(crate) lower_bound: i128,
    pub(crate) upper_bound: i128,
    pub(crate) gap: i128,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum QueryOutcome {
    Sat {
        assignment: Vec<bool>,
        obj_value: i128,
    },
    Unsat,
    Unknown,
    Unsupported,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LowerBoundStatus {
    Complete(i128),
    Interrupted(i128),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CoreGuidedExtraction {
    pub(crate) status: LowerBoundStatus,
    pub(crate) learned_clauses: Vec<Vec<Literal>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
enum NativeCoreMode {
    Enabled,
    DisabledForProofMode,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct NativeCoreGuidedSeed {
    lower_bound: i128,
    core_weight: i128,
    learned_clause: Vec<Literal>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct WeightedSoftLiteral {
    literal: Literal,
    weight: i128,
}

/// Outcome of processing a single UNSAT core inside the stratified OLL loop.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OllCoreOutcome {
    /// Core successfully reformulated; keep iterating.
    Continue,
    /// A non-recoverable condition (overflow, encoding failure, degenerate core)
    /// was hit; return the incumbent as `Satisfiable`.
    Stop,
    /// The core was empty within the current stratum (formula UNSAT with all
    /// assumed softs paid); the caller decides whether to descend or finalize.
    Exhausted,
}

/// Mutable working state of the stratified OLL loop, threaded through the
/// per-round helpers. Owns the single persistent incremental SAT solver.
struct OllState {
    solver: SatSolver,
    /// Active soft literals (objective selectors plus totalizer relaxation
    /// outputs), with their current residual weights.
    softs: Vec<WeightedSoftLiteral>,
    /// Accumulated sound lower bound on the objective.
    lower_bound: i128,
    /// Best proven incumbent assignment.
    best_assignment: Vec<bool>,
    /// Best proven incumbent objective value (a valid upper bound).
    best_value: i128,
    /// Stratification threshold: only softs with `weight >= threshold` are
    /// assumed in the current round.
    threshold: i128,
    /// Reusable assumption buffer.
    assumptions: Vec<Literal>,
}

impl OllState {
    /// Whether stratification should be used at all. A near-uniform weight
    /// distribution (dispersion `< 1`, i.e. all weights equal) gains nothing from
    /// stratification, so the threshold collapses to the minimum and every round
    /// assumes all softs (the classic single-stratum OLL behavior).
    fn stratification_enabled(&self) -> bool {
        let mut min_w = i128::MAX;
        let mut max_w = i128::MIN;
        for soft in &self.softs {
            min_w = min_w.min(soft.weight);
            max_w = max_w.max(soft.weight);
        }
        // Dispersion measured as max - min; `< 1` means a single weight value.
        max_w.saturating_sub(min_w) >= 1
    }

    /// Sets the initial stratification threshold to the maximum soft weight (so the
    /// first rounds target the highest-value cores). When stratification is disabled
    /// (uniform weights) the threshold drops to the minimum so all softs are assumed.
    fn initialize_threshold(&mut self) {
        if !self.stratification_enabled() {
            self.threshold = self.min_soft_weight();
            return;
        }
        self.threshold = self.softs.iter().map(|s| s.weight).max().unwrap_or(1);
    }

    fn min_soft_weight(&self) -> i128 {
        self.softs.iter().map(|s| s.weight).min().unwrap_or(0)
    }

    /// Fills `assumptions` with the no-cost polarity of every soft at or above the
    /// current threshold. Returns `true` when *all* remaining softs are included
    /// (full stratum), which is the only situation in which a SAT result proves
    /// optimality.
    fn collect_stratum_assumptions(&mut self) -> bool {
        self.assumptions.clear();
        let mut included = 0usize;
        for soft in &self.softs {
            if soft.weight >= self.threshold {
                self.assumptions.push(soft.literal.negated());
                included += 1;
            }
        }
        if included == 0 {
            // Threshold overshot every remaining soft (can happen after weight-split
            // changes the maximum). Collapse to the minimum so the stratum is full.
            self.threshold = self.min_soft_weight();
            self.assumptions
                .extend(self.softs.iter().map(|s| s.literal.negated()));
            return true;
        }
        included == self.softs.len()
    }

    /// Lowers the stratification threshold using the CASHWMaxSAT diminishing rule:
    /// the next threshold is `max(floor(avg_weight_below), floor(max_weight_below/2)+1)`,
    /// clamped to strictly decrease and to never drop below the minimum remaining
    /// weight. Considers only softs *strictly below* the current threshold (those not
    /// yet admitted), so the new threshold always admits new softs.
    fn lower_threshold(&mut self) {
        let min_w = self.min_soft_weight();
        if self.threshold <= min_w {
            // Already at the bottom; nothing left to descend to.
            self.threshold = min_w;
            return;
        }

        let mut sum: i128 = 0;
        let mut count: i128 = 0;
        let mut max_below: i128 = 0;
        for soft in &self.softs {
            if soft.weight < self.threshold {
                sum += soft.weight;
                count += 1;
                max_below = max_below.max(soft.weight);
            }
        }
        if count == 0 {
            self.threshold = min_w;
            return;
        }
        let avg = sum / count;
        let half_plus = max_below / 2 + 1;
        let mut next = avg.max(half_plus);
        // Must strictly decrease and admit at least the new max-below soft.
        next = next.min(self.threshold.saturating_sub(1)).max(min_w);
        self.threshold = next;
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct NormalizedObjectiveBounds {
    lower: i128,
    upper: i128,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ObjectiveLiteral {
    ConstantFalse,
    ConstantTrue,
    Literal(Literal),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ProductLiteral {
    ConstantFalse,
    Factors(Vec<i32>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BoundEncodingError {
    UnsupportedCoefficient,
    UnsupportedBound,
    Interrupted,
}

impl From<ObjectiveBoundError> for BoundEncodingError {
    fn from(error: ObjectiveBoundError) -> Self {
        match error {
            ObjectiveBoundError::Coefficient => Self::UnsupportedCoefficient,
            ObjectiveBoundError::Bound => Self::UnsupportedBound,
        }
    }
}

impl<'a> OptimizationEngine<'a> {
    /// Creates a new optimization engine.
    pub fn new<F>(
        solver: SatSolver,
        objective: PbObjective,
        base_cnf: EncodedCnf,
        num_pb_vars: u32,
        should_stop: F,
    ) -> Self
    where
        F: Fn() -> bool + 'a,
    {
        Self {
            base_solver: solver,
            objective,
            base_cnf,
            num_pb_vars,
            should_stop: Box::new(should_stop),
            on_improve: None,
            last_reported_obj: None,
            native_core_mode: NativeCoreMode::Enabled,
            original_constraints: Vec::new(),
            forced_strategy: None,
            lp_lower_bound_cache: std::cell::RefCell::new(LpBoundCache::Uncomputed),
        }
    }

    /// Forces a specific optimization strategy, overriding `select_strategy()`.
    ///
    /// Each strategy (`Linear`, `CoreGuided`/OLL, `BinarySearch`) is
    /// independently soundness-gated: a reported `Optimal` is re-verified against
    /// the original PB constraints regardless of strategy. Forcing one therefore
    /// only changes which search runs, never whether its answer is correct. This
    /// is the diversity lever used by the parallel portfolio.
    pub fn set_forced_strategy(&mut self, strategy: OptStrategy) {
        self.forced_strategy = Some(strategy);
    }

    /// Supplies the original PB constraints so a claimed optimum can be
    /// re-verified (soundness gate) before it is reported as `Optimal`.
    pub fn set_original_constraints(&mut self, constraints: Vec<PbConstraint>) {
        self.original_constraints = constraints;
        // The LP relaxation depends on the constraints; invalidate any memo.
        self.lp_lower_bound_cache.replace(LpBoundCache::Uncomputed);
    }

    #[cfg(test)]
    fn disable_native_core_evidence_for_proof_mode(&mut self) {
        self.native_core_mode = NativeCoreMode::DisabledForProofMode;
    }

    /// Installs an anytime improvement callback.
    pub fn set_on_improve<F>(&mut self, on_improve: F)
    where
        F: FnMut(i128) + 'a,
    {
        self.on_improve = Some(Box::new(on_improve));
    }

    /// Installs an anytime improvement callback.
    pub fn on_improve<F>(&mut self, on_improve: F)
    where
        F: FnMut(i128) + 'a,
    {
        self.set_on_improve(on_improve);
    }

    /// Clears the anytime improvement callback.
    pub fn clear_on_improve(&mut self) {
        self.on_improve = None;
    }

    /// Selects a strategy from objective structure and bound width.
    #[must_use]
    pub fn select_strategy(&self) -> OptStrategy {
        let stats = self.objective_stats();
        let base_var_count = match usize::try_from(self.base_cnf.num_vars) {
            Ok(value) => value,
            Err(_) => usize::MAX,
        };
        let raw_scale = self
            .base_cnf
            .clauses
            .len()
            .max(stats.term_count)
            .max(base_var_count);
        let structural_scale = i128::try_from(raw_scale).unwrap_or(i128::MAX);

        if stats.term_count <= 16 {
            return OptStrategy::Linear;
        }

        let normalized_weighted = self.normalized_weighted_literals();
        if let Some((weighted_literals, _)) = &normalized_weighted {
            // OLL (the CoreGuided path) is now a genuine RC2-style loop, so route
            // weighted-soft objectives with enough soft structure to it. This is
            // the main lever for the OPT-LIN / PARTIAL / SOFT optimization tracks.
            if weighted_literals.len() >= 24 {
                return OptStrategy::CoreGuided;
            }
        } else if stats.term_count >= 64 && stats.single_lit_terms == stats.term_count {
            return OptStrategy::CoreGuided;
        }

        let effective_gap = normalized_weighted
            .as_ref()
            .and_then(|(weighted_literals, offset)| {
                normalized_objective_bounds_from_weighted_literals(weighted_literals, *offset)
            })
            .map_or(stats.gap, |bounds| {
                stats
                    .gap
                    .min(saturating_i128_to_i64((bounds.upper - bounds.lower).max(0)))
            });

        // A wide objective interval with real weighted-soft structure is exactly
        // where core-guided search dominates monotone binary search; keep
        // BinarySearch only for objectives that lack assumable soft structure.
        if effective_gap >= 256 || effective_gap >= structural_scale.saturating_mul(8) {
            if normalized_weighted
                .as_ref()
                .is_some_and(|(weighted_literals, _)| weighted_literals.len() >= 8)
            {
                return OptStrategy::CoreGuided;
            }
            return OptStrategy::BinarySearch;
        }

        OptStrategy::Linear
    }

    /// Solves the optimization problem using the selected strategy.
    pub fn solve(&mut self) -> OptResult {
        self.last_reported_obj = None;
        if !objective_range_fits_i64(&self.objective) {
            return OptResult::Unknown;
        }

        // PRE-CLONE MEMORY BACKPRESSURE (fail-closed, sound).
        //
        // Every optimization strategy's first act is `solve_base_query`, which
        // calls `base_solver.clone_for_incremental()`. On a wide instance the
        // imported base solver can already occupy a large fraction of the process
        // memory budget (measured: ~7 GB of a ~9 GB effective limit for the
        // StableMatchings `Init-x2` family), and cloning it roughly *doubles* its
        // resident footprint in a single allocation — a burst no per-conflict or
        // watchdog poll can interrupt mid-flight, so it OOM-kills the process
        // before any incumbent is found. When current usage is already past a
        // conservative fraction of the limit (so the imminent clone would breach
        // the hard 95% guard), decline this SAT-encoded optimization up front and
        // return `Unknown`. The portfolio then keeps whatever incumbent earlier
        // phases produced; UNKNOWN is always sound (it never fabricates a
        // verdict), and a clean UNKNOWN strictly beats an OOM-kill that loses the
        // whole worker. Strict no-op when no limit is set or usage is low, so
        // normal instances are unaffected.
        if ay_sys::process_memory_exceeded_at_percent(PRE_CLONE_MEMORY_PERCENT) {
            return OptResult::Unknown;
        }

        let strategy = self
            .forced_strategy
            .unwrap_or_else(|| self.select_strategy());
        match strategy {
            OptStrategy::Linear => linear::solve(self),
            OptStrategy::CoreGuided => core_guided::solve(self),
            OptStrategy::BinarySearch => binary_search::solve(self),
        }
    }

    pub(crate) fn objective_stats(&self) -> ObjectiveStats {
        let mut single_lit_terms = 0usize;
        let mut unit_weight_terms = 0usize;
        let mut lower_bound = 0i128;
        let mut upper_bound = 0i128;

        for term in &self.objective.terms {
            if term.lits.len() == 1 {
                single_lit_terms += 1;
                if term.coeff.unsigned_abs() == 1 {
                    unit_weight_terms += 1;
                }
            }

            // Saturating: these are heuristic summaries, and saturation is in the
            // SOUND direction (`lower_bound` only more negative, `upper_bound` only
            // more positive). The soundness-critical bounds use checked arithmetic
            // in `normalized_weighted_literals` and fail closed on overflow.
            if term.coeff < 0 {
                lower_bound = lower_bound.saturating_add(term.coeff);
            } else {
                upper_bound = upper_bound.saturating_add(term.coeff);
            }
        }

        let gap = upper_bound.saturating_sub(lower_bound).max(0);
        ObjectiveStats {
            term_count: self.objective.terms.len(),
            single_lit_terms,
            unit_weight_terms,
            lower_bound: saturating_i128_to_i64(lower_bound),
            upper_bound: saturating_i128_to_i64(upper_bound),
            gap: saturating_i128_to_i64(gap),
        }
    }

    fn objective_lower_bound(&self) -> i128 {
        let stats = self.objective_stats();
        let structural = self.objective_lower_bound_from_stats(stats);
        // This accessor feeds standalone floors (linear search, binary_refine),
        // never an additive core accumulation, so folding in the LP bound is safe.
        self.combined_objective_lower_bound(structural)
    }

    /// Structural lower bound on the objective.
    ///
    /// This is the bound the core-guided (OLL) loop *seeds* its accumulation from
    /// and that linear / binary search use as a floor. It deliberately does **not**
    /// fold in the LP lower bound: OLL adds extracted core weights on top of this
    /// seed, and the LP bound can already account for the same cost, so seeding OLL
    /// with it would double-count and overshoot the optimum. The LP bound is
    /// instead combined as a separate *terminal* clamp via
    /// [`Self::combined_objective_lower_bound`].
    fn objective_lower_bound_from_stats(&self, stats: ObjectiveStats) -> i128 {
        self.normalized_objective_bounds()
            .map_or(stats.lower_bound, |bounds| {
                stats.lower_bound.max(bounds.lower)
            })
    }

    /// Terminal lower bound: the larger of the structural bound and the sound LP
    /// relaxation bound. Safe to use anywhere a *standalone* lower bound is needed
    /// for the optimality proof (linear / binary search floors, OLL's terminal
    /// optimality check) because both inputs are independently sound lower bounds
    /// on the objective and the LP bound is never *added* to a core accumulation.
    fn combined_objective_lower_bound(&self, structural: i128) -> i128 {
        match self.lp_objective_lower_bound() {
            Some(lp_lb) => structural.max(lp_lb),
            None => structural,
        }
    }

    /// Sound LP-relaxation lower bound on the objective, memoized.
    ///
    /// Returns `Some(lb)` with the guarantee `lb <= IntOpt` (see
    /// [`crate::optimize::lp_bound`]), or `None` when no constraints are available
    /// (so the LP cannot tighten anything beyond the structural bound) or the LP
    /// declined to produce a bound (too large / degenerate / interrupted).
    ///
    /// # Soundness
    /// The returned value is always `<= ` the true integer optimum, so taking the
    /// `max` with the structural lower bound can never overshoot the optimum. The
    /// downstream `verify_optimum` gate still re-checks every claimed optimum.
    fn lp_objective_lower_bound(&self) -> Option<i128> {
        if let LpBoundCache::Computed(cached) = *self.lp_lower_bound_cache.borrow() {
            return cached;
        }
        let computed = self.compute_lp_objective_lower_bound();
        self.lp_lower_bound_cache
            .replace(LpBoundCache::Computed(computed));
        computed
    }

    fn compute_lp_objective_lower_bound(&self) -> Option<i128> {
        // Without the original constraints the LP relaxation has no rows to
        // tighten the bound past the trivial structural one, so skip.
        if self.original_constraints.is_empty() {
            return None;
        }
        let should_stop = &self.should_stop;
        lp_bound::lp_lower_bound(
            &self.objective,
            &self.original_constraints,
            self.num_pb_vars,
            &|| should_stop(),
        )
    }

    pub(crate) fn solve_base_query(&self) -> QueryOutcome {
        let mut solver = self.base_solver.clone_for_incremental();
        self.solve_solver(&mut solver)
    }

    #[cfg(test)]
    pub(crate) fn solve_upper_bound_query(&self, upper_bound: i128) -> QueryOutcome {
        let mut session = self.upper_bound_query_session(&[]);
        session.solve(self, upper_bound)
    }

    fn upper_bound_query_session(
        &self,
        learned_clauses: &[Vec<Literal>],
    ) -> UpperBoundQuerySession {
        UpperBoundQuerySession::new(self, learned_clauses)
    }

    fn solve_solver_with_assumptions(
        &self,
        solver: &mut SatSolver,
        assumptions: &[Literal],
    ) -> QueryOutcome {
        let should_stop = &self.should_stop;
        match solver
            .solve_with_assumptions_interruptible(assumptions, should_stop)
            .into_inner()
        {
            AssumeResult::Sat(model) => {
                let assignment = self.project_assignment(model);
                let obj_value = eval_objective(&self.objective, &assignment);
                QueryOutcome::Sat {
                    assignment,
                    obj_value,
                }
            }
            AssumeResult::Unsat(_, _) => QueryOutcome::Unsat,
            AssumeResult::Unknown => QueryOutcome::Unknown,
            #[allow(unreachable_patterns)]
            _ => QueryOutcome::Unknown,
        }
    }

    fn upper_bound_constraint(
        &self,
        upper_bound: i128,
    ) -> Result<PbConstraint, BoundEncodingError> {
        objective_at_most_constraint(&self.objective, upper_bound).map_err(Into::into)
    }

    /// Encodes the objective-at-most-`upper_bound` row, threading the
    /// caller's session-level gap-row BDD pool through the encoder (see
    /// [`crate::encoding::BDD_GAP_NODE_POOL`]). Returns the bound CNF and the
    /// depleted pool, which the caller must persist into the next probe's
    /// encode: the probe loop appends every bound CNF into ONE persistent
    /// solver behind a never-removed activation literal, so a fresh pool per
    /// probe would compound BDD-sized bound encodings without bound.
    fn build_upper_bound_cnf(
        &self,
        upper_bound: i128,
        bdd_gap_pool: u64,
    ) -> Result<(EncodedCnf, u64), BoundEncodingError> {
        if self.objective.terms.is_empty() {
            return Ok((
                EncodedCnf {
                    num_vars: self.num_pb_vars,
                    clauses: if upper_bound >= 0 {
                        Vec::new()
                    } else {
                        vec![Vec::new()]
                    },
                },
                bdd_gap_pool,
            ));
        }

        let constraint = self.upper_bound_constraint(upper_bound)?;
        let instance = PbInstance {
            num_vars: self.num_pb_vars,
            num_constraints: 1,
            constraints: vec![constraint],
            objective: None,
        };
        let should_stop = &self.should_stop;
        CnfEncoder::encode_instance_interruptible_with_gap_pool(
            &instance,
            &mut || should_stop(),
            bdd_gap_pool,
        )
        .ok_or(BoundEncodingError::Interrupted)
    }

    pub(crate) fn extract_core_guided_state(&self) -> CoreGuidedExtraction {
        self.extract_weighted_core_guided_state()
            .unwrap_or_else(|| CoreGuidedExtraction {
                status: LowerBoundStatus::Interrupted(self.objective_stats().lower_bound),
                learned_clauses: Vec::new(),
            })
    }

    pub(crate) fn binary_refine(
        &mut self,
        best_assignment: Vec<bool>,
        best_value: i128,
        lower_bound: i128,
    ) -> OptResult {
        self.binary_refine_with_clauses(best_assignment, best_value, lower_bound, &[])
    }

    pub(crate) fn binary_refine_with_clauses(
        &mut self,
        mut best_assignment: Vec<bool>,
        mut best_value: i128,
        lower_bound: i128,
        learned_clauses: &[Vec<Literal>],
    ) -> OptResult {
        let mut low = lower_bound
            .max(self.objective_lower_bound())
            .min(best_value);
        if best_value <= low {
            return OptResult::Optimal(best_assignment, best_value);
        }

        let Some(mut high) = best_value.checked_sub(1) else {
            return OptResult::Optimal(best_assignment, best_value);
        };

        let mut query_session = self.upper_bound_query_session(learned_clauses);
        while low <= high {
            let probe = midpoint(low, high);
            match query_session.solve(self, probe) {
                QueryOutcome::Sat {
                    assignment,
                    obj_value,
                } => {
                    if obj_value >= best_value {
                        return OptResult::Satisfiable(best_assignment, best_value);
                    }

                    best_value = obj_value;
                    best_assignment = assignment;
                    self.report_improvement(best_value);
                    if best_value <= low {
                        return OptResult::Optimal(best_assignment, best_value);
                    }
                    if self.should_stop_now() {
                        return OptResult::Satisfiable(best_assignment, best_value);
                    }

                    let Some(next_high) = best_value.checked_sub(1) else {
                        return OptResult::Optimal(best_assignment, best_value);
                    };
                    high = next_high.min(probe.saturating_sub(1));
                }
                QueryOutcome::Unsat => {
                    let Some(next_low) = probe.checked_add(1) else {
                        return OptResult::Optimal(best_assignment, best_value);
                    };
                    low = next_low;
                }
                QueryOutcome::Unknown | QueryOutcome::Unsupported => {
                    return OptResult::Satisfiable(best_assignment, best_value);
                }
            }
        }

        OptResult::Optimal(best_assignment, best_value)
    }

    pub(crate) fn report_improvement(&mut self, obj_value: i128) {
        let should_report = match self.last_reported_obj {
            Some(prev) => obj_value < prev,
            None => true,
        };

        if should_report {
            if let Some(callback) = self.on_improve.as_mut() {
                callback(obj_value);
            }
            self.last_reported_obj = Some(obj_value);
        }
    }

    pub(crate) fn should_stop_now(&self) -> bool {
        (self.should_stop)()
    }

    /// Soundness gate: verify that `assignment` is a genuine optimum of value
    /// `claimed_value` before it may be reported as `OptResult::Optimal`.
    ///
    /// Checks (any failure fails the gate, the caller then reports the incumbent
    /// as merely `Satisfiable`):
    /// - `eval_objective(assignment) == claimed_value` (objective is exact),
    /// - every supplied original constraint is satisfied,
    /// - `lower_bound <= claimed_value <= upper_bound` (the proven bracket holds).
    pub(crate) fn verify_optimum(
        &self,
        assignment: &[bool],
        claimed_value: i128,
        lower_bound: i128,
        upper_bound: i128,
    ) -> bool {
        if eval_objective(&self.objective, assignment) != claimed_value {
            return false;
        }
        if claimed_value < lower_bound || claimed_value > upper_bound {
            return false;
        }
        if !crate::eval::verify_all_constraints(&self.original_constraints, assignment) {
            return false;
        }
        true
    }

    fn solve_solver(&self, solver: &mut SatSolver) -> QueryOutcome {
        let should_stop = &self.should_stop;
        match solver.solve_interruptible(should_stop).into_inner() {
            SatResult::Sat(model) => {
                let assignment = self.project_assignment(model);
                let obj_value = eval_objective(&self.objective, &assignment);
                QueryOutcome::Sat {
                    assignment,
                    obj_value,
                }
            }
            SatResult::Unsat(_) => QueryOutcome::Unsat,
            SatResult::Unknown => QueryOutcome::Unknown,
            #[allow(unreachable_patterns)]
            _ => QueryOutcome::Unknown,
        }
    }

    fn project_assignment(&self, mut model: Vec<bool>) -> Vec<bool> {
        let target_len = match usize::try_from(self.num_pb_vars) {
            Ok(value) => value,
            Err(_) => return model,
        };

        if model.len() < target_len {
            model.resize(target_len, false);
        } else {
            model.truncate(target_len);
        }
        model
    }

    fn add_encoded_cnf_with_fresh_aux(
        &self,
        solver: &mut SatSolver,
        cnf: &EncodedCnf,
        activation: Option<Literal>,
    ) -> AddCnfOutcome {
        let aux_vars = match self.allocate_aux_vars_for_cnf(solver, cnf) {
            Ok(aux_vars) => aux_vars,
            Err(outcome) => return outcome,
        };

        self.add_encoded_cnf_with_aux_vars(solver, cnf, activation, &aux_vars)
    }

    fn allocate_aux_vars_for_cnf(
        &self,
        solver: &mut SatSolver,
        cnf: &EncodedCnf,
    ) -> Result<Vec<Variable>, AddCnfOutcome> {
        let extra_aux = cnf.num_vars.saturating_sub(self.num_pb_vars);
        let extra_aux_len = match usize::try_from(extra_aux) {
            Ok(value) => value,
            Err(_) => return Err(AddCnfOutcome::Unsupported),
        };

        let mut aux_vars = Vec::with_capacity(extra_aux_len);
        for _ in 0..extra_aux_len {
            aux_vars.push(solver.new_var());
        }

        Ok(aux_vars)
    }

    fn add_encoded_cnf_with_aux_vars(
        &self,
        solver: &mut SatSolver,
        cnf: &EncodedCnf,
        activation: Option<Literal>,
        aux_vars: &[Variable],
    ) -> AddCnfOutcome {
        for clause in &cnf.clauses {
            let mut mapped_clause =
                Vec::with_capacity(clause.len() + usize::from(activation.is_some()));
            if let Some(lit) = activation {
                mapped_clause.push(lit.negated());
            }
            for &signed_lit in clause {
                let Some(mapped_lit) = self.map_local_dimacs_lit(signed_lit, aux_vars) else {
                    return AddCnfOutcome::Unsupported;
                };
                mapped_clause.push(mapped_lit);
            }

            if !solver.add_clause(mapped_clause) {
                return AddCnfOutcome::Unsat;
            }
        }

        AddCnfOutcome::Added
    }

    /// Encodes a unit-coefficient totalizer (cardinality counter) over the given
    /// solver `inputs` into `solver`, fully up to `at_least(|inputs|)`.
    ///
    /// Reuses the tested generalized-totalizer encoder. Every emitted clause is an
    /// implied consequence of the counting semantics (the encoder guarantees this).
    /// Returns the output literals paired with their thresholds: entry `(k, lit)`
    /// means `lit` is true iff at least `k` of `inputs` are true. Thresholds are
    /// returned in ascending order and form the contiguous range `1..=|inputs|`.
    ///
    /// Returns `None` if interrupted, on overflow, or if any clause is rejected.
    fn encode_cardinality_totalizer(
        &self,
        solver: &mut SatSolver,
        inputs: &[Literal],
    ) -> Option<Vec<(i128, Literal)>> {
        let n = inputs.len();
        if n == 0 {
            return Some(Vec::new());
        }
        let rhs = i128::try_from(n).ok()?;

        // Placeholder DIMACS input vars 1..=n map onto `inputs`; the encoder
        // allocates auxiliary vars starting at n+1.
        let placeholder_count = u32::try_from(n).ok()?;
        let coeffs = vec![1i128; n];
        let lits: Vec<i32> = (1..=placeholder_count).map(|v| v as i32).collect();

        let mut clauses: Vec<Vec<i32>> = Vec::new();
        let mut next_var = placeholder_count.checked_add(1)?;
        let should_stop = &self.should_stop;
        let mut stop = || should_stop();
        let outputs = encode_totalizer_with_outputs_interruptible(
            &coeffs,
            &lits,
            rhs,
            &mut clauses,
            &mut next_var,
            &mut stop,
        )?;

        // Aux variables allocated by the encoder are those with DIMACS index
        // > placeholder_count. Allocate a fresh solver variable for each.
        let aux_count = next_var.checked_sub(placeholder_count)?;
        let aux_len = usize::try_from(aux_count).ok()?;
        let mut aux_vars = Vec::with_capacity(aux_len);
        for _ in 0..aux_len {
            aux_vars.push(solver.new_var());
        }

        let map = |dimacs: i32| -> Option<Literal> {
            if dimacs == 0 {
                return None;
            }
            let magnitude = dimacs.unsigned_abs();
            let base = if magnitude <= placeholder_count {
                let idx = usize::try_from(magnitude.checked_sub(1)?).ok()?;
                *inputs.get(idx)?
            } else {
                let aux_offset = magnitude.checked_sub(placeholder_count)?.checked_sub(1)?;
                let aux_idx = usize::try_from(aux_offset).ok()?;
                Literal::positive(*aux_vars.get(aux_idx)?)
            };
            Some(if dimacs > 0 { base } else { base.negated() })
        };

        let mut mapped_clause = Vec::new();
        for clause in &clauses {
            mapped_clause.clear();
            mapped_clause.reserve(clause.len());
            for &dimacs in clause {
                let lit = map(dimacs)?;
                mapped_clause.push(lit);
            }
            if !solver.add_clause(std::mem::take(&mut mapped_clause)) {
                return None;
            }
        }

        let mut result = Vec::with_capacity(outputs.outputs.len());
        for (&weight, &dimacs) in outputs.weights.iter().zip(outputs.outputs.iter()) {
            let lit = map(dimacs)?;
            result.push((weight, lit));
        }
        Some(result)
    }

    fn map_dimacs_lits_with_fixed_vars(
        &self,
        dimacs_lits: &[i32],
        fixed_var_count: u32,
        aux_vars: &[Variable],
    ) -> Option<Vec<Literal>> {
        let mut mapped = Vec::with_capacity(dimacs_lits.len());
        for &lit in dimacs_lits {
            mapped.push(map_dimacs_lit_with_fixed_vars(
                lit,
                fixed_var_count,
                aux_vars,
            )?);
        }
        Some(mapped)
    }

    fn map_local_dimacs_lit(&self, signed_lit: i32, aux_vars: &[Variable]) -> Option<Literal> {
        if signed_lit == 0 {
            return None;
        }

        let dimacs_var = signed_lit.unsigned_abs();
        let variable = if dimacs_var <= self.num_pb_vars {
            let zero_based = dimacs_var.checked_sub(1)?;
            Variable::new(zero_based)
        } else {
            let aux_offset = dimacs_var.checked_sub(self.num_pb_vars)?.checked_sub(1)?;
            let aux_index = usize::try_from(aux_offset).ok()?;
            *aux_vars.get(aux_index)?
        };

        Some(if signed_lit > 0 {
            Literal::positive(variable)
        } else {
            Literal::negative(variable)
        })
    }

    #[cfg(test)]
    fn normalized_unit_cost_literals(&self) -> Option<(Vec<Literal>, i128)> {
        let (weighted_literals, offset) = self.normalized_weighted_literals()?;
        let mut seen = HashSet::new();
        let mut literals = Vec::with_capacity(weighted_literals.len());
        for weighted in weighted_literals {
            if weighted.weight != 1 || !seen.insert(weighted.literal) {
                return None;
            }
            literals.push(weighted.literal);
        }
        Some((literals, offset))
    }

    fn normalized_weighted_literals(&self) -> Option<(Vec<WeightedSoftLiteral>, i128)> {
        let mut offset = 0i128;
        let mut order = Vec::with_capacity(self.objective.terms.len());
        let mut weights_by_lit: HashMap<i32, i128> = HashMap::new();
        let mut base_clauses = None;

        for term in &self.objective.terms {
            if term.coeff == 0 {
                continue;
            }

            let sat_lit = match self.objective_literal_for_term(term, &mut base_clauses)? {
                ObjectiveLiteral::ConstantFalse => continue,
                ObjectiveLiteral::ConstantTrue => {
                    offset = offset.checked_add(term.coeff)?;
                    continue;
                }
                ObjectiveLiteral::Literal(lit) => lit,
            };
            let (cost_lit, weight) = if term.coeff > 0 {
                (sat_lit, term.coeff)
            } else {
                let flipped = term.coeff.checked_neg()?;
                offset = offset.checked_add(term.coeff)?;
                (sat_lit.negated(), flipped)
            };

            let key = literal_to_dimacs(cost_lit);
            let entry = weights_by_lit.entry(key).or_insert_with(|| {
                order.push(key);
                0
            });
            // Accumulating duplicate product weights can overflow i128; fail
            // closed instead of wrapping to a wrong (saturated) weight.
            *entry = entry.checked_add(weight)?;
        }

        let mut weighted_literals = Vec::with_capacity(order.len());
        for key in order {
            let Some(weight) = weights_by_lit.remove(&key) else {
                continue;
            };

            let complement = key.checked_neg()?;
            if let Some(complement_weight) = weights_by_lit.remove(&complement) {
                let shared = weight.min(complement_weight);
                offset = offset.checked_add(shared)?;
                let residual_weight = weight - shared;
                let residual_complement_weight = complement_weight - shared;
                if residual_weight > 0 {
                    weighted_literals.push(WeightedSoftLiteral {
                        literal: literal_from_dimacs(key),
                        weight: checked_i128_to_i64(residual_weight)?,
                    });
                }
                if residual_complement_weight > 0 {
                    weighted_literals.push(WeightedSoftLiteral {
                        literal: literal_from_dimacs(complement),
                        weight: checked_i128_to_i64(residual_complement_weight)?,
                    });
                }
                continue;
            }

            weighted_literals.push(WeightedSoftLiteral {
                literal: literal_from_dimacs(key),
                weight: checked_i128_to_i64(weight)?,
            });
        }

        Some((weighted_literals, checked_i128_to_i64(offset)?))
    }

    fn normalized_objective_bounds(&self) -> Option<NormalizedObjectiveBounds> {
        let (weighted_literals, offset) = self.normalized_weighted_literals()?;
        normalized_objective_bounds_from_weighted_literals(&weighted_literals, offset)
    }

    fn objective_literal_for_term(
        &self,
        term: &PbTerm,
        base_clauses: &mut Option<NormalizedClauseIndex>,
    ) -> Option<ObjectiveLiteral> {
        let product = normalize_product_literals(&term.lits)?;
        let factors = match product {
            ProductLiteral::ConstantFalse => return Some(ObjectiveLiteral::ConstantFalse),
            ProductLiteral::Factors(factors) => factors,
        };
        match factors.as_slice() {
            [] => Some(ObjectiveLiteral::ConstantTrue),
            [lit] => Some(ObjectiveLiteral::Literal(literal_from_dimacs(*lit))),
            factors => {
                let base_clauses = base_clauses
                    .get_or_insert_with(|| NormalizedClauseIndex::new(&self.base_cnf.clauses));
                self.find_existing_and_literal(factors, base_clauses)
                    .map(ObjectiveLiteral::Literal)
            }
        }
    }

    fn find_existing_and_literal(
        &self,
        factors: &[i32],
        base_clauses: &NormalizedClauseIndex,
    ) -> Option<Literal> {
        for candidate_var in 1..=self.base_cnf.num_vars {
            let candidate = i32::try_from(candidate_var).ok()?;
            if factors.contains(&candidate) || factors.contains(&-candidate) {
                continue;
            }

            let has_implications = factors
                .iter()
                .all(|&factor| base_clauses.contains(vec![-candidate, factor]));
            if !has_implications {
                continue;
            }

            let mut reverse_clause = Vec::with_capacity(factors.len() + 1);
            reverse_clause.push(candidate);
            reverse_clause.extend(factors.iter().map(|&factor| -factor));
            if base_clauses.contains(reverse_clause) {
                return Some(literal_from_dimacs(candidate));
            }
        }

        None
    }

    fn extract_weighted_core_guided_state(&self) -> Option<CoreGuidedExtraction> {
        let (mut active_softs, mut lower_bound) = self.normalized_weighted_literals()?;
        if active_softs.is_empty() {
            return Some(CoreGuidedExtraction {
                status: LowerBoundStatus::Complete(lower_bound),
                learned_clauses: Vec::new(),
            });
        }

        let mut solver = self.base_solver.clone_for_incremental();
        let mut learned_clauses = Vec::new();

        if let Some(status) = self.extract_native_core_guided_seeds(
            &mut active_softs,
            &mut lower_bound,
            &mut solver,
            &mut learned_clauses,
        ) {
            return Some(CoreGuidedExtraction {
                status,
                learned_clauses,
            });
        }

        let mut assumptions = Vec::with_capacity(active_softs.len());
        loop {
            if active_softs.is_empty() {
                return Some(CoreGuidedExtraction {
                    status: LowerBoundStatus::Complete(lower_bound),
                    learned_clauses,
                });
            }

            assumptions.clear();
            assumptions.extend(active_softs.iter().map(|soft| soft.literal.negated()));
            let should_stop = &self.should_stop;
            match solver
                .solve_with_assumptions_interruptible(&assumptions, should_stop)
                .into_inner()
            {
                AssumeResult::Sat(_) => {
                    return Some(CoreGuidedExtraction {
                        status: LowerBoundStatus::Complete(lower_bound),
                        learned_clauses,
                    });
                }
                AssumeResult::Unsat(core, _) => {
                    let trimmed_core = self.trim_assumption_core(&mut solver, core);
                    let core_softs: HashSet<Literal> =
                        trimmed_core.into_iter().map(Literal::negated).collect();
                    if core_softs.is_empty() {
                        return Some(CoreGuidedExtraction {
                            status: LowerBoundStatus::Complete(lower_bound),
                            learned_clauses,
                        });
                    }

                    let clause: Vec<Literal> = active_softs
                        .iter()
                        .filter(|soft| core_softs.contains(&soft.literal))
                        .map(|soft| soft.literal)
                        .collect();
                    if clause.is_empty() {
                        return Some(CoreGuidedExtraction {
                            status: LowerBoundStatus::Complete(lower_bound),
                            learned_clauses,
                        });
                    }

                    let core_weight = active_softs
                        .iter()
                        .filter(|soft| core_softs.contains(&soft.literal))
                        .map(|soft| soft.weight)
                        .min()?;
                    lower_bound = lower_bound.checked_add(core_weight)?;

                    for soft in &mut active_softs {
                        if core_softs.contains(&soft.literal) {
                            soft.weight = soft.weight.saturating_sub(core_weight);
                        }
                    }
                    active_softs.retain(|soft| soft.weight > 0);

                    learned_clauses.push(clause.clone());
                    if !solver.add_clause(clause) {
                        return Some(CoreGuidedExtraction {
                            status: LowerBoundStatus::Complete(lower_bound),
                            learned_clauses,
                        });
                    }
                }
                AssumeResult::Unknown => {
                    return Some(CoreGuidedExtraction {
                        status: LowerBoundStatus::Interrupted(lower_bound),
                        learned_clauses,
                    });
                }
                #[allow(unreachable_patterns)]
                _ => {
                    return Some(CoreGuidedExtraction {
                        status: LowerBoundStatus::Interrupted(lower_bound),
                        learned_clauses,
                    });
                }
            }
        }
    }

    fn extract_native_core_guided_seeds(
        &self,
        active_softs: &mut Vec<WeightedSoftLiteral>,
        lower_bound: &mut i128,
        solver: &mut SatSolver,
        learned_clauses: &mut Vec<Vec<Literal>>,
    ) -> Option<LowerBoundStatus> {
        loop {
            if active_softs.is_empty() {
                return Some(LowerBoundStatus::Complete(*lower_bound));
            }

            let seed = self.extract_native_core_guided_seed(active_softs, *lower_bound)?;
            let core_softs: HashSet<Literal> = seed.learned_clause.iter().copied().collect();
            *lower_bound = seed.lower_bound;

            for soft in active_softs.iter_mut() {
                if core_softs.contains(&soft.literal) {
                    soft.weight = soft.weight.saturating_sub(seed.core_weight);
                }
            }
            active_softs.retain(|soft| soft.weight > 0);

            learned_clauses.push(seed.learned_clause.clone());
            if !solver.add_clause(seed.learned_clause) {
                return Some(LowerBoundStatus::Complete(*lower_bound));
            }
        }
    }

    fn extract_native_core_guided_seed(
        &self,
        active_softs: &[WeightedSoftLiteral],
        lower_bound: i128,
    ) -> Option<NativeCoreGuidedSeed> {
        if self.native_core_mode != NativeCoreMode::Enabled
            || active_softs.is_empty()
            || (self.should_stop)()
        {
            return None;
        }

        let (objective, assumptions, contribution_by_assumption) =
            native_core_probe_objective(active_softs)?;
        let instance = native_core_probe_instance(&self.base_cnf, objective)?;
        let mut solver = PbCdclSolver::new_interruptible(&instance, || (self.should_stop)());
        if (self.should_stop)() {
            return None;
        }

        let core = match solver
            .solve_with_assumptions_interruptible(&assumptions, || (self.should_stop)())
        {
            PbCdclAssumptionResult::Unsatisfiable { core } => core,
            PbCdclAssumptionResult::Satisfiable(_)
            | PbCdclAssumptionResult::Unknown
            | PbCdclAssumptionResult::Unsupported => return None,
        };
        let core =
            self.trim_native_assumption_core(&mut solver, core, &contribution_by_assumption)?;
        let probe_result = native_core_probe_result_from_core(core, &contribution_by_assumption)?;
        let accepted_core = probe_result.accepted_unsat_core_evidence(None)?;
        let core_weight = accepted_core.lower_bound();
        let seeded_lower_bound = lower_bound.checked_add(core_weight)?;

        let mut learned_clause = Vec::with_capacity(accepted_core.weighted_core().len());
        for entry in accepted_core.weighted_core() {
            let objective_lit = entry.objective_lit();
            if objective_lit.var > self.base_cnf.num_vars {
                return None;
            }
            learned_clause.push(pb_lit_to_sat_literal(objective_lit)?);
        }
        learned_clause.sort_by_key(|lit| literal_to_dimacs(*lit));
        learned_clause.dedup();
        if learned_clause.is_empty() || learned_clause.len() != accepted_core.weighted_core().len()
        {
            return None;
        }

        Some(NativeCoreGuidedSeed {
            lower_bound: seeded_lower_bound,
            core_weight,
            learned_clause,
        })
    }

    fn trim_native_assumption_core(
        &self,
        solver: &mut PbCdclSolver,
        mut core_assumptions: Vec<PbLit>,
        contribution_by_assumption: &HashMap<PbLit, (PbLit, i128)>,
    ) -> Option<Vec<PbLit>> {
        if core_assumptions.is_empty()
            || !core_assumptions
                .iter()
                .all(|assumption| contribution_by_assumption.contains_key(assumption))
        {
            return None;
        }
        if core_assumptions.len() <= 1 || core_assumptions.len() > MAX_CORE_TRIM_SIZE {
            return Some(core_assumptions);
        }

        let mut checks = 0usize;
        let mut idx = 0usize;
        while idx < core_assumptions.len() && checks < MAX_CORE_TRIM_CHECKS {
            if (self.should_stop)() {
                return None;
            }

            let mut candidate = Vec::with_capacity(core_assumptions.len().saturating_sub(1));
            candidate.extend_from_slice(&core_assumptions[..idx]);
            candidate.extend_from_slice(&core_assumptions[idx + 1..]);
            checks += 1;

            match solver.solve_with_assumptions_interruptible(&candidate, || (self.should_stop)()) {
                PbCdclAssumptionResult::Unsatisfiable { core } if !core.is_empty() => {
                    if !core
                        .iter()
                        .all(|assumption| contribution_by_assumption.contains_key(assumption))
                    {
                        return None;
                    }
                    core_assumptions = core;
                    idx = 0;
                }
                PbCdclAssumptionResult::Unsatisfiable { .. }
                | PbCdclAssumptionResult::Satisfiable(_) => {
                    idx += 1;
                }
                PbCdclAssumptionResult::Unknown | PbCdclAssumptionResult::Unsupported => {
                    return None;
                }
            }
        }

        Some(core_assumptions)
    }

    fn add_learned_core_clauses(
        &self,
        solver: &mut SatSolver,
        learned_clauses: &[Vec<Literal>],
    ) -> bool {
        for clause in learned_clauses {
            if !solver.add_clause(clause.clone()) {
                return false;
            }
        }
        true
    }

    fn trim_assumption_core(
        &self,
        solver: &mut SatSolver,
        mut core_assumptions: Vec<Literal>,
    ) -> Vec<Literal> {
        if core_assumptions.len() <= 1 || core_assumptions.len() > MAX_CORE_TRIM_SIZE {
            return core_assumptions;
        }

        let mut checks = 0usize;
        let mut idx = 0usize;
        while idx < core_assumptions.len() && checks < MAX_CORE_TRIM_CHECKS {
            if (self.should_stop)() {
                break;
            }

            let mut candidate = Vec::with_capacity(core_assumptions.len().saturating_sub(1));
            candidate.extend_from_slice(&core_assumptions[..idx]);
            candidate.extend_from_slice(&core_assumptions[idx + 1..]);
            checks += 1;

            let should_stop = &self.should_stop;
            match solver
                .solve_with_assumptions_interruptible(&candidate, should_stop)
                .into_inner()
            {
                AssumeResult::Unsat(_, _) => {
                    core_assumptions = candidate;
                }
                AssumeResult::Sat(_) => {
                    idx += 1;
                }
                AssumeResult::Unknown => break,
                #[allow(unreachable_patterns)]
                _ => break,
            }
        }

        core_assumptions
    }

    fn build_persistent_upper_bound_cnf(
        &self,
    ) -> Result<Option<PersistentUpperBoundCnf>, BoundEncodingError> {
        let (weighted_literals, offset) = match self.normalized_weighted_literals() {
            Some(normalized) => normalized,
            None => return Ok(None),
        };
        if weighted_literals.len() < PERSISTENT_BOUND_MIN_TERMS {
            return Ok(None);
        }

        let total_weight = weighted_literals
            .iter()
            .try_fold(0i128, |sum, soft| sum.checked_add(soft.weight))
            .ok_or(BoundEncodingError::UnsupportedBound)?;
        let all_unit = weighted_literals.iter().all(|soft| soft.weight == 1);
        let lits: Vec<i32> = weighted_literals
            .iter()
            .map(|soft| literal_to_dimacs(soft.literal.negated()))
            .collect();

        if all_unit {
            if !should_use_persistent_unit_literal_bounds(weighted_literals.len()) {
                return Ok(None);
            }

            let should_stop = &self.should_stop;
            let mut clauses = Vec::new();
            let mut next_var = self.base_cnf.num_vars + 1;
            let threshold_outputs = match encode_cardinality_with_outputs_interruptible(
                &lits,
                &mut clauses,
                &mut next_var,
                &mut || should_stop(),
            ) {
                Some(outputs) => outputs,
                None => return Err(BoundEncodingError::Interrupted),
            };

            return Ok(Some(PersistentUpperBoundCnf {
                #[cfg(test)]
                kind: PersistentBoundKind::UnitCardinality,
                cnf: EncodedCnf {
                    num_vars: next_var - 1,
                    clauses,
                },
                fixed_var_count: self.base_cnf.num_vars,
                offset,
                total_weight,
                threshold_outputs,
            }));
        }

        if !should_use_persistent_weighted_literal_bounds(&weighted_literals, total_weight) {
            return Ok(None);
        }

        let coeffs: Vec<i128> = weighted_literals.iter().map(|soft| soft.weight).collect();
        let should_stop = &self.should_stop;
        let mut clauses = Vec::new();
        let mut next_var = self.base_cnf.num_vars + 1;
        let outputs = match encode_totalizer_with_outputs_interruptible(
            &coeffs,
            &lits,
            total_weight,
            &mut clauses,
            &mut next_var,
            &mut || should_stop(),
        ) {
            Some(outputs) => outputs,
            None => return Err(BoundEncodingError::Interrupted),
        };

        Ok(Some(PersistentUpperBoundCnf {
            #[cfg(test)]
            kind: PersistentBoundKind::WeightedTotalizer,
            cnf: EncodedCnf {
                num_vars: next_var - 1,
                clauses,
            },
            fixed_var_count: self.base_cnf.num_vars,
            offset,
            total_weight,
            threshold_outputs: outputs.weights.into_iter().zip(outputs.outputs).collect(),
        }))
    }

    /// Genuine OLL (Order/Unsatisfiable-core, RC2-style) core-guided loop with
    /// totalizer relaxations, over a single persistent incremental solver.
    ///
    /// Returns `None` when OLL is not applicable to this objective shape (e.g. the
    /// objective cannot be normalized into weighted soft literals); the caller then
    /// falls back to `binary_refine`.
    ///
    /// # Soundness
    /// - The lower bound only ever increases by exactly the realized weight of a
    ///   disjoint core (`core_weight = min weight among core softs`).
    /// - Relaxation clauses are emitted by the tested totalizer encoder, so each is
    ///   an implied consequence of the counting semantics.
    /// - **Stratification** (process high-weight softs first) only restricts *which*
    ///   softs are assumed in a round; it never changes a derived bound. An optimum
    ///   is declared only when a SAT model is found with the *full* set of remaining
    ///   (non-hardened) softs assumed at their no-cost polarity, so a partial-stratum
    ///   SAT never short-circuits the proof.
    /// - **Hardening** fixes a soft to its no-cost polarity only when its weight is
    ///   strictly greater than the current `(best_value - lower_bound)` gap. Because
    ///   `cost = lower_bound + sum_s w_s*paid(s)` holds for every feasible model, any
    ///   model paying such a soft has `cost >= lower_bound + w_s > best_value`, i.e.
    ///   it is not strictly better than the incumbent; fixing it can only discard
    ///   non-improving models and never the optimum (when the optimum < best_value).
    /// - `OptResult::Optimal` is returned only after `verify_optimum` confirms the
    ///   model satisfies every original constraint, the objective is exact, and the
    ///   value lies in `[lower_bound, upper_bound]`. Any failure downgrades the
    ///   result to `Satisfiable` (the incumbent) -- never a false optimum.
    /// - On interruption the best incumbent is returned as `Satisfiable`.
    fn solve_oll(
        &mut self,
        best_assignment: Vec<bool>,
        best_value: i128,
        structural_lower_bound: i128,
    ) -> Option<OptResult> {
        let (softs, base_lower_bound) = self.normalized_weighted_literals()?;
        if softs.is_empty() {
            // No soft structure: the offset alone is the objective.
            return Some(self.finish_oll_optimum(
                best_assignment,
                best_value,
                base_lower_bound.max(structural_lower_bound),
            ));
        }

        let lower_bound = base_lower_bound.max(structural_lower_bound);
        let solver = self.base_solver.clone_for_incremental();
        let mut state = OllState {
            solver,
            softs,
            lower_bound,
            best_assignment,
            best_value,
            // Stratification threshold: only softs with `weight >= threshold` are
            // assumed in the current round. Starts at the maximum soft weight so the
            // first rounds target the highest-value cores, and is lowered by the
            // CASHWMaxSAT diminishing schedule once a stratum is SAT.
            threshold: i128::MAX,
            assumptions: Vec::new(),
        };
        state.initialize_threshold();
        self.run_oll_loop(state)
    }

    /// Core stratified OLL loop. Pulled out of [`Self::solve_oll`] so the per-round
    /// bookkeeping (hardening, stratum descent, core extraction + exhaustion) reads
    /// linearly. Returns the same `Option<OptResult>` contract as `solve_oll`.
    fn run_oll_loop(&mut self, mut state: OllState) -> Option<OptResult> {
        loop {
            // Opt-in (AY_PB_NATIVE_LP_BOUND): fold the sound LP-relaxation bound
            // into the loop-termination check, not just the terminal clamp in
            // `finish_oll_optimum`. The LP bound is computed once and memoized
            // (`combined_objective_lower_bound`), so for instances whose LP
            // relaxation is tight (e.g. weighted set-packing like KE_*) OLL can
            // certify the incumbent the moment its descent reaches the optimum
            // instead of grinding weak cores to the deadline. `finish_oll_optimum`
            // re-verifies via the soundness gate, so this can never emit a false
            // optimum — a too-low bound merely fails the bracket and returns SAT.
            // Default OFF leaves the terminal check `best_value <= lower_bound`
            // (the LP bound is still applied terminally in `finish_oll_optimum`).
            let loop_lower_bound = if crate::cdcl::native_lp_bound_enabled() {
                self.combined_objective_lower_bound(state.lower_bound)
            } else {
                state.lower_bound
            };
            if state.best_value <= loop_lower_bound {
                return Some(self.finish_oll_optimum(
                    state.best_assignment,
                    state.best_value,
                    state.lower_bound,
                ));
            }
            if self.should_stop_now() {
                return Some(OptResult::Satisfiable(
                    state.best_assignment,
                    state.best_value,
                ));
            }
            if state.softs.is_empty() {
                // No assumable softs left: the lower bound is final.
                return Some(self.finish_oll_optimum(
                    state.best_assignment,
                    state.best_value,
                    state.lower_bound,
                ));
            }

            // HARDENING: any soft whose weight exceeds the proven gap cannot be paid
            // in a strictly-better model, so fix it to no-cost polarity. May make the
            // solver UNSAT (no better model exists), which the SAT/UNSAT logic below
            // then handles via the bracket gate -- never a false optimum.
            if !self.harden_softs(&mut state) {
                return Some(OptResult::Satisfiable(
                    state.best_assignment,
                    state.best_value,
                ));
            }
            if state.softs.is_empty() {
                return Some(self.finish_oll_optimum(
                    state.best_assignment,
                    state.best_value,
                    state.lower_bound,
                ));
            }

            // STRATIFICATION: assume only softs at or above the current threshold.
            // `at_full_stratum` is true when every remaining soft is included; only
            // then can a SAT result certify optimality.
            let at_full_stratum = state.collect_stratum_assumptions();

            let should_stop = &self.should_stop;
            match state
                .solver
                .solve_with_assumptions_interruptible(&state.assumptions, should_stop)
                .into_inner()
            {
                AssumeResult::Sat(model) => {
                    let assignment = self.project_assignment(model);
                    let obj_value = eval_objective(&self.objective, &assignment);
                    if obj_value < state.best_value {
                        state.best_assignment = assignment;
                        state.best_value = obj_value;
                        self.report_improvement(state.best_value);
                    }
                    if at_full_stratum {
                        // Every remaining soft is forced to its no-cost polarity, so
                        // this model realizes the lower bound and is a proven optimum.
                        return Some(self.finish_oll_optimum(
                            state.best_assignment,
                            state.best_value,
                            state.lower_bound,
                        ));
                    }
                    // Partial stratum SAT: a high-weight feasible point was found but
                    // lower-weight softs were not constrained, so optimality is NOT
                    // proven. Descend to the next (lower) weight stratum and retry.
                    state.lower_threshold();
                }
                AssumeResult::Unsat(core, _) => {
                    match self.process_oll_core(&mut state, core) {
                        OllCoreOutcome::Continue => {}
                        OllCoreOutcome::Stop => {
                            return Some(OptResult::Satisfiable(
                                state.best_assignment,
                                state.best_value,
                            ));
                        }
                        OllCoreOutcome::Exhausted => {
                            // UNSAT with an empty core in the current stratum. If we
                            // are below the full stratum, lower-weight softs may still
                            // form cores, so descend; otherwise the bound is final.
                            if at_full_stratum {
                                return Some(self.finish_oll_optimum(
                                    state.best_assignment,
                                    state.best_value,
                                    state.lower_bound,
                                ));
                            }
                            state.lower_threshold();
                        }
                    }
                    if self.should_stop_now() {
                        return Some(OptResult::Satisfiable(
                            state.best_assignment,
                            state.best_value,
                        ));
                    }
                }
                AssumeResult::Unknown => {
                    return Some(OptResult::Satisfiable(
                        state.best_assignment,
                        state.best_value,
                    ));
                }
                #[allow(unreachable_patterns)]
                _ => {
                    return Some(OptResult::Satisfiable(
                        state.best_assignment,
                        state.best_value,
                    ));
                }
            }
        }
    }

    /// HARDENING pass. Fixes (as solver units) every soft whose weight is strictly
    /// greater than the current proven gap `best_value - lower_bound`, then drops it
    /// from the active soft set. Returns `false` if a hardening unit makes the solver
    /// report UNSAT outright (caller then returns the incumbent as `Satisfiable`).
    ///
    /// Soundness: `cost = lower_bound + sum_s w_s*paid(s)` for every feasible model
    /// (the OLL reformulation invariant). For a soft with `w_s > best_value -
    /// lower_bound`, any model paying it has `cost >= lower_bound + w_s > best_value`,
    /// so it cannot be strictly better than the incumbent. Forcing the no-cost
    /// polarity therefore only removes non-improving models; an optimum strictly
    /// below `best_value` is preserved. The gap uses `best_value` = the best *proven
    /// incumbent* cost (a valid UB) and `lower_bound` = the accumulated sound LB.
    fn harden_softs(&self, state: &mut OllState) -> bool {
        // gap = UB - LB, with UB the best proven incumbent. Non-negative here because
        // the loop already returned when `best_value <= lower_bound`.
        let Some(gap) = state.best_value.checked_sub(state.lower_bound) else {
            return true;
        };
        if gap < 0 {
            return true;
        }
        let mut idx = 0;
        let mut ok = true;
        while idx < state.softs.len() {
            if state.softs[idx].weight > gap {
                let soft = state.softs.swap_remove(idx);
                // Fix the soft to its no-cost (negated) polarity as a unit clause.
                if !state.solver.add_clause(vec![soft.literal.negated()]) {
                    // Solver is now UNSAT: there is no model with all hardened softs
                    // unpaid, i.e. no strictly-better model. The incumbent stands; we
                    // stop and let the caller report it as `Satisfiable` (the bracket
                    // gate, not hardening, decides optimality).
                    ok = false;
                    break;
                }
            } else {
                idx += 1;
            }
        }
        ok
    }

    /// Processes one extracted UNSAT core: trims it, increments the lower bound by the
    /// realized core weight, performs weight-split bookkeeping, and registers the
    /// totalizer relaxation outputs as new soft selectors. Returns whether the loop
    /// should continue, stop with the incumbent, or treat the core as exhausted.
    fn process_oll_core(&mut self, state: &mut OllState, core: Vec<Literal>) -> OllCoreOutcome {
        let trimmed_core = self.trim_assumption_core(&mut state.solver, core);
        let core_softs: HashSet<Literal> = trimmed_core.into_iter().map(Literal::negated).collect();
        if core_softs.is_empty() {
            return OllCoreOutcome::Exhausted;
        }

        let Some(core_weight) = state
            .softs
            .iter()
            .filter(|soft| core_softs.contains(&soft.literal))
            .map(|soft| soft.weight)
            .min()
        else {
            return OllCoreOutcome::Stop;
        };
        if core_weight <= 0 {
            return OllCoreOutcome::Stop;
        }

        // Relaxation literals: the cost literals participating in the core (both
        // original objective selectors and earlier totalizer outputs, handled
        // uniformly).
        let relax_lits: Vec<Literal> = state
            .softs
            .iter()
            .filter(|soft| core_softs.contains(&soft.literal))
            .map(|soft| soft.literal)
            .collect();

        let Some(next_lower_bound) = state.lower_bound.checked_add(core_weight) else {
            return OllCoreOutcome::Stop;
        };
        state.lower_bound = next_lower_bound;

        // Weight-split bookkeeping (WCE): decrement the core softs by the core weight
        // and drop the exhausted ones.
        for soft in &mut state.softs {
            if core_softs.contains(&soft.literal) {
                soft.weight = soft.weight.saturating_sub(core_weight);
            }
        }
        state.softs.retain(|soft| soft.weight > 0);

        // Build a fresh totalizer over the core's relaxation literals and register
        // the higher-threshold outputs (>= 2 paid) as new soft selectors of weight
        // `core_weight`. The encoder fully materializes all thresholds at once.
        if relax_lits.len() >= 2 {
            let Some(outputs) = self.encode_cardinality_totalizer(&mut state.solver, &relax_lits)
            else {
                return OllCoreOutcome::Stop;
            };
            for (threshold, output_lit) in outputs {
                // `output_lit` is true iff at least `threshold` of the core selectors
                // are paid. The first payment is already charged into `lower_bound`;
                // thresholds >= 2 each cost one further `core_weight`.
                if threshold >= 2 {
                    state.softs.push(WeightedSoftLiteral {
                        literal: output_lit,
                        weight: core_weight,
                    });
                }
            }
        }

        OllCoreOutcome::Continue
    }

    /// Finalizes an OLL run that believes it has proven `best_value` optimal at
    /// `lower_bound`. Re-verifies via the soundness gate; on any failure the
    /// incumbent is returned as `Satisfiable` rather than a false optimum.
    ///
    /// The effective lower bound is `max(lower_bound, lp_bound)`: both are
    /// independently sound lower bounds on the objective, so their max is sound and
    /// can let the LP relaxation close the optimality gap that OLL's core
    /// accumulation alone has not yet reached. Because the LP bound is never larger
    /// than a feasible objective value, `max(.) <= best_value` still holds whenever
    /// `lower_bound <= best_value`, so this never spuriously fails the bracket.
    fn finish_oll_optimum(
        &self,
        best_assignment: Vec<bool>,
        best_value: i128,
        lower_bound: i128,
    ) -> OptResult {
        let upper_bound = best_value;
        let effective_lb = self.combined_objective_lower_bound(lower_bound);
        if best_value <= effective_lb
            && self.verify_optimum(&best_assignment, best_value, effective_lb, upper_bound)
        {
            OptResult::Optimal(best_assignment, best_value)
        } else {
            OptResult::Satisfiable(best_assignment, best_value)
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AddCnfOutcome {
    Added,
    Unsat,
    Unsupported,
}

struct PersistentUpperBoundCnf {
    #[cfg(test)]
    kind: PersistentBoundKind,
    cnf: EncodedCnf,
    fixed_var_count: u32,
    offset: i128,
    total_weight: i128,
    threshold_outputs: Vec<(i128, i32)>,
}

enum PersistentBoundAssumption {
    None,
    Unsat,
    Assume(Literal),
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PersistentBoundKind {
    UnitCardinality,
    WeightedTotalizer,
}

fn normalized_objective_bounds_from_weighted_literals(
    weighted_literals: &[WeightedSoftLiteral],
    offset: i128,
) -> Option<NormalizedObjectiveBounds> {
    let total_weight = weighted_literals
        .iter()
        .try_fold(0i128, |sum, soft| sum.checked_add(soft.weight))?;

    Some(NormalizedObjectiveBounds {
        lower: offset,
        upper: checked_i128_to_i64(offset + total_weight)?,
    })
}

struct NormalizedClauseIndex {
    clauses: HashSet<Vec<i32>>,
}

impl NormalizedClauseIndex {
    fn new(clauses: &[Vec<i32>]) -> Self {
        Self {
            clauses: clauses
                .iter()
                .cloned()
                .map(normalized_dimacs_clause)
                .collect(),
        }
    }

    fn contains(&self, clause: Vec<i32>) -> bool {
        self.clauses.contains(&normalized_dimacs_clause(clause))
    }
}

fn allocate_aux_vars_after(
    solver: &mut SatSolver,
    cnf_num_vars: u32,
    fixed_var_count: u32,
) -> Option<Vec<Variable>> {
    let extra_aux = cnf_num_vars.saturating_sub(fixed_var_count);
    let extra_aux_len = usize::try_from(extra_aux).ok()?;
    let mut aux_vars = Vec::with_capacity(extra_aux_len);
    for _ in 0..extra_aux_len {
        aux_vars.push(solver.new_var());
    }
    Some(aux_vars)
}

fn add_encoded_cnf_with_fixed_vars(
    solver: &mut SatSolver,
    cnf: &EncodedCnf,
    fixed_var_count: u32,
    aux_vars: &[Variable],
) -> AddCnfOutcome {
    for clause in &cnf.clauses {
        let mut mapped_clause = Vec::with_capacity(clause.len());
        for &signed_lit in clause {
            let Some(mapped_lit) =
                map_dimacs_lit_with_fixed_vars(signed_lit, fixed_var_count, aux_vars)
            else {
                return AddCnfOutcome::Unsupported;
            };
            mapped_clause.push(mapped_lit);
        }

        if !solver.add_clause(mapped_clause) {
            return AddCnfOutcome::Unsat;
        }
    }

    AddCnfOutcome::Added
}

fn map_dimacs_lit_with_fixed_vars(
    signed_lit: i32,
    fixed_var_count: u32,
    aux_vars: &[Variable],
) -> Option<Literal> {
    if signed_lit == 0 {
        return None;
    }

    let dimacs_var = signed_lit.unsigned_abs();
    let variable = if dimacs_var <= fixed_var_count {
        let zero_based = dimacs_var.checked_sub(1)?;
        Variable::new(zero_based)
    } else {
        let aux_offset = dimacs_var.checked_sub(fixed_var_count)?.checked_sub(1)?;
        let aux_index = usize::try_from(aux_offset).ok()?;
        *aux_vars.get(aux_index)?
    };

    Some(if signed_lit > 0 {
        Literal::positive(variable)
    } else {
        Literal::negative(variable)
    })
}

struct PersistentUpperBoundEncoding {
    #[cfg(test)]
    kind: PersistentBoundKind,
    offset: i128,
    total_weight: i128,
    threshold_outputs: Vec<(i128, Literal)>,
}

impl PersistentUpperBoundEncoding {
    fn install(engine: &OptimizationEngine<'_>, solver: &mut SatSolver) -> Option<Self> {
        let cnf = match engine.build_persistent_upper_bound_cnf() {
            Ok(Some(cnf)) => cnf,
            Ok(None) | Err(BoundEncodingError::Interrupted) => return None,
            Err(
                BoundEncodingError::UnsupportedCoefficient | BoundEncodingError::UnsupportedBound,
            ) => return None,
        };

        let aux_vars = allocate_aux_vars_after(solver, cnf.cnf.num_vars, cnf.fixed_var_count)?;
        let local_outputs: Vec<i32> = cnf.threshold_outputs.iter().map(|(_, lit)| *lit).collect();
        let mapped_outputs = engine.map_dimacs_lits_with_fixed_vars(
            &local_outputs,
            cnf.fixed_var_count,
            &aux_vars,
        )?;
        match add_encoded_cnf_with_fixed_vars(solver, &cnf.cnf, cnf.fixed_var_count, &aux_vars) {
            AddCnfOutcome::Added => Some(Self {
                #[cfg(test)]
                kind: cnf.kind,
                offset: cnf.offset,
                total_weight: cnf.total_weight,
                threshold_outputs: cnf
                    .threshold_outputs
                    .into_iter()
                    .map(|(weight, _)| weight)
                    .zip(mapped_outputs)
                    .collect(),
            }),
            AddCnfOutcome::Unsat | AddCnfOutcome::Unsupported => None,
        }
    }

    fn assumption_for_bound(&self, upper_bound: i128) -> PersistentBoundAssumption {
        let allowed_cost = upper_bound - self.offset;
        if allowed_cost < 0 {
            return PersistentBoundAssumption::Unsat;
        }
        if allowed_cost >= self.total_weight {
            return PersistentBoundAssumption::None;
        }

        let required_weight = saturating_i128_to_i64(self.total_weight - allowed_cost);
        let idx = match self
            .threshold_outputs
            .binary_search_by_key(&required_weight, |(weight, _)| *weight)
        {
            Ok(idx) | Err(idx) => idx,
        };
        match self.threshold_outputs.get(idx) {
            Some((_, lit)) => PersistentBoundAssumption::Assume(*lit),
            None => PersistentBoundAssumption::Unsat,
        }
    }
}

struct UpperBoundQuerySession {
    solver: SatSolver,
    base_unsat: bool,
    objective_stats: ObjectiveStats,
    persistent_bounds: Option<PersistentUpperBoundEncoding>,
    normalized_bounds: Option<NormalizedObjectiveBounds>,
    /// Remaining session-level gap-row BDD pool, threaded through every
    /// per-probe bound encode (see [`crate::encoding::BDD_GAP_NODE_POOL`]).
    /// Each probe's bound CNF stays in `solver` behind a never-removed
    /// activation literal, so one shared pool — not a fresh pool per probe —
    /// is what bounds the total BDD-appended clause volume of the session.
    bound_bdd_gap_pool: u64,
    #[cfg(test)]
    bound_clause_growth_since_construction: usize,
}

impl UpperBoundQuerySession {
    fn new(engine: &OptimizationEngine<'_>, learned_clauses: &[Vec<Literal>]) -> Self {
        let mut solver = engine.base_solver.clone_for_incremental();
        let base_unsat = !engine.add_learned_core_clauses(&mut solver, learned_clauses);
        let objective_stats = engine.objective_stats();
        // Core-guided refinement already injects learned soft-core clauses. Keep
        // that path on per-probe encodings; the persistent totalizer can otherwise
        // dominate small exact-one refinements that the legacy path closes quickly.
        let persistent_bounds = if base_unsat || !learned_clauses.is_empty() {
            None
        } else {
            PersistentUpperBoundEncoding::install(engine, &mut solver)
        };
        let normalized_bounds = if base_unsat || persistent_bounds.is_some() {
            None
        } else {
            engine.normalized_objective_bounds()
        };
        Self {
            solver,
            base_unsat,
            objective_stats,
            persistent_bounds,
            normalized_bounds,
            bound_bdd_gap_pool: crate::encoding::BDD_GAP_NODE_POOL,
            #[cfg(test)]
            bound_clause_growth_since_construction: 0,
        }
    }

    fn solve(&mut self, engine: &OptimizationEngine<'_>, upper_bound: i128) -> QueryOutcome {
        if self.base_unsat {
            return QueryOutcome::Unsat;
        }

        if upper_bound < self.objective_stats.lower_bound {
            return QueryOutcome::Unsat;
        }

        if upper_bound >= self.objective_stats.upper_bound {
            return engine.solve_solver(&mut self.solver);
        }

        if let Some(bounds) = self.normalized_bounds {
            if upper_bound < bounds.lower {
                return QueryOutcome::Unsat;
            }

            if upper_bound >= bounds.upper {
                return engine.solve_solver(&mut self.solver);
            }
        }

        if let Some(persistent_bounds) = &self.persistent_bounds {
            return match persistent_bounds.assumption_for_bound(upper_bound) {
                PersistentBoundAssumption::None => engine.solve_solver(&mut self.solver),
                PersistentBoundAssumption::Unsat => QueryOutcome::Unsat,
                PersistentBoundAssumption::Assume(bound_lit) => {
                    engine.solve_solver_with_assumptions(&mut self.solver, &[bound_lit])
                }
            };
        }

        let cnf = match engine.build_upper_bound_cnf(upper_bound, self.bound_bdd_gap_pool) {
            Ok((cnf, remaining_gap_pool)) => {
                // Persist the depleted pool: the session — not each probe —
                // owns the gap-row BDD budget (see the field doc).
                self.bound_bdd_gap_pool = remaining_gap_pool;
                cnf
            }
            Err(BoundEncodingError::Interrupted) => return QueryOutcome::Unknown,
            Err(
                BoundEncodingError::UnsupportedCoefficient | BoundEncodingError::UnsupportedBound,
            ) => {
                return QueryOutcome::Unsupported;
            }
        };

        let activation = Literal::positive(self.solver.new_var());
        match engine.add_encoded_cnf_with_fresh_aux(&mut self.solver, &cnf, Some(activation)) {
            AddCnfOutcome::Added => {
                #[cfg(test)]
                {
                    // Count the encoded clauses directly: the solver defers
                    // arena insertion between incremental solves (IC3
                    // deferral), so an arena-count delta silently under-counts
                    // every probe after the first solve.
                    self.bound_clause_growth_since_construction += cnf.clauses.len();
                }
                engine.solve_solver_with_assumptions(&mut self.solver, &[activation])
            }
            AddCnfOutcome::Unsat => QueryOutcome::Unsat,
            AddCnfOutcome::Unsupported => QueryOutcome::Unsupported,
        }
    }

    #[cfg(test)]
    fn uses_persistent_bounds(&self) -> bool {
        self.persistent_bounds.is_some()
    }

    #[cfg(test)]
    fn persistent_bound_kind(&self) -> Option<PersistentBoundKind> {
        self.persistent_bounds.as_ref().map(|bounds| bounds.kind)
    }

    #[cfg(test)]
    fn bound_clause_growth_since_construction(&self) -> usize {
        self.bound_clause_growth_since_construction
    }

    #[cfg(test)]
    fn bound_bdd_gap_pool(&self) -> u64 {
        self.bound_bdd_gap_pool
    }

    /// Test hook: overrides the session-level gap-row BDD pool so pool
    /// exhaustion across probes is exercisable without million-node BDDs.
    #[cfg(test)]
    fn set_bound_bdd_gap_pool(&mut self, pool: u64) {
        self.bound_bdd_gap_pool = pool;
    }
}

pub(crate) mod linear {
    use super::*;

    pub(crate) fn solve(engine: &mut OptimizationEngine<'_>) -> OptResult {
        let initial = match engine.solve_base_query() {
            QueryOutcome::Sat {
                assignment,
                obj_value,
            } => (assignment, obj_value),
            QueryOutcome::Unsat => return OptResult::Infeasible,
            QueryOutcome::Unknown | QueryOutcome::Unsupported => return OptResult::Unknown,
        };

        let (mut best_assignment, mut best_value) = initial;
        let lower_bound = engine.objective_lower_bound().min(best_value);
        engine.report_improvement(best_value);
        if best_value <= lower_bound {
            return OptResult::Optimal(best_assignment, best_value);
        }

        if engine.should_stop_now() {
            return OptResult::Satisfiable(best_assignment, best_value);
        }

        let mut query_session = engine.upper_bound_query_session(&[]);
        loop {
            let Some(next_bound) = best_value.checked_sub(1) else {
                return OptResult::Optimal(best_assignment, best_value);
            };
            if next_bound < lower_bound {
                return OptResult::Optimal(best_assignment, best_value);
            }

            match query_session.solve(engine, next_bound) {
                QueryOutcome::Sat {
                    assignment,
                    obj_value,
                } => {
                    if obj_value >= best_value {
                        return OptResult::Satisfiable(best_assignment, best_value);
                    }

                    best_assignment = assignment;
                    best_value = obj_value;
                    engine.report_improvement(best_value);
                    if best_value <= lower_bound {
                        return OptResult::Optimal(best_assignment, best_value);
                    }
                    if engine.should_stop_now() {
                        return OptResult::Satisfiable(best_assignment, best_value);
                    }
                }
                QueryOutcome::Unsat => return OptResult::Optimal(best_assignment, best_value),
                QueryOutcome::Unknown | QueryOutcome::Unsupported => {
                    return OptResult::Satisfiable(best_assignment, best_value);
                }
            }
        }
    }
}

pub(crate) mod binary_search {
    use super::*;

    pub(crate) fn solve(engine: &mut OptimizationEngine<'_>) -> OptResult {
        let initial = match engine.solve_base_query() {
            QueryOutcome::Sat {
                assignment,
                obj_value,
            } => (assignment, obj_value),
            QueryOutcome::Unsat => return OptResult::Infeasible,
            QueryOutcome::Unknown | QueryOutcome::Unsupported => return OptResult::Unknown,
        };

        let (best_assignment, best_value) = initial;
        engine.report_improvement(best_value);
        let stats = engine.objective_stats();
        // Binary search uses the lower bound purely as a standalone floor for
        // `binary_refine` (it is never *added* to a core accumulation), so the
        // sound LP bound is safe to fold in here via `combined_objective_lower_bound`.
        let structural = engine.objective_lower_bound_from_stats(stats);
        let lower_bound_floor = engine
            .combined_objective_lower_bound(structural)
            .min(best_value);
        if best_value <= lower_bound_floor {
            return OptResult::Optimal(best_assignment, best_value);
        }
        if engine.should_stop_now() {
            return OptResult::Satisfiable(best_assignment, best_value);
        }
        if let Some(extracted) = engine.extract_weighted_core_guided_state() {
            let lower_bound = match extracted.status {
                LowerBoundStatus::Complete(lb) => lower_bound_floor.max(lb).min(best_value),
                LowerBoundStatus::Interrupted(_) => {
                    return OptResult::Satisfiable(best_assignment, best_value);
                }
            };
            return engine.binary_refine_with_clauses(
                best_assignment,
                best_value,
                lower_bound,
                &extracted.learned_clauses,
            );
        }

        engine.binary_refine(best_assignment, best_value, lower_bound_floor)
    }
}

pub(crate) mod core_guided {
    use super::*;

    pub(crate) fn solve(engine: &mut OptimizationEngine<'_>) -> OptResult {
        let initial = match engine.solve_base_query() {
            QueryOutcome::Sat {
                assignment,
                obj_value,
            } => (assignment, obj_value),
            QueryOutcome::Unsat => return OptResult::Infeasible,
            QueryOutcome::Unknown | QueryOutcome::Unsupported => return OptResult::Unknown,
        };

        let (best_assignment, best_value) = initial;
        engine.report_improvement(best_value);
        let stats = engine.objective_stats();
        // Seed for OLL's *additive* core accumulation: structural-only. Folding the
        // LP bound in here would double-count (OLL adds core weights on top), so the
        // LP bound is applied separately as a terminal clamp inside
        // `finish_oll_optimum` and as the fallback floor below.
        let structural_lower_bound = engine
            .objective_lower_bound_from_stats(stats)
            .min(best_value);
        // The combined (structural + LP) bound is a sound standalone floor and is
        // safe for the initial optimality short-circuit and the binary-refine floor.
        let combined_lower_bound = engine
            .combined_objective_lower_bound(structural_lower_bound)
            .min(best_value);
        if best_value <= combined_lower_bound {
            return OptResult::Optimal(best_assignment, best_value);
        }
        if engine.should_stop_now() {
            return OptResult::Satisfiable(best_assignment, best_value);
        }

        // Primary path: genuine OLL (RC2-style) core-guided loop with totalizer
        // relaxations over one persistent incremental solver. Returns `None` only
        // when the objective cannot be normalized into weighted soft literals, in
        // which case we fall back to the lower-bound-extraction + binary-refine
        // path below (which fits non-soft objective shapes).
        if let Some(result) =
            engine.solve_oll(best_assignment.clone(), best_value, structural_lower_bound)
        {
            return result;
        }

        let extracted = engine.extract_core_guided_state();
        let lower_bound = match extracted.status {
            LowerBoundStatus::Complete(lb) => combined_lower_bound.max(lb).min(best_value),
            LowerBoundStatus::Interrupted(_) => {
                return OptResult::Satisfiable(best_assignment, best_value);
            }
        };

        engine.binary_refine_with_clauses(
            best_assignment,
            best_value,
            lower_bound,
            &extracted.learned_clauses,
        )
    }
}

fn should_use_persistent_weighted_literal_bounds(
    weighted_literals: &[WeightedSoftLiteral],
    total_weight: i128,
) -> bool {
    if weighted_literals.len() < PERSISTENT_BOUND_MIN_TERMS
        || weighted_literals.len() > PERSISTENT_BOUND_MAX_TERMS
        || total_weight <= 0
        || total_weight > PERSISTENT_BOUND_MAX_TOTAL_WEIGHT
    {
        return false;
    }

    let estimated_work = match u64::try_from(weighted_literals.len()) {
        Ok(term_count) => {
            term_count.saturating_mul(u64::try_from(total_weight).unwrap_or(u64::MAX))
        }
        Err(_) => u64::MAX,
    };
    if estimated_work > PERSISTENT_BOUND_MAX_WORK {
        return false;
    }

    !weighted_literals.iter().all(|soft| soft.weight == 1)
}

fn should_use_persistent_unit_literal_bounds(term_count: usize) -> bool {
    if !(PERSISTENT_BOUND_MIN_TERMS..=PERSISTENT_BOUND_MAX_TERMS).contains(&term_count) {
        return false;
    }

    let estimated_clause_work = match u64::try_from(term_count) {
        Ok(term_count) => term_count
            .checked_mul(term_count)
            .and_then(|work| work.checked_mul(4))
            .unwrap_or(u64::MAX),
        Err(_) => u64::MAX,
    };
    estimated_clause_work <= PERSISTENT_UNIT_BOUND_MAX_CLAUSE_WORK
}

fn encode_cardinality_with_outputs_interruptible<F>(
    lits: &[i32],
    clauses: &mut Vec<Vec<i32>>,
    next_var: &mut u32,
    should_stop: &mut F,
) -> Option<Vec<(i128, i32)>>
where
    F: FnMut() -> bool,
{
    let n = lits.len();
    if n == 0 {
        return Some(Vec::new());
    }
    if should_stop() {
        return None;
    }

    let k = n;
    let base = *next_var;
    *next_var += (n * k) as u32;
    let r = |i: usize, j: usize| -> i32 { (base + (i * k + j) as u32) as i32 };

    let mut poll_counter = 0usize;
    clauses.push(vec![-lits[0], r(0, 0)]);
    clauses.push(vec![-r(0, 0), lits[0]]);
    for j in 1..k {
        if persistent_bound_poll(should_stop, &mut poll_counter) {
            return None;
        }
        clauses.push(vec![-r(0, j)]);
    }

    for (i, _) in lits.iter().enumerate().take(n).skip(1) {
        if persistent_bound_poll(should_stop, &mut poll_counter) {
            return None;
        }

        for j in 0..k {
            if persistent_bound_poll(should_stop, &mut poll_counter) {
                return None;
            }

            clauses.push(vec![-r(i - 1, j), r(i, j)]);
            if j == 0 {
                clauses.push(vec![-lits[i], r(i, j)]);
            } else {
                clauses.push(vec![-lits[i], -r(i - 1, j - 1), r(i, j)]);
            }

            clauses.push(vec![-r(i, j), r(i - 1, j), lits[i]]);
            if j > 0 {
                clauses.push(vec![-r(i, j), r(i - 1, j), r(i - 1, j - 1)]);
            }
        }
    }

    Some((0..k).map(|j| ((j + 1) as i128, r(n - 1, j))).collect())
}

fn persistent_bound_poll<F>(should_stop: &mut F, poll_counter: &mut usize) -> bool
where
    F: FnMut() -> bool,
{
    *poll_counter += 1;
    (*poll_counter).is_multiple_of(PERSISTENT_BOUND_STOP_POLL_INTERVAL) && should_stop()
}

fn pb_lit_to_sat_literal(lit: PbLit) -> Option<Literal> {
    let raw_var = lit.var.checked_sub(1)?;
    let variable = Variable::new(raw_var);
    Some(if lit.negated {
        Literal::negative(variable)
    } else {
        Literal::positive(variable)
    })
}

fn sat_literal_to_pb_lit(lit: Literal) -> Option<PbLit> {
    pb_lit_from_dimacs(literal_to_dimacs(lit))
}

fn pb_lit_from_dimacs(dimacs: i32) -> Option<PbLit> {
    if dimacs == 0 || dimacs == i32::MIN {
        return None;
    }

    Some(PbLit {
        var: dimacs.unsigned_abs(),
        negated: dimacs < 0,
    })
}

fn complement_pb_lit(lit: PbLit) -> PbLit {
    PbLit {
        var: lit.var,
        negated: !lit.negated,
    }
}

fn native_core_probe_objective(
    active_softs: &[WeightedSoftLiteral],
) -> Option<(PbObjective, Vec<PbLit>, HashMap<PbLit, (PbLit, i128)>)> {
    let mut terms = Vec::with_capacity(active_softs.len());
    let mut assumptions = Vec::with_capacity(active_softs.len());
    let mut contribution_by_assumption = HashMap::new();

    for soft in active_softs {
        if soft.weight <= 0 {
            return None;
        }

        let objective_lit = sat_literal_to_pb_lit(soft.literal)?;
        let assumption = complement_pb_lit(objective_lit);
        if contribution_by_assumption
            .insert(assumption, (objective_lit, soft.weight))
            .is_some()
        {
            return None;
        }
        assumptions.push(assumption);
        terms.push(PbTerm {
            coeff: soft.weight,
            lits: vec![objective_lit],
        });
    }

    if terms.is_empty() {
        return None;
    }

    Some((
        PbObjective { terms },
        assumptions,
        contribution_by_assumption,
    ))
}

fn native_core_probe_instance(base_cnf: &EncodedCnf, objective: PbObjective) -> Option<PbInstance> {
    let constraints: Vec<PbConstraint> = base_cnf
        .clauses
        .iter()
        .map(|clause| {
            let terms: Option<Vec<PbTerm>> = clause
                .iter()
                .map(|&lit| {
                    Some(PbTerm {
                        coeff: 1,
                        lits: vec![pb_lit_from_dimacs(lit)?],
                    })
                })
                .collect();

            Some(PbConstraint {
                terms: terms?,
                rel: PbRel::Ge,
                rhs: 1,
            })
        })
        .collect::<Option<Vec<_>>>()?;
    let num_constraints = u32::try_from(constraints.len()).ok()?;

    Some(PbInstance {
        num_vars: base_cnf.num_vars,
        num_constraints,
        constraints,
        objective: Some(objective),
    })
}

fn native_core_probe_result_from_core(
    core: Vec<PbLit>,
    contribution_by_assumption: &HashMap<PbLit, (PbLit, i128)>,
) -> Option<PbCdclOptimizationCoreProbeResult> {
    if core.is_empty() {
        return None;
    }

    let mut lower_bound: Option<i128> = None;
    let mut seen = HashSet::new();
    let mut weighted_core = Vec::with_capacity(core.len());
    for assumption in &core {
        if !seen.insert(*assumption) {
            return None;
        }

        let &(objective_lit, contribution) = contribution_by_assumption.get(assumption)?;
        if contribution <= 0 {
            return None;
        }
        lower_bound = Some(match lower_bound {
            Some(current) => current.min(contribution),
            None => contribution,
        });
        weighted_core.push(PbCdclOptimizationCoreWeightedAssumption {
            assumption: *assumption,
            objective_lit,
            contribution,
        });
    }

    weighted_core.sort_by_key(|entry| {
        (
            entry.objective_lit.var,
            entry.objective_lit.negated,
            entry.assumption.var,
            entry.assumption.negated,
            entry.contribution,
        )
    });

    Some(PbCdclOptimizationCoreProbeResult::Evidence(
        PbCdclOptimizationCoreEvidence {
            core,
            lower_bound: lower_bound?,
            weighted_core,
            model: None,
        },
    ))
}

fn literal_to_dimacs(lit: Literal) -> i32 {
    lit.to_dimacs()
}

fn literal_from_dimacs(dimacs: i32) -> Literal {
    Literal::from_dimacs(dimacs)
}

fn normalize_product_literals(lits: &[PbLit]) -> Option<ProductLiteral> {
    let mut normalized = Vec::with_capacity(lits.len());
    for lit in lits {
        let dimacs = literal_to_dimacs(pb_lit_to_sat_literal(*lit)?);
        if normalized.contains(&-dimacs) {
            return Some(ProductLiteral::ConstantFalse);
        }
        if !normalized.contains(&dimacs) {
            normalized.push(dimacs);
        }
    }
    normalized.sort_unstable();
    Some(ProductLiteral::Factors(normalized))
}

fn normalized_dimacs_clause(mut clause: Vec<i32>) -> Vec<i32> {
    clause.sort_unstable();
    clause.dedup();
    clause
}

fn midpoint(low: i128, high: i128) -> i128 {
    saturating_i128_to_i64(i128::midpoint(low, high))
}

// Inert i64-era helpers: objective/bound values are already `i128`. Explicit
// no-ops (the real overflow handling is the checked/saturating arithmetic in the
// bound computations) — keeps clippy's absurd-comparison lint quiet without a
// blanket #![allow].
fn saturating_i128_to_i64(value: i128) -> i128 {
    value
}

fn checked_i128_to_i64(value: i128) -> Option<i128> {
    Some(value)
}

#[cfg(test)]
mod tests;
