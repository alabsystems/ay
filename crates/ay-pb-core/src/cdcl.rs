// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Native pseudo-Boolean CDCL solver.
//!
//! Implements a complete CDCL loop using the PB propagation engine from
//! `propagation.rs` and cutting-planes conflict analysis from
//! `cutting_planes.rs`. This is the PBS (Pseudo-Boolean Satisfiability) track
//! solver for the PB competition.
//!
//! Architecture follows RoundingSat (Elffers & Nordstrom, 2018):
//! - Decision: VSIDS-like variable activity scoring
//! - Propagation: Watched-slack PB propagation
//! - Conflict analysis: Cutting-planes resolution to derive asserting constraint
//! - Backtracking: Non-chronological backtrack to assertion level
//! - Restarts: Luby sequence restart schedule
//!
//! Reference: "Divide and Conquer: Towards Faster Pseudo-Boolean Solving"
//! (Elffers & Nordstrom, SAT 2018)

use std::collections::{BTreeMap as HashMap, BTreeSet as HashSet};
use std::io::Write;

use crate::cp_dense::{DenseCp, HeuristicResolveCapture};
use crate::cutting_planes::{gcd_i64, negate_lit, CpConstraint};
use crate::objective_bound::strictly_better_than_incumbent_constraint;
use crate::preprocess::{preprocess, preprocess_interruptible, PreprocessResult};
use crate::proof::tap::ProofTap;
use crate::proof::{
    self, format_constraint, format_lit, veripb_input_constraint_count, ConstraintId, ProofError,
    ProofStep, VeriPbWriter,
};
use crate::propagation::{Lit, LitValue, PbNativeHelperStats, PbPropagator, PropResult};
use crate::solver::{eval_objective, objective_range_fits_i64};
use crate::types::{PbConstraint, PbInstance, PbLit, PbObjective, PbRel, PbTerm};

mod conflict_cp;
mod conflict_dense;
mod objective_bound;
mod proof_logging;
mod search_maintenance;

const CONSTRUCTOR_LOAD_STOP_POLL_INTERVAL: usize = 256;
/// How many propagated literals to process between wall-clock deadline polls in
/// `propagate_all_interruptible`. `should_stop()` reads `Instant::now`, a
/// syscall that profiling found was ~10% of runtime when called per literal.
/// The cheap `interrupted` flag is still checked every iteration, so the
/// deadline is still honored within ~this many fast propagations (microseconds).
const DEADLINE_POLL_STRIDE: usize = 256;
const ROOT_PROPAGATION_IMPORT_BATCH_INTERVAL: usize = 4096;
const ROOT_PROPAGATION_IMPORT_TERM_POLL_INTERVAL: usize = 256;
const ROOT_PROPAGATION_IMPORT_BATCH_TERM_INTERVAL: usize = 4096;
const ROOT_PROPAGATION_IMPORT_MAX_TERMS_PER_CONSTRAINT: usize = 65_536;
const OBJECTIVE_BOUND_NEIGHBOR_ACTIVITY_SCALE: f64 = 0.25;
const OBJECTIVE_BOUND_NEIGHBOR_MAX_ROW_TERMS: usize = 512;

/// Wall-clock backstop for the single root LP-relaxation lower-bound computation
/// in the native optimization loop. The LP bound is *anytime-sound* (any
/// dual-feasible vertex gives a valid bound), so aborting early only loosens the
/// bound, never breaks soundness. This guards against an exact-rational simplex
/// whose big-integer arithmetic grows large on a pathological instance, and it
/// applies even when the caller passes a no-op `should_stop` (e.g. the
/// non-interruptible `solve_optimize` path used in tests).
const ROOT_LP_BOUND_TIME_BUDGET: std::time::Duration = std::time::Duration::from_secs(5);

/// Denominator of the share of the REMAINING solve deadline granted to the root
/// LP bound when the caller has threaded a deadline via
/// [`PbCdclSolver::set_solve_deadline`]: the effective budget is
/// `min(ROOT_LP_BOUND_TIME_BUDGET, remaining / ROOT_LP_BOUND_DEADLINE_FRACTION)`.
/// A 10s optimize call thus spends at most ~2.5s on the LP floor instead of the
/// flat 5s, leaving the search the majority of the budget. Without a threaded
/// deadline the flat [`ROOT_LP_BOUND_TIME_BUDGET`] backstop applies unchanged.
/// Shrinking the budget only ever weakens (never unsounds) the anytime LP bound.
const ROOT_LP_BOUND_DEADLINE_FRACTION: u32 = 4;

/// Effective wall-clock budget for the single root LP bound given the remaining
/// time to an (optional) caller-threaded solve deadline. Pure so it is unit
/// testable: `min(cap, remaining / fraction)`, or the flat cap when no deadline
/// was threaded.
fn root_lp_budget_for(remaining: Option<std::time::Duration>) -> std::time::Duration {
    match remaining {
        Some(remaining) => {
            (remaining / ROOT_LP_BOUND_DEADLINE_FRACTION).min(ROOT_LP_BOUND_TIME_BUDGET)
        }
        None => ROOT_LP_BOUND_TIME_BUDGET,
    }
}

/// Opt-in env var that folds the sound LP-relaxation lower bound into the *native
/// CDCL* optimization loop's optimality-termination floor (the `solve_optimize` /
/// `solve_optimize_interruptible` linear SAT-UNSAT path). Default ON for the
/// competition (see below): an instance whose LP relaxation is tight can be
/// *proved* OPTIMAL the moment its first optimal incumbent is in hand instead of
/// returning a (sound but unproven) `Feasible`. The bound is used ONLY to raise
/// the termination floor — never to alter an incumbent — so it can never change a
/// reported objective value, only upgrade `Feasible` -> `Optimal` soundly. This
/// directly closes optimality on OPT/SOFT/PARTIAL instances, where a plain
/// `Feasible`/`SATISFIABLE` answer scores zero (the competition ranks on the
/// count of *definitive* answers: OPTIMUM FOUND or UNSATISFIABLE). Opt out with
/// `AY_PB_NATIVE_LP_BOUND=0` (also `false`/`no`/`off`).
const NATIVE_LP_BOUND_ENV: &str = "AY_PB_NATIVE_LP_BOUND";

/// Whether the native-loop LP lower bound is enabled (see [`NATIVE_LP_BOUND_ENV`]).
/// Default ON; read once and memoized. The bound is a sound lower bound that only
/// raises the optimality-termination floor, so enabling it can never produce a
/// wrong answer — only prove optimality sooner.
pub(crate) fn native_lp_bound_enabled() -> bool {
    use std::sync::OnceLock;
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| match std::env::var(NATIVE_LP_BOUND_ENV) {
        Ok(v) => {
            let v = v.trim().to_ascii_lowercase();
            !(v.is_empty() || v == "0" || v == "false" || v == "no" || v == "off")
        }
        Err(_) => true,
    })
}

/// Whether the Luby restart-starvation floor is enabled (see `should_restart`).
/// Default ON; set `AY_PB_NO_RESTART_FLOOR` (non-empty, non-`0`) to disable —
/// used to A/B the dense-PB restart win. Without the floor, dense-PB search can
/// run with ZERO restarts because the glucose LBD ratio never fires.
pub(crate) fn restart_floor_enabled() -> bool {
    // B14: typed A/B switch (`ab_switches`); the never-set env read is gone.
    crate::ab_switches::get().restart_floor
}

/// Learned-constraint activity decay: the per-conflict increment is divided by
/// this factor each conflict so recently-useful lemmas keep a higher activity
/// (VSIDS-style geometric ageing). Matches Glucose's clause-activity decay.
/// Only consulted when `learned_activity_reducedb_enabled` is set.
const LEARNED_ACTIVITY_DECAY: f64 = 0.999;
/// Rescale threshold for learned-constraint activities. When any activity (or
/// the increment) exceeds this, all activities and the increment are scaled down
/// by its reciprocal to avoid f64 overflow. Standard VSIDS rescale.
const LEARNED_ACTIVITY_RESCALE_LIMIT: f64 = 1e100;
/// `reduce_db` protection (opt-in tier): learned constraints with at most this
/// many literals are never deleted (short lemmas propagate cheaply and are
/// re-derived rarely). Only consulted when the opt-in flag is set.
const REDUCE_DB_PROTECT_SIZE: usize = 2;
/// Opt-in growing `reduce_db` cadence: the effective interval grows by this many
/// conflicts after each `reduce_db` call, so the learned DB is allowed to grow
/// as search deepens (Glucose/MiniSat-style increasing reduce interval). Only
/// consulted when `learned_activity_reducedb_enabled` is set.
const REDUCE_DB_INTERVAL_GROWTH: u64 = 300;

/// Result of the PB CDCL solver.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum PbCdclResult {
    /// All constraints satisfiable; assignment is a model.
    Satisfiable(Vec<bool>),
    /// Constraints are unsatisfiable.
    Unsatisfiable,
    /// Solver was interrupted (timeout or external signal).
    Unknown,
    /// Optimal solution found with proven minimum objective value.
    /// Contains (model, objective_value).
    Optimal(Vec<bool>, i128),
    /// Feasible solution found but optimality not proven (interrupted).
    /// Contains (model, objective_value).
    Feasible(Vec<bool>, i128),
}

/// Result of solving under temporary assumption literals.
///
/// This API is intentionally conservative: learned constraints produced while
/// searching under assumptions are retained because they are implied by the
/// original constraints, but SAT/UNSAT proof conclusions for temporary
/// assumptions are not emitted. Callers must treat `Unknown` and `Unsupported`
/// as no-core outcomes.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum PbCdclAssumptionResult {
    /// All constraints and assumptions are satisfiable; assignment is a model.
    Satisfiable(Vec<bool>),
    /// Constraints are unsatisfiable under the returned assumption core.
    ///
    /// The core is sound but not guaranteed minimal. The first implementation
    /// returns all active assumptions for search conflicts, with small
    /// syntactic contradictions trimmed exactly.
    Unsatisfiable { core: Vec<PbLit> },
    /// Solver was interrupted or the query failed closed.
    Unknown,
    /// Assumption solving is unsupported for this solver configuration.
    Unsupported,
}

/// Outcome of adding a constraint to a live solver via the runtime var-pool API.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum RuntimeConstraintOutcome {
    /// The constraint was added (and any level-0 implications propagated) without
    /// a root conflict.
    Added,
    /// Adding the constraint and propagating at level 0 produced a conflict: the
    /// constraint set is now unsatisfiable.
    Conflict,
    /// The runtime add is unsupported in the current configuration (proof logging
    /// on, called above decision level 0, or a literal referenced an unallocated
    /// variable). Fails closed: the caller must treat this as "could not add".
    Unsupported,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(dead_code)]
pub(crate) struct PbCdclOptimizationCoreEvidence {
    pub(crate) core: Vec<PbLit>,
    pub(crate) lower_bound: i128,
    pub(crate) weighted_core: Vec<PbCdclOptimizationCoreWeightedAssumption>,
    pub(crate) model: Option<Vec<bool>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
pub(crate) struct PbCdclOptimizationUnsatCoreEvidence<'a> {
    core: &'a [PbLit],
    lower_bound: i128,
    weighted_core: &'a [PbCdclOptimizationCoreWeightedAssumption],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
pub(crate) struct PbCdclOptimizationCoreSummary {
    core_len: usize,
    lower_bound: i128,
    total_contribution: i128,
    fingerprint: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
pub(crate) struct PbCdclAcceptedOptimizationUnsatCore<'a> {
    evidence: PbCdclOptimizationUnsatCoreEvidence<'a>,
    summary: PbCdclOptimizationCoreSummary,
}

#[allow(dead_code)]
impl<'a> PbCdclAcceptedOptimizationUnsatCore<'a> {
    pub(crate) fn evidence(&self) -> PbCdclOptimizationUnsatCoreEvidence<'a> {
        self.evidence
    }

    pub(crate) fn summary(&self) -> PbCdclOptimizationCoreSummary {
        self.summary
    }
}

#[allow(dead_code)]
impl PbCdclOptimizationUnsatCoreEvidence<'_> {
    pub(crate) fn core(&self) -> &[PbLit] {
        self.core
    }

    pub(crate) fn lower_bound(&self) -> i128 {
        self.lower_bound
    }

    pub(crate) fn weighted_core(&self) -> &[PbCdclOptimizationCoreWeightedAssumption] {
        self.weighted_core
    }

    pub(crate) fn summary(&self) -> Option<PbCdclOptimizationCoreSummary> {
        PbCdclOptimizationCoreSummary::from_evidence(
            self.core,
            self.lower_bound,
            self.weighted_core,
        )
    }
}

#[allow(dead_code)]
impl PbCdclOptimizationCoreSummary {
    pub(crate) fn core_len(&self) -> usize {
        self.core_len
    }

    pub(crate) fn lower_bound(&self) -> i128 {
        self.lower_bound
    }

    pub(crate) fn total_contribution(&self) -> i128 {
        self.total_contribution
    }

    pub(crate) fn fingerprint(&self) -> u64 {
        self.fingerprint
    }

    /// Conservative acceptance guard for optimizer consumers that carry a
    /// previously accepted native-core lower bound.
    pub(crate) fn is_safe_optimizer_successor_of(&self, previous: Option<&Self>) -> bool {
        if !self.has_exact_contribution_invariants() {
            return false;
        }

        match previous {
            Some(previous) => {
                previous.has_exact_contribution_invariants()
                    && self.lower_bound >= previous.lower_bound
            }
            None => true,
        }
    }

    fn has_exact_contribution_invariants(&self) -> bool {
        if self.core_len == 0 || self.lower_bound <= 0 || self.total_contribution <= 0 {
            return false;
        }

        let Ok(core_len) = i128::try_from(self.core_len) else {
            return false;
        };
        let Some(min_total) = self.lower_bound.checked_mul(core_len) else {
            return false;
        };

        self.total_contribution >= min_total
    }

    fn from_evidence(
        core: &[PbLit],
        lower_bound: i128,
        weighted_core: &[PbCdclOptimizationCoreWeightedAssumption],
    ) -> Option<Self> {
        if core.is_empty() || core.len() != weighted_core.len() {
            return None;
        }

        let mut core_set = HashSet::new();
        for assumption in core {
            if !core_set.insert(*assumption) {
                return None;
            }
        }

        let mut seen_weighted = HashSet::new();
        let mut min_contribution: Option<i128> = None;
        let mut total_contribution = 0i128;
        let mut signature_entries = Vec::with_capacity(weighted_core.len());

        for entry in weighted_core {
            if !seen_weighted.insert(entry.assumption) || !core_set.contains(&entry.assumption) {
                return None;
            }
            if entry.objective_lit != complement_pb_lit(entry.assumption) || entry.contribution <= 0
            {
                return None;
            }

            total_contribution = total_contribution.checked_add(entry.contribution)?;
            min_contribution = Some(match min_contribution {
                Some(current) => current.min(entry.contribution),
                None => entry.contribution,
            });
            signature_entries.push((
                entry.objective_lit.var,
                entry.objective_lit.negated,
                entry.assumption.var,
                entry.assumption.negated,
                entry.contribution,
            ));
        }

        if min_contribution? != lower_bound {
            return None;
        }

        signature_entries.sort_by_key(|entry| (entry.0, entry.1, entry.2, entry.3, entry.4));

        let mut fingerprint = 0xcbf29ce484222325u64;
        for (objective_var, objective_negated, assumption_var, assumption_negated, contribution) in
            signature_entries
        {
            fingerprint = stable_core_summary_mix(fingerprint, u64::from(objective_var));
            fingerprint = stable_core_summary_mix(fingerprint, u64::from(objective_negated));
            fingerprint = stable_core_summary_mix(fingerprint, u64::from(assumption_var));
            fingerprint = stable_core_summary_mix(fingerprint, u64::from(assumption_negated));
            // `contribution` is i128; fold BOTH 64-bit halves into the fingerprint so
            // a large (>u64) coefficient contribution cannot alias to a different core
            // summary (a collision would be sound but could cost a missed dedup/bound).
            // Matches the lns.rs coefficient-hash idiom.
            fingerprint = stable_core_summary_mix(
                fingerprint,
                (contribution as u64) ^ ((contribution >> 64) as u64),
            );
        }

        Some(Self {
            core_len: core.len(),
            lower_bound,
            total_contribution,
            fingerprint,
        })
    }
}

#[allow(dead_code)]
impl PbCdclOptimizationCoreEvidence {
    fn satisfiable_model(model: Vec<bool>) -> Self {
        Self {
            core: Vec::new(),
            lower_bound: 0,
            weighted_core: Vec::new(),
            model: Some(model),
        }
    }

    fn unsat_core(core: Vec<PbLit>, bound: PbCdclOptimizationCoreBound) -> Self {
        Self {
            core,
            lower_bound: bound.lower_bound,
            weighted_core: bound.weighted_core,
            model: None,
        }
    }

    pub(crate) fn core(&self) -> &[PbLit] {
        &self.core
    }

    pub(crate) fn lower_bound(&self) -> i128 {
        self.lower_bound
    }

    pub(crate) fn weighted_core(&self) -> &[PbCdclOptimizationCoreWeightedAssumption] {
        &self.weighted_core
    }

    pub(crate) fn model(&self) -> Option<&[bool]> {
        self.model.as_deref()
    }

    pub(crate) fn as_satisfiable_model(&self) -> Option<&[bool]> {
        self.model.as_deref()
    }

    pub(crate) fn as_unsat_core(&self) -> Option<PbCdclOptimizationUnsatCoreEvidence<'_>> {
        if self.model.is_some() {
            return None;
        }

        Some(PbCdclOptimizationUnsatCoreEvidence {
            core: &self.core,
            lower_bound: self.lower_bound,
            weighted_core: &self.weighted_core,
        })
    }

    pub(crate) fn unsat_core_summary(&self) -> Option<PbCdclOptimizationCoreSummary> {
        self.as_unsat_core()?.summary()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(dead_code)]
pub(crate) enum PbCdclOptimizationCoreProbeResult {
    Evidence(PbCdclOptimizationCoreEvidence),
    Unknown,
    Unsupported(PbCdclOptimizationCoreUnsupportedReason),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
pub(crate) enum PbCdclOptimizationCoreUnsupportedReason {
    ProofWriterEnabled,
    AssumptionSolvingUnsupported,
    NonSingleLiteralTerm,
    NegativeCoefficient,
    EmptyObjective,
    WeightOverflow,
}

#[allow(dead_code)]
impl PbCdclOptimizationCoreProbeResult {
    pub(crate) fn evidence(&self) -> Option<&PbCdclOptimizationCoreEvidence> {
        match self {
            Self::Evidence(evidence) => Some(evidence),
            Self::Unknown | Self::Unsupported(_) => None,
        }
    }

    pub(crate) fn unsupported_reason(&self) -> Option<PbCdclOptimizationCoreUnsupportedReason> {
        match self {
            Self::Unsupported(reason) => Some(*reason),
            Self::Evidence(_) | Self::Unknown => None,
        }
    }

    pub(crate) fn accepted_unsat_core(
        &self,
        previous: Option<&PbCdclOptimizationCoreSummary>,
    ) -> Option<PbCdclAcceptedOptimizationUnsatCore<'_>> {
        let evidence = self.evidence()?.as_unsat_core()?;
        let summary = evidence.summary()?;
        summary
            .is_safe_optimizer_successor_of(previous)
            .then_some(PbCdclAcceptedOptimizationUnsatCore { evidence, summary })
    }

    pub(crate) fn accepted_unsat_core_summary(
        &self,
        previous: Option<&PbCdclOptimizationCoreSummary>,
    ) -> Option<PbCdclOptimizationCoreSummary> {
        self.accepted_unsat_core(previous)
            .map(|accepted| accepted.summary())
    }

    pub(crate) fn accepted_unsat_core_evidence(
        &self,
        previous: Option<&PbCdclOptimizationCoreSummary>,
    ) -> Option<PbCdclOptimizationUnsatCoreEvidence<'_>> {
        self.accepted_unsat_core(previous)
            .map(|accepted| accepted.evidence())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(dead_code)]
pub(crate) struct PbCdclOptimizationCoreWeightedAssumption {
    pub(crate) assumption: PbLit,
    pub(crate) objective_lit: PbLit,
    pub(crate) contribution: i128,
}

#[allow(dead_code)]
impl PbCdclOptimizationCoreWeightedAssumption {
    pub(crate) fn assumption(&self) -> PbLit {
        self.assumption
    }

    pub(crate) fn objective_lit(&self) -> PbLit {
        self.objective_lit
    }

    pub(crate) fn contribution(&self) -> i128 {
        self.contribution
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(dead_code)]
struct PbCdclOptimizationCoreBound {
    lower_bound: i128,
    weighted_core: Vec<PbCdclOptimizationCoreWeightedAssumption>,
}

struct NativeConstraintImport {
    propagator: PbPropagator,
    constraints: Vec<PbConstraint>,
    interrupted: bool,
}

impl NativeConstraintImport {
    fn empty(interrupted: bool) -> Self {
        Self {
            propagator: PbPropagator::new(),
            constraints: Vec::new(),
            interrupted,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NativeImportCheck {
    Ready { term_visits: usize },
    UnsupportedNonlinear,
    Interrupted,
}

/// Statistics for the CDCL solver run.
#[derive(Debug, Clone, Default)]
pub struct PbCdclStats {
    /// Total decisions made.
    pub decisions: u64,
    /// Total conflicts encountered.
    pub conflicts: u64,
    /// Total propagations performed.
    pub propagations: u64,
    /// Total restarts triggered.
    pub restarts: u64,
    /// Learned constraints added.
    pub learned: u64,
    /// Learned constraints deleted by `reduce_db`.
    pub learned_deletions: u64,
    /// Number of `reduce_db` invocations.
    pub reduce_db_calls: u64,
    pub glucose_restarts: u64,
    pub luby_restarts: u64,
    pub avg_lbd: f64,
    /// Number of learned constraints where strengthening reduced coefficient count
    /// or degree (saturation + GCD + weakening pipeline).
    pub strengthened: u64,
    /// Number of resolution steps that used the round-to-one division rule.
    pub round_to_one_count: u64,
    /// Number of resolution steps that fell back to standard addition
    /// (overflow or division not applicable).
    pub round_to_one_fallback_count: u64,
    /// Number of dense conflict-analysis resolution steps that used the PROVEN
    /// round-to-one (Elffers & Nordstrom, IJCAI-18; reduce-reason-before-add).
    pub proven_round_to_one_count: u64,
    /// Number of dense conflict-analysis resolution steps where the proven
    /// round-to-one was not applicable (invalid pivot / overflow) and analysis
    /// fell back to the sound heuristic round-to-one path.
    pub proven_round_to_one_fallback_count: u64,
    /// Number of dense conflict-analysis resolution steps where BOTH the proven
    /// and heuristic round-to-one paths overflowed and analysis used the
    /// reduce-to-cardinality overflow fallback (RoundingSat `reduceToCardinality`,
    /// Elffers & Nordstrom IJCAI-18 Alg. 6). The fallback resolves implied
    /// unit-coefficient cardinality constraints, bounding coefficient growth.
    pub reduce_to_cardinality_count: u64,
    /// Number of times `record_learned_constraint_id` found the proof-id map
    /// out of lockstep with the constraint database (a constraint entered the
    /// database without a proof id). Nonzero means every later learned lemma
    /// silently degrades to the RUP proof fallback — this should stay 0.
    pub proof_id_lockstep_desyncs: u64,
    /// Number of solves decided by the single-equality knapsack subset-sum
    /// DP special case (see `crate::eq_knapsack`) instead of CDCL search.
    pub eq_knapsack_dp: u64,
}

/// Trail entry recording an assignment and its reason.
#[derive(Debug, Clone)]
struct TrailEntry {
    /// The literal assigned true.
    lit: Lit,
    /// Decision level at which this assignment was made.
    level: u32,
    /// Reason: None for decisions, Some(constraint_index) for propagations.
    /// Used during conflict analysis to resolve reasons.
    reason: Option<usize>,
}

/// Configuration for the CDCL solver (internal, not user-facing).
struct CdclConfig {
    /// Initial restart interval (Luby unit).
    restart_base: u64,
    /// Activity decay factor (multiplied by 1000 for integer arithmetic).
    activity_decay_milli: u64,
    /// Conflict interval between `reduce_db` calls.
    reduce_interval: u64,
    /// LBD threshold for tier1 "glue" constraints (never deleted).
    glue_lbd_threshold: u32,
    glucose_lbd_ratio_threshold: f64,
    min_restart_interval: u64,
    glucose_warmup_conflicts: u64,
    glucose_recent_window: u64,
    /// Runs a small failed-literal probing pass at decision level 0 before
    /// entering the main search loop.
    root_probe_enabled: bool,
    /// Maximum number of temporary literal probes performed per solve call.
    root_probe_max_probes: usize,
    /// Try one saved-phase completion pass before the initial optimization
    /// search. The produced model is accepted only after full constraint
    /// validation.
    phase_completion_enabled: bool,
    /// Opt-in (default OFF): enable VSIDS-style learned-constraint activity
    /// scoring plus the richer two-tier `reduce_db` (activity tiebreak on equal
    /// LBD, short-lemma size protection, on-reuse LBD refresh, growing reduce
    /// cadence). Purely a deletion-ranking / scheduling heuristic — it never
    /// changes which lemmas are derived, only which low-quality lemmas survive a
    /// reduction, so it cannot affect soundness. When OFF, `reduce_db` uses the
    /// historical LBD-descending sort and the fixed `reduce_interval` cadence.
    learned_activity_reducedb_enabled: bool,
    /// Default ON: decide single-equality 0/1 knapsacks (the Aardal_1 DEC-LIN
    /// family — one huge-coefficient equality as one `Eq` row or two
    /// complementary `Ge` rows) exactly by subset-sum bitset DP before
    /// entering CDCL search. Fail-closed: SAT witnesses are re-verified
    /// against every stored row, UNSAT requires two independent DP passes to
    /// agree, and every uncertain path falls back to normal search. Disabled
    /// automatically under proof logging (the DP derivation is not
    /// proof-logged). See [`crate::eq_knapsack`].
    eq_knapsack_dp_enabled: bool,
}

impl Default for CdclConfig {
    fn default() -> Self {
        Self {
            restart_base: 100,
            activity_decay_milli: 950,
            reduce_interval: 2000,
            glue_lbd_threshold: 2,
            glucose_lbd_ratio_threshold: 1.4,
            min_restart_interval: 50,
            glucose_warmup_conflicts: 100,
            glucose_recent_window: 50,
            root_probe_enabled: true,
            root_probe_max_probes: 8,
            phase_completion_enabled: false,
            learned_activity_reducedb_enabled: false,
            eq_knapsack_dp_enabled: true,
        }
    }
}

/// Row count above which the preprocessed solving instance is freed on a
/// detached thread instead of inline. Freeing a multi-million-row `PbInstance`
/// walks tens of millions of nested term/literal allocations (~0.25s measured
/// on the 6.4M-row lopes-172) and sits exactly between "solver built" and the
/// first search step; below this the thread spawn costs more than the free.
const BACKGROUND_DROP_MIN_ROWS: usize = 1_000_000;

/// Frees a huge preprocessed solving instance off the search critical path.
///
/// SOUNDNESS/MEMORY: this is a pure `drop` — no solver state references the
/// instance once construction returns (the import copies every row it needs).
/// The deferred bytes remain counted by the process allocator until the
/// background free completes, so the memory-ceiling guard still sees them and
/// can only trip EARLIER during the overlap window, never later — the
/// fail-closed direction. If the thread cannot be spawned, the closure (and
/// the instance it owns) is dropped inline right here, restoring the previous
/// behavior exactly.
fn drop_huge_instance_in_background(instance: PbInstance) {
    if instance.constraints.len() < BACKGROUND_DROP_MIN_ROWS {
        return;
    }
    let _ = std::thread::Builder::new()
        .name("pb-prep-drop".into())
        .stack_size(64 * 1024)
        .spawn(move || drop(instance));
}

fn should_stop_constructor_load<F>(should_stop: &mut F, poll_budget: &mut usize) -> bool
where
    F: FnMut() -> bool,
{
    *poll_budget -= 1;
    if *poll_budget == 0 {
        *poll_budget = CONSTRUCTOR_LOAD_STOP_POLL_INTERVAL;
        should_stop()
    } else {
        false
    }
}

fn check_linear_terms_import_interruptible<F>(
    terms: &[PbTerm],
    poll_budget: &mut usize,
    should_stop: &mut F,
) -> NativeImportCheck
where
    F: FnMut() -> bool,
{
    let mut term_visits = 0usize;
    for term in terms {
        if term.lits.len() > 1 {
            return NativeImportCheck::UnsupportedNonlinear;
        }
        term_visits = term_visits.saturating_add(1);
        if should_stop_constructor_load(should_stop, poll_budget) {
            return NativeImportCheck::Interrupted;
        }
    }
    NativeImportCheck::Ready { term_visits }
}

fn check_constraint_import_interruptible<F>(
    constraint: &PbConstraint,
    poll_budget: &mut usize,
    should_stop: &mut F,
) -> NativeImportCheck
where
    F: FnMut() -> bool,
{
    let mut term_visits = match check_linear_terms_import_interruptible(
        &constraint.terms,
        poll_budget,
        should_stop,
    ) {
        NativeImportCheck::Ready { term_visits } => term_visits,
        other => return other,
    };

    if constraint.rel == PbRel::Eq {
        match check_linear_terms_import_interruptible(&constraint.terms, poll_budget, should_stop) {
            NativeImportCheck::Ready {
                term_visits: eq_term_visits,
            } => {
                term_visits = term_visits.saturating_add(eq_term_visits);
            }
            other => return other,
        }
    }

    NativeImportCheck::Ready { term_visits }
}

fn import_native_constraints_interruptible<F>(
    solving_instance: &PbInstance,
    interrupted: bool,
    should_stop: &mut F,
) -> NativeConstraintImport
where
    F: FnMut() -> bool,
{
    let mut import = NativeConstraintImport::empty(interrupted);

    if should_stop() {
        import.interrupted = true;
    }

    if import.interrupted {
        return import;
    }

    let mut term_poll_budget = CONSTRUCTOR_LOAD_STOP_POLL_INTERVAL;
    if let Some(objective) = &solving_instance.objective {
        match check_linear_terms_import_interruptible(
            &objective.terms,
            &mut term_poll_budget,
            should_stop,
        ) {
            NativeImportCheck::Ready { .. } => {}
            NativeImportCheck::UnsupportedNonlinear | NativeImportCheck::Interrupted => {
                return NativeConstraintImport::empty(true);
            }
        }
    }

    // One up-front capacity pass. Import time is unchanged (the doubling
    // copies were never the bottleneck), but the exact reserve drops ~86MB of
    // RETAINED over-allocation on a 6.4M-row instance (measured via
    // `time -l` max RSS on lopes-172: 9.68GB -> 9.59GB) — the final doubling
    // of the constraint vectors otherwise overshoots by ~30% and that excess
    // capacity is held for the entire solve. `Eq` rows import as two internal
    // rows, so these are floors; capacity only, semantics unchanged.
    import.propagator.reserve_for_bulk_import(
        solving_instance.num_vars,
        solving_instance.constraints.len(),
    );
    import
        .constraints
        .reserve_exact(solving_instance.constraints.len());

    let mut load_poll_budget = CONSTRUCTOR_LOAD_STOP_POLL_INTERVAL;
    for constraint in &solving_instance.constraints {
        if should_stop_constructor_load(should_stop, &mut load_poll_budget) {
            return NativeConstraintImport::empty(true);
        }

        match check_constraint_import_interruptible(constraint, &mut term_poll_budget, should_stop)
        {
            NativeImportCheck::Ready { .. } => {}
            NativeImportCheck::UnsupportedNonlinear | NativeImportCheck::Interrupted => {
                return NativeConstraintImport::empty(true);
            }
        }

        let start = import.propagator.num_constraints();
        // Thread the (memory-aware) should_stop THROUGH the add so an
        // ultra-dense single row's normalize/sort/watch-arming fails closed
        // mid-constraint instead of only between constraints. One-time O(rows)
        // construction; Err(()) leaves the propagator to be discarded with the
        // returned interrupted import (caller yields Unknown — always sound).
        if import
            .propagator
            .add_from_pb_constraint_interruptible(constraint, should_stop)
            .is_err()
        {
            return NativeConstraintImport::empty(true);
        }
        let end = import.propagator.num_constraints();

        for cid in start..end {
            let internal_constraint = import
                .propagator
                .get_constraint_pb(cid)
                .expect("freshly added PB constraint must be addressable");
            import.constraints.push(internal_constraint);
        }
    }

    import
}

struct RootOnlyPropagationState {
    pending_sources: Vec<usize>,
    scan_cursor: usize,
    origin: PropagationOrigin,
}

#[derive(Debug, Clone, Copy)]
struct RootPropagationPrecheckLimits {
    import_batch_interval: usize,
    max_terms_per_constraint: usize,
}

impl Default for RootPropagationPrecheckLimits {
    fn default() -> Self {
        Self {
            import_batch_interval: ROOT_PROPAGATION_IMPORT_BATCH_INTERVAL,
            max_terms_per_constraint: ROOT_PROPAGATION_IMPORT_MAX_TERMS_PER_CONSTRAINT,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RootConstraintPrecheck {
    Linear { term_visits: usize },
    Unsupported,
    Interrupted,
}

fn check_root_precheck_constraint<F>(
    constraint: &PbConstraint,
    limits: RootPropagationPrecheckLimits,
    should_stop: &mut F,
) -> RootConstraintPrecheck
where
    F: FnMut() -> bool,
{
    if constraint.terms.len() > limits.max_terms_per_constraint {
        return RootConstraintPrecheck::Unsupported;
    }

    let mut term_poll_budget = ROOT_PROPAGATION_IMPORT_TERM_POLL_INTERVAL;
    let mut term_visits = 0usize;
    let passes = if constraint.rel == PbRel::Eq { 2 } else { 1 };
    for _ in 0..passes {
        for term in &constraint.terms {
            term_visits = term_visits.saturating_add(1);
            term_poll_budget -= 1;
            if term_poll_budget == 0 {
                term_poll_budget = ROOT_PROPAGATION_IMPORT_TERM_POLL_INTERVAL;
                if should_stop() {
                    return RootConstraintPrecheck::Interrupted;
                }
            }

            if term.lits.len() != 1 {
                return RootConstraintPrecheck::Unsupported;
            }
        }
    }

    RootConstraintPrecheck::Linear { term_visits }
}

fn propagate_root_only_interruptible<F>(
    propagator: &mut PbPropagator,
    state: &mut RootOnlyPropagationState,
    should_stop: &mut F,
) -> PropagateOutcome
where
    F: FnMut() -> bool,
{
    if should_stop() {
        return PropagateOutcome::Interrupted;
    }

    let mut result = if let Some(cid) = state.pending_sources.pop() {
        state.origin = PropagationOrigin::SourceRecheck;
        propagator.propagate_constraint_interruptible(cid, &mut *should_stop)
    } else if state.scan_cursor < propagator.num_constraints() {
        state.origin = PropagationOrigin::Scan;
        propagator.propagate_from_interruptible(state.scan_cursor, &mut *should_stop)
    } else {
        return PropagateOutcome::Ok;
    };

    loop {
        match result {
            PropResult::Ok => {
                if state.origin == PropagationOrigin::Scan {
                    state.scan_cursor = propagator.num_constraints();
                }
                if let Some(cid) = state.pending_sources.pop() {
                    state.origin = PropagationOrigin::SourceRecheck;
                    result = propagator.propagate_constraint_interruptible(cid, &mut *should_stop);
                    continue;
                }
                if state.scan_cursor < propagator.num_constraints() {
                    state.origin = PropagationOrigin::Scan;
                    result = propagator
                        .propagate_from_interruptible(state.scan_cursor, &mut *should_stop);
                    continue;
                }
                return PropagateOutcome::Ok;
            }
            PropResult::Interrupted => return PropagateOutcome::Interrupted,
            PropResult::Conflict(_, cid) => return PropagateOutcome::Conflict(cid),
            PropResult::Propagated(lit, _, cid) => {
                if state.origin == PropagationOrigin::Scan {
                    state.scan_cursor = cid.saturating_add(1);
                }
                state.pending_sources.push(cid);
                result = propagator.assign_literal_interruptible(lit, 0, &mut *should_stop);
                if matches!(result, PropResult::Ok) && should_stop() {
                    return PropagateOutcome::Interrupted;
                }
                state.origin = PropagationOrigin::Event;
            }
        }
    }
}

/// VSIDS binary min-heap for O(log n) variable selection.
///
/// Variables with higher activity are at the top. The heap stores variable
/// indices (1-based) and uses the solver's activity array for ordering.
/// Reference: MiniSat (Een & Sorensson 2003), CaDiCaL (Biere 2021).
struct VsidsHeap {
    /// Heap storage: indices are 1-based variable numbers.
    heap: Vec<u32>,
    /// Position of each variable in the heap. 0 means not in heap.
    /// Indexed by variable number (0 unused, 1..=num_vars).
    position: Vec<u32>,
}

impl VsidsHeap {
    /// Creates a new heap with all variables inserted.
    fn new(num_vars: u32) -> Self {
        let mut heap = Vec::with_capacity(num_vars as usize);
        let mut position = vec![0u32; num_vars as usize + 1];

        for var in 1..=num_vars {
            heap.push(var);
            position[var as usize] = var - 1;
        }

        Self { heap, position }
    }

    /// Creates a heap containing the given variables, ordered by the given
    /// activity scores.
    fn from_vars_heapified(num_vars: u32, vars: Vec<u32>, activity: &[f64]) -> Self {
        let mut position = vec![u32::MAX; num_vars as usize + 1];
        for (pos, &var) in vars.iter().enumerate() {
            position[var as usize] = pos as u32;
        }

        let mut heap = Self {
            heap: vars,
            position,
        };
        for pos in (0..(heap.heap.len() / 2)).rev() {
            heap.percolate_down(pos, activity);
        }
        heap
    }

    /// Creates a heap containing all variables, ordered by the given activity.
    fn new_heapified(num_vars: u32, activity: &[f64]) -> Self {
        Self::from_vars_heapified(num_vars, (1..=num_vars).collect(), activity)
    }

    /// Returns true if the variable is in the heap.
    fn contains(&self, var: u32) -> bool {
        (var as usize) < self.position.len() && {
            let pos = self.position[var as usize] as usize;
            pos < self.heap.len() && self.heap[pos] == var
        }
    }

    /// Returns true if the heap is empty.
    #[cfg(test)]
    fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    /// Inserts a variable into the heap if not already present.
    fn insert(&mut self, var: u32, activity: &[f64]) {
        if self.contains(var) {
            return;
        }
        let pos = self.heap.len() as u32;
        self.heap.push(var);
        self.position[var as usize] = pos;
        self.percolate_up(pos as usize, activity);
    }

    /// Removes and returns the variable with highest activity.
    fn pop_max(&mut self, activity: &[f64]) -> Option<u32> {
        if self.heap.is_empty() {
            return None;
        }

        let top = self.heap[0];
        let last_idx = self.heap.len() - 1;

        if last_idx > 0 {
            self.heap.swap(0, last_idx);
            self.position[self.heap[0] as usize] = 0;
        }

        self.heap.pop();
        // Mark removed variable as not in heap (set position beyond heap size).
        self.position[top as usize] = u32::MAX;

        if !self.heap.is_empty() {
            self.percolate_down(0, activity);
        }

        Some(top)
    }

    /// Notifies the heap that a variable's activity increased; percolates up.
    fn update(&mut self, var: u32, activity: &[f64]) {
        if !self.contains(var) {
            return;
        }
        let pos = self.position[var as usize] as usize;
        self.percolate_up(pos, activity);
    }

    /// Percolates element at `pos` upward to restore heap property.
    fn percolate_up(&mut self, mut pos: usize, activity: &[f64]) {
        let var = self.heap[pos];
        let var_act = activity[var as usize];

        while pos > 0 {
            let parent = (pos - 1) / 2;
            let parent_var = self.heap[parent];
            if activity[parent_var as usize] >= var_act {
                break;
            }
            // Move parent down.
            self.heap[pos] = parent_var;
            self.position[parent_var as usize] = pos as u32;
            pos = parent;
        }

        self.heap[pos] = var;
        self.position[var as usize] = pos as u32;
    }

    /// Percolates element at `pos` downward to restore heap property.
    fn percolate_down(&mut self, mut pos: usize, activity: &[f64]) {
        let var = self.heap[pos];
        let var_act = activity[var as usize];
        let len = self.heap.len();

        loop {
            let left = 2 * pos + 1;
            if left >= len {
                break;
            }
            let right = left + 1;

            // Pick the child with higher activity.
            let best_child = if right < len
                && activity[self.heap[right] as usize] > activity[self.heap[left] as usize]
            {
                right
            } else {
                left
            };

            let child_var = self.heap[best_child];
            if var_act >= activity[child_var as usize] {
                break;
            }

            // Move child up.
            self.heap[pos] = child_var;
            self.position[child_var as usize] = pos as u32;
            pos = best_child;
        }

        self.heap[pos] = var;
        self.position[var as usize] = pos as u32;
    }
}

/// Native PB CDCL solver.
pub struct PbCdclSolver {
    /// Number of original variables.
    num_vars: u32,
    /// The PB propagator engine.
    propagator: PbPropagator,
    /// Original internal `>=` constraints stored for conflict analysis.
    constraints: Vec<PbConstraint>,
    /// Learned constraints (appended after original).
    learned_constraints: Vec<PbConstraint>,
    /// LBD (Literal Block Distance) for each learned constraint.
    /// Lower values indicate higher quality ("glue" constraints).
    learned_lbd: Vec<u32>,
    /// Whether each learned constraint is still active (not deleted by reduce_db).
    learned_active: Vec<bool>,
    /// Whether each learned-region constraint is a permanent runtime constraint
    /// (an incremental constraint added via [`PbCdclSolver::add_constraint_runtime`]
    /// rather than a CDCL-derived lemma). Permanent constraints sit in the
    /// learned region of the propagator (so the original-constraint index range
    /// `0..self.constraints.len()` stays immutable) but are NEVER deleted by
    /// `reduce_db` and never participate in learned-constraint quality bookkeeping
    /// beyond keeping the parallel arrays in lockstep. This is the soundness
    /// anchor for incremental cardinality relaxations: their semantics must
    /// persist for the whole solve.
    learned_permanent: Vec<bool>,
    /// VSIDS-style activity score for each learned constraint. Bumped whenever
    /// the constraint participates in a conflict (used as a reason during
    /// conflict analysis, or is the conflict constraint). Higher = more recently
    /// useful; used as the secondary `reduce_db` ranking key (after LBD). Kept in
    /// lockstep with `learned_constraints` at every push-site so indices never
    /// desync; the bumping/decay/tiebreak that consult it are gated behind
    /// `config.learned_activity_reducedb_enabled` (default OFF).
    learned_activity: Vec<f64>,
    /// Global increment added to a learned constraint's activity on each bump.
    /// Grown geometrically each conflict (`/= LEARNED_ACTIVITY_DECAY`) so that
    /// recent bumps outweigh old ones; rescaled with all activities on overflow.
    /// Only mutated when the opt-in activity heuristic is enabled.
    learned_constraint_inc: f64,
    /// Conflict count at which the next `reduce_db` fires under the opt-in
    /// growing cadence (0 = not yet scheduled; derived from
    /// `config.reduce_interval`). Ignored when the opt-in flag is OFF (the fixed
    /// modular cadence is used instead).
    next_reduce_db_conflicts: u64,
    /// Decision trail.
    trail: Vec<TrailEntry>,
    /// Separator indices in trail for each decision level.
    trail_lim: Vec<usize>,
    /// Current decision level.
    decision_level: u32,
    /// Variable activity scores (VSIDS).
    activity: Vec<f64>,
    /// Activity increment (bumped on conflict).
    activity_inc: f64,
    /// VSIDS priority queue for O(log n) variable selection.
    vsids_heap: VsidsHeap,
    /// Phase saving: remembered polarity for each variable.
    /// Indexed by variable (0 unused). `true` = positive polarity preferred.
    saved_phase: Vec<bool>,
    /// Caller-provided warm-start phase seeds (`(var, polarity)` pairs) from
    /// [`Self::seed_phases`]. Re-applied ON TOP of the objective-direction
    /// seeding at every optimization entry point, so a caller's known-good
    /// assignment (e.g. an external incumbent) steers the FIRST descent even
    /// though `seed_saved_phase_from_objective` also writes `saved_phase`.
    /// Purely a branching-polarity bias: never consulted by propagation or
    /// conflict analysis, so it cannot change any verdict (SAT/UNSAT/cost
    /// correctness) — only which of the sound answers is found first.
    user_phase_seeds: Vec<(u32, bool)>,
    /// Solver statistics.
    stats: PbCdclStats,
    /// Configuration.
    config: CdclConfig,
    /// Number of conflicts since last restart.
    conflicts_since_restart: u64,
    /// Current restart threshold.
    restart_threshold: u64,
    /// Luby sequence index.
    luby_index: u32,
    lbd_ema_recent: f64,
    lbd_ema_global: f64,
    lbd_sum: f64,
    lbd_count: u64,
    /// External interrupt flag check.
    interrupted: bool,
    proof_writer: Option<VeriPbWriter<Box<dyn Write>>>,
    /// Asynchronous proof tap (proof-tap spec): when set, the DENSE conflict
    /// path captures micro-op frames through an SPSC ring and a serializer
    /// thread emits the proof text. Mutually exclusive with `proof_writer`
    /// (the tap owns the writer); `proof_writer` stays `None` so the dense
    /// fast path keeps running. Dropped (with the first error stored in
    /// `proof_error`) on any capture/transport failure — the solve then
    /// continues UNLOGGED and no certificate can commit.
    proof_tap: Option<ProofTap>,
    /// Running tap counters (checkpoints, serializer bytes/lines). Kept
    /// separately from `proof_tap` so the stats survive a tap void/drop.
    proof_tap_shared_stats: Option<std::sync::Arc<proof::tap::TapStats>>,
    proof_error: Option<ProofError>,
    optimization_proof_pending: bool,
    suppress_optimization_intermediate_proof_steps: bool,
    proof_input_constraint_count: usize,
    /// Whether every row of the ORIGINAL proof-mode instance was linear.
    ///
    /// `self.constraints` holds the propagator's normalized rows, and that
    /// normalization silently DROPS product terms — a dropped positive product
    /// term makes the stored row strictly stronger than the input row VeriPB
    /// imported. Anything that replays VeriPB's view of the formula out of
    /// `self.constraints` must therefore refuse to run unless this is set.
    proof_input_rows_are_linear: bool,
    last_objective_bound_proof_id: Option<ConstraintId>,
    /// VeriPB witness text (`x1 ~x2 ...`) of the incumbent behind
    /// `last_objective_bound_proof_id`, kept for the `conclusion BOUNDS`
    /// upper-bound hint (required in unchecked-deletion mode, where
    /// `soli`-logged solutions are discounted by the checker).
    last_objective_bound_witness: Option<String>,
    /// Internal propagator range for the strongest currently active native
    /// optimization bound. Older weaker bounds are deactivated once a better
    /// incumbent is found so they do not keep participating in propagation.
    active_optimization_bound_range: Option<(usize, usize)>,
    constraint_ids: Vec<ConstraintId>,
    /// Proof ID of the last constraint derived by `analyze_conflict`.
    /// Set before `add_learned_constraint` so the learned constraint
    /// can be traced back to its CP derivation chain.
    last_analysis_proof_id: Option<ConstraintId>,
    /// Chain id of an empty `>= degree` contradiction derived by dense
    /// analysis; consumed by `handle_unsat_proof` to conclude UNSAT directly on
    /// it instead of emitting a redundant fresh `rup >= 1 ;`.
    root_refutation_proof_id: Option<ConstraintId>,
    /// Proof id of the contradiction row `handle_unsat_proof` derived (or
    /// concluded on) for the last UNSAT verdict. Consumed by callers that own
    /// the proof conclusion themselves ([`Self::take_unsat_contradiction_proof_id`],
    /// used by the OPT-LIN-CERT PB-native lower-bound route to point its
    /// `conclusion BOUNDS` hint at the derived contradiction).
    last_unsat_contradiction_proof_id: Option<ConstraintId>,
    /// Variables fixed during preprocessing (var -> true/false).
    /// These must be incorporated into the model on SAT.
    fixed_literals: HashMap<u32, bool>,
    /// Optional caller-threaded wall-clock deadline for the WHOLE solve, used
    /// only to size internal sub-budgets proportionally (currently the root LP
    /// bound: `min(flat cap, remaining / ROOT_LP_BOUND_DEADLINE_FRACTION)`).
    /// Never used to terminate the search itself — the caller's `should_stop`
    /// closure remains the sole termination authority, so an inaccurate or
    /// absent deadline only affects how much time sub-computations may spend,
    /// never correctness.
    solve_deadline: Option<std::time::Instant>,
    /// Reusable dense accumulator holding the running learned constraint during
    /// the allocation-free conflict-analysis fast path (proof logging off).
    /// Cleared (not reallocated) at the start of every conflict.
    dense_learned: DenseCp,
    /// Reusable dense accumulator for the per-step reason constraint. Reloaded
    /// (cleared, not reallocated) for each resolution step.
    dense_reason: DenseCp,
    /// Reusable dense scratch holding the per-step resolvent before it is
    /// swapped into `dense_learned`. Avoids per-step allocation.
    dense_scratch: DenseCp,
    /// Reusable working space for the round-to-one'd reason inside a single
    /// proven resolution step. Held here, rather than allocated per step, for
    /// the same reason as the buffers above: the step used to `clone()` the
    /// reason, copying the entire `2 * num_vars` backing store instead of the
    /// few dozen literals actually in the support.
    dense_reduced: DenseCp,
    /// Reusable `(var, level)` trail-level buffer for the dense fast path's
    /// conservative weakening. Rebuilt (cleared, not reallocated) per conflict.
    dense_trail_levels: Vec<(u32, u32)>,
    /// Reusable var-indexed map (1-indexed; entry 0 unused) from variable to its
    /// position in `self.trail`, or `usize::MAX` when the variable is not on the
    /// trail (unassigned or preprocessing-fixed at level 0). Used by the
    /// trail-shrinking slack-based asserting test in conflict analysis. Rebuilt
    /// (in place, no reallocation) per conflict.
    dense_var_trail_pos: Vec<usize>,
}

/// Result of the trail-shrinking slack-based asserting test (RoundingSat
/// `isAssertingBefore`): the state of the running conflict if all assignments at
/// (and above) the current decision level were undone.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DenseAssertionStatus {
    /// Slack >= largest active coefficient: still loose; keep resolving.
    NonAsserting,
    /// 0 <= slack < largest active coefficient: would propagate after backjump.
    Asserting,
    /// slack < 0: still falsified below the last decision; backjump a level.
    Falsified,
}

/// Result of the slack-based assertion-level computation (RoundingSat
/// `getAssertionLevel`): the lowest decision level at which the learned lemma
/// propagates a literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DenseAssertionLevel {
    /// The lemma is falsified already at the root (level 0) — a contradiction.
    Root,
    /// The lemma propagates a literal at this decision level after backjumping.
    Level(u32),
    /// The lemma never propagates (RoundingSat INF) — not asserting.
    NonAsserting,
}

impl PbCdclSolver {
    /// Returns the constraint at a flat index (original constraints first, then
    /// learned), skipping learned constraints that have been deleted. Shared
    /// accessor used by both the proof-on and proof-off conflict-analysis paths.
    fn constraint_by_index(&self, constraint_id: usize) -> Option<&PbConstraint> {
        if constraint_id < self.constraints.len() {
            self.constraints.get(constraint_id)
        } else {
            let learned_idx = constraint_id - self.constraints.len();
            // Skip inactive (deleted) learned constraints.
            if learned_idx < self.learned_active.len() && !self.learned_active[learned_idx] {
                return None;
            }
            self.learned_constraints.get(learned_idx)
        }
    }

    /// [`Self::constraint_by_index`] as a dense [`CpConstraint`], if convertible.
    fn cp_constraint_by_index(&self, constraint_id: usize) -> Option<CpConstraint> {
        let constraint = self.constraint_by_index(constraint_id)?;
        CpConstraint::try_from(constraint).ok()
    }

    /// Flat propagator cid of the first ACTIVE permanent learned row that
    /// `model` violates, or `None` when every such row is satisfied.
    ///
    /// Runtime-added rows and the live objective-bound row live in the
    /// LEARNED region (they must not disturb the flat-cid convention
    /// `propagator cid == index into [constraints | learned_constraints]`;
    /// see the tighten loops and [`Self::add_constraint_runtime`]), so every
    /// SAT-side model-validity gate has to consult them alongside
    /// `self.constraints` — an all-assigned trail that violates the live
    /// bound row must never be accepted as a model.
    fn first_violated_active_permanent_learned(&self, model: &[bool]) -> Option<usize> {
        self.learned_constraints
            .iter()
            .enumerate()
            .find(|(idx, constraint)| {
                self.learned_active[*idx]
                    && self.learned_permanent[*idx]
                    && !crate::solver::eval_constraint(constraint, model)
            })
            .map(|(idx, _)| self.constraints.len() + idx)
    }

    /// Creates a new solver for the given PB instance.
    ///
    /// The instance is preprocessed before loading into the propagator.
    /// Preprocessing applies coefficient tightening, GCD strengthening,
    /// literal fixing, trivial constraint removal, and subsumption.
    /// If preprocessing detects UNSAT, the solver is created with an
    /// empty-but-conflicting state that will return UNSAT immediately.
    #[must_use]
    pub fn new(instance: &PbInstance) -> Self {
        Self::from_preprocess_result(instance, preprocess(instance))
    }

    /// Creates a new solver but allows interruption during preprocessing.
    #[must_use]
    pub fn new_interruptible<F>(instance: &PbInstance, mut should_stop: F) -> Self
    where
        F: FnMut() -> bool,
    {
        // Fail-closed on the process-memory guard during PREPROCESSING too. The
        // preprocess/propagation pipeline can allocate past MEMLIMIT on dense
        // instances (measured: Init-x2-i9 reached ~4 GiB at a 1.4 GiB limit)
        // while the caller's stop is only deadline/term, so the in-solver guard
        // never fired and only the harness's external kill contained it. The
        // preprocess polls are strided (per constraint index % 32/64), so the
        // footprint read here runs at most once per that batch — cheap.
        let mut mem_stop = || should_stop() || ay_sys::process_memory_exceeded();
        let preprocessed = preprocess_interruptible(instance, &mut mem_stop);
        Self::from_preprocess_result_interruptible(instance, preprocessed, &mut mem_stop)
    }

    /// Creates a new solver without running PB preprocessing.
    ///
    /// This is intended for huge anytime optimization instances where the
    /// preprocessing pass can consume the whole competition budget before the
    /// first feasible incumbent is searched. Loading the original constraints
    /// is sound because the propagator normalizes supported PB rows on import.
    #[must_use]
    pub fn new_unpreprocessed_interruptible<F>(instance: &PbInstance, mut should_stop: F) -> Self
    where
        F: FnMut() -> bool,
    {
        if should_stop() {
            let empty = PbInstance {
                num_vars: instance.num_vars,
                num_constraints: 0,
                constraints: Vec::new(),
                objective: None,
            };
            return Self::from_solving_instance(instance, &empty, HashMap::new(), true);
        }

        Self::from_solving_instance_interruptible(
            instance,
            instance,
            HashMap::new(),
            false,
            &mut should_stop,
        )
    }

    /// Runs only root-level native PB propagation and reports UNSAT conflicts.
    ///
    /// This fail-closed path avoids CDCL activity/heap setup and the mirrored
    /// constraint vector used for conflict analysis. It is sound for portfolio
    /// prechecks because it only accepts an actual root propagation conflict;
    /// satisfiable, incomplete, interrupted, and non-linear inputs all return
    /// `Unknown`.
    pub(crate) fn root_propagation_unsat_precheck_interruptible<F>(
        instance: &PbInstance,
        mut should_stop: F,
    ) -> PbCdclResult
    where
        F: FnMut() -> bool,
    {
        Self::root_propagation_unsat_precheck_interruptible_with_limits(
            instance,
            &mut should_stop,
            RootPropagationPrecheckLimits::default(),
        )
    }

    /// Runs native CDCL on a caller-built objective-bound decision instance and
    /// accepts only a proven UNSAT result.
    ///
    /// This is intended for checks such as `objective <= incumbent - 1` after
    /// the caller has already appended that bound as a normal PB constraint.
    /// SAT witnesses, interrupts, unsupported imports, and any other uncertain
    /// outcome fail closed as `Unknown`.
    #[allow(dead_code)]
    pub(crate) fn bounded_objective_decision_unsat_check_interruptible<F>(
        bounded_decision_instance: &PbInstance,
        mut should_stop: F,
    ) -> PbCdclResult
    where
        F: FnMut() -> bool,
    {
        if should_stop() {
            return PbCdclResult::Unknown;
        }

        let mut solver =
            Self::new_unpreprocessed_interruptible(bounded_decision_instance, &mut should_stop);
        if let Some(bound_constraint) = bounded_decision_instance.constraints.last() {
            solver.seed_search_from_objective_bound_constraint(bound_constraint);
            solver.seed_activity_from_objective_bound_neighborhood(bound_constraint);
        }
        match solver.solve_interruptible(&mut should_stop) {
            PbCdclResult::Unsatisfiable => PbCdclResult::Unsatisfiable,
            PbCdclResult::Satisfiable(_)
            | PbCdclResult::Unknown
            | PbCdclResult::Optimal(_, _)
            | PbCdclResult::Feasible(_, _) => PbCdclResult::Unknown,
        }
    }

    fn root_propagation_unsat_precheck_interruptible_with_limits<F>(
        instance: &PbInstance,
        should_stop: &mut F,
        limits: RootPropagationPrecheckLimits,
    ) -> PbCdclResult
    where
        F: FnMut() -> bool,
    {
        if should_stop() {
            return PbCdclResult::Unknown;
        }

        let mut propagator = PbPropagator::new();
        let mut state = RootOnlyPropagationState {
            pending_sources: Vec::new(),
            scan_cursor: 0,
            origin: PropagationOrigin::Scan,
        };
        let mut load_poll_budget = CONSTRUCTOR_LOAD_STOP_POLL_INTERVAL;
        let import_batch_interval = limits.import_batch_interval.max(1);
        let mut propagation_batch_budget = import_batch_interval;

        for constraint in &instance.constraints {
            if should_stop_constructor_load(should_stop, &mut load_poll_budget) {
                return PbCdclResult::Unknown;
            }

            let propagate_after_import =
                match check_root_precheck_constraint(constraint, limits, should_stop) {
                    RootConstraintPrecheck::Linear { term_visits } => {
                        if propagator
                            .add_from_pb_constraint_interruptible(constraint, should_stop)
                            .is_err()
                        {
                            return PbCdclResult::Unknown;
                        }
                        propagation_batch_budget -= 1;
                        term_visits >= ROOT_PROPAGATION_IMPORT_BATCH_TERM_INTERVAL
                    }
                    RootConstraintPrecheck::Unsupported | RootConstraintPrecheck::Interrupted => {
                        return PbCdclResult::Unknown;
                    }
                };

            if propagation_batch_budget == 0 || propagate_after_import {
                propagation_batch_budget = import_batch_interval;
                match propagate_root_only_interruptible(&mut propagator, &mut state, should_stop) {
                    PropagateOutcome::Conflict(_) => return PbCdclResult::Unsatisfiable,
                    PropagateOutcome::Ok => {}
                    PropagateOutcome::Interrupted => return PbCdclResult::Unknown,
                }
            }
        }

        match propagate_root_only_interruptible(&mut propagator, &mut state, should_stop) {
            PropagateOutcome::Conflict(_) => PbCdclResult::Unsatisfiable,
            PropagateOutcome::Ok | PropagateOutcome::Interrupted => PbCdclResult::Unknown,
        }
    }

    fn from_preprocess_result(instance: &PbInstance, preprocessed: PreprocessResult) -> Self {
        let mut never_stop = || false;
        Self::from_preprocess_result_interruptible(instance, preprocessed, &mut never_stop)
    }

    fn from_preprocess_result_interruptible<F>(
        instance: &PbInstance,
        preprocessed: PreprocessResult,
        should_stop: &mut F,
    ) -> Self
    where
        F: FnMut() -> bool,
    {
        match preprocessed {
            PreprocessResult::Simplified {
                instance: solving_instance,
                fixed_literals,
            } => {
                let solver = Self::from_solving_instance_interruptible(
                    instance,
                    &solving_instance,
                    fixed_literals,
                    false,
                    should_stop,
                );
                drop_huge_instance_in_background(solving_instance);
                solver
            }
            PreprocessResult::Unsatisfiable => {
                // Create a trivially UNSAT instance: 0 >= 1.
                let unsat = PbInstance {
                    num_vars: instance.num_vars,
                    num_constraints: 1,
                    constraints: vec![PbConstraint {
                        terms: vec![],
                        rel: PbRel::Ge,
                        rhs: 1,
                    }],
                    objective: None,
                };
                Self::from_solving_instance_interruptible(
                    instance,
                    &unsat,
                    HashMap::new(),
                    false,
                    should_stop,
                )
            }
            PreprocessResult::Interrupted => {
                let empty = PbInstance {
                    num_vars: instance.num_vars,
                    num_constraints: 0,
                    constraints: Vec::new(),
                    objective: None,
                };
                Self::from_solving_instance_interruptible(
                    instance,
                    &empty,
                    HashMap::new(),
                    true,
                    should_stop,
                )
            }
        }
    }

    fn from_solving_instance(
        instance: &PbInstance,
        solving_instance: &PbInstance,
        fixed_literals: HashMap<u32, bool>,
        interrupted: bool,
    ) -> Self {
        let mut never_stop = || false;
        Self::from_solving_instance_interruptible(
            instance,
            solving_instance,
            fixed_literals,
            interrupted,
            &mut never_stop,
        )
    }

    fn from_solving_instance_interruptible<F>(
        instance: &PbInstance,
        solving_instance: &PbInstance,
        fixed_literals: HashMap<u32, bool>,
        interrupted: bool,
        should_stop: &mut F,
    ) -> Self
    where
        F: FnMut() -> bool,
    {
        let num_vars = solving_instance.num_vars.max(instance.num_vars);
        let NativeConstraintImport {
            propagator,
            constraints,
            interrupted,
        } = import_native_constraints_interruptible(solving_instance, interrupted, should_stop);

        // Compute initial variable activities from coefficient sums.
        // For each variable, sum its absolute coefficients across all constraints,
        // then normalize to [0, 1] range. This gives the solver structural
        // knowledge about which variables participate most heavily in the instance.
        //
        // Reference: similar to Jeroslow-Wang scoring (Jeroslow & Wang, 1990).
        let mut activity = vec![0.0f64; num_vars as usize + 1];
        for constraint in &constraints {
            for term in &constraint.terms {
                for lit in &term.lits {
                    if (lit.var as usize) < activity.len() {
                        activity[lit.var as usize] += (term.coeff.unsigned_abs().max(1)) as f64;
                    }
                }
            }
        }

        // Normalize to [0, 1] range so initial activities don't interfere with
        // the VSIDS increment scale.
        let max_activity = activity.iter().copied().fold(0.0f64, f64::max);
        if max_activity > 0.0 {
            for a in &mut activity[1..] {
                *a /= max_activity;
            }
        }

        // Build the VSIDS heap with initial activities so that high-coefficient
        // variables are preferred for early decisions.
        let vsids_heap = VsidsHeap::new_heapified(num_vars, &activity);

        let mut solver = Self {
            num_vars,
            propagator,
            constraints,
            learned_constraints: Vec::new(),
            learned_lbd: Vec::new(),
            learned_active: Vec::new(),
            learned_permanent: Vec::new(),
            learned_activity: Vec::new(),
            learned_constraint_inc: 1.0,
            // 0 = not yet scheduled; the first opt-in threshold is derived from
            // `config.reduce_interval` so tests can lower the cadence after
            // construction (see `should_reduce_db`).
            next_reduce_db_conflicts: 0,
            trail: Vec::new(),
            trail_lim: Vec::new(),
            decision_level: 0,
            activity,
            activity_inc: 1.0,
            vsids_heap,
            saved_phase: vec![false; num_vars as usize + 1],
            user_phase_seeds: Vec::new(),
            stats: PbCdclStats::default(),
            config: CdclConfig::default(),
            conflicts_since_restart: 0,
            restart_threshold: 100,
            luby_index: 0,
            lbd_ema_recent: 0.0,
            lbd_ema_global: 0.0,
            lbd_sum: 0.0,
            lbd_count: 0,
            interrupted,
            proof_writer: None,
            proof_tap: None,
            proof_tap_shared_stats: None,
            proof_error: None,
            optimization_proof_pending: false,
            suppress_optimization_intermediate_proof_steps: false,
            proof_input_constraint_count: 0,
            proof_input_rows_are_linear: false,
            last_objective_bound_proof_id: None,
            last_objective_bound_witness: None,
            active_optimization_bound_range: None,
            constraint_ids: Vec::new(),
            last_analysis_proof_id: None,
            root_refutation_proof_id: None,
            last_unsat_contradiction_proof_id: None,
            fixed_literals,
            solve_deadline: None,
            dense_learned: DenseCp::with_num_vars(num_vars as usize),
            dense_reason: DenseCp::with_num_vars(num_vars as usize),
            dense_scratch: DenseCp::with_num_vars(num_vars as usize),
            dense_reduced: DenseCp::with_num_vars(num_vars as usize),
            dense_trail_levels: Vec::new(),
            dense_var_trail_pos: vec![usize::MAX; num_vars as usize + 1],
        };
        solver.install_root_assignments();
        solver
    }

    pub(crate) fn set_root_probing_enabled(&mut self, enabled: bool) {
        self.config.root_probe_enabled = enabled;
    }

    pub(crate) fn set_phase_completion_enabled(&mut self, enabled: bool) {
        self.config.phase_completion_enabled = enabled;
    }

    /// Threads the caller's overall wall-clock deadline into the solver so
    /// internal sub-budgets (currently the root LP lower bound) can be sized as
    /// a fraction of the REMAINING time instead of a flat cap. Advisory only:
    /// termination still rests solely with the caller's `should_stop` closure,
    /// and a missing/withdrawn deadline (`None`) restores the flat backstop
    /// budgets. Aborting the LP early only weakens its (anytime-sound) bound.
    pub fn set_solve_deadline(&mut self, deadline: Option<std::time::Instant>) {
        self.solve_deadline = deadline;
    }

    /// Effective root-LP budget measured from `now`: see [`root_lp_budget_for`].
    fn root_lp_budget(&self, now: std::time::Instant) -> std::time::Duration {
        root_lp_budget_for(
            self.solve_deadline
                .map(|deadline| deadline.saturating_duration_since(now)),
        )
    }

    /// Enables/disables the opt-in learned-constraint activity heuristic and the
    /// richer two-tier `reduce_db` (activity tiebreak, short-lemma protection,
    /// on-reuse LBD refresh, growing reduce cadence). Default OFF. Heuristic
    /// only — affects which low-quality lemmas survive a reduction, never lemma
    /// semantics, so toggling it cannot change SAT/UNSAT verdicts.
    ///
    /// Currently exercised only by tests; kept as a deliberate, default-OFF
    /// entry point for future portfolio wiring (hence `allow(dead_code)` in
    /// non-test builds, matching the crate's other opt-in setters).
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn set_learned_activity_reducedb_enabled(&mut self, enabled: bool) {
        self.config.learned_activity_reducedb_enabled = enabled;
    }

    /// Enables/disables the single-equality knapsack subset-sum DP special
    /// case (default ON; see [`crate::eq_knapsack`]). Used for A/B
    /// measurement; disabling only removes the special case — verdicts stay
    /// sound either way.
    #[doc(hidden)]
    pub fn set_eq_knapsack_dp_enabled(&mut self, enabled: bool) {
        self.config.eq_knapsack_dp_enabled = enabled;
    }

    #[doc(hidden)]
    pub fn set_native_code_helper_validation_enabled(&mut self, enabled: bool) {
        self.propagator
            .set_native_code_helper_validation_enabled(enabled);
    }

    #[must_use]
    pub fn native_code_helper_applications(&self) -> u64 {
        self.propagator.native_code_helper_applications()
    }

    #[must_use]
    pub fn native_helper_stats(&self) -> PbNativeHelperStats {
        self.propagator.native_helper_stats()
    }

    /// Creates a solver with VeriPB proof logging.
    pub fn with_proof_writer<W>(instance: &PbInstance, writer: W) -> proof::Result<Self>
    where
        W: Write + 'static,
    {
        // VeriPB input IDs refer to the original formula after VeriPB's own
        // equality expansion. PB preprocessing can delete or reorder rows, so
        // proof mode loads the original instance directly to keep internal
        // propagator constraint IDs aligned with the proof header.
        let mut solver = Self::new_unpreprocessed_interruptible(instance, || false);
        let num_input_constraints = veripb_input_constraint_count(instance)?;
        solver.proof_writer = Some(VeriPbWriter::new(
            Box::new(writer) as Box<dyn Write>,
            num_input_constraints,
        )?);
        solver.constraint_ids = if solver.interrupted {
            Vec::new()
        } else {
            build_imported_input_constraint_ids(instance)?
        };
        solver.proof_input_constraint_count = solver.constraint_ids.len();
        solver.proof_input_rows_are_linear = instance_rows_are_linear(instance);
        Ok(solver)
    }

    /// Creates a solver with VeriPB proof logging and interruptible preprocessing.
    pub fn with_proof_writer_interruptible<W, F>(
        instance: &PbInstance,
        writer: W,
        should_stop: F,
    ) -> proof::Result<Self>
    where
        W: Write + 'static,
        F: FnMut() -> bool,
    {
        let mut solver = Self::new_unpreprocessed_interruptible(instance, should_stop);
        let num_input_constraints = veripb_input_constraint_count(instance)?;
        solver.proof_writer = Some(VeriPbWriter::new(
            Box::new(writer) as Box<dyn Write>,
            num_input_constraints,
        )?);
        solver.constraint_ids = if solver.interrupted {
            Vec::new()
        } else {
            build_imported_input_constraint_ids(instance)?
        };
        solver.proof_input_constraint_count = solver.constraint_ids.len();
        solver.proof_input_rows_are_linear = instance_rows_are_linear(instance);
        Ok(solver)
    }

    /// Creates a PROOF-TAP solver that CONTINUES an existing VeriPB proof
    /// stream instead of opening a fresh one: `writer` must already carry the
    /// header and any prior steps, and its id counter must equal
    /// `veripb_input_constraint_count(instance)` — i.e. from the checker's
    /// point of view, ids `1..=count` are exactly this instance's rows (some of
    /// them possibly contributed by proof rules rather than `f`; the
    /// OPT-LIN-CERT PB-native route's `soli`-installed objective-improving row
    /// is the motivating case). No header is written; the tap's derived steps
    /// continue the stream's id sequence in lockstep with the checker's.
    ///
    /// The TAP (not the legacy synchronous writer) is essential here, not an
    /// optimization: it drives the DENSE proven round-to-one conflict analysis,
    /// which derives division-strengthened lemmas the legacy heuristic
    /// `CpConstraint` path cannot — on huge-coefficient rows the legacy path
    /// fails to refute even trivially small instances in any practical budget.
    ///
    /// Fails closed with [`ProofError::AppendedProofIdMismatch`] when the id
    /// counter does not line up, before any step is emitted.
    pub(crate) fn with_appended_proof_tap_interruptible<W, F>(
        instance: &PbInstance,
        writer: VeriPbWriter<W>,
        should_stop: F,
    ) -> proof::Result<Self>
    where
        W: Write + Send + 'static,
        F: FnMut() -> bool,
    {
        let num_input_constraints = veripb_input_constraint_count(instance)?;
        match writer.allocated_constraint_count() {
            Some(actual) if actual == num_input_constraints => {}
            actual => {
                return Err(ProofError::AppendedProofIdMismatch {
                    expected: num_input_constraints,
                    actual: actual.unwrap_or(u64::MAX),
                })
            }
        }
        // Same loading rule as `with_proof_tap_interruptible`: proof mode loads
        // the original instance unpreprocessed so internal constraint ids stay
        // aligned with the checker's row ids.
        let mut solver = Self::new_unpreprocessed_interruptible(instance, should_stop);
        solver.constraint_ids = if solver.interrupted {
            Vec::new()
        } else {
            build_imported_input_constraint_ids(instance)?
        };
        solver.proof_input_constraint_count = solver.constraint_ids.len();
        let first_free_id = num_input_constraints
            .checked_add(1)
            .ok_or(ProofError::ConstraintIdOverflow)?;
        let tap = ProofTap::spawn(writer, first_free_id, ProofTap::default_ring_capacity());
        solver.proof_tap_shared_stats = Some(tap.stats_arc());
        solver.proof_tap = Some(tap);
        Ok(solver)
    }

    /// Decision-refutation solve whose proof CONCLUSION is owned by the caller:
    /// runs the normal proof-logging CDCL search, but on UNSAT only DERIVES the
    /// contradiction row into the proof stream — no `output`/`conclusion` block
    /// is written — and records its id for
    /// [`Self::take_unsat_contradiction_proof_id`]. On SAT nothing is concluded
    /// either. Used by the OPT-LIN-CERT PB-native lower-bound route, which
    /// continues the same stream with its own `conclusion BOUNDS` block.
    pub(crate) fn solve_refutation_only_interruptible<F>(&mut self, should_stop: F) -> PbCdclResult
    where
        F: FnMut() -> bool,
    {
        let mut should_stop = should_stop;
        self.solve_interruptible_with_proof_controls(
            &mut should_stop,
            SatProofMode::Suppress,
            UnsatProofMode::DeriveOnly,
        )
    }

    /// Takes the proof id of the contradiction row behind the last UNSAT
    /// verdict (see `handle_unsat_proof`). `None` when no UNSAT was derived or
    /// the proof was voided by an error — callers must decline their
    /// certificate in that case (fail closed).
    pub(crate) fn take_unsat_contradiction_proof_id(&mut self) -> Option<ConstraintId> {
        self.last_unsat_contradiction_proof_id.take()
    }

    /// Creates a solver with the ASYNCHRONOUS proof tap (proof-tap spec):
    /// conflict analysis runs the DENSE fast path and captures micro-op
    /// frames through an SPSC ring; a serializer thread replays each frame as
    /// one VeriPB pol line into `writer`. Ids are allocated solver-side and
    /// reconciled on the serializer; any failure voids the proof (fail
    /// closed) and the solve continues unlogged.
    ///
    /// DECISION solves only in this phase: optimization entry points void the
    /// proof rather than emit an unsupported opt interleave.
    pub fn with_proof_tap_interruptible<W, F>(
        instance: &PbInstance,
        writer: W,
        should_stop: F,
    ) -> proof::Result<Self>
    where
        W: Write + Send + 'static,
        F: FnMut() -> bool,
    {
        // Proof mode loads the original instance unpreprocessed for the same
        // reason as `with_proof_writer`: VeriPB input ids refer to the
        // original formula after VeriPB's own equality expansion.
        let mut solver = Self::new_unpreprocessed_interruptible(instance, should_stop);
        let num_input_constraints = veripb_input_constraint_count(instance)?;
        solver.constraint_ids = if solver.interrupted {
            Vec::new()
        } else {
            build_imported_input_constraint_ids(instance)?
        };
        solver.proof_input_constraint_count = solver.constraint_ids.len();
        let tap = ProofTap::spawn_counting(
            writer,
            num_input_constraints,
            ProofTap::default_ring_capacity(),
        )?;
        solver.proof_tap_shared_stats = Some(tap.stats_arc());
        solver.proof_tap = Some(tap);
        Ok(solver)
    }

    /// Point-in-time proof-tap counters (checkpoints, serializer bytes/lines
    /// written). `None` when the solver was not constructed with the tap. The
    /// counters survive a tap void/drop, so post-run inspection still works.
    #[must_use]
    pub fn proof_tap_stats(&self) -> Option<proof::ProofTapStats> {
        self.proof_tap_shared_stats
            .as_ref()
            .map(|stats| stats.snapshot())
    }

    /// Test/diagnostic hook: overrides the proof-tap CHECKPOINT thresholds so
    /// small instances force multi-segment pol derivations. No-op without the
    /// tap.
    #[doc(hidden)]
    pub fn set_proof_tap_checkpoint_limits(&mut self, ops: u32, bytes: usize) {
        if let Some(tap) = self.proof_tap.as_mut() {
            tap.set_checkpoint_limits(ops, bytes);
        }
    }

    /// True when the last optimization conclusion could not close its lower
    /// bound with a native cutting-planes cut and deferred certification to the
    /// caller's OPT-LIN fallback (see [`ProofError::UnprovableOptimizationLowerBound`]).
    ///
    /// This is a RECOVERABLE condition, not proof corruption: the solve's
    /// `OptimumFound` verdict stands (the optimum and its model are correct);
    /// only the *native* proof shortcut did not apply. A caller that sees this
    /// should discard the native proof file and re-certify the known optimum
    /// out-of-band (a real augmented-instance refutation), rather than treating
    /// `conclude_proof`'s `Err` as a hard failure.
    pub fn opt_lower_bound_deferred(&self) -> bool {
        matches!(
            self.proof_error,
            Some(ProofError::UnprovableOptimizationLowerBound)
        )
    }

    /// Concludes the proof. Call after solve() completes.
    pub fn conclude_proof(&mut self) -> proof::Result<()> {
        if let Some(error) = self.proof_error.take() {
            return Err(error);
        }

        if self.optimization_proof_pending {
            return Err(ProofError::MissingOptimizationBounds);
        }

        if let Some(proof_writer) = &mut self.proof_writer {
            proof_writer.flush()?;
        }

        // Proof tap: shut the serializer down and surface any late error. A
        // committed conclusion has already completed its handshake (drain +
        // conclusion block + flush), so this is a final safety check.
        if let Some(mut tap) = self.proof_tap.take() {
            tap.finish()?;
        }

        Ok(())
    }

    /// Solves the PB instance. Returns SAT/UNSAT/Unknown.
    pub fn solve(&mut self) -> PbCdclResult {
        self.solve_with_stop(|solver| solver.interrupted)
    }

    /// Solves with an interruptibility check function.
    pub fn solve_interruptible<F>(&mut self, should_stop: F) -> PbCdclResult
    where
        F: FnMut() -> bool,
    {
        let mut should_stop = should_stop;
        self.solve_interruptible_with_proof_controls(
            &mut should_stop,
            SatProofMode::Conclude,
            UnsatProofMode::Conclude,
        )
    }

    /// Solves the PB instance under temporary assumption literals.
    ///
    /// Assumptions are applied as a decision-level prefix and are removed before
    /// returning. If the query is UNSAT, the returned core is a sound subset of
    /// the assumptions, but it is not currently minimized except for direct
    /// contradictory assumption pairs.
    pub fn solve_with_assumptions(&mut self, assumptions: &[PbLit]) -> PbCdclAssumptionResult {
        self.solve_with_assumptions_with_stop(assumptions, |solver| solver.interrupted)
    }

    /// Solves under assumptions with an interruptibility check.
    pub fn solve_with_assumptions_interruptible<F>(
        &mut self,
        assumptions: &[PbLit],
        should_stop: F,
    ) -> PbCdclAssumptionResult
    where
        F: FnMut() -> bool,
    {
        let mut should_stop = should_stop;
        self.solve_with_assumptions_with_stop(assumptions, |solver| {
            solver.interrupted || should_stop()
        })
    }

    /// Solves under assumptions with an interruptibility check AND a hard cap on
    /// the conflicts this single query may spend.
    ///
    /// Bounded-effort queries let a caller ask many cheap questions instead of
    /// one unbounded expensive one — a wall-clock budget is far too coarse to
    /// bound a probe that must run thousands of times.
    ///
    /// THE SHAPE IS THE SOUNDNESS ARGUMENT. The cap is expressed purely as a
    /// stop closure over [`Self::solve_with_assumptions_with_stop`], so it adds
    /// NO new `Unsatisfiable` return site: every abort path is the pre-existing
    /// one, and every pre-existing abort path returns `Unknown`. That is the
    /// contract pinned by
    /// `interrupted_assumption_solve_never_reports_a_bogus_core`, and expressing
    /// the cap this way makes it bind here by construction rather than by
    /// review. A cap can therefore cost us a core; it can never fabricate one.
    /// Do NOT reimplement this by threading a counter into the search loop with
    /// its own return arm — that reopens exactly the hazard this shape closes.
    ///
    /// The cap also cannot suppress a core the solver actually proved: the
    /// `decision_level <= assumption_boundary` check runs BEFORE the stop poll,
    /// so a conflict that refutes the assumption prefix is reported even when it
    /// is the same conflict that trips the cap.
    #[cfg(test)]
    pub(crate) fn solve_with_assumptions_conflict_capped<F>(
        &mut self,
        assumptions: &[PbLit],
        max_conflicts: u64,
        should_stop: F,
    ) -> PbCdclAssumptionResult
    where
        F: FnMut() -> bool,
    {
        let mut should_stop = should_stop;
        // `stats.conflicts` is monotone across the solver's whole lifetime — it
        // is incremented on conflict and reset nowhere — so an absolute limit
        // computed once here is a budget for THIS call alone.
        let limit = self.stats.conflicts.saturating_add(max_conflicts);
        self.solve_with_assumptions_with_stop(assumptions, |solver| {
            solver.interrupted || solver.stats.conflicts >= limit || should_stop()
        })
    }

    #[allow(dead_code)]
    pub(crate) fn probe_single_lit_objective_core(
        &mut self,
        objective: &PbObjective,
    ) -> PbCdclOptimizationCoreProbeResult {
        self.probe_single_lit_objective_core_with_stop(objective, |solver| solver.interrupted)
    }

    fn solve_with_stop<F>(&mut self, mut should_stop: F) -> PbCdclResult
    where
        F: FnMut(&Self) -> bool,
    {
        self.solve_with_proof_controls(
            &mut should_stop,
            SatProofMode::Conclude,
            UnsatProofMode::Conclude,
        )
    }

    #[allow(dead_code)]
    fn probe_single_lit_objective_core_with_stop<F>(
        &mut self,
        objective: &PbObjective,
        mut should_stop: F,
    ) -> PbCdclOptimizationCoreProbeResult
    where
        F: FnMut(&Self) -> bool,
    {
        if self.proof_writer.is_some() || self.proof_tap.is_some() {
            return PbCdclOptimizationCoreProbeResult::Unsupported(
                PbCdclOptimizationCoreUnsupportedReason::ProofWriterEnabled,
            );
        }

        let probe = match build_single_lit_objective_probe(objective) {
            Ok(probe) => probe,
            Err(reason) => return PbCdclOptimizationCoreProbeResult::Unsupported(reason),
        };

        match self
            .solve_with_assumptions_with_stop(&probe.assumptions, |solver| should_stop(solver))
        {
            PbCdclAssumptionResult::Satisfiable(model) => {
                PbCdclOptimizationCoreProbeResult::Evidence(
                    PbCdclOptimizationCoreEvidence::satisfiable_model(model),
                )
            }
            PbCdclAssumptionResult::Unsatisfiable { core } => {
                let Some(original_bound) = probe.bound_for_core(&core) else {
                    return PbCdclOptimizationCoreProbeResult::Unknown;
                };

                let refined_core = self
                    .trim_unsat_assumption_core_prefix_with_stop(core.clone(), &mut should_stop)
                    .and_then(|trimmed_core| {
                        probe.bound_for_core(&trimmed_core).map(|_| trimmed_core)
                    })
                    .unwrap_or(core);
                let bound = probe
                    .bound_for_core(&refined_core)
                    .unwrap_or(original_bound);

                PbCdclOptimizationCoreProbeResult::Evidence(
                    PbCdclOptimizationCoreEvidence::unsat_core(refined_core, bound),
                )
            }
            PbCdclAssumptionResult::Unknown => PbCdclOptimizationCoreProbeResult::Unknown,
            PbCdclAssumptionResult::Unsupported => PbCdclOptimizationCoreProbeResult::Unsupported(
                PbCdclOptimizationCoreUnsupportedReason::AssumptionSolvingUnsupported,
            ),
        }
    }

    fn trim_unsat_assumption_core_prefix_with_stop<F>(
        &mut self,
        core: Vec<PbLit>,
        should_stop: &mut F,
    ) -> Option<Vec<PbLit>>
    where
        F: FnMut(&Self) -> bool,
    {
        let mut best = core;

        while best.len() > 1 {
            let candidate = best[..best.len() - 1].to_vec();
            match self.solve_with_assumptions_with_stop(&candidate, |solver| should_stop(solver)) {
                PbCdclAssumptionResult::Unsatisfiable { core } if !core.is_empty() => {
                    best = core;
                }
                PbCdclAssumptionResult::Unsatisfiable { .. }
                | PbCdclAssumptionResult::Satisfiable(_) => break,
                PbCdclAssumptionResult::Unknown | PbCdclAssumptionResult::Unsupported => {
                    return None;
                }
            }
        }

        Some(best)
    }

    fn solve_with_assumptions_with_stop<F>(
        &mut self,
        assumptions: &[PbLit],
        mut should_stop: F,
    ) -> PbCdclAssumptionResult
    where
        F: FnMut(&Self) -> bool,
    {
        if self.proof_writer.is_some() || self.proof_tap.is_some() {
            return PbCdclAssumptionResult::Unsupported;
        }

        let active_assumptions = match self.prepare_assumptions(assumptions) {
            AssumptionPreparation::Ready(active) => active,
            AssumptionPreparation::Contradiction(core) => {
                return PbCdclAssumptionResult::Unsatisfiable { core };
            }
            AssumptionPreparation::Unsupported => return PbCdclAssumptionResult::Unknown,
        };

        self.backtrack_to(0);

        match self.propagate_all(&mut should_stop) {
            PropagateOutcome::Ok => {}
            PropagateOutcome::Conflict(_) => {
                return self.finish_assumption_solve(PbCdclAssumptionResult::Unsatisfiable {
                    core: Vec::new(),
                });
            }
            PropagateOutcome::Interrupted => {
                return self.finish_assumption_solve(PbCdclAssumptionResult::Unknown);
            }
        }

        match self.run_root_probing_with_stop(&mut should_stop) {
            RootProbeOutcome::Ok => {}
            RootProbeOutcome::Unsat => {
                return self.finish_assumption_solve(PbCdclAssumptionResult::Unsatisfiable {
                    core: Vec::new(),
                });
            }
            RootProbeOutcome::Interrupted => {
                return self.finish_assumption_solve(PbCdclAssumptionResult::Unknown);
            }
        }

        let mut assumption_boundary =
            match self.apply_assumptions(&active_assumptions, &mut should_stop) {
                ApplyAssumptionsOutcome::Ok(boundary) => boundary,
                ApplyAssumptionsOutcome::Unsat(core) => {
                    return self
                        .finish_assumption_solve(PbCdclAssumptionResult::Unsatisfiable { core });
                }
                ApplyAssumptionsOutcome::Interrupted => {
                    return self.finish_assumption_solve(PbCdclAssumptionResult::Unknown);
                }
            };

        // Bounded retries for the rare PB conflict-analysis "non-asserting lemma"
        // give-up case: instead of abandoning the whole assumption query as
        // `Unknown` (which would needlessly abort a core-guided optimization
        // round), restart and continue. Each restart re-establishes the
        // assumption prefix, so this never changes the verdict — it only gives the
        // search another chance to find an asserting lemma. The cap keeps the loop
        // finite if every restart hits the same edge case.
        let mut non_asserting_restarts_remaining: u32 = 32;

        loop {
            if should_stop(self) {
                return self.finish_assumption_solve(PbCdclAssumptionResult::Unknown);
            }

            if self.all_assigned() {
                let model = self.extract_model();
                // Assumption probes may feed optimizer evidence; invalid SAT
                // witnesses must fail closed in release builds too.
                let constraints_valid = self
                    .constraints
                    .iter()
                    .all(|c| crate::solver::eval_constraint(c, &model))
                    && self
                        .first_violated_active_permanent_learned(&model)
                        .is_none();
                let assumptions_valid = active_assumptions
                    .iter()
                    .all(|&assumption| eval_pb_lit_on_model(assumption, &model));
                if !constraints_valid || !assumptions_valid {
                    return self.finish_assumption_solve(PbCdclAssumptionResult::Unknown);
                }
                debug_assert!(
                    constraints_valid,
                    "BUG: PB CDCL returned SAT under assumptions but model violates a constraint"
                );
                debug_assert!(
                    assumptions_valid,
                    "BUG: PB CDCL returned SAT under assumptions but model violates an assumption"
                );
                return self.finish_assumption_solve(PbCdclAssumptionResult::Satisfiable(model));
            }

            let decision_lit = self.pick_decision_literal();
            self.decide(decision_lit);

            loop {
                match self.propagate_all(&mut should_stop) {
                    PropagateOutcome::Ok => break,
                    PropagateOutcome::Conflict(conflict_cid) => {
                        self.stats.conflicts += 1;
                        self.conflicts_since_restart += 1;

                        if self.decision_level <= assumption_boundary {
                            let core = self.extract_assumption_conflict_core(
                                conflict_cid,
                                &active_assumptions,
                            );
                            return self.finish_assumption_solve(
                                PbCdclAssumptionResult::Unsatisfiable { core },
                            );
                        }

                        if should_stop(self) {
                            return self.finish_assumption_solve(PbCdclAssumptionResult::Unknown);
                        }

                        let (backtrack_level, learned) =
                            match self.analyze_conflict_with_stop(conflict_cid, &mut should_stop) {
                                ConflictAnalysisOutcome::Learned(result) => result,
                                ConflictAnalysisOutcome::Interrupted => {
                                    return self
                                        .finish_assumption_solve(PbCdclAssumptionResult::Unknown);
                                }
                            };

                        if learned.is_none() {
                            // Conflict analysis gave up (a non-asserting lemma on a
                            // PB overflow edge case). Rather than abandon the query,
                            // restart from the assumption prefix and try again, up
                            // to a bounded number of times. Soundness is unchanged:
                            // restarting only resets the decision stack above the
                            // assumptions; the assumptions and all learned/permanent
                            // constraints remain in force.
                            if non_asserting_restarts_remaining == 0 {
                                return self
                                    .finish_assumption_solve(PbCdclAssumptionResult::Unknown);
                            }
                            non_asserting_restarts_remaining -= 1;
                            self.backtrack_to(0);
                            assumption_boundary = match self
                                .apply_assumptions(&active_assumptions, &mut should_stop)
                            {
                                ApplyAssumptionsOutcome::Ok(boundary) => boundary,
                                ApplyAssumptionsOutcome::Unsat(core) => {
                                    return self.finish_assumption_solve(
                                        PbCdclAssumptionResult::Unsatisfiable { core },
                                    );
                                }
                                ApplyAssumptionsOutcome::Interrupted => {
                                    return self
                                        .finish_assumption_solve(PbCdclAssumptionResult::Unknown);
                                }
                            };
                            break;
                        }

                        self.backtrack_to(backtrack_level);

                        if let Some(constraint) = learned {
                            self.add_learned_constraint(constraint);
                        }

                        let mut restore_assumptions = backtrack_level < assumption_boundary;
                        if self.should_restart() {
                            self.restart();
                            restore_assumptions = true;
                        }

                        if restore_assumptions {
                            assumption_boundary = match self
                                .apply_assumptions(&active_assumptions, &mut should_stop)
                            {
                                ApplyAssumptionsOutcome::Ok(boundary) => boundary,
                                ApplyAssumptionsOutcome::Unsat(core) => {
                                    return self.finish_assumption_solve(
                                        PbCdclAssumptionResult::Unsatisfiable { core },
                                    );
                                }
                                ApplyAssumptionsOutcome::Interrupted => {
                                    return self
                                        .finish_assumption_solve(PbCdclAssumptionResult::Unknown);
                                }
                            };
                        }

                        if self.should_reduce_db() {
                            if self.reduce_db_with_stop(&mut should_stop) {
                                return self
                                    .finish_assumption_solve(PbCdclAssumptionResult::Unknown);
                            }
                        }

                        if should_stop(self) {
                            return self.finish_assumption_solve(PbCdclAssumptionResult::Unknown);
                        }
                    }
                    PropagateOutcome::Interrupted => {
                        return self.finish_assumption_solve(PbCdclAssumptionResult::Unknown);
                    }
                }
            }
        }
    }

    /// Single-equality knapsack special case (the Aardal_1 / cuww / prob
    /// DEC-LIN family): when the ENTIRE solving instance is one linear
    /// equality (`Eq` row, or two complementary `Ge` rows), decide it exactly
    /// by subset-sum bitset DP instead of CDCL search. Measured on the PB24
    /// family: every instance UNKNOWN at 30s under search resolves in well
    /// under a second here.
    ///
    /// FAIL-CLOSED SOUNDNESS CONTRACT (`None` = decline, normal search runs):
    /// * gated OFF under proof logging/tap (the DP derivation is not
    ///   proof-logged);
    /// * SAT: the DP witness is patched into the standard `extract_model`
    ///   base (preprocessing-fixed literals keep their fixed values) and the
    ///   full model is re-verified against EVERY stored row — the originals
    ///   AND the whole learned region (derived lemmas are implied by the
    ///   originals so a genuine model always passes; runtime-permanent rows
    ///   carry extra semantics and genuinely arbitrate). A DP bug can
    ///   decline but never mis-report;
    /// * UNSAT: the two original rows alone are contradictory, which stays
    ///   sound under any extra learned/runtime rows; only accepted when two
    ///   independent DP passes agree (see [`crate::eq_knapsack`]), and the
    ///   DP core is differential-tested against brute-force enumeration;
    /// * interrupts, out-of-budget targets, and any internal anomaly decline.
    fn try_eq_knapsack_special_case(
        &self,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Option<PbCdclResult> {
        if !self.config.eq_knapsack_dp_enabled
            || self.proof_writer.is_some()
            || self.proof_tap.is_some()
            || self.decision_level != 0
            || self.constraints.is_empty()
            || self.constraints.len() > 2
        {
            return None;
        }

        let knapsack = crate::eq_knapsack::EqKnapsack::detect(&self.constraints)?;
        if !knapsack.within_budget() {
            return None;
        }

        match knapsack.solve(should_stop) {
            crate::eq_knapsack::EqKnapsackOutcome::Sat(assignment) => {
                let mut model = self.extract_model();
                for (var, value) in assignment {
                    let idx = var.checked_sub(1)? as usize;
                    if idx >= model.len() {
                        return None; // Row var outside the model: decline.
                    }
                    if self.fixed_literals.contains_key(&var) {
                        // Preprocessing-fixed values win; the row verification
                        // below arbitrates any conflict by declining.
                        continue;
                    }
                    model[idx] = value;
                }
                let all_rows_satisfied = self
                    .constraints
                    .iter()
                    .chain(self.learned_constraints.iter())
                    .all(|c| crate::solver::eval_constraint(c, &model));
                if !all_rows_satisfied {
                    return None; // Fail closed: fall back to normal search.
                }
                Some(PbCdclResult::Satisfiable(model))
            }
            crate::eq_knapsack::EqKnapsackOutcome::Unsat => Some(PbCdclResult::Unsatisfiable),
            crate::eq_knapsack::EqKnapsackOutcome::Inconclusive => None,
        }
    }

    fn solve_with_proof_controls<F>(
        &mut self,
        mut should_stop: F,
        sat_proof_mode: SatProofMode,
        unsat_proof_mode: UnsatProofMode,
    ) -> PbCdclResult
    where
        F: FnMut(&Self) -> bool,
    {
        match self.propagate_all(&mut should_stop) {
            PropagateOutcome::Ok => {}
            PropagateOutcome::Conflict(_) => {
                self.handle_unsat_proof(unsat_proof_mode);
                return PbCdclResult::Unsatisfiable;
            }
            PropagateOutcome::Interrupted => return PbCdclResult::Unknown,
        }

        match self.run_root_probing_with_stop(&mut should_stop) {
            RootProbeOutcome::Ok => {}
            RootProbeOutcome::Unsat => {
                self.handle_unsat_proof(unsat_proof_mode);
                return PbCdclResult::Unsatisfiable;
            }
            RootProbeOutcome::Interrupted => return PbCdclResult::Unknown,
        }

        let dp_result = {
            let self_ref = &*self;
            self_ref
                .try_eq_knapsack_special_case(&mut || self_ref.interrupted || should_stop(self_ref))
        };
        if let Some(result) = dp_result {
            self.stats.eq_knapsack_dp += 1;
            return result;
        }

        loop {
            if should_stop(self) {
                return PbCdclResult::Unknown;
            }

            if self.all_assigned() {
                let model = self.extract_model();
                let constraints_valid = self
                    .constraints
                    .iter()
                    .all(|c| crate::solver::eval_constraint(c, &model))
                    && self
                        .first_violated_active_permanent_learned(&model)
                        .is_none();
                if !constraints_valid {
                    return PbCdclResult::Unknown;
                }
                if sat_proof_mode == SatProofMode::Conclude {
                    self.conclude_sat_proof(&model);
                }
                return PbCdclResult::Satisfiable(model);
            }

            let decision_lit = self.pick_decision_literal();
            self.decide(decision_lit);

            loop {
                match self.propagate_all(&mut should_stop) {
                    PropagateOutcome::Ok => break,
                    PropagateOutcome::Conflict(conflict_cid) => {
                        self.stats.conflicts += 1;
                        self.conflicts_since_restart += 1;

                        if self.decision_level == 0 {
                            self.handle_unsat_proof(unsat_proof_mode);
                            return PbCdclResult::Unsatisfiable;
                        }

                        if should_stop(self) {
                            return PbCdclResult::Unknown;
                        }

                        let (backtrack_level, learned) =
                            match self.analyze_conflict_with_stop(conflict_cid, &mut should_stop) {
                                ConflictAnalysisOutcome::Learned(result) => result,
                                ConflictAnalysisOutcome::Interrupted => {
                                    return PbCdclResult::Unknown;
                                }
                            };

                        self.backtrack_to(backtrack_level);

                        if let Some(constraint) = learned {
                            self.add_learned_constraint(constraint);
                        }

                        if self.should_restart() {
                            self.restart();
                        }

                        if self.should_reduce_db() {
                            if self.reduce_db_with_stop(&mut should_stop) {
                                return PbCdclResult::Unknown;
                            }
                        }

                        if should_stop(self) {
                            return PbCdclResult::Unknown;
                        }
                    }
                    PropagateOutcome::Interrupted => return PbCdclResult::Unknown,
                }
            }
        }
    }

    fn solve_interruptible_with_proof_controls<F>(
        &mut self,
        should_stop: &mut F,
        sat_proof_mode: SatProofMode,
        unsat_proof_mode: UnsatProofMode,
    ) -> PbCdclResult
    where
        F: FnMut() -> bool,
    {
        match self.propagate_all_interruptible(should_stop) {
            PropagateOutcome::Ok => {}
            PropagateOutcome::Conflict(_) => {
                self.handle_unsat_proof(unsat_proof_mode);
                return PbCdclResult::Unsatisfiable;
            }
            PropagateOutcome::Interrupted => return PbCdclResult::Unknown,
        }

        match self.run_root_probing_interruptible(should_stop) {
            RootProbeOutcome::Ok => {}
            RootProbeOutcome::Unsat => {
                self.handle_unsat_proof(unsat_proof_mode);
                return PbCdclResult::Unsatisfiable;
            }
            RootProbeOutcome::Interrupted => return PbCdclResult::Unknown,
        }

        let dp_result = {
            let self_ref = &*self;
            self_ref.try_eq_knapsack_special_case(&mut || self_ref.interrupted || should_stop())
        };
        if let Some(result) = dp_result {
            self.stats.eq_knapsack_dp += 1;
            return result;
        }

        loop {
            if self.interrupted || should_stop() {
                return PbCdclResult::Unknown;
            }

            if self.all_assigned() {
                let model = self.extract_model();
                // SOUNDNESS SAFETY NET. The watched-slack propagator may, on rare
                // watch-state edge cases, report no conflict yet allow a complete
                // assignment that actually violates some constraint (cached-slack
                // staleness). Before declaring SAT, verify EVERY original
                // constraint against the model. If any is violated, the candidate
                // is NOT a model: convert the (exactly verified) violated
                // constraint into a conflict and drive normal conflict analysis,
                // so the search recovers instead of mis-reporting. This is sound
                // (only a genuinely violated constraint triggers it) and is the
                // last line of defence against silently dropped conflicts.
                let first_violated = self
                    .constraints
                    .iter()
                    .position(|c| !crate::solver::eval_constraint(c, &model))
                    .or_else(|| self.first_violated_active_permanent_learned(&model));
                if let Some(violated_cid) = first_violated {
                    if self.decision_level == 0 {
                        self.handle_unsat_proof(unsat_proof_mode);
                        return PbCdclResult::Unsatisfiable;
                    }
                    self.stats.conflicts += 1;
                    self.conflicts_since_restart += 1;
                    let (backtrack_level, learned) = {
                        let mut stop = InterruptOnlyStop { inner: should_stop };
                        match self.analyze_conflict_with_stop(violated_cid, &mut stop) {
                            ConflictAnalysisOutcome::Learned(result) => result,
                            ConflictAnalysisOutcome::Interrupted => {
                                return PbCdclResult::Unknown;
                            }
                        }
                    };
                    if self.backtrack_to_interruptible(backtrack_level, should_stop) {
                        return PbCdclResult::Unknown;
                    }
                    if let Some(constraint) = learned {
                        self.add_learned_constraint(constraint);
                    }
                    if self.should_restart() && self.restart_interruptible(should_stop) {
                        return PbCdclResult::Unknown;
                    }
                    if self.should_reduce_db() {
                        let mut stop = InterruptOnlyStop { inner: should_stop };
                        if self.reduce_db_with_stop(&mut stop) {
                            return PbCdclResult::Unknown;
                        }
                    }
                    continue;
                }
                if sat_proof_mode == SatProofMode::Conclude {
                    self.conclude_sat_proof(&model);
                }
                return PbCdclResult::Satisfiable(model);
            }

            let decision_lit = self.pick_decision_literal();
            let decision_result = self.decide_interruptible(decision_lit, should_stop);
            if matches!(decision_result, PropResult::Interrupted) {
                return PbCdclResult::Unknown;
            }

            loop {
                match self.propagate_all_interruptible(should_stop) {
                    PropagateOutcome::Ok => break,
                    PropagateOutcome::Conflict(conflict_cid) => {
                        self.stats.conflicts += 1;
                        self.conflicts_since_restart += 1;

                        if self.decision_level == 0 {
                            self.handle_unsat_proof(unsat_proof_mode);
                            return PbCdclResult::Unsatisfiable;
                        }

                        let (backtrack_level, learned) = {
                            let mut stop = InterruptOnlyStop { inner: should_stop };
                            match self.analyze_conflict_with_stop(conflict_cid, &mut stop) {
                                ConflictAnalysisOutcome::Learned(result) => result,
                                ConflictAnalysisOutcome::Interrupted => {
                                    return PbCdclResult::Unknown;
                                }
                            }
                        };

                        if self.backtrack_to_interruptible(backtrack_level, should_stop) {
                            return PbCdclResult::Unknown;
                        }

                        if let Some(constraint) = learned {
                            self.add_learned_constraint(constraint);
                        }

                        if self.should_restart() {
                            if self.restart_interruptible(should_stop) {
                                return PbCdclResult::Unknown;
                            }
                        }

                        if self.should_reduce_db() {
                            let mut stop = InterruptOnlyStop { inner: should_stop };
                            if self.reduce_db_with_stop(&mut stop) {
                                return PbCdclResult::Unknown;
                            }
                        }

                        if self.interrupted || should_stop() {
                            return PbCdclResult::Unknown;
                        }
                    }
                    PropagateOutcome::Interrupted => return PbCdclResult::Unknown,
                }
            }
        }
    }

    /// Returns solver statistics.
    #[must_use]
    pub fn stats(&self) -> &PbCdclStats {
        &self.stats
    }

    /// Diagnostic snapshot of the propagator event backlog (harness/profiling
    /// use): current length of the falsified-watch-events repair list. The
    /// unassign repair pass compacts this whole list, so its steady-state size
    /// bounds the per-backtrack undo cost.
    #[must_use]
    pub fn propagation_event_backlog(&self) -> usize {
        self.propagator.falsified_watch_events_len()
    }

    /// Diagnostic snapshot of the learned-constraint database (harness/profiling
    /// use): `(active_rows, glue_rows, avg_terms_of_active, max_terms_of_active)`.
    /// `glue_rows` counts active rows at or below the glue LBD threshold (never
    /// deleted by `reduce_db`). Heuristic diagnostics only — no solver state is
    /// touched.
    #[must_use]
    pub fn learned_db_diag(&self) -> (usize, usize, f64, usize) {
        let mut active = 0usize;
        let mut glue = 0usize;
        let mut term_sum = 0usize;
        let mut term_max = 0usize;
        for (idx, constraint) in self.learned_constraints.iter().enumerate() {
            if !self.learned_active.get(idx).copied().unwrap_or(false) {
                continue;
            }
            active += 1;
            let terms: usize = constraint.terms.iter().map(|t| t.lits.len()).sum();
            term_sum += terms;
            term_max = term_max.max(terms);
            if self.learned_lbd.get(idx).copied().unwrap_or(u32::MAX)
                <= self.config.glue_lbd_threshold
            {
                glue += 1;
            }
        }
        let avg = if active == 0 {
            0.0
        } else {
            term_sum as f64 / active as f64
        };
        (active, glue, avg, term_max)
    }

    /// Seeds the branching polarity (`saved_phase`) toward a caller-known
    /// assignment — a warm start. Each `(var, polarity)` pair biases the FIRST
    /// decision on `var` toward `polarity`; out-of-range vars are ignored.
    ///
    /// The seeds are retained and re-applied ON TOP of the internal
    /// objective-direction seeding at every `solve_optimize*` entry, so a
    /// caller-supplied incumbent (e.g. a heuristic baseline solution) wins over
    /// the default all-cheap-direction start and the first descent lands in the
    /// incumbent's neighborhood. Under a hard `objective <= G-1` bound this
    /// turns the anytime search into "improve the known solution" instead of
    /// "repair the over-optimistic all-zeros start".
    ///
    /// Soundness-neutral BY CONSTRUCTION: phase saving is consulted only when
    /// picking a decision literal's polarity. Propagation, conflict analysis,
    /// and model checking are unaffected, so seeding can never change a
    /// SAT/UNSAT verdict or admit an infeasible model — only which sound
    /// answer is reached first (and how fast).
    pub fn seed_phases(&mut self, phases: &[(u32, bool)]) {
        self.user_phase_seeds = phases.to_vec();
        self.apply_user_phase_seeds();
    }

    /// Re-applies the retained caller phase seeds onto `saved_phase` (see
    /// [`Self::seed_phases`]).
    fn apply_user_phase_seeds(&mut self) {
        for i in 0..self.user_phase_seeds.len() {
            let (var, polarity) = self.user_phase_seeds[i];
            let idx = var as usize;
            if idx < self.saved_phase.len() {
                self.saved_phase[idx] = polarity;
            }
        }
    }

    /// Sets the interrupt flag.
    pub fn interrupt(&mut self) {
        self.interrupted = true;
    }

    /// Solves a PB optimization instance using linear search with native
    /// bound tightening.
    ///
    /// Algorithm:
    /// 1. Find a feasible solution using `solve()`
    /// 2. Evaluate the objective on the solution
    /// 3. Add a PB constraint `sum(a_i * l_i) <= best - 1` (as `>= -(best-1)`)
    /// 4. Repeat until UNSAT (proving optimality) or interrupted
    ///
    /// Returns `Optimal` if the search completes, `Feasible` if interrupted
    /// with a best-known solution, or `Unsatisfiable` if no feasible solution
    /// exists.
    pub fn solve_optimize(
        &mut self,
        objective: &PbObjective,
        on_improve: Option<&mut dyn FnMut(i128, &[bool])>,
    ) -> PbCdclResult {
        self.solve_optimize_with_stop(objective, on_improve, |solver| solver.interrupted)
    }

    /// Solves optimization with an interruptibility check function.
    pub fn solve_optimize_interruptible<F>(
        &mut self,
        objective: &PbObjective,
        on_improve: Option<&mut dyn FnMut(i128, &[bool])>,
        should_stop: F,
    ) -> PbCdclResult
    where
        F: FnMut() -> bool,
    {
        let mut should_stop = should_stop;
        self.solve_optimize_interruptible_with_stop(objective, on_improve, &mut should_stop)
    }

    fn solve_optimize_with_stop<F>(
        &mut self,
        objective: &PbObjective,
        mut on_improve: Option<&mut dyn FnMut(i128, &[bool])>,
        mut should_stop: F,
    ) -> PbCdclResult
    where
        F: FnMut(&Self) -> bool,
    {
        if !objective_range_fits_i64(objective) {
            return PbCdclResult::Unknown;
        }

        // PROOF TAP: decision-only in this phase. Optimization under the tap
        // VOIDS the proof (fail closed: no certificate, never a wrong one)
        // and the solve continues unlogged.
        if self.proof_tap.is_some() {
            self.store_proof_error(ProofError::TapUnsupportedStep(
                "optimization solves are not tap-encodable in this phase",
            ));
        }

        // Phase 1: Find initial feasible solution.
        if self.proof_writer.is_some() {
            self.optimization_proof_pending = true;
        }
        self.seed_activity_from_objective(objective);
        self.seed_saved_phase_from_objective(objective);
        self.apply_user_phase_seeds();

        let initial_unsat_proof_mode = if self.proof_writer.is_some() {
            UnsatProofMode::DeriveOnly
        } else {
            UnsatProofMode::Conclude
        };
        let initial_result = self.solve_with_proof_controls(
            &mut should_stop,
            SatProofMode::Suppress,
            initial_unsat_proof_mode,
        );
        let (mut best_model, mut best_value) = match initial_result {
            PbCdclResult::Satisfiable(model) => {
                let value = eval_objective(objective, &model);
                if let Some(ref mut cb) = on_improve {
                    cb(value, &model);
                }
                (model, value)
            }
            PbCdclResult::Unsatisfiable => {
                self.conclude_opt_infeasible_proof();
                return PbCdclResult::Unsatisfiable;
            }
            PbCdclResult::Unknown => return PbCdclResult::Unknown,
            // Should not occur from solve_with_stop, but handle gracefully.
            other => return other,
        };

        // This variant's stop closure needs `&self`, so neither the structural
        // bound nor the LP can poll it; give them the solver deadline plus the
        // process-memory guard instead so a runaway exact-rational bound still
        // escapes before the harness's hard kill.
        let deadline = self.solve_deadline;
        let bound_stop = strided_process_memory_stop(move || {
            deadline.is_some_and(|d| std::time::Instant::now() >= d)
        });
        let structural_lower_bound = if self.proof_writer.is_none() {
            self.objective_lower_bound_from_solver_state(objective, &bound_stop)
        } else {
            None
        };

        // Opt-in: also compute the sound LP-relaxation lower bound once at the
        // root and fold it into the optimality-termination floor. The effective
        // floor is `max(structural, lp)`; both are independently sound lower
        // bounds, so their max never overshoots the optimum. Used ONLY to raise
        // the optimality-termination floor below — never to alter the incumbent.
        // A too-low/absent bound merely fails to prove (still sound).
        let effective_lower_bound = if native_lp_bound_enabled() {
            // `best_value` (the incumbent in hand) is the LP's early-exit
            // target: a floor at the incumbent already proves optimality, so
            // further LP tightening would be paid-for but unusable work.
            let lp_lower_bound =
                self.lp_objective_lower_bound_at_root(objective, Some(best_value), &bound_stop);
            max_optional_bounds(structural_lower_bound, lp_lower_bound)
        } else {
            structural_lower_bound
        };

        let mut can_conclude_opt_proof = self.proof_writer.is_some();

        // Phase 2: Iteratively tighten the objective bound.
        loop {
            if effective_lower_bound.is_some_and(|lower_bound| lower_bound >= best_value) {
                return PbCdclResult::Optimal(best_model, best_value);
            }

            // Fail-closed on the process-memory guard at incumbent-improvement
            // cadence: each iteration adds a PERMANENT dense objective-bound row
            // (add_from_pb_constraint below) that reduce-db cannot shed, so on a
            // dense instance thousands of improvements accrete GBs of permanent
            // rows. Reading the guard here ties the memory check directly to that
            // allocation event (once per improvement, off the propagation hot
            // path). Returning the incumbent is sound (never fabricates OPTIMAL).
            if should_stop(self) || ay_sys::process_memory_exceeded() {
                return PbCdclResult::Feasible(best_model, best_value);
            }

            // Add constraint: objective < best_value
            // i.e., sum(a_i * l_i) <= best_value - 1
            // Encoded as: sum(-a_i * l_i) >= -(best_value - 1)
            let Some(bound_constraint) = build_upper_bound_constraint(objective, best_value) else {
                // Overflow while encoding a stricter objective bound means we
                // can no longer prove optimality. Keep the incumbent but do
                // not upgrade it to OPTIMAL.
                return PbCdclResult::Feasible(best_model, best_value);
            };

            if !self.log_objective_bound_update(&best_model) {
                can_conclude_opt_proof = false;
            }

            // Add the bound constraint to the propagator and constraint list.
            let start = self.propagator.num_constraints();
            self.propagator.add_from_pb_constraint(&bound_constraint);
            let end = self.propagator.num_constraints();

            for cid in start..end {
                let internal = self
                    .propagator
                    .get_constraint_pb(cid)
                    .expect("freshly added bound constraint must be addressable");
                // The bound row goes to the LEARNED region as a permanent row,
                // NEVER into `self.constraints`: propagator cids are flat
                // indexes into [constraints | learned_constraints], and a
                // mirror-side push here would shift every already-learned
                // lemma by one — reduce_db would then deactivate (and, under
                // proof logging, `del`) the WRONG rows, including this very
                // bound row (silently demoting OPTIMUM FOUND to Feasible).
                // Mirrors add_constraint_runtime, the canonical runtime-row
                // path; LBD 1 + permanent keeps it off every deletion path.
                // Proof-id lockstep FIRST (the recorder computes the index the
                // row is ABOUT to occupy, exactly like the learn path): the
                // bound row's proof row is the soli-installed `obj <= best-1`
                // from log_objective_bound_update above. Without an entry at
                // this flat index, every LATER lemma's constraint_ids slot
                // shifts (shifted `del id`s -> checker rejects).
                if self.proof_writer.is_some() {
                    if let Some(bound_pid) = self.last_objective_bound_proof_id {
                        self.record_learned_constraint_id(bound_pid);
                    }
                }
                self.learned_constraints.push(internal);
                self.learned_lbd.push(1);
                self.learned_active.push(true);
                self.learned_permanent.push(true);
                self.learned_activity.push(self.learned_constraint_inc);
            }
            self.debug_assert_constraint_arrays_in_lockstep();
            self.replace_active_optimization_bound(start, end);

            // Restart to decision level 0 before re-solving.
            self.backtrack_to(0);

            // Re-solve with the tightened bound.
            match decide_tightened_solve_result(objective, &best_model, best_value, {
                let previous_suppression = self.suppress_optimization_intermediate_proof_steps;
                // Suppression — and the del-through-suppression whitelist it
                // guards (proof_logging.rs
                // should_suppress_optimization_intermediate_proof_step) — is
                // keyed on the WRITER, not the tap, on purpose. Tap-mode OPT
                // proof is not yet built: the OPT drivers construct
                // with_proof_writer_interruptible (solve_optimization_with_proof
                // in bin/ay.rs, cmd_pb.rs), the tap only certifies decision
                // SAT/UNSAT, and this loop fails closed for a tap solver at the
                // fence above (proof_tap.is_some() -> TapUnsupportedStep). So
                // under the tap proof_writer is None -> suppression stays off ->
                // no suppressed-born lemmas and reduce_db dels carry real pids.
                // FOLLOW-ON B item-3 activates only when tap-mode OPT lands (see
                // conclude_opt_proof, likewise writer-only).
                self.suppress_optimization_intermediate_proof_steps = self.proof_writer.is_some();
                let result = self.solve_with_proof_controls(
                    &mut should_stop,
                    SatProofMode::Suppress,
                    UnsatProofMode::DeriveOnly,
                );
                self.suppress_optimization_intermediate_proof_steps = previous_suppression;
                result
            }) {
                TightenedSolveDecision::Continue { model, value } => {
                    best_value = value;
                    best_model = model;
                    if let Some(ref mut cb) = on_improve {
                        cb(best_value, &best_model);
                    }
                }
                TightenedSolveDecision::Return(result) => {
                    if matches!(result, PbCdclResult::Optimal(_, _)) && can_conclude_opt_proof {
                        self.conclude_opt_proof(objective, best_value);
                    }
                    return result;
                }
            }
        }
    }

    fn solve_optimize_interruptible_with_stop<F>(
        &mut self,
        objective: &PbObjective,
        mut on_improve: Option<&mut dyn FnMut(i128, &[bool])>,
        should_stop: &mut F,
    ) -> PbCdclResult
    where
        F: FnMut() -> bool,
    {
        if !objective_range_fits_i64(objective) {
            return PbCdclResult::Unknown;
        }

        // PROOF TAP: decision-only in this phase (see solve_optimize_with_stop).
        if self.proof_tap.is_some() {
            self.store_proof_error(ProofError::TapUnsupportedStep(
                "optimization solves are not tap-encodable in this phase",
            ));
        }

        if self.proof_writer.is_some() {
            self.optimization_proof_pending = true;
        }
        self.seed_activity_from_objective(objective);
        self.seed_saved_phase_from_objective(objective);
        self.apply_user_phase_seeds();

        let phase_completion_result = if self.config.phase_completion_enabled {
            self.try_phase_completion_incumbent_interruptible(should_stop)
        } else {
            PhaseCompletionOutcome::Skipped
        };

        let initial_result = match phase_completion_result {
            PhaseCompletionOutcome::Model(model) => PbCdclResult::Satisfiable(model),
            PhaseCompletionOutcome::Interrupted => return PbCdclResult::Unknown,
            PhaseCompletionOutcome::Conflict
            | PhaseCompletionOutcome::Invalid
            | PhaseCompletionOutcome::Skipped => {
                let initial_unsat_proof_mode = if self.proof_writer.is_some() {
                    UnsatProofMode::DeriveOnly
                } else {
                    UnsatProofMode::Conclude
                };
                self.solve_interruptible_with_proof_controls(
                    should_stop,
                    SatProofMode::Suppress,
                    initial_unsat_proof_mode,
                )
            }
        };
        let (mut best_model, mut best_value) = match initial_result {
            PbCdclResult::Satisfiable(model) => {
                let value = eval_objective(objective, &model);
                if let Some(ref mut cb) = on_improve {
                    cb(value, &model);
                }
                (model, value)
            }
            PbCdclResult::Unsatisfiable => {
                self.conclude_opt_infeasible_proof();
                return PbCdclResult::Unsatisfiable;
            }
            PbCdclResult::Unknown => return PbCdclResult::Unknown,
            other => return other,
        };

        // Opt-in: also compute the sound LP-relaxation lower bound once at the
        // root and fold it into the optimality-termination floor (see
        // [`Self::lp_objective_lower_bound_at_root`]). The interruptible caller's
        // stop closure fires on every anytime improvement (to yield the
        // incumbent), so it must NOT gate this bound — the bound runs precisely
        // to promote an interrupted incumbent to optimal, and gating it on the
        // just-fired interrupt would degrade every anytime OPTIMUM to FEASIBLE.
        // Bound it by the solver deadline plus the process-memory guard instead
        // (the work-proxy already declines a detonator-sized elimination
        // upfront), mirroring `solve_optimize_with_stop`. The bound is used ONLY
        // to raise the termination floor, never to alter the incumbent.
        let effective_lower_bound = {
            let deadline = self.solve_deadline;
            let bound_stop = strided_process_memory_stop(move || {
                deadline.is_some_and(|d| std::time::Instant::now() >= d)
            });
            let structural_lower_bound = if self.proof_writer.is_none() {
                self.objective_lower_bound_from_solver_state(objective, &bound_stop)
            } else {
                None
            };
            if native_lp_bound_enabled() {
                // `best_value` (the incumbent in hand) is the LP's early-exit
                // target: a floor at the incumbent already proves optimality,
                // so further LP tightening would be unusable work.
                let lp_lower_bound =
                    self.lp_objective_lower_bound_at_root(objective, Some(best_value), &bound_stop);
                max_optional_bounds(structural_lower_bound, lp_lower_bound)
            } else {
                structural_lower_bound
            }
        };

        let mut can_conclude_opt_proof = self.proof_writer.is_some();

        loop {
            if effective_lower_bound.is_some_and(|lower_bound| lower_bound >= best_value) {
                return PbCdclResult::Optimal(best_model, best_value);
            }

            // Fail-closed on the process-memory guard at incumbent-improvement
            // cadence — see the sibling tighten loop: the permanent dense bound
            // row added each iteration (add_from_pb_constraint below) is not
            // shed-able, so this direct read ties the check to that allocation.
            if self.interrupted || should_stop() || ay_sys::process_memory_exceeded() {
                return PbCdclResult::Feasible(best_model, best_value);
            }

            let Some(bound_constraint) = build_upper_bound_constraint(objective, best_value) else {
                return PbCdclResult::Feasible(best_model, best_value);
            };

            if !self.log_objective_bound_update(&best_model) {
                can_conclude_opt_proof = false;
            }

            let start = self.propagator.num_constraints();
            self.propagator.add_from_pb_constraint(&bound_constraint);
            let end = self.propagator.num_constraints();

            for cid in start..end {
                let internal = self
                    .propagator
                    .get_constraint_pb(cid)
                    .expect("freshly added bound constraint must be addressable");
                // The bound row goes to the LEARNED region as a permanent row,
                // NEVER into `self.constraints`: propagator cids are flat
                // indexes into [constraints | learned_constraints], and a
                // mirror-side push here would shift every already-learned
                // lemma by one — reduce_db would then deactivate (and, under
                // proof logging, `del`) the WRONG rows, including this very
                // bound row (silently demoting OPTIMUM FOUND to Feasible).
                // Mirrors add_constraint_runtime, the canonical runtime-row
                // path; LBD 1 + permanent keeps it off every deletion path.
                // Proof-id lockstep FIRST (the recorder computes the index the
                // row is ABOUT to occupy, exactly like the learn path): the
                // bound row's proof row is the soli-installed `obj <= best-1`
                // from log_objective_bound_update above. Without an entry at
                // this flat index, every LATER lemma's constraint_ids slot
                // shifts (shifted `del id`s -> checker rejects).
                if self.proof_writer.is_some() {
                    if let Some(bound_pid) = self.last_objective_bound_proof_id {
                        self.record_learned_constraint_id(bound_pid);
                    }
                }
                self.learned_constraints.push(internal);
                self.learned_lbd.push(1);
                self.learned_active.push(true);
                self.learned_permanent.push(true);
                self.learned_activity.push(self.learned_constraint_inc);
            }
            self.debug_assert_constraint_arrays_in_lockstep();
            self.replace_active_optimization_bound(start, end);

            if self.backtrack_to_interruptible(0, should_stop) {
                return PbCdclResult::Feasible(best_model, best_value);
            }

            match decide_tightened_solve_result(objective, &best_model, best_value, {
                let previous_suppression = self.suppress_optimization_intermediate_proof_steps;
                // Suppression — and the del-through-suppression whitelist it
                // guards (proof_logging.rs
                // should_suppress_optimization_intermediate_proof_step) — is
                // keyed on the WRITER, not the tap, on purpose. Tap-mode OPT
                // proof is not yet built: the OPT drivers construct
                // with_proof_writer_interruptible (solve_optimization_with_proof
                // in bin/ay.rs, cmd_pb.rs), the tap only certifies decision
                // SAT/UNSAT, and this loop fails closed for a tap solver at the
                // fence above (proof_tap.is_some() -> TapUnsupportedStep). So
                // under the tap proof_writer is None -> suppression stays off ->
                // no suppressed-born lemmas and reduce_db dels carry real pids.
                // FOLLOW-ON B item-3 activates only when tap-mode OPT lands (see
                // conclude_opt_proof, likewise writer-only).
                self.suppress_optimization_intermediate_proof_steps = self.proof_writer.is_some();
                let result = self.solve_interruptible_with_proof_controls(
                    should_stop,
                    SatProofMode::Suppress,
                    UnsatProofMode::DeriveOnly,
                );
                self.suppress_optimization_intermediate_proof_steps = previous_suppression;
                result
            }) {
                TightenedSolveDecision::Continue { model, value } => {
                    best_value = value;
                    best_model = model;
                    if let Some(ref mut cb) = on_improve {
                        cb(best_value, &best_model);
                    }
                }
                TightenedSolveDecision::Return(result) => {
                    if matches!(result, PbCdclResult::Optimal(_, _)) && can_conclude_opt_proof {
                        self.conclude_opt_proof(objective, best_value);
                    }
                    return result;
                }
            }
        }
    }

    fn try_phase_completion_incumbent_interruptible<F>(
        &mut self,
        should_stop: &mut F,
    ) -> PhaseCompletionOutcome
    where
        F: FnMut() -> bool,
    {
        if self.proof_writer.is_some() || self.proof_tap.is_some() || self.decision_level != 0 {
            return PhaseCompletionOutcome::Skipped;
        }

        match self.propagate_all_interruptible(should_stop) {
            PropagateOutcome::Ok => {}
            PropagateOutcome::Conflict(_) => {
                self.backtrack_to(0);
                return PhaseCompletionOutcome::Conflict;
            }
            PropagateOutcome::Interrupted => {
                self.backtrack_to(0);
                return PhaseCompletionOutcome::Interrupted;
            }
        }

        for var in 1..=self.num_vars {
            if self.interrupted || should_stop() {
                self.backtrack_to(0);
                return PhaseCompletionOutcome::Interrupted;
            }
            let lit = var as Lit;
            if self.propagator.value(lit) != LitValue::Unassigned {
                continue;
            }

            self.decision_level += 1;
            self.trail_lim.push(self.trail.len());
            self.stats.decisions += 1;

            let preferred_lit = if self.saved_phase.get(var as usize).copied().unwrap_or(false) {
                lit
            } else {
                -lit
            };

            match self.assign_interruptible(preferred_lit, None, should_stop) {
                PropResult::Ok | PropResult::Propagated(_, _, _) => {}
                PropResult::Conflict(_, _) => {
                    self.backtrack_to(0);
                    return PhaseCompletionOutcome::Conflict;
                }
                PropResult::Interrupted => {
                    self.backtrack_to(0);
                    return PhaseCompletionOutcome::Interrupted;
                }
            }

            match self.propagate_all_interruptible(should_stop) {
                PropagateOutcome::Ok => {}
                PropagateOutcome::Conflict(_) => {
                    self.backtrack_to(0);
                    return PhaseCompletionOutcome::Conflict;
                }
                PropagateOutcome::Interrupted => {
                    self.backtrack_to(0);
                    return PhaseCompletionOutcome::Interrupted;
                }
            }
        }

        let model = self.extract_model();
        let valid = self
            .constraints
            .iter()
            .all(|constraint| crate::solver::eval_constraint(constraint, &model));
        self.backtrack_to(0);

        if valid {
            PhaseCompletionOutcome::Model(model)
        } else {
            PhaseCompletionOutcome::Invalid
        }
    }

    // --- Internal methods ---

    /// Runs a bounded failed-literal probing pass before the first search
    /// decision. Conflicting probes are turned into learned root constraints.
    fn run_root_probing_with_stop<F>(&mut self, should_stop: &mut F) -> RootProbeOutcome
    where
        F: FnMut(&Self) -> bool,
    {
        if !self.config.root_probe_enabled
            || self.config.root_probe_max_probes == 0
            || self.decision_level != 0
            || self.all_assigned()
        {
            return RootProbeOutcome::Ok;
        }

        let candidates = self.root_probe_candidates(self.config.root_probe_max_probes);
        let mut probes_used = 0usize;

        for var in candidates {
            if should_stop(self) {
                return RootProbeOutcome::Interrupted;
            }
            if self.propagator.value(var as Lit) != LitValue::Unassigned {
                continue;
            }

            for probe_lit in self.root_probe_literals(var) {
                if probes_used >= self.config.root_probe_max_probes {
                    return RootProbeOutcome::Ok;
                }
                if should_stop(self) {
                    return RootProbeOutcome::Interrupted;
                }
                if self.propagator.value(var as Lit) != LitValue::Unassigned {
                    break;
                }

                probes_used += 1;
                match self.run_single_root_probe_with_stop(probe_lit, should_stop) {
                    RootProbeOutcome::Ok => {}
                    RootProbeOutcome::Unsat => return RootProbeOutcome::Unsat,
                    RootProbeOutcome::Interrupted => return RootProbeOutcome::Interrupted,
                }
            }
        }

        RootProbeOutcome::Ok
    }

    fn run_root_probing_interruptible<F>(&mut self, should_stop: &mut F) -> RootProbeOutcome
    where
        F: FnMut() -> bool,
    {
        if !self.config.root_probe_enabled
            || self.config.root_probe_max_probes == 0
            || self.decision_level != 0
            || self.all_assigned()
        {
            return RootProbeOutcome::Ok;
        }

        let candidates = self.root_probe_candidates(self.config.root_probe_max_probes);
        let mut probes_used = 0usize;

        for var in candidates {
            if self.interrupted || should_stop() {
                return RootProbeOutcome::Interrupted;
            }
            if self.propagator.value(var as Lit) != LitValue::Unassigned {
                continue;
            }

            for probe_lit in self.root_probe_literals(var) {
                if probes_used >= self.config.root_probe_max_probes {
                    return RootProbeOutcome::Ok;
                }
                if self.interrupted || should_stop() {
                    return RootProbeOutcome::Interrupted;
                }
                if self.propagator.value(var as Lit) != LitValue::Unassigned {
                    break;
                }

                probes_used += 1;
                match self.run_single_root_probe_interruptible(probe_lit, should_stop) {
                    RootProbeOutcome::Ok => {}
                    RootProbeOutcome::Unsat => return RootProbeOutcome::Unsat,
                    RootProbeOutcome::Interrupted => return RootProbeOutcome::Interrupted,
                }
            }
        }

        RootProbeOutcome::Ok
    }

    fn run_single_root_probe_with_stop<F>(
        &mut self,
        lit: Lit,
        should_stop: &mut F,
    ) -> RootProbeOutcome
    where
        F: FnMut(&Self) -> bool,
    {
        debug_assert_eq!(self.decision_level, 0);
        let saved_phase_before = self.saved_phase.clone();
        self.decision_level = 1;
        self.trail_lim.push(self.trail.len());

        let initial = self.assign(lit, None);
        let propagation = match initial {
            PropResult::Conflict(_, cid) if cid != usize::MAX => PropagateOutcome::Conflict(cid),
            PropResult::Conflict(_, _) => PropagateOutcome::Ok,
            PropResult::Interrupted => PropagateOutcome::Interrupted,
            _ => self.propagate_all(should_stop),
        };

        match propagation {
            PropagateOutcome::Ok => {
                self.undo_root_probe_to_boundary();
                self.saved_phase.clone_from(&saved_phase_before);
                RootProbeOutcome::Ok
            }
            PropagateOutcome::Interrupted => {
                self.undo_root_probe_to_boundary();
                self.saved_phase.clone_from(&saved_phase_before);
                RootProbeOutcome::Interrupted
            }
            PropagateOutcome::Conflict(conflict_cid) => {
                self.record_conflict();
                let analyzed = self.analyze_conflict_with_stop(conflict_cid, should_stop);
                self.undo_root_probe_to_boundary();
                self.saved_phase.clone_from(&saved_phase_before);

                let ConflictAnalysisOutcome::Learned((backtrack_level, learned)) = analyzed else {
                    return RootProbeOutcome::Interrupted;
                };
                debug_assert_eq!(
                    backtrack_level, 0,
                    "root probing should only learn constraints that backtrack to level 0"
                );

                if let Some(constraint) = learned {
                    self.add_learned_constraint(constraint);
                }

                match self.propagate_all(should_stop) {
                    PropagateOutcome::Ok => RootProbeOutcome::Ok,
                    PropagateOutcome::Conflict(_) => RootProbeOutcome::Unsat,
                    PropagateOutcome::Interrupted => RootProbeOutcome::Interrupted,
                }
            }
        }
    }

    /// Cheap, **state-restoring** root-implication query: pushes `assumption` as a
    /// fresh decision at level 1, unit-propagates with the existing propagator, and
    /// returns the literals forced true (the assumption plus its consequences),
    /// then backtracks cleanly to the prior level-0 state.
    ///
    /// This is the building block for at-most-one (AM1) clique extraction over soft
    /// selectors in the weighted core-guided optimizer: an edge `s_i -- s_j` exists
    /// iff assuming `s_i` forces `s_j` false (the complement of `s_j` is implied).
    ///
    /// # Soundness
    /// Unit propagation only derives logically-entailed consequences of the
    /// constraint set under the assumption, so every literal in the returned
    /// `Implied` vector is true in EVERY feasible assignment that sets `assumption`
    /// true. A `Conflict` outcome means `assumption` is false in every feasible
    /// assignment (its complement is a forced fact). Neither verdict is ever
    /// reported on an interruption / proof-mode / out-of-range query — those return
    /// `Unavailable`, which the caller must treat as "no information".
    ///
    /// # State restoration
    /// The query runs entirely above a fresh level-1 trail boundary and is undone
    /// via the same `pop_root_probe_suffix` path the standard root probe uses: every
    /// literal pushed above the boundary is unassigned, the variables are returned
    /// to the VSIDS heap, the trail-limit marker is popped, and `decision_level`
    /// is reset to 0. Unlike the standard probe it learns NO constraint (no
    /// `add_learned_constraint`), so the constraint database, `saved_phase`, and
    /// every other field are byte-for-byte identical before and after the call.
    /// A `debug_assert` checks the trail and decision level are fully restored.
    pub(crate) fn implied_literals_at_root(&mut self, assumption: PbLit) -> ImpliedLiteralsOutcome {
        // Match the gating the standard root probe relies on: proof logging makes
        // the (silent, un-logged) probe unsound to mix into a certificate, and the
        // primitive is only meaningful from a clean root.
        if self.proof_writer.is_some() || self.proof_tap.is_some() || self.decision_level != 0 {
            return ImpliedLiteralsOutcome::Unavailable;
        }
        if assumption.var == 0 || assumption.var > self.num_vars || assumption.var > i32::MAX as u32
        {
            return ImpliedLiteralsOutcome::Unavailable;
        }

        let dimacs = pb_lit_to_dimacs(assumption);
        // If the assumption's value is already fixed at the root, no probe is
        // needed: a true literal implies (at least) itself with no new
        // consequences to collect beyond the existing root units; a false literal
        // is a forced conflict.
        match self.propagator.value(dimacs) {
            LitValue::True => return ImpliedLiteralsOutcome::Implied(vec![assumption]),
            LitValue::False => return ImpliedLiteralsOutcome::Conflict,
            LitValue::Unassigned => {}
        }

        // Snapshot the fields the probe is allowed to perturb so we can assert exact
        // restoration. (Behavioral fields like stats are intentionally excluded.)
        let saved_phase_before = self.saved_phase.clone();
        let trail_len_before = self.trail.len();
        let trail_lim_len_before = self.trail_lim.len();
        let learned_count_before = self.learned_constraints.len();

        // Open a fresh decision level and assert the assumption, mirroring
        // `run_single_root_probe_with_stop` but WITHOUT conflict learning.
        self.decision_level = 1;
        self.trail_lim.push(self.trail.len());

        let initial = self.assign(dimacs, None);
        let mut never_stop = |_: &Self| false;
        let propagation = match initial {
            PropResult::Conflict(_, _) => PropagateOutcome::Conflict(usize::MAX),
            PropResult::Interrupted => PropagateOutcome::Interrupted,
            _ => self.propagate_all(&mut never_stop),
        };

        let result = match propagation {
            PropagateOutcome::Ok => {
                // Collect everything forced true above the boundary, in trail order
                // (the assumption is first), BEFORE unwinding.
                let mut implied = Vec::with_capacity(self.trail.len() - trail_len_before);
                for entry in &self.trail[trail_len_before..] {
                    implied.push(dimacs_to_pb_lit(entry.lit));
                }
                ImpliedLiteralsOutcome::Implied(implied)
            }
            PropagateOutcome::Conflict(_) => ImpliedLiteralsOutcome::Conflict,
            PropagateOutcome::Interrupted => ImpliedLiteralsOutcome::Unavailable,
        };

        // Restore: pop the probe suffix back to the boundary (unassign + reheap),
        // pop the trail-limit marker, reset to level 0. No learned constraint is
        // added, so the database is unchanged. `saved_phase` is restored from the
        // snapshot because `assign` records phases for the probed literals.
        self.undo_root_probe_to_boundary();
        self.saved_phase.clone_from(&saved_phase_before);

        debug_assert_eq!(
            self.decision_level, 0,
            "implied_literals_at_root must restore level 0"
        );
        debug_assert_eq!(
            self.trail.len(),
            trail_len_before,
            "implied_literals_at_root must restore the trail length"
        );
        debug_assert_eq!(
            self.trail_lim.len(),
            trail_lim_len_before,
            "implied_literals_at_root must restore trail_lim"
        );
        debug_assert_eq!(
            self.learned_constraints.len(),
            learned_count_before,
            "implied_literals_at_root must not learn any constraint"
        );

        result
    }

    fn run_single_root_probe_interruptible<F>(
        &mut self,
        lit: Lit,
        should_stop: &mut F,
    ) -> RootProbeOutcome
    where
        F: FnMut() -> bool,
    {
        debug_assert_eq!(self.decision_level, 0);
        let saved_phase_before = self.saved_phase.clone();
        self.decision_level = 1;
        self.trail_lim.push(self.trail.len());

        let initial = self.assign_interruptible(lit, None, should_stop);
        let propagation = match initial {
            PropResult::Conflict(_, cid) if cid != usize::MAX => PropagateOutcome::Conflict(cid),
            PropResult::Conflict(_, _) => PropagateOutcome::Ok,
            PropResult::Interrupted => PropagateOutcome::Interrupted,
            _ => self.propagate_all_interruptible(should_stop),
        };

        match propagation {
            PropagateOutcome::Ok => {
                let interrupted = self.undo_root_probe_to_boundary_interruptible(should_stop);
                self.saved_phase.clone_from(&saved_phase_before);
                if interrupted {
                    RootProbeOutcome::Interrupted
                } else {
                    RootProbeOutcome::Ok
                }
            }
            PropagateOutcome::Interrupted => {
                let _ = self.undo_root_probe_to_boundary_interruptible(should_stop);
                self.saved_phase.clone_from(&saved_phase_before);
                RootProbeOutcome::Interrupted
            }
            PropagateOutcome::Conflict(conflict_cid) => {
                self.record_conflict();
                let analyzed = {
                    let mut stop = InterruptOnlyStop { inner: should_stop };
                    self.analyze_conflict_with_stop(conflict_cid, &mut stop)
                };
                let interrupted = self.undo_root_probe_to_boundary_interruptible(should_stop);
                self.saved_phase.clone_from(&saved_phase_before);
                if interrupted {
                    return RootProbeOutcome::Interrupted;
                }

                let ConflictAnalysisOutcome::Learned((backtrack_level, learned)) = analyzed else {
                    return RootProbeOutcome::Interrupted;
                };
                debug_assert_eq!(
                    backtrack_level, 0,
                    "root probing should only learn constraints that backtrack to level 0"
                );

                if let Some(constraint) = learned {
                    self.add_learned_constraint(constraint);
                }

                match self.propagate_all_interruptible(should_stop) {
                    PropagateOutcome::Ok => RootProbeOutcome::Ok,
                    PropagateOutcome::Conflict(_) => RootProbeOutcome::Unsat,
                    PropagateOutcome::Interrupted => RootProbeOutcome::Interrupted,
                }
            }
        }
    }

    fn undo_root_probe_to_boundary(&mut self) {
        let unassigned_lits = self.pop_root_probe_suffix();
        self.propagator.unassign_literals(&unassigned_lits);
    }

    fn undo_root_probe_to_boundary_interruptible<F>(&mut self, should_stop: &mut F) -> bool
    where
        F: FnMut() -> bool,
    {
        let unassigned_lits = self.pop_root_probe_suffix();
        self.propagator
            .unassign_literals_interruptible(&unassigned_lits, &mut *should_stop)
    }

    fn pop_root_probe_suffix(&mut self) -> Vec<Lit> {
        debug_assert_eq!(self.decision_level, 1);
        let Some(target_trail_pos) = self.trail_lim.pop() else {
            debug_assert!(false, "root probe must have a trail boundary");
            self.decision_level = 0;
            return Vec::new();
        };

        let mut unassigned_lits = Vec::with_capacity(self.trail.len() - target_trail_pos);
        while self.trail.len() > target_trail_pos {
            let entry = self.trail.pop().expect("trail not empty");
            let var = entry.lit.unsigned_abs();
            unassigned_lits.push(entry.lit);
            self.vsids_heap.insert(var, &self.activity);
        }
        self.decision_level = 0;
        unassigned_lits
    }

    fn record_conflict(&mut self) {
        self.stats.conflicts += 1;
        self.conflicts_since_restart += 1;
    }

    fn root_probe_candidates(&self, max_candidates: usize) -> Vec<u32> {
        if max_candidates == 0 {
            return Vec::new();
        }

        let mut candidates: Vec<(u32, f64)> = Vec::with_capacity(max_candidates);
        for var in 1..=self.num_vars {
            if self.propagator.value(var as Lit) != LitValue::Unassigned {
                continue;
            }

            let score = self.activity.get(var as usize).copied().unwrap_or_default();
            let mut insert_at = candidates.len();
            for (idx, (existing_var, existing_score)) in candidates.iter().enumerate() {
                if score > *existing_score || (score == *existing_score && var < *existing_var) {
                    insert_at = idx;
                    break;
                }
            }

            if insert_at == candidates.len() {
                if candidates.len() < max_candidates {
                    candidates.push((var, score));
                }
                continue;
            }

            candidates.insert(insert_at, (var, score));
            if candidates.len() > max_candidates {
                candidates.pop();
            }
        }

        candidates.into_iter().map(|(var, _)| var).collect()
    }

    fn root_probe_literals(&self, var: u32) -> [Lit; 2] {
        let lit = var as Lit;
        if self.saved_phase.get(var as usize).copied().unwrap_or(false) {
            [-lit, lit]
        } else {
            [lit, -lit]
        }
    }

    fn prepare_assumptions(&self, assumptions: &[PbLit]) -> AssumptionPreparation {
        let mut active = Vec::with_capacity(assumptions.len());
        let mut by_var: HashMap<u32, PbLit> = HashMap::new();

        for &assumption in assumptions {
            if assumption.var == 0
                || assumption.var > self.num_vars
                || assumption.var > i32::MAX as u32
            {
                return AssumptionPreparation::Unsupported;
            }

            if let Some(&previous) = by_var.get(&assumption.var) {
                if previous.negated != assumption.negated {
                    return AssumptionPreparation::Contradiction(vec![previous, assumption]);
                }
                continue;
            }

            by_var.insert(assumption.var, assumption);
            active.push(assumption);
        }

        AssumptionPreparation::Ready(active)
    }

    fn apply_assumptions<F>(
        &mut self,
        assumptions: &[PbLit],
        should_stop: &mut F,
    ) -> ApplyAssumptionsOutcome
    where
        F: FnMut(&Self) -> bool,
    {
        for (idx, &assumption) in assumptions.iter().enumerate() {
            if should_stop(self) {
                return ApplyAssumptionsOutcome::Interrupted;
            }

            let dimacs_lit = pb_lit_to_dimacs(assumption);
            match self.propagator.value(dimacs_lit) {
                LitValue::True => continue,
                LitValue::False => {
                    // DOMINANT PATH on core-guided search: this assumption was
                    // already falsified by propagation from EARLIER assumptions,
                    // so the conflict is "the reason that forced it" plus this
                    // assumption. Recover that reason from the trail and run the
                    // same conflict analysis; falling back to the prefix only
                    // when the literal has no recorded reason (a root-level
                    // fixing, where the prefix is already the honest answer).
                    let falsified = pb_lit_to_dimacs(assumption).unsigned_abs();
                    let reason = self
                        .trail
                        .iter()
                        .rev()
                        .find(|entry| entry.lit.unsigned_abs() == falsified)
                        .and_then(|entry| entry.reason);
                    let core = match reason {
                        Some(cid) => {
                            let mut c =
                                self.extract_assumption_conflict_core(cid, &assumptions[..=idx]);
                            // The TRIGGERING assumption is part of the conflict by
                            // construction (its negation is what propagation forced)
                            // but it is not on the trail yet, so the analysis cannot
                            // find it. Omitting it yields a core that does not
                            // actually entail UNSAT.
                            if !c.contains(&assumption) {
                                c.push(assumption);
                            }
                            // Canonical order: cores are compared and summarised
                            // downstream, so emit them in ASSUMPTION order rather
                            // than trail-resolution order (which runs newest-first
                            // and would make the same core look different).
                            let rank: HashMap<PbLit, usize> = assumptions[..=idx]
                                .iter()
                                .enumerate()
                                .map(|(i, &a)| (a, i))
                                .collect();
                            c.sort_by_key(|lit| rank.get(lit).copied().unwrap_or(usize::MAX));
                            c
                        }
                        None => assumptions[..=idx].to_vec(),
                    };
                    return ApplyAssumptionsOutcome::Unsat(core);
                }
                LitValue::Unassigned => {}
            }

            self.decision_level += 1;
            self.trail_lim.push(self.trail.len());
            self.stats.decisions += 1;

            match self.assign(dimacs_lit, None) {
                PropResult::Conflict(_, cid) => {
                    // Same true-core extraction as the propagate_all arm below.
                    let core = self.extract_assumption_conflict_core(cid, &assumptions[..=idx]);
                    return ApplyAssumptionsOutcome::Unsat(core);
                }
                PropResult::Interrupted => return ApplyAssumptionsOutcome::Interrupted,
                PropResult::Ok | PropResult::Propagated(_, _, _) => {}
            }

            match self.propagate_all(should_stop) {
                PropagateOutcome::Ok => {}
                PropagateOutcome::Conflict(cid) => {
                    // TRUE CORE, not the assumption PREFIX. Returning
                    // `assumptions[..=idx]` is sound but maximally weak: it
                    // names every assumption applied so far, including the many
                    // that had nothing to do with the conflict. Core-guided
                    // search then pays for that twice — a weak core claims far
                    // more softs than it should (so fewer disjoint cores fit in
                    // a round, and the bound rises more slowly), and OLL burns
                    // up to MAX_CORE_TRIM_CHECKS solves per core trying to
                    // shrink it back down by deletion.
                    //
                    // Measured before this change on domset mw19_19: the
                    // returned core was byte-identical to the assumption set in
                    // 980 of 982 re-solves, and deletion-trimming recovered only
                    // 0.96 literals per solve while cutting cores roughly in
                    // half (62 -> 32) before hitting its check cap.
                    //
                    // `extract_assumption_conflict_core` resolves the conflict
                    // back through the trail and keeps only the assumptions that
                    // actually participate; it falls back to the full prefix on
                    // any shape it cannot analyse, so this is never less sound.
                    let core = self.extract_assumption_conflict_core(cid, &assumptions[..=idx]);
                    return ApplyAssumptionsOutcome::Unsat(core);
                }
                PropagateOutcome::Interrupted => return ApplyAssumptionsOutcome::Interrupted,
            }
        }

        ApplyAssumptionsOutcome::Ok(self.decision_level)
    }

    fn finish_assumption_solve(
        &mut self,
        result: PbCdclAssumptionResult,
    ) -> PbCdclAssumptionResult {
        self.backtrack_to(0);
        result
    }

    fn decide(&mut self, lit: Lit) {
        self.decision_level += 1;
        self.trail_lim.push(self.trail.len());
        self.stats.decisions += 1;
        let _ = self.assign(lit, None);
    }

    fn decide_interruptible<F>(&mut self, lit: Lit, should_stop: &mut F) -> PropResult
    where
        F: FnMut() -> bool,
    {
        if self.interrupted || should_stop() {
            return PropResult::Interrupted;
        }
        let trail_len_before_decision = self.trail.len();
        self.decision_level += 1;
        self.trail_lim.push(trail_len_before_decision);
        self.stats.decisions += 1;
        let result = self.assign_interruptible(lit, None, should_stop);
        if matches!(result, PropResult::Interrupted)
            && self.trail.len() == trail_len_before_decision
        {
            self.decision_level -= 1;
            self.trail_lim.pop();
            self.stats.decisions = self.stats.decisions.saturating_sub(1);
        }
        result
    }

    fn assign(&mut self, lit: Lit, reason: Option<usize>) -> PropResult {
        // Phase saving: remember the polarity of this variable assignment.
        let var = lit.unsigned_abs();
        if (var as usize) < self.saved_phase.len() {
            self.saved_phase[var as usize] = lit > 0;
        }
        self.trail.push(TrailEntry {
            lit,
            level: self.decision_level,
            reason,
        });
        self.propagator.assign_literal(lit, self.decision_level)
    }

    fn assign_interruptible<F>(
        &mut self,
        lit: Lit,
        reason: Option<usize>,
        should_stop: &mut F,
    ) -> PropResult
    where
        F: FnMut() -> bool,
    {
        if self.interrupted || should_stop() {
            return PropResult::Interrupted;
        }
        let var = lit.unsigned_abs();
        let saved_phase_before = self.saved_phase.get(var as usize).copied();
        if (var as usize) < self.saved_phase.len() {
            self.saved_phase[var as usize] = lit > 0;
        }
        self.trail.push(TrailEntry {
            lit,
            level: self.decision_level,
            reason,
        });
        let result =
            self.propagator
                .assign_literal_interruptible(lit, self.decision_level, should_stop);
        if matches!(result, PropResult::Interrupted) && self.propagator.value(lit) != LitValue::True
        {
            self.trail.pop();
            if let Some(saved_phase_before) = saved_phase_before {
                self.saved_phase[var as usize] = saved_phase_before;
            }
        }
        result
    }

    fn propagate_all<F>(&mut self, should_stop: &mut F) -> PropagateOutcome
    where
        F: FnMut(&Self) -> bool,
    {
        if should_stop(self) {
            return PropagateOutcome::Interrupted;
        }

        // EVENT-DRIVEN FIXPOINT (P2d). Historically this drive opened with a
        // full `propagate_from(0)` scan over EVERY constraint on EVERY call —
        // once per decision in the search loop — because the event machinery
        // was incomplete: watch notification kept only the first propagation
        // per event, and several state transitions (unwatched falsifications
        // on blind rows, backtrack un-falsifications, constraints added
        // mid-search) produced no event at all. The propagator now closes
        // each of those gaps — a pending-check queue records every
        // propagating/conflicting constraint seen during notification
        // (`queue_pending_check`), unassignment re-queues watchers whose
        // tight slack may re-enable propagations, blind rows (cached watched
        // slack below `max_watched_coeff`) are armed to watch every literal
        // (`arm_watch_all_if_blind`), and newly added constraints queue
        // themselves — so after ONE successful full scan (per
        // construction/rebuild, `needs_full_scan`) draining the queue reaches
        // the same fixpoint the scan did. Conflicts abort a notification pass
        // early, but every literal falsified at the conflicting level is
        // unassigned by the ensuing backtrack, so no state is lost across
        // conflicts. Debug builds verify the equivalence with a full-scan
        // oracle on every event-driven `Ok` return below.
        let scan_needed = self.propagator.needs_full_scan();
        let scan_token = self.propagator.full_scan_token();
        let mut scan_cursor = 0usize;
        let mut origin = PropagationOrigin::Scan;
        let mut result = if scan_needed {
            self.propagator.propagate_from(scan_cursor)
        } else {
            scan_cursor = self.propagator.num_constraints();
            PropResult::Ok
        };

        loop {
            match result {
                PropResult::Ok => {
                    if origin == PropagationOrigin::Scan {
                        scan_cursor = self.propagator.num_constraints();
                    }
                    if let Some(cid) = self.propagator.pop_pending_check() {
                        origin = PropagationOrigin::SourceRecheck;
                        result = self.propagator.propagate_constraint(cid);
                        continue;
                    }
                    if scan_needed && scan_cursor < self.propagator.num_constraints() {
                        origin = PropagationOrigin::Scan;
                        result = self.propagator.propagate_from(scan_cursor);
                        continue;
                    }
                    if scan_needed {
                        // The full scan completed and the queue drained with no
                        // outstanding propagation: event-driven propagation is
                        // sufficient from here until the next full rebuild.
                        self.propagator.mark_full_scan_complete(scan_token);
                    } else {
                        // Debug-build fixpoint oracle: the event-driven drain
                        // must reach exactly the fixpoint the historical full
                        // scan reached. Any queued/armed completeness gap in
                        // the propagator surfaces here instead of as a subtle
                        // search-quality regression.
                        #[cfg(debug_assertions)]
                        {
                            let diff = self.propagator.propagate_from(0);
                            debug_assert!(
                                matches!(diff, PropResult::Ok),
                                "event-driven propagate_all fixpoint incomplete: \
                                 {diff:?} at level {}",
                                self.decision_level
                            );
                        }
                    }
                    return PropagateOutcome::Ok;
                }
                PropResult::Interrupted => return PropagateOutcome::Interrupted,
                PropResult::Conflict(_, cid) => return PropagateOutcome::Conflict(cid),
                PropResult::Propagated(lit, _, cid) => {
                    self.stats.propagations += 1;
                    if origin == PropagationOrigin::Scan {
                        scan_cursor = cid.saturating_add(1);
                    }
                    self.propagator.queue_pending_check(cid);
                    result = self.assign(lit, Some(cid));
                    if matches!(result, PropResult::Ok) {
                        if should_stop(self) {
                            return PropagateOutcome::Interrupted;
                        }
                    }
                    origin = PropagationOrigin::Event;
                }
            }
        }
    }

    fn propagate_all_interruptible<F>(&mut self, should_stop: &mut F) -> PropagateOutcome
    where
        F: FnMut() -> bool,
    {
        if self.interrupted || should_stop() {
            return PropagateOutcome::Interrupted;
        }

        // EVENT-DRIVEN FIXPOINT (P2d): see `propagate_all`. The full scan runs
        // only until it first reaches a fixpoint (per construction/rebuild);
        // afterwards the propagator's pending-check queue alone is drained.
        let scan_needed = self.propagator.needs_full_scan();
        let scan_token = self.propagator.full_scan_token();
        let mut scan_cursor = 0usize;
        let mut origin = PropagationOrigin::Scan;
        // Deadline-poll throttle. `should_stop()` reads the wall clock
        // (`Instant::now` -> `mach_absolute_time`), which profiling showed was
        // ~10% of total runtime on propagation-heavy instances when invoked
        // once per propagated literal here. The cheap `self.interrupted` flag
        // is still checked every iteration, and the inner scan/assign already
        // poll `should_stop` on their own `STOP_POLL_INTERVAL` budgets, so the
        // deadline is still honored within microseconds; only the redundant
        // per-literal clock read is amortized. Results are bit-identical.
        let mut deadline_poll_countdown = DEADLINE_POLL_STRIDE;
        let mut result = if scan_needed {
            self.propagator
                .propagate_from_interruptible(scan_cursor, &mut *should_stop)
        } else {
            scan_cursor = self.propagator.num_constraints();
            PropResult::Ok
        };

        loop {
            match result {
                PropResult::Ok => {
                    if origin == PropagationOrigin::Scan {
                        scan_cursor = self.propagator.num_constraints();
                    }
                    if let Some(cid) = self.propagator.pop_pending_check() {
                        origin = PropagationOrigin::SourceRecheck;
                        result = self
                            .propagator
                            .propagate_constraint_interruptible(cid, &mut *should_stop);
                        if matches!(result, PropResult::Interrupted) {
                            // The recheck did not complete (D2): once the full
                            // scan is done the queue is the ONLY discovery
                            // vehicle for this row's pending propagation, so
                            // dropping the popped entry here would lose it for
                            // the solver's lifetime. Re-queue before returning
                            // (idempotent via the in-pending dedup flag).
                            self.propagator.queue_pending_check(cid);
                        }
                        continue;
                    }
                    if scan_needed && scan_cursor < self.propagator.num_constraints() {
                        origin = PropagationOrigin::Scan;
                        result = self
                            .propagator
                            .propagate_from_interruptible(scan_cursor, &mut *should_stop);
                        continue;
                    }
                    if scan_needed {
                        self.propagator.mark_full_scan_complete(scan_token);
                    } else {
                        // Debug-build fixpoint oracle; see `propagate_all`.
                        #[cfg(debug_assertions)]
                        {
                            let diff = self.propagator.propagate_from(0);
                            debug_assert!(
                                matches!(diff, PropResult::Ok),
                                "event-driven propagate_all_interruptible fixpoint \
                                 incomplete: {diff:?} at level {}",
                                self.decision_level
                            );
                        }
                    }
                    return PropagateOutcome::Ok;
                }
                PropResult::Interrupted => return PropagateOutcome::Interrupted,
                PropResult::Conflict(_, cid) => return PropagateOutcome::Conflict(cid),
                PropResult::Propagated(lit, _, cid) => {
                    self.stats.propagations += 1;
                    if origin == PropagationOrigin::Scan {
                        scan_cursor = cid.saturating_add(1);
                    }
                    self.propagator.queue_pending_check(cid);
                    result = self.assign_interruptible(lit, Some(cid), should_stop);
                    if matches!(result, PropResult::Ok) {
                        if self.interrupted {
                            return PropagateOutcome::Interrupted;
                        }
                        deadline_poll_countdown -= 1;
                        if deadline_poll_countdown == 0 {
                            deadline_poll_countdown = DEADLINE_POLL_STRIDE;
                            if should_stop() {
                                return PropagateOutcome::Interrupted;
                            }
                        }
                    }
                    origin = PropagationOrigin::Event;
                }
            }
        }
    }

    fn all_assigned(&self) -> bool {
        for var in 1..=self.num_vars {
            let lit = var as Lit;
            if self.propagator.value(lit) == LitValue::Unassigned {
                return false;
            }
        }
        true
    }

    fn extract_model(&self) -> Vec<bool> {
        (1..=self.num_vars)
            .map(|var| {
                // Fixed literals from preprocessing take priority.
                if let Some(&val) = self.fixed_literals.get(&var) {
                    return val;
                }
                self.propagator.value(var as Lit) == LitValue::True
            })
            .collect()
    }

    fn pick_decision_literal(&mut self) -> Lit {
        // VSIDS heap: pop variables until we find one that's unassigned.
        // Variables already assigned (by propagation) are skipped and not
        // re-inserted; they will be re-inserted on backtrack.
        loop {
            if let Some(var) = self.vsids_heap.pop_max(&self.activity) {
                let lit = var as Lit;
                if self.propagator.value(lit) != LitValue::Unassigned {
                    continue;
                }
                // Phase saving: use the saved polarity for this variable.
                return if self.saved_phase[var as usize] {
                    var as Lit
                } else {
                    -(var as Lit)
                };
            }
            // Fallback: find any unassigned variable (should not normally reach).
            for var in 1..=self.num_vars {
                if self.propagator.value(var as Lit) == LitValue::Unassigned {
                    return var as Lit;
                }
            }
            return 1; // Should not reach here if all_assigned() was false.
        }
    }

    /// Extracts a SOUND assumption core from a level-0..=`assumption_boundary`
    /// conflict by walking the implication graph back to the assumption decisions
    /// that forced it (the classic MiniSat `analyzeFinal`).
    ///
    /// Returns the subset of `active_assumptions` whose assignment participated in
    /// the conflict. The result is a genuine UNSAT core: re-asserting exactly these
    /// assumptions reproduces the same propagation chain to the same conflict.
    /// Falls back to the full `active_assumptions` set (always sound, just larger)
    /// if anything cannot be resolved cleanly, so this never produces an unsound
    /// (too-small) core.
    ///
    /// This is the quality lever for native core-guided optimization: a tight core
    /// keeps the OLL totalizer relaxations small and the lower bound climbing fast.
    fn extract_assumption_conflict_core(
        &self,
        conflict_cid: usize,
        active_assumptions: &[PbLit],
    ) -> Vec<PbLit> {
        let full = || active_assumptions.to_vec();

        let Some(conflict) = self.propagator.get_constraint_pb(conflict_cid) else {
            return full();
        };

        // Map assumption variable -> the assumption literal, for fast membership.
        let mut assumption_by_var: HashMap<u32, PbLit> = HashMap::new();
        for &assumption in active_assumptions {
            assumption_by_var.insert(assumption.var, assumption);
        }

        // `seen` marks variables already pulled into the analysis. `core` collects
        // assumption literals found on the conflict side.
        let mut seen: HashSet<u32> = HashSet::new();
        let mut core_vars: HashSet<u32> = HashSet::new();
        let mut core: Vec<PbLit> = Vec::new();

        // Seed: every FALSE literal of the conflict constraint participates.
        let mut frontier: Vec<u32> = Vec::new();
        for term in &conflict.terms {
            let [lit] = term.lits.as_slice() else {
                return full();
            };
            let dimacs = pb_lit_to_dimacs(*lit);
            if self.propagator.value(dimacs) == LitValue::False && seen.insert(lit.var) {
                frontier.push(lit.var);
            }
        }

        // Resolve back through the trail (newest first), expanding reasons of
        // non-assumption propagations and collecting assumption decisions.
        for entry in self.trail.iter().rev() {
            if frontier.is_empty() {
                break;
            }
            let var = entry.lit.unsigned_abs();
            if !seen.contains(&var) {
                continue;
            }
            // This trail variable is part of the conflict cone. Remove it from the
            // frontier bookkeeping (it is being processed now).
            if let Some(pos) = frontier.iter().position(|&v| v == var) {
                frontier.swap_remove(pos);
            }

            match entry.reason {
                None => {
                    // A decision. If it is an assumption, record it in the core.
                    if let Some(&assumption) = assumption_by_var.get(&var) {
                        if core_vars.insert(var) {
                            core.push(assumption);
                        }
                    }
                    // Non-assumption decisions cannot occur at or below the
                    // assumption boundary; if one appears, fail safe to the full
                    // core (sound, just larger).
                    else if entry.level > 0 {
                        return full();
                    }
                }
                Some(reason_cid) => {
                    let Some(reason) = self.propagator.get_constraint_pb(reason_cid) else {
                        return full();
                    };
                    for term in &reason.terms {
                        let [lit] = term.lits.as_slice() else {
                            return full();
                        };
                        // Pull in the other falsified literals of the reason that
                        // are not already seen (the propagated literal itself is
                        // true, so it is skipped by the False check).
                        let dimacs = pb_lit_to_dimacs(*lit);
                        if self.propagator.value(dimacs) == LitValue::False && seen.insert(lit.var)
                        {
                            frontier.push(lit.var);
                        }
                    }
                }
            }
        }

        if core.is_empty() {
            // Could not localize the core; fall back to the full set.
            return full();
        }
        core
    }

    fn analyze_conflict_with_stop<S>(
        &mut self,
        conflict_cid: usize,
        should_stop: &mut S,
    ) -> ConflictAnalysisOutcome
    where
        S: ConflictStop,
    {
        // Fast path: when proof logging is OFF, run the allocation-free
        // DenseCp-based conflict analysis. This reuses solver-owned dense
        // buffers across conflicts (no per-conflict allocation), avoids the
        // per-step `CpConstraint` clone and per-reason `BTreeMap` rebuild, and
        // uses O(1) var-indexed level lookups for the falsified-literal counts.
        //
        // The dense path uses the PROVEN round-to-one (Elffers & Nordstrom,
        // IJCAI-18; RoundingSat/Exact): it reduces the reason before adding,
        // producing stronger/smaller learned constraints than this heuristic
        // (add-then-divide) `CpConstraint` path. Its soundness is enforced by
        // always-on debug invariants (the running and final conflict must remain
        // falsified — RoundingSat slack < 0 — and the final lemma must be
        // asserting) and the exhaustive `proven_round_to_one_semantic_entailment`
        // property test (C ∧ R ⊨ C' over all assignments). On invalid pivot or
        // arithmetic overflow it falls back to the sound heuristic round-to-one.
        if self.proof_writer.is_none() {
            return self.analyze_conflict_dense(conflict_cid, should_stop);
        }

        let Some(mut learned) = self.cp_constraint_by_index(conflict_cid) else {
            return ConflictAnalysisOutcome::Learned((0, None));
        };

        // The conflict constraint participated in this conflict: bump it if it is
        // a learned lemma (no-op for original constraints / when opt-in is off).
        self.bump_learned_activity(conflict_cid);

        self.last_analysis_proof_id = None;
        if should_stop.should_stop(self) {
            return ConflictAnalysisOutcome::Interrupted;
        }

        // Track the current proof constraint ID through the analysis chain.
        let mut current_proof_id = self.proof_id_for_constraint(conflict_cid);

        // Log initial saturation of the conflict constraint.
        learned.saturate();
        if let Some(pid) = current_proof_id {
            current_proof_id = self.log_proof_step(ProofStep::Saturate(pid));
        }

        // Collect trail entries to iterate over (avoids borrow conflict with &mut self).
        let trail_snapshot: Vec<(Lit, Option<usize>)> = self
            .trail
            .iter()
            .rev()
            .map(|entry| (entry.lit, entry.reason))
            .collect();

        for (trail_lit, reason_opt) in &trail_snapshot {
            if should_stop.should_stop(self) {
                return ConflictAnalysisOutcome::Interrupted;
            }

            if self.count_current_level_falsified_literals(&learned) <= 1 {
                break;
            }

            let falsified_lit = dimacs_to_pb_lit(-*trail_lit);
            if learned.coefficient(falsified_lit) == 0 {
                continue;
            }

            let Some(reason_cid) = reason_opt else {
                continue;
            };
            let Some(reason) = self.cp_constraint_by_index(*reason_cid) else {
                continue;
            };

            // This reason is about to be resolved into the learned constraint:
            // bump it if it is a learned lemma (no-op for original constraints /
            // when opt-in is off), and refresh its LBD (kept only if improved).
            self.bump_learned_activity(*reason_cid);
            self.refresh_learned_lbd_on_reason_use(*reason_cid);

            let reason_proof_id = self.proof_id_for_constraint(*reason_cid);

            let pivot = dimacs_to_pb_lit(*trail_lit);

            // Identify the asserting literal candidate: the unique literal at
            // the current decision level (excluding the pivot we are about to
            // resolve). This is used by round-to-one to decide whether to
            // apply the division rule.
            let asserting_candidate = self.asserting_candidate_after_resolve(&learned, pivot);

            let resolved = self.resolve_round_to_one_with_proof(
                &learned,
                &reason,
                pivot,
                asserting_candidate,
                current_proof_id,
                reason_proof_id,
            );
            let Some((resolved_constraint, resolved_proof_id, used_division)) = resolved else {
                continue;
            };

            if used_division {
                self.stats.round_to_one_count += 1;
            } else {
                self.stats.round_to_one_fallback_count += 1;
            }

            learned = resolved_constraint;
            current_proof_id = resolved_proof_id;
        }

        if should_stop.should_stop(self) {
            return ConflictAnalysisOutcome::Interrupted;
        }

        // Snapshot before strengthening for stats tracking.
        let pre_strengthen_size = learned.coefficients().len();
        let pre_strengthen_degree = learned.degree();

        // Full strengthening pipeline: saturation + GCD + conservative weakening.
        //
        // Step 1: Saturation + GCD (logged for proof).
        let gcd = learned
            .coefficients()
            .values()
            .copied()
            .fold(0i128, gcd_i64);
        learned.saturate();
        if let Some(pid) = current_proof_id {
            current_proof_id = self.log_proof_step(ProofStep::Saturate(pid));
        }
        learned
            .gcd_divide()
            .expect("final learned PB constraint must support GCD division");
        if gcd > 1 {
            if let Some(pid) = current_proof_id {
                current_proof_id = self.log_proof_step(ProofStep::Divide(pid, gcd));
            }
        }

        if should_stop.should_stop(self) {
            return ConflictAnalysisOutcome::Interrupted;
        }

        // Step 2: Conservative weakening — remove literals with small coefficients
        // while preserving the asserting property.
        let asserting_lit = self.unique_current_level_falsified_literal(&learned);

        // Build a snapshot of the trail levels for the weakening callback.
        // We need this because weaken_conservative takes a closure that checks
        // falsified literal levels, and we can't borrow self inside it.
        // KEYED, NOT SCANNED. Both snapshots used to be `Vec`s that the closure
        // searched linearly on every call, which is the `(n + |trail|)` factor in
        // the `O(n^2 * (n + |trail|))` conflict-analysis stall this call site was
        // measured causing (see `CpConstraint::weaken_conservative`). The maps
        // answer the same questions with the same answers in O(log n).
        //
        // `trail_levels` was searched with `.rev().find(..)`, i.e. LAST entry
        // wins; inserting in forward trail order and letting later entries
        // overwrite reproduces that exactly.
        let mut trail_levels: std::collections::BTreeMap<u32, u32> =
            std::collections::BTreeMap::new();
        for entry in self.trail.iter() {
            trail_levels.insert(entry.lit.unsigned_abs(), entry.level);
        }
        let propagator_snapshot: std::collections::BTreeMap<PbLit, bool> = learned
            .coefficients()
            .keys()
            .map(|&lit| {
                let dimacs = pb_lit_to_dimacs(lit);
                let is_false = self.propagator.value(dimacs) == LitValue::False;
                (lit, is_false)
            })
            .collect();

        learned.weaken_conservative(asserting_lit, |lit| {
            // Check if this literal is falsified and return its decision level.
            let is_false = propagator_snapshot.get(&lit).copied().unwrap_or(false);
            if !is_false {
                return None;
            }
            // Find the decision level of the variable in the trail.
            trail_levels.get(&lit.var).copied()
        });

        if should_stop.should_stop(self) {
            return ConflictAnalysisOutcome::Interrupted;
        }

        // Step 3: Re-saturate and GCD after weakening (may create new opportunities).
        learned.saturate();
        learned
            .gcd_divide()
            .expect("post-weakening GCD division must succeed");

        if should_stop.should_stop(self) {
            return ConflictAnalysisOutcome::Interrupted;
        }

        // Track strengthening effectiveness.
        if learned.coefficients().len() < pre_strengthen_size
            || learned.degree() < pre_strengthen_degree
        {
            self.stats.strengthened += 1;
        }

        // Store the final proof ID for the learned constraint so the RUP step
        // in add_learned_constraint can reference it.
        self.last_analysis_proof_id = current_proof_id;

        for (lit, coeff) in learned.coefficients() {
            self.bump_activity_weighted(lit.var, *coeff);
        }
        self.decay_activity();
        self.decay_learned_activity();

        let backtrack_level = self
            .unique_current_level_falsified_literal(&learned)
            .map_or(0, |al| self.backtrack_level_for_constraint(&learned, al));

        ConflictAnalysisOutcome::Learned((backtrack_level, Some(PbConstraint::from(&learned))))
    }

    /// Returns the VeriPB proof constraint ID for an internal constraint index.
    fn proof_id_for_constraint(&self, constraint_index: usize) -> Option<ConstraintId> {
        if self.proof_writer.is_none() && self.proof_tap.is_none() {
            return None;
        }
        self.constraint_ids.get(constraint_index).copied()
    }

    fn count_current_level_falsified_literals(&self, constraint: &CpConstraint) -> usize {
        constraint
            .coefficients()
            .keys()
            .copied()
            .filter(|&lit| self.false_literal_level(lit) == Some(self.decision_level))
            .count()
    }

    fn unique_current_level_falsified_literal(&self, constraint: &CpConstraint) -> Option<PbLit> {
        let mut asserting_lit = None;

        for lit in constraint.coefficients().keys().copied() {
            if self.false_literal_level(lit) != Some(self.decision_level) {
                continue;
            }

            if asserting_lit.is_some() {
                return None;
            }
            asserting_lit = Some(lit);
        }

        asserting_lit
    }

    fn false_literal_level(&self, lit: PbLit) -> Option<u32> {
        if self.propagator.value(pb_lit_to_dimacs(lit)) != LitValue::False {
            return None;
        }

        self.level_of_var(lit.var)
    }

    fn level_of_var(&self, var: u32) -> Option<u32> {
        self.trail
            .iter()
            .rev()
            .find(|entry| entry.lit.unsigned_abs() == var)
            .map(|entry| entry.level)
            .or_else(|| self.fixed_literals.contains_key(&var).then_some(0))
    }

    fn backtrack_level_for_constraint(
        &self,
        constraint: &CpConstraint,
        asserting_lit: PbLit,
    ) -> u32 {
        constraint
            .coefficients()
            .keys()
            .copied()
            .filter(|&lit| lit != asserting_lit)
            .filter_map(|lit| self.level_of_var(lit.var))
            .filter(|&level| level < self.decision_level)
            .max()
            .unwrap_or(0)
    }

    fn add_learned_constraint(&mut self, constraint: PbConstraint) {
        let lbd = self.compute_lbd(&constraint);

        self.update_lbd_averages(lbd);

        // Use the proof ID from the CP derivation chain if available,
        // otherwise fall back to emitting a RUP step. Under the proof tap the
        // RUP fallback pushes STRUCTURED terms so the constraint formatting
        // happens on the serializer thread, not here.
        let proof_id = if let Some(analysis_pid) = self.last_analysis_proof_id.take() {
            Some(analysis_pid)
        } else if self.proof_tap.is_some() {
            if self.suppress_optimization_intermediate_proof_steps {
                None
            } else {
                self.tap_log_rup_constraint(&constraint)
            }
        } else if let Some(formatted) = format_pb_constraint(&constraint) {
            self.log_proof_step(ProofStep::Rup(formatted))
        } else {
            None
        };

        if let Some(pid) = proof_id {
            self.record_learned_constraint_id(pid);
        }

        let start = self.propagator.num_constraints();
        self.propagator.add_from_pb_constraint(&constraint);
        let end = self.propagator.num_constraints();

        for cid in start..end {
            let learned_constraint = self
                .propagator
                .get_constraint_pb(cid)
                .expect("freshly learned PB constraint must be addressable");
            self.learned_constraints.push(learned_constraint);
            self.learned_lbd.push(lbd);
            self.learned_active.push(true);
            self.learned_permanent.push(false);
            // Seed the activity with the current increment: a freshly learned
            // constraint just participated in a conflict, so it starts "warm"
            // (MiniSat/Glucose bump-on-creation) rather than as the worst lemma.
            // Kept in lockstep unconditionally; only consulted when the opt-in
            // activity heuristic is enabled.
            self.learned_activity.push(self.learned_constraint_inc);
            self.stats.learned += 1;
        }
        self.debug_assert_constraint_arrays_in_lockstep();
    }

    /// Debug-only invariant: every per-variable array stays sized in lockstep at
    /// `num_vars + 1` (index 0 unused, `1..=num_vars` live), and the parallel
    /// learned-constraint bookkeeping arrays stay equal length. Cheap O(1) checks
    /// guarding the runtime var-pool against silent array desynchronization.
    #[inline]
    fn debug_assert_var_arrays_in_lockstep(&self) {
        debug_assert_eq!(
            self.activity.len(),
            self.num_vars as usize + 1,
            "activity array must be sized num_vars + 1"
        );
        debug_assert_eq!(
            self.saved_phase.len(),
            self.num_vars as usize + 1,
            "saved_phase array must be sized num_vars + 1"
        );
        debug_assert_eq!(
            self.vsids_heap.position.len(),
            self.num_vars as usize + 1,
            "vsids_heap.position must be sized num_vars + 1"
        );
    }

    #[inline]
    fn debug_assert_constraint_arrays_in_lockstep(&self) {
        debug_assert_eq!(
            self.learned_constraints.len(),
            self.learned_lbd.len(),
            "learned_constraints and learned_lbd must stay in lockstep"
        );
        debug_assert_eq!(
            self.learned_constraints.len(),
            self.learned_active.len(),
            "learned_constraints and learned_active must stay in lockstep"
        );
        debug_assert_eq!(
            self.learned_constraints.len(),
            self.learned_permanent.len(),
            "learned_constraints and learned_permanent must stay in lockstep"
        );
        debug_assert_eq!(
            self.learned_constraints.len(),
            self.learned_activity.len(),
            "learned_constraints and learned_activity must stay in lockstep"
        );
    }

    /// Allocates a fresh runtime variable, growing every per-variable structure
    /// consistently, and returns its 1-based variable number.
    ///
    /// # Soundness
    /// The new variable is appended at index `num_vars + 1`; no existing index is
    /// touched, so no prior assignment, activity, phase, watch, or trail entry is
    /// invalidated. The variable starts fully unconstrained (no constraint
    /// references it yet) and unassigned, exactly as a genuine free variable. All
    /// per-variable arrays (`activity`, `saved_phase`, the VSIDS heap position
    /// table) are grown by one slot; the propagator's dense assignment and watch
    /// arrays grow lazily when the first constraint over the variable is added
    /// (and unconditionally here, so `value()`/watch lookups are always in range);
    /// the dense conflict-analysis buffers self-grow on first touch. The variable
    /// is inserted into the VSIDS heap so it can be selected for decisions.
    ///
    /// Returns `None` only on `u32` overflow of the variable counter (never
    /// silently corrupting state).
    #[must_use]
    pub fn new_var(&mut self) -> Option<u32> {
        let new_var = self.num_vars.checked_add(1)?;
        // Bound the variable to the DIMACS literal range used throughout the
        // propagator and assumption machinery (`pb_lit_to_dimacs` etc.).
        if new_var > i32::MAX as u32 {
            return None;
        }

        // Grow per-variable solver arrays by exactly one slot each. Pushing keeps
        // every existing index byte-for-byte identical.
        self.activity.push(0.0);
        self.saved_phase.push(false);
        // Grow the VSIDS position table to cover the new variable, then insert it.
        self.vsids_heap.position.push(0);
        self.num_vars = new_var;
        self.vsids_heap.insert(new_var, &self.activity);

        // Ensure the propagator's dense assignment + watch arrays cover the new
        // variable so `value()`/`assign_literal()` never read out of range even
        // before any constraint references it.
        self.propagator.ensure_var_capacity(new_var);

        self.debug_assert_var_arrays_in_lockstep();
        Some(new_var)
    }

    /// Adds a pseudo-Boolean constraint to the live solver as a PERMANENT
    /// constraint and propagates any forced literals at decision level 0.
    ///
    /// This is the incremental counterpart to constructor-time loading. It is the
    /// engine behind incremental core-guided (OLL) relaxation: the optimizer
    /// builds a cardinality relaxation over a core, then registers it here without
    /// rebuilding the solver.
    ///
    /// # Preconditions / behaviour
    /// - Must be called at decision level 0 (the OLL loop is always there between
    ///   assumption queries). Asserted in debug builds; if violated in release the
    ///   call fails closed with `RuntimeConstraintOutcome::Unsupported`.
    /// - All literals must reference live variables (`1..=num_vars`); allocate any
    ///   fresh auxiliaries with [`PbCdclSolver::new_var`] first.
    /// - Proof logging must be OFF (this is the no-proof incremental path).
    ///
    /// # Soundness
    /// - The constraint is appended to the propagator's learned region but flagged
    ///   permanent, so the original-constraint index window `0..constraints.len()`
    ///   is never disturbed and `reduce_db` never deletes it. Its watched-slack
    ///   state is initialized by the same tested propagator import path used for
    ///   every other constraint, preserving the watched-slack invariant.
    /// - After import we run unit propagation at level 0; a level-0 conflict means
    ///   the constraint set is now UNSAT, reported as `Conflict`.
    /// - Adding an implied constraint cannot remove any model; adding a generally
    ///   sound constraint (e.g. a totalizer relaxation, which is implied by its
    ///   counting clauses) only restricts to an equisatisfiable-on-original-vars
    ///   set. The caller is responsible for only adding implied/relaxation
    ///   constraints; the optimizer's final answer is independently re-verified by
    ///   `verify_optimum` against the ORIGINAL constraints, so even a hypothetical
    ///   bad relaxation cannot yield a false optimum.
    pub fn add_constraint_runtime(
        &mut self,
        constraint: &PbConstraint,
    ) -> RuntimeConstraintOutcome {
        if self.proof_writer.is_some() || self.proof_tap.is_some() {
            return RuntimeConstraintOutcome::Unsupported;
        }
        debug_assert_eq!(
            self.decision_level, 0,
            "add_constraint_runtime must be called at decision level 0"
        );
        if self.decision_level != 0 {
            return RuntimeConstraintOutcome::Unsupported;
        }
        // Every referenced variable must already be live.
        for term in &constraint.terms {
            for lit in &term.lits {
                if lit.var == 0 || lit.var > self.num_vars {
                    return RuntimeConstraintOutcome::Unsupported;
                }
            }
        }

        let start = self.propagator.num_constraints();
        // `add_from_pb_constraint` returns None when the constraint is trivially
        // satisfied (degree <= 0 after normalization); then there is nothing to
        // track or propagate.
        if self.propagator.add_from_pb_constraint(constraint).is_none()
            && self.propagator.num_constraints() == start
        {
            return RuntimeConstraintOutcome::Added;
        }
        let end = self.propagator.num_constraints();

        for cid in start..end {
            let Some(stored) = self.propagator.get_constraint_pb(cid) else {
                // Should never happen for a freshly added constraint; fail closed.
                return RuntimeConstraintOutcome::Unsupported;
            };
            self.learned_constraints.push(stored);
            // LBD 1 + permanent flag keeps it off every reduce_db deletion path.
            self.learned_lbd.push(1);
            self.learned_active.push(true);
            self.learned_permanent.push(true);
            // Lockstep with `learned_constraints`; permanent constraints are
            // never deleted so the value is bookkeeping only.
            self.learned_activity.push(self.learned_constraint_inc);
        }
        self.debug_assert_constraint_arrays_in_lockstep();

        // Propagate any level-0 implications introduced by the new constraint.
        let mut never_stop = |_: &Self| false;
        match self.propagate_all(&mut never_stop) {
            PropagateOutcome::Ok => RuntimeConstraintOutcome::Added,
            PropagateOutcome::Conflict(_) => RuntimeConstraintOutcome::Conflict,
            PropagateOutcome::Interrupted => RuntimeConstraintOutcome::Unsupported,
        }
    }

    /// Adds a unit-coefficient cardinality constraint `sum(lits) >= rhs` to the
    /// live solver as a permanent constraint, propagating at level 0.
    ///
    /// Thin wrapper over [`PbCdclSolver::add_constraint_runtime`] that builds the
    /// `PbConstraint`. Used by the native OLL loop to register relaxation clauses
    /// (`sum >= 1`) emitted by the tested totalizer encoder.
    pub fn add_cardinality_runtime(
        &mut self,
        lits: &[PbLit],
        rhs: i128,
    ) -> RuntimeConstraintOutcome {
        let terms = lits
            .iter()
            .map(|&lit| PbTerm {
                coeff: 1,
                lits: vec![lit],
            })
            .collect();
        let constraint = PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs,
        };
        self.add_constraint_runtime(&constraint)
    }
}

/// Outcome of propagation to fixpoint.
enum PropagateOutcome {
    Ok,
    /// Conflict with the originating internal constraint index.
    Conflict(usize),
    Interrupted,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PropagationOrigin {
    Scan,
    SourceRecheck,
    Event,
}

enum AssumptionPreparation {
    Ready(Vec<PbLit>),
    Contradiction(Vec<PbLit>),
    Unsupported,
}

enum ApplyAssumptionsOutcome {
    Ok(u32),
    Unsat(Vec<PbLit>),
    Interrupted,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RootProbeOutcome {
    Ok,
    Unsat,
    Interrupted,
}

/// Outcome of [`PbCdclSolver::implied_literals_at_root`]: a cheap, side-effect-free
/// (state-restoring) "what does assuming this literal force" query.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ImpliedLiteralsOutcome {
    /// Assuming the literal at the root unit-propagated without conflict. The
    /// vector holds every literal forced true by the assumption (the assumption
    /// itself first, then its unit-propagation consequences), in trail order.
    /// Each is a sound logical consequence of `(hard constraints) AND assumption`.
    Implied(Vec<PbLit>),
    /// The assumption alone conflicts at the root: NO feasible assignment can set
    /// it true. Equivalently, the complement of the assumption is a forced fact.
    Conflict,
    /// The query could not run to completion (interruption, decision level was not
    /// 0, proof logging is active, or the literal is out of range). The caller
    /// must treat this as "no information" — never as a conflict or an implication.
    Unavailable,
}

enum ConflictAnalysisOutcome {
    Learned((u32, Option<PbConstraint>)),
    Interrupted,
}

enum PhaseCompletionOutcome {
    Model(Vec<bool>),
    Conflict,
    Invalid,
    Interrupted,
    Skipped,
}

trait ConflictStop {
    fn should_stop(&mut self, solver: &PbCdclSolver) -> bool;
}

impl<F> ConflictStop for F
where
    F: FnMut(&PbCdclSolver) -> bool,
{
    fn should_stop(&mut self, solver: &PbCdclSolver) -> bool {
        self(solver)
    }
}

struct InterruptOnlyStop<'a, F> {
    inner: &'a mut F,
}

impl<F> ConflictStop for InterruptOnlyStop<'_, F>
where
    F: FnMut() -> bool,
{
    fn should_stop(&mut self, solver: &PbCdclSolver) -> bool {
        solver.interrupted || (self.inner)()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SatProofMode {
    Conclude,
    Suppress,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum UnsatProofMode {
    Conclude,
    DeriveOnly,
}

#[allow(dead_code)]
struct SingleLitObjectiveProbe {
    assumptions: Vec<PbLit>,
    contribution_by_assumption: HashMap<PbLit, i128>,
}

impl SingleLitObjectiveProbe {
    #[allow(dead_code)]
    fn bound_for_core(&self, core: &[PbLit]) -> Option<PbCdclOptimizationCoreBound> {
        let mut lower_bound: Option<i128> = None;
        let mut seen = HashSet::new();
        let mut weighted_core = Vec::with_capacity(core.len());

        for assumption in core {
            if !seen.insert(*assumption) {
                return None;
            }
            let &contribution = self.contribution_by_assumption.get(assumption)?;
            weighted_core.push(PbCdclOptimizationCoreWeightedAssumption {
                assumption: *assumption,
                objective_lit: complement_pb_lit(*assumption),
                contribution,
            });
            lower_bound = Some(match lower_bound {
                Some(current) => current.min(contribution),
                None => contribution,
            });
        }
        sort_weighted_core_for_optimizer(&mut weighted_core);

        Some(PbCdclOptimizationCoreBound {
            lower_bound: lower_bound?,
            weighted_core,
        })
    }

    #[allow(dead_code)]
    fn lower_bound_for_core(&self, core: &[PbLit]) -> Option<i128> {
        self.bound_for_core(core).map(|bound| bound.lower_bound)
    }
}

#[allow(dead_code)]
fn build_single_lit_objective_probe(
    objective: &PbObjective,
) -> Result<SingleLitObjectiveProbe, PbCdclOptimizationCoreUnsupportedReason> {
    let mut assumptions = Vec::new();
    let mut contribution_by_assumption = HashMap::new();

    for term in &objective.terms {
        if term.lits.len() != 1 {
            return Err(PbCdclOptimizationCoreUnsupportedReason::NonSingleLiteralTerm);
        }
        if term.coeff < 0 {
            return Err(PbCdclOptimizationCoreUnsupportedReason::NegativeCoefficient);
        }
        if term.coeff == 0 {
            continue;
        }

        let objective_lit = term.lits[0];
        let assumption = complement_pb_lit(objective_lit);
        let contribution = contribution_by_assumption
            .entry(assumption)
            .or_insert_with(|| {
                assumptions.push(assumption);
                0i128
            });
        *contribution = (*contribution)
            .checked_add(term.coeff)
            .ok_or(PbCdclOptimizationCoreUnsupportedReason::WeightOverflow)?;
    }

    if assumptions.is_empty() {
        return Err(PbCdclOptimizationCoreUnsupportedReason::EmptyObjective);
    }

    Ok(SingleLitObjectiveProbe {
        assumptions,
        contribution_by_assumption,
    })
}

#[allow(dead_code)]
fn sort_weighted_core_for_optimizer(
    weighted_core: &mut [PbCdclOptimizationCoreWeightedAssumption],
) {
    weighted_core.sort_by_key(|entry| {
        (
            entry.objective_lit.var,
            entry.objective_lit.negated,
            entry.assumption.var,
            entry.assumption.negated,
            entry.contribution,
        )
    });
}

#[allow(dead_code)]
fn stable_core_summary_mix(fingerprint: u64, value: u64) -> u64 {
    fingerprint.wrapping_mul(0x100000001b3) ^ value
}

#[allow(dead_code)]
fn complement_pb_lit(lit: PbLit) -> PbLit {
    PbLit {
        var: lit.var,
        negated: !lit.negated,
    }
}

fn eval_pb_lit_on_model(lit: PbLit, model: &[bool]) -> bool {
    let value = lit
        .var
        .checked_sub(1)
        .and_then(|idx| usize::try_from(idx).ok())
        .and_then(|idx| model.get(idx))
        .copied()
        .unwrap_or(false);

    if lit.negated {
        !value
    } else {
        value
    }
}

/// Converts a DIMACS literal to a PbLit.
fn dimacs_to_pb_lit(lit: Lit) -> PbLit {
    PbLit {
        var: lit.unsigned_abs(),
        negated: lit < 0,
    }
}

/// Converts a PbLit to a DIMACS literal.
fn pb_lit_to_dimacs(lit: PbLit) -> Lit {
    let var = i32::try_from(lit.var).expect("PbLit variable must fit in i32 for DIMACS encoding");
    if lit.negated {
        -var
    } else {
        var
    }
}

/// Builds the round-to-one resolvent of `learned` and `reason` on `pivot` into
/// `scratch` (cleared first), saturated, mirroring the build phase of
/// [`PbCdclSolver::resolve_round_to_one_with_proof`]. Returns `None` when the
/// pivot is absent in the expected polarity or arithmetic overflows (in which
/// case `scratch` holds the plain-resolve fallback on success).
///
/// Free function (not a method) so the caller can pass the three disjoint
/// `self` field borrows directly, satisfying the borrow checker.
fn dense_build_resolvent(
    scratch: &mut DenseCp,
    learned: &DenseCp,
    reason: &DenseCp,
    pivot: PbLit,
    mut capture: Option<&mut HeuristicResolveCapture>,
) -> Option<()> {
    let negated_pivot = negate_lit(pivot);

    // Determine sides: pivot_side has `pivot`, negated_side has `~pivot`.
    // `learned_is_pivot_side` tracks the orientation so the proof-tap capture
    // can normalize the factors back to the (running conflict, reason)
    // convention the serializer replays.
    let (pivot_side, negated_side, learned_is_pivot_side): (&DenseCp, &DenseCp, bool) =
        if learned.coefficient(pivot) > 0 && reason.coefficient(negated_pivot) > 0 {
            (learned, reason, true)
        } else if learned.coefficient(negated_pivot) > 0 && reason.coefficient(pivot) > 0 {
            (reason, learned, false)
        } else {
            return None;
        };

    let a = pivot_side.coefficient(pivot);
    let b = negated_side.coefficient(negated_pivot);
    let g = gcd_i64(a, b);
    let left_factor = b / g;
    let right_factor = a / g;

    // Build the resolvent: pivot_side*left_factor + negated_side*right_factor.
    // `add_scaled` performs the checked scaling and addition in one pass;
    // `normalize` then cancels the complementary pivot pair (and any other
    // complementary pairs created by resolution), reproducing the
    // `CpConstraint::new(coeffs, degree)` normalization used by the trusted
    // path. The pivot pair contributes coefficient `lcm = a/g*b` to each
    // polarity, so normalization subtracts `lcm` from the degree exactly as the
    // trusted path does.
    scratch.clear();
    let built = scratch.add_scaled(pivot_side, left_factor).is_ok()
        && scratch.add_scaled(negated_side, right_factor).is_ok()
        && scratch.normalize().is_ok();

    if !built {
        // Overflow fallback: mirror the plain-resolve path (no GCD), which is
        // strictly safer than the trusted path here (the trusted fallback uses
        // panicking multiply with the same factors and is unreachable on inputs
        // that do not overflow).
        let (pivot_factor, negated_factor) =
            dense_build_resolvent_plain(scratch, pivot_side, negated_side, pivot)?;
        if let Some(cap) = capture.as_deref_mut() {
            let (conflict_factor, reason_factor) = if learned_is_pivot_side {
                (pivot_factor, negated_factor)
            } else {
                (negated_factor, pivot_factor)
            };
            cap.conflict_factor = conflict_factor;
            cap.reason_factor = reason_factor;
            cap.div = None;
        }
        return Some(());
    }

    scratch.saturate();
    if let Some(cap) = capture {
        let (conflict_factor, reason_factor) = if learned_is_pivot_side {
            (left_factor, right_factor)
        } else {
            (right_factor, left_factor)
        };
        cap.conflict_factor = conflict_factor;
        cap.reason_factor = reason_factor;
        cap.div = None;
    }
    Some(())
}

/// Plain PB resolution into `scratch` mirroring
/// [`PbCdclSolver::resolve_cp_constraints_with_proof`] (LCM scaling, no GCD,
/// saturate). Overflow fallback for [`dense_build_resolvent`]. Returns the
/// `(pivot_factor, negated_factor)` scaling pair on success (proof-tap
/// capture needs the actual factors used).
fn dense_build_resolvent_plain(
    scratch: &mut DenseCp,
    pivot_side: &DenseCp,
    negated_side: &DenseCp,
    pivot: PbLit,
) -> Option<(i128, i128)> {
    let negated_pivot = negate_lit(pivot);
    let pivot_coeff = pivot_side.coefficient(pivot);
    let negated_coeff = negated_side.coefficient(negated_pivot);
    // CHECKED LCM: `lcm_i64` PANICS on i128 overflow. Compute it with checked
    // arithmetic so this overflow fallback FAILS CLOSED (`None`) instead of
    // panicking; the caller then resorts to the reduce-to-cardinality fallback.
    let gcd = gcd_i64(pivot_coeff, negated_coeff);
    let lcm = (pivot_coeff / gcd).checked_mul(negated_coeff)?;
    let pivot_factor = lcm / pivot_coeff;
    let negated_factor = lcm / negated_coeff;

    scratch.clear();
    scratch.add_scaled(pivot_side, pivot_factor).ok()?;
    scratch.add_scaled(negated_side, negated_factor).ok()?;
    scratch.normalize().ok()?;
    scratch.saturate();
    Some((pivot_factor, negated_factor))
}

/// Canonical comparison form for a `>=` PB constraint: terms sorted by
/// `(var, negated)` plus the degree. Retained alongside the trusted heuristic
/// reference [`PbCdclSolver::analyze_conflict_cp_reference`] for comparing two
/// learned constraints for exact equality.
#[cfg(debug_assertions)]
#[allow(dead_code)]
fn canonical_pb_terms(constraint: &PbConstraint) -> (Vec<(u32, bool, i128)>, i128) {
    let mut terms: Vec<(u32, bool, i128)> = constraint
        .terms
        .iter()
        .filter_map(|term| {
            term.lits
                .first()
                .map(|lit| (lit.var, lit.negated, term.coeff))
        })
        .collect();
    terms.sort_by_key(|&(var, negated, _)| (var, negated));
    (terms, constraint.rhs)
}

/// Whether every constraint of `instance` is linear (each term over a single
/// literal).
fn instance_rows_are_linear(instance: &PbInstance) -> bool {
    instance
        .constraints
        .iter()
        .all(|constraint| constraint.terms.iter().all(|term| term.lits.len() == 1))
}

fn build_imported_input_constraint_ids(instance: &PbInstance) -> proof::Result<Vec<ConstraintId>> {
    let mut constraint_ids = Vec::with_capacity(instance.constraints.len().saturating_mul(2));
    let mut raw_id = 1u64;

    for constraint in &instance.constraints {
        if ge_constraint_import_is_nontrivial(&constraint.terms, constraint.rhs) {
            constraint_ids.push(raw_input_constraint_id(raw_id)?);
        }
        raw_id = raw_id
            .checked_add(1)
            .ok_or(ProofError::ConstraintIdOverflow)?;

        if constraint.rel == PbRel::Eq {
            if negated_ge_constraint_import_is_nontrivial(&constraint.terms, -constraint.rhs) {
                constraint_ids.push(raw_input_constraint_id(raw_id)?);
            }
            raw_id = raw_id
                .checked_add(1)
                .ok_or(ProofError::ConstraintIdOverflow)?;
        }
    }

    Ok(constraint_ids)
}

fn raw_input_constraint_id(raw_id: u64) -> proof::Result<ConstraintId> {
    ConstraintId::new(raw_id).ok_or(ProofError::ConstraintIdOverflow)
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ObjectiveLowerBoundCutStep {
    Constraint {
        constraint_id: ConstraintId,
        multiplier: i128,
    },
    Polynomial(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ObjectiveLowerBoundCutPlan {
    steps: Vec<ObjectiveLowerBoundCutStep>,
}

/// Outcome of emitting the native objective-floor cutting-planes chain
/// (`try_log_objective_lower_bound_cut_proof`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ObjectiveFloorCutOutcome {
    /// The floor + contradiction chain was fully emitted; carries the id of
    /// the final contradiction row (floor `obj >= optimum` added to the soli
    /// row `obj <= optimum-1`), used as the `conclusion BOUNDS` lower-bound
    /// hint.
    Derived(ConstraintId),
    /// A proof step failed to emit; the error is stored and the writer nulled
    /// (fail closed), so the conclusion must not be attempted.
    EmissionFailed,
    /// The objective floor is not expressible as a positive combination of
    /// input rows (needs a rounding cut or genuine search); the caller routes
    /// to the certified OPT-LIN fallback.
    Inexpressible,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ObjectiveLowerBoundCandidate {
    coefficients: Vec<(PbLit, i128)>,
    degree: i128,
    max_multiplier: i128,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct CardinalityObjectiveLowerBoundCandidate {
    degree: i128,
    expression: String,
}

fn objective_positive_linear_coefficients(objective: &PbObjective) -> Option<HashMap<PbLit, i128>> {
    let mut coefficients = HashMap::new();

    for term in &objective.terms {
        let [lit] = term.lits.as_slice() else {
            return None;
        };
        if term.coeff <= 0 {
            return None;
        }
        let entry = coefficients.entry(*lit).or_insert(0i128);
        *entry = entry.checked_add(term.coeff)?;
    }

    (!coefficients.is_empty()).then_some(coefficients)
}

/// Combines two optional lower bounds into the tighter (larger) one. Each input
/// is independently sound (`<= IntOpt`), so their max is sound. `None` means "no
/// bound"; the max of a bound with `None` is that bound.
fn max_optional_bounds(a: Option<i128>, b: Option<i128>) -> Option<i128> {
    match (a, b) {
        (Some(a), Some(b)) => Some(a.max(b)),
        (Some(a), None) => Some(a),
        (None, Some(b)) => Some(b),
        (None, None) => None,
    }
}

/// Stride between process-memory footprint polls for the exact-rational
/// bound/certificate stop closures (see [`strided_process_memory_stop`]).
pub(crate) const FLOOR_MEMORY_STRIDE: u32 = 16;

/// Wraps a set of cheap stop predicates (term flag / deadline) with a STRIDED
/// process-memory poll for the exact-rational lower-bound and floor-certificate
/// eliminations. Those routines poll `should_stop` per pivot column, per
/// eliminated row, and every 64 bignum ops; the footprint read is far heavier
/// than the cheap predicates it is bundled with (on Linux it reads
/// `/proc/self/statm`) and a MEMLIMIT breach accrues over seconds, so the memory
/// signal is consulted only once per [`FLOOR_MEMORY_STRIDE`] polls while the
/// cheap predicates still fire every call. A `Cell` countdown keeps the wrapper
/// `Fn` (the eliminations take `&dyn Fn() -> bool`). Declining stays sound
/// (fail-closed): a real breach is caught at most `FLOOR_MEMORY_STRIDE` polls
/// later, still far inside the guard's 5% headroom. The first poll checks memory
/// immediately so a call site already over the limit declines at once.
pub(crate) fn strided_process_memory_stop<'a>(
    cheap: impl Fn() -> bool + 'a,
) -> impl Fn() -> bool + 'a {
    let countdown = std::cell::Cell::new(1u32);
    move || {
        if cheap() {
            return true;
        }
        let next = countdown.get() - 1;
        if next == 0 {
            countdown.set(FLOOR_MEMORY_STRIDE);
            ay_sys::process_memory_exceeded()
        } else {
            countdown.set(next);
            false
        }
    }
}

/// Inner-loop poll cadence (in bignum operations) for the equality-aggregation
/// elimination's two innermost coefficient loops, mirroring
/// `EQ_AFFINE_INNER_POLL` in [`crate::proof::optimum_check`]. A single dense-row
/// combination near the shape cap is up to `n+1` growing-BigRational ops, which
/// can be a multi-second poll-free window; polling every 64 ops (a free
/// power-of-two modulo) bounds it while staying negligible against the bignum
/// arithmetic. The wrapped `should_stop` strides its own memory read, so this
/// adds no extra syscalls.
const EQ_AGG_INNER_POLL: usize = 64;

/// Cost cap on the number of `=` rows fed to the Gaussian-elimination affine
/// reduction. Declining above this is always sound (we just return `None`).
const EQ_AGG_MAX_ROWS: usize = 4000;
/// Cost cap on the size of the variable universe touched by the `=` rows plus
/// the objective. Declining above this is always sound.
const EQ_AGG_MAX_VARS: usize = 6000;
// Design note (work-proxy decline for the equality-aggregation Gauss-Jordan):
// NO upfront work-proxy is used. A dimension-based cost (`rows*cells` /
// `rows^2*universe`) CANNOT separate a bignum-blowup detonator from a benign
// large aggregation: the exact-arith cost is dominated by BIT growth, not
// shape. Measured counterexample — `mult_diagcomm_opt_less_teq_nbits_15`
// (735 `=` rows over 1380 vars, `rows^2*universe ~= 7.5e8`) certifies its
// incumbent OPTIMAL in ~1 s at ~105 MiB, while the reproduced `eqagg_repro`
// (600 rows over 1202 vars, `~4.3e8` — a LOWER proxy) is the one that blows up.
// A 1e8 `rows*cells` threshold therefore declined the former (losing a real
// OPTIMUM: the whole `mult_diagcomm` family regressed, wf memguard-verify A/B)
// while ranking it costlier than the actual detonator. The correct bound is the
// runtime one already in place: the per-column / per-row / per-`EQ_AGG_INNER_POLL`
// stop poll (deadline + strided process-memory guard) sheds a genuine runaway
// mid-elimination (eqagg_repro at MEMLIMIT=1429: bounded to 415 MiB, `s UNKNOWN`
// at the 15 s deadline), and `EQ_AGG_MAX_ROWS`/`EQ_AGG_MAX_VARS` bound the dense
// matrix's shape. `equality_aggregation` feeds ONLY the optimality-termination
// floor (never the incumbent), so a poll-driven decline is always sound.

/// Emit a one-line trace of each equality-aggregation work-proxy decision
/// (rows, universe, cost, admit/decline) when `--pb-eqagg-debug` is set, so the
/// OPT-LIN A/B can confirm the new threshold sheds only the runaway shapes and
/// loses no real floor. Off by default (no cost on the hot path).
fn eqagg_debug_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| ay_core::misc_cli_flags().pb_eqagg_debug)
}

/// Folds a slice of linear single-literal `PbTerm`s into exact-rational net
/// per-variable coefficients plus a constant moved off the LHS, using the same
/// `~x = 1 - x` convention as [`crate::optimize::lp_bound::build_row`].
///
/// For a negated literal `~x` with coefficient `c`, the contribution is
/// `c*(1-x) = c - c*x`: the `-c` lands on the variable coefficient and the `+c`
/// constant is returned in `lhs_const` (to be moved to the RHS by the caller).
///
/// Returns `None` on any non-linear (multi-literal or zero-literal) term or a
/// term referencing the reserved variable index `0` — in those cases the row
/// cannot be modelled as an exact linear equality and the whole aggregation
/// must decline (which is sound).
fn fold_linear_terms(
    terms: &[PbTerm],
) -> Option<(
    std::collections::BTreeMap<u32, num_rational::BigRational>,
    num_rational::BigRational,
)> {
    use num_bigint::BigInt;
    use num_rational::BigRational;
    use num_traits::Zero;

    let mut coeffs: std::collections::BTreeMap<u32, BigRational> =
        std::collections::BTreeMap::new();
    let mut lhs_const = BigRational::zero();
    for term in terms {
        let [lit] = term.lits.as_slice() else {
            return None; // non-linear term: cannot model as an exact linear row.
        };
        if lit.var == 0 {
            return None;
        }
        let coeff = BigRational::from_integer(BigInt::from(term.coeff));
        let entry = coeffs.entry(lit.var).or_insert_with(BigRational::zero);
        if lit.negated {
            // c * (1 - x) = c - c * x.
            *entry -= &coeff;
            lhs_const += &coeff;
        } else {
            *entry += &coeff;
        }
    }
    Some((coeffs, lhs_const))
}

/// Equality-aggregation (Gaussian-elimination) affine objective reduction.
///
/// When the objective is an exact rational linear combination of the instance's
/// `=` rows, the objective is a CONSTANT on the entire feasible set: if
/// `obj_coeffs = sum_k lambda_k A_k` over the rationals (where `A_k . x = b_k`
/// are the equality rows), then for every feasible `x`
/// `obj(x) = sum_k lambda_k b_k + c0 = c`, a fixed constant independent of `x`.
///
/// This routine row-reduces the equality system to echelon form, reduces the
/// objective vector against the pivots, and — ONLY when the residual objective
/// coefficient vector is entirely zero and the leftover constant is integral —
/// returns `Some(c)`. Because the value is the EXACT objective on every feasible
/// point, `c` is simultaneously a valid lower AND upper bound; it can never
/// overshoot the true minimum, which is what the upgrade paths in
/// `portfolio.rs` and `verify_native_optimum` (which trust this bound without
/// re-deriving it) require for soundness.
///
/// Returns `None` (declines, always sound) when: there are no equality rows;
/// the cost caps are exceeded; any row/objective term is non-linear; the
/// residual is non-empty (objective is genuinely variable on the feasible set);
/// or the implied constant is non-integral.
///
/// `should_stop` is polled per pivot column, per eliminated row, AND every
/// [`EQ_AGG_INNER_POLL`] bignum ops inside the two innermost coefficient loops:
/// the exact-rational elimination has multiplicatively growing bignum entries,
/// so without an inner stop hook a single dense-row combination near the shape
/// cap can burn seconds of CPU deaf to the deadline, SIGTERM and the memory
/// guard. A stop declines (`None`), which every caller treats as "no
/// information".
fn equality_aggregation_objective_constant(
    constraints: &[PbConstraint],
    objective: &PbObjective,
    should_stop: &dyn Fn() -> bool,
) -> Option<i128> {
    use num_bigint::BigInt;
    use num_rational::BigRational;
    use num_traits::Zero;

    if objective.terms.is_empty() {
        return None;
    }

    // Collect equality rows as (net coeffs, effective rhs = rhs - lhs_const).
    let mut eq_rows: Vec<(std::collections::BTreeMap<u32, BigRational>, BigRational)> = Vec::new();
    for constraint in constraints {
        if constraint.rel != PbRel::Eq {
            continue;
        }
        let (coeffs, lhs_const) = fold_linear_terms(&constraint.terms)?;
        let rhs_eff = BigRational::from_integer(BigInt::from(constraint.rhs)) - lhs_const;
        eq_rows.push((coeffs, rhs_eff));
        if eq_rows.len() > EQ_AGG_MAX_ROWS {
            return None;
        }
    }
    if eq_rows.is_empty() {
        return None;
    }

    // Fold the objective to net per-variable coeffs and constant c0.
    let (obj_coeffs, c0) = fold_linear_terms(&objective.terms)?;

    // Build the variable universe (objective + all equality rows). The dense
    // augmented matrix has columns 0..n for variables and a final column `n`
    // for the constant. For an equality row A_k . x = b_k we store the
    // homogeneous form A_k . x - b_k = 0, so the constant column holds -b_k.
    let mut universe: std::collections::BTreeSet<u32> = std::collections::BTreeSet::new();
    universe.extend(obj_coeffs.keys().copied());
    for (coeffs, _) in &eq_rows {
        universe.extend(coeffs.keys().copied());
    }
    let n = universe.len();
    if n > EQ_AGG_MAX_VARS {
        return None;
    }
    // No upfront cost cap (see the module note above): the elimination is bounded
    // by the per-column/row/inner-op stop poll and the row/var shape caps, not a
    // dimension proxy that mis-declines benign large aggregations.
    if eqagg_debug_enabled() {
        let cells = (eq_rows.len() as u128).saturating_mul(n as u128 + 1);
        eprintln!(
            "[ay-pb eqagg] rows={} universe={} cells={} (poll-bounded, admitted)",
            eq_rows.len(),
            n,
            cells,
        );
    }
    // Poll BEFORE committing the dense matrix so a fired stop (deadline / the
    // process-memory guard) sheds the work without the up-to-`rows*(n+1)`
    // BigRational allocation.
    if should_stop() {
        return None;
    }
    let col_of: std::collections::BTreeMap<u32, usize> =
        universe.iter().enumerate().map(|(i, v)| (*v, i)).collect();

    // Dense augmented equality rows: index n holds -rhs_eff.
    let mut rows: Vec<Vec<BigRational>> = Vec::with_capacity(eq_rows.len());
    for (coeffs, rhs_eff) in &eq_rows {
        let mut row = vec![BigRational::zero(); n + 1];
        for (v, c) in coeffs {
            row[col_of[v]] = c.clone();
        }
        row[n] = -rhs_eff.clone();
        rows.push(row);
    }

    // Objective vector: index n holds +c0 (so the homogeneous obj - c == 0 form
    // matches the rows, and the leftover constant is read directly).
    let mut obj_vec = vec![BigRational::zero(); n + 1];
    for (v, c) in &obj_coeffs {
        obj_vec[col_of[v]] = c.clone();
    }
    obj_vec[n] = c0;

    // Gaussian elimination of the equality system to reduced echelon form.
    // We never pivot on the constant column `n`.
    let mut pivot_for_col: Vec<Option<usize>> = vec![None; n];
    let mut next_row = 0usize;
    for col in 0..n {
        if should_stop() {
            return None;
        }
        if next_row >= rows.len() {
            break;
        }
        // Find a pivot row at or below `next_row` with a nonzero entry in `col`.
        let mut sel: Option<usize> = None;
        for (i, row) in rows.iter().enumerate().skip(next_row) {
            if !row[col].is_zero() {
                sel = Some(i);
                break;
            }
        }
        let Some(sel) = sel else {
            continue;
        };
        rows.swap(next_row, sel);
        let pivot = next_row;
        // Normalize the pivot row so the pivot entry is 1.
        let inv = rows[pivot][col].clone();
        for x in rows[pivot].iter_mut() {
            *x /= &inv;
        }
        // Eliminate this column from every OTHER row (full reduction).
        for i in 0..rows.len() {
            if i == pivot {
                continue;
            }
            if rows[i][col].is_zero() {
                continue;
            }
            if should_stop() {
                return None;
            }
            let factor = rows[i][col].clone();
            for j in 0..=n {
                if j % EQ_AGG_INNER_POLL == 0 && should_stop() {
                    return None;
                }
                let term = &factor * &rows[pivot][j];
                rows[i][j] -= term;
            }
        }
        pivot_for_col[col] = Some(pivot);
        next_row += 1;
    }

    // Reduce the objective against the pivots: subtract factor * pivot_row.
    for col in 0..n {
        if should_stop() {
            return None;
        }
        let Some(pivot) = pivot_for_col[col] else {
            continue;
        };
        if obj_vec[col].is_zero() {
            continue;
        }
        let factor = obj_vec[col].clone();
        for j in 0..=n {
            if j % EQ_AGG_INNER_POLL == 0 && should_stop() {
                return None;
            }
            let term = &factor * &rows[pivot][j];
            obj_vec[j] -= term;
        }
    }

    // Residual: any nonzero variable coefficient means the objective is NOT
    // expressible as a combination of the equalities — decline.
    if obj_vec[0..n].iter().any(|c| !c.is_zero()) {
        return None;
    }

    // The leftover constant is the objective value on every feasible point. It
    // must be integral to be a sound integer bound.
    let constant = &obj_vec[n];
    if !constant.denom().eq(&BigInt::from(1)) {
        return None;
    }
    i128::try_from(constant.numer().clone()).ok()
}

/// `should_stop` is threaded into every sub-bound (the equality-aggregation
/// elimination, the covering/weighted-DP scans and the surrogate aggregation);
/// a stop makes the affected sub-bound decline (`None`), which only ever
/// weakens the combined bound — never a wrong one. Pass `&|| false` where no
/// stop context exists (tests / verification harnesses on tiny inputs).
pub(crate) fn objective_lower_bound_from_constraints(
    constraints: &[PbConstraint],
    objective: &PbObjective,
    should_stop: &dyn Fn() -> bool,
) -> Option<i128> {
    if objective.terms.is_empty() {
        return Some(0);
    }

    // Equality-aggregation affine reduction, computed on the RAW SIGNED
    // objective. When the objective is an exact rational combination of the `=`
    // rows it is a constant on the feasible set; that constant is folded in
    // AFTER (outside) the `.max(0)` clamp below via `max_optional_bounds`, so
    // the clamp can never inflate a legitimately-negative constant. This bound
    // declines (None) on any non-empty residual, so it is only ever an exact
    // constant — never a box-min — and is therefore correct-by-construction.
    let equality_aggregation =
        equality_aggregation_objective_constant(constraints, objective, should_stop);

    // Existing positive-coefficient covering/cardinality/aggregation path. This
    // requires every objective coefficient to be positive (single-literal); it
    // contributes `None` otherwise so the equality bound still applies.
    let positive_path = (|| {
        let objective_coefficients = objective_positive_linear_coefficients(objective)?;
        let direct = direct_objective_lower_bound_from_constraints(
            constraints,
            objective_coefficients.clone(),
            should_stop,
        )?;
        let cardinality = cardinality_objective_lower_bound_from_constraints(
            constraints,
            &objective_coefficients,
            should_stop,
        )?;
        // Surrogate LP-dual aggregation bound (None => contributes 0, no bound).
        let aggregation = aggregation_objective_lower_bound_from_constraints(
            constraints,
            &objective_coefficients,
            should_stop,
        )
        .unwrap_or(0);

        Some(direct.max(cardinality).max(aggregation).max(0))
    })();

    max_optional_bounds(positive_path, equality_aggregation)
}

fn objective_lower_bound_with_fixed_literals(
    constraints: &[PbConstraint],
    objective: &PbObjective,
    fixed_literals: &HashMap<u32, bool>,
    should_stop: &dyn Fn() -> bool,
) -> Option<i128> {
    if fixed_literals.is_empty() {
        return objective_lower_bound_from_constraints(constraints, objective, should_stop);
    }

    let (fixed_bound, residual_objective) =
        residual_positive_objective_after_fixed_literals(objective, fixed_literals)?;
    let residual_bound =
        objective_lower_bound_from_constraints(constraints, &residual_objective, should_stop)?;
    fixed_bound.checked_add(residual_bound)
}

fn residual_positive_objective_after_fixed_literals(
    objective: &PbObjective,
    fixed_literals: &HashMap<u32, bool>,
) -> Option<(i128, PbObjective)> {
    let mut fixed_bound = 0i128;
    let mut residual_terms = Vec::with_capacity(objective.terms.len());

    for term in &objective.terms {
        let [lit] = term.lits.as_slice() else {
            return None;
        };
        if term.coeff <= 0 {
            return None;
        }

        match fixed_literals.get(&lit.var).copied() {
            Some(value) => {
                if value ^ lit.negated {
                    fixed_bound = fixed_bound.checked_add(term.coeff)?;
                }
            }
            None => residual_terms.push(term.clone()),
        }
    }

    Some((
        fixed_bound,
        PbObjective {
            terms: residual_terms,
        },
    ))
}

fn direct_objective_lower_bound_from_constraints(
    constraints: &[PbConstraint],
    mut remaining_coefficients: HashMap<PbLit, i128>,
    should_stop: &dyn Fn() -> bool,
) -> Option<i128> {
    let mut proven_lower_bound = 0i128;

    for constraint in constraints {
        if should_stop() {
            return None;
        }
        let Some(candidate) = objective_lower_bound_candidate(constraint, &remaining_coefficients)
        else {
            continue;
        };

        for (lit, coeff) in candidate.coefficients {
            let remaining = remaining_coefficients.get_mut(&lit)?;
            *remaining = remaining.checked_sub(coeff.checked_mul(candidate.max_multiplier)?)?;
        }
        proven_lower_bound = proven_lower_bound
            .checked_add(candidate.degree.checked_mul(candidate.max_multiplier)?)?;
    }

    Some(proven_lower_bound)
}

fn cardinality_objective_lower_bound_from_constraints(
    constraints: &[PbConstraint],
    objective_coefficients: &HashMap<PbLit, i128>,
    should_stop: &dyn Fn() -> bool,
) -> Option<i128> {
    let mut best_lower_bound = 0i128;
    for constraint in constraints {
        if should_stop() {
            return None;
        }
        if let Some(lower_bound) =
            cardinality_objective_lower_bound_value(constraint, objective_coefficients)
        {
            best_lower_bound = best_lower_bound.max(lower_bound);
        }
        if let Some(lower_bound) =
            weighted_objective_lower_bound_value(constraint, objective_coefficients, should_stop)
        {
            best_lower_bound = best_lower_bound.max(lower_bound);
        }
    }
    Some(best_lower_bound)
}

/// Surrogate (uniform-multiplier) LP-dual lower bound.
///
/// Aggregates the `>=` covering rows with a single nonnegative rational multiplier
/// `1/M` (with `M = max over literals of colsum/objcoeff`) to obtain a Chvátal-Gomory
/// dual bound `objective >= ceil(sum_rhs / M)`. This certifies the LP-tight bound that
/// conflict-driven / core-guided search structurally cannot synthesize — e.g. the exact
/// minimum dominating set on a `k`-closed-regular graph: every variable appears in `k`
/// rows, so `M = k` and `LB = n/k` (the perfect-code optimum). Exact `i128` with checked
/// arithmetic; returns `None` (no bound) on any unsupported shape or overflow.
///
/// SOUNDNESS: nonnegative multipliers on `>=` rows give a valid `>=` consequence; because
/// every aggregated literal has aggregated coefficient `colsum/M <= objcoeff`, the
/// aggregated LHS is `<= objective`, hence `objective >= sum_rhs / M`, and (objective is
/// integer) `>= ceil(sum_rhs / M)`. This is only ever `max`-merged into the optimality
/// floor — it can never change an incumbent or exceed the true optimum, PROVIDED every
/// literal in every aggregated row has a strictly-positive objective coefficient on the
/// SAME literal (the load-bearing guard below). Any row with another literal is excluded
/// entirely, which only weakens the bound (still sound).
fn aggregation_objective_lower_bound_from_constraints(
    constraints: &[PbConstraint],
    objective_coefficients: &HashMap<PbLit, i128>,
    should_stop: &dyn Fn() -> bool,
) -> Option<i128> {
    let mut colsum: HashMap<PbLit, i128> = HashMap::new();
    let mut rhs_sum: i128 = 0;
    for constraint in constraints {
        if should_stop() {
            return None;
        }
        if constraint.rel != PbRel::Ge || constraint.rhs <= 0 {
            continue;
        }
        // Include a row only if EVERY term is a single positive-coefficient literal
        // whose EXACT literal (incl. negation) has a strictly-positive objective
        // coefficient. This is the load-bearing soundness guard: it guarantees the
        // aggregated coefficient on each literal is bounded by the objective
        // coefficient on the same literal, so the aggregate cannot exceed the
        // objective. Any other shape => skip the row (sound, weaker bound).
        let row_ok = constraint
            .terms
            .iter()
            .all(|term| match term.lits.as_slice() {
                [lit] => {
                    term.coeff > 0 && objective_coefficients.get(lit).copied().unwrap_or(0) > 0
                }
                _ => false,
            });
        if !row_ok {
            continue;
        }
        rhs_sum = rhs_sum.checked_add(constraint.rhs)?;
        for term in &constraint.terms {
            let entry = colsum.entry(term.lits[0]).or_insert(0);
            *entry = entry.checked_add(term.coeff)?;
        }
    }
    if rhs_sum <= 0 || colsum.is_empty() {
        return None;
    }
    // M = max over included literals of colsum/objcoeff, via exact checked
    // cross-multiplication (overflow => None, sound). Tracked as the fraction cs*/cv*.
    let mut best_cs: i128 = 0;
    let mut best_cv: i128 = 1;
    for (lit, &cs) in &colsum {
        let cv = *objective_coefficients.get(lit)?; // present and > 0 by construction
                                                    // cs/cv > cs*/cv*  <=>  cs*cv* > cs**cv   (all strictly positive)
        if cs.checked_mul(best_cv)? > best_cs.checked_mul(cv)? {
            best_cs = cs;
            best_cv = cv;
        }
    }
    if best_cs <= 0 {
        return None;
    }
    // LB = ceil(sum_rhs / M) = ceil(sum_rhs * cv* / cs*)  (positive ceiling division).
    let numerator = rhs_sum.checked_mul(best_cv)?;
    let lower_bound = numerator.checked_add(best_cs - 1)? / best_cs;
    (lower_bound > 0).then_some(lower_bound)
}

const WEIGHTED_OBJECTIVE_LOWER_BOUND_RHS_LIMIT: i128 = 4096;

fn weighted_objective_lower_bound_value(
    constraint: &PbConstraint,
    objective_coefficients: &HashMap<PbLit, i128>,
    should_stop: &dyn Fn() -> bool,
) -> Option<i128> {
    if constraint.rel != PbRel::Ge
        || constraint.rhs <= 0
        || constraint.rhs > WEIGHTED_OBJECTIVE_LOWER_BOUND_RHS_LIMIT
    {
        return None;
    }

    let mut row_coefficients = HashMap::<PbLit, i128>::new();
    for term in &constraint.terms {
        let [lit] = term.lits.as_slice() else {
            return None;
        };
        if term.coeff <= 0 || !objective_coefficients.contains_key(lit) {
            return None;
        }
        let entry = row_coefficients.entry(*lit).or_insert(0);
        *entry = entry.checked_add(term.coeff)?;
    }

    let rhs = usize::try_from(constraint.rhs).ok()?;
    let infinity = i128::MAX;
    let mut min_cost_by_activity = vec![infinity; rhs + 1];
    min_cost_by_activity[0] = 0;

    for (lit, row_coeff) in row_coefficients {
        // Per-literal poll keeps the inter-poll DP work at most one
        // `rhs`-length (<= 4096) sweep of machine-word ops.
        if should_stop() {
            return None;
        }
        let objective_coeff = *objective_coefficients.get(&lit)?;
        let activity = usize::try_from(row_coeff.min(constraint.rhs)).ok()?;
        for previous_activity in (0..=rhs).rev() {
            let previous_cost = min_cost_by_activity[previous_activity];
            if previous_cost == infinity {
                continue;
            }

            let next_activity = (previous_activity + activity).min(rhs);
            let next_cost = previous_cost.checked_add(objective_coeff)?;
            if next_cost < min_cost_by_activity[next_activity] {
                min_cost_by_activity[next_activity] = next_cost;
            }
        }
    }

    (min_cost_by_activity[rhs] != infinity).then_some(min_cost_by_activity[rhs])
}

fn cardinality_objective_lower_bound_value(
    constraint: &PbConstraint,
    objective_coefficients: &HashMap<PbLit, i128>,
) -> Option<i128> {
    if constraint.rel != PbRel::Ge || constraint.rhs <= 0 {
        return None;
    }

    let mut row_weights = Vec::with_capacity(constraint.terms.len());
    let mut seen_row_lits = HashSet::new();
    for term in &constraint.terms {
        let [lit] = term.lits.as_slice() else {
            return None;
        };
        if term.coeff != 1 || !seen_row_lits.insert(*lit) {
            return None;
        }
        row_weights.push(*objective_coefficients.get(lit)?);
    }

    let required = usize::try_from(constraint.rhs).ok()?;
    if required == 0 || required > row_weights.len() {
        return None;
    }

    row_weights.sort_unstable();
    row_weights
        .into_iter()
        .take(required)
        .try_fold(0i128, i128::checked_add)
}

fn objective_lower_bound_candidate(
    constraint: &PbConstraint,
    remaining_objective_coefficients: &HashMap<PbLit, i128>,
) -> Option<ObjectiveLowerBoundCandidate> {
    if constraint.rel != PbRel::Ge || constraint.rhs <= 0 {
        return None;
    }

    let mut coefficients = HashMap::new();
    for term in &constraint.terms {
        let [lit] = term.lits.as_slice() else {
            return None;
        };
        if term.coeff <= 0 {
            return None;
        }
        if !remaining_objective_coefficients.contains_key(lit) {
            return None;
        }
        let entry = coefficients.entry(*lit).or_insert(0i128);
        *entry = entry.checked_add(term.coeff)?;
    }

    let mut max_multiplier = i128::MAX;
    for (lit, coeff) in &coefficients {
        let remaining = *remaining_objective_coefficients.get(lit)?;
        if *coeff <= 0 || remaining <= 0 {
            return None;
        }
        max_multiplier = max_multiplier.min(remaining / *coeff);
    }
    if max_multiplier <= 0 {
        return None;
    }

    let mut coefficients: Vec<_> = coefficients.into_iter().collect();
    coefficients.sort_by_key(|(lit, _)| (lit.var, lit.negated));

    Some(ObjectiveLowerBoundCandidate {
        coefficients,
        degree: constraint.rhs,
        max_multiplier,
    })
}

fn cardinality_objective_lower_bound_candidate(
    constraint: &PbConstraint,
    constraint_id: ConstraintId,
    objective_coefficients: &HashMap<PbLit, i128>,
) -> Option<CardinalityObjectiveLowerBoundCandidate> {
    if constraint.rel != PbRel::Ge || constraint.rhs <= 0 {
        return None;
    }

    let mut row_lits = Vec::with_capacity(constraint.terms.len());
    let mut seen_row_lits = HashSet::new();
    for term in &constraint.terms {
        let [lit] = term.lits.as_slice() else {
            return None;
        };
        if term.coeff != 1 || !seen_row_lits.insert(*lit) {
            return None;
        }
        if !objective_coefficients.contains_key(lit) {
            return None;
        }
        row_lits.push(*lit);
    }

    let required = usize::try_from(constraint.rhs).ok()?;
    if required == 0 || required > row_lits.len() {
        return None;
    }

    let mut weighted_row_lits: Vec<_> = row_lits
        .iter()
        .map(|lit| Some((*lit, *objective_coefficients.get(lit)?)))
        .collect::<Option<_>>()?;
    weighted_row_lits.sort_by_key(|(lit, coeff)| (*coeff, lit.var, lit.negated));
    let threshold = weighted_row_lits.get(required - 1)?.1;
    if threshold <= 0 {
        return None;
    }

    let mut current_coefficients = HashMap::new();
    for lit in &row_lits {
        current_coefficients.insert(*lit, threshold);
    }

    let mut degree = constraint.rhs.checked_mul(threshold)?;
    let mut expression = constraint_id.to_string();
    if threshold > 1 {
        expression.push(' ');
        expression.push_str(&threshold.to_string());
        expression.push_str(" *");
    }

    for (lit, objective_coeff) in weighted_row_lits
        .iter()
        .take(required)
        .filter(|(_, objective_coeff)| *objective_coeff < threshold)
    {
        let delta = threshold.checked_sub(*objective_coeff)?;
        append_pol_literal_axiom(&mut expression, complement_pb_lit(*lit), delta)?;
        *current_coefficients.get_mut(lit)? = *objective_coeff;
        degree = degree.checked_sub(delta)?;
    }

    let mut sorted_objective_coefficients: Vec<_> = objective_coefficients
        .iter()
        .map(|(lit, coeff)| (*lit, *coeff))
        .collect();
    sorted_objective_coefficients.sort_by_key(|(lit, _)| (lit.var, lit.negated));

    for (lit, objective_coeff) in sorted_objective_coefficients {
        let current = current_coefficients.get(&lit).copied().unwrap_or(0);
        if objective_coeff < current {
            return None;
        }
        let delta = objective_coeff.checked_sub(current)?;
        append_pol_literal_axiom(&mut expression, lit, delta)?;
    }

    expression.push_str(" ;");
    Some(CardinalityObjectiveLowerBoundCandidate { degree, expression })
}

fn append_pol_literal_axiom(expression: &mut String, lit: PbLit, coefficient: i128) -> Option<()> {
    if coefficient < 0 {
        return None;
    }
    if coefficient == 0 {
        return Some(());
    }

    expression.push(' ');
    expression.push_str(&format_lit(lit));
    if coefficient > 1 {
        expression.push(' ');
        expression.push_str(&coefficient.to_string());
        expression.push_str(" *");
    }
    expression.push_str(" +");
    Some(())
}

fn ceil_div_positive(numerator: i128, denominator: i128) -> Option<i128> {
    if numerator <= 0 || denominator <= 0 {
        return None;
    }
    let adjusted = numerator.checked_add(denominator.checked_sub(1)?)?;
    Some(adjusted / denominator)
}

fn negated_ge_constraint_import_is_nontrivial(terms: &[PbTerm], rhs: i128) -> bool {
    let negated_terms: Vec<PbTerm> = terms
        .iter()
        .map(|term| PbTerm {
            coeff: -term.coeff,
            lits: term.lits.clone(),
        })
        .collect();
    ge_constraint_import_is_nontrivial(&negated_terms, rhs)
}

fn ge_constraint_import_is_nontrivial(terms: &[PbTerm], rhs: i128) -> bool {
    let mut adjusted_rhs = rhs;

    for term in terms {
        if term.coeff == 0 {
            continue;
        }

        match term.lits.as_slice() {
            [] => {
                adjusted_rhs = adjusted_rhs.saturating_sub(term.coeff);
            }
            [_] if term.coeff < 0 => {
                adjusted_rhs = adjusted_rhs.saturating_sub(term.coeff);
            }
            [_] => {}
            _ => return false,
        }
    }

    adjusted_rhs > 0
}

fn format_pb_constraint(constraint: &PbConstraint) -> Option<String> {
    if constraint.rel != PbRel::Ge {
        return None;
    }

    let mut linear_terms = Vec::with_capacity(constraint.terms.len());
    for term in &constraint.terms {
        if term.lits.len() != 1 {
            return None;
        }

        linear_terms.push((term.lits[0], term.coeff));
    }
    linear_terms.sort_by_key(|(lit, _)| (lit.var, lit.negated));

    Some(format_constraint(&linear_terms, constraint.rhs))
}

/// Computes the Luby sequence value at a given index (1-based).
///
/// Reference: Luby, Sinclair, Zuckerman (1993).
fn luby_sequence(index: u32) -> u64 {
    if index == 0 {
        return 1;
    }

    let mut size = 1u64;
    let mut seq = 1u64;

    while size < u64::from(index) + 1 {
        size = 2 * size + 1;
        seq += 1;
    }

    let mut remaining = index;
    while size - 1 != u64::from(remaining) {
        size = (size - 1) / 2;
        seq -= 1;
        if u64::from(remaining) >= size {
            remaining -= size as u32;
        }
    }

    1u64 << (seq - 1)
}

/// Builds a PB constraint encoding `sum(objective terms) <= upper_bound - 1`.
///
/// This is equivalent to: `sum(-a_i * l_i) >= -(upper_bound - 1)`.
/// Returns `None` if arithmetic overflows (cannot tighten further).
fn build_upper_bound_constraint(
    objective: &PbObjective,
    upper_bound: i128,
) -> Option<PbConstraint> {
    strictly_better_than_incumbent_constraint(objective, upper_bound).ok()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TightenedSatOutcome {
    Improved,
    NotProven,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum TightenedSolveDecision {
    Continue { model: Vec<bool>, value: i128 },
    Return(PbCdclResult),
}

fn classify_tightened_sat_candidate(
    best_value: i128,
    candidate_value: i128,
) -> TightenedSatOutcome {
    if candidate_value < best_value {
        TightenedSatOutcome::Improved
    } else {
        TightenedSatOutcome::NotProven
    }
}

fn decide_tightened_solve_result(
    objective: &PbObjective,
    incumbent_model: &[bool],
    incumbent_value: i128,
    result: PbCdclResult,
) -> TightenedSolveDecision {
    match result {
        PbCdclResult::Satisfiable(model) => {
            let value = eval_objective(objective, &model);
            match classify_tightened_sat_candidate(incumbent_value, value) {
                TightenedSatOutcome::Improved => TightenedSolveDecision::Continue { model, value },
                TightenedSatOutcome::NotProven => {
                    // Tightening returned SAT but did not improve the incumbent.
                    // This does not prove optimality; fail closed to a feasible result.
                    TightenedSolveDecision::Return(PbCdclResult::Feasible(
                        incumbent_model.to_vec(),
                        incumbent_value,
                    ))
                }
            }
        }
        PbCdclResult::Unsatisfiable => {
            // No solution with objective < incumbent_value exists.
            // incumbent_value is provably optimal.
            TightenedSolveDecision::Return(PbCdclResult::Optimal(
                incumbent_model.to_vec(),
                incumbent_value,
            ))
        }
        PbCdclResult::Unknown => {
            // Interrupted during tightening search.
            TightenedSolveDecision::Return(PbCdclResult::Feasible(
                incumbent_model.to_vec(),
                incumbent_value,
            ))
        }
        // Should not occur from solve_with_stop.
        _ => TightenedSolveDecision::Return(PbCdclResult::Feasible(
            incumbent_model.to_vec(),
            incumbent_value,
        )),
    }
}

#[cfg(test)]
mod tests;

#[cfg(kani)]
mod kani_covering_bound;
