// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Interpolation-based lemma learning for PDR/Spacer
//!
//! This module implements interpolating SAT solving for CHC problems.
//! When A ∧ B is UNSAT, we compute an interpolant I such that:
//! - A ⊨ I (I is implied by A)
//! - I ∧ B is UNSAT (I is inconsistent with B)
//! - I uses only variables shared between A and B
//!
//! This is the core technique from Golem/Spacer for learning more general
//! blocking lemmas than point-based blocking.
//!
//! ## Implementation
//!
//! Currently uses Farkas-based interpolation for linear arithmetic.
//! Future: integrate with proof-producing SMT solver for richer interpolants.

use crate::farkas::{
    compute_interpolant_until as farkas_interpolant_until, normalize_linear_inequality_expr,
};
use crate::ChcExpr;
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_core::time::Instant;
use stats::StrategyExit;
use std::sync::{Mutex, OnceLock};
use std::time::Duration;
use tracing::{debug, info};

pub(crate) mod core_ite_farkas;
mod fallback;
mod heuristics;
pub(crate) mod mbp_interpolation;
mod proof_backed;
mod proof_eq_diffvar;
// Workstream D (CHC-COMP 2026) Rung 1: proof substrate (owner WP-D1-P) and
// the ITP-BOARD telemetry (owner WP-D1-M).
pub(crate) mod proof_groups;
pub(crate) mod proof_script;
pub(crate) mod stats;
pub(crate) mod unit_transfer;
use fallback::{
    compute_unsat_core_interpolant_until, interpolate_with_disjunction_split,
    is_valid_interpolant_until,
};
use heuristics::{compute_bound_interpolant, compute_transitivity_interpolant};
pub(crate) use proof_backed::{
    interpolating_sat_constraints_with_proof_provenance, proof_interpolant_stats,
    proof_itp_solve_timeouts,
};

/// Budget of the plain cascade entry when the thread has no deadline
/// (contract C-M2).
const PLAIN_CASCADE_DEFAULT_BUDGET: Duration = Duration::from_secs(5);
/// Maximum total branches explored during disjunction-split interpolation.
/// Prevents exponential blowup from nested disjunctions (k^n for n disjunctions
/// with k disjuncts each). Each branch invokes a full SMT solve, so this bounds
/// the worst-case cost. Exceeding the limit triggers Unknown (sound fallback).
const DISJUNCTION_SPLIT_BRANCH_LIMIT: usize = 32;
const CONE_CACHE_ENV: &str = "AY_CHC_INTERPOLATION_CONE_CACHE";
const CONE_CACHE_CAP: usize = 4096;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct InterpolationConeCacheKey {
    a_constraints: Vec<ChcExpr>,
    b_constraints: Vec<ChcExpr>,
    shared_vars: Vec<String>,
}

#[derive(Default)]
struct ReplayableInterpolationConeCache {
    entries: FxHashMap<InterpolationConeCacheKey, ChcExpr>,
    hits: u64,
    misses: u64,
    rejected_hits: u64,
    inserts: u64,
    clears: u64,
}

static REPLAYABLE_CONE_CACHE: OnceLock<Mutex<ReplayableInterpolationConeCache>> = OnceLock::new();

fn replayable_cone_cache_enabled() -> bool {
    std::env::var(CONE_CACHE_ENV)
        .is_ok_and(|value| value == "1" || value.eq_ignore_ascii_case("true"))
}

fn replayable_cone_cache() -> &'static Mutex<ReplayableInterpolationConeCache> {
    REPLAYABLE_CONE_CACHE.get_or_init(|| Mutex::new(ReplayableInterpolationConeCache::default()))
}

fn canonicalize_interpolation_constraints(constraints: &[ChcExpr]) -> Vec<ChcExpr> {
    let mut canonical: Vec<ChcExpr> = constraints
        .iter()
        .map(|constraint| {
            normalize_linear_inequality_expr(constraint)
                .unwrap_or_else(|| constraint.clone())
                .simplify_constants()
        })
        .collect();
    canonical.sort_by_key(|expr| (expr.structural_hash(), format!("{expr:?}")));
    canonical
}

fn interpolation_cone_cache_key(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
) -> InterpolationConeCacheKey {
    let mut shared_vars: Vec<String> = shared_vars.iter().cloned().collect();
    shared_vars.sort();
    InterpolationConeCacheKey {
        a_constraints: canonicalize_interpolation_constraints(a_constraints),
        b_constraints: canonicalize_interpolation_constraints(b_constraints),
        shared_vars,
    }
}

fn try_replay_cached_interpolant(
    key: &InterpolationConeCacheKey,
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
    deadline: Option<Instant>,
) -> Option<ChcExpr> {
    let cached = {
        let mut cache = replayable_cone_cache().lock().ok()?;
        match cache.entries.get(key).cloned() {
            Some(interpolant) => {
                cache.hits = cache.hits.saturating_add(1);
                interpolant
            }
            None => {
                cache.misses = cache.misses.saturating_add(1);
                return None;
            }
        }
    };

    if is_valid_interpolant_until(a_constraints, b_constraints, &cached, shared_vars, deadline) {
        debug_assert_shared_var_locality(&cached, shared_vars, "cone_cache");
        info!(
            event = "chc_interpolation_cone_cache_hit",
            key_hash = cache_key_hash(key),
            "Replayable interpolation cone cache hit passed Craig validation",
        );
        Some(cached)
    } else if deadline_expired(deadline) {
        info!(
            event = "chc_interpolation_cone_cache_rejected",
            key_hash = cache_key_hash(key),
            reason = "deadline_expired",
            "Replayable interpolation cone cache hit validation reached the caller deadline",
        );
        None
    } else {
        if let Ok(mut cache) = replayable_cone_cache().lock() {
            cache.rejected_hits = cache.rejected_hits.saturating_add(1);
            cache.entries.remove(key);
        }
        info!(
            event = "chc_interpolation_cone_cache_rejected",
            key_hash = cache_key_hash(key),
            reason = "craig_validation_failed",
            "Replayable interpolation cone cache hit failed validation and was evicted",
        );
        None
    }
}

fn insert_replayable_cone_cache_entry(key: InterpolationConeCacheKey, interpolant: &ChcExpr) {
    if let Ok(mut cache) = replayable_cone_cache().lock() {
        if cache.entries.len() >= CONE_CACHE_CAP && !cache.entries.contains_key(&key) {
            cache.entries.clear();
            cache.clears = cache.clears.saturating_add(1);
        }
        cache.entries.insert(key.clone(), interpolant.clone());
        cache.inserts = cache.inserts.saturating_add(1);
        debug!(
            event = "chc_interpolation_cone_cache_insert",
            key_hash = cache_key_hash(&key),
            entries = cache.entries.len(),
            hits = cache.hits,
            misses = cache.misses,
            rejected_hits = cache.rejected_hits,
            inserts = cache.inserts,
            clears = cache.clears,
            "Inserted replayable interpolation cone cache entry",
        );
    }
}

fn cache_key_hash(key: &InterpolationConeCacheKey) -> u64 {
    use std::hash::{Hash, Hasher};

    let mut hasher = rustc_hash::FxHasher::default();
    key.hash(&mut hasher);
    hasher.finish()
}

fn record_replayable_cone_cache_success(
    key: Option<&InterpolationConeCacheKey>,
    interpolant: &ChcExpr,
) {
    if let Some(key) = key {
        insert_replayable_cone_cache_entry(key.clone(), interpolant);
    }
}

/// Result of interpolant computation
#[derive(Debug, Clone)]
pub(crate) enum InterpolatingSatResult {
    /// A ∧ B is unsatisfiable, with interpolant
    Unsat(ChcExpr),
    /// Unknown (could not determine)
    Unknown,
}

#[inline]
fn debug_assert_shared_var_locality(
    _interpolant: &ChcExpr,
    _shared_vars: &FxHashSet<String>,
    _strategy: &'static str,
) {
    #[cfg(debug_assertions)]
    {
        let non_shared: Vec<String> = _interpolant
            .vars()
            .into_iter()
            .map(|v| v.name)
            .filter(|name| !_shared_vars.contains(name))
            .collect();
        debug_assert!(
            non_shared.is_empty(),
            "BUG: strategy {_strategy} produced interpolant with non-shared vars: {non_shared:?}"
        );
    }
}

/// Compute an interpolant from constraint lists.
///
/// When A (transition constraints) ∧ B (bad state) is UNSAT, compute an
/// interpolant I such that:
/// - A ⊨ I
/// - I ∧ B is UNSAT
/// - I uses only variables shared between A and B
///
/// REQUIRES: `shared_vars` contains exactly the variables that appear in both
///   `a_constraints` and `b_constraints` (the "interface" variables).
///
/// ENSURES: If `InterpolatingSatResult::Unsat(I)` is returned:
///   - `∧a_constraints ⊨ I` (A implies I, soundness of interpolant)
///   - `I ∧ ∧b_constraints` is UNSAT (I blocks B)
///   - `I` mentions only variables in `shared_vars` (locality property)
///
/// ENSURES: `InterpolatingSatResult::Unknown` is returned if:
///   - Either constraint list is empty, OR
///   - No interpolation technique could find a valid interpolant, OR
///   - Candidate interpolants fail Craig property validation
///     (This is NOT an error - caller should fall back to other methods)
pub(crate) fn interpolating_sat_constraints(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
) -> InterpolatingSatResult {
    // Contract C-M2 (Workstream D, DESIGN_lra_interp_tpa.md §9): the plain
    // entry is always bounded -- by the thread's SMT/solve deadline when one
    // is installed (every portfolio engine runs under one), else by
    // `PLAIN_CASCADE_DEFAULT_BUDGET`. Unbounded, the strategy legs' own
    // validation checks ran with no timeout and could wedge an engine thread
    // (PDR stage 1, TPA, DAR, LAWI, CEGAR, `interpolation_api`). Only
    // completeness can change: a cascade that runs out of time answers
    // `Unknown`, which every caller already handles.
    let (deadline, origin) = match crate::smt::deadline::effective_thread_deadline() {
        Some(deadline) => (deadline, stats::CascadeDeadline::Thread),
        None => (
            Instant::now() + PLAIN_CASCADE_DEFAULT_BUDGET,
            stats::CascadeDeadline::Default,
        ),
    };
    let mut budget = DISJUNCTION_SPLIT_BRANCH_LIMIT;
    stats::record_cascade_call(origin);
    let result = interpolating_sat_constraints_with_budget(
        a_constraints,
        b_constraints,
        shared_vars,
        &mut budget,
        Some(deadline),
    );
    stats::record_cascade_result(matches!(result, InterpolatingSatResult::Unsat(_)));
    result
}

/// Cap on the proof solve of [`interpolating_sat_constraints_lra_proof_first`].
const LRA_PROOF_FIRST_CAP: Duration = Duration::from_secs(5);
/// Consecutive budget-exhausted proof solves after which a thread stops
/// trying the proof substrate (as IMC's strike rule does).
const LRA_PROOF_FIRST_STRIKES: u32 = 3;

thread_local! {
    static LRA_PROOF_FIRST_TIMEOUTS: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

/// Engine interpolation on the proof substrate first when the pair is pure
/// QF_LRA(+Bool): ONE proof-producing solve, equalities solved across the cut
/// (`unit_transfer`), the first extracted candidate that passes the
/// Verification-lane Craig check (`proof_backed`). Anything else — another
/// logic, a failed or timed-out proof, three timeouts in a row on this thread
/// — runs the cascade exactly as [`interpolating_sat_constraints_until`]
/// (`deadline`: the caller's, else the thread's, else 5 s).
pub(crate) fn interpolating_sat_constraints_lra_proof_first(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
    deadline: Option<Instant>,
) -> InterpolatingSatResult {
    let deadline = deadline
        .or_else(crate::smt::deadline::effective_thread_deadline)
        .unwrap_or_else(|| Instant::now() + PLAIN_CASCADE_DEFAULT_BUDGET);
    let roots: Vec<&ChcExpr> = a_constraints.iter().chain(b_constraints).collect();
    let pure_lra = !a_constraints.is_empty()
        && !b_constraints.is_empty()
        && proof_script::scan_logic(&roots, proof_groups::DEFAULT_DAG_CAPS.max_unique_nodes)
            == Ok(proof_script::ProofLogic::QfLra);
    let strikes = LRA_PROOF_FIRST_TIMEOUTS.with(std::cell::Cell::get);
    if pure_lra && strikes < LRA_PROOF_FIRST_STRIKES {
        let budget = deadline
            .saturating_duration_since(Instant::now())
            .min(LRA_PROOF_FIRST_CAP);
        if !budget.is_zero() {
            let timeouts_before = proof_itp_solve_timeouts();
            let served = proof_backed::try_proof_derived_interpolant(
                a_constraints,
                b_constraints,
                shared_vars,
                budget,
            );
            let timed_out = proof_itp_solve_timeouts() > timeouts_before;
            LRA_PROOF_FIRST_TIMEOUTS.with(|c| c.set(if timed_out { c.get() + 1 } else { 0 }));
            if let Some(itp) = served {
                return InterpolatingSatResult::Unsat(itp);
            }
        }
    }
    interpolating_sat_constraints_until(a_constraints, b_constraints, shared_vars, deadline)
}

/// Compute an interpolant, returning Unknown if the wall-clock deadline is
/// reached before a strategy can produce a valid interpolant.
pub(crate) fn interpolating_sat_constraints_until(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
    deadline: Instant,
) -> InterpolatingSatResult {
    let _census_role = crate::smt::lane::ScopedCensusRole::set("interp");
    let mut budget = DISJUNCTION_SPLIT_BRANCH_LIMIT;
    stats::record_cascade_call(stats::CascadeDeadline::Caller);
    let result = interpolating_sat_constraints_with_budget(
        a_constraints,
        b_constraints,
        shared_vars,
        &mut budget,
        Some(deadline),
    );
    stats::record_cascade_result(matches!(result, InterpolatingSatResult::Unsat(_)));
    result
}

pub(super) fn deadline_expired(deadline: Option<Instant>) -> bool {
    // A cancelled portfolio lane is past every deadline, including a cascade
    // call that was handed none.
    crate::smt::deadline::lane_cancelled()
        || deadline.is_some_and(|deadline| Instant::now() >= deadline)
}

pub(super) fn timeout_for_deadline(deadline: Option<Instant>, cap: Duration) -> Option<Duration> {
    let deadline = deadline?;
    let remaining = deadline.saturating_duration_since(Instant::now());
    if remaining.is_zero() {
        None
    } else {
        Some(remaining.min(cap))
    }
}

/// Budget-aware interpolation. The `branch_budget` tracks how many disjunction
/// branches remain across the entire recursive call tree. When exhausted,
/// disjunction splitting returns Unknown (sound: only affects completeness).
pub(super) fn interpolating_sat_constraints_with_budget(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
    branch_budget: &mut usize,
    deadline: Option<Instant>,
) -> InterpolatingSatResult {
    if deadline_expired(deadline) {
        info!(
            event = "chc_interpolation_unknown",
            reason = "deadline_expired",
            "Interpolation skipped because caller deadline expired",
        );
        return InterpolatingSatResult::Unknown;
    }

    if a_constraints.is_empty() || b_constraints.is_empty() {
        info!(
            event = "chc_interpolation_strategy_failed",
            strategy = "precheck",
            reason = "empty_constraints",
            a_constraints = a_constraints.len(),
            b_constraints = b_constraints.len(),
            "Interpolation skipped: one side had no constraints",
        );
        return InterpolatingSatResult::Unknown;
    }

    debug!(
        event = "chc_interpolation_start",
        a_constraints = a_constraints.len(),
        b_constraints = b_constraints.len(),
        shared_vars = shared_vars.len(),
        branch_budget = *branch_budget,
        "Starting interpolation cascade",
    );

    let cone_cache_key = if replayable_cone_cache_enabled() {
        let key = interpolation_cone_cache_key(a_constraints, b_constraints, shared_vars);
        if let Some(interpolant) =
            try_replay_cached_interpolant(&key, a_constraints, b_constraints, shared_vars, deadline)
        {
            stats::record_cascade_strategy("cone_cache", StrategyExit::Served);
            return InterpolatingSatResult::Unsat(interpolant);
        }
        if deadline_expired(deadline) {
            return InterpolatingSatResult::Unknown;
        }
        Some(key)
    } else {
        None
    };

    // Try Farkas-based interpolation first (deadline-aware since inc-19: the
    // strategy loops inside validate O(|B|) / O(|A|^2) candidates at up to
    // 2 checks x 2s each, which overstayed the IMC cascade budget by minutes
    // on k>=2 unrollings — the observed "no itp line for 70s+" leg).
    // `farkas::compute_interpolant_until` returns only candidates that
    // passed locality plus both Craig checks against the conjunction of
    // exactly these `a_constraints` / `b_constraints` (its ENSURES), so the
    // result is served without a second validation (2 more solves).
    debug!(
        event = "chc_interpolation_strategy_try",
        strategy = "farkas",
        "Trying Farkas interpolation",
    );
    if let Some(interpolant) =
        farkas_interpolant_until(a_constraints, b_constraints, shared_vars, deadline)
    {
        debug_assert_shared_var_locality(&interpolant, shared_vars, "farkas");
        info!(
            event = "chc_interpolation_strategy_succeeded",
            strategy = "farkas",
            "Interpolation succeeded with Farkas strategy",
        );
        stats::record_cascade_strategy("farkas", StrategyExit::Served);
        record_replayable_cone_cache_success(cone_cache_key.as_ref(), &interpolant);
        return InterpolatingSatResult::Unsat(interpolant);
    }
    info!(
        event = "chc_interpolation_strategy_failed",
        strategy = "farkas",
        reason = "no_candidate",
        "Farkas interpolation produced no candidate",
    );
    stats::record_cascade_strategy("farkas", StrategyExit::NoCandidate);

    // Try bound-based interpolation
    debug!(
        event = "chc_interpolation_strategy_try",
        strategy = "bound",
        "Trying bound interpolation",
    );
    if let Some(interpolant) = compute_bound_interpolant(a_constraints, b_constraints, shared_vars)
    {
        if is_valid_interpolant_until(
            a_constraints,
            b_constraints,
            &interpolant,
            shared_vars,
            deadline,
        ) {
            debug_assert_shared_var_locality(&interpolant, shared_vars, "bound");
            info!(
                event = "chc_interpolation_strategy_succeeded",
                strategy = "bound",
                "Interpolation succeeded with bound strategy",
            );
            stats::record_cascade_strategy("bound", StrategyExit::Served);
            record_replayable_cone_cache_success(cone_cache_key.as_ref(), &interpolant);
            return InterpolatingSatResult::Unsat(interpolant);
        }
        info!(
            event = "chc_interpolation_strategy_failed",
            strategy = "bound",
            reason = "craig_validation_failed",
            "Bound strategy produced a candidate interpolant that failed Craig validation",
        );
        stats::record_cascade_strategy("bound", StrategyExit::CraigInvalid);
    } else {
        info!(
            event = "chc_interpolation_strategy_failed",
            strategy = "bound",
            reason = "no_candidate",
            "Bound interpolation produced no candidate",
        );
        stats::record_cascade_strategy("bound", StrategyExit::NoCandidate);
    }

    // Try transitivity-based interpolation
    debug!(
        event = "chc_interpolation_strategy_try",
        strategy = "transitivity",
        "Trying transitivity interpolation",
    );
    if let Some(interpolant) =
        compute_transitivity_interpolant(a_constraints, b_constraints, shared_vars)
    {
        if is_valid_interpolant_until(
            a_constraints,
            b_constraints,
            &interpolant,
            shared_vars,
            deadline,
        ) {
            debug_assert_shared_var_locality(&interpolant, shared_vars, "transitivity");
            info!(
                event = "chc_interpolation_strategy_succeeded",
                strategy = "transitivity",
                "Interpolation succeeded with transitivity strategy",
            );
            stats::record_cascade_strategy("transitivity", StrategyExit::Served);
            record_replayable_cone_cache_success(cone_cache_key.as_ref(), &interpolant);
            return InterpolatingSatResult::Unsat(interpolant);
        }
        info!(
            event = "chc_interpolation_strategy_failed",
            strategy = "transitivity",
            reason = "craig_validation_failed",
            "Transitivity strategy produced a candidate interpolant that failed Craig validation",
        );
        stats::record_cascade_strategy("transitivity", StrategyExit::CraigInvalid);
    } else {
        info!(
            event = "chc_interpolation_strategy_failed",
            strategy = "transitivity",
            reason = "no_candidate",
            "Transitivity interpolation produced no candidate",
        );
        stats::record_cascade_strategy("transitivity", StrategyExit::NoCandidate);
    }

    // D11: Core-guided ITE-normalized Farkas interpolation.
    // When pure-LIA strategies fail because of ITE terms, case-split on ITE
    // conditions so each case becomes pure LIA, then delegate to Farkas.
    debug!(
        event = "chc_interpolation_strategy_try",
        strategy = "ite_farkas",
        "Trying ITE-normalized Farkas interpolation (D11)",
    );
    if let Some(interpolant) = core_ite_farkas::compute_ite_farkas_interpolant_until(
        a_constraints,
        b_constraints,
        shared_vars,
        deadline,
    ) {
        debug_assert_shared_var_locality(&interpolant, shared_vars, "ite_farkas");
        info!(
            event = "chc_interpolation_strategy_succeeded",
            strategy = "ite_farkas",
            "Interpolation succeeded with ITE-normalized Farkas (D11)",
        );
        stats::record_cascade_strategy("ite_farkas", StrategyExit::Served);
        record_replayable_cone_cache_success(cone_cache_key.as_ref(), &interpolant);
        return InterpolatingSatResult::Unsat(interpolant);
    }
    info!(
        event = "chc_interpolation_strategy_failed",
        strategy = "ite_farkas",
        reason = "no_candidate",
        "ITE-normalized Farkas interpolation produced no candidate",
    );
    stats::record_cascade_strategy("ite_farkas", StrategyExit::NoCandidate);

    if deadline_expired(deadline) {
        return InterpolatingSatResult::Unknown;
    }

    // Dual MBP interpolation: when heuristic methods fail on mixed Bool+LIA,
    // use model-based projection to compute interpolants from B-partition models.
    // Placed before UNSAT-core: at TPA power 1+, UNSAT-core echoes previous
    // interpolants (shared-only conjuncts) and succeeds weakly, preventing MBP
    // from running. MBP produces fresh projections at every power level. (D10)
    debug!(
        event = "chc_interpolation_strategy_try",
        strategy = "dual_mbp",
        "Trying dual MBP interpolation for mixed Bool+LIA",
    );
    if let Some(interpolant) = mbp_interpolation::compute_dual_mbp_interpolant_until(
        a_constraints,
        b_constraints,
        shared_vars,
        deadline,
    ) {
        debug_assert_shared_var_locality(&interpolant, shared_vars, "dual_mbp");
        info!(
            event = "chc_interpolation_strategy_succeeded",
            strategy = "dual_mbp",
            "Interpolation succeeded with dual MBP strategy",
        );
        stats::record_cascade_strategy("dual_mbp", StrategyExit::Served);
        record_replayable_cone_cache_success(cone_cache_key.as_ref(), &interpolant);
        return InterpolatingSatResult::Unsat(interpolant);
    }
    info!(
        event = "chc_interpolation_strategy_failed",
        strategy = "dual_mbp",
        reason = "no_candidate",
        "Dual MBP interpolation produced no valid candidate",
    );
    stats::record_cascade_strategy("dual_mbp", StrategyExit::NoCandidate);

    // Fallback: UNSAT-core-based interpolation.
    // When heuristic methods fail, use the SMT solver's UNSAT core to extract
    // A-side constraints that conflict with B. Filter to shared-variable-only
    // conjuncts for a valid (though possibly weak) interpolant.
    debug!(
        event = "chc_interpolation_strategy_try",
        strategy = "unsat_core",
        "Trying UNSAT-core interpolation fallback",
    );
    if let Some(interpolant) =
        compute_unsat_core_interpolant_until(a_constraints, b_constraints, shared_vars, deadline)
    {
        debug_assert_shared_var_locality(&interpolant, shared_vars, "unsat_core");
        info!(
            event = "chc_interpolation_strategy_succeeded",
            strategy = "unsat_core",
            "Interpolation succeeded with UNSAT-core fallback",
        );
        stats::record_cascade_strategy("unsat_core", StrategyExit::Served);
        record_replayable_cone_cache_success(cone_cache_key.as_ref(), &interpolant);
        return InterpolatingSatResult::Unsat(interpolant);
    }
    info!(
        event = "chc_interpolation_strategy_failed",
        strategy = "unsat_core",
        reason = "no_candidate",
        "UNSAT-core interpolation fallback produced no valid candidate",
    );
    stats::record_cascade_strategy("unsat_core", StrategyExit::NoCandidate);

    // Disjunction case-splitting: if A contains top-level disjunctions,
    // split into cases and interpolate each branch separately.
    //
    // If A = A1 ∨ A2, and A ∧ B is UNSAT, then both A1 ∧ B and A2 ∧ B are UNSAT.
    // Get I1 from (A1, B) and I2 from (A2, B). Then I1 ∨ I2 is a valid interpolant:
    //   - A ⊨ I1 ∨ I2 (each disjunct implies its interpolant)
    //   - (I1 ∨ I2) ∧ B is UNSAT (both I1 ∧ B and I2 ∧ B are UNSAT)
    //   - Variable locality preserved (each Ii uses only shared vars)
    //
    // This enables k-to-1-inductive conversion where build_formula produces
    // Init(x_k) ∨ (Inv ∧ Trans) disjunctions (#2753).
    debug!(
        event = "chc_interpolation_strategy_try",
        strategy = "disjunction_split",
        branch_budget = *branch_budget,
        "Trying disjunction-split interpolation fallback",
    );
    if let Some(result) = interpolate_with_disjunction_split(
        a_constraints,
        b_constraints,
        shared_vars,
        branch_budget,
        deadline,
    ) {
        match result {
            InterpolatingSatResult::Unsat(interpolant) => {
                debug_assert_shared_var_locality(&interpolant, shared_vars, "disjunction_split");
                info!(
                    event = "chc_interpolation_strategy_succeeded",
                    strategy = "disjunction_split",
                    "Interpolation succeeded with disjunction-split fallback",
                );
                stats::record_cascade_strategy("disjunction_split", StrategyExit::Served);
                record_replayable_cone_cache_success(cone_cache_key.as_ref(), &interpolant);
                return InterpolatingSatResult::Unsat(interpolant);
            }
            InterpolatingSatResult::Unknown => {
                info!(
                    event = "chc_interpolation_strategy_failed",
                    strategy = "disjunction_split",
                    reason = "branch_failure_or_budget_exhausted_or_invalid_combination",
                    "Disjunction-split interpolation failed",
                );
                stats::record_cascade_strategy("disjunction_split", StrategyExit::NoCandidate);
            }
        }
    } else {
        info!(
            event = "chc_interpolation_strategy_failed",
            strategy = "disjunction_split",
            reason = "no_disjunction",
            "Disjunction-split interpolation not applicable",
        );
        stats::record_cascade_strategy("disjunction_split", StrategyExit::NoCandidate);
    }

    info!(
        event = "chc_interpolation_unknown",
        a_constraints = a_constraints.len(),
        b_constraints = b_constraints.len(),
        shared_vars = shared_vars.len(),
        remaining_branch_budget = *branch_budget,
        "All interpolation strategies failed",
    );
    InterpolatingSatResult::Unknown
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
mod tests;
