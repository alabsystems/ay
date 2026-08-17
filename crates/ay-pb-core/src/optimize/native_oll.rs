// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Native PB-CDCL core-guided optimization (OLL / RC2-style) over the native
//! pseudo-Boolean engine [`PbCdclSolver`].
//!
//! This is the native-engine counterpart of the SAT-based OLL loop in
//! [`crate::optimize`]. It uses ONE persistent [`PbCdclSolver`] for the whole
//! solve and never rebuilds it per core. Cardinality totalizer relaxations are
//! materialized incrementally via the solver's runtime var-pool
//! ([`PbCdclSolver::new_var`] + [`PbCdclSolver::add_cardinality_runtime`]),
//! retaining the native engine's cutting-planes power on PB-structured instances
//! where the SAT solver is slow.
//!
//! # References
//! - Andres, Kaufmann, Matheis, Schaub, "Unsatisfiability-based optimization in
//!   clasp" (OLL), 2012
//! - Morgado, Dodaro, Marques-Silva, "Core-guided MaxSAT with soft cardinality
//!   constraints", 2014
//! - Ignatiev, Morgado, Marques-Silva, "RC2: an efficient MaxSAT solver", 2019
//!
//! # Soundness summary
//! - The lower bound only increases by the EXACT realized weight of a disjoint
//!   core (`core_weight = min weight among core softs`), accumulated with checked
//!   arithmetic (overflow -> stop with the incumbent). Each extraction round may
//!   batch several PAIRWISE-DISJOINT cores (see [`process_disjoint_core_round`]),
//!   whose weights are additive by disjointness — the sum can never overcount.
//! - Relaxation clauses are emitted by the tested generalized-totalizer encoder
//!   (the same encoder the SAT-OLL path uses); each is an implied consequence of
//!   the counting semantics, so adding them removes no feasible model over the
//!   original variables.
//! - A model proves optimality only when found with the FULL set of remaining
//!   (non-hardened) softs assumed at their no-cost polarity; a partial-stratum
//!   SAT never short-circuits the proof.
//! - `OptResult::Optimal` is returned only after the soundness gate
//!   (`verify_native_optimum`) re-checks the model against every ORIGINAL
//!   constraint, confirms the objective is exact, and confirms the value lies in
//!   `[lower_bound, upper_bound]`. Any failure downgrades to `Satisfiable`.
//! - On interruption / overflow / unsupported core the best incumbent is returned
//!   as `Satisfiable` -- never a false optimum.
//! - EXTERNAL UB CUTOFF (design §2.7 DOWN-channel): when running as a parallel
//!   worker the engine POLLS the [`SharedBounds`] bus `ub` at iteration
//!   boundaries (wait-free `Relaxed` read; an absent/overflowed bus value reads
//!   as "no cutoff", never "0/unbounded-good") and consumes it ONLY TO PRUNE:
//!   the cutoff is installed as an extra bound `objective <= cutoff` inside the
//!   persistent solver. The bus `ub` is the exact objective value of a
//!   coordinator-VERIFIED feasible model (the bus's single-writer invariant),
//!   so every OPTIMAL model of the original instance satisfies the row —
//!   installing it removes no optimal point, every model the solver returns is
//!   still a model of the ORIGINAL constraints, and the OLL core lower bounds
//!   remain sound global lower bounds. The cutoff NEVER overwrites
//!   `best_value`: the returned `(best_assignment, best_value)` pair is always
//!   the engine's OWN witness (the §2.7 desync fix), and a (bus-poisoning-only)
//!   root conflict on the install fail-closes by returning that own pair as
//!   `Satisfiable` — never any claim from the conflicted state.

use std::collections::{BTreeMap as HashMap, BTreeSet as HashSet};

use std::ffi::OsStr;

use crate::cdcl::{PbCdclAssumptionResult, PbCdclSolver, RuntimeConstraintOutcome};
use crate::encoding::encode_totalizer_with_outputs_interruptible;
use crate::objective_bound::objective_at_most_constraint;
use crate::optimize::gf2_parity::gf2_parity_cuts_preferring;
use crate::optimize::shared_bounds::SharedBounds;
use crate::optimize::OptResult;
use crate::solver::{eval_objective, objective_range_fits_i64};
use crate::types::{PbConstraint, PbInstance, PbLit, PbObjective};

/// Maximum number of literals in a core we will attempt to deletion-trim.
const MAX_CORE_TRIM_SIZE: usize = 128;
/// Maximum number of trimming subset-queries per core.
const MAX_CORE_TRIM_CHECKS: usize = 32;

/// Environment gate for GF(2) parity cuts. See [`parity_cuts_enabled`].
const PARITY_CUTS_ENV: &str = "AY_PB_PARITY_CUTS";

/// Environment gate for LP reduced-cost variable fixing. Default **OFF** (opt-in).
/// Set to `1|true|yes|on` to enable. See [`reduced_cost_fixing_enabled`].
const REDUCED_COST_ENV: &str = "AY_PB_REDUCED_COST";
/// Wall-clock budget (ms) for a single reduced-cost-fixing LP solve, size-scaled by
/// the LP-floor schedule and clamped to `[LP_FLOOR_BUDGET_MIN_MS, this]`. The
/// exact-rational simplex + cut loop must not starve the core-guided descent; on a
/// budget abort the LP returns its best sound dual point, so fewer (never unsound)
/// fixings result. Overridable via `AY_PB_REDUCED_COST_MS` (`0` disables).
const REDUCED_COST_BUDGET_MS: u64 = 20_000;
/// Environment override for the reduced-cost-fixing budget (ms). `0` disables.
const REDUCED_COST_BUDGET_ENV: &str = "AY_PB_REDUCED_COST_MS";

/// A soft selector literal with its current residual weight. `literal` true under
/// a model means the soft is "paid" (costs `weight`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct WeightedSoft {
    literal: PbLit,
    weight: i128,
}

/// Outcome of processing a single extracted core.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CoreOutcome {
    /// Core reformulated; keep iterating.
    Continue,
    /// Non-recoverable condition (overflow / encoding failure / degenerate core).
    /// Return the incumbent as `Satisfiable`.
    Stop,
    /// UNSAT with an empty core in the current stratum.
    Exhausted,
}

/// Runs native PB-CDCL core-guided (OLL) optimization on `instance` minimizing
/// `objective`.
///
/// Returns `None` when native OLL does not apply to this objective shape (the
/// objective cannot be normalized into weighted soft literals), so the caller can
/// fall back to the SAT-based path. Otherwise returns a soundness-gated
/// [`OptResult`].
///
/// `should_stop` is polled cooperatively; on a stop request the best incumbent is
/// returned as `Satisfiable`.
///
/// `external_bounds` is the parallel [`SharedBounds`] bus (design §2.7):
/// `Some` only when running as the dedicated parallel worker. The engine READS
/// its `ub` at iteration boundaries as `external_ub_cutoff: Option<i128>` and
/// consumes it ONLY to prune (see the module docs); it never writes the bus.
/// Sequential callers pass `None` (identical pre-bus behavior).
pub(crate) fn solve<F>(
    instance: &PbInstance,
    objective: &PbObjective,
    should_stop: F,
    on_improve: Option<&mut dyn FnMut(i128, &[bool])>,
    external_bounds: Option<&SharedBounds>,
) -> Option<OptResult>
where
    F: FnMut() -> bool,
{
    solve_with_round_core_cap(
        instance,
        objective,
        should_stop,
        on_improve,
        MAX_DISJOINT_CORES_PER_ROUND,
        external_bounds,
    )
}

/// [`solve`] with an explicit per-round disjoint-core cap (`round_core_cap`).
///
/// A cap of `1` (or `0`) reproduces the pre-batching single-core loop exactly:
/// [`process_disjoint_core_round`] delegates to [`process_core`] verbatim in
/// that case, performing no intra-round re-solves. The default entry point uses
/// [`MAX_DISJOINT_CORES_PER_ROUND`]. Split out so the in-file tests can
/// differentially compare the batched and single-core paths.
fn solve_with_round_core_cap<F>(
    instance: &PbInstance,
    objective: &PbObjective,
    mut should_stop: F,
    mut on_improve: Option<&mut dyn FnMut(i128, &[bool])>,
    round_core_cap: usize,
    external_bounds: Option<&SharedBounds>,
) -> Option<OptResult>
where
    F: FnMut() -> bool,
{
    if !objective_range_fits_i64(objective) {
        return None;
    }

    // Normalize the objective into weighted soft selectors + a constant offset.
    let (softs, offset) = normalize_weighted_softs(objective)?;

    // Build the single persistent native solver from the (already relaxed) PBO
    // instance. Use the interruptible constructor so a stop during preprocessing
    // is honored.
    let mut solver = PbCdclSolver::new_interruptible(instance, &mut should_stop);

    // ROOT GF(2) PARITY CUTS (level 0, permanent). For families whose LP
    // relaxation is 0 (e.g. evencolouring) the dual bound is a parity argument,
    // not an LP/Gomory one. Each emitted cut `sum_{j in P} x_j >= 1` is an exact
    // GF(2)/integer consequence of the original equality rows (see the
    // `gf2_parity` module) and is routed through
    // `add_constraint_runtime`, the level-0 gate that performs undefined-var /
    // conflict checks. Soundness is anchored by the brute-force entailment
    // property test in the `gf2_parity` module. Gated behind `AY_PB_PARITY_CUTS`.
    //
    // The returned cuts are ALSO fed to `finish_optimum`'s structural
    // lower-bound computation: a parity cut whose support is exactly the
    // objective ("slacks") is a cardinality row `sum(obj) >= 1` and lifts the
    // sound structural bound to `1` immediately — without forcing OLL to do an
    // expensive totalizer reformulation of a large core. This is sound because
    // the cuts are entailed by the original constraints (they never remove a
    // feasible point), so a lower bound derived from `original ++ cuts` is a
    // valid lower bound on the original objective; `verify_native_optimum` still
    // re-checks the witness against the ORIGINAL constraints only.
    let parity_cuts = inject_root_parity_cuts(&mut solver, instance, objective);

    // Initial feasibility / incumbent: solve with no assumptions.
    let (mut best_assignment, mut best_value) =
        match solver.solve_with_assumptions_interruptible(&[], &mut should_stop) {
            PbCdclAssumptionResult::Satisfiable(model) => {
                let value = eval_objective(objective, &model);
                report(&mut on_improve, value, &model);
                (model, value)
            }
            PbCdclAssumptionResult::Unsatisfiable { .. } => return Some(OptResult::Infeasible),
            PbCdclAssumptionResult::Unknown | PbCdclAssumptionResult::Unsupported => return None,
        };

    if softs.is_empty() {
        // Objective is a pure constant: the incumbent is the optimum at `offset`.
        return Some(finish_optimum(
            instance,
            objective,
            &parity_cuts,
            best_assignment,
            best_value,
            offset,
            &mut should_stop,
        ));
    }

    // PARITY-FLOOR INCUMBENT PROBE. When the entailed parity cuts give a sound
    // structural floor `f` strictly below the current incumbent, try to realize
    // a model at exactly `f` by solving `objective <= f` directly (this is how a
    // good solver closes the evencolouring family: the bound is `1`, so one
    // focused query finds the unique value-1 colouring instead of OLL's slow
    // stratified descent). The probe runs in an ISOLATED fresh solver so a
    // failure can never corrupt the persistent OLL solver, and any model it
    // returns is re-verified against the ORIGINAL constraints before being
    // accepted as the optimum.
    let parity_floor = {
        // `objective_lower_bound_from_constraints` wants a `&dyn Fn()`; wrap the
        // OLL `FnMut` stop in a `RefCell` (same idiom as `lp_relaxation_floor`)
        // and add the process-memory guard so the exact-rational equality
        // aggregation can never grind past MEMLIMIT.
        let stop_cell = std::cell::RefCell::new(&mut should_stop);
        let stop = crate::cdcl::strided_process_memory_stop(|| (stop_cell.borrow_mut())());
        structural_lower_bound_with_parity(instance, objective, &parity_cuts, &stop)
            .unwrap_or(i128::MIN)
    };
    // Only probe when the parity cuts actually apply (non-empty), so we never add
    // a speculative `objective <= floor` query to instances the parity argument
    // does not touch — that keeps the change a strict no-op for the rest of the
    // benchmark set and avoids any regression from wasted probe time.
    if !parity_cuts.is_empty() && parity_floor > i128::MIN && parity_floor < best_value {
        if let Some((model, value)) =
            try_parity_floor_incumbent(instance, objective, parity_floor, &mut should_stop)
        {
            if value < best_value {
                report(&mut on_improve, value, &model);
                best_assignment = model;
                best_value = value;
            }
            // `value <= parity_floor` and `parity_floor` is a sound lower bound,
            // so this incumbent is provably optimal; `finish_optimum` re-verifies.
            if best_value <= parity_floor {
                return Some(finish_optimum(
                    instance,
                    objective,
                    &parity_cuts,
                    best_assignment,
                    best_value,
                    parity_floor,
                    &mut should_stop,
                ));
            }
        }
    }

    // Seed the ADDITIVE lower bound from the constant offset ONLY. The offset is
    // the part of the objective not represented by any soft selector (e.g. the
    // sum of negative-coefficient terms folded into the constant), so the OLL core
    // accumulation `lower_bound = offset + sum(core_weights)` is exact and never
    // double-counts. A stronger constraint-derived bound is NOT folded in here
    // (that would double-count, since OLL adds the same cost on top via cores); it
    // is instead applied as a separate TERMINAL clamp in `finish_optimum`.
    let mut lower_bound = offset.min(best_value);

    // LP-RELAXATION FLOOR. A sound, exact-rational lower bound on the objective
    // from the LP relaxation of the (per-constraint GCD-strengthened) constraints.
    // For proof-complexity-hard cardinality families (e.g. pebbling) the
    // strengthened LP relaxation is integral and EQUALS the integer optimum, so
    // the moment OLL's incremental search reaches a matching incumbent the
    // optimality is proven without the (slow) full stratified core descent — the
    // same mechanism RoundingSat/Exact use to close these instances in
    // milliseconds. It is a STANDALONE floor (never added to core weights, so it
    // cannot double-count) used only for the terminal `best_value <= floor`
    // short-circuit and as a clamp in `finish_optimum`; the optimum witness is
    // always re-verified against the ORIGINAL constraints by `verify_native_optimum`.
    let lp_floor = lp_relaxation_floor(instance, objective, &mut should_stop).unwrap_or(i128::MIN);

    // LP REDUCED-COST VARIABLE FIXING (RoundingSat/Exact's general-OPT edge,
    // OPT-IN via AY_PB_REDUCED_COST). Build the fixer once (GCD-strengthening the
    // constraints) and derive an initial batch of fixings against the root
    // incumbent. Each fixing is a sound, level-0, permanent unit the strong CDCL
    // then propagates; the fix set is re-derived whenever the incumbent improves
    // (the gap shrinks -> more vars fixable). A root conflict means no
    // strictly-better model exists, so the incumbent is optimal. When the gate is
    // OFF the fixer is a no-op on every call (it is a strict no-op for the default
    // benchmark path).
    let mut fixer = ReducedCostFixer::new(instance, &mut should_stop);
    match fixer.refresh(&mut solver, objective, best_value, &mut should_stop) {
        RefreshOutcome::Unchanged => {}
        RefreshOutcome::Improved(model, value) => {
            report(&mut on_improve, value, &model);
            best_assignment = model;
            best_value = value;
        }
        RefreshOutcome::RootClosed => {
            // No strictly-better model than the incumbent exists. The incumbent is
            // optimal at its value; finish_optimum re-verifies against ORIGINAL
            // constraints (its bracket gate enforces correctness).
            return Some(finish_optimum(
                instance,
                objective,
                &parity_cuts,
                best_assignment,
                best_value,
                best_value,
                &mut should_stop,
            ));
        }
    }

    // `parity_floor` (computed above) is a STANDALONE sound lower bound on the
    // objective derived from the original constraints augmented with the entailed
    // parity cuts. Unlike OLL's additive accumulator (`lower_bound`), it is never
    // *added* to core weights, so it cannot double-count. Combine it with the LP
    // floor: both are independently sound lower bounds, so their max is sound. Used
    // only for the terminal `best_value <= floor` short-circuit in the loop below:
    // the moment the incumbent matches this floor we have a proven optimum
    // (re-verified against the ORIGINAL constraints by `finish_optimum`).
    //
    // The reduced-cost LP solves the SAME exact-rational LP the floor uses, so its
    // bound is folded in too (mutable, refreshed alongside the fixings on each
    // incumbent improvement). All these are independently sound lower bounds, so
    // their max is sound.
    //
    // AM1 (at-most-one) CLIQUE FLOOR. A sound pigeonhole lower bound from greedy
    // at-most-one clique extraction over the soft selectors (see
    // [`crate::optimize::am1_bound`]). Like the LP/parity floors it is a STANDALONE
    // sound floor (never added to core weights), combined via `max`, used only for
    // the terminal short-circuit and the `finish_optimum` clamp; the witness is
    // always re-verified against the ORIGINAL constraints.
    //
    // Gated OFF by default (`AY_PB_AM1_BOUND`): on the targeted PB benchmark
    // families the soft selectors are isolated from the base-variable propagation
    // by the big-M relaxation, so single-literal root propagation derives no
    // mutual-exclusion edges and the bound is `0` (a measured no-op that only adds
    // probe cost). The implementation is sound and self-tested; it is retained
    // behind the gate so instances whose selectors DO carry propagation-visible
    // at-most-one structure can opt in without any default-path regression.
    let am1_floor = if am1_bound_enabled() {
        am1_clique_floor(instance, &softs, &mut should_stop).unwrap_or(i128::MIN)
    } else {
        i128::MIN
    };

    // All four floors (parity, LP, reduced-cost LP, AM1 clique) are independently
    // sound lower bounds; their max is sound. `mut` because the reduced-cost LP
    // bound is refreshed alongside the fixings on each incumbent improvement below.
    let mut external_floor = parity_floor
        .max(lp_floor)
        .max(fixer.lp_lower_bound())
        .max(am1_floor);

    // Report the constraint-derived floor immediately: on families where core
    // extraction stalls (measured: 0 cores in 60s on liu/domset while CP-SAT's
    // bool_core found 96 in 300s) this is the only dual the run ever proves,
    // and without it an OPT run that ends SATISFIABLE reports nothing at all.
    {
        let floor = external_floor.min(best_value);
        if let Some(bus) = external_bounds {
            bus.publish_reported_dual(floor);
        }
        if crate::optimize::shared_bounds::publish_reported_dual_global(floor) {
            eprintln!("c dual {floor}");
        }
    }

    // LP-FLOOR INCUMBENT PROBE. When the (exact-rational, cut-strengthened) LP
    // relaxation floor sits strictly below the current incumbent, try to realize a
    // model AT the floor by a single bounded `objective <= floor` query — exactly
    // as the parity-floor probe above does for the parity argument. For the
    // injection/assignment family (injcomp) the LP relaxation is INTEGRAL and equals
    // the integer optimum, so one focused query finds the optimal model directly
    // instead of OLL's slow stratified descent climbing toward it one unit at a time
    // (which times out before proving optimality even though it reached the
    // incumbent). The probe runs in an ISOLATED fresh solver (cannot corrupt the
    // persistent OLL solver) and any model is re-verified against the ORIGINAL
    // constraints before being accepted; optimality holds only because `lp_floor` is
    // an independently sound lower bound, and `finish_optimum` re-verifies once more.
    //
    // REGRESSION SAFETY: the probe is gated to the parity path being absent (so it
    // never duplicates the parity probe above) and is run under a BOUNDED budget
    // (`lp_floor_probe_budget`). When the floor is NOT tight the `objective <= floor`
    // query is UNSAT and could be as hard as the whole problem, so the bounded budget
    // caps the wasted time and OLL FALLS THROUGH to its normal stratified descent
    // with the remaining budget — the worst case is the small probe slice, never the
    // loss of an instance OLL would otherwise have closed.
    if parity_cuts.is_empty() && lp_floor > i128::MIN && lp_floor < best_value && !should_stop() {
        let probe_deadline = std::time::Instant::now() + lp_floor_probe_budget(instance);
        let mut probe_stop = || should_stop() || std::time::Instant::now() >= probe_deadline;
        if let Some((model, value)) =
            try_parity_floor_incumbent(instance, objective, lp_floor, &mut probe_stop)
        {
            if value < best_value {
                report(&mut on_improve, value, &model);
                best_assignment = model;
                best_value = value;
            }
            // `value <= lp_floor` and `lp_floor` is a sound lower bound, so this
            // incumbent is provably optimal; `finish_optimum` re-verifies.
            if best_value <= lp_floor {
                return Some(finish_optimum(
                    instance,
                    objective,
                    &parity_cuts,
                    best_assignment,
                    best_value,
                    lp_floor,
                    &mut should_stop,
                ));
            }
        }
    }

    let mut state = LoopState {
        softs,
        threshold: i128::MAX,
        pending_outputs: std::collections::HashMap::new(),
    };
    state.initialize_threshold();

    // Tightest external-ub prune row installed so far (design §2.7 DOWN-
    // channel); `None` until the bus publishes a cutoff. Only used to avoid
    // re-installing a row the solver already has.
    let mut installed_cutoff: Option<i128> = None;

    loop {
        if best_value <= lower_bound || best_value <= external_floor {
            return Some(finish_optimum(
                instance,
                objective,
                &parity_cuts,
                best_assignment,
                best_value,
                lower_bound.max(external_floor),
                &mut should_stop,
            ));
        }
        if should_stop() {
            return Some(OptResult::Satisfiable(best_assignment, best_value));
        }

        // EXTERNAL UB CUTOFF (design §2.7 DOWN-channel), polled at this
        // iteration boundary. Wait-free `Relaxed` bus read; an absent or
        // overflow-rejected bus ub reads as `None` == NO CUTOFF (never
        // "0/unbounded-good"), and the i64 transport value is losslessly
        // widened to i128 inside the bus (never `as`-cast).
        //
        // CONSUMED ONLY TO PRUNE: installed as the extra bound
        // `objective <= cutoff` in the persistent solver. Soundness: the bus
        // ub is the exact objective value of a coordinator-VERIFIED feasible
        // model, so `optimum <= cutoff` — every OPTIMAL model satisfies the
        // row, installing it removes no optimal point, all solver models
        // remain models of the ORIGINAL constraints (the row only restricts),
        // and the OLL core lower bound stays a sound GLOBAL lower bound
        // (cores now reason over a space that still contains every optimal
        // model). It NEVER overwrites `best_value` — the engine's returned
        // pair stays its OWN witness (the §2.7 desync fix); incumbents still
        // only ever come from the engine's own models.
        //
        // SINGLE-STRATUM SKIP (measured 2026-07-28). At a FULL stratum the
        // assumption set forces `objective == lower_bound`, and
        // `lower_bound <= optimum <= cutoff` always holds, so the row is
        // ENTAILED by the assumptions and can prune nothing — it is dead weight
        // in every propagation and every conflict resolution.
        //
        // On a unit-weight objective (this domset family: 467/467 unit terms)
        // `initialize_threshold` makes max weight == min weight, so
        // `collect_stratum_assumptions` reports a full stratum from iteration 1
        // and the row is NEVER able to bite. Measured cost of installing it
        // anyway, 90s per arm on `domset ..._mw19_19`:
        //     no cutoff        -> dual 127
        //     cutoff 177       -> dual 65
        //     cutoff 140       -> dual 65
        //     cutoff 230       -> dual 65   (near-vacuous vs the engine's own
        //                                    best of 237 — the CONTROL)
        // The vacuous arm costing exactly as much as the tight one shows the
        // damage is the 467-term dense row itself, not the strength of the
        // bound. This crippled the one bus consumer (`native-oll-opt`, the
        // FULL-budget worker) to the parity floor on every default parallel
        // run, which is why the parallel dual (124) trailed the bus-free
        // sequential pre-pass (127).
        //
        // The row is still installed for genuinely multi-stratum (weighted)
        // objectives, where a partial stratum does not pin the objective and
        // the cutoff can legitimately prune.
        let external_ub_cutoff: Option<i128> = external_bounds.and_then(SharedBounds::ub);
        // CANARY (kept even when the row is skipped). The `Conflict` arm below
        // used to be the only in-engine signal that the bus ub sits BELOW the
        // true optimum — a poisoned bus. Skipping the row would silence it, so
        // check the same invariant directly and cheaply: a bus ub must never be
        // below a bound we have already PROVEN.
        if let Some(ub) = external_ub_cutoff {
            debug_assert!(
                ub >= lower_bound,
                "poisoned bus: ub {ub} < proven lower bound {lower_bound}"
            );
        }
        if let Some(cutoff) = external_cutoff_row_wanted(
            external_ub_cutoff.filter(|_| state.stratification_enabled()),
            best_value,
            installed_cutoff,
        ) {
            // A row-construction overflow (`Err`) is treated as NO CUTOFF.
            if let Ok(row) = objective_at_most_constraint(objective, cutoff) {
                match solver.add_constraint_runtime(&row) {
                    RuntimeConstraintOutcome::Added => installed_cutoff = Some(cutoff),
                    RuntimeConstraintOutcome::Conflict => {
                        // A root conflict here is impossible with a valid
                        // bus (a verified model AT the cutoff exists and
                        // satisfies every solver row). FAIL-CLOSED
                        // early-exit with the engine's OWN consistent
                        // (model, value) pair — never a claim derived
                        // from the conflicted solver state.
                        return Some(OptResult::Satisfiable(best_assignment, best_value));
                    }
                    // Could not add (e.g. proof logging on): no prune,
                    // identical pre-bus behavior.
                    RuntimeConstraintOutcome::Unsupported => {}
                }
            }
        }
        if state.softs.is_empty() {
            return Some(finish_optimum(
                instance,
                objective,
                &parity_cuts,
                best_assignment,
                best_value,
                lower_bound.max(external_floor),
                &mut should_stop,
            ));
        }

        // HARDENING: any soft whose weight exceeds the proven gap cannot be paid
        // in a strictly-better model, so fix it to its no-cost polarity as a unit
        // constraint. Soundness identical to the SAT-OLL hardening argument.
        if !harden_softs(&mut solver, &mut state, lower_bound, best_value) {
            return Some(OptResult::Satisfiable(best_assignment, best_value));
        }
        if state.softs.is_empty() {
            return Some(finish_optimum(
                instance,
                objective,
                &parity_cuts,
                best_assignment,
                best_value,
                lower_bound.max(external_floor),
                &mut should_stop,
            ));
        }

        // STRATIFICATION: assume only softs at or above the current threshold at
        // their no-cost polarity. `at_full_stratum` is true when every remaining
        // soft is included; only then can SAT certify optimality.
        let (assumptions, at_full_stratum) = state.collect_stratum_assumptions();

        match solver.solve_with_assumptions_interruptible(&assumptions, &mut should_stop) {
            PbCdclAssumptionResult::Satisfiable(model) => {
                let value = eval_objective(objective, &model);
                if value < best_value {
                    best_assignment = model;
                    best_value = value;
                    report(&mut on_improve, best_value, &best_assignment);
                    // INCUMBENT IMPROVED: the gap shrank, so re-derive reduced-cost
                    // fixings (more variables may now be fixable) and let them drive
                    // the incumbent down via a focused re-solve. No-op when the gate
                    // is off.
                    match fixer.refresh(&mut solver, objective, best_value, &mut should_stop) {
                        RefreshOutcome::Unchanged => {}
                        RefreshOutcome::Improved(m, v) => {
                            best_assignment = m;
                            best_value = v;
                            report(&mut on_improve, best_value, &best_assignment);
                        }
                        RefreshOutcome::RootClosed => {
                            return Some(finish_optimum(
                                instance,
                                objective,
                                &parity_cuts,
                                best_assignment,
                                best_value,
                                best_value,
                                &mut should_stop,
                            ));
                        }
                    }
                    // The re-derived LP bound may have tightened; fold it in.
                    external_floor = external_floor.max(fixer.lp_lower_bound());
                }
                if at_full_stratum {
                    return Some(finish_optimum(
                        instance,
                        objective,
                        &parity_cuts,
                        best_assignment,
                        best_value,
                        lower_bound.max(external_floor),
                        &mut should_stop,
                    ));
                }
                state.lower_threshold();
            }
            PbCdclAssumptionResult::Unsatisfiable { core } => {
                // DISJOINT-CORE ROUND: rather than process this single core and
                // re-solve from scratch (lower_bound += one core_weight per
                // re-solve), collect a batch of pairwise-disjoint cores at this
                // stratum and apply them all, so lower_bound jumps by Σ
                // core_weights in one round. Disjointness (enforced by dropping
                // each claimed core's softs before the next intra-round solve)
                // makes the sum an exact, non-overcounting lower bound. See
                // `process_disjoint_core_round` for the soundness argument.
                match process_disjoint_core_round(
                    &mut solver,
                    &mut state,
                    &mut lower_bound,
                    &assumptions,
                    core,
                    round_core_cap,
                    &mut should_stop,
                ) {
                    CoreOutcome::Continue => {}
                    CoreOutcome::Stop => {
                        return Some(OptResult::Satisfiable(best_assignment, best_value));
                    }
                    CoreOutcome::Exhausted => {
                        if at_full_stratum {
                            return Some(finish_optimum(
                                instance,
                                objective,
                                &parity_cuts,
                                best_assignment,
                                best_value,
                                lower_bound.max(external_floor),
                                &mut should_stop,
                            ));
                        }
                        state.lower_threshold();
                    }
                }
                // TELEMETRY ONLY (see `SharedBounds::publish_reported_dual`):
                // surface how far core-guided reasoning has driven the dual, so
                // an OPT run that ends SATISFIABLE still reports what it proved.
                // Clamped to `best_value` because this accumulator is a floor
                // over the CURRENT solver state — hardening, the external-UB
                // prune row and (opt-in) reduced-cost fixings can all push it
                // past the true optimum, and the clamp keeps the printed number
                // inside `[.., incumbent]` where it is meaningful. It licenses
                // nothing: the bus routes it away from `lb`, which is the only
                // value the OPTIMUM upgrade reads.
                let reported = lower_bound.max(external_floor).min(best_value);
                if let Some(bus) = external_bounds {
                    bus.publish_reported_dual(reported);
                }
                {
                    if crate::optimize::shared_bounds::publish_reported_dual_global(reported) {
                        // STDERR, and only on improvement. The PB competition
                        // verdict is read from STDOUT, so this cannot perturb a
                        // result; it exists because an OPT run that ends
                        // SATISFIABLE currently reports nothing about how far it
                        // drove the dual, which makes the dual side of the
                        // search unmeasurable from outside.
                        eprintln!("c dual {reported}");
                    }
                }
                if should_stop() {
                    return Some(OptResult::Satisfiable(best_assignment, best_value));
                }
            }
            PbCdclAssumptionResult::Unknown | PbCdclAssumptionResult::Unsupported => {
                return Some(OptResult::Satisfiable(best_assignment, best_value));
            }
        }
    }
}

fn report(on_improve: &mut Option<&mut dyn FnMut(i128, &[bool])>, value: i128, model: &[bool]) {
    if let Some(cb) = on_improve.as_mut() {
        cb(value, model);
    }
}

/// PURE decision core for the external-ub prune row (design §2.7 DOWN-channel;
/// unit-tested): returns the cutoff to install as `objective <= cutoff`, or
/// `None` when nothing should be installed at this iteration boundary.
///
/// * `cutoff` is the polled bus ub. `None` — bus absent, never published, or
///   the value was overflow-REJECTED at the i128->i64 boundary — means **no
///   cutoff** (never "0/unbounded-good").
/// * Install only when strictly informative: tighter than the engine's OWN
///   incumbent (a row at `>= best_value` cannot prune anything the incumbent
///   has not already bounded) and tighter than any row already installed
///   (`installed`), so re-polls of an unchanged bus are free.
fn external_cutoff_row_wanted(
    cutoff: Option<i128>,
    best_value: i128,
    installed: Option<i128>,
) -> Option<i128> {
    let cutoff = cutoff?;
    (cutoff < best_value && installed.is_none_or(|prev| cutoff < prev)).then_some(cutoff)
}

/// Whether the GF(2) parity-cut root injection is enabled.
///
/// Default is **ON** (the cuts are fully sound — every emitted cut is brute-force
/// entailment-tested — and only ever tighten the dual bound). Set
/// `AY_PB_PARITY_CUTS` to one of `0|false|no|off` to disable; any other value (or
/// an unset variable) keeps it on.
fn parity_cuts_enabled() -> bool {
    fn disabled(value: &OsStr) -> bool {
        value.to_str().is_some_and(|value| {
            matches!(
                value.trim().to_ascii_lowercase().as_str(),
                "0" | "false" | "no" | "off"
            )
        })
    }
    match std::env::var_os(PARITY_CUTS_ENV) {
        Some(value) => !disabled(&value),
        None => true,
    }
}

/// Environment gate for the AM1 (at-most-one) clique lower bound. Default **OFF**:
/// see the call site in [`solve`] for why (the bound is a measured no-op on the
/// current PB benchmark families). Set `AY_PB_AM1_BOUND` to one of `1|true|yes|on`
/// to enable.
const AM1_BOUND_ENV: &str = "AY_PB_AM1_BOUND";

fn am1_bound_enabled() -> bool {
    fn enabled(value: &OsStr) -> bool {
        value.to_str().is_some_and(|value| {
            matches!(
                value.trim().to_ascii_lowercase().as_str(),
                "1" | "true" | "yes" | "on"
            )
        })
    }
    match std::env::var_os(AM1_BOUND_ENV) {
        Some(value) => enabled(&value),
        None => false,
    }
}

/// Computes the AM1 (at-most-one) clique lower bound over the soft selectors as a
/// STANDALONE sound floor on the objective.
///
/// Builds a fresh native solver over the instance and runs greedy at-most-one
/// clique extraction certified by root unit-propagation (see
/// [`crate::optimize::am1_bound`]). Returns `None` when the technique does not
/// apply (no clique structure / interrupted). The returned value is always a
/// sound floor: it never exceeds the cost of any feasible assignment (the witness
/// is independently re-verified against the ORIGINAL constraints in
/// `finish_optimum`).
fn am1_clique_floor<F>(
    instance: &PbInstance,
    softs: &[WeightedSoft],
    should_stop: &mut F,
) -> Option<i128>
where
    F: FnMut() -> bool,
{
    if softs.is_empty() || should_stop() {
        return None;
    }
    let am1_softs: Vec<crate::optimize::am1_bound::Am1Soft> = softs
        .iter()
        .map(|s| crate::optimize::am1_bound::Am1Soft {
            literal: s.literal,
            weight: s.weight,
        })
        .collect();
    crate::optimize::am1_bound::am1_clique_lower_bound_for_instance(instance, &am1_softs, || {
        should_stop()
    })
}

/// Derives GF(2) parity cuts from the instance's equality rows and injects each
/// as a permanent root constraint via the level-0 [`PbCdclSolver::add_constraint_runtime`]
/// gate.
///
/// # Soundness
/// Every cut is an exact GF(2)/integer consequence of the original equality
/// constraints (`sum_{j in P} x_j >= 1` derived from an all-cancel row
/// combination with odd combined RHS); see
/// [`gf2_parity_cuts_preferring`](crate::optimize::gf2_parity::gf2_parity_cuts_preferring)
/// and its brute-force entailment property test. `add_constraint_runtime` is the
/// authoritative gate: it rejects (returns `Unsupported`) under proof logging,
/// above decision level 0, or for any out-of-range literal, and reports a
/// level-0 `Conflict` if a cut closes the root — all handled here without
/// affecting correctness. A root conflict simply means the parity argument
/// already proved infeasibility; the subsequent solve will surface it as UNSAT.
///
/// Returns the derived cuts so the caller can also fold them into the structural
/// lower-bound computation in [`finish_optimum`]. When disabled or when no cut is
/// derivable, returns an empty vector.
fn inject_root_parity_cuts(
    solver: &mut PbCdclSolver,
    instance: &PbInstance,
    objective: &PbObjective,
) -> Vec<PbConstraint> {
    if !parity_cuts_enabled() {
        return Vec::new();
    }
    // Prefer eliminating non-objective columns first so residual cuts concentrate
    // on the objective variables (ideally yielding `sum(obj) >= 1`), which lifts
    // the structural lower bound directly.
    let mut preferred: Vec<u32> = objective
        .terms
        .iter()
        .flat_map(|term| term.lits.iter().map(|lit| lit.var))
        .collect();
    preferred.sort_unstable();
    preferred.dedup();
    let cuts = gf2_parity_cuts_preferring(&instance.constraints, instance.num_vars, &preferred);
    for cut in &cuts {
        // The outcome is intentionally not propagated upward: `Added` and
        // `Conflict` both leave the solver in a sound state (a conflict means the
        // root is closed and the next solve reports UNSAT), and `Unsupported`
        // means the cut was not installed (no soundness impact). We stop early on
        // a conflict since further cuts cannot change the now-closed root.
        match solver.add_constraint_runtime(cut) {
            RuntimeConstraintOutcome::Conflict => break,
            RuntimeConstraintOutcome::Added | RuntimeConstraintOutcome::Unsupported => {}
        }
    }
    cuts
}

/// Mutable per-round loop state (the stratification threshold and the active soft
/// set with residual weights). The persistent solver is threaded separately.
struct LoopState {
    softs: Vec<WeightedSoft>,
    threshold: i128,
    /// NODE ABSTRACTION (lazy totalizer output activation).
    ///
    /// A core of size `k` reformulates into totalizer outputs
    /// `o_2..o_k` (`o_j` = "at least `j` of this core are paid"). Registering
    /// all of them as softs immediately floods the active set: every one joins
    /// every subsequent assumption set, and the stratum query is exactly what
    /// gets expensive as the search deepens.
    ///
    /// Only the FRONTMOST output is registered up front. The rest wait here,
    /// keyed by the literal whose exhaustion unlocks the next one, so the ladder
    /// is climbed one rung at a time and only as far as the search actually
    /// needs. The bound is unaffected — `o_j` cannot be paid before `o_{j-1}` —
    /// but the assumption sets stay small.
    ///
    /// The stored weight is the weight of the core that BUILT the ladder, not
    /// of whatever core later consumes a rung: charging the consumer's weight
    /// would over-count.
    pending_outputs: std::collections::HashMap<PbLit, (Vec<PbLit>, i128)>,
}

impl LoopState {
    fn stratification_enabled(&self) -> bool {
        let mut min_w = i128::MAX;
        let mut max_w = i128::MIN;
        for soft in &self.softs {
            min_w = min_w.min(soft.weight);
            max_w = max_w.max(soft.weight);
        }
        max_w.saturating_sub(min_w) >= 1
    }

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

    /// Returns the no-cost-polarity assumptions for every soft at or above the
    /// current threshold, plus whether the stratum is full (all remaining softs).
    fn collect_stratum_assumptions(&mut self) -> (Vec<PbLit>, bool) {
        let mut assumptions = Vec::with_capacity(self.softs.len());
        for soft in &self.softs {
            if soft.weight >= self.threshold {
                assumptions.push(complement(soft.literal));
            }
        }
        if assumptions.is_empty() {
            // Threshold overshot every remaining soft; collapse to the minimum so
            // the stratum is full.
            self.threshold = self.min_soft_weight();
            assumptions.extend(self.softs.iter().map(|s| complement(s.literal)));
            return (assumptions, true);
        }
        let full = assumptions.len() == self.softs.len();
        (assumptions, full)
    }

    /// CASHWMaxSAT diminishing threshold descent (mirrors the SAT-OLL schedule).
    fn lower_threshold(&mut self) {
        let min_w = self.min_soft_weight();
        if self.threshold <= min_w {
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
        next = next.min(self.threshold.saturating_sub(1)).max(min_w);
        self.threshold = next;
    }
}

/// Hardens softs whose weight exceeds the proven gap. Returns `false` only if a
/// hardening unit makes the solver UNSAT at level 0 (no strictly-better model
/// exists); the caller then returns the incumbent as `Satisfiable`.
fn harden_softs(
    solver: &mut PbCdclSolver,
    state: &mut LoopState,
    lower_bound: i128,
    best_value: i128,
) -> bool {
    let Some(gap) = best_value.checked_sub(lower_bound) else {
        return true;
    };
    if gap < 0 {
        return true;
    }
    let mut idx = 0;
    while idx < state.softs.len() {
        if state.softs[idx].weight > gap {
            let soft = state.softs.swap_remove(idx);
            // Force the soft to its no-cost (complemented) polarity as a unit PB
            // constraint `complement(soft) >= 1`.
            match solver.add_cardinality_runtime(&[complement(soft.literal)], 1) {
                RuntimeConstraintOutcome::Added => {}
                RuntimeConstraintOutcome::Conflict => {
                    // No model leaves every hardened soft unpaid -> no strictly
                    // better model. Stop; the bracket gate (not hardening) decides
                    // optimality.
                    return false;
                }
                RuntimeConstraintOutcome::Unsupported => {
                    // Could not add the unit; conservatively stop.
                    return false;
                }
            }
        } else {
            idx += 1;
        }
    }
    true
}

/// Processes one extracted UNSAT core: trims it, raises the lower bound by the
/// realized core weight, performs weight-split bookkeeping, and registers the
/// totalizer relaxation outputs (thresholds >= 2) as new soft selectors.
fn process_core<F>(
    solver: &mut PbCdclSolver,
    state: &mut LoopState,
    lower_bound: &mut i128,
    core: Vec<PbLit>,
    should_stop: &mut F,
) -> CoreOutcome
where
    F: FnMut() -> bool,
{
    let trimmed = trim_core(solver, core, should_stop);
    let core_softs: HashSet<PbLit> = trimmed.into_iter().map(complement).collect();
    apply_trimmed_core(solver, state, lower_bound, core_softs, should_stop)
}

/// Applies an already-trimmed core (given as the set of its SOFT selector
/// literals, i.e. the complements of the core's assumption literals): raises the
/// lower bound by the realized core weight, performs weight-split bookkeeping,
/// and registers the totalizer relaxation outputs (thresholds >= 2) as new soft
/// selectors.
///
/// Split out of [`process_core`] so the disjoint-core round can trim each core
/// ONCE (during collection, to identify its softs for the disjointness
/// invariant) and then apply it here without a redundant second trim pass.
fn apply_trimmed_core<F>(
    solver: &mut PbCdclSolver,
    state: &mut LoopState,
    lower_bound: &mut i128,
    core_softs: HashSet<PbLit>,
    should_stop: &mut F,
) -> CoreOutcome
where
    F: FnMut() -> bool,
{
    if core_softs.is_empty() {
        return CoreOutcome::Exhausted;
    }

    let Some(core_weight) = state
        .softs
        .iter()
        .filter(|soft| core_softs.contains(&soft.literal))
        .map(|soft| soft.weight)
        .min()
    else {
        // The core referenced no currently-active soft (already exhausted by a
        // prior round). Treat as exhausted rather than as progress.
        return CoreOutcome::Exhausted;
    };
    if core_weight <= 0 {
        return CoreOutcome::Stop;
    }

    let relax_lits: Vec<PbLit> = state
        .softs
        .iter()
        .filter(|soft| core_softs.contains(&soft.literal))
        .map(|soft| soft.literal)
        .collect();

    // LB increase == realized core weight, exactly (checked).
    let Some(next_lb) = lower_bound.checked_add(core_weight) else {
        return CoreOutcome::Stop;
    };
    *lower_bound = next_lb;

    // Weight-split (WCE): decrement the core softs and drop the exhausted ones.
    for soft in &mut state.softs {
        if core_softs.contains(&soft.literal) {
            soft.weight = soft.weight.saturating_sub(core_weight);
        }
    }
    // Climb the ladder: a soft that just reached zero weight has been fully
    // paid, so its successor output becomes reachable and is registered now.
    let exhausted: Vec<PbLit> = state
        .softs
        .iter()
        .filter(|soft| soft.weight <= 0)
        .map(|soft| soft.literal)
        .collect();
    state.softs.retain(|soft| soft.weight > 0);
    for literal in exhausted {
        let Some((mut rest, weight)) = state.pending_outputs.remove(&literal) else {
            continue;
        };
        if rest.is_empty() {
            continue;
        }
        let next = rest.remove(0);
        // Weight comes from the LADDER, never from the consuming core.
        state.softs.push(WeightedSoft {
            literal: next,
            weight,
        });
        if !rest.is_empty() {
            state.pending_outputs.insert(next, (rest, weight));
        }
    }

    // Build an incremental totalizer over the core's relaxation literals and
    // register the higher-threshold outputs (>= 2 paid) as new soft selectors of
    // weight `core_weight`.
    if relax_lits.len() >= 2 {
        let Some(outputs) = encode_incremental_totalizer(solver, &relax_lits, should_stop) else {
            return CoreOutcome::Stop;
        };
        let ladder: Vec<PbLit> = outputs
            .into_iter()
            .filter(|(threshold, _)| *threshold >= 2)
            .map(|(_, lit)| lit)
            .collect();
        if let Some((&front, rest)) = ladder.split_first().map(|(f, r)| (f, r.to_vec())) {
            state.softs.push(WeightedSoft {
                literal: front,
                weight: core_weight,
            });
            if !rest.is_empty() {
                state.pending_outputs.insert(front, (rest, core_weight));
            }
        }
    }

    CoreOutcome::Continue
}

/// Default maximum number of disjoint cores collected in a single extraction
/// round before falling through to process them. A safety valve so a
/// pathological stratum with thousands of tiny singleton cores cannot make one
/// round spin unbounded; the remaining cores are picked up by the next round's
/// re-solve. Generous enough that realistic strata extract all their disjoint
/// cores in one round. A cap of `1` reproduces the pre-batching single-core
/// loop exactly (see [`process_disjoint_core_round`]).
const MAX_DISJOINT_CORES_PER_ROUND: usize = 4096;

/// Wall-clock budget for ONE disjoint-core round.
///
/// The count cap alone does not bound a round's cost: each additional core
/// costs an intra-round assumption solve PLUS up to [`MAX_CORE_TRIM_CHECKS`]
/// trimming solves, and those solves get harder as the stratum tightens. With
/// the cap at 4096 a single round can issue >100k solves.
///
/// Measured on `domset ..._mw19_19` before this budget existed, the rounds ran
/// 32ms, 101ms, **12.6s**, **85.2s** — i.e. the engine spent whole minutes
/// inside one round and the reported dual sat frozen at the parity floor while
/// it did. Core-guided search wants MANY ratcheting rounds, not one enormous
/// one: every applied core raises `lower_bound` immediately, so finishing a
/// round early and re-solving strictly dominates stalling inside it.
///
/// Cutting a round short is purely a scheduling decision — every core already
/// collected is still applied, and each is independently valid — so this
/// bounds latency without touching the bound's soundness.
const DISJOINT_CORE_ROUND_BUDGET: std::time::Duration = std::time::Duration::from_millis(500);

/// DISJOINT-CORE EXTRACTION ROUND.
///
/// Given the stratum's `base_assumptions` (no-cost-polarity literals for every
/// soft at/above the current threshold) and the FIRST UNSAT `first_core`
/// already returned by the caller's solve, collect a batch of up to
/// `round_core_cap` **pairwise-disjoint** UNSAT cores at this stratum, then
/// apply them all so the lower bound jumps by the SUM of their core weights in
/// one round (instead of `+min_weight` per full re-solve — the documented
/// bound-crawl bottleneck on weighted families).
///
/// # Fail-toward-baseline
/// `round_core_cap <= 1` delegates to [`process_core`] verbatim: no intra-round
/// re-solves, byte-identical behavior to the pre-batching single-core loop.
///
/// # Method
/// After trimming the first core and recording its soft selectors, repeatedly:
///   1. Remove EVERY already-claimed soft's assumption literal from
///      `base_assumptions`.
///   2. Re-solve under that reduced assumption set.
///   3. On UNSAT, trim the new core and record it; on SAT/Unknown/stop/empty
///      stop collecting.
/// Finally [`apply_trimmed_core`] each collected core (raising the bound,
/// relaxing via the incremental totalizer) exactly as the single-core path does.
///
/// # Soundness — the disjointness invariant (crux)
/// A core returned by `solve_with_assumptions_interruptible` is always a SUBSET
/// of the assumption literals it was given (and deletion trimming only ever
/// shrinks it). Before each re-solve we DELETE the assumption literals of all
/// previously-claimed softs from the assumption set, so a newly returned core
/// literally cannot contain any claimed soft — every collected core is pairwise
/// disjoint over the soft selectors **by construction**. (A redundant explicit
/// `retain` guard drops any unexpected overlap, failing closed.) Disjoint cores
/// assert independent lower-bound facts — "at least one soft in C_i must be
/// paid" for each i over non-overlapping soft sets — so the costs are additive:
/// Σ core_weight_i is a valid lower bound that CANNOT overcount, because no
/// single paid soft is charged toward two different cores. Each
/// [`apply_trimmed_core`] then performs the SAME exact, checked
/// `lower_bound += core_weight` and totalizer relaxation (including the WCE
/// weight-split) the one-core path uses; applying core B after core A stays
/// valid because A's reformulation only ADDS implied constraints over fresh
/// variables (B remains a core of the augmented formula) and, by disjointness,
/// A's weight-split never touches B's softs (B's realized min-weight at apply
/// time equals its min-weight at collection time). The only change relative to
/// the single-core path is that several disjoint cores are accumulated per
/// round. This construction was implemented and independently
/// soundness-verified once before (git 6ce3c564; reverted in 397799c6 purely
/// for lack of a demonstrated A/B win at a 60s budget, NOT for any soundness
/// issue).
fn process_disjoint_core_round<F>(
    solver: &mut PbCdclSolver,
    state: &mut LoopState,
    lower_bound: &mut i128,
    base_assumptions: &[PbLit],
    first_core: Vec<PbLit>,
    round_core_cap: usize,
    should_stop: &mut F,
) -> CoreOutcome
where
    F: FnMut() -> bool,
{
    // FAIL TOWARD THE BASELINE: a cap of 1 (or 0) IS the pre-batching
    // single-core path — delegate to it verbatim so the equivalence holds by
    // construction, not by argument.
    if round_core_cap <= 1 {
        return process_core(solver, state, lower_bound, first_core, should_stop);
    }

    // The round clock starts BEFORE the first core's trim, not after it. It used
    // to start below, which left that trim — up to `MAX_CORE_TRIM_CHECKS` full
    // assumption solves — running against the raw global stop, entirely outside
    // the very budget whose stated purpose is to bound round latency.
    let round_started = std::time::Instant::now();

    // Trim the first core and record its softs. An empty trimmed core means the
    // stratum is exhausted (matches the one-core path's `Exhausted`).
    let first_trimmed = {
        let mut first_trim_stop =
            || round_started.elapsed() >= DISJOINT_CORE_ROUND_BUDGET || should_stop();
        trim_core(solver, first_core, &mut first_trim_stop)
    };
    let first_softs: HashSet<PbLit> = first_trimmed.into_iter().map(complement).collect();
    if first_softs.is_empty() {
        return CoreOutcome::Exhausted;
    }

    // `claimed` = union of all collected cores' softs (the disjointness ledger).
    let mut claimed: HashSet<PbLit> = first_softs.clone();
    let mut collected: Vec<HashSet<PbLit>> = vec![first_softs];

    // The budget must bind INSIDE the solves, not only between them. Checking it
    // in the loop condition alone leaves a single hard intra-round query free to
    // run forever: measured on `domset ..._mw19_19`, the dual reached 125 in 6.9s
    // and then one such query consumed the remaining 83s of a 90s run without
    // returning. Wrapping the stop closure makes every intra-round solve — and
    // every trimming solve beneath it — honour the same deadline, so the round
    // ends with the cores it has instead of hanging.
    let round_stop = |elapsed: &mut dyn FnMut() -> bool| {
        round_started.elapsed() >= DISJOINT_CORE_ROUND_BUDGET || elapsed()
    };
    while collected.len() < round_core_cap
        && !round_stop(&mut *should_stop)
        && round_started.elapsed() < DISJOINT_CORE_ROUND_BUDGET
    {
        // Reduced assumption set: drop every assumption literal whose underlying
        // soft has already been claimed. (Assumption literals are
        // `complement(soft.literal)`, so an assumption `a` is claimed iff
        // `complement(a)` is in `claimed`.) Because the new core must be a
        // subset of THIS set, it cannot reference any claimed soft -> disjoint
        // by construction.
        let reduced: Vec<PbLit> = base_assumptions
            .iter()
            .copied()
            .filter(|&a| !claimed.contains(&complement(a)))
            .collect();
        if reduced.is_empty() {
            break;
        }

        let mut bounded = || round_stop(&mut *should_stop);
        match solver.solve_with_assumptions_interruptible(&reduced, &mut bounded) {
            PbCdclAssumptionResult::Unsatisfiable { core } => {
                let mut bounded = || round_stop(&mut *should_stop);
                let trimmed = trim_core(solver, core, &mut bounded);
                let mut softs: HashSet<PbLit> = trimmed.into_iter().map(complement).collect();
                if softs.is_empty() {
                    // No more cores reachable under the reduced set.
                    break;
                }
                // Redundant disjointness guard (fail-closed): the construction
                // already guarantees no overlap, but if any claimed soft somehow
                // appears, drop it so the recorded core stays strictly disjoint.
                softs.retain(|s| !claimed.contains(s));
                if softs.is_empty() {
                    break;
                }
                for s in &softs {
                    claimed.insert(*s);
                }
                collected.push(softs);
            }
            // SAT: no further disjoint core exists at this stratum under the
            // reduced assumptions. Unknown/Unsupported: stop collecting and
            // apply what we have (each collected core is independently sound).
            PbCdclAssumptionResult::Satisfiable(_)
            | PbCdclAssumptionResult::Unknown
            | PbCdclAssumptionResult::Unsupported => break,
        }
    }

    // Apply every collected (pairwise-disjoint) core. Each contributes its exact
    // realized weight to the lower bound and its own totalizer relaxation.
    // Soundness is per-core identical to the one-core path; disjointness makes
    // the sum exact.
    let mut applied_any = false;
    for core_softs in collected {
        match apply_trimmed_core(solver, state, lower_bound, core_softs, should_stop) {
            CoreOutcome::Continue => applied_any = true,
            // A degenerate collected core (its softs already consumed by a prior
            // apply in THIS batch via weight-split, or zero residual) is treated
            // as a no-op; keep applying the rest.
            CoreOutcome::Exhausted => {}
            // Hard failure (overflow / encoding / non-positive weight): bail out
            // of the whole optimization with the incumbent (sound).
            CoreOutcome::Stop => return CoreOutcome::Stop,
        }
    }

    if applied_any {
        CoreOutcome::Continue
    } else {
        CoreOutcome::Exhausted
    }
}

/// Deletion-based core trimming over the native solver (mirrors the SAT-OLL
/// `trim_assumption_core`). Drops a core literal if the remaining literals are
/// still an UNSAT core. Sound: only ever returns a subset that is itself a core.
fn trim_core<F>(solver: &mut PbCdclSolver, mut core: Vec<PbLit>, should_stop: &mut F) -> Vec<PbLit>
where
    F: FnMut() -> bool,
{
    if core.len() <= 1 || core.len() > MAX_CORE_TRIM_SIZE {
        return core;
    }
    let mut checks = 0usize;
    let mut idx = 0usize;
    while idx < core.len() && checks < MAX_CORE_TRIM_CHECKS {
        if should_stop() {
            break;
        }
        let mut candidate = Vec::with_capacity(core.len().saturating_sub(1));
        candidate.extend_from_slice(&core[..idx]);
        candidate.extend_from_slice(&core[idx + 1..]);
        checks += 1;

        match solver.solve_with_assumptions_interruptible(&candidate, &mut *should_stop) {
            PbCdclAssumptionResult::Unsatisfiable { core: refined } => {
                // Adopt the solver's refined core when it is strictly smaller.
                // Before the true-core fix this was always identical to
                // `candidate` (the assumption prefix); now that conflict
                // analysis is real, one solve can drop several literals at once
                // instead of exactly the one we removed.
                if refined.len() < candidate.len() {
                    core = refined;
                    idx = 0;
                } else {
                    core = candidate;
                }
            }
            PbCdclAssumptionResult::Satisfiable(_) => {
                idx += 1;
            }
            PbCdclAssumptionResult::Unknown | PbCdclAssumptionResult::Unsupported => break,
        }
    }
    core
}

/// Encodes a unit-coefficient cardinality totalizer over `inputs` into the live
/// native solver, allocating fresh aux variables via [`PbCdclSolver::new_var`]
/// and emitting each totalizer clause as an incremental PB constraint.
///
/// Reuses the tested generalized-totalizer encoder (same one the SAT-OLL path
/// uses); every emitted clause is an implied consequence of the counting
/// semantics. Returns `(threshold, output_lit)` pairs where `output_lit` is true
/// iff at least `threshold` of `inputs` are true, in ascending threshold order.
///
/// Returns `None` on interruption, overflow, or any failed runtime add.
fn encode_incremental_totalizer<F>(
    solver: &mut PbCdclSolver,
    inputs: &[PbLit],
    should_stop: &mut F,
) -> Option<Vec<(i128, PbLit)>>
where
    F: FnMut() -> bool,
{
    let n = inputs.len();
    if n == 0 {
        return Some(Vec::new());
    }
    let rhs = i128::try_from(n).ok()?;
    let placeholder_count = u32::try_from(n).ok()?;
    let coeffs = vec![1i128; n];
    let lits: Vec<i32> = (1..=placeholder_count).map(|v| v as i32).collect();

    let mut clauses: Vec<Vec<i32>> = Vec::new();
    let mut next_var = placeholder_count.checked_add(1)?;
    let mut stop = || should_stop();
    let outputs = encode_totalizer_with_outputs_interruptible(
        &coeffs,
        &lits,
        rhs,
        &mut clauses,
        &mut next_var,
        &mut stop,
    )?;

    // Aux variables (DIMACS index > placeholder_count) -> fresh native vars.
    let aux_count = next_var.checked_sub(placeholder_count)?;
    let aux_len = usize::try_from(aux_count).ok()?;
    let mut aux_vars: Vec<u32> = Vec::with_capacity(aux_len);
    for _ in 0..aux_len {
        aux_vars.push(solver.new_var()?);
    }

    // Map a placeholder DIMACS literal to a native PbLit. Magnitudes
    // `1..=placeholder_count` map onto `inputs`; larger ones map onto `aux_vars`.
    let map = |dimacs: i32| -> Option<PbLit> {
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
            let aux_var = *aux_vars.get(aux_idx)?;
            PbLit {
                var: aux_var,
                negated: false,
            }
        };
        Some(if dimacs > 0 { base } else { complement(base) })
    };

    // Emit every totalizer clause as `sum(mapped) >= 1`. An empty clause means the
    // encoder proved the constraint unreachable -> the relaxation forces UNSAT;
    // signal failure (caller stops). The encoder for a full `at_least(n)` counter
    // does not emit the root unit, so empty clauses here are genuine failures.
    //
    // DEADLINE/MEMORY POLL: a large core (hundreds of relaxation literals) yields a
    // totalizer with hundreds of thousands of clauses (e.g. a 479-literal core ->
    // ~356k clauses), and each `add_cardinality_runtime` runs level-0 unit
    // propagation over the whole instance, so this emission loop alone can run for
    // minutes. The interruptible totalizer *builder* above already polls
    // `should_stop`, but emission did not — so an OLL core round could blow far past
    // the wall-clock budget (the lp4l overrun: ~356s on a 60s limit). Poll the stop
    // signal and the process memory guard on a fixed cadence and BAIL with `None` on
    // a trip. `None` is fully sound: `process_core` maps it to `CoreOutcome::Stop`,
    // which returns the (already verified) incumbent as SATISFIABLE -- abandoning the
    // optimality proof, never emitting a wrong verdict. Any partial totalizer
    // constraints left in the solver are themselves sound implied cardinality
    // clauses; the solver is not queried again after the bail.
    const TOTALIZER_EMIT_POLL_INTERVAL: usize = 4096;
    let mut mapped: Vec<PbLit> = Vec::new();
    for (emitted, clause) in clauses.iter().enumerate() {
        if emitted % TOTALIZER_EMIT_POLL_INTERVAL == 0
            && (should_stop() || ay_sys::process_memory_exceeded())
        {
            return None;
        }
        if clause.is_empty() {
            return None;
        }
        mapped.clear();
        mapped.reserve(clause.len());
        for &dimacs in clause {
            mapped.push(map(dimacs)?);
        }
        match solver.add_cardinality_runtime(&mapped, 1) {
            RuntimeConstraintOutcome::Added => {}
            RuntimeConstraintOutcome::Conflict => {
                // A relaxation clause is implied, so it should never falsify the
                // formula at level 0. Fail closed defensively.
                return None;
            }
            RuntimeConstraintOutcome::Unsupported => return None,
        }
    }

    let mut result = Vec::with_capacity(outputs.outputs.len());
    for (&weight, &dimacs) in outputs.weights.iter().zip(outputs.outputs.iter()) {
        result.push((weight, map(dimacs)?));
    }
    Some(result)
}

/// Normalizes the objective `min: sum(coeff_i * lit_i)` into weighted soft
/// selectors plus a constant offset, mirroring the SAT-OLL normalization.
///
/// Each returned `WeightedSoft { literal, weight }` means: paying `weight` iff
/// `literal` is true. Negative-coefficient terms are flipped (the no-cost
/// polarity becomes the term literal). Duplicate cost literals are merged.
/// Returns `None` if the objective has any non-single-literal (product) term.
fn normalize_weighted_softs(objective: &PbObjective) -> Option<(Vec<WeightedSoft>, i128)> {
    let mut offset: i128 = 0;
    let mut order: Vec<PbLit> = Vec::new();
    let mut weights_by_lit: HashMap<PbLit, i128> = HashMap::new();

    for term in &objective.terms {
        if term.coeff == 0 {
            continue;
        }
        let [lit] = term.lits.as_slice() else {
            return None;
        };
        let (cost_lit, weight) = if term.coeff > 0 {
            (*lit, term.coeff)
        } else {
            let flipped = term.coeff.checked_neg()?;
            offset += term.coeff;
            (complement(*lit), flipped)
        };
        let entry = weights_by_lit.entry(cost_lit).or_insert_with(|| {
            order.push(cost_lit);
            0
        });
        *entry += weight;
    }

    let mut softs = Vec::with_capacity(order.len());
    for lit in order {
        let weight = *weights_by_lit.get(&lit)?;
        if weight <= 0 {
            continue;
        }
        softs.push(WeightedSoft {
            literal: lit,
            weight: i128::try_from(weight).ok()?,
        });
    }

    let offset = i128::try_from(offset).ok()?;
    Some((softs, offset))
}

/// Finalizes a native-OLL run believed optimal at `lower_bound`. Re-verifies via
/// the soundness gate; on any failure returns the incumbent as `Satisfiable`.
///
/// The effective lower bound is `max(lower_bound, structural_lb)`: both are
/// independently sound lower bounds, so their max is sound and never exceeds a
/// feasible objective value.
///
/// `should_stop` (plus the process-memory guard) bounds the structural-bound
/// recomputation; on a stop the already-proven `lower_bound` stands unchanged.
fn finish_optimum<F>(
    instance: &PbInstance,
    objective: &PbObjective,
    parity_cuts: &[PbConstraint],
    best_assignment: Vec<bool>,
    best_value: i128,
    lower_bound: i128,
    should_stop: &mut F,
) -> OptResult
where
    F: FnMut() -> bool,
{
    let structural = {
        let stop_cell = std::cell::RefCell::new(should_stop);
        let stop = crate::cdcl::strided_process_memory_stop(|| (stop_cell.borrow_mut())());
        structural_lower_bound_with_parity(instance, objective, parity_cuts, &stop)
            .unwrap_or(lower_bound)
    };
    let effective_lb = lower_bound.max(structural);
    let upper_bound = best_value;
    if best_value <= effective_lb
        && verify_native_optimum(
            instance,
            objective,
            &best_assignment,
            best_value,
            effective_lb,
            upper_bound,
        )
    {
        OptResult::Optimal(best_assignment, best_value)
    } else {
        OptResult::Satisfiable(best_assignment, best_value)
    }
}

/// Upper bound on the (size-scaled) wall-clock budget for the LP-relaxation floor.
/// The exact-rational simplex can be slow on larger instances; this cap keeps the
/// LP floor from starving the core-guided descent that follows. On a budget abort
/// the LP returns its best sound (possibly weaker) bound, so soundness is
/// unaffected — only tightness. The effective budget is scaled by variable count
/// (see [`lp_relaxation_floor`]) and clamped to this ceiling. Overridable via
/// `AY_PB_LP_FLOOR_MS` (fixed budget; `0` disables the floor).
const LP_FLOOR_BUDGET_MS: u64 = 35_000;
/// Lower bound on the size-scaled LP-floor budget: small instances whose LP solves
/// near-instantly still get this floor so a borderline-cheap LP is never cut off.
const LP_FLOOR_BUDGET_MIN_MS: u64 = 2_000;
/// Milliseconds of LP-floor budget granted per instance variable. Tuned so a
/// few-thousand-variable cardinality instance (e.g. pebbling) reaches the ceiling
/// while a few-hundred-variable weighted instance gets only a couple of seconds.
const LP_FLOOR_BUDGET_MS_PER_VAR: u64 = 8;
/// Environment override for the LP-floor wall-clock budget (milliseconds). A value
/// of `0` disables the LP floor entirely (returns no floor); any other value pins a
/// fixed budget, bypassing the size scaling.
const LP_FLOOR_BUDGET_ENV: &str = "AY_PB_LP_FLOOR_MS";
/// Variable-count pre-guard for the LP floor. The exact-rational LP solver itself
/// declines (returns `None`) above an internal cap of a few thousand variables, so
/// for clearly-oversized inputs we skip the whole attempt — including the
/// (non-trivial) preprocessing pass — rather than pay for work that cannot yield a
/// floor. Kept a touch above the LP solver's own cap so preprocessing-driven
/// variable reductions still get a chance to bring a borderline instance under it.
const LP_FLOOR_MAX_VARS: u32 = 5_500;

/// Wall-clock slice reserved for the Lagrangian subgradient floor AND its cut
/// loop, taken BEFORE the simplex tiers so they cannot starve it.
///
/// This is the binding constraint on cut rounds, not `SUBGRADIENT_CUT_ROUNDS`
/// and not `MAX_TOTAL_CUTS`: instrumented on `..._mw19_19`, the loop exited with
/// `stopped=true` after 7-8 rounds and ~1000 of the 1500 permitted cuts, still
/// improving. Raising the round cap alone therefore does nothing. Measured
/// 2000ms -> dual 143, 6000ms -> 144.
const SUBGRADIENT_FLOOR_BUDGET: std::time::Duration = std::time::Duration::from_secs(6);

/// Maximum wall-clock budget for the LP-floor incumbent probe (`objective <= floor`
/// realize query). When the LP floor is tight (integral LP relaxation, e.g. the
/// injcomp injection family) the query is SATISFIABLE and resolves in well under a
/// second; when it is not tight the query proves UNSAT of `objective <= floor` and
/// can be arbitrarily hard, so this cap bounds the wasted time before OLL falls
/// through to its normal stratified descent. Kept small relative to a competition
/// budget so a non-tight probe is a negligible tax on the descent that follows.
const LP_FLOOR_PROBE_BUDGET_MS: u64 = 5_000;
/// Per-variable scaling for the LP-floor probe budget, clamped to
/// [`LP_FLOOR_PROBE_BUDGET_MIN_MS`, `LP_FLOOR_PROBE_BUDGET_MS`]. The realize query's
/// difficulty grows with instance size, and so does the payoff, but the cap keeps it
/// bounded.
const LP_FLOOR_PROBE_BUDGET_MS_PER_VAR: u64 = 2;
/// Lower bound on the LP-floor probe budget so a borderline-cheap realize query on a
/// small instance is never cut off before it can succeed.
const LP_FLOOR_PROBE_BUDGET_MIN_MS: u64 = 1_500;

/// Size-scaled, bounded budget for the LP-floor incumbent probe. See
/// [`LP_FLOOR_PROBE_BUDGET_MS`].
fn lp_floor_probe_budget(instance: &PbInstance) -> std::time::Duration {
    let ms = u64::from(instance.num_vars)
        .saturating_mul(LP_FLOOR_PROBE_BUDGET_MS_PER_VAR)
        .clamp(LP_FLOOR_PROBE_BUDGET_MIN_MS, LP_FLOOR_PROBE_BUDGET_MS);
    std::time::Duration::from_millis(ms)
}

/// Computes a sound LP-relaxation lower bound (floor) on the objective, evaluated
/// over the **per-constraint GCD-strengthened** constraint set produced by
/// [`crate::preprocess::preprocess`].
///
/// # Why preprocess first
/// GCD strengthening rewrites e.g. `2a + 2b + 2c + 2d >= 3` into the entailed
/// `a + b + c + d >= 2` (the LHS is always even, so `>= 3` forces `>= 4`). For
/// proof-complexity-hard cardinality families (pebbling) this strengthened LP
/// relaxation is *integral* and its optimum equals the integer optimum, which is
/// exactly why RoundingSat/Exact close them instantly. The un-strengthened LP is
/// markedly weaker (e.g. 284 vs the true 378), so without this step the floor would
/// not prove optimality.
///
/// # Soundness
/// Every preprocessing step is a satisfiability-preserving / entailed
/// transformation (see [`crate::preprocess`]), so the LP optimum over the
/// strengthened constraints is `<= IntOpt` of the ORIGINAL problem, and
/// [`crate::optimize::lp_bound::lp_lower_bound`] returns an exact-rational sound
/// lower bound (`ceil(LP*)`) computed without trusting floating point. The
/// returned value is therefore a valid floor on the original objective. As a
/// backstop, [`verify_native_optimum`] re-checks the witness against the
/// ORIGINAL constraints and the `value <= floor` bracket — that catches
/// witness/value corruption, but the floor it compares against is this very
/// value, so an overshooting floor is not detectable there: the soundness of
/// an OPTIMUM claim rests on the exact-rational LP bound derivation itself.
fn lp_relaxation_floor<F>(
    instance: &PbInstance,
    objective: &PbObjective,
    should_stop: &mut F,
) -> Option<i128>
where
    F: FnMut() -> bool,
{
    // Budget. An explicit `AY_PB_LP_FLOOR_MS` override pins a fixed budget (and `0`
    // disables the floor entirely). Otherwise the budget SCALES WITH INSTANCE SIZE:
    // the exact-rational simplex cost grows with the variable count, and so does the
    // payoff (only large cardinality families like pebbling need the floor — small
    // weighted instances are closed by the core-guided descent alone). Scaling keeps
    // tiny instances from ever spending a large fixed slice on a doomed LP while
    // still granting big pebbling instances the seconds their (tight) LP needs to
    // complete. Clamped to `[LP_FLOOR_BUDGET_MIN_MS, LP_FLOOR_BUDGET_MS]`.
    let budget_ms = match std::env::var(LP_FLOOR_BUDGET_ENV)
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
    {
        Some(fixed) => fixed,
        None => u64::from(instance.num_vars)
            .saturating_mul(LP_FLOOR_BUDGET_MS_PER_VAR)
            .clamp(LP_FLOOR_BUDGET_MIN_MS, LP_FLOOR_BUDGET_MS),
    };
    if budget_ms == 0 || should_stop() {
        return None;
    }

    // Cheap size pre-guard: the exact-rational LP solver declines (returns `None`)
    // above its internal variable cap, so for clearly-too-large instances skip the
    // whole attempt — including the (non-trivial) preprocessing pass below — rather
    // than paying for work that cannot yield a floor. Pegged slightly above the LP
    // solver's own cap so preprocessing-driven variable reductions still get a
    // chance to bring an instance under it.
    if instance.num_vars > LP_FLOOR_MAX_VARS {
        return None;
    }

    // Strengthen the constraints (GCD strengthening, coefficient tightening) via
    // the shared preprocessing pipeline. On UNSAT/Interrupted we simply skip the
    // floor (a missing floor is always safe).
    let strengthened =
        match crate::preprocess::preprocess_interruptible(instance, &mut *should_stop) {
            crate::preprocess::PreprocessResult::Simplified { instance, .. } => instance,
            _ => return None,
        };

    let deadline = std::time::Instant::now() + std::time::Duration::from_millis(budget_ms);
    // `lp_lower_bound` wants a `&dyn Fn()`; the caller's `should_stop` is `FnMut`.
    // Wrap it in a `RefCell` so the inner `Fn` closure can poll it (the OLL stop
    // closures are cheap idempotent deadline/term-flag checks). The LP's own
    // deadline is the binding budget; the outer stop is honored as a backstop.
    let should_stop_cell = std::cell::RefCell::new(should_stop);
    let lp_should_stop =
        || std::time::Instant::now() >= deadline || (should_stop_cell.borrow_mut())();

    // When the Farkas-certificate emit path is enabled (`--pb-farkas-cert`), build
    // and self-validate a checked certificate for the base LP bound. This is purely
    // an ADDED, fail-closed trust layer: the floor returned is the SAME value the
    // exact simplex computed regardless of the certificate outcome. On `Verified`
    // the bound is corroborated by the fast checked certificate (no re-derivation
    // needed); on `Rejected`/`Disabled` we fall back to the exact path verbatim, so
    // this is byte-for-byte at least as sound as before.
    // The certified base bound, when the Farkas emit path is on. This used to
    // RETURN here, which meant the subgradient floor below was never computed on
    // the certificate path at all — measured on `..._mw19_19`, the dual dropped
    // from 139 to 130 the moment `--pb-farkas-cert` was set, putting proof
    // coverage and floor quality in direct conflict. Now it feeds the same
    // single exit as every other floor.
    //
    // NOTE FOR CERTIFICATE CONSUMERS: the returned floor is a MAX over several
    // independently sound sources, so it can exceed the certified `bound`. Both
    // are sound, but the certificate covers only its own value — never report a
    // floor as certified unless it equals the certificate's claimed bound.
    let certified_floor = if crate::optimize::lp_bound::cert_path_enabled() {
        crate::optimize::lp_bound::lp_lower_bound_with_cert(
            objective,
            &strengthened.constraints,
            strengthened.num_vars,
            &lp_should_stop,
        )
        .map(|(bound, _cert, _outcome)| bound)
    } else {
        None
    };

    // Take the best of the simplex floor and the LAGRANGIAN SUBGRADIENT floor.
    // Both are sound lower bounds derived by exact rational arithmetic, so their
    // max is sound. The subgradient route exists because the simplex tiers stall
    // on degenerate covering LPs — measured on `liu/domset ..._mw19_19`, the
    // simplex floor is 35 against a true LP optimum of 138.086, while the
    // subgradient certifies 139.
    //
    // ORDER MATTERS. The subgradient runs FIRST, on its own short deadline. It is
    // the cheap one (O(nnz) per iteration, ~400ms total) and the simplex tiers
    // will otherwise consume the entire LP-floor budget and leave it with an
    // already-expired stop closure — measured: it exited at iteration 0 and
    // returned nothing at all.
    let sub_deadline = std::time::Instant::now() + SUBGRADIENT_FLOOR_BUDGET;
    let sub_should_stop =
        || std::time::Instant::now() >= sub_deadline || (should_stop_cell.borrow_mut())();
    let subgradient_floor = crate::optimize::lp_bound::lagrangian_dual_floor(
        objective,
        &strengthened.constraints,
        strengthened.num_vars,
        &sub_should_stop,
    );
    let simplex_floor = crate::optimize::lp_bound::lp_lower_bound(
        objective,
        &strengthened.constraints,
        strengthened.num_vars,
        &lp_should_stop,
    );
    // SINGLE EXIT over every independently sound source, so no future branch can
    // skip one the way the certificate branch used to skip the subgradient.
    [certified_floor, simplex_floor, subgradient_floor]
        .into_iter()
        .flatten()
        .max()
}

/// Sound structural lower bound on the objective, computed over the original
/// constraints **augmented with the entailed GF(2) parity cuts**.
///
/// # Soundness
/// Each parity cut in `parity_cuts` is entailed by `instance.constraints` (it is
/// satisfied by every feasible 0/1 point — proven by the brute-force entailment
/// test in [`crate::optimize::gf2_parity`]). Adding entailed constraints never
/// removes a feasible point, so `objective_lower_bound_from_constraints` over the
/// augmented set is still a valid lower bound on the *original* objective. The
/// final optimum is independently re-verified against the ORIGINAL constraints by
/// [`verify_native_optimum`], so even if a cut were somehow wrong the reported
/// value could not be unsound — but the entailment test guarantees it is right.
fn structural_lower_bound_with_parity(
    instance: &PbInstance,
    objective: &PbObjective,
    parity_cuts: &[PbConstraint],
    should_stop: &dyn Fn() -> bool,
) -> Option<i128> {
    let base = crate::cdcl::objective_lower_bound_from_constraints(
        &instance.constraints,
        objective,
        should_stop,
    );
    if parity_cuts.is_empty() {
        return base;
    }
    let mut augmented =
        Vec::with_capacity(instance.constraints.len().saturating_add(parity_cuts.len()));
    augmented.extend_from_slice(&instance.constraints);
    augmented.extend_from_slice(parity_cuts);
    let with_cuts =
        crate::cdcl::objective_lower_bound_from_constraints(&augmented, objective, should_stop);
    match (base, with_cuts) {
        (Some(a), Some(b)) => Some(a.max(b)),
        (Some(a), None) => Some(a),
        (None, Some(b)) => Some(b),
        (None, None) => None,
    }
}

/// Tries to realize an incumbent at exactly the sound parity floor `floor` by
/// solving `objective <= floor` in an ISOLATED fresh solver.
///
/// Returns `Some((model, value))` with `value <= floor` when such a model exists
/// and satisfies every ORIGINAL constraint; `None` otherwise (no such model,
/// interrupted, encoding failure, or verification failure — all fail-closed).
///
/// # Soundness
/// The probe runs on a freshly built [`PbCdclSolver`] over a copy of the
/// instance with the single added bound `objective <= floor`, so it cannot affect
/// the persistent OLL solver. A returned model is re-checked against the original
/// constraints (and its objective value recomputed) before being handed back; the
/// caller then treats it as optimal only because `floor` is an independently
/// sound lower bound, and `finish_optimum` re-verifies once more.
fn try_parity_floor_incumbent<F>(
    instance: &PbInstance,
    objective: &PbObjective,
    floor: i128,
    should_stop: &mut F,
) -> Option<(Vec<bool>, i128)>
where
    F: FnMut() -> bool,
{
    if should_stop() {
        return None;
    }
    let bound = objective_at_most_constraint(objective, floor).ok()?;
    let mut probe_constraints = Vec::with_capacity(instance.constraints.len().saturating_add(1));
    probe_constraints.extend_from_slice(&instance.constraints);
    probe_constraints.push(bound);
    let probe_instance = PbInstance {
        num_vars: instance.num_vars,
        num_constraints: u32::try_from(probe_constraints.len()).unwrap_or(u32::MAX),
        constraints: probe_constraints,
        objective: None,
    };

    let mut probe =
        PbCdclSolver::new_unpreprocessed_interruptible(&probe_instance, &mut *should_stop);
    match probe.solve_interruptible(&mut *should_stop) {
        crate::cdcl::PbCdclResult::Satisfiable(model) => {
            // Re-verify against the ORIGINAL constraints and recompute the value.
            if !crate::eval::verify_all_constraints(&instance.constraints, &model) {
                return None;
            }
            let value = eval_objective(objective, &model);
            if value > floor {
                // Should not happen (the bound forces value <= floor), but stay
                // fail-closed if the encoding/eval disagree.
                return None;
            }
            Some((model, value))
        }
        crate::cdcl::PbCdclResult::Unsatisfiable
        | crate::cdcl::PbCdclResult::Unknown
        | crate::cdcl::PbCdclResult::Optimal(_, _)
        | crate::cdcl::PbCdclResult::Feasible(_, _) => None,
    }
}

/// Soundness gate: a claimed optimum is accepted only when the objective is
/// exact, the value lies in `[lower_bound, upper_bound]`, and the model satisfies
/// EVERY original constraint.
fn verify_native_optimum(
    instance: &PbInstance,
    objective: &PbObjective,
    assignment: &[bool],
    claimed_value: i128,
    lower_bound: i128,
    upper_bound: i128,
) -> bool {
    if eval_objective(objective, assignment) != claimed_value {
        return false;
    }
    if claimed_value < lower_bound || claimed_value > upper_bound {
        return false;
    }
    crate::eval::verify_all_constraints(&instance.constraints, assignment)
}

fn complement(lit: PbLit) -> PbLit {
    PbLit {
        var: lit.var,
        negated: !lit.negated,
    }
}

/// Whether LP reduced-cost variable fixing is enabled. Default **OFF** (opt-in):
/// the fixing rule is fully sound (every fix is certified by a strict
/// exact-rational test and the final optimum is re-verified against the ORIGINAL
/// constraints), but it is gated so the default solver behavior is unchanged. Set
/// `AY_PB_REDUCED_COST` to `1|true|yes|on` to enable.
fn reduced_cost_fixing_enabled() -> bool {
    fn enabled(value: &OsStr) -> bool {
        value.to_str().is_some_and(|value| {
            matches!(
                value.trim().to_ascii_lowercase().as_str(),
                "1" | "true" | "yes" | "on"
            )
        })
    }
    match std::env::var_os(REDUCED_COST_ENV) {
        Some(value) => enabled(&value),
        None => false,
    }
}

/// Drives LP reduced-cost variable fixing over the persistent native solver.
///
/// At the root (and after each incumbent improvement) it solves the exact-rational
/// LP relaxation of the **GCD-strengthened** constraints, computes per-variable
/// reduced costs, and for every variable the rule in
/// [`crate::optimize::lp_bound::lp_reduced_cost_fixings`] certifies, installs a
/// level-0 permanent unit (`lit >= 1`) via [`PbCdclSolver::add_cardinality_runtime`].
/// The strong CDCL then propagates those fixings + sees the tighter constraint set.
///
/// # Soundness
/// - A fixing means: every assignment *strictly better* than the current incumbent
///   must take that value. Installing it as a unit prunes only non-improving
///   assignments; it never removes the optimum. (Proof: see `lp_reduced_cost_fixings`.)
/// - The LP is solved over GCD-strengthened constraints, which are entailed by the
///   ORIGINAL constraints, so the reduced-cost argument bounds the ORIGINAL
///   objective. The unit it installs is sound on the original problem.
/// - Fixings are re-derived only when the incumbent IMPROVES (the gap shrinks -> the
///   `strict_target` shrinks -> the fixing test only gets *easier*), so the fix set
///   grows monotonically and a later fixing can never contradict an earlier one.
///   A `debug_assert` enforces this; a contradictory re-add (which cannot happen
///   soundly) is rejected at runtime rather than installed.
/// - Fixings are prunings, NOT part of the optimality certificate:
///   `verify_native_optimum` re-checks the witness against ALL ORIGINAL constraints.
struct ReducedCostFixer {
    /// GCD-strengthened constraints the LP reasons over (computed once; entailed by
    /// the original constraints). `None` once we have decided not to run (disabled,
    /// preprocess failed/UNSAT, too large) so subsequent calls are cheap no-ops.
    strengthened: Option<StrengthenedConstraints>,
    /// Variables already fixed, with their forced value. Used to skip redundant
    /// re-adds and to assert no later derivation contradicts an earlier fix.
    applied: HashMap<u32, bool>,
    /// The incumbent value at the last derivation; re-derive only when it improves.
    last_incumbent: i128,
    /// Best (largest) sound LP lower bound observed across derivations. This is the
    /// same exact-rational LP bound the floor uses, so it can also tighten the
    /// terminal `best_value <= floor` short-circuit. `i128::MIN` until the first LP
    /// solve succeeds.
    best_lp_bound: i128,
    /// Remaining LP-solve budget (number of derivations). Each `refresh` that
    /// actually runs an LP decrements this; at zero the fixer becomes a no-op. Caps
    /// the total exact-rational LP work so an instance that improves its incumbent
    /// many times cannot spend an unbounded fraction of the solve budget on repeated
    /// LP solves (defensive -- the per-solve deadline already bounds each call).
    refreshes_remaining: u32,
}

/// Maximum number of LP solves (root + per-improvement re-derivations) a single
/// instance's reduced-cost fixer will perform. Each solve is independently
/// deadline-bounded; this caps the cumulative count so repeated incumbent
/// improvements cannot trigger unboundedly many exact-rational LP solves.
const MAX_REDUCED_COST_REFRESHES: u32 = 16;

/// The strengthened constraint set + variable count the LP reasons over.
struct StrengthenedConstraints {
    constraints: Vec<PbConstraint>,
    num_vars: u32,
}

impl ReducedCostFixer {
    /// Builds the fixer, GCD-strengthening the constraints once. Returns a disabled
    /// fixer (a no-op on every call) when the gate is off, the budget is `0`, the
    /// instance is too large, or preprocessing declined/proved UNSAT.
    fn new<F>(instance: &PbInstance, should_stop: &mut F) -> Self
    where
        F: FnMut() -> bool,
    {
        let disabled = Self {
            strengthened: None,
            applied: HashMap::new(),
            last_incumbent: i128::MAX,
            best_lp_bound: i128::MIN,
            refreshes_remaining: 0,
        };
        if !reduced_cost_fixing_enabled() {
            return disabled;
        }
        if reduced_cost_budget_ms(instance) == 0 {
            return disabled;
        }
        // Same size pre-guard as the LP floor: the exact-rational LP declines above
        // its internal cap, so skip the (non-trivial) preprocessing for oversized
        // inputs rather than pay for work that cannot yield a fixing.
        if instance.num_vars > LP_FLOOR_MAX_VARS {
            return disabled;
        }
        let strengthened = match crate::preprocess::preprocess_interruptible(instance, should_stop)
        {
            crate::preprocess::PreprocessResult::Simplified { instance, .. } => {
                StrengthenedConstraints {
                    constraints: instance.constraints,
                    num_vars: instance.num_vars,
                }
            }
            _ => return disabled,
        };
        Self {
            strengthened: Some(strengthened),
            applied: HashMap::new(),
            last_incumbent: i128::MAX,
            best_lp_bound: i128::MIN,
            refreshes_remaining: MAX_REDUCED_COST_REFRESHES,
        }
    }

    /// The best sound LP lower bound derived so far (`i128::MIN` if none). Folded into
    /// the terminal floor by the caller; always `<= IntOpt`.
    fn lp_lower_bound(&self) -> i128 {
        self.best_lp_bound
    }

    /// Re-derives reduced-cost fixings against `incumbent_ub`, installs any new ones
    /// as level-0 units on `solver`, and (if any new fixing was installed) re-solves
    /// with no assumptions to surface the strictly-better model the fixings now force.
    /// A no-op when disabled or when the incumbent has not improved.
    ///
    /// Returning the fresh model is what makes the fixings actually *drive* the
    /// incumbent down: the OLL core/hardening machinery reasons over soft selectors
    /// and, once variables are hard-fixed, can collapse cores in a way that leaves
    /// the stale incumbent in place. A direct re-solve over the now-pruned formula
    /// finds the better model immediately (exactly RoundingSat's "fix, then let CDCL
    /// propagate + search" flow), and is re-verified by the caller.
    fn refresh<F>(
        &mut self,
        solver: &mut PbCdclSolver,
        objective: &PbObjective,
        incumbent_ub: i128,
        should_stop: &mut F,
    ) -> RefreshOutcome
    where
        F: FnMut() -> bool,
    {
        let Some(strengthened) = self.strengthened.as_ref() else {
            return RefreshOutcome::Unchanged; // disabled
        };
        // Only re-derive when the incumbent strictly improved: a smaller UB shrinks
        // `strict_target`, making the fixing test strictly easier, so the fix set
        // only grows. No improvement => the previously installed fixings already
        // capture everything this LP can prove.
        if incumbent_ub >= self.last_incumbent {
            return RefreshOutcome::Unchanged;
        }
        if should_stop() {
            return RefreshOutcome::Unchanged;
        }
        // Defensive cumulative cap: never spend more than a fixed number of
        // exact-rational LP solves on one instance, no matter how often the
        // incumbent improves.
        if self.refreshes_remaining == 0 {
            return RefreshOutcome::Unchanged;
        }
        self.refreshes_remaining -= 1;

        let budget_ms = reduced_cost_budget_ms_for(strengthened.num_vars);
        let deadline = std::time::Instant::now() + std::time::Duration::from_millis(budget_ms);
        // Scoped so the `&mut *should_stop` re-borrow ends before the post-fix
        // re-solve below re-uses `should_stop`.
        let result = {
            let should_stop_cell = std::cell::RefCell::new(&mut *should_stop);
            let lp_should_stop =
                || std::time::Instant::now() >= deadline || (should_stop_cell.borrow_mut())();
            crate::optimize::lp_bound::lp_reduced_cost_fixings(
                objective,
                &strengthened.constraints,
                strengthened.num_vars,
                incumbent_ub,
                &lp_should_stop,
            )
        };
        self.last_incumbent = incumbent_ub;

        let Some(result) = result else {
            return RefreshOutcome::Unchanged; // LP declined; nothing to install.
        };
        // Record the sound LP lower bound (max across derivations). It is the same
        // exact-rational bound the LP floor uses, so it can also tighten the
        // terminal optimality short-circuit.
        self.best_lp_bound = self.best_lp_bound.max(result.lower_bound);

        let mut installed_any = false;
        for fixing in result.fixings {
            // Consistency invariant: a re-derived fixing must never contradict an
            // earlier one (the fix set is monotone as the incumbent shrinks). If it
            // somehow does, REJECT it rather than install -- never trust an
            // unexplained contradiction.
            if let Some(&prev) = self.applied.get(&fixing.var) {
                debug_assert_eq!(
                    prev, fixing.value,
                    "reduced-cost fixing contradiction on var {}: was {prev}, now {}",
                    fixing.var, fixing.value
                );
                continue; // already installed (or rejected contradiction).
            }
            // Install `lit >= 1` forcing the variable to `fixing.value`.
            let lit = PbLit {
                var: fixing.var,
                negated: !fixing.value,
            };
            match solver.add_cardinality_runtime(&[lit], 1) {
                RuntimeConstraintOutcome::Added => {
                    self.applied.insert(fixing.var, fixing.value);
                    installed_any = true;
                }
                RuntimeConstraintOutcome::Conflict => {
                    // Forcing this sound fixing closed the root: no model strictly
                    // better than the incumbent exists. The incumbent is optimal.
                    self.applied.insert(fixing.var, fixing.value);
                    return RefreshOutcome::RootClosed;
                }
                RuntimeConstraintOutcome::Unsupported => {
                    // Could not install (e.g. above level 0 -- should not happen here).
                    // Skip without recording; conservative and sound.
                }
            }
        }

        if !installed_any {
            return RefreshOutcome::Unchanged;
        }

        // A fixing was installed. Re-solve with NO assumptions over the now-pruned
        // formula to surface the strictly-better model the fixings force. The result
        // is re-verified by the caller against the ORIGINAL constraints.
        if should_stop() {
            return RefreshOutcome::Unchanged;
        }
        match solver.solve_with_assumptions_interruptible(&[], should_stop) {
            PbCdclAssumptionResult::Satisfiable(model) => {
                let value = eval_objective(objective, &model);
                if value < incumbent_ub {
                    RefreshOutcome::Improved(model, value)
                } else {
                    RefreshOutcome::Unchanged
                }
            }
            PbCdclAssumptionResult::Unsatisfiable { .. } => {
                // The pruned formula is UNSAT: no model at all leaves every fixed
                // variable at its forced value AND every (non-hardened) soft unpaid.
                // But fixings only forbid NON-improving assignments, so UNSAT here
                // means no strictly-better model exists -> the incumbent is optimal.
                RefreshOutcome::RootClosed
            }
            PbCdclAssumptionResult::Unknown | PbCdclAssumptionResult::Unsupported => {
                RefreshOutcome::Unchanged
            }
        }
    }
}

/// Outcome of a [`ReducedCostFixer::refresh`].
enum RefreshOutcome {
    /// Nothing changed (disabled, no new fixings, LP declined, or interrupted).
    Unchanged,
    /// A strictly-better model was found after installing fixings.
    Improved(Vec<bool>, i128),
    /// Installing a fixing (or the post-fix re-solve) proved no strictly-better
    /// model than the incumbent exists; the incumbent is optimal.
    RootClosed,
}

/// Size-scaled reduced-cost-fixing budget (ms) for an instance. Mirrors the LP-floor
/// schedule: scale with variable count (simplex cost + payoff both grow with size),
/// clamp to `[LP_FLOOR_BUDGET_MIN_MS, REDUCED_COST_BUDGET_MS]`. An explicit
/// `AY_PB_REDUCED_COST_MS` override pins a fixed budget (`0` disables entirely).
fn reduced_cost_budget_ms(instance: &PbInstance) -> u64 {
    reduced_cost_budget_ms_for(instance.num_vars)
}

fn reduced_cost_budget_ms_for(num_vars: u32) -> u64 {
    match std::env::var(REDUCED_COST_BUDGET_ENV)
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
    {
        Some(fixed) => fixed,
        None => u64::from(num_vars)
            .saturating_mul(LP_FLOOR_BUDGET_MS_PER_VAR)
            .clamp(LP_FLOOR_BUDGET_MIN_MS, REDUCED_COST_BUDGET_MS),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::{parse_opb, parse_wbo};
    use crate::types::{PbConstraint, PbTerm};
    use ay_test_support::env::{lock_env, ScopedEnvVar};

    /// Runs native OLL to completion (no timeout) on a parsed OPB instance and
    /// returns the result.
    fn run_native_oll_opb(input: &str) -> OptResult {
        let instance = parse_opb(input).expect("parse OPB");
        let objective = instance.objective.clone().expect("has objective");
        solve(&instance, &objective, || false, None, None)
            .expect("native OLL should apply to a single-literal weighted objective")
    }

    fn optimum_value(result: &OptResult) -> Option<i128> {
        match result {
            OptResult::Optimal(_, value) => Some(*value),
            _ => None,
        }
    }

    /// Brute-force exact minimum objective over all 2^n assignments. Returns
    /// `None` if the instance is infeasible.
    fn brute_force_optimum(instance: &PbInstance, objective: &PbObjective) -> Option<i128> {
        let n = instance.num_vars as usize;
        assert!(n <= 20, "brute force only for tiny instances");
        let mut best: Option<i128> = None;
        for mask in 0u32..(1u32 << n) {
            let assignment: Vec<bool> = (0..n).map(|i| (mask >> i) & 1 == 1).collect();
            if !crate::eval::verify_all_constraints(&instance.constraints, &assignment) {
                continue;
            }
            let value = eval_objective(objective, &assignment);
            best = Some(best.map_or(value, |b| b.min(value)));
        }
        best
    }

    // ---- Unit OLL correctness (mirror of the SAT-OLL fixtures) ----

    #[test]
    fn native_oll_solves_unit_vertex_cover_to_known_optimum() {
        // Vertex cover on a 6-cycle plus chord 1-4. Minimum cover has size 3.
        let input = "* #variable= 6 #constraint= 7\n\
            min: +1 x1 +1 x2 +1 x3 +1 x4 +1 x5 +1 x6 ;\n\
            +1 x1 +1 x2 >= 1 ;\n\
            +1 x2 +1 x3 >= 1 ;\n\
            +1 x3 +1 x4 >= 1 ;\n\
            +1 x4 +1 x5 >= 1 ;\n\
            +1 x5 +1 x6 >= 1 ;\n\
            +1 x6 +1 x1 >= 1 ;\n\
            +1 x1 +1 x4 >= 1 ;\n";
        let result = run_native_oll_opb(input);
        assert_eq!(optimum_value(&result), Some(3), "got {result:?}");
    }

    #[test]
    fn native_oll_solves_weighted_objective_to_known_optimum() {
        let input = "* #variable= 4 #constraint= 3\n\
            min: +1 x1 +2 x2 +3 x3 +4 x4 ;\n\
            +1 x1 +1 x2 +1 x3 +1 x4 >= 2 ;\n\
            +1 x1 +1 x3 >= 1 ;\n\
            +1 x2 +1 x4 >= 1 ;\n";
        let result = run_native_oll_opb(input);
        assert_eq!(optimum_value(&result), Some(3), "got {result:?}");
    }

    #[test]
    fn native_oll_lp_floor_proves_gcd_strengthened_cardinality_optimum() {
        // Two disjoint groups, each `2a+2b+2c+2d >= 3`. GCD strengthening rewrites
        // each to the entailed `a+b+c+d >= 2`, whose LP relaxation forces the group
        // sum to exactly 2 (integral). So min total = 2 + 2 = 4. Without the LP
        // floor the un-strengthened LP only yields ceil(3/2)+ceil(3/2)=2 per group's
        // fractional 1.5, i.e. a loose floor; the strengthened LP floor is what
        // proves optimality here. The result must be a verified OPTIMUM at 4.
        let input = "* #variable= 8 #constraint= 2\n\
            min: +1 x1 +1 x2 +1 x3 +1 x4 +1 x5 +1 x6 +1 x7 +1 x8 ;\n\
            +2 x1 +2 x2 +2 x3 +2 x4 >= 3 ;\n\
            +2 x5 +2 x6 +2 x7 +2 x8 >= 3 ;\n";
        let instance = parse_opb(input).expect("parse OPB");
        let objective = instance.objective.clone().expect("has objective");
        let result = run_native_oll_opb(input);
        // OLL must return a *proven* optimum (Optimal), not just a feasible value.
        assert!(
            matches!(result, OptResult::Optimal(_, 4)),
            "expected proven Optimal(4), got {result:?}"
        );
        // Cross-check against the exact brute-force minimum.
        assert_eq!(brute_force_optimum(&instance, &objective), Some(4));
    }

    #[test]
    fn native_oll_disjoint_weighted_cores_accumulate_lower_bound() {
        // Two independent at-least-one pairs: min cost = min(3,4)+min(5,6)=3+5=8.
        let input = "* #variable= 4 #constraint= 2\n\
            min: +3 x1 +4 x2 +5 x3 +6 x4 ;\n\
            +1 x1 +1 x2 >= 1 ;\n\
            +1 x3 +1 x4 >= 1 ;\n";
        let result = run_native_oll_opb(input);
        assert_eq!(optimum_value(&result), Some(8), "got {result:?}");
    }

    #[test]
    fn native_oll_at_least_two_single_core_uses_totalizer_relaxation() {
        // A single core forcing TWO selectors -> exercises the totalizer output
        // o_2 path: at least 2 of {x1,x2,x3}, unit cost -> optimum 2.
        let input = "* #variable= 3 #constraint= 1\n\
            min: +1 x1 +1 x2 +1 x3 ;\n\
            +1 x1 +1 x2 +1 x3 >= 2 ;\n";
        let result = run_native_oll_opb(input);
        assert_eq!(optimum_value(&result), Some(2), "got {result:?}");
    }

    #[test]
    fn native_oll_weighted_at_least_two_uses_totalizer_relaxation() {
        // Pick the two cheapest of {2,3,4} -> 5 via totalizer relaxation thresholds.
        let input = "* #variable= 3 #constraint= 1\n\
            min: +2 x1 +3 x2 +4 x3 ;\n\
            +1 x1 +1 x2 +1 x3 >= 2 ;\n";
        let result = run_native_oll_opb(input);
        assert_eq!(optimum_value(&result), Some(5), "got {result:?}");
    }

    #[test]
    fn native_oll_high_dispersion_weights_reaches_known_optimum() {
        // Widely-dispersed weights exercise stratification + totalizer relaxation.
        let input = "* #variable= 5 #constraint= 3\n\
            min: +1 x1 +10 x2 +100 x3 +1000 x4 +10000 x5 ;\n\
            +1 x1 +1 x2 +1 x3 >= 2 ;\n\
            +1 x3 +1 x4 +1 x5 >= 1 ;\n\
            +1 x1 +1 x2 >= 1 ;\n";
        let result = run_native_oll_opb(input);
        let bf = {
            let instance = parse_opb(input).expect("parse");
            let obj = instance.objective.clone().expect("obj");
            brute_force_optimum(&instance, &obj).expect("feasible")
        };
        assert_eq!(optimum_value(&result), Some(bf), "got {result:?}");
    }

    #[test]
    fn native_oll_negative_coefficients_normalize_correctly() {
        // Negative coefficients should flip to the complemented selector + offset.
        let input = "* #variable= 3 #constraint= 1\n\
            min: -2 x1 +3 x2 -1 x3 ;\n\
            +1 x1 +1 x2 +1 x3 >= 1 ;\n";
        let instance = parse_opb(input).expect("parse");
        let objective = instance.objective.clone().expect("obj");
        let result = solve(&instance, &objective, || false, None, None).expect("applies");
        let bf = brute_force_optimum(&instance, &objective).expect("feasible");
        assert_eq!(optimum_value(&result), Some(bf), "got {result:?}");
    }

    #[test]
    fn native_oll_infeasible_base_is_infeasible() {
        // x1 and ~x1 both required: base is UNSAT.
        let input = "* #variable= 1 #constraint= 2\n\
            min: +1 x1 ;\n\
            +1 x1 >= 1 ;\n\
            +1 ~x1 >= 1 ;\n";
        let instance = parse_opb(input).expect("parse");
        let objective = instance.objective.clone().expect("obj");
        let result = solve(&instance, &objective, || false, None, None).expect("applies");
        assert_eq!(result, OptResult::Infeasible, "got {result:?}");
    }

    #[test]
    fn native_oll_optimal_results_pass_soundness_verification() {
        // Every Optimal result must re-verify against the original constraints.
        let input = "* #variable= 4 #constraint= 2\n\
            min: +2 x1 +3 x2 +5 x3 +7 x4 ;\n\
            +1 x1 +1 x2 +1 x3 +1 x4 >= 2 ;\n\
            +1 ~x1 +1 ~x2 +1 ~x3 +1 ~x4 >= 2 ;\n";
        let instance = parse_opb(input).expect("parse");
        let objective = instance.objective.clone().expect("obj");
        let result = solve(&instance, &objective, || false, None, None).expect("applies");
        match result {
            OptResult::Optimal(assignment, value) => {
                assert!(verify_native_optimum(
                    &instance,
                    &objective,
                    &assignment,
                    value,
                    value,
                    value
                ));
                let bf = brute_force_optimum(&instance, &objective).expect("feasible");
                assert_eq!(value, bf);
            }
            other => panic!("expected Optimal, got {other:?}"),
        }
    }

    // ---- Differential: native-OLL == brute force on random weighted instances ----

    #[test]
    fn native_oll_agrees_with_brute_force_on_random_weighted_instances() {
        // Deterministic LCG-driven random small weighted covering instances.
        let mut seed: u64 = 0x9E37_79B9_7F4A_7C15;
        let mut next = || {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            seed >> 33
        };

        let mut checked = 0usize;
        for _ in 0..40 {
            let num_vars = 3 + (next() % 5) as u32; // 3..=7 vars
            let num_constraints = 1 + (next() % 4) as usize; // 1..=4 constraints

            let mut obj_terms = Vec::new();
            for v in 1..=num_vars {
                let coeff = 1 + (next() % 8) as i128; // weights 1..=8
                obj_terms.push(PbTerm {
                    coeff,
                    lits: vec![PbLit {
                        var: v,
                        negated: false,
                    }],
                });
            }
            let objective = PbObjective { terms: obj_terms };

            let mut constraints = Vec::new();
            for _ in 0..num_constraints {
                let mut terms = Vec::new();
                for v in 1..=num_vars {
                    // ~50% inclusion, random polarity.
                    if next() % 2 == 0 {
                        terms.push(PbTerm {
                            coeff: 1,
                            lits: vec![PbLit {
                                var: v,
                                negated: next() % 2 == 0,
                            }],
                        });
                    }
                }
                if terms.is_empty() {
                    terms.push(PbTerm {
                        coeff: 1,
                        lits: vec![PbLit {
                            var: 1,
                            negated: false,
                        }],
                    });
                }
                let max_rhs = terms.len() as i128;
                let rhs = 1 + (next() as i128 % max_rhs.max(1));
                constraints.push(PbConstraint {
                    terms,
                    rel: crate::types::PbRel::Ge,
                    rhs,
                });
            }

            let instance = PbInstance {
                num_vars,
                num_constraints: num_constraints as u32,
                constraints,
                objective: Some(objective.clone()),
            };

            let bf = brute_force_optimum(&instance, &objective);
            let result = solve(&instance, &objective, || false, None, None);

            match (bf, result) {
                (None, Some(OptResult::Infeasible)) => {}
                (Some(opt), Some(OptResult::Optimal(assignment, value))) => {
                    assert_eq!(
                        value, opt,
                        "native-OLL optimum {value} != brute force {opt}"
                    );
                    assert!(
                        crate::eval::verify_all_constraints(&instance.constraints, &assignment),
                        "optimal model must satisfy all constraints"
                    );
                    assert_eq!(eval_objective(&objective, &assignment), value);
                }
                (bf, result) => panic!("mismatch: brute={bf:?} native={result:?}"),
            }
            checked += 1;
        }
        assert!(checked >= 40);
    }

    // ---- Disjoint-core batching: differential + equivalence gates ----

    /// Deterministic LCG-driven random small weighted covering instance
    /// (mirrors the existing differential-test generator; adds random objective
    /// literal polarity so soft-selector complementation is exercised).
    fn random_weighted_instance(next: &mut impl FnMut() -> u64) -> (PbInstance, PbObjective) {
        let num_vars = 3 + (next() % 5) as u32; // 3..=7 vars
        let num_constraints = 1 + (next() % 4) as usize; // 1..=4 constraints

        let mut obj_terms = Vec::new();
        for v in 1..=num_vars {
            let coeff = 1 + (next() % 8) as i128; // weights 1..=8
            let negated = next().is_multiple_of(4);
            obj_terms.push(PbTerm {
                coeff,
                lits: vec![PbLit { var: v, negated }],
            });
        }
        let objective = PbObjective { terms: obj_terms };

        let mut constraints = Vec::new();
        for _ in 0..num_constraints {
            let mut terms = Vec::new();
            for v in 1..=num_vars {
                // ~50% inclusion, random polarity.
                if next().is_multiple_of(2) {
                    terms.push(PbTerm {
                        coeff: 1,
                        lits: vec![PbLit {
                            var: v,
                            negated: next().is_multiple_of(2),
                        }],
                    });
                }
            }
            if terms.is_empty() {
                terms.push(PbTerm {
                    coeff: 1,
                    lits: vec![PbLit {
                        var: 1,
                        negated: false,
                    }],
                });
            }
            let max_rhs = terms.len() as i128;
            let rhs = 1 + (next() as i128 % max_rhs.max(1));
            constraints.push(PbConstraint {
                terms,
                rel: crate::types::PbRel::Ge,
                rhs,
            });
        }

        let instance = PbInstance {
            num_vars,
            num_constraints: num_constraints as u32,
            constraints,
            objective: Some(objective.clone()),
        };
        (instance, objective)
    }

    /// Outcome of [`drive_core_descent`].
    #[derive(Debug, PartialEq, Eq)]
    struct DescentOutcome {
        /// Accumulated lower bound after each core round that made progress
        /// (`CoreOutcome::Continue`), in order.
        trace: Vec<i128>,
        /// Final accumulated lower bound (offset + Σ applied core weights).
        lower_bound: i128,
        /// Objective value of the terminal FULL-STRATUM SAT model, when the
        /// descent ended by realizing one (the OLL proof condition); `None`
        /// otherwise.
        full_stratum_value: Option<i128>,
    }

    /// Drives the raw OLL core descent (no floors / hardening / incumbent
    /// machinery) to completion, processing cores either through the
    /// single-core reference path (`cap == None`, i.e. `process_core`) or
    /// through `process_disjoint_core_round` with the given per-round cap.
    /// Panics on infeasible instances; callers gate on brute-force feasibility.
    fn drive_core_descent(
        instance: &PbInstance,
        objective: &PbObjective,
        cap: Option<usize>,
    ) -> DescentOutcome {
        let (softs, offset) =
            normalize_weighted_softs(objective).expect("single-literal objective");
        let mut stop = || false;
        let mut solver = PbCdclSolver::new_interruptible(instance, &mut stop);
        match solver.solve_with_assumptions_interruptible(&[], &mut stop) {
            PbCdclAssumptionResult::Satisfiable(_) => {}
            other => panic!("descent driver requires a feasible instance, got {other:?}"),
        }
        let mut state = LoopState {
            softs,
            threshold: i128::MAX,
            pending_outputs: std::collections::HashMap::new(),
        };
        state.initialize_threshold();
        let mut lower_bound = offset;
        let mut trace = Vec::new();
        let mut rounds = 0usize;
        loop {
            rounds += 1;
            assert!(rounds < 10_000, "descent did not terminate");
            if state.softs.is_empty() {
                return DescentOutcome {
                    trace,
                    lower_bound,
                    full_stratum_value: None,
                };
            }
            let (assumptions, at_full_stratum) = state.collect_stratum_assumptions();
            match solver.solve_with_assumptions_interruptible(&assumptions, &mut stop) {
                PbCdclAssumptionResult::Satisfiable(model) => {
                    if at_full_stratum {
                        return DescentOutcome {
                            trace,
                            lower_bound,
                            full_stratum_value: Some(eval_objective(objective, &model)),
                        };
                    }
                    state.lower_threshold();
                }
                PbCdclAssumptionResult::Unsatisfiable { core } => {
                    let outcome = match cap {
                        None => {
                            process_core(&mut solver, &mut state, &mut lower_bound, core, &mut stop)
                        }
                        Some(n) => process_disjoint_core_round(
                            &mut solver,
                            &mut state,
                            &mut lower_bound,
                            &assumptions,
                            core,
                            n,
                            &mut stop,
                        ),
                    };
                    match outcome {
                        CoreOutcome::Continue => trace.push(lower_bound),
                        CoreOutcome::Stop => {
                            return DescentOutcome {
                                trace,
                                lower_bound,
                                full_stratum_value: None,
                            }
                        }
                        CoreOutcome::Exhausted => {
                            if at_full_stratum {
                                return DescentOutcome {
                                    trace,
                                    lower_bound,
                                    full_stratum_value: None,
                                };
                            }
                            state.lower_threshold();
                        }
                    }
                }
                PbCdclAssumptionResult::Unknown | PbCdclAssumptionResult::Unsupported => {
                    return DescentOutcome {
                        trace,
                        lower_bound,
                        full_stratum_value: None,
                    }
                }
            }
        }
    }

    /// DIFFERENTIAL GATE (design §3.3): over randomized small weighted
    /// instances the BATCHED disjoint-core round's accumulated lower bound must
    /// NEVER exceed the true (brute-force) optimum at ANY point of the descent
    /// — an overcounting bound is exactly the failure mode that would let OLL
    /// declare a suboptimal incumbent OPTIMUM. When the descent terminates by
    /// realizing a full-stratum SAT model, that model must attain the
    /// accumulated bound exactly (the OLL proof condition), which must equal
    /// the brute-force optimum.
    #[test]
    fn native_oll_batched_lower_bound_never_exceeds_brute_force_optimum() {
        let mut seed: u64 = 0x0DD5_EED5_D15C_C04E;
        let mut next = || {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            seed >> 33
        };

        let mut checked = 0usize;
        for _ in 0..60 {
            let (instance, objective) = random_weighted_instance(&mut next);
            let Some(bf) = brute_force_optimum(&instance, &objective) else {
                continue; // infeasible: no bound to violate
            };
            let descent =
                drive_core_descent(&instance, &objective, Some(MAX_DISJOINT_CORES_PER_ROUND));
            for (round, &lb) in descent.trace.iter().enumerate() {
                assert!(
                    lb <= bf,
                    "batched lower bound {lb} after round {} exceeds true optimum {bf}",
                    round + 1
                );
            }
            assert!(
                descent.lower_bound <= bf,
                "final batched lower bound {} exceeds true optimum {bf}",
                descent.lower_bound
            );
            if let Some(value) = descent.full_stratum_value {
                assert_eq!(value, bf, "full-stratum model value {value} != brute {bf}");
                assert_eq!(
                    descent.lower_bound, bf,
                    "full-stratum bound {} != brute {bf}",
                    descent.lower_bound
                );
            }
            checked += 1;
        }
        assert!(checked >= 40, "only {checked} feasible instances checked");
    }

    /// ROUND-CORE-CAP=1 EQUIVALENCE GATE: with a per-round cap of 1 the batched
    /// entry point must reproduce the single-core reference path exactly —
    /// identical lower-bound trace, identical final bound, identical terminal
    /// full-stratum value — across the randomized suite. (A cap of 1 delegates
    /// to `process_core` by construction; this test pins that contract against
    /// future drift.) End-to-end, the full solve at cap 1 (the old loop) and at
    /// the default cap must both prove the brute-force optimum.
    #[test]
    fn native_oll_round_core_cap_one_matches_single_core_reference() {
        let mut seed: u64 = 0xCAB1_F00D_5EED_2026;
        let mut next = || {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            seed >> 33
        };

        let mut checked = 0usize;
        for _ in 0..40 {
            let (instance, objective) = random_weighted_instance(&mut next);
            let bf = brute_force_optimum(&instance, &objective);

            // End-to-end: cap=1 (the old single-core loop) and the default
            // batched cap must both prove the brute-force optimum.
            let single = solve_with_round_core_cap(&instance, &objective, || false, None, 1, None);
            let batched = solve(&instance, &objective, || false, None, None);
            let Some(opt) = bf else {
                assert_eq!(single, Some(OptResult::Infeasible), "cap=1: {single:?}");
                assert_eq!(batched, Some(OptResult::Infeasible), "batched: {batched:?}");
                continue;
            };
            match (&single, &batched) {
                (Some(OptResult::Optimal(_, s)), Some(OptResult::Optimal(_, b))) => {
                    assert_eq!(*s, opt, "cap=1 optimum {s} != brute {opt}");
                    assert_eq!(*b, opt, "batched optimum {b} != brute {opt}");
                }
                other => panic!("expected proven optima, got {other:?}"),
            }

            // Descent-level: the cap=1 lower-bound trajectory is identical to
            // the single-core reference path.
            let reference = drive_core_descent(&instance, &objective, None);
            let capped = drive_core_descent(&instance, &objective, Some(1));
            assert_eq!(
                reference, capped,
                "cap=1 descent diverged from the single-core reference path"
            );
            checked += 1;
        }
        assert!(checked >= 25, "only {checked} feasible instances checked");
    }

    /// A/B GATE: on k independent unit-cost cores the batched round accumulates
    /// the WHOLE bound (Σ of the disjoint cores' min-weights) in ONE
    /// reformulation round, where the single-core path needs k rounds
    /// (+min-weight per full re-solve) — the documented bound-crawl this change
    /// removes.
    #[test]
    fn native_oll_batched_round_reaches_bound_in_fewer_rounds() {
        // Three independent at-least-one pairs, unit weights: optimum 3.
        let input = "* #variable= 6 #constraint= 3\n\
            min: +1 x1 +1 x2 +1 x3 +1 x4 +1 x5 +1 x6 ;\n\
            +1 x1 +1 x2 >= 1 ;\n\
            +1 x3 +1 x4 >= 1 ;\n\
            +1 x5 +1 x6 >= 1 ;\n";
        let instance = parse_opb(input).expect("parse OPB");
        let objective = instance.objective.clone().expect("has objective");
        assert_eq!(brute_force_optimum(&instance, &objective), Some(3));

        let batched = drive_core_descent(&instance, &objective, Some(MAX_DISJOINT_CORES_PER_ROUND));
        let single = drive_core_descent(&instance, &objective, Some(1));

        // Both reach the same sound bound and realize it at the full stratum.
        assert_eq!(batched.lower_bound, 3, "batched: {batched:?}");
        assert_eq!(single.lower_bound, 3, "single: {single:?}");
        assert_eq!(batched.full_stratum_value, Some(3));
        assert_eq!(single.full_stratum_value, Some(3));
        // ONE batched round accumulates Σ core weights = 3 ...
        assert_eq!(
            batched.trace,
            vec![3],
            "batched round must accumulate the sum of all disjoint core weights in one round"
        );
        // ... where the single-core path crawls +min-weight per solve round.
        assert_eq!(single.trace, vec![1, 2, 3]);
        assert!(batched.trace.len() < single.trace.len());
    }

    // ---- External ub cutoff (SharedBounds DOWN-channel, design §2.7) ----

    /// Brute-force exact minimum + witnessing model over all 2^n assignments.
    fn brute_force_optimum_with_model(
        instance: &PbInstance,
        objective: &PbObjective,
    ) -> Option<(Vec<bool>, i128)> {
        let n = instance.num_vars as usize;
        assert!(n <= 20, "brute force only for tiny instances");
        let mut best: Option<(Vec<bool>, i128)> = None;
        for mask in 0u32..(1u32 << n) {
            let assignment: Vec<bool> = (0..n).map(|i| (mask >> i) & 1 == 1).collect();
            if !crate::eval::verify_all_constraints(&instance.constraints, &assignment) {
                continue;
            }
            let value = eval_objective(objective, &assignment);
            if best.as_ref().is_none_or(|(_, b)| value < *b) {
                best = Some((assignment, value));
            }
        }
        best
    }

    /// UNIT: the pure install-decision core. `None` (absent bus / never
    /// published / overflow-REJECTED at the i128->i64 boundary) is NO CUTOFF —
    /// never "0/unbounded-good" — and the row fires exactly when strictly
    /// tighter than both the engine's own incumbent and the installed row.
    #[test]
    fn external_cutoff_row_decision_treats_absence_as_no_cutoff_and_fires_when_tighter() {
        // Absent bus value: NO row, regardless of engine state.
        assert_eq!(external_cutoff_row_wanted(None, 100, None), None);
        assert_eq!(external_cutoff_row_wanted(None, i128::MIN, Some(5)), None);
        // An overflow-rejected publish leaves the bus absent: same reading.
        let bus = SharedBounds::new();
        assert!(!bus.publish_incumbent(i128::MAX, &[true]));
        assert_eq!(external_cutoff_row_wanted(bus.ub(), 100, None), None);

        // Fires exactly when strictly below the engine's own incumbent.
        assert_eq!(external_cutoff_row_wanted(Some(7), 8, None), Some(7));
        assert_eq!(external_cutoff_row_wanted(Some(8), 8, None), None);
        assert_eq!(external_cutoff_row_wanted(Some(9), 8, None), None);
        // Negative (maximization-shaped) cutoffs work unchanged.
        assert_eq!(external_cutoff_row_wanted(Some(-3), -1, None), Some(-3));

        // Monotone re-install: only a strictly tighter cutoff than the row
        // already in the solver fires again.
        assert_eq!(external_cutoff_row_wanted(Some(7), 100, Some(7)), None);
        assert_eq!(external_cutoff_row_wanted(Some(6), 100, Some(7)), Some(6));
    }

    /// An engine handed a PRESENT but EMPTY bus behaves identically to the
    /// bus-free engine (absence == no cutoff, end to end).
    #[test]
    fn external_ub_cutoff_empty_bus_is_identical_to_no_bus() {
        let input = "* #variable= 4 #constraint= 3\n\
            min: +1 x1 +2 x2 +3 x3 +4 x4 ;\n\
            +1 x1 +1 x2 +1 x3 +1 x4 >= 2 ;\n\
            +1 x1 +1 x3 >= 1 ;\n\
            +1 x2 +1 x4 >= 1 ;\n";
        let instance = parse_opb(input).expect("parse OPB");
        let objective = instance.objective.clone().expect("has objective");
        let bus = SharedBounds::new();
        let with_empty_bus = solve(&instance, &objective, || false, None, Some(&bus));
        let without_bus = solve(&instance, &objective, || false, None, None);
        assert_eq!(with_empty_bus, without_bus);
        assert!(matches!(with_empty_bus, Some(OptResult::Optimal(_, 3))));
    }

    /// MANDATORY DIFFERENTIAL (design §7-P3 gate): with a VALID bus cutoff (the
    /// coordinator only ever publishes sanitize-verified values, so in contract
    /// the bus ub is the exact objective of a feasible model), the engine
    /// * never returns a (model, value) pair whose value differs from its own
    ///   model's exact objective (the §2.7 desync fix: the cutoff must never
    ///   overwrite `best_value`),
    /// * never LOSES or WORSENS a claimed optimum relative to the bus-free
    ///   run, and
    /// * never returns an incumbent better than the true (brute-force) optimum.
    #[test]
    fn external_ub_cutoff_differential_prunes_without_desync_or_worse_claims() {
        let mut seed: u64 = 0xB0BA_F377_5EED_CAFE;
        let mut next = || {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            seed >> 33
        };

        let mut checked = 0usize;
        for _ in 0..40 {
            let (instance, objective) = random_weighted_instance(&mut next);
            let Some((bf_model, bf_value)) = brute_force_optimum_with_model(&instance, &objective)
            else {
                // Infeasible: nothing for a bus to publish; covered elsewhere.
                continue;
            };

            let without = solve(&instance, &objective, || false, None, None);

            // In-contract bus: the verified optimum-valued incumbent — the
            // tightest cutoff a valid coordinator can ever publish, so the
            // prune row fires whenever the engine's own incumbent lags.
            let bus = SharedBounds::new();
            assert!(bus.publish_incumbent(bf_value, &bf_model));
            let with = solve(&instance, &objective, || false, None, Some(&bus));

            // (model, value) self-consistency of every returned pair.
            for (label, result) in [("without", &without), ("with", &with)] {
                match result {
                    Some(OptResult::Optimal(model, value))
                    | Some(OptResult::Satisfiable(model, value)) => {
                        assert!(
                            crate::eval::verify_all_constraints(&instance.constraints, model),
                            "{label}: returned model violates a constraint"
                        );
                        assert_eq!(
                            eval_objective(&objective, model),
                            *value,
                            "{label}: value desynced from its own model"
                        );
                        assert!(
                            *value >= bf_value,
                            "{label}: incumbent {value} beats the true optimum {bf_value}"
                        );
                    }
                    other => panic!("{label}: unexpected result {other:?}"),
                }
            }

            // Claim comparison: the cutoff may only PRUNE — a claimed optimum
            // must never be lost or worsened by the bus.
            match (&without, &with) {
                (Some(OptResult::Optimal(_, v0)), Some(OptResult::Optimal(_, v1))) => {
                    assert_eq!(v0, v1, "with-cutoff claimed a different optimum");
                    assert_eq!(*v1, bf_value);
                }
                (Some(OptResult::Optimal(_, _)), other) => {
                    panic!("with-cutoff LOST the bus-free optimum claim: {other:?}")
                }
                // A claim the bus-free run does not make is fine (the prune
                // can only accelerate); anything else was caught above.
                _ => {}
            }
            checked += 1;
        }
        assert!(checked >= 25, "only {checked} feasible instances checked");
    }

    /// Regression: the instance that exposed the OLL hardening/core collapse must be
    /// solved to the proven optimum 4 WITH reduced-cost fixing enabled (it was
    /// returning a stale Satisfiable(6) before the post-fix re-solve was added).
    #[test]
    fn native_oll_reduced_cost_fixing_solves_hardening_collapse_regression() {
        let _g = lock_env();
        let input = "* #variable= 5 #constraint= 1\n\
            min: +4 x1 +92 ~x2 +6 x3 +3 x4 +10 x5 ;\n\
            +1 x1 +1 x2 +1 x3 >= 2 ;\n";
        let instance = parse_opb(input).expect("parse");
        let objective = instance.objective.clone().expect("obj");
        let with = {
            let _rc = ScopedEnvVar::set(REDUCED_COST_ENV, "on");
            solve(&instance, &objective, || false, None, None)
        };
        assert!(
            matches!(with, Some(OptResult::Optimal(_, 4))),
            "expected proven Optimal(4) WITH reduced-cost fixing, got {with:?}"
        );
    }

    /// MANDATORY DIFFERENTIAL: the proven optimum WITH reduced-cost fixing must
    /// equal the optimum WITHOUT it, and both must equal brute force. A too-
    /// aggressive fix that removed the optimum would make the WITH run disagree.
    #[test]
    fn native_oll_reduced_cost_fixing_preserves_optimum_vs_disabled_and_brute_force() {
        let _guard = lock_env();

        let mut seed: u64 = 0xD1CE_F00D_2024_BEEF;
        let mut next = || {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            seed >> 33
        };

        let mut checked = 0usize;
        for _ in 0..60 {
            let num_vars = 3 + (next() % 6) as u32; // 3..=8 vars
            let num_constraints = 1 + (next() % 4) as usize; // 1..=4 constraints

            let mut obj_terms = Vec::new();
            for v in 1..=num_vars {
                // Wide weight spread (incl. a few very large) so reduced costs are
                // big enough to actually fix variables.
                let coeff = match next() % 10 {
                    0 => 50 + (next() % 50) as i128,
                    _ => 1 + (next() % 10) as i128,
                };
                let negated = next() % 4 == 0;
                obj_terms.push(PbTerm {
                    coeff,
                    lits: vec![PbLit { var: v, negated }],
                });
            }
            let objective = PbObjective { terms: obj_terms };

            let mut constraints = Vec::new();
            for _ in 0..num_constraints {
                let mut terms = Vec::new();
                for v in 1..=num_vars {
                    if next() % 2 == 0 {
                        terms.push(PbTerm {
                            coeff: 1,
                            lits: vec![PbLit {
                                var: v,
                                negated: next() % 2 == 0,
                            }],
                        });
                    }
                }
                if terms.is_empty() {
                    terms.push(PbTerm {
                        coeff: 1,
                        lits: vec![PbLit {
                            var: 1,
                            negated: false,
                        }],
                    });
                }
                let max_rhs = terms.len() as i128;
                let rhs = 1 + (next() as i128 % max_rhs.max(1));
                constraints.push(PbConstraint {
                    terms,
                    rel: crate::types::PbRel::Ge,
                    rhs,
                });
            }

            let instance = PbInstance {
                num_vars,
                num_constraints: num_constraints as u32,
                constraints,
                objective: Some(objective.clone()),
            };

            let bf = brute_force_optimum(&instance, &objective);

            // WITHOUT reduced-cost fixing (default OFF).
            let without = {
                let _rc = ScopedEnvVar::set(REDUCED_COST_ENV, "off");
                solve(&instance, &objective, || false, None, None)
            };
            // WITH reduced-cost fixing (opt-in).
            let with = {
                let _rc = ScopedEnvVar::set(REDUCED_COST_ENV, "on");
                solve(&instance, &objective, || false, None, None)
            };

            let opt_of = |r: &Option<OptResult>| match r {
                Some(OptResult::Optimal(_, v)) => Some(*v),
                _ => None,
            };

            match bf {
                None => {
                    assert_eq!(without, Some(OptResult::Infeasible), "WITHOUT: {without:?}");
                    assert_eq!(with, Some(OptResult::Infeasible), "WITH: {with:?}");
                }
                Some(opt) => {
                    let (Some(wo), Some(w)) = (opt_of(&without), opt_of(&with)) else {
                        panic!(
                            "expected proven optima; without={without:?} with={with:?} \
                             brute={opt:?}"
                        );
                    };
                    assert_eq!(wo, opt, "WITHOUT optimum {wo} != brute {opt}");
                    assert_eq!(
                        w, opt,
                        "WITH reduced-cost optimum {w} != brute {opt} (fixing removed the optimum!)"
                    );
                    // Verify the WITH model is feasible against ORIGINAL constraints.
                    if let Some(OptResult::Optimal(model, value)) = &with {
                        assert!(
                            crate::eval::verify_all_constraints(&instance.constraints, model),
                            "WITH optimal model must satisfy all original constraints"
                        );
                        assert_eq!(eval_objective(&objective, model), *value);
                    }
                }
            }
            checked += 1;
        }
        assert!(checked >= 60);
    }

    // ---- Real instance optima vs Exact (gated by file availability) ----

    /// Resolves a PB-competition corpus file under the checkout-relative
    /// `benchmarks/pb-comp/<rel>` (B14: the env override nothing set is
    /// deleted; a relocated corpus is a symlink). The corpus is not tracked
    /// in git; tests skip when the file is absent.
    fn pbcomp_path(rel: &str) -> String {
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../benchmarks/pb-comp")
            .join(rel)
            .display()
            .to_string()
    }

    fn opb_path_optimum(rel: &str, expected: i128) {
        let path = pbcomp_path(rel);
        let Ok(text) = std::fs::read_to_string(&path) else {
            eprintln!("skipping {path}: not available");
            return;
        };
        let instance = parse_opb(&text).expect("parse OPB");
        let objective = instance.objective.clone().expect("has objective");
        let result =
            solve(&instance, &objective, || false, None, None).expect("native OLL should apply");
        assert_eq!(
            optimum_value(&result),
            Some(expected),
            "native OLL optimum for {path} must match Exact ({expected}); got {result:?}"
        );
    }

    fn wbo_path_optimum(rel: &str, expected: i128) {
        let path = pbcomp_path(rel);
        let Ok(text) = std::fs::read_to_string(&path) else {
            eprintln!("skipping {path}: not available");
            return;
        };
        let wbo = parse_wbo(&text).expect("parse WBO");
        let instance = crate::optimize::wbo::wbo_to_pbo(&wbo);
        let objective = instance
            .objective
            .clone()
            .expect("WBO conversion yields objective");
        let result =
            solve(&instance, &objective, || false, None, None).expect("native OLL should apply");
        assert_eq!(
            optimum_value(&result),
            Some(expected),
            "native OLL optimum for {path} must match Exact ({expected}); got {result:?}"
        );
    }

    #[test]
    fn native_oll_matches_exact_on_real_opt_lin_lo_6x6() {
        opb_path_optimum(
            "PB24/normalized-PB15eval/OPT-LIN/dt-problems/normalized-lo_6x6_000.opb.metafix.opb",
            16,
        );
    }

    #[test]
    fn native_oll_matches_exact_on_real_opt_lin_lo_8x8() {
        opb_path_optimum(
            "PB24/normalized-PB15eval/OPT-LIN/dt-problems/normalized-lo_8x8_000.opb.metafix.opb",
            30,
        );
    }

    /// A third, larger OPT-LIN instance (lo_10x10, optimum 42 per Exact). Native
    /// OLL reaches a sound result here; under a bounded budget it may return a
    /// feasible incumbent rather than the proof, so this enforces the anytime
    /// soundness contract (proven optimum must equal 42; any incumbent must be
    /// feasible and never beat 42).
    #[test]
    fn native_oll_on_real_opt_lin_lo_10x10_is_sound_anytime() {
        let path = pbcomp_path(
            "PB24/normalized-PB15eval/OPT-LIN/dt-problems/normalized-lo_10x10_002.opb.metafix.opb",
        );
        let Ok(text) = std::fs::read_to_string(&path) else {
            eprintln!("skipping {path}: not available");
            return;
        };
        let instance = parse_opb(&text).expect("parse OPB");
        let objective = instance.objective.clone().expect("objective");
        let start = std::time::Instant::now();
        let result = solve(
            &instance,
            &objective,
            || start.elapsed() >= std::time::Duration::from_secs(15),
            None,
            None,
        )
        .expect("native OLL applies");
        match result {
            OptResult::Optimal(assignment, value) => {
                assert_eq!(value, 42, "false optimum: claimed {value}, true is 42");
                assert!(verify_native_optimum(
                    &instance,
                    &objective,
                    &assignment,
                    value,
                    value,
                    value
                ));
            }
            OptResult::Satisfiable(assignment, value) => {
                assert!(
                    crate::eval::verify_all_constraints(&instance.constraints, &assignment),
                    "incumbent must satisfy all hard constraints"
                );
                assert_eq!(eval_objective(&objective, &assignment), value);
                assert!(
                    value >= 42,
                    "incumbent {value} beats true optimum 42 (unsound)"
                );
            }
            other => panic!("unexpected result for lo_10x10: {other:?}"),
        }
    }

    /// spot5-54 (optimum 37 per Exact) is the hardest of the verification
    /// targets: the native PB engine reaches a strong lower bound and feasible
    /// incumbent but does not always prove this specific instance to optimality
    /// within a bounded budget (the full ay-pb portfolio is similarly short of 37
    /// here). This test therefore enforces the SOUNDNESS contract rather than
    /// exact optimality: any result must be a valid anytime answer -- either the
    /// proven optimum 37, or a feasible incumbent that is NEVER falsely claimed
    /// optimal and never better than the true optimum (>= 37).
    #[test]
    fn native_oll_on_real_wbo_spot5_54_is_sound_anytime() {
        let path = pbcomp_path("PB24/WBO/PARTIAL-LIN/wcsp/spot5/normalized-spot5-54_wcsp.wbo");
        let Ok(text) = std::fs::read_to_string(&path) else {
            eprintln!("skipping {path}: not available");
            return;
        };
        let wbo = parse_wbo(&text).expect("parse WBO");
        let instance = crate::optimize::wbo::wbo_to_pbo(&wbo);
        let objective = instance.objective.clone().expect("objective");
        // Bound the work so the test stays fast; anytime semantics apply.
        let start = std::time::Instant::now();
        let result = solve(
            &instance,
            &objective,
            || start.elapsed() >= std::time::Duration::from_secs(20),
            None,
            None,
        )
        .expect("native OLL applies");
        match result {
            OptResult::Optimal(assignment, value) => {
                // If proven optimal, it MUST be the true optimum 37 and verify.
                assert_eq!(value, 37, "false optimum: claimed {value}, true is 37");
                assert!(verify_native_optimum(
                    &instance,
                    &objective,
                    &assignment,
                    value,
                    value,
                    value
                ));
            }
            OptResult::Satisfiable(assignment, value) => {
                // A feasible incumbent: must satisfy all constraints, evaluate to
                // `value`, and never beat the true optimum (no unsound under-shoot).
                assert!(
                    crate::eval::verify_all_constraints(&instance.constraints, &assignment),
                    "incumbent must satisfy all hard constraints"
                );
                assert_eq!(eval_objective(&objective, &assignment), value);
                assert!(
                    value >= 37,
                    "incumbent {value} beats true optimum 37 (unsound)"
                );
            }
            other => panic!("unexpected result for spot5-54: {other:?}"),
        }
    }

    #[test]
    fn native_oll_matches_exact_on_real_wbo_warehouse0() {
        wbo_path_optimum(
            "PB24/WBO/PARTIAL-LIN/wcsp/academics/normalized-warehouse0_wcsp.wbo",
            328,
        );
    }

    /// The incremental-totalizer clause-emission loop must honor the cooperative
    /// stop signal. A large OLL core builds a totalizer with hundreds of thousands
    /// of clauses, each emitted via a level-0 propagating `add_cardinality_runtime`;
    /// before the deadline poll was threaded into the emission loop this ran for
    /// minutes regardless of the budget (the lp4l ~356s/60s overrun). On a stop trip
    /// the function must BAIL with `None` (which `process_core` maps to a sound
    /// `CoreOutcome::Stop`), and with no stop it must complete and return the
    /// per-threshold output selectors.
    #[test]
    fn incremental_totalizer_bails_on_stop_and_completes_in_budget() {
        let input = "* #variable= 4 #constraint= 1\n\
            min: +1 x1 +1 x2 +1 x3 +1 x4 ;\n\
            +1 x1 +1 x2 +1 x3 +1 x4 >= 1 ;\n";
        let instance = parse_opb(input).expect("parse OPB");

        let inputs: Vec<PbLit> = (1..=4)
            .map(|var| PbLit {
                var,
                negated: false,
            })
            .collect();

        // (a) Forced stop: emission must bail with None at the first poll (the poll
        // fires at clause index 0), abandoning the proof rather than overrunning.
        {
            let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
            let mut always_stop = || true;
            let bailed = encode_incremental_totalizer(&mut solver, &inputs, &mut always_stop);
            assert!(
                bailed.is_none(),
                "totalizer emission must bail to None on a stop trip"
            );
        }

        // (b) No stop: emission completes and yields the threshold outputs. A
        // 4-input at-least-n totalizer exposes the high-threshold (>= 2) selectors
        // the OLL core descent relaxes on, so the output set is non-empty.
        {
            let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
            let mut never_stop = || false;
            let outputs = encode_incremental_totalizer(&mut solver, &inputs, &mut never_stop)
                .expect("totalizer must complete when the budget is not exhausted");
            assert!(
                !outputs.is_empty(),
                "a multi-input totalizer must expose threshold outputs"
            );
        }
    }
}
