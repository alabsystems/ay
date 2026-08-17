// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Catamorphism-abstraction lane for recursive-ADT CHC problems (CHC-COMP
//! agenda #7, "CATA v1"). Routing: recursive-datatype problems reach this
//! pre-strategy before the class dispatch; non-recursive datatype problems
//! keep the exact `DtFlattener` pipelines. Kill switch:
//! `AY_CHC_DISABLE_CATA=1`.
//!
//! The lane's verdict discipline (agenda gating, non-negotiable):
//!
//! - **SAT side** — abstract SAT ⇒ original SAT holds ONLY under the
//!   per-clause implication obligations `θ ⇒ θ#`, so the route accepts an
//!   abstract Safe iff (1) EVERY obligation is discharged `unsat` by a fresh
//!   ADT+LIA+UF SMT query and (2) the abstract model fully re-verifies against
//!   every abstract clause in a fresh verifier. Only then is the composed
//!   original-vocabulary model returned, stamped
//!   [`ValidationEvidence::CataAbstraction`]. Any failure ⇒ refine or fall
//!   through (unknown). `define-fun-rec` re-verification on the original
//!   clauses is not dischargeable by the ay executor (bounded macro expansion
//!   diverges on symbolic ADT arguments), so the per-clause induction
//!   obligations ARE the original-clause certificate — exactly the fallback
//!   the agenda prescribes.
//! - **UNSAT side** — an abstract counterexample is NEVER reported. It is
//!   used only as a depth hint to concretize on the ORIGINAL clauses with
//!   bounded BMC; a concrete counterexample then flows through the standard
//!   `validate_final_unsafe_result` replay gate in
//!   `finalize_verified_result_with_deadline` (fail-closed). Infeasible
//!   concretization ⇒ refine by adding the next catamorphism from the pool.

use std::time::Duration;

// The workspace-wide monotonic clock shim (#wasm port): byte-identical to
// `std::time::Instant` on native targets, host-clock-backed on wasm32 (raw
// `std::time::Instant` panics there and breaks the wasm build).
use ay_core::time::Instant;

use crate::adaptive::{AdaptiveConfig, AdaptivePortfolio};
use crate::adaptive_decision_log::DecisionEntry;
use crate::bmc::{BmcConfig, BmcSolver};
use crate::engine_config::ChcEngineConfig;
use crate::engine_result::ValidationEvidence;
use crate::pdr::PdrConfig;
use crate::portfolio::PortfolioResult;
use crate::transform::cata_abstract::{build_cata_ladder, CataAbstraction};

/// Kill switch: set to any value to disable the catamorphism lane.

/// Kill switch for the CATA v2 multi-predicate affine-Houdini abstract solver
/// (default ON). Setting it forces the v1 nested-portfolio abstract solve only.

/// Toggle for the CATA v2 depth-1 GUARDED candidate families (flag-guarded
/// ordering facts + non-convex min recurrences). Default ON; set
/// `AY_CHC_CATA_GUARDED=0` (or `off`/`false`/`no`) to suppress them — the
/// affine Houdini then runs with an EMPTY tags map, so its candidate pool is
/// byte-identical to the pure-conjunctive path.
const CATA_GUARDED_ENV: &str = "AY_CHC_CATA_GUARDED";
/// Budget for the affine-Houdini abstract solve at one ladder level.
const CATA_AFFINE_HOUDINI_CAP: Duration = Duration::from_secs(12);
/// Kill switch for the CATA v3 disjunctive (exact predicate-abstraction) ICE
/// learner (default ON). Set `AY_CHC_CATA_ICE=0` to disable.
const CATA_ICE_ENV: &str = "AY_CHC_CATA_ICE";
/// Budget for the disjunctive ICE learner at one ladder level.
const CATA_ICE_CAP: Duration = Duration::from_secs(30);
/// Kill switch for the CATA v3 disjunctive learner on the NON-sorted (nat-peano
/// / element-free) size levels (default ON). The sorted-level disjunctive lane
/// is gated separately by `AY_CHC_CATA_ICE`; this switch ONLY governs the
/// element-free extension. Set `AY_CHC_CATA_DISJ_NONSORT=0` to make the route
/// byte-identical to the pre-extension baseline on every problem.
const CATA_DISJ_NONSORT_ENV: &str = "AY_CHC_CATA_DISJ_NONSORT";
/// Sub-switch for the CATA v3 GENERALIZING decision-tree learner (Horn-ICE-DT),
/// the PRIMARY sorted-level strategy (default ON). Set `AY_CHC_CATA_ICE_DT=0` to
/// fall back to the exact-fixpoint DNF learner alone (A/B lever). Gated under
/// `AY_CHC_CATA_ICE`, so disabling that kills both learners.
const CATA_ICE_DT_ENV: &str = "AY_CHC_CATA_ICE_DT";
/// Budget slice for the DT learner before the DNF learner runs as fallback. The
/// DT learner converges in seconds when it wins and its divergence guard bails
/// within this slice, so the DNF fallback always keeps a workable remainder.
const CATA_ICE_DT_CAP: Duration = Duration::from_secs(20);
/// Sub-switch for the ADDITIVE flag-only DT retry (default ON). After the full
/// vocabulary DT + exact DNF fixpoint both fail, the learner retries the DT over
/// the compact `AtomProfile::FlagsOnly` vocabulary — the atom set that converts
/// the WIDE sortedness family (`BSortSorts` and relatives), where the full
/// vocabulary hits the ay-dpll `Unknown` / SMT-latency walls. Purely additive:
/// it runs only when the primary attempts return no model, and its result is
/// re-certified by the same gate. Set `AY_CHC_CATA_ICE_FLAGS=0` to disable.
const CATA_ICE_FLAGS_ENV: &str = "AY_CHC_CATA_ICE_FLAGS";
/// Per-level cap on the fallback nested-portfolio abstract solve. Bounds how
/// much any single early ladder level can consume so the route reliably climbs
/// to the element/ordering (sortedness) levels within the route budget — the
/// disjunctive ICE learner is the intended solver there and is fast when it
/// succeeds. Affine-Houdini (≤12 s) and the ICE learner (≤30 s) run BEFORE this
/// and return on the first certified verdict, so the size-family conversions
/// (which those two produce) are unaffected.
const CATA_NESTED_SOLVE_CAP: Duration = Duration::from_secs(12);

/// Structural cap: clause count above which the lane does not engage.
const CATA_MAX_CLAUSES: usize = 2048;
/// Nominal / scaling parameters for the route budget. The nominal floor must
/// leave the nested abstract solve a workable slice per refinement level —
/// the lane is the primary lever on the recursive-ADT tracks, so it earns a
/// generous pre-pass budget.
const CATA_NOMINAL_BUDGET: Duration = Duration::from_secs(20);
const CATA_BUDGET_PERCENT: u32 = 30;
const CATA_BUDGET_CAP: Duration = Duration::from_mins(1);
/// Bounded budget EXTENSION granted to the element/ordering (sortedness) ladder
/// levels beyond the route budget, so the size-family levels keep their EXACT
/// baseline schedule (zero size-family regression — the size levels are
/// byte-identical to the pre-v3 route) while the element levels still get enough
/// time for the CATA v3 ICE learner to reach and solve the sortedness level.
/// Only spent by instances that fail every size level and climb into the
/// element levels (a size-family Safe returns at its size level and never sees
/// this); always capped by the overall solve deadline.
const CATA_ELEMENT_EXTENSION: Duration = Duration::from_secs(45);
/// Minimum route budget for the CATA v3 element/ICE enhancements (reserve, ICE
/// learner, affine-skip + nested-cap at element levels) to engage. Below this,
/// the route is BYTE-IDENTICAL to the pre-v3 baseline: the disjunctive
/// sortedness invariant needs the learner to reach the element level AND solve
/// + re-certify (empirically ~45 s of route budget on `ISortSorts`), which a
/// tight per-instance budget (e.g. the 40 s competition sample ⇒ ~20 s route)
/// cannot afford — so stealing size-level budget there would only regress the
/// size family for no possible sortedness win. This gate makes the feature a
/// no-op at sample budgets (0 regression by construction) and active only at
/// competition-scale budgets.
const CATA_ELEMENT_MIN_BUDGET: Duration = Duration::from_secs(45);
/// Per-obligation SMT budget and per-level obligation-total cap.
const CATA_PER_OBLIGATION_BUDGET: Duration = Duration::from_millis(1500);
const CATA_OBLIGATIONS_TOTAL_CAP: Duration = Duration::from_secs(5);
/// Element/ordering levels (Min/Max/Sorted) discharge their obligations
/// CONJUNCT-BY-CONJUNCT (see `CataAbstraction::obligation_sub_scripts`): each
/// sub-query is a millisecond-scale `θ ∧ ¬θ#ᵢ ⊨ ⊥`, but a sortedness clause has
/// 100+ such conjuncts, so the per-LEVEL total needs more headroom than the
/// size family's monolithic 5 s. Still bounded by the level deadline (the 45 s
/// element extension divided across the element levels), so this only widens
/// the cap where the split makes each individual query cheap.
const CATA_ELEMENT_OBLIGATIONS_TOTAL_CAP: Duration = Duration::from_secs(20);
/// Fresh full re-verification budget for the abstract model.
const CATA_ABSTRACT_VERIFY_CAP: Duration = Duration::from_secs(6);
/// Extra unrolling slack over the abstract counterexample depth.
const CATA_CEX_DEPTH_SLACK: usize = 2;

fn cata_lane_disabled() -> bool {
    !crate::ab_switches::get().cata_route
}

fn cata_v2_disabled() -> bool {
    !crate::ab_switches::get().cata_v2
}

/// CATA v3 disjunctive ICE learner: ON by default, off only when
/// `AY_CHC_CATA_ICE` is explicitly set to a falsy value.
fn cata_ice_enabled() -> bool {
    match std::env::var(CATA_ICE_ENV) {
        Ok(v) => !matches!(
            v.trim().to_ascii_lowercase().as_str(),
            "0" | "off" | "false" | "no"
        ),
        Err(_) => true,
    }
}

/// CATA v3 Horn-ICE decision-tree learner (primary sorted-level strategy): ON
/// by default, off only when `AY_CHC_CATA_ICE_DT` is explicitly falsy — then
/// the exact-fixpoint DNF learner runs alone.
fn cata_ice_dt_enabled() -> bool {
    match std::env::var(CATA_ICE_DT_ENV) {
        Ok(v) => !matches!(
            v.trim().to_ascii_lowercase().as_str(),
            "0" | "off" | "false" | "no"
        ),
        Err(_) => true,
    }
}

/// Additive flag-only DT retry for the wide sortedness family: ON by default,
/// off only when `AY_CHC_CATA_ICE_FLAGS` is explicitly falsy.
fn cata_ice_flags_enabled() -> bool {
    match std::env::var(CATA_ICE_FLAGS_ENV) {
        Ok(v) => !matches!(
            v.trim().to_ascii_lowercase().as_str(),
            "0" | "off" | "false" | "no"
        ),
        Err(_) => true,
    }
}

/// Disjunctive learner on the element-free (nat-peano) size levels: ON by
/// default, off only when `AY_CHC_CATA_DISJ_NONSORT` is explicitly falsy.
fn cata_disj_nonsort_enabled() -> bool {
    match std::env::var(CATA_DISJ_NONSORT_ENV) {
        Ok(v) => !matches!(
            v.trim().to_ascii_lowercase().as_str(),
            "0" | "off" | "false" | "no"
        ),
        Err(_) => true,
    }
}

/// Depth-1 guarded candidate families: ON by default, off only when
/// `AY_CHC_CATA_GUARDED` is explicitly set to a falsy value.
fn cata_guarded_enabled() -> bool {
    match std::env::var(CATA_GUARDED_ENV) {
        Ok(v) => !matches!(
            v.trim().to_ascii_lowercase().as_str(),
            "0" | "off" | "false" | "no"
        ),
        Err(_) => true,
    }
}

impl AdaptivePortfolio {
    /// Catamorphism-abstraction pre-strategy for recursive-ADT problems.
    ///
    /// Returns `Some((result, evidence))` only for a fully certified Safe
    /// (composite obligation + abstract-model certification) or a CONCRETE
    /// original-clause counterexample found by abstract-cex-guided BMC (which
    /// the finalize boundary independently replays). Everything else returns
    /// `None` so the normal adaptive pipeline runs.
    pub(crate) fn try_cata_abstraction_route(
        &self,
        deadline: Option<Instant>,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        if cata_lane_disabled() {
            return None;
        }
        // Route gate: the cata lane owns RECURSIVE datatypes; non-recursive
        // datatype problems keep the exact DtFlattener pipelines. Mixed
        // theories (arrays/reals/BV) are out of v1 scope.
        if !self.problem.has_recursive_datatype_sorts()
            || self.problem.has_array_sorts()
            || self.problem.has_real_sorts()
            || self.problem.has_bv_sorts()
            || self.problem.clauses().len() > CATA_MAX_CLAUSES
        {
            return None;
        }

        let route_start = Instant::now();
        let route_budget = self.scaled_probe_budget(
            deadline,
            CATA_NOMINAL_BUDGET,
            CATA_BUDGET_PERCENT,
            CATA_BUDGET_CAP,
        );
        if route_budget < Duration::from_millis(500) {
            return None;
        }
        let route_deadline = route_start + route_budget;

        // CATA v3 element/ordering levels (Min/Max projections, sortedness
        // fold). Appended AFTER the exact v2 size-family ladder, so instances
        // the size family already certifies return before any element level
        // runs (the landed conversions are provably unaffected). Every verdict
        // still passes the same fail-closed certificate gate (obligations +
        // abstract re-verification + query gate), so the lever is 0-wrong by
        // construction. Opt-out: `--chc-no-cata-elements` (B27: env retired).
        let element_catas = crate::ab_switches::get().cata_elements; // B27: CLI-owned.
        let ladder = build_cata_ladder(&self.problem, element_catas);
        if ladder.is_empty() {
            return None;
        }

        let levels = ladder.len();
        // Element/ordering levels (a `Min`/`Max`/`Sorted` column) need a
        // GUARANTEED budget slice: their disjunctive invariant is only found by
        // the CATA v3 ICE learner, and the front-loaded size-family levels would
        // otherwise consume the whole route budget (affine-Houdini alone burns
        // up to its cap per level before returning None on a sortedness
        // instance). Instead of STEALING size-level budget (which would regress
        // the size family), the element levels run in a bounded EXTENSION beyond
        // the route budget: the size levels keep their EXACT baseline schedule
        // (byte-identical), and only an instance that fails every size level and
        // climbs into the element levels spends the extension.
        let is_elem_level = |pool: &[crate::transform::cata_abstract::CataKind]| {
            pool.iter().any(|k| {
                matches!(
                    k,
                    crate::transform::cata_abstract::CataKind::Min
                        | crate::transform::cata_abstract::CataKind::Max
                        | crate::transform::cata_abstract::CataKind::Sorted
                )
            })
        };
        let n_elem = ladder.iter().filter(|p| is_elem_level(p)).count();
        // ELEMENT-FREE class (nat-peano / structural ADT with no Int payload):
        // `build_cata_ladder` appends Min/Max/Sorted levels ONLY when a datatype
        // carries Int fields, so `n_elem == 0` ⟺ the ladder is size-family only
        // ⟺ the sorted-level disjunctive lane can never fire. This is exactly the
        // class whose safety invariant is disjunctive over Peano sizes yet has no
        // sorted level to route it — the nonsort disjunctive lane targets it.
        let element_free = n_elem == 0;
        // "Enhanced" mode: the v3 element/ICE machinery engages ONLY when the
        // ladder has element levels AND the route budget is large enough to
        // possibly win a sortedness instance. Otherwise the route is
        // byte-identical to the pre-v3 baseline (no extension, no ICE, no
        // affine-skip, no nested cap) — so tight per-instance budgets never
        // regress the size family.
        let enhanced = n_elem > 0 && route_budget >= CATA_ELEMENT_MIN_BUDGET;
        // Element levels get the route budget PLUS a bounded extension, capped by
        // the overall solve deadline; size levels use the plain route deadline.
        let elem_deadline = if enhanced {
            let extended = route_deadline + CATA_ELEMENT_EXTENSION;
            match deadline {
                Some(d) => extended.min(d),
                None => extended,
            }
        } else {
            route_deadline
        };

        // Cross-level memo for the Unsafe-arm concretization BMC (see
        // `try_cata_level`): highest depth hint already searched to completion
        // on the ORIGINAL clauses with no counterexample found.
        let mut bmc_no_cex_depth: Option<usize> = None;
        for (level, pool) in ladder.iter().enumerate() {
            let now = Instant::now();
            let is_elem = enhanced && is_elem_level(pool);
            let this_deadline = if is_elem {
                elem_deadline
            } else {
                route_deadline
            };
            let remaining = this_deadline.saturating_duration_since(now);
            if remaining < Duration::from_millis(250) {
                if !enhanced || is_elem {
                    // Baseline behavior (or: the element extension is exhausted).
                    self.log_cata_decision(
                        route_start,
                        route_budget,
                        false,
                        format!("route budget exhausted before level {level}"),
                        "timeout",
                    );
                    return None;
                }
                // Enhanced size level with the route budget gone: skip ahead to
                // the element levels, which draw on the extension.
                continue;
            }
            let level_budget = if is_elem {
                // Element level: equally divide the remaining (extended) budget
                // among the element levels still to run.
                let elem_left = ladder[level..]
                    .iter()
                    .filter(|p| is_elem_level(p))
                    .count()
                    .max(1);
                remaining / (elem_left as u32)
            } else {
                // Size level: EXACT baseline front-load schedule.
                remaining / ((levels - level) as u32).min(2)
            };
            let level_deadline = now + level_budget;

            match self.try_cata_level(
                level,
                pool,
                level_deadline,
                route_start,
                route_budget,
                enhanced,
                &mut bmc_no_cex_depth,
                element_free,
            ) {
                CataLevelOutcome::Solved(result, evidence) => return Some((result, evidence)),
                CataLevelOutcome::Refine => continue,
                CataLevelOutcome::Abort(reason) => {
                    self.log_cata_decision(route_start, route_budget, false, reason, "skipped");
                    return None;
                }
            }
        }

        self.log_cata_decision(
            route_start,
            route_budget,
            false,
            "catamorphism pool exhausted without a certified verdict".to_string(),
            "unknown",
        );
        None
    }

    fn try_cata_level(
        &self,
        level: usize,
        pool: &[crate::transform::cata_abstract::CataKind],
        level_deadline: Instant,
        route_start: Instant,
        route_budget: Duration,
        enhanced: bool,
        bmc_no_cex_depth: &mut Option<usize>,
        element_free: bool,
    ) -> CataLevelOutcome {
        // Element/ordering levels (a `Min`/`Max`/`Sorted` column) carry a
        // provably-disjunctive safety invariant: the conjunctive affine Houdini
        // cannot solve them and only burns its cap returning None, so in
        // ENHANCED mode it is SKIPPED there and the CATA v3 ICE learner runs
        // instead. Outside enhanced mode this flag is unused and the level
        // behaves exactly as the pre-v3 baseline (affine + nested, no ICE).
        let is_element = enhanced
            && pool.iter().any(|k| {
                matches!(
                    k,
                    crate::transform::cata_abstract::CataKind::Min
                        | crate::transform::cata_abstract::CataKind::Max
                        | crate::transform::cata_abstract::CataKind::Sorted
                )
            });
        // The disjunctive sortedness invariant lives at the level carrying the
        // ascending-`Sorted` fold; a `Min`/`Max`-only element level is provably
        // too coarse (its abstract query is reachable), so the ICE learner runs
        // ONLY at Sorted levels — running its least fixpoint on a Min/Max-only
        // level would only burn the extension budget returning None.
        let is_sorted_level = is_element
            && pool
                .iter()
                .any(|k| matches!(k, crate::transform::cata_abstract::CataKind::Sorted));
        // 1. Build the abstraction.
        let abstraction = match CataAbstraction::build(&self.problem, pool) {
            Ok(abstraction) => abstraction,
            Err(skip) => {
                return CataLevelOutcome::Abort(format!(
                    "abstraction not applicable at level {level}: {skip:?}"
                ));
            }
        };

        // Diagnostic: dump the abstract LIA problem for offline standalone
        // solving (--chc-cata-dump-abstract <dir>). Datatype-free, so it is a
        // plain LIA-CHC script.
        if let Some(dir) = ay_core::misc_cli_flags().chc_cata_dump_abstract.as_deref() {
            let dir = std::path::PathBuf::from(dir);
            let _ = std::fs::create_dir_all(&dir);
            let script = crate::transform::cata_abstract::dump_abstract_lia_problem(
                &abstraction.abstract_problem,
            );
            let _ = std::fs::write(dir.join(format!("abstract_L{level}.smt2")), script);
        }

        // 2. Per-original-clause implication obligation cap (fail-closed
        //    soundness gate; the transform is NOT trusted). The discharge
        //    itself is deferred into `certify_and_compose_abstract_model` —
        //    see the PERF note below.
        let obligations_total_cap = if is_element {
            CATA_ELEMENT_OBLIGATIONS_TOTAL_CAP
        } else {
            CATA_OBLIGATIONS_TOTAL_CAP
        };
        // PERF (PERF-3 residue, chc_dt_mutual_recursive): the per-clause
        // implication obligations are DEFERRED into
        // `certify_and_compose_abstract_model` — they are only needed to
        // certify a SAFE verdict, and eagerly discharging them here charged
        // every non-winning ladder level ~10-50 ms of fresh SMT solves before
        // any abstract model even existed. Soundness is unchanged: every Safe
        // still requires BOTH the discharged obligations and the re-verified
        // abstract model (fail-closed, same budgets); the Unsafe path never
        // relied on the obligations (its concrete BMC counterexample is
        // replayed on the ORIGINAL clauses by the finalize boundary).
        // 2.5 CATA v2: multi-predicate affine Houdini on the abstract LIA
        //     problem. These abstractions are multi-relation equality-invariant
        //     Horn systems that PDR/Spacer (and AY's own portfolio) do not
        //     converge on, but that Houdini over mined affine relations solves
        //     directly — the ChocoCatalia `Choco` ICE-learner analogue. The
        //     result is re-certified by the SAME gate as the nested path, so it
        //     is a candidate generator only (never a trusted verdict).
        if !cata_v2_disabled() && !is_element {
            let houdini_deadline = Instant::now()
                + CATA_AFFINE_HOUDINI_CAP
                    .min(level_deadline.saturating_duration_since(Instant::now()));
            // Depth-1 guarded families: derive per-column tags from the
            // abstraction's layout (default ON). An empty map ⇒ the affine
            // Houdini's pool is byte-identical to the pure-conjunctive path.
            let tags: ay_core::kani_compat::DetHashMap<
                crate::PredicateId,
                Vec<crate::transform::cata_abstract::ColumnTag>,
            > = if cata_guarded_enabled() {
                abstraction
                    .abstract_problem
                    .predicates()
                    .iter()
                    .map(|p| (p.id, abstraction.column_tags(p.id)))
                    .collect()
            } else {
                ay_core::kani_compat::DetHashMap::default()
            };
            if let Some(model) =
                crate::transform::cata_abstract::affine_houdini::solve_abstract_affine(
                    &abstraction.abstract_problem,
                    &tags,
                    houdini_deadline,
                )
            {
                if let Some((result, evidence)) = self.certify_and_compose_abstract_model(
                    &abstraction,
                    &model,
                    pool,
                    level,
                    level_deadline,
                    obligations_total_cap,
                    route_start,
                    route_budget,
                    "affine houdini (v2)",
                ) {
                    return CataLevelOutcome::Solved(result, evidence);
                }
            }
        }

        // 2.7 CATA v3 ICE lane: disjunctive (exact predicate-abstraction
        //     least-fixpoint) learner. The element/ordering abstractions
        //     (`Min` + `Sorted` columns — the sortedness fold) provably require
        //     a DISJUNCTIVE invariant that the conjunctive affine Houdini cannot
        //     express, so it returns None on them. This learner computes the
        //     strongest invariant expressible as a Boolean combination of a
        //     small tag-derived atom set (a disjunction of conjunctive minterms
        //     — a decision-tree region). Re-certified by the SAME fail-closed
        //     gate, so it is a candidate generator only. Kill switch:
        //     `AY_CHC_CATA_ICE=0`.
        //
        //     Restricted to the SORTED element level: that is where the
        //     disjunctive invariant lives, and its exact-post least fixpoint can
        //     be slow on the wide size-family abstractions (empirically ~11 s at
        //     a size level of bubble sort) or waste the extension on a too-coarse
        //     Min/Max-only level — so it runs only where it can win. Size levels
        //     keep affine Houdini (conjunctive, fast) as their solver.
        if cata_ice_enabled() && is_sorted_level {
            // Bounded by the per-level slice (the element extension guarantees
            // the Sorted level a generous slice) and by the hard ICE cap.
            let ice_deadline = Instant::now()
                + CATA_ICE_CAP.min(level_deadline.saturating_duration_since(Instant::now()));
            if ice_deadline.saturating_duration_since(Instant::now()) >= Duration::from_millis(500)
            {
                let ice_tags: ay_core::kani_compat::DetHashMap<
                    crate::PredicateId,
                    Vec<crate::transform::cata_abstract::ColumnTag>,
                > = abstraction
                    .abstract_problem
                    .predicates()
                    .iter()
                    .map(|p| (p.id, abstraction.column_tags(p.id)))
                    .collect();

                // Candidate generators for the sorted-level disjunctive invariant,
                // tried in order; the FIRST whose model re-certifies + composes
                // (`certify_and_compose_abstract_model`) wins. Each is a bounded
                // candidate generator — a non-composing candidate never shadows a
                // later one (we try the next), and a wrong candidate is rejected
                // by the fail-closed certify gate, so ordering is a completeness
                // choice only, never a soundness one.
                //
                //   1. DT-flagsOnly — the compact `FlagsOnly` vocabulary. It runs
                //      FIRST because the WIDE sortedness family (`BSortSorts` and
                //      relatives) drives DT-full + the DNF fixpoint into the
                //      ay-dpll `Unknown` / SMT-latency walls, which WASTE the whole
                //      sorted-level slice before the flag-only lane ever gets a
                //      turn. On the narrow family the flag-only lane fails fast
                //      (~0.5 s → None), so DT-full below still converts those with
                //      no regression. Sub-switch `AY_CHC_CATA_ICE_FLAGS=0`.
                //   2. DT-full — the generalizing Horn-ICE learner over the full
                //      vocabulary; converts the narrow family (`ISortSorts`,
                //      `nat_ISortSorts`). Sub-switch `AY_CHC_CATA_ICE_DT=0`.
                //   3. DNF — the exact-fixpoint least-fixpoint learner (still wins
                //      some levels the DT learners cannot).
                // Try each generator and IMMEDIATELY certify its model, returning
                // on the first that composes. Sequential-with-early-return (not
                // eager collection) so a successful earlier lane never pays for a
                // later lane's wasted budget — critical on the wide family, where
                // running DT-full after the flag-only lane already won would burn
                // ~20 s on the `Unknown` wall.
                let flags_deadline = || (Instant::now() + CATA_ICE_DT_CAP).min(ice_deadline);
                let try_certify =
                    |this: &Self, model: &crate::InvariantModel, label: &'static str| {
                        this.certify_and_compose_abstract_model(
                            &abstraction,
                            model,
                            pool,
                            level,
                            level_deadline,
                            obligations_total_cap,
                            route_start,
                            route_budget,
                            label,
                        )
                    };

                if cata_ice_dt_enabled() && cata_ice_flags_enabled() {
                    let dl = flags_deadline();
                    if dl.saturating_duration_since(Instant::now()) >= Duration::from_millis(500) {
                        if let Some(m) =
                            crate::transform::cata_abstract::ice_dt::solve_abstract_ice_dt_flags_only(
                                &abstraction.abstract_problem,
                                &ice_tags,
                                dl,
                            )
                        {
                            if let Some((result, evidence)) =
                                try_certify(self, &m, "disjunctive ice-dt flags (v3)")
                            {
                                return CataLevelOutcome::Solved(result, evidence);
                            }
                        }
                    }
                }

                if cata_ice_dt_enabled() {
                    let dl = flags_deadline();
                    if dl.saturating_duration_since(Instant::now()) >= Duration::from_millis(500) {
                        if let Some(m) =
                            crate::transform::cata_abstract::ice_dt::solve_abstract_ice_dt(
                                &abstraction.abstract_problem,
                                &ice_tags,
                                dl,
                            )
                        {
                            if let Some((result, evidence)) =
                                try_certify(self, &m, "disjunctive ice-dt (v3)")
                            {
                                return CataLevelOutcome::Solved(result, evidence);
                            }
                        }
                    }
                }

                if Instant::now() < ice_deadline {
                    if let Some(m) =
                        crate::transform::cata_abstract::disj_abstract::solve_abstract_disjunctive(
                            &abstraction.abstract_problem,
                            &ice_tags,
                            ice_deadline,
                        )
                    {
                        if let Some((result, evidence)) =
                            try_certify(self, &m, "disjunctive dnf-fixpoint (v3)")
                        {
                            return CataLevelOutcome::Solved(result, evidence);
                        }
                    }
                }
            }
        }

        // 2.8 CATA v3 DISJUNCTIVE lane for the ELEMENT-FREE (nat-peano /
        //     structural-ADT) class. These problems have NO Min/Max/Sorted level
        //     (their datatypes carry no Int payload — `element_free`), so the
        //     sorted-level ICE lane above never engaged, yet their safety
        //     invariant is provably DISJUNCTIVE / piecewise-linear over Peano
        //     sizes (minus-clamp, leq, min/max, even/odd laws) — which the
        //     conjunctive affine Houdini (step 2.5) cannot express and returns
        //     None on (MEASURED: isaplanner nat props ⇒ affine unknown, z3/spacer
        //     decides the SAME size abstract instantly ⇒ the abstraction is
        //     already precise). The disjunctive ICE-DT learner re-certifies a
        //     Boolean-combination invariant here exactly as at the sorted level.
        //     Two atom vocabularies, tried in order and each re-certified by the
        //     SAME fail-closed gate (candidate generators only, 0-wrong by
        //     construction — a spurious/too-weak invariant leaves the query
        //     reachable ⇒ certify fails ⇒ refine, never a false Safe):
        //       (a) `solve_abstract_ice_dt` (Full) — converts the
        //           difference/equality-law family (minus / leq via size diffs).
        //       (b) `solve_abstract_ice_dt_nat` (Full + size `<=` leq-splits) —
        //           converts the min/max/clamp family whose invariant splits on a
        //           size ordering the Full unit-difference atoms cannot express.
        //     Kill switch `AY_CHC_CATA_DISJ_NONSORT=0` ⇒ block skipped ⇒
        //     byte-identical to the pre-extension baseline. Gated on
        //     `element_free && !is_element` so sorted/size-int families are
        //     untouched, and reached only when affine (2.5) already failed, so
        //     the landed size-family conversions return before it and are
        //     provably unaffected.
        if cata_disj_nonsort_enabled() && element_free && !is_element && !is_sorted_level {
            let disj_deadline = Instant::now()
                + CATA_ICE_CAP.min(level_deadline.saturating_duration_since(Instant::now()));
            if disj_deadline.saturating_duration_since(Instant::now()) >= Duration::from_millis(500)
            {
                let ice_tags: ay_core::kani_compat::DetHashMap<
                    crate::PredicateId,
                    Vec<crate::transform::cata_abstract::ColumnTag>,
                > = abstraction
                    .abstract_problem
                    .predicates()
                    .iter()
                    .map(|p| (p.id, abstraction.column_tags(p.id)))
                    .collect();
                let try_certify =
                    |this: &Self, model: &crate::InvariantModel, label: &'static str| {
                        this.certify_and_compose_abstract_model(
                            &abstraction,
                            model,
                            pool,
                            level,
                            level_deadline,
                            obligations_total_cap,
                            route_start,
                            route_budget,
                            label,
                        )
                    };
                // (a) Full vocabulary.
                let dl = (Instant::now() + CATA_ICE_DT_CAP).min(disj_deadline);
                if dl.saturating_duration_since(Instant::now()) >= Duration::from_millis(500) {
                    if let Some(m) = crate::transform::cata_abstract::ice_dt::solve_abstract_ice_dt(
                        &abstraction.abstract_problem,
                        &ice_tags,
                        dl,
                    ) {
                        if let Some((result, evidence)) =
                            try_certify(self, &m, "disjunctive ice-dt nonsort (v3)")
                        {
                            return CataLevelOutcome::Solved(result, evidence);
                        }
                    }
                }
                // (b) NatSize vocabulary (adds size leq-splits).
                let dl = (Instant::now() + CATA_ICE_DT_CAP).min(disj_deadline);
                if dl.saturating_duration_since(Instant::now()) >= Duration::from_millis(500) {
                    if let Some(m) =
                        crate::transform::cata_abstract::ice_dt::solve_abstract_ice_dt_nat(
                            &abstraction.abstract_problem,
                            &ice_tags,
                            dl,
                        )
                    {
                        if let Some((result, evidence)) =
                            try_certify(self, &m, "disjunctive ice-dt nat-leq (v3)")
                        {
                            return CataLevelOutcome::Solved(result, evidence);
                        }
                    }
                }
            }
        }

        // 3. Solve the abstract LIA system with a NESTED adaptive portfolio.
        //    The abstract problem is datatype-free, so the nested solver can
        //    never re-enter this lane (no recursion), and its own finalize
        //    boundary fully verifies whatever verdict it returns against the
        //    ABSTRACT clauses.
        let solve_budget = {
            let raw = level_deadline.saturating_duration_since(Instant::now());
            // The per-level nested cap applies ONLY at element levels (the
            // nested portfolio provably times out on the element/ordering
            // abstractions, so capping it there frees the extension for the ICE
            // learner). Size levels keep their full baseline slice — so a
            // size-family Safe that the nested portfolio decides is unaffected.
            if is_element {
                raw.min(CATA_NESTED_SOLVE_CAP)
            } else {
                raw
            }
        };
        if solve_budget < Duration::from_millis(100) {
            return CataLevelOutcome::Refine;
        }
        debug_assert!(!abstraction.abstract_problem.has_datatype_sorts());
        let mut nested_config = AdaptiveConfig::with_budget(solve_budget, self.config.verbose);
        nested_config.strict_proofs = self.config.strict_proofs;
        let nested = AdaptivePortfolio::new(abstraction.abstract_problem.clone(), nested_config);
        let nested_result = nested.solve();

        match nested_result {
            crate::VerifiedChcResult::Safe(verified) => {
                let abstract_model = verified.into_inner();
                match self.certify_and_compose_abstract_model(
                    &abstraction,
                    &abstract_model,
                    pool,
                    level,
                    level_deadline,
                    obligations_total_cap,
                    route_start,
                    route_budget,
                    "nested portfolio",
                ) {
                    Some((result, evidence)) => CataLevelOutcome::Solved(result, evidence),
                    None => CataLevelOutcome::Refine,
                }
            }
            crate::VerifiedChcResult::Unsafe(verified_cex) => {
                // 4c. NEVER report the abstract counterexample. Concretize on
                //     the ORIGINAL clauses with depth-hinted bounded BMC; the
                //     finalize boundary replays whatever BMC finds.
                let abstract_cex = verified_cex.into_inner();
                let depth_hint = abstract_cex.steps.len() + CATA_CEX_DEPTH_SLACK;
                // PERF (PERF-3 residue): concretization BMC runs on the
                // ORIGINAL clauses and depends only on `depth_hint` — not on
                // the level's abstraction. When an earlier level already ran
                // this exact search to completion (all depths <= hint explored
                // well inside its budget, no counterexample), an identical
                // re-run is skipped: BMC is deterministic on (problem, depth),
                // so the re-run provably finds nothing either. A budget-
                // truncated earlier attempt does NOT populate the memo, so a
                // deeper/slower search is never masked.
                if bmc_no_cex_depth.is_some_and(|done| depth_hint <= done) {
                    return CataLevelOutcome::Refine;
                }
                let bmc_budget = level_deadline.saturating_duration_since(Instant::now());
                if bmc_budget < Duration::from_millis(100) {
                    return CataLevelOutcome::Refine;
                }
                // Child of the portfolio handle (item 5).
                let cancel = self.cancellation_token.child();
                let bmc_config = BmcConfig {
                    base: ChcEngineConfig {
                        verbose: self.config.verbose,
                        cancellation_token: Some(cancel.clone()),
                    },
                    max_depth: depth_hint,
                    per_depth_timeout: Some(bmc_budget),
                    time_budget: Some(bmc_budget),
                    ..BmcConfig::default()
                };
                let _timeout_guard = cancel.cancel_after(bmc_budget);
                let _smt_deadline_guard = crate::smt::ScopedSmtDeadline::install(bmc_budget);
                let bmc_start = Instant::now();
                let bmc_result = BmcSolver::new(self.problem.clone(), bmc_config).solve();
                if !matches!(bmc_result, PortfolioResult::Unsafe(_))
                    && bmc_start.elapsed() < bmc_budget / 2
                {
                    // Completed (not budget-truncated) search with no cex:
                    // remember the depth so later levels skip the re-run.
                    *bmc_no_cex_depth =
                        Some(bmc_no_cex_depth.map_or(depth_hint, |d| d.max(depth_hint)));
                }
                if let PortfolioResult::Unsafe(concrete_cex) = bmc_result {
                    self.log_cata_decision(
                        route_start,
                        route_budget,
                        true,
                        format!(
                            "level {level}: abstract cex at depth {} concretized \
                             on original clauses by BMC (depth hint {depth_hint})",
                            abstract_cex.steps.len(),
                        ),
                        "unsafe",
                    );
                    // BmcCounterexample evidence: the finalize boundary
                    // independently replays this trace before exposing Unsafe.
                    return CataLevelOutcome::Solved(
                        PortfolioResult::Unsafe(concrete_cex),
                        ValidationEvidence::BmcCounterexample,
                    );
                }
                // Spurious (or unconfirmed) abstract counterexample: refine.
                CataLevelOutcome::Refine
            }
            crate::VerifiedChcResult::Unknown(_) => CataLevelOutcome::Refine,
        }
    }

    /// Certify an abstract model against every abstract clause, discharge the
    /// per-original-clause implication obligations, then compose the model
    /// with the reserved catamorphism symbols into an original-vocabulary
    /// model. Shared by the affine-Houdini (v2), ICE (v3) and
    /// nested-portfolio (v1) abstract-solve paths. Returns `None` (caller
    /// refines) on any failure — the certification is fail-closed.
    #[allow(clippy::too_many_arguments)]
    fn certify_and_compose_abstract_model(
        &self,
        abstraction: &CataAbstraction,
        abstract_model: &crate::InvariantModel,
        pool: &[crate::transform::cata_abstract::CataKind],
        level: usize,
        level_deadline: Instant,
        obligations_total_cap: Duration,
        route_start: Instant,
        route_budget: Duration,
        source: &str,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        // Fresh full re-verification of the abstract model against EVERY
        // abstract clause (init + transition + query). This is the soundness
        // gate: it does not trust the abstract solver (Houdini or nested).
        let verify_budget = CATA_ABSTRACT_VERIFY_CAP
            .min(level_deadline.saturating_duration_since(Instant::now()))
            .max(Duration::from_millis(500));
        let verify_config = PdrConfig {
            verbose: self.config.verbose,
            strict_proofs: true,
            solve_timeout: Some(verify_budget),
            ..PdrConfig::default()
        };
        let abstract_model_certified = matches!(
            crate::engines::validate_external_invariant_model(
                &abstraction.abstract_problem,
                abstract_model,
                &verify_config,
            ),
            Ok(true)
        );
        if !abstract_model_certified {
            tracing::debug!(
                level,
                source,
                "cata: abstract model did NOT re-certify on abstract clauses"
            );
            return None;
        }
        tracing::debug!(level, source, "cata: abstract model re-certified");

        // Discharge the per-original-clause implication obligations
        // (fail-closed soundness gate; the transform is NOT trusted). Deferred
        // here from the level entry (PERF-3 residue): a candidate abstract
        // model now exists, so this work is spent only on levels that can
        // actually produce a Safe verdict — same budgets, same fail-closed
        // polarity as the eager placement.
        let obligations_deadline = Instant::now()
            + obligations_total_cap.min(level_deadline.saturating_duration_since(Instant::now()));
        if !abstraction.discharge_obligations(
            CATA_PER_OBLIGATION_BUDGET,
            Some(obligations_deadline.min(level_deadline)),
        ) {
            tracing::debug!(
                level,
                pool = pool.len(),
                "cata: implication obligations not discharged; rejecting candidate (fail-closed)"
            );
            return None;
        }

        // Compose the certified abstract model with the reserved catamorphism
        // symbols into an original-vocabulary model.
        let composed = abstraction.compose_model(abstract_model)?;
        let obligations_discharged = abstraction.obligations.len();
        self.log_cata_decision(
            route_start,
            route_budget,
            true,
            format!(
                "level {level} [{source}]: {} catas, {} obligations discharged, \
                 {} conjuncts weakened; abstract model fully verified",
                pool.len(),
                obligations_discharged,
                abstraction.dropped_conjuncts,
            ),
            "safe",
        );
        Some((
            PortfolioResult::Safe(composed),
            ValidationEvidence::CataAbstraction {
                pool_size: pool.len(),
                obligations_discharged,
            },
        ))
    }

    fn log_cata_decision(
        &self,
        route_start: Instant,
        route_budget: Duration,
        gate_result: bool,
        gate_reason: String,
        result: &'static str,
    ) {
        self.decision_log.log_decision(DecisionEntry {
            stage: "cata_abstraction",
            gate_result,
            gate_reason,
            budget_secs: route_budget.as_secs_f64(),
            elapsed_secs: route_start.elapsed().as_secs_f64(),
            result,
            lemmas_learned: 0,
            max_frame: 0,
        });
    }
}

enum CataLevelOutcome {
    Solved(PortfolioResult, ValidationEvidence),
    Refine,
    Abort(String),
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "adaptive_cata_tests.rs"]
mod tests;
