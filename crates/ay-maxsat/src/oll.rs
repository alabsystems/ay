// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! OLL core-guided MaxSAT engine.
//!
//! Implements the OLL algorithm (Andres et al. 2012; Morgado et al. 2014) in
//! the style of RC2 (Ignatiev et al. 2019), the algorithm family behind the
//! top exact solvers of recent MaxSAT Evaluations (RC2, EvalMaxSAT,
//! CASHWMaxSAT, UWrMaxSat):
//!
//! 1. Every soft clause gets a selector literal that is assumed true
//!    (= clause satisfied) in each SAT call on one persistent incremental
//!    SAT solver.
//! 2. Each UNSAT core over the selectors raises the lower bound by the
//!    minimum weight in the core, splits the weights of core members
//!    (weight-aware cores), and introduces a totalizer counting the core's
//!    violated selectors. The totalizer's "at least 2 violated" output
//!    becomes a new selector, extended lazily one bound at a time when it
//!    reappears in later cores (incremental totalizer, Martins et al. 2014).
//! 3. Weighted instances are stratified (#climit-discipline, in the style of
//!    CGSS2's climit / BLO stratification): the engine keeps a current
//!    `level` and assumes ONLY selectors — original and sum selectors alike —
//!    whose residual weight is >= level, so every core found at a level pays
//!    at least `level` into the lower bound. The next level is recomputed
//!    from the live residual-weight histogram at every satisfiable point
//!    with nothing suspended (adaptive stratification + BLO rules), and the
//!    run is terminal only at level 1, where nothing is filtered.
//! 4. Soft clauses whose residual weight cannot be paid within the current
//!    upper bound are hardened into unit clauses (Ansótegui et al. 2013).
//! 5. Core relaxation is deferred (#wce, weight-aware core extraction in the
//!    style of CGSS2's `cores_to_relax`): a multi-member core pays its lb
//!    contribution and splits weights immediately, but its totalizer is only
//!    built at a flush point — the Sat arm, an empty filtered assumption
//!    set, or right before an LP-boost round / descent commit — so one
//!    extraction phase mines many disjoint cores against an unchanged
//!    encoding (see flush_pending for the flush-point catalogue).
//!
//! The engine is anytime: every satisfiable intermediate model updates the
//! incumbent, and interruption returns the best model found so far.

use std::collections::{HashMap, HashSet};
use std::time::{Duration, Instant};

use ay_sat::{AssumeResult, Literal, Solver as SatSolver, Variable};

use crate::dpw::{dpw_size, gte_size, DpwEnc};
use crate::solver::MaxSatStats;

/// Diagnostics gate: pass `--maxsat-debug` to trace engine decisions on
/// stderr. Zero cost when unset. B41: CLI-owned via misc_cli_flags, same
/// OnceLock pattern as the other engine knobs below — the previous literal
/// env::var_os read of the flag name was dead (nothing sets an env var
/// named "--maxsat-debug").
fn debug_trace() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| ay_core::misc_cli_flags().maxsat_debug)
}

/// Weight type for soft clauses.
pub(crate) type Weight = u64;

/// Compact clause storage: one flat literal buffer plus offsets (CSR).
/// Avoids per-clause `Vec` headers and allocator overhead, which dominate
/// memory on instances with tens of millions of clauses.
pub(crate) struct ClauseStore {
    lits: Vec<Literal>,
    /// `offsets[i]..offsets[i + 1]` bounds clause `i`; always starts with 0.
    offsets: Vec<usize>,
}

impl ClauseStore {
    pub(crate) fn new() -> Self {
        ClauseStore {
            lits: Vec::new(),
            offsets: vec![0],
        }
    }

    pub(crate) fn push_from_iter(&mut self, lits: impl Iterator<Item = Literal>) {
        self.lits.extend(lits);
        self.offsets.push(self.lits.len());
    }

    pub(crate) fn len(&self) -> usize {
        self.offsets.len() - 1
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub(crate) fn get(&self, i: usize) -> &[Literal] {
        &self.lits[self.offsets[i]..self.offsets[i + 1]]
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = &[Literal]> {
        (0..self.len()).map(move |i| self.get(i))
    }
}

impl Default for ClauseStore {
    fn default() -> Self {
        Self::new()
    }
}

/// Outcome of an OLL run.
#[derive(Debug, Clone)]
pub(crate) enum OllOutcome {
    /// Proven optimal model with its cost.
    Optimal { model: Vec<bool>, cost: Weight },
    /// Hard clauses are unsatisfiable.
    Unsatisfiable,
    /// Interrupted; carries the best (cost, model) found so far, if any.
    Unknown { best: Option<(Weight, Vec<bool>)> },
}

// ----- UP-probe AM1 pass (#maxsat-am1-probe) tuning constants --------------
// At each post-solve stratification level change, UP-probe the level-qualified
// active ORIGINAL selectors to mine at-most-one structure that install-time
// adapt_am1 (direct binary edges only) cannot see — selectors conflicting only
// through unit-propagation chains (CSG: 0.008% direct edges but rich UP
// structure). Reimplements CGSS2's calc_conns/try_am1s (cgss2.cpp:1134-1402)
// natively over ay-sat's propagate-only probe (probe_implications_false).

/// Fraction of total elapsed solve time the AM1 probe passes may consume.
const AM1_PROBE_TIME_SHARE: f64 = 0.07;
/// Skip the pass when the level-qualified active original set exceeds this:
/// the O(n) probes plus greedy clique cover would dominate the level phase.
const AM1_PROBE_MAX_ACTIVE: usize = 2000;
/// Reiteration cap for the OVERLAPPING weighted clique cover (#am1-overlap,
/// CGSS2 try_am1s port). Each pass peels one min-weight layer per am1 and
/// reuses selectors across cliques until their residual weight is spent; the
/// scan reiterates over the surviving residuals. CGSS2 converges in ~6 passes
/// on the auctions family (148 am1s, avg size 33, paying 99.8% of the optimum
/// lb up front); the cap only guards a pathological dense graph from spinning
/// — hitting it merely leaves some lb to the ordinary core loop, never wrong.
const AM1_PROBE_MAX_ITERS: u32 = 64;
/// Distinct-soft-weight count at/above which the overlapping weighted clique
/// cover replaces the disjoint one (#am1-overlap gate; see `am1_overlap`).
/// #core-mine: cap the arity of a mined core. A hard clause that forbids k
/// unit softs from all holding is a core of size k; very wide ones are weak
/// (they pay one `w_min` regardless of k) and cost more to carry.
const CORE_MINE_MAX_ARITY: usize = 8;
/// #core-mine: cap on collected cores, so the scan is O(hards) with bounded
/// memory on formulas where nearly every clause qualifies.
const CORE_MINE_MAX_CORES: usize = 200_000;
const AM1_OVERLAP_MIN_DISTINCT_WEIGHTS: usize = 20;

/// #am1-maxcover kill switch (env A/B). DEFAULT ON: for the overlapping AM1
/// clique cover (`adapt_am1`, gated on the >= 20-distinct-weight family) score
/// BOTH candidate growth orderings — the landed shared-neighbour reorder and
/// CGSS2's ascending-degree order (try_am1s am1s_order=1) — and keep the plan
/// with the higher lower bound. A higher clique-cover lb is a strictly better
/// VALID bound (both plans are the same sound per-layer peel over the same
/// direct-conflict graph, only the clique partition differs), so this can only
/// raise install lb, never lower it. Motivation: the shared-neighbour order
/// fragments the dense mutual-conflict cliques of combinatorial auctions (whose
/// hard clauses are all binary, so the whole conflict graph is direct edges and
/// a UP probe adds nothing) — on auctions_wt-cat_reg_60_150_0004 it pays install
/// lb 112419 where the ascending-degree order pays 113275 (99.8% of the 113503
/// optimum, matching cgss). The shared order still WINS elsewhere
/// (cat_paths_60_150_0004: +171), so neither dominates and max-of-both is the
/// safe choice. `--maxsat-no-am1-maxcover` restores the shared-only landed
/// cover bit-identically; low-weight/unweighted is untouched (overlap gate).
fn am1_maxcover_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| !ay_core::misc_cli_flags().maxsat_no_am1_maxcover)
}

/// #tot-eqs budget constants — CGSS2's `add_eq_max_decs` / `add_eq_max_cost` /
/// `add_eq_max_prod` defaults (ss_encoder.h:200-202). They bound the recursion
/// that adds totalizer REVERSE-direction clauses: `DECS` caps how many inputs
/// would have to be shown false elsewhere before a subtree learns anything,
/// `COST` caps the equivalences other subtrees must pay for that information,
/// and `PROD` caps their product. Together they keep the encoding from growing
/// faster than the propagation it buys (AY has measured the opposite extreme:
/// a blanket-strong encoding — GTE — blew clause counts up 250x and lost).
const TOT_EQ_MAX_DECS: i64 = 50;
const TOT_EQ_MAX_COST: i64 = 50;
const TOT_EQ_MAX_PROD: i64 = 2500;

/// #tot-eqs recursion budget, resolved once per process. CGSS2's defaults were
/// tuned against SHARED totalizer nodes (its encoder reuses subtrees across
/// cores, so one equivalence can pay off in several cardinality constraints);
/// AY's trees are per-core, so the productive budget may differ and each bound
/// is env-overridable for A/B without a rebuild.
#[derive(Clone, Copy)]
struct TotEqCfg {
    max_decs: i64,
    max_cost: i64,
    max_prod: i64,
}

fn tot_eq_cfg() -> TotEqCfg {
    use std::sync::OnceLock;
    static CFG: OnceLock<TotEqCfg> = OnceLock::new();
    *CFG.get_or_init(|| {
        let get = |key: &str, default: i64| {
            std::env::var(key)
                .ok()
                .and_then(|v| v.parse::<i64>().ok())
                .filter(|&v| v >= 0)
                .unwrap_or(default)
        };
        TotEqCfg {
            max_decs: get("AY_AB_MAXSAT_TOT_EQ_DECS", TOT_EQ_MAX_DECS),
            max_cost: get("AY_AB_MAXSAT_TOT_EQ_COST", TOT_EQ_MAX_COST),
            max_prod: get("AY_AB_MAXSAT_TOT_EQ_PROD", TOT_EQ_MAX_PROD),
        }
    })
}

/// #tot-eqs per-instance ceiling on emitted reverse-direction clauses,
/// as a multiple of the hard-clause count. Backstop only: the CGSS2 cost model
/// above is what normally bounds emission. Prevents a pathological
/// many-cores instance from trading its whole BCP budget for encoding
/// strength, which is the failure mode that killed the GTE encoder.
const TOT_EQ_CLAUSE_BUDGET_FACTOR: i64 = 2;
const TOT_EQ_CLAUSE_BUDGET_FLOOR: i64 = 200_000;

/// #tot-eqs master gate (env A/B). When ON, every totalizer output that OLL has
/// PROVEN true — the `sum >= 1` of a freshly relaxed core, and every bound a
/// unit core hardens — gets CGSS2's budgeted reverse-direction clauses so the
/// proven bound can actually propagate (CGSS2 calls `forced_true` at exactly
/// these two points: cgss2.cpp:714 after building a core's totalizer, and
/// cgss2.cpp:621 in exhaust_totalizer after asserting the output unit).
///
/// Motivation: AY already asserts those units (process_core's unit-core branch)
/// but its totalizers are input->output ONLY (see `TotNode`), so a TRUE output
/// satisfies every clause it appears in and propagates NOTHING downward — the
/// engine must re-derive an already-proven bound by search on every later
/// conflict. That is the shape of AY's measured weakness: 64K-134K conflicts
/// per unit of lower bound on the deep lb-proving UNSAT calls, where cgss
/// proves the same optima in ~7x fewer conflicts.
fn tot_eqs_enabled() -> bool {
    // B17: CLI-populated global (--maxsat-no-tot-eqs) replaced the never-set
    // env var; default on.
    !ay_core::misc_cli_flags().maxsat_no_tot_eqs
}

/// #core-clause gate (env A/B). Adds the extracted core's own disjunction
/// `(∨ members' violation indicators)` to the hard formula when the core is
/// relaxed.
///
/// Sound and non-restricting: an UNSAT core means the hard clauses ENTAIL that
/// disjunction, so adding it removes no model and cannot change the optimum.
///
/// Why it may pay where the full `#tot-eqs` machinery does not: the reverse
/// clauses' first-order benefit on a SMALL core is exactly this disjunction
/// (for a 2-member core `#tot-eqs` emits three clauses plus a unit just to make
/// it derivable), and the CDCL engine's own copy — learned during core
/// extraction — is subject to `reduce_db` deletion, whereas this one is
/// permanent. One clause per core instead of a budgeted subtree walk.
fn core_clause_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| ay_core::misc_cli_flags().ab_maxsat_core_clause)
}

/// Active-soft cap for the EAGER initial probe (#maxsat-am1-probe eager init).
/// The failed sweep itself is uncapped (only the hit-rate abort bounds it), so
/// on million-scale active sets even its 200-probe SAMPLE — each a decide+BCP
/// over millions of clauses — costs ~19s and pushes the solve past the wall
/// (SeanSafarpour-wb_conmax3: 1.22M active, 41s→60s timeout). titanic (260) and
/// des-cnf (4920) are cheap and benefit. Well above the measured gains, far
/// below the pathology; larger instances keep their prior behavior (no eager
/// probe), so this can only avoid regressions, never add one.
const EAGER_PROBE_MAX_ACTIVE: usize = 50_000;

/// Hard-clause count at/above which the one-shot MaxSAT preprocessor
/// (#maxsat-oneshot-preproc) activates. Full-track A/B (mse24 weighted, 60s):
/// at a 500k gate the fired subset went +4/-1 (the one loss, metro at 875k
/// hards, sits in the 500k-1M band where the BVE pass cost doesn't pay);
/// at a 1M gate it went **+3/-0** (CSG150-150-55 1.65M, polysite-avrora
/// 9.9M, polysite-lusearch) with zero regressions. Gate at 1M. The
/// UWr/MaxPre headline target (rna-alignment, ~1.36M hards, 73% hard-only
/// vars) remains inside this band.
const ONESHOT_PREPROC_MIN_HARDS: usize = 1_000_000;

/// Clause-count divisor for the incremental inprocessing re-fire interval
/// (#maxsat-inproc-throttle). The SAT engine sets the between-solve
/// inprocessing interval to `clamp(500, num_clauses / N, 20_000)` conflicts.
/// N=100 means inprocessing re-fires once per ~1% growth in clause count,
/// keeping its O(arena) subsumption/vivification scans a bounded fraction of
/// runtime on the larger MaxSAT families while still simplifying often enough
/// to bound clause bloat. Value chosen by full-track A/B on mse24 weighted
/// (N=100 → 281→296 solved, cleaner than the more aggressive N=50 which broke
/// fast instances). See `Solver::set_incremental_inprobe_divisor`.
const MAXSAT_INCR_INPROBE_DIVISOR: u64 = 100;

/// Kill switch for BMO layer promotion (#maxsat-bmo-promote). DEFAULT ON
/// since the net-positive full-track leg (weighted 304 -> 321, +21/-4, zero
/// wrong: drmx x11, abstraction, frb, CSG, auctions, css, haplotyping,
/// quantum, spot5): `--maxsat-no-bmo` disables. Uniform-weight
/// (unweighted-track) instances are structurally unaffected — the boundary
/// rule requires a non-empty strictly-lower mass, which a single distinct
/// weight never has.
fn maxsat_bmo_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| !ay_core::misc_cli_flags().maxsat_no_bmo)
}

/// Conflict budget for one BMO joint-satisfiability check
/// (#maxsat-bmo-promote). Exhaustion = no promotion (fail-open, sound).
const BMO_CHECK_CONFLICTS: u64 = 200_000;
/// Wall-clock cap for one BMO check.
const BMO_CHECK_WALL: Duration = Duration::from_secs(8);

/// Mean per-core wall-clock (ms) above which OLL cores count as "expensive"
/// for the early descent kick (#expensive-core-descent). Chosen an order of
/// magnitude above the `lsu_stall_ms_per_core` cheap-core threshold (30ms) so
/// only genuinely SAT-call-bound instances (big hard formulas) qualify.
const EXPENSIVE_CORE_MS: u64 = 250;
/// Skip the BMO throwaway check entirely above this many clauses
/// (hards + candidate softs) — the throwaway build would cost more than the
/// promotion is worth.
const BMO_MAX_CHECK_CLAUSES: usize = 2_000_000;

/// Kill switch for the one-shot MaxSAT preprocessor. DEFAULT ON since the
/// net-positive full-track leg (fired subset +3/-0 at the 1M-hards gate, zero
/// wrong): `--maxsat-no-preproc` disables. Matches the ay-sat `AY_AB_*`
/// convention's kill-switch form.
/// Opt-in gate for the BCE-first one-shot config (#maxsat-bce-preprocess).
/// When --maxsat-bce the one-shot fires from this lower hard-clause
/// threshold (so the LP-extracted mid-size families qualify) AND arms BCE.
const BCE_ONESHOT_MIN_HARDS: usize = 100_000;

/// #bce-risky-revert kill switch (env A/B). DEFAULT ON.
///
/// The one-shot pass's BCE has two arms (`ay_sat::bce`). The PURE arm deletes a
/// clause whose blocking literal's negation occurs nowhere — it could never
/// have propagated onto it, so the deletion is FREE. The tautological-resolvent
/// arm deletes a LIVE implication. On metro the reduction is ~99% pure (54% of
/// the formula, genuinely free) and one-shot mode is a large win. On
/// `quantum-circuit-qgan_6_15` it is **0% pure**: every pure literal there
/// belongs to a FROZEN soft variable, which BCE skips as a blocking candidate,
/// so all ~11.8k deletions come from the risky arm and are live `(¬a ∨ ¬b)`
/// MUTEX edges — precisely the binary conflict graph that `adapt_am1` /
/// `run_am1_probe` mine for the AM1 clique-cover lower bound. The preprocessor
/// eats the solver's own lower bound: qgan goes from a 6.7s optimum (pass off)
/// to a 60s timeout stuck at cost 33 against a true optimum of 24.
///
/// So when the reduction is mostly RISKY, discard the preprocessed engine and
/// rebuild from the untouched hard clauses — landing the instance on exactly
/// the measured-good no-preprocessing trajectory. Raising the reduction bar
/// instead does NOT work (measured: the edges are already gone by then).
///
/// With BCE unarmed (`--maxsat-bce` unset) the risky count is 0, so the
/// predicate collapses to the legacy rule and the default lane is unchanged.
fn bce_risky_revert_enabled() -> bool {
    // B17: CLI-populated global (--maxsat-no-bce-revert) replaced the
    // never-set env var; default on.
    !ay_core::misc_cli_flags().maxsat_no_bce_revert
}

/// #bce-risky-revert: install exactly the size-banded SAT configuration the
/// NON-one-shot path installs, so a reverted instance runs on the measured-good
/// no-preprocessing trajectory rather than on a third, unmeasured one. Mirrors
/// the `else` arm of the one-shot branch; that arm is left textually untouched
/// so this cannot perturb it.
fn install_non_oneshot_sat_config(sat: &mut SatSolver, n_hard: usize) {
    if n_hard > 2_000_000 {
        sat.set_preprocess_enabled(false);
    }
    if let Some(profile) = non_oneshot_inprocessing_profile(n_hard) {
        sat.set_inprocessing_profile(&profile);
    }
}

/// #oneshot-dry-guard-band: the single source of truth for the size-banded
/// inprocessing profile the NON-one-shot path runs on.
///
/// `None` means **install no profile at all**. That is what the non-one-shot
/// path does at or below 500k hards, and it is NOT equivalent to installing
/// `InprocessingFeatureProfile::default()` — that would also re-arm
/// `preprocess` (`default().preprocess == true`).
///
/// This function exists because the one-shot dry-guard used to carry its own
/// hand-copied duplicate of these bands. The copy asserted `hard.len() >= 1M`,
/// an invariant that held while `ONESHOT_PREPROC_MIN_HARDS` (1M) was the only
/// gate and was broken the same day by `BCE_ONESHOT_MIN_HARDS` (100k), which
/// `--maxsat-bce` lowers the gate to. A 242,578-hard instance then ran
/// its whole solve on a profile meant for a formula 4x larger — every
/// inprocessing technique disabled where the correct path leaves them on. On
/// `tcp_wt-tcp_students_112_it_5` that cost a ~5,000x conflict blow-up
/// (5.7e3 -> 3.2e7) and produced WRONG ANSWERS: `o 3441`, `o 3477` and
/// `o 3549` across runs, against a true optimum of 3366. Both callers now
/// share this function so the two mirrors cannot drift apart again.
///
/// NOTE: this removes the *enabler*. The underlying unsoundness — a wrong
/// UNSAT out of `ay-sat` after ~3e7 conflicts, surfacing either as an empty
/// core or as an over-paid lb ladder — is nondeterministic and still open.
fn non_oneshot_inprocessing_profile(n_hard: usize) -> Option<ay_sat::InprocessingFeatureProfile> {
    if n_hard <= 500_000 {
        return None;
    }
    let mut profile = ay_sat::InprocessingFeatureProfile::default();
    profile.vivify = false;
    profile.subsume = false;
    profile.probe = false;
    profile.transred = false;
    profile.sweep = false;
    profile.congruence = false;
    if n_hard > 2_000_000 {
        profile.bve = false;
        profile.bce = false;
        profile.sbva = false;
        profile.htr = false;
        profile.gate = false;
        profile.factor = false;
        profile.decompose = false;
        profile.hbr = false;
        profile.condition = false;
        profile.backbone = false;
        profile.symmetry = false;
        profile.cce = false;
    }
    Some(profile)
}

/// Opt-in switch for BCE-first one-shot preprocessing
/// (#maxsat-bce-preprocess): `--maxsat-bce`. DEFAULT OFF — net-negative
/// under bench jobs=10 contention, net-positive at the jobs=1 competition
/// protocol (metro x4 etc.). Use for competition submissions.
fn maxsat_bce_preproc_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| ay_core::misc_cli_flags().maxsat_bce)
}

fn maxsat_oneshot_preproc_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| !ay_core::misc_cli_flags().maxsat_no_preproc)
}

/// Kill switch for RATE-AWARE descent entry (#cold-core-descent). DEFAULT ON:
/// `--maxsat-no-cold-descent` restores the pre-2026-08-02 gate, so the lever
/// can be measured as a paired A/B — with an A/A control — from ONE binary, the
/// way `--maxsat-no-early-descent` and `--maxsat-no-descent-residual` are.
///
/// THE DEFECT. The organic descent gate's core conjunct is
/// `cores_found >= lsu_min_cores` (64), a FLAT COUNT that is blind to how fast
/// cores arrive. Where the count is never reached the wait is the whole run:
/// af-synthesis ends at ~17 cores, and AY is 0/15 there while the upper-bound
/// solvers are 15/15.
///
/// ⚠️ THE MOTIVATING TRACE DID NOT REPRODUCE, AND THE HONEST READING MATTERS.
/// An earlier probe of `causal-discovery_wt-causal_n6_i2_N500_uai13_log_int` at
/// 900s reported 641 of 806 seconds spent reaching core #64 at one core per
/// 20-40s, with the descent then closing the instance in 164s — i.e. 80% of the
/// run spent waiting on a counter. Re-measured here, twice, on the same box and
/// the same 900s budget: core #64 lands at t=408.3s (lever off) and t=473.2s
/// (lever on), the walk is still paying `w_min` 8.17e6 of lb per core the whole
/// way, and the instance closes at 491.0s / 561.6s with the correct optimum.
/// The rate arm fires in NEITHER leg, and it should not: nothing had gone cold.
/// So this lever is NOT justified by causal-discovery. Its case rests on the
/// families where the count arm is structurally unreachable.
///
/// THE SIGNAL. Core discovery on these families does not decay gently, it
/// COLLAPSES (CSG: 111 cores in 38.7s then zero; css-ebay: 465 in 40.7s then
/// zero), so "no core for a long time BY THIS INSTANCE'S OWN STANDARDS" is a
/// sharp, cheap statement — see [`OllEngine::core_discovery_cold`]. It is
/// measured against the instance's own RECENT inter-core intervals because the
/// corpus spans 3 to 1,035,351 hard clauses and no absolute interval could mean
/// the same thing at both ends.
///
/// SOUNDNESS. Structurally nil risk: this changes only WHEN `ensure_descent_enc`
/// is called, never WHAT it builds. Every descent encoding is sound on its own
/// terms (a violated soft implies its indicator, and any model extends to exact
/// indicator values), and the descent's UNSAT branch is a complete optimality
/// proof of the incumbent. An earlier entry can cost TIME, but it cannot make an
/// answer wrong. The cost is bounded as well as sound: a cold entry takes a
/// REVERSIBLE slice (see [`descent_slice_len`]), so a misfire costs one slice
/// rather than the rest of the budget.
fn cold_core_descent_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| !ay_core::misc_cli_flags().maxsat_no_cold_descent)
}

/// #cold-core-descent: how many of the MOST RECENT search-derived inter-core
/// intervals form the rate baseline.
///
/// TRAILING, not "the first N" — which is what shipped first and what the
/// measurement killed. A first-N baseline samples the OPENING BURST, and on
/// this corpus the opening cores fall out of propagation-level conflicts in
/// milliseconds on nearly every family, so `COLD_CORE_DROUGHT_MULT * median`
/// collapses to a few hundred ms and [`COLD_CORE_MIN_DROUGHT`] becomes the
/// entire bar. Measured over every core of every traced run, the relative term
/// bound on ONE trace out of 63, and there by 2.5% (`bar_ms=30756` against the
/// 30000ms floor). A term documented as adaptive that is measurably a constant
/// is worse than a constant, because the comment stops people re-deriving it.
///
/// MEASURED, both statistics against the same real gap streams
/// (`--maxsat-debug`, this box):
///
///   causal-discovery_wt-causal_n6_i2_N500_uai13_log_int @240s — 53 intervals,
///   ramping 20ms -> 21.3s (last sixteen: 13.5 8.6 9.1 3.8 10.1 9.2 21.3 8.1
///   15.2 13.8 11.5 11.9 8.0s):
///     first-N median   1303ms -> bar   30000ms  (the FLOOR; term inert)
///     trailing median  9607ms -> bar  115284ms  (the term BINDS, 3.8x)
///   With the flat 30s bar this walk reads as COLD after ~1.4 of its own
///   typical gaps — the premature commit the slow-walk families cannot afford.
///
///   af-synthesis_wt-af-synthesis_stb_50_160_9 @120s — 16 intervals, all
///   sub-7s: BOTH statistics give bar 30000ms. The family the lever measured
///   its win on is unmoved by the statistic change, which is the point.
///
/// A trailing window CANNOT cancel itself on a decelerating walk, which is the
/// failure the first-N cap was defending against: a drought contributes NO
/// interval until a core actually ARRIVES, so the baseline freezes the instant
/// discovery stops and the drought grows past it. What the trailing window adds
/// is that the slowdown must beat the instance's RECENT trend rather than its
/// opening burst — i.e. it is a rate-of-DECELERATION test, which a flat floor
/// is not. On a geometric slowdown with ratio r the arm needs the current
/// drought to exceed `COLD_CORE_DROUGHT_MULT / r^(WINDOW/2)` times the last
/// observed gap; at r = 1.4 that is ~3x beyond trend, not "slightly slower".
const COLD_CORE_WINDOW: usize = 16;

/// #cold-core-descent: intervals required before the rate is meaningful, so the
/// gate cannot fire on the first few cores (an instance whose 2nd core is slow
/// says nothing about its rate). Set below the ~16 intervals the af-synthesis
/// runs produce, since those are a target of this lever.
const COLD_CORE_MIN_SAMPLE: usize = 8;

/// #cold-core-descent: multiple of the instance's own median inter-core
/// interval that a drought must reach to count as cold.
const COLD_CORE_DROUGHT_MULT: u64 = 12;

/// #cold-core-descent: absolute floor under the relative bar. It is the binding
/// term on the FAST families and only there: on an instance whose recent cores
/// are milliseconds apart, `COLD_CORE_DROUGHT_MULT` times the trailing median
/// is milliseconds too, and a sub-second lull is noise rather than a collapse.
/// Once the trailing median passes 2.5s — the slow-walk families this lever
/// must not disturb — the RELATIVE term takes over and this floor is inert.
/// That division of labour is asserted in
/// `cold_core_gate_measures_the_drought_against_the_instances_own_rate`.
///
/// SET FROM MEASURED TRAJECTORIES, not from taste, and expressed in the
/// engine's own unit: ONE ORGANIC DESCENT SLICE. The gate is about to spend at
/// least that much on a descent, so "we have gone longer than that without a
/// core" is the natural bar for calling the walk over.
///
/// Traced on causal n6 at 900s (`--maxsat-debug`, this box), inter-core gaps
/// in seconds:
///
///   cores #21-32 (t=9..18):    0.08 0.24 0.74 0.08 0.08 0.14 1.30 1.64 ...
///   cores #33-40 (t=25..65):   6.96 2.83 6.03 2.57 3.38 15.15 3.53 6.13
///   cores #41-54 (t=70..220):  5.24 8.64 3.70 9.21 4.88 17.63 7.32 13.74
///                              7.89 13.21 13.32 11.63 27.82
///
/// i.e. a SMOOTH deceleration, with the walk still paying `w_min` 8.17e6 of lb
/// per core at t=220. A 20s floor would have committed one-way right there, on
/// a gap barely above the ones either side of it — "slower", not "stopped" —
/// and that is the premature commit that would cost the slow-walk families
/// (rna-alignment, protein_ins) instances AY solves today. 30s clears the whole
/// observed deceleration including its 27.8s outlier.
///
/// The other side of the bracket, from `af-synthesis_wt-af-synthesis_stb_50_120_5`
/// at 900s — the family the count arm cannot reach (AY 0/15): 16 cores arrive
/// sub-second by t=16.5 (median 569ms), then ONE 41.0s assumption solve delivers
/// core #17 at t=57.49. That 41s is a drought the gate never sees (brake 2 in
/// [`OllEngine::core_discovery_cold`]: it is a single in-flight solve, and it
/// PAID), so the arm stays shut and the reversible `#expensive-core-descent`
/// kick takes the entry at t=57.59 exactly as it does today. The rate arm's
/// reach on this family is the entry AFTER that: once a kick slice hands back
/// dry, the next evaluation is 30s+ past core #17 with nothing since, and the
/// descent gets the longer, evidence-backed slice instead of another 10s one —
/// which is the whole point on a family where the kick already reaches 14/15
/// entries and converts 0.
///
/// The 41s gap DOES enter the trailing window when core #17 lands, but with 15
/// sub-second gaps still in a 16-wide window the median stays sub-second, so
/// this floor remains the bar on af-synthesis exactly as it was under the
/// first-N baseline. That is deliberate: the statistic change must not move the
/// family the lever measured a win on.
const COLD_CORE_MIN_DROUGHT: Duration = ORGANIC_DESCENT_SLICE;

/// #cold-core-descent: no rate-based entry inside the opening of a run,
/// matching the `#ub-stale-descent` floor. The incumbent is usually still
/// moving here, and an early entry is the one that risks
/// [`OllEngine::select_descent_enc`] declining on size — see
/// `descent_size_declined` for why that decline is no longer permanent.
const COLD_CORE_MIN_ELAPSED: Duration = Duration::from_secs(20);

/// #cold-core-descent: where a core handed to [`OllEngine::process_core`] came
/// from. Consumed ONLY by the rate gate — every other effect of `process_core`
/// is identical for both variants.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum CoreOrigin {
    /// Extracted from a SAT call that returned UNSAT under assumptions (the
    /// main OLL loop, `exhaust_sum`). Only these measure how fast the engine
    /// is DISCOVERING cores, so only these set the rate baseline.
    Search,
    /// Paid out of a batch that was computed without a SAT call of its own:
    /// `pay_mined_cores` replaying pre-mined cores at entry and at every level
    /// change, and the AM1 probe's failed-selector loop. These land
    /// back-to-back in MICROSECONDS — 8 of them satisfy `COLD_CORE_MIN_SAMPLE`
    /// with a ~0ms median, which would hand the gate a "the instance was
    /// streaming cores" baseline manufactured entirely out of bookkeeping.
    Batch,
}

/// Which arm opened the descent entry gate, and therefore what treatment the
/// entry gets. Naming the arm is what makes a corpus sweep attributable: the
/// trace used to label by core count, which reports every cold-rate entry on an
/// instance that had also reached `lsu_min_cores` as a `count` entry.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum DescentArm {
    /// The gate is shut.
    None,
    /// `#ub-stale-descent` / `#expensive-core-descent` / `#fold-descent-kick`:
    /// a heuristic gap signal with no stall evidence. Bounded 10s-class slice.
    Kick,
    /// #cold-core-descent: core discovery went cold against this instance's own
    /// recent rate. Bounded organic-length slice.
    Cold,
    /// The historical organic gate: `cores_found >= lsu_min_cores`, lb-stalling,
    /// gap open. One-way commit unless `#descent-organic-slice` is enabled.
    Count,
}

/// The descent entry gate, as a pure function of the arms' evidence.
///
/// Extracted from `solve` so the WIRING is testable, not only the predicates it
/// consumes: before this existed, deleting `cold_entry` from the gate or
/// reverting the kick/cold precedence left the whole suite green.
///
/// PRECEDENCE. `Cold` outranks `Kick` because a kick and the rate arm can open
/// in the SAME iteration — on the af-synthesis family the
/// `#expensive-core-descent` kick arms within a minute of the last core, which
/// is also when a drought passes the rate bar. If `Kick` won that race the
/// entry would be downgraded to a 10s slice, which is precisely the rotation
/// this lever exists to replace on a family where the kick already reaches
/// 14/15 entries and converts 0 while the upper-bound solvers go 15/15. The
/// rate arm carries evidence the kick does not (a drought past the instance's
/// OWN bar, over a minimum sample of search-derived intervals, with an
/// incumbent in hand), so it earns the LONGER — still reversible — slice.
/// With `cold_enabled == false` the classification is bit-identical to the
/// pre-lever gate, which is what makes the A/B a single-binary paired run.
fn classify_descent_arm(
    have_incumbent: bool,
    cold_enabled: bool,
    cold_ready: bool,
    kick_armed: bool,
    count_ready: bool,
) -> DescentArm {
    if !have_incumbent {
        return DescentArm::None;
    }
    if cold_enabled && cold_ready {
        return DescentArm::Cold;
    }
    if kick_armed {
        return DescentArm::Kick;
    }
    if count_ready {
        return DescentArm::Count;
    }
    DescentArm::None
}

/// How long this entry's descent slice may run: `Some(len)` for a REVERSIBLE
/// slice that hands control back to OLL when it expires dry, `None` for the
/// one-way commit (no deadline; lb is frozen for the rest of the budget,
/// because `descend` only ever moves ub).
///
/// `DescentArm::None` never reaches here — the gate is shut — and maps to
/// `None` only because there is no slice to run.
fn descent_slice_len(
    arm: DescentArm,
    organic_slice_enabled: bool,
    kick_len: Duration,
    organic_len: Duration,
) -> Option<Duration> {
    match arm {
        DescentArm::Kick => Some(kick_len),
        // #cold-core-descent D5: ALWAYS reversible, independent of the
        // `#descent-organic-slice` flag. The cold arm carries the weakest
        // evidence of the three (no core count, no lb-stall test, no gap cap
        // beyond `gap_ok`), so it must not carry the strongest treatment. On
        // the slow-walk families it is most likely to misfire on — rna-alignment
        // and protein_ins — the core walk is the PRODUCTIVE path, and a one-way
        // commit there forfeits instances AY solves today. Escalating a cold
        // entry to an unbounded commit needs its own paired A/B, not a default.
        DescentArm::Cold => Some(organic_len),
        DescentArm::Count => organic_slice_enabled.then_some(organic_len),
        DescentArm::None => None,
    }
}

/// Kill switch for the expensive-core early descent kick
/// (#expensive-core-descent). DEFAULT ON: `--maxsat-no-early-descent`
/// restores the pre-fix gate. Motivation (rna-alignment_wt-k100 family): on a
/// large hard formula each assumption solve costs ~1s, so OLL reaches neither
/// the 64-core organic descent bar nor the 20s ub-stale kick floor within
/// budget — yet the (reversible) uniform-residual totalizer descent, once
/// engaged, converges from the ub side in a handful of solves. This brings the
/// kick forward once cores are demonstrably expensive (high mean solve time)
/// with a small remaining gap and a uniform-weight residual (so the descent
/// encoding is the cheap totalizer). Reversible: a dry 10s slice hands control
/// back to OLL, so a mis-fire costs at most one slice.
fn maxsat_early_descent_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| !ay_core::misc_cli_flags().maxsat_no_early_descent)
}

/// #descent-organic-slice: bound the ORGANIC descent entry the same way kick
/// entries are already bounded, instead of committing for
/// `Duration::from_hours(8760)` (one year, i.e. the rest of the run).
///
/// `descend()` only ever advances `self.ub`; the lower bound moves exclusively
/// in the OLL loop, which a one-way commit never re-enters. So the instant the
/// organic gate fires, lb is frozen for the whole remaining budget — measured
/// on causal-discovery at 60–93% of the run spent unable to improve lb at all.
/// That is the flat time-curve: 3600s buys exactly what 60s bought.
///
/// The bounded form keeps the kick path's proven discipline — a slice that
/// improved the incumbent earns another (the descent is converging; cutting it
/// wastes warm bound clauses), and only a DRY slice hands control back to OLL —
/// so a productive descent still runs to completion. What it removes is the
/// case where an UNPRODUCTIVE descent owns the rest of the run.
///
/// DEFAULT OFF pending the paired A/B; `--ab-maxsat-descent-organic-slice`.
fn descent_organic_slice_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| ay_core::misc_cli_flags().ab_maxsat_descent_organic_slice)
}

/// Organic descent slice when the engine is budget-blind (no deadline set).
/// Larger than the kick's 10s because an organic entry has already cleared the
/// stall evidence the kicks only guess at.
const ORGANIC_DESCENT_SLICE: Duration = Duration::from_secs(30);

/// Share of the REMAINING budget one organic descent slice may take when a
/// deadline is known. The point is not the constant but that the slice scales:
/// a 60s run keeps today's short slices, while a 3600s run alternates OLL and
/// descent in large blocks instead of handing the descent everything at once.
const ORGANIC_DESCENT_BUDGET_DIVISOR: u32 = 8;

/// Clamp for the budget-scaled organic slice.
const ORGANIC_DESCENT_SLICE_MIN: Duration = Duration::from_secs(10);
const ORGANIC_DESCENT_SLICE_MAX: Duration = Duration::from_mins(5);

/// A/B escape for [`OllEngine::descent_kick_gap_cap`]: restore the pre-2026-08-02
/// ABSOLUTE kick gap bar (`DESCENT_KICK_GAP`, ignoring the objective's own
/// granularity). Exists only so the scale-relative bar can be measured against
/// its predecessor as a paired A/B; delete once that measurement is banked.
/// `--ab-maxsat-kick-gap-abs`.
fn kick_gap_abs_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| ay_core::misc_cli_flags().ab_maxsat_kick_gap_abs)
}

/// Floor of the kick gap bar; see [`OllEngine::descent_kick_gap_cap`] for the
/// scale-relative widening built on top of it.
const DESCENT_KICK_GAP: Weight = 32;

/// Mirrors the `gte_build` budgets in `ensure_descent_enc` (the `inputs.len() >
/// 10_000` bail and `out_budget`). The gap bar only widens where those budgets
/// predict a GTE/totalizer rather than the propagation-dead wide adder.
const GTE_CHEAP_INPUTS: usize = 10_000;
const GTE_CHEAP_OUTS: Weight = 400_000;

/// #dpw-descent: DPW's own emission budgets, enforced by the closed-form
/// predictor BEFORE a variable is allocated or a clause emitted. Deliberately
/// the same numbers `gte_build` uses, so "which encoding is cheaper" is asked
/// on one scale.
const DPW_VAR_BUDGET: usize = 400_000;
const DPW_CLAUSE_BUDGET: usize = 4_000_000;

/// #dpw-descent: how much smaller than the GTE a DPW must be before it is
/// taken.
///
/// NOT a tie-break at 1x. DPW is a strictly WEAKER PROPAGATOR than the GTE it
/// would replace — measured over 26,948 arc-consistency probes, DPW forces
/// 81.9% of the literals GTE's 100% does, and the loss concentrates exactly at
/// the boundary a closing UNSAT lives on (58.5% at excess 1, degrading with top
/// granularity: 77.9% at this family's `2^3`). Trading that away for a 5%
/// clause saving is a bad deal in both directions; trading it for the measured
/// 6.0x–11.0x on the af-synthesis family is the whole point of the encoding.
/// A 2x floor keeps today's behaviour on everything in between.
const DPW_MIN_ADVANTAGE: usize = 2;

/// #dpw-descent: THE selection predicate — is the watchdog a decisive enough
/// win over the GTE this instance would otherwise get?
///
/// Factored out so `select_descent_enc` and
/// [`lsu_tests::dpw_selection_requires_a_decisive_size_win`] decide on the
/// same code rather than on two copies of it.
fn dpw_beats_gte(dpw_clauses: usize, gte_clauses: usize) -> bool {
    dpw_clauses.saturating_mul(DPW_MIN_ADVANTAGE) <= gte_clauses
}

/// #dpw-descent escape hatch. DEFAULT ON. `--maxsat-no-dpw` never selects
/// DPW, leaving encoding choice bit-identical to the pre-lever engine, so the
/// lever can be measured as a paired A/B — with an A/A control — from ONE
/// binary (the discipline `--maxsat-no-descent-residual` exists for).
fn dpw_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| !ay_core::misc_cli_flags().maxsat_no_dpw)
}

/// The measured kick slice, and the floor of the budget-scaled form.
const DESCENT_KICK_SLICE: Duration = Duration::from_secs(10);

/// #descent-residual: hard ceiling on how many residual cuts one run may build.
/// A rebuild already requires the cap to have halved, so this is a backstop
/// against pathological cap sequences, not the primary limiter.
const RESIDUAL_MAX_BUILDS: u32 = 8;

/// #descent-residual: strengthen the descent with a redundant cut over the
/// REFORMULATED residual objective at cap `ub - lb`, alongside the exact
/// original-objective encoding at `ub - preproc_cost`. See [`ResidualBound`]
/// for the encodings and the additive rationale, and
/// [`OllEngine::descent_residual_cap`] for the soundness invariant.
///
/// DEFAULT ON. `--maxsat-no-descent-residual` is an ESCAPE HATCH: it builds
/// and tightens no residual cut, leaving the descent bit-identical to the
/// pre-lever engine (encoding SELECTION is untouched either way). Kept, as
/// `--maxsat-no-early-descent` is, so the lever can be measured as a paired
/// A/B — with an A/A control — from one binary.
fn descent_residual_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| !ay_core::misc_cli_flags().maxsat_no_descent_residual)
}

/// #descent-kick-scale: budget-scale the KICK descent slice, which is otherwise
/// a hard-coded 10s.
///
/// The organic arm already scales (`ORGANIC_DESCENT_*`), but measurement shows
/// the organic gate is UNREACHABLE on the expensive-core families: it demands
/// `cores_found >= lsu_min_cores` = 64 and af-synthesis runs end at ~17 cores.
/// So on exactly the instances this matters for, the 10s kick is the ONLY entry
/// path — 17% of a 60s budget but **0.28% of a 3600s budget**, against a proof
/// obligation that Pacose/PacoseMP2 need 275–803s to refute with a stronger
/// encoding than AY's GTE.
///
/// A kick slice is reversible (a DRY slice hands control back to OLL; one that
/// improved the incumbent earns another), and the descent's UNSAT branch is a
/// complete optimality proof, so a longer slice is a second complete route to
/// the answer rather than a gamble. The downside is bounded by one dry slice.
///
/// DEFAULT OFF — the 10s kick is measured behaviour and scaling it changes the
/// default path. `--ab-maxsat-descent-kick-scale`.
fn descent_kick_scale_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| ay_core::misc_cli_flags().ab_maxsat_descent_kick_scale)
}

/// Retired diagnostic gate for the residual cost-identity trace.
/// B24 removed its never-set environment opt-in; it is always disabled.
fn identity_check_enabled() -> bool {
    false // B24: never-set diagnostic opt-in retired.
}

/// Wall-clock budget for one core-exhaustion SAT probe.
const EXHAUST_PROBE_BUDGET: Duration = Duration::from_millis(150);

/// Fraction of total elapsed solve time that core exhaustion may consume.
const EXHAUST_TIME_SHARE: f64 = 0.25;

// ----- Deletion-based core minimization (#minimize) -------------------------
// CGSS2 budgets each minimize pass in conflicts — 1000 absolute plus 1% of
// the conflicts spent so far, split across the members with unused allowance
// carried forward (cgss2.cpp:899-914). AY keeps that conflict budget as the
// PRIMARY limiter (ay-sat's deterministic set_conflict_budget) and adds two
// wall-clock guards its reset-heavy assumption path needs: a per-probe
// deadline and a per-core cap (one assumption solve on a large formula can
// burn hundreds of ms in uninterruptible setup before the first conflict —
// measured on haplotyping-pedigrees, where 30ms deadlines returned 100%
// Unknown probes), plus the global share gate at the call site.

/// Conflict budget for one whole minimize pass (CGSS2
/// minimize_budget_absolute).
const MINIMIZE_CONFLICTS_ABS: u64 = 1000;
/// Additional pass budget as a share of all conflicts spent so far (CGSS2
/// minimize_budget_relative = 1%).
const MINIMIZE_CONFLICTS_REL: f64 = 0.01;
/// Wall-clock interrupt for one deletion-minimization SAT probe (#minimize).
const MINIMIZE_PROBE_BUDGET: Duration = Duration::from_millis(50);
/// Total wall-clock budget for minimizing one core (#minimize).
const MINIMIZE_CORE_BUDGET: Duration = Duration::from_millis(300);
/// Fraction of total elapsed solve time deletion minimization may consume.
const MINIMIZE_TIME_SHARE: f64 = 0.12;
/// Dry-pass damper (#minimize): after this many consecutive passes in which
/// EVERY probe returned Unknown (no SAT answer, no shrink — per-call setup
/// swallows the budget on this formula), stop paying for new passes.
/// Measured on haplotyping ped3.G.recomb10-0.20-14: 15 dry passes of doomed
/// probes helped push a 46s solve past the 60s timeout.
const MINIMIZE_DRY_PASS_LIMIT: u32 = 4;
/// While dampened, still attempt every Nth fat core so minimization can
/// recover when the residual problem becomes cheap enough to probe.
const MINIMIZE_RETRY_STRIDE: u64 = 16;

// ----- LP-boost lane (#lp-boost) tuning constants ---------------------------
// A certified lower-bound booster: a dual packing LP over stored
// pure-original UNSAT cores (max sum y, one y >= 0 per core, one `<=` row
// per soft selector). See OllEngine::run_lp_boost for the soundness
// argument; caps sized to ay-lp's dense-tableau simplex.

/// Maximum stored cores (= LP columns). Beyond this the store stops growing.
const LP_BOOST_MAX_CORES: usize = 2000;
/// Maximum distinct soft selectors across stored cores (= LP rows). The
/// build is skipped — and the lane disabled — when the support exceeds it.
const LP_BOOST_MAX_SUPPORT: usize = 1500;
/// Cores larger than this are not stored: fat cores make weak packing rows
/// and inflate the support toward the row cap (quality cap, not soundness).
const LP_BOOST_MAX_CORE_SIZE: usize = 128;
/// After the first (stall-gated) round, re-run at most every this many
/// newly processed cores.
const LP_BOOST_CORE_STRIDE: u64 = 64;
/// Auto-disable the lane after this many consecutive rounds that failed to
/// raise the effective lower bound (the verdict's dry-round rule).
const LP_BOOST_MAX_DRY_ROUNDS: u32 = 3;
/// Simplex pivot budget per LP call (budgeted entry point, P0b).
const LP_BOOST_MAX_ITERS: usize = 20_000;
/// Wall-clock budget per LP call: a stuck simplex must not eat the run.
/// Truncation is sound — any feasible dual iterate is a valid bound.
const LP_BOOST_CALL_BUDGET: Duration = Duration::from_secs(2);
/// Fixed-point shift for the exact rational certification of dual iterates.
const LP_BOOST_FP_SHIFT: u32 = 20;

/// LP-boost lane activation mode (#lp-boost).
// Force/Off are only constructed by the test tunings today; production
// builds run Auto (the default: lane ON behind its instance gate).
#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) enum LpBoostMode {
    /// Enabled with the instance gate (non-uniform weights only) and the
    /// size caps. Default: the lane is ON for weighted instances.
    #[default]
    Auto,
    /// Test-only: bypass the non-uniform-weight instance gate so tiny
    /// brute-force nets exercise the lane. Size caps still apply.
    Force,
    /// Lane fully disabled (no capture, no LP rounds).
    Off,
}

/// Engine thresholds, overridable in tests so small instances exercise the
/// same code paths (notably LSU) that big competition instances take.
pub(crate) struct OllTuning {
    /// Minimum processed cores before the LSU switch is considered
    /// (a conjunct of the descent entry gate; `0` = no core-count bar,
    /// `u64::MAX` = descents never engage).
    pub(crate) lsu_min_cores: u64,
    /// Minimum `ub - lb` gap, in multiples of the uniform weight, before
    /// the LSU switch is considered.
    pub(crate) lsu_min_gap_units: Weight,
    /// Minimum average wall-clock milliseconds per processed core before
    /// OLL counts as stalling (cheap cores beat any descent).
    pub(crate) lsu_stall_ms_per_core: u64,
    /// Skip the GTE attempt and go straight to the adder descent (tests).
    pub(crate) force_adder: bool,
    /// Cores to observe before forming abstraction sets (0 = immediately).
    pub(crate) abstraction_min_cores: u64,
    /// Test-only: try the cluster descent BEFORE the GTE so tiny
    /// brute-force instances exercise the ClusterTot path.
    pub(crate) force_cluster: bool,
    /// #dpw-descent test-only: take the DPW descent whenever it BUILDS,
    /// skipping the size comparison against the GTE. Brute-force fixtures are
    /// far too small for DPW to win on size honestly (the watchdog's advantage
    /// is asymptotic in the cap), so without this the end-to-end nets would
    /// never reach the path at all.
    pub(crate) force_dpw: bool,
    /// LP-boost lane mode (#lp-boost). Default Auto (on, gated to
    /// non-uniform weights).
    pub(crate) lp_boost: LpBoostMode,
    /// #tot-eqs override: `None` defers to the `AY_AB_MAXSAT_TOT_EQS` env
    /// gate, `Some(b)` forces the lever (tests pin it ON so the
    /// brute-force cross-checks cover the reverse-direction clauses).
    pub(crate) tot_eqs: Option<bool>,
    /// #core-clause override: `None` defers to `--ab-maxsat-core-clause`.
    pub(crate) core_clause: Option<bool>,
}

impl Default for OllTuning {
    fn default() -> Self {
        OllTuning {
            lsu_min_cores: 64,
            lsu_min_gap_units: 128,
            lsu_stall_ms_per_core: 30,
            force_adder: false,
            // Ex-ante id-locality sets measured NEUTRAL on MSE 2024 stride
            // samples (-1 unweighted / +1 weighted vs baseline); disabled
            // until formation is core-informed. The machinery and its
            // correctness nets stay exercised through the test tunings.
            abstraction_min_cores: u64::MAX,
            force_cluster: false,
            force_dpw: false,
            lp_boost: LpBoostMode::Auto,
            tot_eqs: None,
            core_clause: None,
        }
    }
}

/// One node of a lazily-built totalizer tree.
///
/// `outs[j]` is a literal that is implied true whenever at least `j + 1` of
/// the leaf input literals are true. Only the input→output direction is
/// encoded (sufficient for enforcing upper bounds via assuming `¬outs[j]`);
/// the output→input direction is added LAZILY where it can propagate — see
/// [`TotNode::force_true`] (#tot-eqs).
///
/// ⚠️ STATUS (corrected 2026-07-27): `#tot-eqs` is **LANDED and DEFAULT ON** for
/// weighted instances — `tot_eqs_enabled()` reads `AY_AB_MAXSAT_TOT_EQS != "0"`,
/// and commit `26de25fa7` measured **+5 solved full-track** (571 @60s paired,
/// zero-wrong, 0 cost mismatches on 321 commonly-solved). It is gated to
/// weighted instances by `tot_eq_budget = 0` unless there are ≥2 distinct soft
/// weights, so the unweighted track is bit-identical.
///
/// The "default-OFF / MEASURED NEGATIVE" text that stood here until 2026-07-27
/// described the pre-landing state and contradicted the code beside it; it was
/// on track to make a future session re-propose a lever that is already in.
/// The −3 record below is retained because its REASONING is still correct and
/// still explains the shape of the win — but read it as history, not status.
///
/// HISTORICAL — the reverse direction measured −3 BEFORE the fixes that made it
/// pay (2026-07-25, branch `maxsat/tot-eqs-experiment`). The known
/// gap is real: with implication-only clauses a PROVEN-true output satisfies
/// every clause it occurs in and propagates nothing downward, so the engine
/// re-derives an already-proven bound by search on every later conflict.
/// CGSS2 closes it by calling `forced_true`/`add_partial_eqs` at the two
/// points where an output is proven. A faithful port of that machinery —
/// including CGSS2's budget model (decs/cost/prod = 50/50/2500) and a
/// distilled "one permanent hard clause per core" variant — was measured on
/// mse24 weighted, 30s, paired 3+3 legs on the same binary:
///   #tot-eqs      net -3 solved (300 vs 303), median ratio 1.0045, +5.1% wall
///   #core-clause  net -3 solved (298 vs 301), median ratio 1.0074, +7.2% wall
/// Both legs: ZERO wrong answers, 0 cost mismatches over ~295 commonly-solved
/// instances — the soundness argument held empirically; it simply loses on
/// cost. WHY: CGSS2's equivalences earn their BCP cost by propagating into
/// SHARED subtrees (it prunes with `!eql && !eqr && parents < 2`), but AY
/// builds a FRESH balanced tree per core, so the port is a strictly weakened
/// CGSS — full clause cost, little payoff.
///
/// The prerequisite that would change the verdict is STRUCTURE SHARING:
/// arena-ify `TotNode` and intern leaves and child pairs (CGSS `lit_leafs` /
/// `parents`). TRAP for that work: guarded-descent totalizers must NEVER be
/// interned — a guard-weakened node does not entail input→output for another
/// owner, which would under-charge the cost identity and report a cost BELOW
/// the optimum.
struct TotNode {
    outs: Vec<Literal>,
    size: usize,
    /// Bound this node's clause set is complete up to (`min(k, size)`).
    built_k: usize,
    /// #tot-eqs: reverse-direction bookkeeping, mirroring CGSS2's
    /// `Node::lleq`/`rreq`/`litseq` (ss_encoder.h:20-22). `eq_l` / `eq_r` are
    /// the left/right child output-index ranges the reverse clauses are
    /// complete for, and `eq_outs` the number of this node's outputs they
    /// cover. All three only grow, so a clause is never emitted twice
    /// (duplicate clauses are sound but inflate the watch lists this engine
    /// scans linearly on removal).
    eq_l: usize,
    eq_r: usize,
    eq_outs: usize,
    left: Option<Box<TotNode>>,
    right: Option<Box<TotNode>>,
}

impl TotNode {
    /// Build a balanced tree over the input literals. No clauses are added
    /// until [`TotNode::extend`] is called.
    fn build(lits: &[Literal]) -> TotNode {
        debug_assert!(!lits.is_empty());
        if lits.len() == 1 {
            return TotNode {
                outs: vec![lits[0]],
                size: 1,
                built_k: 1,
                eq_l: 0,
                eq_r: 0,
                eq_outs: 0,
                left: None,
                right: None,
            };
        }
        let mid = lits.len() / 2;
        let left = Box::new(TotNode::build(&lits[..mid]));
        let right = Box::new(TotNode::build(&lits[mid..]));
        TotNode {
            outs: Vec::new(),
            size: lits.len(),
            built_k: 0,
            eq_l: 0,
            eq_r: 0,
            eq_outs: 0,
            left: Some(left),
            right: Some(right),
        }
    }

    /// Ensure output literals and clauses exist for counts up to `k`
    /// (capped at this node's size). Newly required output variables are
    /// allocated through `fresh`.
    fn extend(
        &mut self,
        k: usize,
        sat: &mut SatSolver,
        fresh: &mut dyn FnMut(&mut SatSolver) -> Literal,
        guard: Option<Literal>,
    ) {
        let target = k.min(self.size);
        if target <= self.built_k {
            return;
        }
        let (Some(left), Some(right)) = (self.left.as_mut(), self.right.as_mut()) else {
            // Leaf: fully built by construction.
            return;
        };
        left.extend(target, sat, fresh, guard);
        right.extend(target, sat, fresh, guard);

        while self.outs.len() < target {
            self.outs.push(fresh(sat));
        }

        let a = left.size;
        let b = right.size;
        // All (i, j) pairs with i + j = t <= built_k were added previously
        // (any such i, j <= t <= built_k), so only levels built_k+1..=target
        // are new.
        for t in (self.built_k + 1)..=target {
            let i_lo = t.saturating_sub(b.min(t));
            let i_hi = a.min(t);
            for i in i_lo..=i_hi {
                let j = t - i;
                let mut clause = Vec::with_capacity(3);
                if i > 0 {
                    clause.push(left.outs[i - 1].negated());
                }
                if j > 0 {
                    clause.push(right.outs[j - 1].negated());
                }
                clause.push(self.outs[t - 1]);
                if let Some(g) = guard {
                    clause.push(g.negated());
                }
                sat.add_clause(clause);
            }
        }
        self.built_k = target;
    }

    /// #tot-eqs: emit this node's REVERSE-direction clauses, extending
    /// coverage to left-child output range `leq_in`, right-child range
    /// `req_in`, and every output built so far. Port of CGSS2
    /// `SSEncoder::add_equivalences` (ss_encoder.cpp:434-476).
    ///
    /// Each emitted clause is `(l.outs[li] ∨ r.outs[ri] ∨ ¬outs[li+ri])`:
    /// `¬l.outs[li]` bounds the left subtree's true-input count by `li` and
    /// `¬r.outs[ri]` bounds the right's by `ri`, so the total is at most
    /// `li + ri` and `outs[li+ri]` (which asserts at least `li+ri+1`) must be
    /// false. An index equal to the child's own input count is a tautological
    /// bound, so that literal is DROPPED — a shorter, strictly stronger
    /// clause. Every clause is therefore a valid consequence of the intended
    /// meaning of the (fresh) output variables, which is what makes this
    /// sound: it can only pin `outs` closer to the exact count.
    fn add_equivalences(
        &mut self,
        leq_in: usize,
        req_in: usize,
        sat: &mut SatSolver,
        budget: &mut i64,
    ) {
        let (Some(left), Some(right)) = (self.left.as_ref(), self.right.as_ref()) else {
            return; // leaf: its single output IS its input
        };
        let outs = &self.outs;
        let m = outs.len();
        if m == 0 || *budget <= 0 {
            return;
        }
        // Clamp to output literals that exist (a partially built child only
        // supports the indices it has) and keep coverage monotone.
        let leq = leq_in.min(left.outs.len()).max(self.eq_l);
        let req = req_in.min(right.outs.len()).max(self.eq_r);
        let (l_size, r_size) = (left.size, right.size);
        let (l_outs, r_outs) = (&left.outs, &right.outs);
        let (eq_l, eq_r, eq_outs) = (self.eq_l, self.eq_r, self.eq_outs);

        let mut emit = |li: usize, ri: usize| {
            let t = li + ri;
            debug_assert!(t < m);
            let mut clause = Vec::with_capacity(3);
            if li != l_size {
                match l_outs.get(li) {
                    Some(&lit) => clause.push(lit),
                    None => return, // index not materialized: skip
                }
            }
            if ri != r_size {
                match r_outs.get(ri) {
                    Some(&lit) => clause.push(lit),
                    None => return,
                }
            }
            clause.push(outs[t].negated());
            *budget -= 1;
            sat.add_clause(clause);
        };

        // (a) Outputs grew: backfill pairs inside the already-committed child
        //     ranges for the new output indices.
        for t in eq_outs..m {
            for ri in 0..=t {
                let li = t - ri;
                if ri < eq_r || li < eq_l {
                    emit(li, ri);
                }
            }
        }
        // (b) The left range grew: all partners for each newly covered li.
        for li in eq_l..leq {
            let mut ri = 0;
            while li + ri < m && ri <= r_outs.len() {
                emit(li, ri);
                ri += 1;
            }
        }
        // (c) The right range grew: all partners for each newly covered ri,
        //     skipping the li values (b) just covered.
        for ri in eq_r..req {
            let mut li = 0;
            while ri + li < m && li <= l_outs.len() {
                if !(li >= eq_l && li < leq) {
                    emit(li, ri);
                }
                li += 1;
            }
        }

        self.eq_l = leq;
        self.eq_r = req;
        self.eq_outs = m;
    }

    /// #tot-eqs: make this whole subtree a full-equivalence subtree (CGSS2
    /// `SSEncoder::add_full_eqs`, ss_encoder.cpp:481-487).
    fn add_full_eqs(&mut self, sat: &mut SatSolver, budget: &mut i64) {
        if *budget <= 0 {
            return;
        }
        self.add_equivalences(usize::MAX, usize::MAX, sat, budget);
        if let (Some(left), Some(right)) = (self.left.as_mut(), self.right.as_mut()) {
            left.add_full_eqs(sat, budget);
            right.add_full_eqs(sat, budget);
        }
    }

    /// #tot-eqs: recursive, budgeted equivalence addition (CGSS2
    /// `SSEncoder::add_partial_eqs`, ss_encoder.cpp:502-531).
    ///
    /// `nof_true` is how many of this subtree's inputs are known true (may go
    /// negative: then it records how many inputs must be shown FALSE
    /// elsewhere before this subtree learns anything), and `cost` how many
    /// equivalences other subtrees would have to pay for that information to
    /// arrive. The three budget constants cut the recursion off before the
    /// encoding grows faster than the propagation it buys. Return sign
    /// follows CGSS2: negative asks the caller to make the SIBLING a full
    /// equivalence subtree, magnitude is the child output range to cover.
    fn add_partial_eqs(
        &mut self,
        nof_true: i64,
        cost: i64,
        cfg: TotEqCfg,
        sat: &mut SatSolver,
        budget: &mut i64,
    ) -> i64 {
        if *budget <= 0 {
            return 0;
        }
        if nof_true <= -cfg.max_decs || (nof_true <= 0 && cost > cfg.max_cost) {
            return 0;
        }
        if nof_true <= 0 && nof_true.saturating_neg().saturating_mul(cost) > cfg.max_prod {
            return 0;
        }
        let (Some(left), Some(right)) = (self.left.as_ref(), self.right.as_ref()) else {
            // Leaf: its output is an input literal, so information reaching
            // here propagates directly.
            return if nof_true > 0 { 1 } else { -1 };
        };
        let (l_size, r_size) = (left.size as i64, right.size as i64);
        let l_cost = cost.saturating_add(l_size.saturating_mul(l_size));
        let r_cost = cost.saturating_add(r_size.saturating_mul(r_size));

        let eql = self
            .left
            .as_mut()
            .map(|l| l.add_partial_eqs(nof_true - r_size, r_cost, cfg, sat, budget))
            .unwrap_or(0);
        let eqr = self
            .right
            .as_mut()
            .map(|r| r.add_partial_eqs(nof_true - l_size, l_cost, cfg, sat, budget))
            .unwrap_or(0);
        if eql == 0 && eqr == 0 {
            // Nothing below can propagate, and (unlike CGSS2, whose nodes are
            // shared between cores) an unshared node has no other consumer.
            return 0;
        }
        if eql < 0 {
            if let Some(right) = self.right.as_mut() {
                right.add_full_eqs(sat, budget);
            }
        }
        if eqr < 0 {
            if let Some(left) = self.left.as_mut() {
                left.add_full_eqs(sat, budget);
            }
        }
        let (leq, req) = (eql.unsigned_abs() as usize, eqr.unsigned_abs() as usize);
        self.add_equivalences(leq, req, sat, budget);

        let m = self.outs.len() as i64;
        if cost > cfg.max_cost {
            return m.min(nof_true);
        }
        -(m.min(nof_true.saturating_add(cfg.max_decs)))
    }

    /// #tot-eqs: `outs[ix]` has been PROVEN true (asserted as a hard unit), so
    /// at least `ix + 1` of this node's inputs are violated. Add the reverse
    /// clauses that let unit propagation actually use that fact — CGSS2
    /// `SSEncoder::forced_true` (ss_encoder.cpp:537-549).
    ///
    /// Without this the unit is inert: with only input→output clauses, a TRUE
    /// output satisfies every clause it occurs in and propagates nothing, so
    /// the SAT engine must re-derive the already-proven bound by search on
    /// every subsequent conflict.
    fn force_true(&mut self, ix: usize, sat: &mut SatSolver, budget: &mut i64) {
        if *budget <= 0 {
            return;
        }
        self.add_partial_eqs(ix as i64 + 1, 0, tot_eq_cfg(), sat, budget);
    }
}

/// Generalized totalizer (Joshi et al. 2015) over weighted inputs, with all
/// sums capped at `cap`: an output literal exists per distinct achievable
/// (capped) violation-weight sum s, implied true whenever the true inputs'
/// weights reach s. Build respects output/clause budgets; `None` = too big.
fn gte_build(
    inputs: &[(Literal, Weight)],
    cap: Weight,
    sat: &mut SatSolver,
    fresh: &mut dyn FnMut(&mut SatSolver) -> Literal,
    guard: Option<Literal>,
    out_budget: &mut i64,
    clause_budget: &mut i64,
) -> Option<Vec<(Weight, Literal)>> {
    debug_assert!(!inputs.is_empty());
    if inputs.len() == 1 {
        let (lit, w) = inputs[0];
        return Some(vec![(w.min(cap), lit)]);
    }
    let mid = inputs.len() / 2;
    let left = gte_build(
        &inputs[..mid],
        cap,
        sat,
        fresh,
        guard,
        out_budget,
        clause_budget,
    )?;
    let right = gte_build(
        &inputs[mid..],
        cap,
        sat,
        fresh,
        guard,
        out_budget,
        clause_budget,
    )?;

    // Work bound BEFORE the O(|L|·|R|) pair enumeration: the emission loop
    // below spends one clause-budget unit per nonzero pair — exactly
    // (|L|+1)·(|R|+1) − 1 of them (only the (0, 0) pair sums to zero) — so
    // a node whose pair count exceeds the remaining clause budget is
    // rejected either way. Bailing here is decision-equivalent and keeps
    // the build's wall time bounded by the budgets: rounded-weight shapes
    // (correlation-clustering) previously burned 30+ uninterruptible
    // seconds and gigabytes enumerating pair sums of a doomed node.
    let pairs = (left.len() as i64 + 1).saturating_mul(right.len() as i64 + 1);
    if pairs - 1 > *clause_budget {
        return None;
    }

    // Distinct capped sums over (0 ∪ left) x (0 ∪ right).
    let mut sums: Vec<Weight> = Vec::new();
    for &(a, _) in std::iter::once(&(0, Literal::positive(Variable::new(0)))).chain(left.iter()) {
        for &(b, _) in
            std::iter::once(&(0, Literal::positive(Variable::new(0)))).chain(right.iter())
        {
            let s = a.saturating_add(b).min(cap);
            if s > 0 {
                sums.push(s);
            }
        }
    }
    sums.sort_unstable();
    sums.dedup();
    *out_budget -= sums.len() as i64;
    if *out_budget < 0 {
        return None;
    }
    let outs: Vec<(Weight, Literal)> = sums.iter().map(|&s| (s, fresh(sat))).collect();
    let find = |s: Weight| -> Literal {
        let idx = outs.partition_point(|&(v, _)| v < s);
        outs[idx].1
    };

    // (¬L_a ∨ ¬R_b ∨ O_{min(a+b, cap)}) for all child-output pairs.
    for &(a, la) in std::iter::once(&(0u64, Literal::positive(Variable::new(0)))).chain(left.iter())
    {
        for &(b, lb) in
            std::iter::once(&(0u64, Literal::positive(Variable::new(0)))).chain(right.iter())
        {
            let s = a.saturating_add(b).min(cap);
            if s == 0 {
                continue;
            }
            *clause_budget -= 1;
            if *clause_budget < 0 {
                return None;
            }
            let mut clause = Vec::with_capacity(3);
            if a > 0 {
                clause.push(la.negated());
            }
            if b > 0 {
                clause.push(lb.negated());
            }
            clause.push(find(s));
            if let Some(g) = guard {
                clause.push(g.negated());
            }
            sat.add_clause(clause);
        }
    }
    Some(outs)
}

/// Test-only: run the real [`gte_build`] on a private solver under the given
/// budgets, reporting `(aux vars allocated, root outputs)`, or `None` when it
/// declined.
///
/// The budgets are the observable: `gte_build` consumes exactly one
/// `out_budget` unit per fresh output and exactly one `clause_budget` unit per
/// emitted clause, so running it at a budget one unit below `dpw::gte_size`'s
/// prediction — and requiring it to decline — pins the mirror's counts to the
/// builder's own accounting. (The solver's `num_original_clauses` is refreshed
/// from the arena at solve time, not incremented on add, so it cannot serve.)
#[cfg(test)]
pub(crate) fn gte_build_for_test(
    weights: &[Weight],
    cap: Weight,
    out_budget: i64,
    clause_budget: i64,
) -> Option<(usize, usize)> {
    let mut sat = SatSolver::new(0);
    let inputs: Vec<(Literal, Weight)> = weights
        .iter()
        .map(|&w| (Literal::positive(sat.new_var()), w))
        .collect();
    let mut vars = 0usize;
    let mut fresh = |s: &mut SatSolver| {
        vars += 1;
        Literal::positive(s.new_var())
    };
    let mut out_budget = out_budget;
    let mut clause_budget = clause_budget;
    let outs = gte_build(
        &inputs,
        cap,
        &mut sat,
        &mut fresh,
        None,
        &mut out_budget,
        &mut clause_budget,
    );
    outs.map(|outs| (vars, outs.len()))
}

/// Tseitin gates for the adder network. `None` encodes constant false.
/// Full equality encodings keep auxiliary variables functionally
/// determined, so any input assignment extends to the circuit.
struct AdderCtx<'a> {
    sat: &'a mut SatSolver,
    fresh: &'a mut dyn FnMut(&mut SatSolver) -> Literal,
    guard: Option<Literal>,
}

impl AdderCtx<'_> {
    fn emit(&mut self, mut clause: Vec<Literal>) {
        if let Some(g) = self.guard {
            clause.push(g.negated());
        }
        self.sat.add_clause(clause);
    }

    fn xor2(&mut self, a: Literal, b: Literal) -> Literal {
        let o = (self.fresh)(self.sat);
        self.emit(vec![a.negated(), b.negated(), o.negated()]);
        self.emit(vec![a, b, o.negated()]);
        self.emit(vec![a.negated(), b, o]);
        self.emit(vec![a, b.negated(), o]);
        o
    }

    fn and2(&mut self, a: Literal, b: Literal) -> Literal {
        let o = (self.fresh)(self.sat);
        self.emit(vec![a.negated(), b.negated(), o]);
        self.emit(vec![a, o.negated()]);
        self.emit(vec![b, o.negated()]);
        o
    }

    fn maj3(&mut self, a: Literal, b: Literal, c: Literal) -> Literal {
        let o = (self.fresh)(self.sat);
        self.emit(vec![a.negated(), b.negated(), o]);
        self.emit(vec![a.negated(), c.negated(), o]);
        self.emit(vec![b.negated(), c.negated(), o]);
        self.emit(vec![a, b, o.negated()]);
        self.emit(vec![a, c, o.negated()]);
        self.emit(vec![b, c, o.negated()]);
        o
    }

    /// One full-adder bit: returns (sum, carry) with constant folding.
    fn full_add(
        &mut self,
        a: Option<Literal>,
        b: Option<Literal>,
        c: Option<Literal>,
    ) -> (Option<Literal>, Option<Literal>) {
        let mut lits: Vec<Literal> = [a, b, c].into_iter().flatten().collect();
        match lits.len() {
            0 => (None, None),
            1 => (Some(lits[0]), None),
            2 => {
                let (x, y) = (lits[0], lits[1]);
                (Some(self.xor2(x, y)), Some(self.and2(x, y)))
            }
            _ => {
                let (x, y, z) = (lits[0], lits[1], lits[2]);
                let t = self.xor2(x, y);
                let sum = self.xor2(t, z);
                let carry = self.maj3(x, y, z);
                lits.clear();
                (Some(sum), Some(carry))
            }
        }
    }

    /// Ripple-carry addition of two little-endian bit vectors.
    fn add_vecs(&mut self, a: &[Option<Literal>], b: &[Option<Literal>]) -> Vec<Option<Literal>> {
        let n = a.len().max(b.len());
        let mut out = Vec::with_capacity(n + 1);
        let mut carry: Option<Literal> = None;
        for i in 0..n {
            let (s, c) = self.full_add(
                a.get(i).copied().flatten(),
                b.get(i).copied().flatten(),
                carry,
            );
            out.push(s);
            carry = c;
        }
        out.push(carry);
        while out.last().is_some_and(|x| x.is_none()) && out.len() > 1 {
            out.pop();
        }
        out
    }
}

/// Build an adder network summing `weight` for every true `indicator`.
/// Returns the little-endian sum bits.
fn adder_build(
    inputs: &[(Literal, Weight)],
    sat: &mut SatSolver,
    fresh: &mut dyn FnMut(&mut SatSolver) -> Literal,
    guard: Option<Literal>,
) -> Vec<Option<Literal>> {
    let mut ctx = AdderCtx { sat, fresh, guard };
    let mut vecs: Vec<Vec<Option<Literal>>> = inputs
        .iter()
        .map(|&(lit, w)| {
            (0..Weight::BITS - w.leading_zeros())
                .map(|b| if (w >> b) & 1 == 1 { Some(lit) } else { None })
                .collect()
        })
        .collect();
    // Balanced reduction keeps intermediate widths near log2 of the total.
    while vecs.len() > 1 {
        let mut next = Vec::with_capacity(vecs.len().div_ceil(2));
        let mut it = vecs.chunks(2);
        for pair in &mut it {
            match pair {
                [a, b] => next.push(ctx.add_vecs(a, b)),
                [a] => next.push(a.clone()),
                _ => unreachable!(),
            }
        }
        vecs = next;
    }
    vecs.pop().unwrap_or_default()
}

/// Force `sum_bits <= bound` for a constant bound (little-endian S):
/// for every zero bit i of the bound, (¬S_i ∨ ⋁_{j>i, bound_j=1} ¬S_j).
fn assert_sum_le(
    sat: &mut SatSolver,
    sum_bits: &[Option<Literal>],
    bound: Weight,
    guard: Option<Literal>,
) {
    if sum_bits.len() < Weight::BITS as usize && bound >= (1u64 << sum_bits.len()) - 1 {
        return; // trivially satisfied
    }
    'bits: for i in 0..sum_bits.len() {
        if (bound >> i) & 1 == 1 {
            continue;
        }
        let Some(si) = sum_bits[i] else { continue };
        let mut clause = vec![si.negated()];
        for (j, &sj) in sum_bits.iter().enumerate().skip(i + 1) {
            if (bound >> j) & 1 == 1 {
                match sj {
                    Some(sj) => clause.push(sj.negated()),
                    // Constant-0 sum bit under a 1 bound bit: the sum is
                    // already strictly below the bound in this region, so
                    // this clause is trivially satisfied — emitting it
                    // without the disjunct would wrongly exclude models.
                    None => continue 'bits,
                }
            }
        }
        if let Some(g) = guard {
            clause.push(g.negated());
        }
        sat.add_clause(clause);
    }
}

/// Where a sum selector points: which totalizer, and which bound its
/// negated output enforces (`selector = ¬outs[bound - 1]`).
#[derive(Clone, Copy)]
struct SumRef {
    tot: usize,
    bound: usize,
}

/// A core read straight off a hard clause at install time.
#[derive(Clone, Debug)]
struct MinedCore {
    /// The UNIT-soft selectors the clause forbids from all being true.
    lits: Vec<Literal>,
    /// 1-based position of the originating clause among the instance's hard
    /// clauses. The loader adds hard clauses unconditionally in file order, so
    /// this is also that clause's constraint id in an emitted OPB — which is
    /// what lets a certificate name the row a core came from.
    hard_row: u64,
}

/// A mined core the engine charged, in the terms a PB proof needs.
#[derive(Clone, Debug)]
pub struct PaidMinedCore {
    /// Constraint id of the originating hard clause (see `MinedCore::hard_row`).
    pub hard_row: u64,
    /// The weight actually charged, measured as the lower bound's increase.
    pub w_min: u64,
    /// Core members as DIMACS literals. For a unit soft the selector IS the
    /// soft's own literal, so no translation is needed.
    pub members: Vec<i32>,
}

/// A core returned by a SAT CALL that the engine charged, in the terms a PB
/// proof needs.
///
/// Distinct from [`PaidMinedCore`] in exactly one way that matters to a
/// certificate: a mined core IS an input hard clause, so its PB derivation is
/// pure `pol` over input rows. This one is a REFUTATION — the solver needed
/// search to establish it — so the emitter has to justify it as a separate
/// derivation step and must first convince itself the step is replayable. That
/// check lives in `ay::maxsat_proof`, not here; this struct only reports what
/// the engine did.
///
/// Only cores over UNIT-soft selectors are recorded. A core containing a
/// totalizer / sum / AM1-disjunction selector names variables that exist
/// nowhere in the emitted OPB, so it cannot be stated at all, let alone
/// checked.
#[derive(Clone, Debug)]
pub struct PaidSatCore {
    /// The weight actually charged, measured as the lower bound's increase.
    pub w_min: u64,
    /// Core members as DIMACS literals. For a unit soft the selector IS the
    /// soft's own literal, so no translation is needed.
    pub members: Vec<i32>,
}

/// Cap on recorded SAT-derived cores. Bounds the evidence buffer on instances
/// that extract hundreds of thousands of cores; the certificate simply omits
/// the overflow, which only weakens the bound.
const PAID_SAT_CORE_CAP: usize = 4096;

/// OLL engine state over one persistent incremental SAT solver.
pub(crate) struct OllEngine {
    sat: SatSolver,
    /// Next fresh raw variable id (variable ids are used raw; id 0 unused).
    next_var: u32,
    /// #core-mine: cores found by scanning hard clauses at install time (see
    /// `mine_any_arity_cores`). Each entry is a set of UNIT-soft selectors that
    /// a hard clause forbids from all being true, i.e. a ready-made UNSAT core.
    mined_cores: Vec<MinedCore>,
    /// #core-mine: mined cores this run actually PAID, as proof evidence.
    ///
    /// Recorded for certificate emission only. Nothing in the engine reads this
    /// back — see the write-only rule in `ay::maxsat_proof`.
    paid_mined_cores: Vec<PaidMinedCore>,
    /// Cores returned by SAT CALLS that this run charged, as proof evidence.
    ///
    /// Same write-only rule as `paid_mined_cores`: recorded for certificate
    /// emission only, never read back by the engine. Kept in a separate vector
    /// because the two need DIFFERENT proof steps (input-row `pol` versus a
    /// `rup` the emitter must first verify for itself).
    paid_sat_cores: Vec<PaidSatCore>,
    /// #core-mine: selectors already charged by a paid mined core. Persistent
    /// across strata so disjointness holds over the WHOLE run, not per level.
    mined_used: HashSet<Literal>,
    /// Original soft clause literals for model-cost evaluation.
    softs: ClauseStore,
    /// Weights parallel to `softs`.
    soft_weights: Vec<Weight>,
    /// Selector literal per soft, parallel to `softs` (diagnostics).
    soft_selectors: Vec<Literal>,
    /// Cost every model necessarily pays, discovered during preprocessing
    /// (empty softs, complementary unit pairs).
    preproc_cost: Weight,
    /// Active selectors and their residual weights.
    active: HashMap<Literal, Weight>,
    /// Not-yet-activated selectors (stratification pool), weight descending.
    pool: Vec<(Literal, Weight)>,
    /// Current stratification level (#climit-discipline): each SAT call
    /// assumes only selectors with residual weight >= level, so every core
    /// found at this level pays at least `level` into `lb`. Starts at
    /// `Weight::MAX` (= everything filtered) until solve() computes the
    /// first level; 1 is terminal (nothing filtered).
    level: Weight,
    /// Sum selector metadata for totalizer bound extension.
    sums: HashMap<Literal, SumRef>,
    totalizers: Vec<TotNode>,
    /// Creation weight per totalizer, parallel to `totalizers`: the w_min of
    /// the creating core (band_min / class weight for set totalizers). Every
    /// not-yet-opened bound of the totalizer accounts for exactly this much
    /// potential cost per excess violation (see `residual_mass_bound`).
    tot_base_w: Vec<Weight>,
    /// Highest opened bound per totalizer, parallel to `totalizers`.
    tot_top_bound: Vec<usize>,
    /// #tot-eqs: remaining budget of reverse-direction clauses this instance
    /// may emit (see `TOT_EQ_CLAUSE_BUDGET_FACTOR`). Zero when the lever is
    /// gated off, which makes every `force_true` call a no-op.
    tot_eq_budget: i64,
    /// Certified lower bound on the optimum.
    lb: Weight,
    /// Cost of the incumbent model (u64::MAX when none).
    ub: Weight,
    /// When `ub` last improved (#ub-stale-descent). Instances whose optimum
    /// lies strictly below the frozen incumbent can NEVER prove optimality by
    /// lb progress alone (lb cannot exceed the optimum), so a stale ub with a
    /// small gap is the true model-improvement signal — lb-stall gates miss
    /// it when cores keep paying steadily (protein_ins: lb +1.3/s, ub frozen
    /// from t≈8s, optimum 15 below ub).
    ub_last_improved: Instant,
    best_model: Option<Vec<bool>>,
    stats: MaxSatStats,
    /// #minimize dry-pass damper: consecutive minimize passes in which every
    /// probe returned Unknown (see MINIMIZE_DRY_PASS_LIMIT).
    minimize_dry_passes: u32,
    /// #minimize: passes skipped by the damper, drives MINIMIZE_RETRY_STRIDE.
    minimize_skips: u64,
    tuning: OllTuning,
    /// Cached descent encoding, built once and reused across time slices.
    descent: Option<DescentEnc>,
    /// True when no descent encoding can EVER be available on this instance
    /// (every residual soft is hardened, or `ub == preproc_cost`). Sticky, and
    /// deliberately NOT set by the size-budget declines — see
    /// `descent_size_declined`.
    descent_unavailable: bool,
    /// #cold-core-descent D6: `(hardened_sels.len(), ub)` at the last SIZE
    /// decline in [`OllEngine::select_descent_enc`].
    ///
    /// The size budgets there are STATE-DEPENDENT: the residual soft set
    /// shrinks as softs harden and the cap `ub - preproc_cost` falls as the
    /// incumbent improves, so an encoding that is too large at t=25s can fit
    /// at t=200s. Poisoning the sticky `descent_unavailable` on those declines
    /// made an EARLY entry permanently forfeit the descent — and the whole
    /// point of the rate arm is to enter EARLIER, i.e. exactly when the
    /// encoding is at its largest. Recording the size signature instead lets
    /// the engine re-try, but only once one of its two monotone components has
    /// strictly improved (`hardened_sels` only grows, `ub` only falls), so a
    /// declining instance still short-circuits the gate for free rather than
    /// re-running `flush_pending` every stalling iteration.
    descent_size_declined: Option<(usize, Weight)>,
    /// #descent-residual: LATCHED fail-safe. Set only when
    /// `descent_residual_cap` catches `lb > ub` — an arithmetic impossibility
    /// that means the residual accounting is inconsistent. Once set, no residual
    /// cut is ever built or tightened again and the descent runs on the exact
    /// original-objective encoding alone.
    residual_exhausted: bool,
    /// #descent-residual: the newest redundant cut over the residual objective,
    /// asserted alongside the exact descent encoding. See [`ResidualBound`].
    /// Older cuts stay in the solver — each was independently sound when built
    /// and only ever excluded models costing at least the incumbent of the day.
    residual_bound: Option<ResidualBound>,
    /// Residual cuts built so far, so a long run cannot pile them up.
    residual_builds: u32,
    /// Wall-clock deadline for the whole solve, when the caller supplied one
    /// (`MaxSatSolver::set_deadline`). `None` = budget-blind, the historical
    /// behaviour: policies fall back to their fixed absolute constants.
    deadline: Option<Instant>,
    /// Activation literal guarding every descent clause: descents assume it
    /// true; OLL solves leave it free so the solver can switch the entire
    /// descent circuit off instead of dragging it through core extraction.
    descent_guard: Option<Literal>,
    /// Selectors hardened to true (their softs are satisfied in every
    /// remaining model): excluded from descent encodings, and descent
    /// uniformity is judged on the residual problem.
    hardened_sels: HashSet<Literal>,
    /// Whether abstraction sets were already formed (one-shot).
    abstraction_done: bool,
    /// Open lower-bound observation window: (window start, lb at start).
    /// Rolled every ~5s by the solve loop to judge core VALUE (lb rate)
    /// instead of core cost (#value-stall-gate).
    lb_window: Option<(Instant, Weight)>,
    /// lb gained over the last COMPLETED observation window. `None` until
    /// one window has elapsed, so the gate cannot fire in the first
    /// seconds no matter how slow the first SAT call is.
    lb_last_window_gain: Option<Weight>,
    /// #cold-core-descent: this instance's TRAILING inter-core arrival
    /// intervals in ms, most recent last, at most `COLD_CORE_WINDOW` entries.
    /// Fed ONLY by [`CoreOrigin::Search`] cores (see `note_search_core`).
    core_gaps_ms: Vec<u64>,
    /// Cached median of `core_gaps_ms` — one sort of <= `COLD_CORE_WINDOW`
    /// u64s per search core, so the search loop reads the rate baseline free.
    core_gap_median_ms: u64,
    /// #cold-core-descent: SEARCH time already banked toward the current
    /// drought, i.e. time since the last search-derived core MINUS the spans
    /// the clock was paused for. See [`OllEngine::core_drought`].
    core_drought: Duration,
    /// Start of the drought segment currently running; `None` while the
    /// drought clock is PAUSED (the engine is not looking for cores).
    core_drought_since: Option<Instant>,
    /// Count of [`CoreOrigin::Search`] cores, so the first one does not record
    /// a bogus "interval" measured from the start of the run.
    core_search_cores: u64,
    /// Original-selector membership of the first observed cores, recorded
    /// BEFORE weight splitting consumes them. Drives core-informed
    /// abstraction-set formation (CGSS-style co-occurrence clustering):
    /// selectors that appeared together in a core share structure, so a
    /// shared counting totalizer over them lets one future set-level core
    /// replace a family of concrete cores.
    core_history: Vec<Vec<Literal>>,
    /// #lp-boost: pure-original core store — each entry is a sorted,
    /// deduplicated set of soft indices whose selectors formed one UNSAT
    /// core. ONLY cores in which EVERY member is an original soft selector
    /// are stored: a core containing (or stripped of) sum selectors is a
    /// statement about OLL's residual totalizer bookkeeping, not about the
    /// original softs, and using it as a packing row would be unsound.
    /// This is deliberately NOT `core_history` (that filter keeps the
    /// original-selector residue of mixed cores — a strengthened row).
    lp_cores: Vec<Vec<u32>>,
    /// Dedup set over `lp_cores` rows (a duplicate row is sound but wastes
    /// an LP column and store capacity).
    lp_core_seen: HashSet<Vec<u32>>,
    /// Original selector -> soft index (inverse of `soft_selectors`).
    sel_to_soft: HashMap<Literal, u32>,
    /// #lp-boost: certified dual-packing lower bound (preproc-inclusive).
    /// NEVER merged into `lb` — see run_lp_boost / effective_lb.
    boost_lb: Weight,
    /// #lp-boost instance gate: >= 2 distinct nonzero INPUT weights. The
    /// lane must never activate on uniform (in particular unweighted)
    /// instances, whose behavior must be identical to the lane-free engine.
    lp_eligible: bool,
    /// #am1-overlap gate: enable the OVERLAPPING weighted clique cover (a
    /// selector reused across every entailed am1 until its weight is spent,
    /// with reiteration — CGSS2 try_am1s) over the plain disjoint cover, iff
    /// the instance has enough DISTINCT soft weights to be OLL-dust-prone.
    /// The dust pathology the overlap cures is CAUSED by many distinct
    /// weights (each per-w_min core split leaves a residual = weight
    /// difference that re-spawns), so the distinct-weight count is the direct
    /// predictor. Measured cleanly on the mse24 weighted families: the
    /// instances the overlap SPEEDS UP or FLIPS all have >= 32 distinct soft
    /// weights (auctions cat_reg/cat_paths 32-175, warehouses 1245-2482,
    /// css-refactoring 71-110), while the ones it REGRESSED — turning a
    /// sub-second solve into seconds, or a 58s solve into a timeout — all have
    /// <= 15 (auctions cat_sched 4-15, rna-alignment 2). The overlap's extra
    /// disjunction softs only pay off when the disjoint cover leaves real
    /// clique-cover lower bound on the table; below the gate the disjoint
    /// cover already suffices and the extra structure is pure overhead on
    /// AY's (vs CGSS2's) heavier per-SAT-call cost. Off => the am1 covers are
    /// bit-identical to the pre-overlap engine.
    am1_overlap: bool,
    /// #lp-boost: lane disabled (dry rounds exhausted or caps exceeded).
    lp_disabled: bool,
    /// Consecutive LP rounds without an effective-lb improvement.
    lp_dry_rounds: u32,
    /// cores_found at the last LP round (stride scheduling).
    lp_last_run_cores: u64,
    /// #wce (weight-aware core extraction, CGSS2 `cores_to_relax`):
    /// extracted multi-member cores whose relaxation — totalizer build +
    /// bound-2 selector registration — is deferred to the next flush
    /// point. Each entry stores the trimmed core's members and its w_min
    /// AT EXTRACTION TIME. The lb payment and the members' weight
    /// splitting happen immediately in process_core (the climit invariant
    /// "every core pays >= level" is untouched), so a pending entry
    /// represents ONLY outstanding counting structure: the cost identity
    /// carries one extra nonnegative term w_min·(v − 1) per entry, where
    /// v >= 1 is the entry's number of violated members (v >= 1 because
    /// the core was UNSAT when extracted), capped at w_min·(k − 1) — see
    /// residual_mass_bound and flush_pending.
    pending_relax: Vec<(Vec<Literal>, Weight)>,
    /// Union of `pending_relax` members: the solve loop flushes BEFORE
    /// processing a core that intersects it, keeping every batch a
    /// DISJOINT core family (see the overlap flush in solve()).
    pending_members: HashSet<Literal>,
}

/// Cached solution-improving descent encoding over all soft-violation
/// indicators. Sound independently of OLL's selector bookkeeping: violated
/// soft => indicator true, and any model extends to exact indicator values,
/// so forcing "violated weight < incumbent" never excludes a cheaper model.
enum DescentEnc {
    /// Uniform weight w over the residual (non-hardened) softs indexed by
    /// `soft_idx`: unweighted totalizer, bounds by violation count.
    Tot {
        tot: TotNode,
        w: Weight,
        soft_idx: Vec<usize>,
    },
    /// Near-uniform weights (#cluster-descent): count totalizer over the
    /// CLUSTER members only (weights >= band_min, >=75% of live weight
    /// mass). Sound bound: any model with cost < ub violates fewer than
    /// ceil((ub - preproc) / band_min) cluster members regardless of what
    /// the off-band "dust" softs do, so the count clauses never exclude a
    /// cheaper model and an UNSAT walk end is a genuine optimum. `last_k`
    /// detects a non-tightening round (dust-driven ub progress the count
    /// bound cannot cut), which swaps to the exact adder to avoid a
    /// livelock inside the one-way commit.
    ClusterTot {
        tot: TotNode,
        band_min: Weight,
        member_idx: Vec<usize>,
        last_k: usize,
    },
    /// Mixed weights, small instances: generalized totalizer outputs
    /// (sorted by sum) with the index of the first forced-false output.
    Gte {
        outs: Vec<(Weight, Literal)>,
        forbidden_from: usize,
    },
    /// Mixed weights, any size: adder-network sum bits and the current
    /// exclusive upper bound on violated weight.
    Adder {
        bits: Vec<Option<Literal>>,
        bound: Weight,
    },
    /// #dpw-descent: Dynamic Polynomial Watchdog (Paxian et al., SAT 2018)
    /// over mixed weights, taken ONLY where it is decisively smaller than the
    /// GTE this instance would otherwise get. See [`crate::dpw`].
    ///
    /// ⚠️ UNLIKE EVERY OTHER VARIANT THE BOUND IS NOT A CLAUSE. `k` is carried
    /// by the assumption vector rebuilt each round in `descend_slice`, because
    /// DPW's tare constant `T* = 2^{p-1} − 1 − (k mod 2^{p-1})` is NON-MONOTONE
    /// in `k` (k=115→T=4, k=112→T=7, k=111→T=0) and therefore cannot be
    /// committed one-way. `k_last` is bookkeeping for the trace only — the
    /// tighten arm adds nothing.
    ///
    /// CONSEQUENCE, and it is a real behaviour change: the GTE/adder bounds are
    /// unguarded HARD clauses that constrain OLL's own solves too; DPW's
    /// clauses are inert definitions outside the descent. The compensating
    /// requirement is absolute — these literals must reach the descent solve
    /// and NOWHERE else, or an extracted core will contain watchdog internals
    /// and corrupt OLL's cost identity (see the `debug_assert` in
    /// `process_core`).
    ///
    /// ⚠️ MEASURED COST OF THAT CHOICE — RSS. On
    /// `af-synthesis_wt-af-synthesis_stb_50_120_5` at 900s, sampled every 5s,
    /// same binary, `--maxsat-no-dpw` the only difference (2 runs each, both
    /// legs identical in outcome within a leg):
    ///
    /// | t | DPW RSS | GTE RSS |
    /// | --- | --- | --- |
    /// | 300s | 2.40 GB | 1.77 GB |
    /// | 600s | 5.00 GB | 3.56 GB |
    /// | ~700s | **>6.0 GB — killed** | 4.4 GB |
    /// | 900s | — | 5.59 GB peak, ran to completion |
    ///
    /// The encoding itself is 8.6x SMALLER here (13,743 clauses against the
    /// GTE's 118,460), so this is not the watchdog's own footprint — it is the
    /// learned-clause database growing faster because OLL's solves no longer
    /// see the `Σ < ub` bound the GTE leaves behind as hard units. Both legs
    /// end at the same incumbent (`o 115`) and neither proves it, so nothing
    /// was traded for it. That is the first thing to fix before this lever is
    /// worth an A/B — the identified remedy is hard-committing the top bound as
    /// `¬S_top[i]` units while keeping the NON-MONOTONE tare on assumptions
    /// (sound: a leftover unit at `K0 >= K_now` states a WEAKER bound), which
    /// needs its own brute-force net.
    Dpw { enc: DpwEnc, k_last: Option<Weight> },
}

/// #descent-residual: a redundant cut over the REFORMULATED residual objective,
/// asserted ALONGSIDE the descent's exact encoding rather than instead of it.
///
/// THE PROBLEM. Every `DescentEnc` above encodes the ORIGINAL objective capped
/// at `ub - preproc_cost` — the WHOLE objective — so on a proof-bound instance
/// the closing UNSAT call re-derives from scratch the bound OLL already paid
/// cores for. Traced on MSE24 exact-weighted at 300s with `--maxsat-debug`,
/// reading the two caps off the same descent entry:
///
/// | instance | original cap | residual cap (`ub - lb`) | discarded |
/// | --- | --- | --- | --- |
/// | `causal_Bands_6_277` | 100243 | 49502 (ub 100243, lb 50741) | 51% |
/// | `CSG_wt-CSGNaive140-140-6` | 53132 | 4245 (ub 57056, lb 52811) | 92% |
///
/// A longer probe of `causal n6` reports the same shape at the other end of the
/// scale — cap 877436991 against `lb` 711233689, 81% discarded, an adder 36 sum
/// bits wide where the residual mass needs ~28 — with 1.35 BILLION propagations
/// spent on 40k conflicts. (Its descent does not engage inside 300s, so that
/// one is not reproducible from a short run.)
///
/// THE FIX, AND WHY IT IS ADDITIVE. `Σ <= ub - lb - 1` is sound (see
/// [`OllEngine::descent_residual_cap`]) but it is a RELAXATION: the identity's
/// ladder term is slack, so a model can satisfy it and still cost more than the
/// incumbent. Measured, running it as the descent's ONLY encoding: on
/// `CSGNaive140-140-6` the first model under a cap of 3516 cost 57269 against
/// `ub` 56309; on `causal_Bands_6_277`, 217861 against `ub` 107215. A
/// relaxation therefore CANNOT drive the `ub` walk — it wastes a solve and
/// falls back. Conjoined with the exact encoding it costs nothing and pays
/// twice over: the exact bound keeps every SAT model strictly `ub`-improving,
/// while this cut is what the UNSAT proof actually needs.
///
/// It is REDUNDANT semantically (`Σ >= ub - lb` implies `cost >= ub`, which the
/// exact bound already forbids) and NOT redundant propagationally, which is the
/// entire point: the exact encodings are propagation-dead on these families
/// (`causal n6`: 1.35 BILLION propagations for 40k conflicts) because they are
/// stated over the original softs at a cap an order of magnitude too loose,
/// while this is stated over the very sum selectors OLL's cores are about, at a
/// cap that shrinks every time OLL pays for one.
///
/// ⚠️ RELAXATION, NOT AN EXACT COST ENCODING. A first attempt at this lever was
/// reverted for TEN wrong answers, and both bugs were the same mistake —
/// applying exact-encoding logic to it:
///   1. the build clamped `units` with `.min(sels.len())`, silently turning a
///      VACUOUS bound into a real one that excluded models where every selector
///      is falsified;
///   2. the tighten step derived the bound from the model just found. Valid for
///      an exact encoding ("find something strictly better than this"), invalid
///      here, because a model with the SAME `Σ` can be cheaper.
/// So: the bound comes only ever from `ub`, never from a model, and a bound the
/// encoding cannot represent is VACUOUS and must not be asserted. All three
/// encodings below are vacuous-safe BY CONSTRUCTION rather than by a clamp —
/// `residual_units` returns `None`, `gte_build`'s capped sums match no output,
/// and `assert_sum_le` returns early — and none of them may be "fixed" with a
/// `.min(width)`.
struct ResidualBound {
    enc: ResidualBoundEnc,
    /// The residual objective as encoded: `(selector, residual weight)`,
    /// selectors in POSITIVE form. Read by the debug identity check in
    /// `descend` only.
    terms: Vec<(Literal, Weight)>,
    /// `self.lb` when `terms` were read — the `lb` of `(★)`. MUST be the plain
    /// `lb`, never `effective_lb()`: the LP-boost `boost_lb` is an external lift
    /// that does not participate in the identity.
    lb_at_build: Weight,
    /// Tightest cap asserted so far, so a round that cannot tighten adds no
    /// clauses.
    last_cap: Weight,
}

/// Encoding behind a [`ResidualBound`], picked by the residual objective's own
/// weight shape: counting totalizer when its live weights are uniform (much the
/// cheapest — this is the case the retired `--maxsat-no-descent-residual`
/// prototype was restricted to), else the same `gte_build` / `adder_build` pair
/// the original objective already uses.
enum ResidualBoundEnc {
    /// Uniform residual weight `w`: unweighted totalizer over the violation
    /// indicators, bounding the COUNT at `last_k`.
    Tot {
        tot: TotNode,
        w: Weight,
        last_k: usize,
    },
    /// Generalized totalizer outputs (sorted by capped sum) with the index of
    /// the first forced-false output.
    Gte {
        outs: Vec<(Weight, Literal)>,
        forbidden_from: usize,
    },
    /// Adder-network sum bits, little-endian.
    Adder { bits: Vec<Option<Literal>> },
}

impl OllEngine {
    /// Create an engine from hard clauses and soft clauses (consumed).
    ///
    /// #maxsat-bmo-promote: promote dominating weight layers to hard clauses.
    ///
    /// Boundary rule: let `w_b` be the LOWEST distinct weight such that
    /// `w_b > Σ (weights of all softs with weight < w_b)`. Every soft with
    /// weight >= `w_b` ("the group") then individually outweighs everything
    /// below, so IF `hards ∪ group` is satisfiable (bounded SAT check, the
    /// witness is the proof), every optimal solution satisfies the whole
    /// group: violating one member costs >= w_b, strictly more than the
    /// witness pays (it violates at most all-below = mass < w_b). On
    /// success the group's clauses move to the hard store (cost 0 forever)
    /// and the rule re-applies to the remainder (metro-style multi-level
    /// hierarchies), up to 4 rounds. UNSAT/Unknown/oversized => promote
    /// nothing (fail-open, bit-identical run).
    fn bmo_promote_layers(
        num_vars: u32,
        hard: ClauseStore,
        soft: ClauseStore,
        soft_weights: Vec<Weight>,
    ) -> (ClauseStore, ClauseStore, Vec<Weight>) {
        let mut hard = hard;
        let mut soft = soft;
        let mut soft_weights = soft_weights;
        for _round in 0..4 {
            // Distinct weights ascending with cumulative below-mass.
            let mut weights: Vec<Weight> =
                soft_weights.iter().copied().filter(|&w| w > 0).collect();
            if weights.is_empty() {
                break;
            }
            weights.sort_unstable();
            let total_mass: Weight = weights.iter().fold(0u64, |a, &w| a.saturating_add(w));
            // Lowest boundary weight w_b with w_b > mass strictly below it,
            // requiring a non-empty below-part (otherwise this is just "is
            // the whole instance SAT", which the engine handles anyway).
            let mut below: Weight = 0;
            let mut boundary: Option<Weight> = None;
            let mut i = 0;
            while i < weights.len() {
                let w = weights[i];
                // advance over the equal-weight run, tracking run mass
                let mut run_mass: Weight = 0;
                while i < weights.len() && weights[i] == w {
                    run_mass = run_mass.saturating_add(w);
                    i += 1;
                }
                if below > 0 && w > below {
                    boundary = Some(w);
                    break;
                }
                below = below.saturating_add(run_mass);
            }
            let Some(w_b) = boundary else { break };
            debug_assert!(w_b <= total_mass);
            let group: Vec<usize> = (0..soft.len())
                .filter(|&i| soft_weights[i] >= w_b)
                .collect();
            if group.is_empty() || hard.len().saturating_add(group.len()) > BMO_MAX_CHECK_CLAUSES {
                break;
            }
            // Bounded joint-satisfiability check on a throwaway solver.
            let mut probe = SatSolver::new(num_vars as usize);
            for cl in hard.iter() {
                probe.add_clause(cl.to_vec());
            }
            for &i in &group {
                probe.add_clause(soft.get(i).to_vec());
            }
            probe.set_conflict_budget(Some(BMO_CHECK_CONFLICTS));
            let deadline = Instant::now() + BMO_CHECK_WALL;
            let stop = || Instant::now() >= deadline;
            let sat_ok = matches!(
                probe
                    .solve_with_assumptions_interruptible(&[], &stop)
                    .into_inner(),
                AssumeResult::Sat(_)
            );
            drop(probe);
            if !sat_ok {
                break; // fail-open: keep everything soft
            }
            if debug_trace() {
                eprintln!(
                    "c bmo-promote: {} softs at weight >= {} promoted to hard (below-mass {})",
                    group.len(),
                    w_b,
                    below,
                );
            }
            // Move group clauses to the hard store; rebuild the soft store.
            let group_set: Vec<bool> = {
                let mut v = vec![false; soft.len()];
                for &i in &group {
                    v[i] = true;
                }
                v
            };
            let mut new_soft = ClauseStore::new();
            let mut new_weights = Vec::with_capacity(soft.len() - group.len());
            for i in 0..soft.len() {
                if group_set[i] {
                    hard.push_from_iter(soft.get(i).iter().copied());
                } else {
                    new_soft.push_from_iter(soft.get(i).iter().copied());
                    new_weights.push(soft_weights[i]);
                }
            }
            soft = new_soft;
            soft_weights = new_weights;
        }
        (hard, soft, soft_weights)
    }

    /// `num_vars` is one past the maximum raw variable id used by the input.
    pub(crate) fn new(
        num_vars: u32,
        hard: ClauseStore,
        soft: ClauseStore,
        soft_weights: Vec<Weight>,
    ) -> Self {
        // #maxsat-bmo-promote (opt-in): Boolean Multilevel Optimization layer
        // promotion, the MaxPre/UWr transformation measured to matter most on
        // drmx (11 flips) and metro (7). If the softs at/above some weight w
        // carry individually more weight than the TOTAL mass of all softs
        // strictly below w, then any solution violating one of them costs
        // more than violating everything below — so IF the hard clauses plus
        // that whole top group are jointly satisfiable (one bounded SAT
        // check on a throwaway solver; witness = proof), every optimal
        // solution satisfies the entire group and it can be promoted to
        // PLAIN HARD clauses. Unlike selector-level hardening this feeds the
        // promoted structure to root-UP, install-time AM1 edge mining, and
        // the one-shot preprocessor (geffe128: 0 hards + 9044 softs becomes
        // 6481 hards + 1319 unit softs and solves in ~2s). Fail-open: an
        // UNSAT/Unknown check promotes nothing and the instance proceeds
        // bit-identically.
        let (hard, soft, soft_weights) = if maxsat_bmo_enabled() {
            Self::bmo_promote_layers(num_vars, hard, soft, soft_weights)
        } else {
            (hard, soft, soft_weights)
        };
        let mut sat = SatSolver::new(num_vars as usize);
        // #witness-oracle: `--solution-file` installs a known-good model, after
        // which ay-sat checks EVERY clause at insertion and every shrunken
        // clause, panicking on the first one the model falsifies. A sound
        // derivation can never falsify a true model, so a panic names the exact
        // clause that wrongly excluded it. This was already wired for ay-dpll
        // and the DIMACS CLI but NOT for the MaxSAT lane; wiring it here is what
        // proved the clause database stays sound during a wrong answer, which
        // localised the defect to unsat-core construction instead.
        //
        // NOTE: OLL uses RAW variable ids (DIMACS n -> id n, id 0 unused) while
        // `load_solution_file` maps DIMACS n -> index n-1, so a witness file
        // must be shifted by one or every report is a false positive.
        sat.maybe_load_solution_from_env();
        // (The interim #maxsat-domain-bcp-regression-workaround that disabled
        // domain BCP for +5 is now REMOVED: the underlying regression is fixed
        // directly — see #maxsat-domain-bcp-fix (propagate_domain_bcp's fused
        // out-of-domain skip) in propagation_bcp.rs. Domain BCP is re-enabled and
        // recovers the full regression. B9: the AY_AB_NO_DOMAIN_BCP escape
        // hatch is deleted with the rest of the never-set env surface.)
        // #maxsat-inproc-throttle: scale the incremental inprocessing re-fire
        // interval with clause count. Between OLL core-extraction solves the
        // SAT engine re-runs subsumption + vivification, each an O(arena) scan;
        // on the larger weighted/unweighted families (hard clauses plus
        // totalizers accumulated over hundreds of cores) the flat 500-conflict
        // cadence over-fires and inprocessing dominates runtime (~50% profiled
        // on causal-discovery vs ~7% for BCP), starving lower-bound proving.
        // Divisor 100 → interval clamp(500, num_clauses/100, 20_000); this
        // recovered +15 solved instances on the mse24 weighted track (281→296,
        // zero wrong) — e.g. the haplotyping-pedigrees family, causal-discovery,
        // frb, and CSG. Frequency-only, so it cannot change any optimum.
        sat.set_incremental_inprobe_divisor(Some(MAXSAT_INCR_INPROBE_DIVISOR));
        // NOTE (#cgss-focused-core-extraction, measured 2026-07-19): locking
        // the SAT core into focused-only mode + walk off (CGSS2's
        // stabilize=0/walk=0 core-extraction bias) A/B'd exactly NEUTRAL on
        // the weighted track (298 = 298, ±7 churn: abstraction/spot5 gained,
        // lisbon/timetabling lost). The alternating mode schedule earns its
        // keep on the model-finding (ub) side, so the default stands and the
        // focused-lock plumbing was not kept.
        // #maxsat-oneshot-preproc (MaxPre labeled-BVE edge): on large instances
        // where AY otherwise gates clause preprocessing off, run ONE BVE +
        // subsumption pass over the HARD formula before installing softs, with
        // every soft-clause variable frozen. BVE then eliminates only hard-only
        // variables, so the weighted optimum is preserved exactly (cost depends
        // only on soft vars; reconstruction over eliminated hard vars is
        // automatic per solve). This is the UWr/MaxPre win on rna-alignment
        // (73% hard-only vars) and the timetabling/causal families. It is
        // size-gated and has a default-on environment kill switch.
        // #maxsat-bce-preprocess (opt-in, --maxsat-bce): the BCE-first
        // one-shot config for the COMPETITION protocol (one instance per
        // machine ~ jobs=1). BCE reproduces MaxPre's hard-clause reduction
        // natively (metro 246k->112k, 54%) and flips metro/synplicate/causal,
        // but its pass cost is net-negative under bench jobs=10 contention
        // (measured 314-315 vs 321) — so it is OFF by default (the jobs=10-
        // optimal config stays 321) and ON for competition submissions where
        // the 8 frontier flips (metro x4 etc.) are free. When armed it also
        // lowers the one-shot gate to 100k so the mid-size LP-extracted
        // families (metro) qualify.
        let bce_preproc = maxsat_bce_preproc_enabled();
        let oneshot_gate = if bce_preproc {
            BCE_ONESHOT_MIN_HARDS
        } else {
            ONESHOT_PREPROC_MIN_HARDS
        };
        let oneshot_preproc = hard.len() >= oneshot_gate && maxsat_oneshot_preproc_enabled();

        if oneshot_preproc {
            // SOUNDNESS + survival: freeze every variable occurring in any soft
            // clause so BVE cannot eliminate it (an eliminated var can never be
            // referenced by install_softs' later add_clause). Keep them frozen
            // for the engine's lifetime — no melt.
            for clause in soft.iter() {
                for &lit in clause {
                    if (lit.variable().index() as u32) < num_vars {
                        sat.freeze(lit.variable());
                    }
                }
            }
            // Arm a cheap ONE-SHOT profile: keep BVE + subsumption, drop the
            // expensive/less-useful passes for a bounded pass.
            sat.set_preprocess_enabled(true);
            let mut profile = ay_sat::InprocessingFeatureProfile::default();
            profile.vivify = false;
            profile.probe = false;
            profile.sweep = false;
            profile.congruence = false;
            profile.sbva = false;
            profile.factor = false;
            profile.symmetry = false;
            profile.cce = false;
            profile.condition = false;
            profile.bce = bce_preproc; // #maxsat-bce-preprocess (opt-in)
            sat.set_inprocessing_profile(&profile);
        } else {
            // SAT-level preprocessing (BVE/probing) is uninterruptible inside
            // the first assumption solve and scales super-linearly; on multi-
            // million clause instances it can burn minutes before the first
            // conflict. Disable it above a size threshold - CDCL still runs.
            if hard.len() > 2_000_000 {
                sat.set_preprocess_enabled(false);
            }
            // #dense-hard-inproc: occurrence-list passes (BVE the worst)
            // rebuild OccList over every clause per incremental core-extraction
            // solve — a HashMap-rehash storm dominating protein (2.6M hards).
            let disable_occ_passes = hard.len() > 2_000_000;
            // On large formulas the incremental inprocessing passes (vivify,
            // subsumption, probing) can consume entire 100-150ms probe budgets
            // and dominate 60s runs. Keep only cheap maintenance above 500k.
            if hard.len() > 500_000 {
                let mut profile = ay_sat::InprocessingFeatureProfile::default();
                profile.vivify = false;
                profile.subsume = false;
                profile.probe = false;
                profile.transred = false;
                profile.sweep = false;
                profile.congruence = false;
                if disable_occ_passes {
                    profile.bve = false;
                    profile.bce = false;
                    profile.sbva = false;
                    profile.htr = false;
                    profile.gate = false;
                    profile.factor = false;
                    profile.decompose = false;
                    profile.hbr = false;
                    profile.condition = false;
                    profile.backbone = false;
                    profile.symmetry = false;
                    profile.cce = false;
                }
                sat.set_inprocessing_profile(&profile);
            }
        }
        // #hard-dedup: the SOFT install path normalises and merges identical
        // clauses (see the `merged` HashMap below), but the HARD path did not,
        // so duplicate hards were installed verbatim. That is not a corner
        // case: on `judgment-aggregation/ja-kemeny` every hard clause appears
        // exactly THREE times (175,560 -> 58,520 distinct; the 1.56M-hard
        // members collapse to 520,260). Duplicates cost watch-list scans on
        // every propagation, and they inflate `hard.len()`, which is what the
        // size-band gates above key on — so a formula could be pushed into a
        // band that strips vivify/subsume/probe/transred/sweep purely on
        // duplicated rows, and then nothing ever removes the duplicates because
        // subsumption was the thing that got disabled.
        //
        // Sound: adding a clause twice is logically identical to adding it
        // once. Literals are sorted for the key only; the clause installed
        // keeps its original order.
        // #core-mine: unit-soft literals, for the any-arity core scan below.
        // For a unit soft the SELECTOR IS THE LITERAL ITSELF (see the selector
        // construction later in this function), so a mined clause maps to a
        // core with no further translation.
        let unit_soft_lits: HashSet<Literal> = soft
            .iter()
            .zip(soft_weights.iter())
            .filter(|(lits, w)| lits.len() == 1 && **w > 0)
            .map(|(lits, _)| lits[0])
            .collect();
        let mut mined: Vec<MinedCore> = Vec::new();
        let mut binary: Vec<(Literal, Literal)> = Vec::new();
        let mut seen_hard: HashSet<Vec<Literal>> = HashSet::with_capacity(hard.len());
        let mut dup_hards = 0usize;
        for (hard_idx, clause) in hard.iter().enumerate() {
            let mut key = clause.to_vec();
            key.sort_unstable();
            key.dedup();
            if !seen_hard.insert(key) {
                dup_hards += 1;
                continue;
            }
            if clause.len() == 2 && clause[0].variable() != clause[1].variable() {
                binary.push((clause[0], clause[1]));
            }
            // #core-mine: AY's install-time lower bound was arity-locked to
            // binary clauses — `binary` above feeds `adapt_am1`, and nothing
            // else looks at a hard clause. On an all-ternary formula
            // (judgment-aggregation/ja-kemeny: 175,560 hards, every clause
            // length exactly 3, zero unit, zero binary) that means OLL starts
            // at lb = 0 and must buy the whole optimum one small core at a
            // time — measured 90.7% of its cores have min-weight 1, so it
            // needs 400+ UNSAT proofs over a 175k-clause formula and solves
            // 0 of 15 such instances.
            //
            // But a hard clause all of whose literals are the NEGATION of a
            // unit soft's literal is already an UNSAT core over those softs:
            // it asserts they cannot all be satisfied. Collect them here; they
            // are paid (greedily, disjointly) once the first stratum is
            // active. This is the any-arity generalisation of `adapt_am1`.
            if clause.len() >= 2
                && clause.len() <= CORE_MINE_MAX_ARITY
                && mined.len() < CORE_MINE_MAX_CORES
                && clause.iter().all(|l| unit_soft_lits.contains(&l.negated()))
            {
                let mut core: Vec<Literal> = clause.iter().map(|l| l.negated()).collect();
                core.sort_unstable();
                core.dedup();
                if core.len() == clause.len() {
                    // `hard_idx` counts hard clauses in file order INCLUDING the
                    // duplicates skipped above, which is the numbering an OPB
                    // restatement of the same file uses.
                    mined.push(MinedCore {
                        lits: core,
                        hard_row: hard_idx as u64 + 1,
                    });
                }
            }
            sat.add_clause(clause.to_vec());
        }
        if dup_hards > 0 && debug_trace() {
            eprintln!(
                "c hard-dedup: {} duplicate hard clauses dropped ({} -> {})",
                dup_hards,
                hard.len(),
                hard.len() - dup_hards
            );
        }
        if oneshot_preproc {
            // Run the single BVE+subsumption pass now (hards added, softs not
            // yet). Soundness note: this may report UNSAT (empty hards); the
            // first OLL solve will then return Unsatisfiable. Reconstruction
            // over eliminated hard vars runs automatically on every later solve.
            let clauses_before = sat.active_clause_count();
            let (bce_elim0, bce_pure0) = {
                let s = sat.bce_stats();
                (s.clauses_eliminated, s.pure_blocked)
            };
            let _ = sat.preprocess_once();
            let clauses_after = sat.active_clause_count();
            // #bce-risky-revert: split the reduction into the FREE (pure-arm)
            // and RISKY (tautological-resolvent) parts — see
            // `bce_risky_revert_enabled`. A mostly-risky reduction has eaten
            // live implications, which on these instances are the very mutex
            // edges the AM1 clique-cover lower bound is mined from.
            let (bce_elim1, bce_pure1) = {
                let s = sat.bce_stats();
                (s.clauses_eliminated, s.pure_blocked)
            };
            let bce_removed = bce_elim1.saturating_sub(bce_elim0);
            let bce_pure = bce_pure1.saturating_sub(bce_pure0);
            let risky = bce_removed.saturating_sub(bce_pure);
            let removed = clauses_before.saturating_sub(clauses_after) as u64;
            let free = removed.saturating_sub(risky);
            let mostly_risky = risky > free;
            if debug_trace() {
                eprintln!(
                    "c ONESHOT-PREPROC: clauses {clauses_before} -> {clauses_after} \
                     (bce removed {bce_removed}, pure {bce_pure}, risky {risky}, free {free}{})",
                    if mostly_risky { ", MOSTLY-RISKY" } else { "" }
                );
            }
            // #oneshot-dry-guard: on binary-dense formulas BVE finds nothing
            // (rna-alignment: 1002441 -> 1002441). Require a reduction larger
            // than floor(1% of the input) to commit to one-shot mode (all
            // inprocessing off).
            // A dry pass instead falls back to EXACTLY the size-banded
            // profile the non-oneshot path installs at this scale — no third
            // behavior.
            // #bce-risky-revert: a mostly-risky reduction has removed live
            // implications (the AM1 mutex edges). Throw the preprocessed engine
            // away and rebuild from the untouched hard clauses — `hard` is
            // still alive here (dropped below, after root-UP).
            let reverted = bce_risky_revert_enabled() && mostly_risky;
            if reverted {
                let mut fresh = SatSolver::new(num_vars as usize);
                fresh.set_incremental_inprobe_divisor(Some(MAXSAT_INCR_INPROBE_DIVISOR));
                for clause in hard.iter() {
                    fresh.add_clause(clause.to_vec());
                }
                install_non_oneshot_sat_config(&mut fresh, hard.len());
                sat = fresh;
                if debug_trace() {
                    eprintln!(
                        "c ONESHOT-PREPROC: REVERTED (risky {risky} > free {free}); \
                         rebuilt {} hard clauses without preprocessing",
                        hard.len()
                    );
                }
            }
            let oneshot_paid = clauses_after < clauses_before.saturating_sub(clauses_before / 100);
            if reverted {
                // Configuration already installed by the rebuild above; do not
                // overwrite it with the one-shot/dry profile.
            } else if oneshot_paid {
                // One-shot mode proper: the pass simplified the formula; stop
                // ALL further inprocessing (this is what makes it a ONE-shot
                // and dodges the per-solve rehash storm).
                let mut off = ay_sat::InprocessingFeatureProfile::default();
                off.bve = false;
                off.bce = false;
                off.subsume = false;
                off.vivify = false;
                off.probe = false;
                off.transred = false;
                off.sweep = false;
                off.congruence = false;
                off.sbva = false;
                off.htr = false;
                off.gate = false;
                off.factor = false;
                off.decompose = false;
                off.hbr = false;
                off.condition = false;
                off.backbone = false;
                off.symmetry = false;
                off.cce = false;
                sat.set_inprocessing_profile(&off);
                // preprocess_once already set preprocess_enabled=false.
            } else if let Some(off) = non_oneshot_inprocessing_profile(hard.len()) {
                // Dry pass: the one-shot removed nothing, so run on exactly the
                // configuration the NON-one-shot path would have used — via the
                // shared band helper, never a hand-copy of it. At or below 500k
                // hards the helper returns `None` and we install NOTHING, which
                // is what the non-one-shot path does at that size. See
                // `non_oneshot_inprocessing_profile` for the wrong answers the
                // previous hand-copied duplicate caused.
                sat.set_inprocessing_profile(&off);
            }
        }
        // #root-up-softs (MaxPre 'u' rule): root-UP consequences of the HARD
        // formula hold in every model, so softs can be normalized against
        // them exactly — a soft containing a root-true literal is satisfied
        // in every model (drop it, no selector, no cost), and root-false
        // literals can never satisfy a soft (strip them; empty => the weight
        // is unavoidable, pay preproc_cost). Strengthening multi-literal
        // softs to units also feeds adapt_am1 (it folds unit softs only).
        // Standalone bounded UP fixpoint here because ay-sat probing needs a
        // prior solve (probe contract) and install_softs runs pre-solve; the
        // fixpoint costs one O(total-lits) scan per round and exits the
        // moment a round derives nothing (formulas without unit hards pay
        // exactly one scan).
        let root_vals = Self::root_up_implied(&hard, num_vars as usize);
        // #tot-eqs: sized off the hard formula (see TOT_EQ_CLAUSE_BUDGET_FACTOR).
        let num_hard_clauses = hard.len();
        drop(hard);

        // #lp-boost instance gate, judged on the ORIGINAL input weights
        // (before install-time merging can turn duplicate unit softs of a
        // uniform instance into merged non-uniform weights): uniform-weight
        // instances — the unweighted track in particular — must behave
        // bit-identically to the lane-free engine.
        let distinct_weights = {
            let mut distinct: Vec<Weight> =
                soft_weights.iter().copied().filter(|&w| w > 0).collect();
            distinct.sort_unstable();
            distinct.dedup();
            distinct.len()
        };
        let lp_eligible = distinct_weights >= 2;
        // #am1-overlap gate (see the field doc): winners had >= 32 distinct
        // soft weights, regressors <= 15 — gate at 20 (clear of both, margin
        // above the loss band so a borderline instance stays on the safe,
        // bit-identical disjoint path).
        let am1_overlap = distinct_weights >= AM1_OVERLAP_MIN_DISTINCT_WEIGHTS;

        let mut engine = OllEngine {
            sat,
            next_var: num_vars,
            mined_cores: mined,
            paid_mined_cores: Vec::new(),
            paid_sat_cores: Vec::new(),
            mined_used: HashSet::new(),
            softs: ClauseStore::new(),
            soft_weights: Vec::new(),
            soft_selectors: Vec::new(),
            preproc_cost: 0,
            active: HashMap::new(),
            pool: Vec::new(),
            level: Weight::MAX,
            sums: HashMap::new(),
            totalizers: Vec::new(),
            tot_base_w: Vec::new(),
            tot_top_bound: Vec::new(),
            // #tot-eqs: WEIGHTED-ONLY by construction. A zero budget makes
            // every force_true call a no-op, so uniform-weight instances — the
            // whole UNWEIGHTED TRACK, where AY holds the crown at 341 vs
            // cgss2's 332 — run bit-identically to the lever-free engine and
            // need no re-measurement. Every measured gain is on a weighted
            // instance, so the gate costs nothing.
            tot_eq_budget: if lp_eligible {
                TOT_EQ_CLAUSE_BUDGET_FLOOR
                    .max(num_hard_clauses as i64 * TOT_EQ_CLAUSE_BUDGET_FACTOR)
            } else {
                0
            },
            lb: 0,
            ub: Weight::MAX,
            ub_last_improved: Instant::now(),
            best_model: None,
            stats: MaxSatStats::default(),
            minimize_dry_passes: 0,
            minimize_skips: 0,
            tuning: OllTuning::default(),
            descent: None,
            descent_unavailable: false,
            descent_size_declined: None,
            residual_exhausted: false,
            residual_bound: None,
            residual_builds: 0,
            deadline: None,
            descent_guard: None,
            hardened_sels: HashSet::new(),
            abstraction_done: false,
            lb_window: None,
            lb_last_window_gain: None,
            core_gaps_ms: Vec::new(),
            core_gap_median_ms: 0,
            core_drought: Duration::ZERO,
            core_drought_since: None,
            core_search_cores: 0,
            core_history: Vec::new(),
            lp_cores: Vec::new(),
            lp_core_seen: HashSet::new(),
            sel_to_soft: HashMap::new(),
            boost_lb: 0,
            lp_eligible,
            am1_overlap,
            lp_disabled: false,
            lp_dry_rounds: 0,
            lp_last_run_cores: 0,
            pending_relax: Vec::new(),
            pending_members: HashSet::new(),
        };
        engine.install_softs(&soft, &soft_weights, &binary, &root_vals);
        engine.lb = engine.preproc_cost;
        engine
    }

    /// Root-level unit-propagation fixpoint over the hard clauses, computed
    /// standalone (no SAT-engine probing: the probe contract requires a prior
    /// solve, and this runs pre-solve). Returns per-variable assignments:
    /// `1` = variable forced true in every model of the hards, `-1` = forced
    /// false, `0` = not determined by root UP. Rounds run only while a round
    /// derives a new unit, so unit-free formulas pay exactly one O(total-
    /// lits) scan; an early exit (bounded rounds) is sound — it only means
    /// fewer derived units, never a wrong one. A root conflict (all-false
    /// hard clause) returns the partial map — with unsatisfiable hards there
    /// are no models, the engine reports Unsatisfiable via its first solve,
    /// and any soft normalization is vacuously sound.
    fn root_up_implied(hard: &ClauseStore, num_vars: usize) -> Vec<i8> {
        let mut vals = vec![0i8; num_vars];
        let lit_val = |vals: &[i8], l: Literal| -> i8 {
            let v = vals[l.variable().index()];
            if l.is_positive() {
                v
            } else {
                -v
            }
        };
        const MAX_ROUNDS: usize = 32;
        for _ in 0..MAX_ROUNDS {
            let mut derived = false;
            'clauses: for clause in hard.iter() {
                let mut unassigned: Option<Literal> = None;
                for &l in clause {
                    match lit_val(&vals, l) {
                        1 => continue 'clauses, // satisfied at root
                        0 => {
                            if unassigned.is_some() {
                                continue 'clauses; // >= 2 free literals
                            }
                            unassigned = Some(l);
                        }
                        _ => {}
                    }
                }
                match unassigned {
                    Some(l) => {
                        // Unit under the root assignment: l is forced.
                        vals[l.variable().index()] = if l.is_positive() { 1 } else { -1 };
                        derived = true;
                    }
                    None => return vals, // root conflict: hards UNSAT
                }
            }
            if !derived {
                break;
            }
        }
        vals
    }

    /// Override engine thresholds (tests only).
    #[cfg(test)]
    pub(crate) fn set_tuning(&mut self, tuning: OllTuning) {
        self.tuning = tuning;
    }

    /// Preprocess and register soft clauses: merge duplicates, drop
    /// tautologies, count empty softs as unavoidable cost, resolve
    /// complementary unit pairs, detect intrinsic at-most-one groups, and
    /// create selectors.
    fn install_softs(
        &mut self,
        soft: &ClauseStore,
        soft_weights: &[Weight],
        binary: &[(Literal, Literal)],
        root_vals: &[i8],
    ) {
        let root_of = |l: Literal| -> i8 {
            let v = root_vals.get(l.variable().index()).copied().unwrap_or(0);
            if l.is_positive() {
                v
            } else {
                -v
            }
        };
        // Normalize: sort/dedup literals; merge identical clauses.
        let mut merged: HashMap<Vec<Literal>, Weight> = HashMap::new();
        for (lits, w) in soft.iter().zip(soft_weights) {
            if *w == 0 {
                continue;
            }
            let mut key = lits.to_vec();
            key.sort_unstable();
            key.dedup();
            // Tautology (x ∨ ¬x): always satisfied, no cost. (Checked before
            // the root filter: stripping a root-false side of a tautology
            // would be sound but wasteful — the whole clause is free.)
            if key.windows(2).any(|p| p[0].variable() == p[1].variable()) {
                continue;
            }
            // #root-up-softs (MaxPre 'u'): root-UP consequences of the hards
            // hold in EVERY model, so the per-model cost is preserved
            // exactly: a root-true literal satisfies the soft in every model
            // (free, no selector); root-false literals can never satisfy it
            // (strip). Softs strengthened to units feed the complementary-
            // pair resolution and adapt_am1 below.
            if key.iter().any(|&l| root_of(l) > 0) {
                continue;
            }
            key.retain(|&l| root_of(l) == 0);
            if key.is_empty() {
                // Empty soft clause: unconditionally violated.
                self.preproc_cost = self.preproc_cost.saturating_add(*w);
                continue;
            }
            let entry = merged.entry(key).or_insert(0);
            *entry = entry.saturating_add(*w);
        }

        // Complementary unit pair resolution: (l, w1) and (¬l, w2) always
        // cost min(w1, w2); only the difference remains soft.
        let unit_keys: Vec<Literal> = merged
            .keys()
            .filter(|k| k.len() == 1 && k[0].is_positive())
            .map(|k| k[0])
            .collect();
        for lit in unit_keys {
            let pos_key = vec![lit];
            let neg_key = vec![lit.negated()];
            let (Some(&wp), Some(&wn)) = (merged.get(&pos_key), merged.get(&neg_key)) else {
                continue;
            };
            let min = wp.min(wn);
            self.preproc_cost = self.preproc_cost.saturating_add(min);
            merged.remove(&pos_key);
            merged.remove(&neg_key);
            if wp > wn {
                merged.insert(pos_key, wp - wn);
            } else if wn > wp {
                merged.insert(neg_key, wn - wp);
            }
        }

        self.adapt_am1(&mut merged, binary);

        // Register remaining softs and create selectors.
        // Sorted for determinism (HashMap iteration order is not stable).
        let mut entries: Vec<(Vec<Literal>, Weight)> = merged.into_iter().collect();
        entries.sort_unstable();
        for (lits, w) in entries {
            self.softs.push_from_iter(lits.iter().copied());
            self.soft_weights.push(w);
            let selector = if lits.len() == 1 {
                lits[0]
            } else {
                let relax = self.fresh_lit();
                let mut clause = lits;
                clause.push(relax);
                self.sat.add_clause(clause);
                relax.negated()
            };
            // Freeze selector variables: later strata are not assumptions in
            // the first SAT call, and an unfrozen relaxation variable could
            // be eliminated or pure-literal-assigned by preprocessing before
            // it is ever assumed.
            self.sat.freeze(selector.variable());
            self.soft_selectors.push(selector);
            // #lp-boost: inverse selector map. Selectors are pairwise
            // distinct (merged softs are distinct clauses, complementary
            // unit pairs were resolved, relaxation literals are fresh).
            self.sel_to_soft
                .insert(selector, (self.soft_selectors.len() - 1) as u32);
            self.pool.push((selector, w));
        }
        self.pool
            .sort_unstable_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));

        // Bias search toward satisfying softs: force each selector's phase
        // to "satisfied" so intermediate models (exhaust probes, stratum
        // boundaries) carry good upper bounds instead of arbitrary ones.
        // Iterate ascending weight so on shared variables the highest
        // weight wins the phase.
        for &(sel, _) in self.pool.iter().rev() {
            self.sat.set_phase(sel.variable(), sel.is_positive());
        }
    }

    /// Intrinsic at-most-one detection (RC2 `adapt_am1`): find cliques of
    /// pairwise-incompatible unit soft literals (edges = binary hard clauses
    /// `(¬a ∨ ¬b)`). In a clique of size k at most one literal is true, so
    /// `w_min * (k-1)` is unavoidable cost; the exact remainder is one soft
    /// disjunction of the clique at `w_min` plus the residual unit weights.
    fn adapt_am1(
        &mut self,
        merged: &mut HashMap<Vec<Literal>, Weight>,
        binary: &[(Literal, Literal)],
    ) {
        let mut unit_w: HashMap<Literal, Weight> = merged
            .iter()
            .filter(|(k, _)| k.len() == 1)
            .map(|(k, &w)| (k[0], w))
            .collect();
        if unit_w.len() < 2 || binary.is_empty() {
            return;
        }

        let mut adj: HashMap<Literal, Vec<Literal>> = HashMap::new();
        let mut edges = 0usize;
        for &(x, y) in binary {
            let a = x.negated();
            let b = y.negated();
            if unit_w.contains_key(&a) && unit_w.contains_key(&b) {
                adj.entry(a).or_default().push(b);
                adj.entry(b).or_default().push(a);
                edges += 1;
                // Guard pathological densities; missing cliques only costs
                // lower-bound quality, never correctness.
                if edges > 4_000_000 {
                    break;
                }
            }
        }
        if adj.is_empty() {
            return;
        }
        let adj_sets: HashMap<Literal, HashSet<Literal>> = adj
            .iter()
            .map(|(l, ns)| (*l, ns.iter().copied().collect()))
            .collect();

        // OVERLAPPING iterated weighted clique cover (#am1-overlap, CGSS2
        // try_am1s port, cgss2.cpp:1258-1402). The former cover was DISJOINT
        // (the `used` set retired every clique member) and ran a SINGLE pass,
        // so on a dense weighted conflict graph — combinatorial auctions, where
        // one high-value bid conflicts with many pairwise-disjoint rivals in
        // different combinations — it paid only the disjoint-partition bound
        // (auctions_wt-cat_reg_60_150_0004: lb 107639) and left the rest to
        // ~850 dust cores at solve time. CGSS2 instead REUSES a selector across
        // every am1 it fits until its residual weight is spent, and REITERATES
        // over the survivors; on that instance that pays 148 am1s worth lb
        // 113291 (99.8% of the 113503 optimum) up front, so the core loop then
        // closes only the last ~212. Soundness is unchanged from the disjoint
        // peel: every am1 is a genuine direct-binary conflict clique, so
        // peeling one minimum-weight layer applies the same exact identity
        //   Σ_i d·[l_i violated] = d·(k−1) + d·[all violated]
        // (lb += d·(k−1) plus one disjunction soft at weight d for the residual
        // "all violated" term); reuse only decomposes a member's soft weight
        // across the distinct entailed am1s it belongs to. For a UNIFORM-weight
        // clique (one-hot domains: frb) the single peel exhausts every member,
        // so nothing is reused and the cover is bit-identical to the disjoint
        // one — the reuse changes only the non-uniform-weight case. Bounded by
        // AM1_PROBE_MAX_ITERS; the shared-neighbour candidate order (below) is
        // kept so a cross-edge cannot fragment a clean clique. Gated on the
        // instance's distinct-weight count (#am1-overlap): below the gate the
        // else-branch runs the original DISJOINT cover bit-identically.
        if self.am1_overlap {
            // #am1-maxcover: the overlapping cover's lb depends on the candidate
            // growth order. Score the landed shared-neighbour order and CGSS2's
            // ascending-degree order as pure plans (no engine mutation) and keep
            // the higher-lb one — a strictly better VALID bound (see
            // `am1_maxcover_enabled`). With the flag off, only the shared plan is
            // computed and applied, bit-identically to the pre-#am1-maxcover
            // cover. `plan_overlap_cover` performs the same sound per-layer peel
            // the inline loop used; applying its plan (add lb, register the
            // disjunction softs, replace the residual unit weights) reproduces
            // that loop's effect exactly for a given ordering.
            let unit_w0 = unit_w.clone();
            let shared_plan = Self::plan_overlap_cover(&unit_w0, &adj, &adj_sets, edges, true);
            let (lb_add, disjunctions, final_uw, groups) = if am1_maxcover_enabled() {
                let ascdeg_plan = Self::plan_overlap_cover(&unit_w0, &adj, &adj_sets, edges, false);
                if ascdeg_plan.0 > shared_plan.0 {
                    ascdeg_plan
                } else {
                    shared_plan
                }
            } else {
                shared_plan
            };
            self.preproc_cost = self.preproc_cost.saturating_add(lb_add);
            self.stats.am1_groups = self.stats.am1_groups.saturating_add(groups);
            for (disjunction, d) in disjunctions {
                let entry = merged.entry(disjunction).or_insert(0);
                *entry = entry.saturating_add(d);
            }
            unit_w = final_uw;
            // Reconcile each participating unit's `merged` entry with the residual
            // weight the peels left (the disjoint cover expressed this as the max-
            // weight survivor re-add). Only vertices with edges were ever touched;
            // fully-spent ones drop out, the rest keep their residual.
            for &lit in adj.keys() {
                if let Some(&w) = unit_w.get(&lit) {
                    if w == 0 {
                        merged.remove(&vec![lit]);
                    } else {
                        merged.insert(vec![lit], w);
                    }
                }
            }
        } else {
            // DISJOINT single-pass cover (pre-#am1-overlap behavior, used
            // below the distinct-weight gate): each unit is claimed by one
            // clique and full-peeled; the max-weight survivor's residual is
            // re-added as a unit. Bit-identical to the pre-overlap engine.
            let mut order: Vec<Literal> = adj.keys().copied().collect();
            order.sort_unstable_by_key(|l| (std::cmp::Reverse(adj[l].len()), *l));
            let mut used: HashSet<Literal> = HashSet::new();
            for &seed in &order {
                if used.contains(&seed) {
                    continue;
                }
                let mut clique = vec![seed];
                let mut cands: Vec<Literal> = adj[&seed]
                    .iter()
                    .copied()
                    .filter(|n| !used.contains(n) && unit_w.contains_key(n))
                    .collect();
                cands.sort_unstable();
                cands.dedup();
                if edges <= 200_000 {
                    let seed_adj = &adj_sets[&seed];
                    let mut scored: Vec<(usize, Literal)> = cands
                        .iter()
                        .map(|&n| {
                            let shared = adj_sets
                                .get(&n)
                                .map_or(0, |s| s.intersection(seed_adj).count());
                            (shared, n)
                        })
                        .collect();
                    scored.sort_unstable_by_key(|&(shared, l)| (std::cmp::Reverse(shared), l));
                    cands = scored.into_iter().map(|(_, l)| l).collect();
                }
                for n in cands {
                    if n != seed
                        && clique
                            .iter()
                            .all(|m| adj_sets.get(&n).is_some_and(|s| s.contains(m)))
                    {
                        clique.push(n);
                    }
                }
                if clique.len() < 2 {
                    continue;
                }
                for &m in &clique {
                    used.insert(m);
                }
                let mut members: Vec<(Literal, Weight)> = clique
                    .iter()
                    .filter_map(|m| unit_w.get(m).map(|&w| (*m, w)))
                    .collect();
                members.sort_unstable_by_key(|&(l, w)| (w, l));
                for &(m, _) in &members {
                    merged.remove(&vec![m]);
                    unit_w.remove(&m);
                }
                while members.len() >= 2 {
                    let d = members[0].1;
                    self.preproc_cost = self
                        .preproc_cost
                        .saturating_add(d.saturating_mul(members.len() as Weight - 1));
                    let mut disjunction: Vec<Literal> = members.iter().map(|&(l, _)| l).collect();
                    disjunction.sort_unstable();
                    let entry = merged.entry(disjunction).or_insert(0);
                    *entry = entry.saturating_add(d);
                    for e in members.iter_mut() {
                        e.1 -= d;
                    }
                    members.retain(|&(_, w)| w > 0);
                }
                if let Some(&(m, w)) = members.first() {
                    let entry = merged.entry(vec![m]).or_insert(0);
                    *entry = entry.saturating_add(w);
                }
                self.stats.am1_groups = self.stats.am1_groups.saturating_add(1);
            }
        }
    }

    /// Pure overlapping weighted clique-cover PLAN (#am1-maxcover). Simulates the
    /// same sound per-layer peel as the landed overlap cover on a CLONE of the
    /// unit weights and returns `(lb_added, disjunction softs to register, final
    /// residual unit weights, #groups)` WITHOUT touching engine state, so two
    /// candidate orderings can be scored and the higher-lb plan applied.
    ///
    /// `shared` selects the candidate growth order used to extend each clique:
    /// `true` reproduces the landed shared-neighbour reorder (descending shared
    /// neighbours with the seed, guarded to sparse graphs — the pre-#am1-maxcover
    /// behaviour); `false` uses CGSS2's ascending-degree order (try_am1s
    /// am1s_order=1 / cmp_conns_increasing_n). Seed order is ascending degree in
    /// both. Every peel obeys the identity lb += d·(k−1) plus one disjunction
    /// soft (the clique) at weight d, so ANY returned lb is a valid lower bound
    /// regardless of ordering — max-of-both is therefore always sound.
    ///
    /// Applying a plan (add `lb_added` to preproc_cost, `merged.entry(disj) +=
    /// d` for each disjunction, overwrite the participating units with the final
    /// residuals) reproduces the inline cover's effect for that ordering exactly;
    /// with `shared = true` and the plan applied, the result is bit-identical to
    /// the pre-#am1-maxcover inline loop.
    fn plan_overlap_cover(
        unit_w0: &HashMap<Literal, Weight>,
        adj: &HashMap<Literal, Vec<Literal>>,
        adj_sets: &HashMap<Literal, HashSet<Literal>>,
        edges: usize,
        shared: bool,
    ) -> (
        Weight,
        Vec<(Vec<Literal>, Weight)>,
        HashMap<Literal, Weight>,
        u64,
    ) {
        let mut unit_w = unit_w0.clone();
        let mut lb_added: Weight = 0;
        let mut disjunctions: Vec<(Vec<Literal>, Weight)> = Vec::new();
        let mut groups: u64 = 0;
        let mut iters = 0u32;
        loop {
            iters += 1;
            let mut order: Vec<Literal> = adj
                .keys()
                .copied()
                .filter(|l| unit_w.get(l).is_some_and(|&w| w > 0))
                .collect();
            // Seed low-degree vertices first (CGSS2 am1s_order=1), id tiebreak.
            order.sort_unstable_by_key(|l| (adj[l].len(), *l));
            let mut progressed = false;
            for seed in order {
                if unit_w.get(&seed).is_none_or(|&w| w == 0) {
                    continue;
                }
                let mut cands: Vec<Literal> = adj[&seed]
                    .iter()
                    .copied()
                    .filter(|n| unit_w.get(n).is_some_and(|&w| w > 0))
                    .collect();
                cands.sort_unstable();
                cands.dedup();
                if edges <= 200_000 {
                    if shared {
                        // Prefer candidates sharing the most neighbours with the
                        // seed: in one-hot/domain encodings a low-degree cross-edge
                        // vertex entering first fragments the true clique. Guarded
                        // to sparse graphs where the intersection scan is cheap.
                        let seed_adj = &adj_sets[&seed];
                        let mut scored: Vec<(usize, Literal)> = cands
                            .iter()
                            .map(|&n| {
                                let sh = adj_sets
                                    .get(&n)
                                    .map_or(0, |s| s.intersection(seed_adj).count());
                                (sh, n)
                            })
                            .collect();
                        scored.sort_unstable_by_key(|&(sh, l)| (std::cmp::Reverse(sh), l));
                        cands = scored.into_iter().map(|(_, l)| l).collect();
                    } else {
                        // CGSS2 ascending-degree candidate order: grows tight
                        // cliques over the dense mutual-conflict graphs of
                        // combinatorial auctions where the shared reorder fragments.
                        cands.sort_unstable_by_key(|n| (adj[n].len(), *n));
                    }
                }
                let mut clique = vec![seed];
                for n in cands {
                    if n != seed
                        && clique
                            .iter()
                            .all(|m| adj_sets.get(&n).is_some_and(|s| s.contains(m)))
                    {
                        clique.push(n);
                    }
                }
                let members: Vec<(Literal, Weight)> = clique
                    .iter()
                    .filter_map(|m| unit_w.get(m).map(|&w| (*m, w)))
                    .filter(|&(_, w)| w > 0)
                    .collect();
                if members.len() < 2 {
                    continue;
                }
                // Peel one minimum-weight layer; reiteration handles the rest.
                let d = members
                    .iter()
                    .map(|&(_, w)| w)
                    .min()
                    .expect("members is non-empty");
                lb_added = lb_added.saturating_add(d.saturating_mul(members.len() as Weight - 1));
                let mut disjunction: Vec<Literal> = members.iter().map(|&(l, _)| l).collect();
                disjunction.sort_unstable();
                disjunctions.push((disjunction, d));
                for &(m, _) in &members {
                    if let Some(w) = unit_w.get_mut(&m) {
                        *w -= d.min(*w);
                    }
                }
                groups += 1;
                progressed = true;
            }
            if !progressed || iters >= AM1_PROBE_MAX_ITERS {
                break;
            }
        }
        (lb_added, disjunctions, unit_w, groups)
    }

    /// #maxsat-am1-probe: at a post-solve stratification level change, mine
    /// at-most-one structure that install-time `adapt_am1` (direct binary
    /// edges only) cannot see — selectors that conflict only through
    /// unit-propagation chains, never a single binary hard clause (CGSS2
    /// calc_conns/try_am1s, cgss2.cpp:1134-1402, reimplemented natively over
    /// ay-sat's propagate-only probe). CSG-shaped instances have ~0.008%
    /// direct selector-selector edges but rich UP structure.
    ///
    /// For each level-qualified active ORIGINAL selector `s` (assumed
    /// SATISFIED), one propagate-only probe yields:
    ///  (1) `failed`: assuming `s` unit-propagates to a conflict, so the soft
    ///      is violated in EVERY model — routed through the identical
    ///      unit-core path (`process_core(&[s])`: pays lb += residual weight,
    ///      adds the hard unit ¬s);
    ///  (2) each other probed selector `s'` that UP forces FALSE: a SEMANTIC
    ///      AM1 edge, i.e. `¬s ∨ ¬s'` is entailed by the hard clauses, so at
    ///      most one of `s, s'` is satisfied in every model.
    ///
    /// The edges feed the SAME exact iterated-peeling accounting as
    /// `adapt_am1` (`relax_am1_clique_layer`): a clique of k selectors forces
    /// >= k−1 violations, so lb += d·(k−1) at each peel level d, plus one
    /// disjunction
    /// soft (s_1 ∨ … ∨ s_k) at weight d for the residual "all violated" term.
    ///
    /// SOUNDNESS. Every reported implication is UP-derived, hence a logical
    /// consequence of the hard clauses, so each edge `¬s_i ∨ ¬s_j` holds in
    /// every model — exactly the precondition adapt_am1 gets from binary hard
    /// clauses. The peel transformation is therefore identity-preserving
    /// (cost(A) unchanged for every AM1-respecting model), so lb stays a valid
    /// bound. climit invariant: every probed selector has residual >= level,
    /// so every peel payment d·(k−1) is >= level. WCE: the pass runs only with
    /// `pending_relax` already drained (flush (a) precedes it), and it queues
    /// no cores of its own.
    ///
    /// PHANTOM-VAR SAFETY. Phase A (probing) is strictly READ-ONLY — it
    /// collects `failed`/edges without mutating the solver — and runs only in
    /// the Sat arm after a real solve (watches attached, per the probe
    /// contract). All clause additions and lb motion happen in Phase B, after
    /// the last probe. Verified: the vals[]/trail invariant holds across this
    /// exact usage (solve → mid-stream hardening units → probe batch → solve).
    fn run_am1_probe(
        &mut self,
        started: Instant,
        am1_probe_spent: &mut Duration,
        should_stop: &dyn Fn() -> bool,
    ) {
        debug_assert!(
            self.pending_relax.is_empty(),
            "am1 probe pass must run with no unrelaxed cores (flush (a) first)",
        );
        // Failed-literal detection is SOUND at EVERY level, level 1 included:
        // a UP-refuted soft is false in every model, so hardening it is the
        // existing sound unit-core path. Uniform/unweighted instances (and the
        // ConsistentQueryAnswering family, ~13.8k active softs where CGSS2
        // pays ~97% of the lb by pure BCP failed-literal hardening) never
        // leave level 1, so the pass MUST run there for them. AM1 EDGE/clique
        // mining now also runs at level 1 (#am1-l1-stale-core, 2026-07-17):
        // the old level>1 gate was protecting against a stale-core double-
        // charge at the eager initial-probe call site — the in-flight `result`
        // core was processed after clique peels consumed its members'
        // residuals, and process_core's w_min filter_map silently skips absent
        // members and re-pays residual mass (reported 20 on privilege-
        // escalation-task-54, optimum 19). The caller's re-solve guard now
        // fires on ANY probe state motion (failed literals OR relaxed
        // cliques), closing that hazard; the peel accounting itself is level-
        // agnostic (d >= level holds trivially at level 1). Verified: task-54
        // solves to 19 OPTIMUM with edges on, keeping the lb 0->10 clique
        // gains. Edge collection stays bounded by AM1_PROBE_MAX_ACTIVE and
        // the hit-rate abort below. (#cqa-failed-probe)
        let collect_edges = true;
        // Time-share gate (~5-8%): keep the pass a minor share of the run.
        // Always allow the first pass (nothing spent yet) so tiny instances,
        // whose elapsed time rounds to ~0 at the level change, are not starved.
        if *am1_probe_spent > Duration::ZERO
            && am1_probe_spent.as_secs_f64()
                >= AM1_PROBE_TIME_SHARE * started.elapsed().as_secs_f64()
        {
            return;
        }
        let t0 = Instant::now();
        // Level-qualified active ORIGINAL selectors (exclude sum/set
        // selectors; those are counting structure, not softs to AM1-fold).
        // Probe ALL active original selectors (not just w >= level): a failed
        // literal is false in every model whatever its residual weight, and
        // this matches CGSS2's calc_conns (all active softs). Sum/set
        // selectors are counting structure, excluded.
        let mut probes: Vec<Literal> = self
            .active
            .iter()
            .filter(|(l, _)| !self.sums.contains_key(l))
            .map(|(&l, _)| l)
            .collect();
        probes.sort_unstable(); // determinism (HashMap order is unstable)
        if probes.is_empty() {
            *am1_probe_spent += t0.elapsed();
            return;
        }
        // Failed-literal detection (Phase A below) runs UNCAPPED — each probe
        // is a cheap decide+BCP (CGSS2 does ~13.6k in ~0.05s). Only the
        // expensive EDGE collection + clique cover is capped: over the cap we
        // skip edges entirely and keep just the failed sweep. On the CQA family
        // nearly all probes are FAILED (not edges), so `adj` stays tiny
        // regardless.
        let collect_edges = collect_edges && probes.len() <= AM1_PROBE_MAX_ACTIVE;
        self.stats.am1_probe_passes = self.stats.am1_probe_passes.saturating_add(1);
        let probe_set: HashSet<Literal> = probes.iter().copied().collect();

        // Phase A (READ-ONLY): probe each selector; collect failed literals and
        // symmetric conflict edges. No clause additions / no lb changes here,
        // so every probe sees the same post-solve clause database and solver
        // state is never mutated mid-batch.
        let mut failed: Vec<Literal> = Vec::new();
        let mut adj: HashMap<Literal, HashSet<Literal>> = HashMap::new();
        // Failed-hit-rate early abort (#cqa-failed-probe): the uncapped level-1
        // sweep pays off ONLY on instances where UP-refuted softs are common
        // (ConsistentQueryAnswering: ~97% of probes fail). On large-active
        // instances where few probes fail (CircuitDebuggingProblems), the
        // sweep is pure overhead that delays real search — an unconditional
        // full-track leg showed it REGRESSING those (327 vs 330). So after a
        // small sample, abort a no-edge sweep unless the failed rate is high.
        // When edge collection is on (the active set is capped),
        // the pass is already size-bounded and worth completing for the AM1
        // edges.
        const HITRATE_SAMPLE: usize = 200;
        const HITRATE_MIN_PERMILLE: usize = 300; // 30% failed to continue
        for (i, &s) in probes.iter().enumerate() {
            if should_stop() {
                *am1_probe_spent += t0.elapsed();
                return;
            }
            if !collect_edges && i == HITRATE_SAMPLE && probes.len() > HITRATE_SAMPLE {
                let permille = failed.len().saturating_mul(1000) / HITRATE_SAMPLE;
                if permille < HITRATE_MIN_PERMILLE {
                    // Low failed rate: this instance won't benefit — stop the
                    // sweep and harden only what the sample already found.
                    break;
                }
            }
            let r = self.sat.probe_implications_false(s, &probes);
            if r.failed {
                failed.push(s);
                continue;
            }
            if collect_edges {
                for s2 in r.falsified {
                    if s2 != s && probe_set.contains(&s2) {
                        adj.entry(s).or_default().insert(s2);
                        adj.entry(s2).or_default().insert(s);
                    }
                }
            }
        }

        // Phase B: accounting. Failed literals first — the identical unit-core
        // path. A failed selector is violated in every model, so it cannot be
        // an AM1 member (which needs "can be the one satisfied"); drop it from
        // the conflict graph.
        let failed_set: HashSet<Literal> = failed.iter().copied().collect();
        for &s in &failed {
            // Active-membership can only change via our own process_core calls
            // here; each probed selector is distinct, so this always holds.
            if self.active.contains_key(&s) {
                self.stats.am1_probe_failed = self.stats.am1_probe_failed.saturating_add(1);
                let lb_pre = self.lb;
                // #cold-core-descent: BATCH — these failed selectors were all
                // decided by the one probe sweep above and are paid back-to-back
                // in microseconds, with no SAT call between them.
                self.process_core(&[s], CoreOrigin::Batch);
                self.record_sat_core(&[s], lb_pre);
            }
        }
        if !failed_set.is_empty() {
            for s in &failed_set {
                adj.remove(s);
            }
            for nbrs in adj.values_mut() {
                nbrs.retain(|n| !failed_set.contains(n));
            }
        }

        // OVERLAPPING iterated weighted clique cover (#am1-overlap, CGSS2
        // try_am1s port, cgss2.cpp:1258-1402). The former cover was DISJOINT
        // (a selector claimed by one clique could never join another) and ran
        // a SINGLE pass, so on a dense conflict graph — combinatorial auctions,
        // where one high-value bid conflicts with many pairwise-disjoint rivals
        // in different combinations — it paid only a fraction of the clique-
        // cover lower bound (auctions_wt-cat_reg_60_150_0004: 7 disjoint
        // cliques, lb 107639) and left the rest to ~850 dust cores. CGSS2
        // instead REUSES a selector across every am1 it fits until its residual
        // weight is spent and REITERATES over the surviving residuals; on the
        // same instance that pays 148 am1s worth lb 113291 (99.8% of the
        // 113503 optimum) in ~6 passes, so the core loop closes the last 212 in
        // ~34 cores. Soundness is unchanged from relax_am1_clique's per-layer
        // identity: every am1 is UP-entailed (symmetric edges in `adj`, valid
        // under any later clause addition), and reusing a selector merely
        // decomposes its soft weight across the distinct entailed am1s it
        // belongs to — each weight slice `d` pays lb += d·(k−1) with the same
        // cost-preserving disjunction selector. Bounded by AM1_PROBE_MAX_ITERS,
        // the outer time share, and should_stop; missing an am1 costs only lb.
        let groups_before = self.stats.am1_probe_groups;
        let mut iters = 0u32;
        if self.am1_overlap {
            loop {
                iters += 1;
                // Seed order: ascending degree, id tiebreak (CGSS2 am1s_order=1,
                // cmp_conns_increasing). Only selectors with residual weight and
                // a live edge can still seed an am1.
                let mut order: Vec<Literal> = adj
                    .keys()
                    .copied()
                    .filter(|l| self.active.get(l).is_some_and(|&w| w > 0))
                    .collect();
                order.sort_unstable_by_key(|l| (adj[l].len(), *l));
                let mut progressed = false;
                for seed in order {
                    if self.active.get(&seed).is_none_or(|&w| w == 0) {
                        continue;
                    }
                    let mut clique = vec![seed];
                    let mut cands: Vec<Literal> = adj[&seed]
                        .iter()
                        .copied()
                        .filter(|n| self.active.get(n).is_some_and(|&w| w > 0))
                        .collect();
                    cands.sort_unstable_by_key(|n| (adj[n].len(), *n));
                    for n in cands {
                        if clique.iter().all(|m| adj[&n].contains(m)) {
                            clique.push(n);
                        }
                    }
                    if clique.len() >= 2 {
                        self.relax_am1_clique_layer(&clique);
                        progressed = true;
                    }
                }
                if !progressed || iters >= AM1_PROBE_MAX_ITERS || should_stop() {
                    break;
                }
            }
        } else {
            // Disjoint single-pass cover (pre-#am1-overlap behavior): each
            // selector is claimed by the first clique that fits it. Kept for
            // instances below the distinct-weight gate, where the overlap's
            // extra disjunction softs cost more than the lb they buy.
            iters = 1;
            for clique in Self::greedy_clique_cover(&adj) {
                self.relax_am1_clique(&clique);
            }
        }
        if debug_trace() {
            eprintln!(
                "c am1-probe: probes={} failed={} edge_nodes={} groups={} iters={} lb={} ub={}",
                probes.len(),
                failed.len(),
                adj.len(),
                self.stats.am1_probe_groups - groups_before,
                iters,
                self.lb,
                self.ub,
            );
        }
        *am1_probe_spent += t0.elapsed();
    }

    /// Peel ONE minimum-weight layer of an entailed AM1 clique (#am1-overlap,
    /// CGSS2 relaxes exactly one layer per am1 found, then reiterates — the
    /// driver in run_am1_probe supplies the reiteration and the vertex reuse
    /// across cliques). `members` are the clique's still-active selectors with
    /// positive residual weight; fewer than two and nothing is done. `d` is
    /// their minimum residual weight: lb += d·(k−1), one disjunction soft over
    /// the members is emitted at weight `d`, and `d` is subtracted from each
    /// member (spent members leave `active`).
    ///
    /// Identity preservation (the entailed AM1 forces "at most one satisfied"):
    /// Δlb = d·(k−1); the plain-selector sum loses d·Σ_i[s_i falsified] and
    /// gains d·[all s_i falsified] from the new disjunction selector, and
    /// (k−1) − Σ_i[falsified] + [all falsified] = 0 for both feasible cases
    /// (exactly one satisfied → Σ=k−1, all-false term 0; none satisfied →
    /// Σ=k, all-false term 1). So cost(A) is unchanged for every model and lb
    /// stays valid, independently of which OTHER am1s a member also joins —
    /// reuse only decomposes the member's soft weight across disjoint slices.
    fn relax_am1_clique_layer(&mut self, clique: &[Literal]) {
        let members: Vec<(Literal, Weight)> = clique
            .iter()
            .filter_map(|&m| self.active.get(&m).map(|&w| (m, w)))
            .filter(|&(_, w)| w > 0)
            .collect();
        if members.len() < 2 {
            return;
        }
        let d = members
            .iter()
            .map(|&(_, w)| w)
            .min()
            .expect("members is non-empty");
        self.lb = self
            .lb
            .saturating_add(d.saturating_mul(members.len() as Weight - 1));
        let disjunction: Vec<Literal> = members.iter().map(|&(l, _)| l).collect();
        self.install_am1_disjunction(&disjunction, d);
        for &(m, _) in &members {
            if let Some(w) = self.active.get_mut(&m) {
                *w -= d.min(*w);
                if *w == 0 {
                    self.active.remove(&m);
                }
            }
        }
        self.stats.am1_probe_groups = self.stats.am1_probe_groups.saturating_add(1);
    }

    /// Greedy DISJOINT clique cover over a symmetric conflict graph (the
    /// pre-#am1-overlap probe cover, used below the distinct-weight gate).
    /// Vertices are consumed by the first clique that claims them; only
    /// cliques of size >= 2 are returned. Missing a clique costs lower-bound
    /// quality, never correctness.
    fn greedy_clique_cover(adj: &HashMap<Literal, HashSet<Literal>>) -> Vec<Vec<Literal>> {
        let mut order: Vec<Literal> = adj.keys().copied().collect();
        order.sort_unstable_by_key(|l| (std::cmp::Reverse(adj[l].len()), *l));
        let mut used: HashSet<Literal> = HashSet::new();
        let mut cliques: Vec<Vec<Literal>> = Vec::new();
        for &seed in &order {
            if used.contains(&seed) {
                continue;
            }
            let mut clique = vec![seed];
            let mut cands: Vec<Literal> = adj[&seed]
                .iter()
                .copied()
                .filter(|n| !used.contains(n))
                .collect();
            cands.sort_unstable_by_key(|n| {
                (std::cmp::Reverse(adj.get(n).map_or(0, |s| s.len())), *n)
            });
            for n in cands {
                if clique
                    .iter()
                    .all(|m| adj.get(&n).is_some_and(|s| s.contains(m)))
                {
                    clique.push(n);
                }
            }
            if clique.len() >= 2 {
                for &m in &clique {
                    used.insert(m);
                }
                cliques.push(clique);
            }
        }
        cliques
    }

    /// Exact iterated FULL-peel relaxation of one disjoint AM1 clique (the
    /// pre-#am1-overlap probe relaxation, used below the distinct-weight gate).
    /// Members sorted weight-ascending; while >= 2 remain, the minimum residual
    /// `d` pays lb += d·(members−1) and emits one disjunction soft at weight
    /// `d`, then `d` is subtracted from each (spent members leave). The
    /// maximum-weight member keeps its surviving residual in `active`. Same
    /// per-level identity as `relax_am1_clique_layer`, iterated over the whole
    /// clique in one call.
    fn relax_am1_clique(&mut self, clique: &[Literal]) {
        let mut members: Vec<(Literal, Weight)> = clique
            .iter()
            .filter_map(|&m| self.active.get(&m).map(|&w| (m, w)))
            .filter(|&(_, w)| w > 0)
            .collect();
        if members.len() < 2 {
            return;
        }
        members.sort_unstable_by_key(|&(l, w)| (w, l));
        self.stats.am1_probe_groups = self.stats.am1_probe_groups.saturating_add(1);
        while members.len() >= 2 {
            let d = members[0].1;
            self.lb = self
                .lb
                .saturating_add(d.saturating_mul(members.len() as Weight - 1));
            let disjunction: Vec<Literal> = members.iter().map(|&(l, _)| l).collect();
            self.install_am1_disjunction(&disjunction, d);
            for &(m, _) in &members {
                if let Some(w) = self.active.get_mut(&m) {
                    *w -= d.min(*w);
                    if *w == 0 {
                        self.active.remove(&m);
                    }
                }
            }
            for e in members.iter_mut() {
                e.1 -= d;
            }
            members.retain(|&(_, w)| w > 0);
        }
    }

    /// Register a disjunction soft `(l_1 ∨ … ∨ l_k)` at weight `w` as an
    /// internal OLL accounting selector: fresh relax `r`, hard clause
    /// `(l_1 ∨ … ∨ l_k ∨ r)`, selector `¬r` added to `active` at weight `w`.
    /// Mirrors the multi-literal soft encoding in `install_softs`, but is NOT
    /// pushed to `self.softs` (`model_cost` evaluates the ORIGINAL soft set;
    /// the AM1 transformation is cost-preserving, so double-listing would
    /// double-count) nor to `sel_to_soft` (a disjunction soft is not an
    /// original soft — cores containing it stay LP-unusable, the sound
    /// conservative choice, matching how totalizer/sum selectors are treated).
    fn install_am1_disjunction(&mut self, lits: &[Literal], w: Weight) {
        let relax = self.fresh_lit();
        let mut clause: Vec<Literal> = lits.to_vec();
        clause.push(relax);
        self.sat.add_clause(clause);
        let selector = relax.negated();
        self.sat.freeze(selector.variable());
        // Bias toward "satisfied": relax defaults false => selector true.
        self.sat
            .set_phase(selector.variable(), selector.is_positive());
        *self.active.entry(selector).or_insert(0) += w;
    }

    /// Shrink a core by re-solving with only the core as assumptions under a
    /// small budget; the re-derived core is often smaller. Reversing the
    /// order between rounds lets late assumptions fail first.
    fn trim_core(
        &mut self,
        mut core: Vec<Literal>,
        should_stop: &dyn Fn() -> bool,
    ) -> Vec<Literal> {
        const TRIM_BUDGET: Duration = Duration::from_millis(100);
        if core.len() <= 8 {
            return core;
        }
        for _ in 0..3 {
            if should_stop() {
                break;
            }
            core.reverse();
            let deadline = Instant::now() + TRIM_BUDGET;
            let stop = || should_stop() || Instant::now() >= deadline;
            self.stats.sat_calls = self.stats.sat_calls.saturating_add(1);
            match self
                .sat
                .solve_with_assumptions_interruptible(&core, &stop)
                .into_inner()
            {
                AssumeResult::Unsat(new_core, _)
                    if !new_core.is_empty() && new_core.len() < core.len() =>
                {
                    core = new_core;
                }
                _ => break,
            }
        }
        core
    }

    /// Deletion-based core minimization (#minimize; CGSS2 cgss2.cpp:857-972,
    /// reimplemented natively): probe each member `m` by re-solving with
    /// assumptions `core \ {m}` under a small wall-clock budget. UNSAT means
    /// the core stands without `m` — adopt the solver-returned core (a
    /// certified UNSAT subset of `core \ {m}`, often several members smaller
    /// at once; CGSS2's minimize=2) and restart the sweep on it. SAT proves
    /// `m` load-bearing permanently: for every later shrink `core'` of
    /// `core`, `core' \ {m}` is a subset of the satisfiable `core \ {m}` and
    /// assumption sets are anti-monotone (fewer assumptions can only stay
    /// satisfiable), so `m` is never retried. Unknown (budget) counts as
    /// keep.
    ///
    /// Members are probed weight-ASCENDING: process_core pays
    /// `w_min = min residual weight over members` into lb, so dropping the
    /// cheapest members first is where the payoff lives — `w_min` can only
    /// rise as cheap members leave. Soundness of the larger payment: any
    /// UNSAT subset of an assumption set is itself a valid core (every model
    /// falsifies at least one member), and process_core computes `w_min`
    /// fresh from the final membership.
    ///
    /// Gates mirror trim (len > 8, should_stop). Budgets follow CGSS2's
    /// two-level conflict scheme — a pass budget of MINIMIZE_CONFLICTS_ABS
    /// plus MINIMIZE_CONFLICTS_REL of the conflicts spent so far, split
    /// across the members with unused allowance carried forward — under
    /// wall-clock guards (MINIMIZE_PROBE_BUDGET per probe,
    /// MINIMIZE_CORE_BUDGET per core); the caller adds the global
    /// MINIMIZE_TIME_SHARE gate.
    fn minimize_core(
        &mut self,
        mut core: Vec<Literal>,
        should_stop: &dyn Fn() -> bool,
    ) -> Vec<Literal> {
        if core.len() <= 8 {
            return core;
        }
        // Dry-pass damper: when this formula's per-call setup swallows every
        // probe (all-Unknown passes), stop paying; retry sparsely so the
        // lane can recover once the residual problem gets cheap to probe.
        if self.minimize_dry_passes >= MINIMIZE_DRY_PASS_LIMIT {
            self.minimize_skips = self.minimize_skips.wrapping_add(1);
            if !self.minimize_skips.is_multiple_of(MINIMIZE_RETRY_STRIDE) {
                return core;
            }
        }
        let original_len = core.len();
        let core_deadline = Instant::now() + MINIMIZE_CORE_BUDGET;
        // CGSS2-shape conflict allowance: pass budget split per member,
        // leftovers carried to the next probe.
        let start_conflicts = self.sat.num_conflicts();
        let pass_budget = MINIMIZE_CONFLICTS_ABS
            .saturating_add((MINIMIZE_CONFLICTS_REL * start_conflicts as f64) as u64);
        let per_probe = (pass_budget / core.len() as u64).max(1);
        let mut available: u64 = 0;
        let (mut probes, mut sat_probes, mut unknown_probes) = (0u32, 0u32, 0u32);
        // Members proven (or assumed, on Unknown) load-bearing; skipped by
        // every later sweep.
        let mut kept: HashSet<Literal> = HashSet::new();
        'sweep: loop {
            let mut candidates: Vec<(Weight, Literal)> = core
                .iter()
                .filter(|l| !kept.contains(l))
                .map(|&l| (self.active.get(&l).copied().unwrap_or(0), l))
                .collect();
            if candidates.is_empty() {
                break;
            }
            candidates.sort_unstable_by(|a, b| a.0.cmp(&b.0).then(a.1.cmp(&b.1)));
            for &(_, m) in &candidates {
                if should_stop() || Instant::now() >= core_deadline {
                    break 'sweep;
                }
                let assumptions: Vec<Literal> = core.iter().copied().filter(|&l| l != m).collect();
                let probe_deadline = Instant::now() + MINIMIZE_PROBE_BUDGET;
                let stop = || should_stop() || Instant::now() >= probe_deadline;
                self.stats.sat_calls = self.stats.sat_calls.saturating_add(1);
                probes += 1;
                available = available.saturating_add(per_probe);
                let before = self.sat.num_conflicts();
                self.sat
                    .set_conflict_budget(Some(before.saturating_add(available)));
                let result = self
                    .sat
                    .solve_with_assumptions_interruptible(&assumptions, &stop)
                    .into_inner();
                let used = self.sat.num_conflicts().saturating_sub(before);
                available = available.saturating_sub(used);
                match result {
                    // Empty returned core = UNSAT independent of assumptions;
                    // leave that discovery to the main loop (mirrors trim).
                    // The < guard is the same defensive check trim makes:
                    // a returned core is a subset of core \ {m}, so it is
                    // always strictly smaller and the sweep terminates.
                    AssumeResult::Unsat(new_core, _)
                        if !new_core.is_empty() && new_core.len() < core.len() =>
                    {
                        self.stats.minimize_removed_literals = self
                            .stats
                            .minimize_removed_literals
                            .saturating_add((core.len() - new_core.len()) as u64);
                        core = new_core;
                        if core.len() <= 1 {
                            break 'sweep;
                        }
                        continue 'sweep;
                    }
                    AssumeResult::Sat(_) => {
                        sat_probes += 1;
                        kept.insert(m);
                    }
                    _ => {
                        unknown_probes += 1;
                        if used == 0 {
                            // The wall deadline fired before the FIRST
                            // conflict: per-call setup swallows the probe
                            // budget on this formula, so no probe in this
                            // pass can conclude — stop burning the cap.
                            break 'sweep;
                        }
                        kept.insert(m);
                    }
                }
            }
            break;
        }
        self.sat.set_conflict_budget(None);
        if core.len() < original_len {
            self.stats.cores_minimized = self.stats.cores_minimized.saturating_add(1);
        }
        // Classify the pass for the dry damper: information-free means every
        // probe ran into the budget wall (no SAT verdict, no shrink).
        if probes > 0 {
            if unknown_probes == probes && core.len() == original_len {
                self.minimize_dry_passes = self.minimize_dry_passes.saturating_add(1);
            } else {
                self.minimize_dry_passes = 0;
            }
        }
        if debug_trace() {
            eprintln!(
                "c minimize: core {} -> {} members (probes={probes} sat={sat_probes} unknown={unknown_probes})",
                original_len,
                core.len(),
            );
        }
        core
    }

    /// Allocate a fresh variable and return its positive literal.
    fn fresh_lit(&mut self) -> Literal {
        let var = self.sat.new_var();
        debug_assert_eq!(var.id(), self.next_var, "fresh var id out of sync");
        self.next_var = var.id() + 1;
        Literal::positive(var)
    }

    pub(crate) fn stats(&self) -> &MaxSatStats {
        &self.stats
    }

    /// Mined cores this run charged, for certificate emission.
    ///
    /// Write-only evidence (see `ay::maxsat_proof`): the engine never reads it
    /// back, and a caller may not derive a verdict from it.
    pub(crate) fn take_paid_mined_cores(&mut self) -> Vec<PaidMinedCore> {
        std::mem::take(&mut self.paid_mined_cores)
    }

    /// SAT-derived cores this run charged, for certificate emission.
    ///
    /// Write-only evidence (see `ay::maxsat_proof`): the engine never reads it
    /// back, and a caller may not derive a verdict from it.
    pub(crate) fn take_paid_sat_cores(&mut self) -> Vec<PaidSatCore> {
        std::mem::take(&mut self.paid_sat_cores)
    }

    /// Best (cost, model) found so far.
    pub(crate) fn best(&self) -> Option<(Weight, Vec<bool>)> {
        self.best_model.clone().map(|m| (self.ub, m))
    }

    /// Compute the true cost of a model against the original soft clauses,
    /// including unavoidable preprocessing-time cost.
    fn model_cost(&self, model: &[bool]) -> Weight {
        let mut cost: Weight = self.preproc_cost;
        for (lits, w) in self.softs.iter().zip(&self.soft_weights) {
            let satisfied = lits
                .iter()
                .any(|&lit| model.get(lit.variable().index()).copied() == Some(lit.is_positive()));
            if !satisfied {
                cost = cost.saturating_add(*w);
            }
        }
        cost
    }

    /// Weight thresholds for stratified activation, descending.
    /// Band abstraction (#band-abstraction): on rounded-similarity shapes
    /// (>=75% of soft weight mass within 10% of the modal weight, many
    /// distinct weights — the correlation-clustering signature), register
    /// ONE shared counting totalizer over the band members as an OLL sum at
    /// weight band_min, and leave each member's residual (w - band_min) as
    /// an individual selector. This is an EXACT decomposition of the cost —
    /// sum_violated w_i = band_min * count + sum residuals — not a
    /// relaxation, so all existing sum bookkeeping (cores, bound bumps,
    /// exhaustion) applies unchanged. Cores over the set raise lb in
    /// band_min-sized steps where per-selector OLL crawled in w_min dust
    /// steps. Runs on the pre-stratification pool at solve entry; returns
    /// the set's assumption selector for an immediate exhaustion pass.
    fn form_band_abstraction(&mut self) -> Option<Literal> {
        // DEFAULT OFF (2026-07-12): on correlation-clustering the band set
        // lifts lb +73% (1.03M vs 0.60M at 60s, exhaustion in 45k steps)
        // and the ClusterTot walk separately reaches exact-optimum
        // incumbents — but neither half nor both convert to solves: the
        // set-level probes hit the same SAT-hardness wall (~20 of the ~113
        // needed steps land). The family is engine-speed/MIP-lane bound
        // (UWr's SCIP crushes the ILP-shaped polytope in seconds).
        // Machinery stays test-exercised via force_cluster.
        if !self.tuning.force_cluster {
            return None;
        }
        let (min_members, min_distinct) = (4, 2);
        let mut mass_by_w: HashMap<Weight, Weight> = HashMap::new();
        let mut total_mass: Weight = 0;
        for &(_, w) in &self.pool {
            *mass_by_w.entry(w).or_insert(0) += w;
            total_mass = total_mass.saturating_add(w);
        }
        if mass_by_w.len() < min_distinct {
            return None;
        }
        let (&modal_w, _) = mass_by_w.iter().max_by_key(|(_, &m)| m)?;
        let band_min = modal_w.saturating_sub(modal_w / 10);
        let band_max = modal_w.saturating_add(modal_w / 10);
        if band_min == 0 {
            return None;
        }
        let members: Vec<usize> = (0..self.pool.len())
            .filter(|&i| {
                let w = self.pool[i].1;
                w >= band_min && w <= band_max
            })
            .collect();
        let band_mass: Weight = members
            .iter()
            .map(|&i| self.pool[i].1)
            .fold(0, |a, w| a.saturating_add(w));
        if members.len() < min_members || band_mass.saturating_mul(4) < total_mass.saturating_mul(3)
        {
            return None;
        }
        let indicators: Vec<Literal> = members.iter().map(|&i| self.pool[i].0.negated()).collect();
        let mut root = TotNode::build(&indicators);
        let next_var = &mut self.next_var;
        let mut fresh = |sat: &mut SatSolver| {
            let var = sat.new_var();
            *next_var = var.id() + 1;
            sat.set_phase(var, false);
            Literal::positive(var)
        };
        root.extend(1, &mut self.sat, &mut fresh, None);
        let sum_sel = root.outs[0].negated();
        self.sat.freeze(sum_sel.variable());
        // Members pay band_min into the set; residuals stay individual.
        for &i in &members {
            self.pool[i].1 -= band_min.min(self.pool[i].1);
        }
        self.pool.retain(|&(_, w)| w > 0);
        self.totalizers.push(root);
        self.tot_base_w.push(band_min);
        self.tot_top_bound.push(1);
        self.sums.insert(
            sum_sel,
            SumRef {
                tot: self.totalizers.len() - 1,
                bound: 1,
            },
        );
        self.pool.push((sum_sel, band_min));
        self.stats.abstraction_sets = self.stats.abstraction_sets.saturating_add(1);
        if debug_trace() {
            eprintln!(
                "c band-abstraction: {} members at band_min={} (modal {}, mass {}%)",
                members.len(),
                band_min,
                modal_w,
                band_mass.saturating_mul(100) / total_mass.max(1),
            );
        }
        Some(sum_sel)
    }

    /// Residual weights of pool-resident SUM selectors (normally empty: only
    /// the band abstraction parks a sum selector in the pool). Lets the
    /// level scheduler and the residual-mass bound resolve a totalizer
    /// bound's residual no matter where it currently lives.
    fn pool_sum_residuals(&self) -> HashMap<Literal, Weight> {
        self.pool
            .iter()
            .filter(|(sel, _)| self.sums.contains_key(sel))
            .map(|&(sel, w)| (sel, w))
            .collect()
    }

    /// Residual weight of the selector for `bound` of totalizer `tot`
    /// (0 = consumed or never assigned).
    fn bound_residual(
        &self,
        tot: usize,
        bound: usize,
        pool_sums: &HashMap<Literal, Weight>,
    ) -> Weight {
        let sel = self.totalizers[tot].outs[bound - 1].negated();
        self.active
            .get(&sel)
            .or_else(|| pool_sums.get(&sel))
            .copied()
            .unwrap_or(0)
    }

    /// Compute the next stratification level strictly below `self.level`
    /// (#climit-discipline, CGSS2-style `next_strat_level`), from the LIVE
    /// residual-weight histogram:
    ///
    /// - one entry per active/pool selector at its residual weight, plus
    /// - `size - top_bound` entries at the creation weight per totalizer
    ///   whose unopened tail is reachable below the current level (top
    ///   bound's residual and creation weight both below `self.level`; a
    ///   top bound at or above the level is assumed and satisfied before
    ///   the level ever advances, so its tail cannot be violated yet).
    ///
    /// Walking the distinct weights downward from the current level, the
    /// first level satisfying either rule is chosen:
    ///
    /// - BLO rule: `level > total residual mass strictly below it` — a
    ///   single soft at this level outweighs everything below (Boolean
    ///   lexicographic optimization boundary), or
    /// - stratification rule: `2 * count_below > levels_below * total_levels`
    ///   — the remaining population is broad relative to its level
    ///   structure, so batching it beats level-at-a-time descent.
    ///
    /// Falls through to the terminal level 1 when no level qualifies, when
    /// the walk reaches the last distinct weight, or when nothing lives
    /// below the current level. Both rules are heuristics: correctness
    /// depends only on the assumption filter and the level-1 terminal test
    /// in solve(), never on WHICH level is chosen.
    ///
    /// Deviation from the CGSS2 source (deliberate): CGSS2's `numc` /
    /// `levels_left` counters mix tail entries into the walk but not into
    /// their initialization; here the histogram is built once and every
    /// derived quantity (counts, masses, level counts) comes from it
    /// consistently.
    fn next_level(&self) -> Weight {
        if self.level <= 1 {
            return 1;
        }
        let mut counts: HashMap<Weight, u64> = HashMap::new();
        for &w in self.active.values() {
            if w > 0 {
                *counts.entry(w).or_insert(0) += 1;
            }
        }
        for &(_, w) in &self.pool {
            if w > 0 {
                *counts.entry(w).or_insert(0) += 1;
            }
        }
        let pool_sums = self.pool_sum_residuals();
        for tot in 0..self.totalizers.len() {
            let top = self.tot_top_bound[tot];
            let tail = self.totalizers[tot].size.saturating_sub(top);
            let w0 = self.tot_base_w[tot];
            if tail == 0 || w0 == 0 || w0 >= self.level {
                continue;
            }
            let top_resid = self.bound_residual(tot, top, &pool_sums);
            if top_resid == 0 || top_resid >= self.level {
                continue;
            }
            *counts.entry(w0).or_insert(0) += tail as u64;
        }

        let mut hist: Vec<(Weight, u64)> = counts.into_iter().collect();
        hist.sort_unstable_by_key(|&(w, _)| std::cmp::Reverse(w)); // weight descending
        let total_levels = hist.len() as u128;
        let start = hist.partition_point(|&(w, _)| w >= self.level);
        let mut numc: u128 = hist[start..].iter().map(|&(_, c)| c as u128).sum();
        let mut mass_below: u128 = hist[start..]
            .iter()
            .map(|&(w, c)| w as u128 * c as u128)
            .sum();
        let mut levels_left = (hist.len() - start) as u128;
        for &(w, c) in &hist[start..] {
            numc -= c as u128;
            mass_below -= w as u128 * c as u128;
            levels_left -= 1;
            if levels_left == 0 {
                // Selected the lowest distinct weight: nothing lives below
                // it, so level w filters nothing extra — go terminal.
                return 1;
            }
            if w as u128 > mass_below {
                return w; // BLO rule
            }
            if 2 * numc > levels_left * total_levels {
                return w; // stratification rule
            }
        }
        1
    }

    /// Move pool selectors with weight >= threshold into the active set.
    /// Already-active selectors need no motion: the per-call assumption
    /// filter in solve() re-judges every residual against the current
    /// level, so residuals requalify automatically as the level drops.
    /// #core-mine: pay install-time mined cores that are now fully active.
    ///
    /// Each mined entry is a set of unit-soft selectors that a hard clause
    /// forbids from ALL holding, so every model violates at least one of them.
    ///
    /// SOUNDNESS — the load-bearing precondition is ALL-MEMBERS-ACTIVE-AND-
    /// LEVEL-QUALIFIED, **not** disjointness.
    ///
    /// For a unit soft the selector IS the soft's literal (see the
    /// `lits.len() == 1` branch of selector construction), and every
    /// relaxation / sum / AM1-disjunction selector lives on a variable minted
    /// by `fresh_lit` at an id >= `num_vars`. A mined member is the negation of
    /// an ORIGINAL hard-clause literal, so a hit in `self.active` for it can
    /// only be a surviving unit soft's selector. With EVERY member present,
    /// `process_core`'s `w_min` filter_map degenerates to a true minimum and
    /// the split debits every member in full, so the peel is the exact OLL
    /// weight-splitting identity and `lb` cannot outrun the optimum.
    ///
    /// A core with a MISSING member must be DISCARDED, never shrunk: a
    /// not-all-true clause has NO valid proper subset — (¬s1∨¬s2∨¬s3) does not
    /// entail (¬s1∨¬s2) — so paying `w_min` over the survivors charges `lb` for
    /// weight the absent member no longer carries. This is NOT the AM1 case:
    /// `relax_am1_clique`'s neighbouring `filter_map` shrink is safe because
    /// every subset of an at-most-one set is still at-most-one. DO NOT copy
    /// that idiom here. Counterexample: hard (¬x1∨¬x2), softs (x1)=7 (x2)=2,
    /// optimum 2 — `adapt_am1` spends x2 to zero, and shrinking the mined core
    /// to {x1} pays lb = 7. That is the #stale-core wrong answer recorded
    /// above (privilege-escalation-task-54: reported 20, optimum 19).
    ///
    /// The `w >= self.level` half is not optional. Presence alone suffices at
    /// the solve-entry call, where `activate_stratum` has just built `active`
    /// from an empty map. It is NOT enough at the level-change call, where
    /// `active` still holds selectors whose residual an earlier peel drove
    /// below the NEW level; paying one queues a core whose relaxation mints a
    /// sum selector the assumption filter can never assume.
    ///
    /// `mined_used` is a BATCHING heuristic, not a safety property. Dropping it
    /// is also sound and pays strictly more lb (measured 381 -> 435 of the 504
    /// optimum on judgment-00049-00000405). Keep or drop it on MEASUREMENT.
    fn pay_mined_cores(&mut self) {
        if self.mined_cores.is_empty() {
            return;
        }
        let mined = std::mem::take(&mut self.mined_cores);
        let mut deferred: Vec<MinedCore> = Vec::new();
        let (mut paid, lb_before) = (0usize, self.lb);
        for mined_core in mined {
            let core = mined_core.lits.clone();
            if core.iter().any(|l| self.mined_used.contains(l)) {
                // Batching only (see above), NOT soundness: requeue rather
                // than drop so a later batch can still pay it.
                deferred.push(mined_core);
                continue;
            }
            // [SOUND-CRITICAL] every member must be a LIVE, LEVEL-QUALIFIED
            // UNIT-soft selector. Defer the core WHOLE on any failure; never
            // shrink it. The unit test is redundant today (fresh_lit ids
            // >= num_vars cannot alias an original literal) and is kept so a
            // future change to variable allocation cannot silently admit a
            // multi-literal soft's selector, for which "selector false" only
            // ALLOWS a violation rather than entailing one.
            let payable = core.iter().all(|l| {
                self.sel_to_soft
                    .get(l)
                    .is_some_and(|&i| self.softs.get(i as usize).len() == 1)
                    && self.active.get(l).is_some_and(|&w| w >= self.level)
            });
            if !payable {
                deferred.push(mined_core);
                continue;
            }
            for &l in &core {
                self.mined_used.insert(l);
            }
            let lb_pre = self.lb;
            // #cold-core-descent: BATCH — mined cores are replayed from a
            // pre-computed list, not discovered by this engine's search.
            let _ = self.process_core(&core, CoreOrigin::Batch);
            paid += 1;
            // Proof evidence, recorded AFTER the fact: the charge is the lower
            // bound's actual increase, so it cannot overstate what the engine
            // did even if `process_core` changes. Write-only — nothing in the
            // engine reads `paid_mined_cores` back.
            self.paid_mined_cores.push(PaidMinedCore {
                hard_row: mined_core.hard_row,
                w_min: self.lb.saturating_sub(lb_pre),
                // NOT `to_dimacs()`: that maps internal variable index `v` to
                // DIMACS `v + 1`, but OLL uses RAW ids where internal `n` IS
                // DIMACS `n` (id 0 unused). Getting this wrong has already cost
                // this project two false results; the certificate's fail-closed
                // membership check caught it a third time.
                members: core
                    .iter()
                    .map(|l| {
                        // `raw()` packs as `2 * var + sign`, so `raw() >> 1` is
                        // the variable id with no DIMACS shift applied.
                        let v = (l.raw() >> 1) as i32;
                        if l.is_positive() {
                            v
                        } else {
                            -v
                        }
                    })
                    .collect(),
            });
            // [SOUND-CRITICAL] F4 fail-safe. `ub` is the cost of a model this
            // engine actually found, so it is ACHIEVABLE; a lower bound above
            // an achievable cost is arithmetically impossible and means the
            // accounting over-paid. Stop mining immediately and surrender the
            // rest of the batch: an unsolved instance costs one solve, a wrong
            // `s OPTIMUM FOUND` is disqualifying.
            if self.ub != Weight::MAX && self.lb > self.ub {
                self.stats.core_mine_abandoned = self.stats.core_mine_abandoned.saturating_add(1);
                eprintln!(
                    "c CORE-MINE-ABANDONED: lb {} exceeded reached cost ub {} — \
                     mined-core accounting is inconsistent; disabling the pass",
                    self.lb, self.ub
                );
                self.mined_cores.clear();
                self.mined_used.clear();
                // The accounting that produced these is the thing we just
                // caught being wrong; do not certify from it. That verdict
                // covers the SAT-derived evidence too — the over-pay is in the
                // shared residual accounting, not in the mining pass alone.
                self.paid_mined_cores.clear();
                self.paid_sat_cores.clear();
                return;
            }
        }
        if debug_trace() && paid > 0 {
            eprintln!(
                "c core-mine: paid {paid} disjoint cores, lb {} -> {}, {} deferred",
                lb_before,
                self.lb,
                deferred.len()
            );
        }
        self.mined_cores = deferred;
    }

    /// Record a core that came out of a SAT CALL as certificate evidence.
    ///
    /// Call this IMMEDIATELY after the `process_core` that charged it, passing
    /// the lower bound as it stood BEFORE that call: the charge is measured as
    /// the bound's actual increase, so this cannot overstate what the engine
    /// did even if `process_core`'s arithmetic changes underneath it.
    ///
    /// Write-only — see the rule in `ay::maxsat_proof`. Nothing here may be
    /// read back by the engine, and this function must have no effect on the
    /// solve beyond its own bookkeeping.
    ///
    /// Two filters, both mandatory:
    ///
    /// * **charge > 0** — a core that moved nothing contributes nothing and
    ///   would only add a `0 *` term to the derivation.
    /// * **every member is a UNIT-soft selector** — for a unit soft the
    ///   selector IS the soft's own literal, which is the one case where the
    ///   core can be restated over the emitted OPB's variables. A totalizer /
    ///   sum / AM1-disjunction selector lives on a variable minted by
    ///   `fresh_lit` that appears NOWHERE in the OPB, so such a core is not
    ///   weak evidence, it is inexpressible. Skip it whole; never shrink it
    ///   to the expressible members (a not-all-true set has no valid proper
    ///   subset — the #stale-core wrong answer, oll.rs:3531).
    fn record_sat_core(&mut self, core: &[Literal], lb_before: Weight) {
        if self.paid_sat_cores.len() >= PAID_SAT_CORE_CAP || core.is_empty() {
            return;
        }
        let charge = self.lb.saturating_sub(lb_before);
        if charge == 0 {
            return;
        }
        let all_unit_soft = core.iter().all(|l| {
            self.sel_to_soft
                .get(l)
                .is_some_and(|&i| self.softs.get(i as usize).len() == 1)
        });
        if !all_unit_soft {
            return;
        }
        let mut members: Vec<i32> = core
            .iter()
            .map(|l| {
                // NOT `to_dimacs()`: that maps internal variable index `v` to
                // DIMACS `v + 1`, but OLL uses RAW ids where internal `n` IS
                // DIMACS `n` (id 0 unused). `raw()` packs as `2 * var + sign`,
                // so `raw() >> 1` is the variable id with no DIMACS shift.
                // Getting this wrong has already cost this project two false
                // results.
                let v = (l.raw() >> 1) as i32;
                if l.is_positive() {
                    v
                } else {
                    -v
                }
            })
            .collect();
        // A core is a SET of assumptions; a repeated member would be charged
        // twice by the emitter's accounting and would emit `+1 r +1 r >= 1`.
        members.sort_unstable();
        members.dedup();
        self.paid_sat_cores.push(PaidSatCore {
            w_min: charge,
            members,
        });
    }

    fn activate_stratum(&mut self, threshold: Weight) {
        // #cold-core-descent D4: a stratification level change legitimately
        // pauses core discovery — the previous stratum ran out of assumable
        // selectors and the new one has not been searched yet — and the rate
        // gate cannot tell that apart from discovery going cold. Without this
        // reset the arm can take the entry before the fresh stratum has had a
        // single chance to produce a core. This is the one chokepoint through
        // which every level activation passes, including the first.
        self.reset_core_drought();
        if debug_trace() {
            eprintln!(
                "c level: threshold={} pool={} active={} lb={} ub={}",
                threshold,
                self.pool.len(),
                self.active.len(),
                self.lb,
                self.ub
            );
        }
        let mut i = 0;
        while i < self.pool.len() {
            if self.pool[i].1 >= threshold {
                let (sel, w) = self.pool.swap_remove(i);
                *self.active.entry(sel).or_insert(0) += w;
            } else {
                i += 1;
            }
        }
    }

    /// Harden selectors whose violation can no longer beat the incumbent:
    /// if lb + weight > ub, any model violating the selector costs more
    /// than the best model already found.
    fn harden(&mut self) {
        if self.ub == Weight::MAX {
            return;
        }
        self.harden_above(self.ub - self.lb);
    }

    /// Harden every active/pool selector whose residual weight strictly
    /// exceeds `cap`. Callers must guarantee that any model falsifying such
    /// a selector is strictly worse than some model that survives the added
    /// unit clauses (see harden / harden_residual_mass).
    fn harden_above(&mut self, cap: Weight) {
        let mut harden_lits: Vec<Literal> = Vec::new();
        self.active.retain(|&sel, &mut w| {
            if w > cap {
                harden_lits.push(sel);
                false
            } else {
                true
            }
        });
        let mut i = 0;
        while i < self.pool.len() {
            if self.pool[i].1 > cap {
                harden_lits.push(self.pool.swap_remove(i).0);
            } else {
                i += 1;
            }
        }
        for sel in harden_lits {
            self.sat.add_clause(vec![sel]);
            self.hardened_sels.insert(sel);
            self.stats.hardened = self.stats.hardened.saturating_add(1);
        }
    }

    /// Residual-mass hardening (#climit-discipline; CGSS2 `try_hardening`'s
    /// second rule): at a satisfiable point, harden every selector whose
    /// residual weight strictly exceeds the total residual mass the just
    /// found model can still be paying. Called ONLY from the Sat arm of the
    /// main OLL loop — the argument below needs the witness model.
    ///
    /// SOUNDNESS. Let M be the model just found: it satisfies every
    /// non-suspended active selector with residual weight >= level. The
    /// engine's exact cost identity (maintained by process_core /
    /// bump_sum_bound; weights only ever MOVE between a selector and its
    /// totalizer successor, in equal w_min amounts, alongside each lb
    /// payment) is, for every model A of the current formula:
    ///
    ///   cost(A) = lb + Σ_{sel ∈ active ∪ pool} w_sel · [sel falsified]
    ///                + Σ_t Σ_{j=j0+1..n_t} (w0_t − W_{t,j}) · [v_t >= j]
    ///
    /// where v_t = number of violated inputs of totalizer t, j0 its first
    /// bound (2 for core totalizers, 1 for set/band totalizers), w0_t its
    /// creation weight, and W_{t,j} the total weight ever moved onto bound
    /// j's selector. Mass conservation on each totalizer's bound ladder
    /// gives w0_t − W_{t,j} = Σ_{i<j} w_{t,i} (the CURRENT residuals of the
    /// lower bounds) for opened j, and w0_t for unopened j. Grouping per
    /// level, totalizer t contributes  Σ_j u_j · [v_t >= j]  with
    /// u_j = Σ_{i<=j} w_{t,i} for opened and u_j = w0_t for unopened j.
    ///
    /// Evaluating at M: falsified plain selectors all carry weight < level
    /// (or are suspended); for a totalizer whose lowest assumed bound is
    /// j* (residual >= level, not suspended), M satisfies it, so
    /// v_t <= j* − 1 and t contributes at most Σ_{i<j*} w_i · (j* − i);
    /// with no assumed bound t contributes at most
    /// Σ_i w_i · (top − i + 1) + w0_t · (size − top). Summing gives the
    /// computable bound `ub2` with cost(M) <= lb + ub2. For a fresh
    /// suspended totalizer over a size-k core at weight w_min this is
    /// exactly w_min · (k − 1) — CGSS2's pending-core slack; the cumulative
    /// Σ_{i<=j} w_i coefficients (not just each bound's own residual) are
    /// REQUIRED here because AY opens bounds in w_min installments, unlike
    /// CGSS2 whose bounds always open at the full totalizer weight.
    ///
    /// Any model A falsifying a selector of residual weight w has, by the
    /// same identity (all terms nonnegative), cost(A) >= lb + w. If
    /// w > ub2 then cost(A) > lb + ub2 >= cost(M) >= opt, so A is strictly
    /// suboptimal and forcing the selector true preserves every optimal
    /// model. This also keeps the engine-wide invariant that hardening
    /// clauses only exclude models costing >= the incumbent ub (relied on
    /// by the lp-boost lane and the empty-core arm): ub <= cost(M) was
    /// just recorded, so excluded models cost > ub2 + lb >= ub.
    ///
    /// NOTE: because ub <= cost(M) <= lb + ub2 at every point where this
    /// rule is sound, the rule is subsumed by harden()'s `w > ub − lb`
    /// whenever the incumbent is current — it is kept as CGSS2 keeps it,
    /// as the hardening rule that needs no incumbent bookkeeping, and it
    /// guards any future configuration that skips model-cost extraction.
    fn harden_residual_mass(&mut self, suspended: &HashSet<Literal>) {
        let ub2 = self.residual_mass_bound(suspended);
        self.harden_above(ub2);
    }

    /// The computable `ub2` of harden_residual_mass: an upper bound on
    /// cost(M) − lb for any model M satisfying every non-suspended active
    /// selector with residual weight >= `self.level`.
    fn residual_mass_bound(&self, suspended: &HashSet<Literal>) -> Weight {
        let pool_sums = self.pool_sum_residuals();
        let mut ub2: Weight = 0;
        // Plain (non-sum) selectors: potentially falsified iff filtered
        // (weight below level), suspended (defensive: suspended holds only
        // sum selectors today), or pool-resident (all pool weights are
        // below the level after activation).
        for (sel, &w) in &self.active {
            if self.sums.contains_key(sel) {
                continue; // counted via its totalizer's ladder below
            }
            if w < self.level || suspended.contains(sel) {
                ub2 = ub2.saturating_add(w);
            }
        }
        for (sel, &w) in self.pool.iter().map(|(l, w)| (l, w)) {
            if !self.sums.contains_key(sel) {
                ub2 = ub2.saturating_add(w);
            }
        }
        // Totalizer bound ladders: (bound, residual, assumed) per totalizer.
        let mut ladders: Vec<Vec<(usize, Weight, bool)>> = vec![Vec::new(); self.totalizers.len()];
        for (&sel, &SumRef { tot, bound }) in &self.sums {
            let w = self
                .active
                .get(&sel)
                .or_else(|| pool_sums.get(&sel))
                .copied()
                .unwrap_or(0);
            if w == 0 {
                continue;
            }
            let assumed =
                w >= self.level && !suspended.contains(&sel) && self.active.contains_key(&sel);
            ladders[tot].push((bound, w, assumed));
        }
        for (tot, ladder) in ladders.iter_mut().enumerate() {
            ladder.sort_unstable_by_key(|&(bound, _, _)| bound);
            let cap = match ladder.iter().find(|&&(_, _, assumed)| assumed) {
                // M satisfies bound j*: at most j* − 1 violations, each
                // opened level i < j* charging at most u_i (cumulative
                // residuals), totalling Σ w_i · (j* − i).
                Some(&(j_star, _, _)) => ladder
                    .iter()
                    .take_while(|&&(b, _, _)| b < j_star)
                    .fold(0u64, |acc, &(b, w, _)| {
                        acc.saturating_add(w.saturating_mul((j_star - b) as Weight))
                    }),
                // No assumed bound: all size violations possible — every
                // opened level up to the top plus the unopened tail at the
                // creation weight.
                None => {
                    let top = self.tot_top_bound[tot];
                    let opened = ladder.iter().fold(0u64, |acc, &(b, w, _)| {
                        acc.saturating_add(w.saturating_mul((top + 1 - b) as Weight))
                    });
                    let tail = (self.totalizers[tot].size.saturating_sub(top)) as Weight;
                    opened.saturating_add(self.tot_base_w[tot].saturating_mul(tail))
                }
            };
            ub2 = ub2.saturating_add(cap);
        }
        // #wce: pending (queued, unrelaxed) cores. Their lb payment and
        // weight splitting already happened at extraction, so the cost
        // identity carries one extra nonnegative term per pending core
        // (members, w_min): w_min·(v − 1), where v >= 1 is its number of
        // violated members (v >= 1 because the core was UNSAT when
        // extracted). Nothing about M constrains v — the would-be bound-2
        // selector does not exist, so it is not assumed — hence the cap is
        // the full w_min·(k − 1): exactly the fresh-suspended-totalizer
        // slack (see the ladder arithmetic above) that flush_pending will
        // materialize for this core.
        for (members, w_min) in &self.pending_relax {
            ub2 = ub2
                .saturating_add(w_min.saturating_mul((members.len() as Weight).saturating_sub(1)));
        }
        ub2
    }

    /// Extend the totalizer behind a sum selector to its next bound and
    /// activate the new bound's selector with weight `w`. Returns the new
    /// bound selector, or `None` when the totalizer is saturated.
    fn bump_sum_bound(&mut self, sel: Literal, w: Weight) -> Option<Literal> {
        let &SumRef { tot, bound } = self.sums.get(&sel)?;
        let next_bound = bound + 1;
        if next_bound > self.totalizers[tot].size {
            // Totalizer exhausted: every input can be violated, fully paid.
            return None;
        }
        let next_var = &mut self.next_var;
        let mut fresh = |sat: &mut SatSolver| {
            let var = sat.new_var();
            *next_var = var.id() + 1;
            // Prefer "few violations": totalizer outputs default false.
            sat.set_phase(var, false);
            Literal::positive(var)
        };
        self.totalizers[tot].extend(next_bound, &mut self.sat, &mut fresh, None);
        self.tot_top_bound[tot] = self.tot_top_bound[tot].max(next_bound);
        let new_sel = self.totalizers[tot].outs[next_bound - 1].negated();
        self.sums.insert(
            new_sel,
            SumRef {
                tot,
                bound: next_bound,
            },
        );
        *self.active.entry(new_sel).or_insert(0) += w;
        Some(new_sel)
    }

    /// Process one UNSAT core of selectors: raise the lower bound, split
    /// weights, and extend the totalizers of sum members. Returns the sum
    /// selectors newly added to the active set (candidates for delayed
    /// assumption). #wce: a multi-member core's NEW totalizer is not built
    /// here — the core is queued on `pending_relax` for the next flush
    /// point (flush_pending); only the immediate accounting (lb payment,
    /// weight splitting, bound bumps of existing sums, unit-core hard
    /// clauses) happens at extraction time.
    ///
    /// `origin` feeds ONLY the #cold-core-descent rate gate and nothing else;
    /// it is a required parameter rather than an inferred flag so that a new
    /// call site cannot silently be counted as core-discovery progress (see
    /// [`CoreOrigin`]).
    fn process_core(&mut self, core: &[Literal], origin: CoreOrigin) -> Vec<Literal> {
        // #dpw-descent [SOUND-CRITICAL, debug builds]: DPW is the only descent
        // encoding whose literals are ASSUMED, and they are assumed at exactly
        // one site (`descend_slice`). If a tare variable or a watchdog output
        // ever reached a core-producing solve — OLL's own extraction, or the
        // minimisation probes — the extracted core would contain watchdog
        // internals and OLL's cost identity would be corrupted, which is a
        // wrong answer and not a lost solve. The memory note on this family's
        // soundness hunts is explicit that such bookkeeping bugs are
        // trajectory-dependent and will not reproduce under plain defaults, so
        // the invariant is asserted rather than argued.
        #[cfg(debug_assertions)]
        if let Some(DescentEnc::Dpw { enc, .. }) = self.descent.as_ref() {
            for &lit in core {
                debug_assert!(
                    !enc.owns(lit),
                    "DPW literal {lit:?} leaked into an UNSAT core: the watchdog's \
                     assumptions escaped `descend_slice`",
                );
            }
        }
        self.stats.cores_found = self.stats.cores_found.saturating_add(1);
        match origin {
            CoreOrigin::Search => self.note_search_core(Instant::now()),
            // Batch payments are lb progress but NOT search progress, so they
            // never enter the rate sample. They do restart the drought clock,
            // which is the conservative direction: it can only DELAY the rate
            // arm, never advance it.
            CoreOrigin::Batch => self.reset_core_drought(),
        }
        let mut new_sums = Vec::new();
        // Record original-selector membership BEFORE weight splitting
        // consumes members, for core-informed abstraction formation.
        const CORE_HISTORY_CAP: usize = 512;
        if self.core_history.len() < CORE_HISTORY_CAP && core.len() >= 2 {
            let originals: Vec<Literal> = core
                .iter()
                .copied()
                .filter(|sel| self.active.contains_key(sel) && !self.sums.contains_key(sel))
                .collect();
            if originals.len() >= 2 {
                self.core_history.push(originals);
            }
        }
        // #lp-boost: store the core as a packing row iff EVERY member is an
        // original soft selector (sum-selector cores are excluded for LP
        // soundness — see the lp_cores field docs).
        self.lp_capture_core(core);
        if debug_trace() {
            let w_min = core
                .iter()
                .filter_map(|sel| self.active.get(sel).copied())
                .min()
                .unwrap_or(0);
            eprintln!(
                "c core #{}: size={} w_min={} lb={} ub={} active={}",
                self.stats.cores_found,
                core.len(),
                w_min,
                self.lb,
                self.ub,
                self.active.len()
            );
        }

        // #stale-core diagnostic (2026-07-28): the `w_min` filter_map below
        // SILENTLY SKIPS core members that are no longer in `active`, yet
        // `lb += w_min` is paid regardless. Absent-because-hardened is sound —
        // a hardened soft is true in every model, so it cannot be the
        // falsified member. Absent because the member's residual was already
        // spent into a totalizer or an AM1 disjunction is NOT sound: a model
        // falsifying only that member pays nothing, so `lb` is over-paid. That
        // is the defect recorded at oll.rs:2570-2582 (reported 20 on
        // privilege-escalation-task-54, optimum 19), whose fix guarded one
        // call site rather than this computation.
        if debug_trace() {
            let (mut hardened, mut pooled) = (0usize, 0usize);
            let mut unaccounted: Vec<Literal> = Vec::new();
            for sel in core {
                if self.active.contains_key(sel) {
                    continue;
                }
                if self.hardened_sels.contains(sel) {
                    hardened += 1;
                } else if self.pool.iter().any(|(p, _)| p == sel) {
                    pooled += 1;
                } else {
                    unaccounted.push(*sel);
                }
            }
            if hardened + pooled + unaccounted.len() > 0 {
                eprintln!(
                    "c STALE-CORE #{}: absent={} hardened={} pooled={} UNACCOUNTED={} lb={} ub={} sels={:?}",
                    self.stats.cores_found,
                    hardened + pooled + unaccounted.len(),
                    hardened,
                    pooled,
                    unaccounted.len(),
                    self.lb,
                    self.ub,
                    unaccounted.iter().take(8).collect::<Vec<_>>()
                );
            }
        }

        let w_min = core
            .iter()
            .filter_map(|sel| self.active.get(sel).copied())
            .min()
            .unwrap_or(0);
        debug_assert!(w_min > 0, "core contains only zero-weight selectors");
        self.lb = self.lb.saturating_add(w_min);

        // Weight splitting: every member pays w_min; exhausted members leave
        // the assumption set.
        for sel in core {
            if let Some(w) = self.active.get_mut(sel) {
                *w -= w_min.min(*w);
                if *w == 0 {
                    self.active.remove(sel);
                }
            }
        }

        // Sum selectors that reappeared in a core: count one more violation
        // by unlocking the next totalizer bound. This must happen for unit
        // cores too, or violations beyond the current bound would go
        // unaccounted and a suboptimal model could be declared optimal.
        for &sel in core {
            if self.sums.contains_key(&sel) {
                new_sums.extend(self.bump_sum_bound(sel, w_min));
            }
        }

        if core.len() == 1 {
            // Unit core: the selector is falsified in every model of the
            // current formula; make it a hard fact for propagation.
            self.sat.add_clause(vec![core[0].negated()]);
            // #tot-eqs: when that selector is a sum selector `¬outs[b]`, the
            // unit just asserted is `outs[b]` — a PROVEN bound of at least
            // b+1 violations in this totalizer. Add the reverse clauses so
            // the bound propagates instead of being re-derived by search
            // (CGSS2 exhaust_totalizer, cgss2.cpp:614-621, does exactly this
            // after its matching add_clause).
            if self.tot_eqs_on() {
                if let Some(&SumRef { tot, bound }) = self.sums.get(&core[0]) {
                    let mut budget = self.tot_eq_budget;
                    self.totalizers[tot].force_true(bound - 1, &mut self.sat, &mut budget);
                    self.stats.tot_eq_clauses = self
                        .stats
                        .tot_eq_clauses
                        .saturating_add((self.tot_eq_budget - budget) as u64);
                    self.stats.tot_eq_forced = self.stats.tot_eq_forced.saturating_add(1);
                    self.tot_eq_budget = budget;
                }
            }
            return new_sums;
        }

        // #wce: defer the relaxation. The lb payment and the weight
        // splitting above stay IMMEDIATE, but the new totalizer over the
        // members' violation indicators is only built at the next flush
        // point (flush_pending), so the solver keeps mining further
        // DISJOINT cores among the remaining assumptions without fighting
        // freshly added cardinality clauses. Trim/minimize already ran on
        // `core`; the solve loop guarantees disjointness by flushing
        // before processing an overlapping core.
        self.pending_members.extend(core.iter().copied());
        self.pending_relax.push((core.to_vec(), w_min));
        new_sums
    }

    /// #wce: materialize the deferred relaxation of one multi-member core —
    /// build the totalizer over the members' violation indicators, open it
    /// at bound 2, and activate the bound-2 selector at the core's
    /// extraction-time w_min. Exactly the structure eager OLL used to build
    /// inside process_core.
    /// #tot-eqs: lever active for this instance? Tuning override first (tests),
    /// then the env gate, and always subject to the remaining clause budget.
    fn tot_eqs_on(&self) -> bool {
        self.tot_eq_budget > 0 && self.tuning.tot_eqs.unwrap_or_else(tot_eqs_enabled)
    }

    fn relax_core(&mut self, members: &[Literal], w_min: Weight) -> Literal {
        let inputs: Vec<Literal> = members.iter().map(|sel| sel.negated()).collect();
        let mut root = TotNode::build(&inputs);
        let next_var = &mut self.next_var;
        let mut fresh = |sat: &mut SatSolver| {
            let var = sat.new_var();
            *next_var = var.id() + 1;
            // Prefer "few violations": totalizer outputs default false.
            sat.set_phase(var, false);
            Literal::positive(var)
        };
        root.extend(2, &mut self.sat, &mut fresh, None);
        // #core-clause: the core was UNSAT, so the hard clauses entail that at
        // least one member is violated. Pin that disjunction permanently.
        if self.tuning.core_clause.unwrap_or_else(core_clause_enabled) {
            self.sat.add_clause(inputs.clone());
            self.stats.core_clauses_added = self.stats.core_clauses_added.saturating_add(1);
        }
        let sum_sel = root.outs[1].negated();
        // #tot-eqs: the core was UNSAT, so the hard clauses entail that at
        // least one member is violated — `outs[0]` is proven true. Assert it
        // and add the reverse clauses that make the assertion propagate
        // (CGSS2 cgss2.cpp:714 calls forced_true(t.outputs[0]) here). Asserting
        // it cannot change the optimum: `outs` are fresh variables and every
        // model of the hard clauses violates >= 1 member, so every optimum
        // extends to satisfy the unit.
        if self.tot_eqs_on() {
            let out0 = root.outs[0];
            self.sat.add_clause(vec![out0]);
            let mut budget = self.tot_eq_budget;
            root.force_true(0, &mut self.sat, &mut budget);
            self.stats.tot_eq_clauses = self
                .stats
                .tot_eq_clauses
                .saturating_add((self.tot_eq_budget - budget) as u64);
            self.stats.tot_eq_forced = self.stats.tot_eq_forced.saturating_add(1);
            self.tot_eq_budget = budget;
        }
        self.totalizers.push(root);
        self.tot_base_w.push(w_min);
        self.tot_top_bound.push(2);
        self.stats.cardinality_constraints = self.stats.cardinality_constraints.saturating_add(1);
        self.sums.insert(
            sum_sel,
            SumRef {
                tot: self.totalizers.len() - 1,
                bound: 2,
            },
        );
        *self.active.entry(sum_sel).or_insert(0) += w_min;
        sum_sel
    }

    /// #wce: flush every pending core — build its totalizer (relax_core),
    /// then run the budgeted exhaust over each new sum selector (the probe
    /// that eager OLL ran at extraction time). With `delay` the new
    /// selectors join `suspended` (totalizer-delay discipline: they stay
    /// out of the assumptions until the phase reaches SAT); without it they
    /// become immediately assumable (used when the assumption set ran
    /// empty — nothing is left for the delay to protect, CGSS2 flushes
    /// into the live assumptions the same way).
    ///
    /// Returns `false` when an exhaust probe proved the formula globally
    /// UNSAT (the caller must treat this as terminal, exactly like
    /// exhaust_sum's own callers).
    ///
    /// Flush points and their reasoning (kept in one place):
    /// (a) Sat arm, BEFORE the suspended-set check: the model terminates
    ///     the delay phase, so all deferred structure materializes and the
    ///     existing suspended branch re-solves at the same level with
    ///     everything activated together. The level logic (level-1
    ///     terminal, next_level histogram) therefore NEVER runs with
    ///     unrelaxed cores — the level-1 terminal argument "model
    ///     satisfies every active selector => cost == lb" needs every
    ///     extracted core's counting structure to be active, and
    ///     next_level must see the flushed selectors/tails in its live
    ///     histogram.
    /// (b) When the filtered assumption set runs empty with cores pending:
    ///     that emptiness is an artifact of the deferral (the would-be sum
    ///     selectors, each with w_min >= level, don't exist yet), not a
    ///     finished level phase.
    /// (c) Before an LP-boost round and before a descent commit: both are
    ///     followed by potential optimal() exits and (for the descent) a
    ///     one-way encoding commitment; run them on the materialized
    ///     encoding, with any lb/ub motion from the flush exhausts already
    ///     applied.
    /// (e) Overlap flush (solve()'s Unsat arm): before processing a core
    ///     that intersects `pending_members`, so every batch stays a
    ///     DISJOINT core family — overlapping batches fragment a region's
    ///     weight into sub-level residue that only the dust level can
    ///     collect (see the measurement at the call site).
    /// (d) Deliberately NOT flushed before returning optimal()/Unknown:
    ///     lb payments are immediate, so `effective_lb() >= ub` is a
    ///     complete optimality proof with or without the pending
    ///     totalizers (they are definitional counting structure whose
    ///     clauses every model extends to satisfy — adding them cannot
    ///     change the optimum, and their w_min·(v−1) identity terms are
    ///     nonnegative, so lb stays a valid bound). The hard-UNSAT
    ///     empty-core exit is likewise independent of definitional
    ///     clauses, and the level-1 terminal — the one exit whose argument
    ///     DOES need materialized bounds — is protected structurally by
    ///     (a) running first. Unknown returns only the incumbent and makes
    ///     no accounting claim; building totalizers at a timeout would be
    ///     pure waste.
    fn flush_pending(
        &mut self,
        suspended: &mut HashSet<Literal>,
        delay: bool,
        started: Instant,
        exhaust_spent: &mut Duration,
        should_stop: &dyn Fn() -> bool,
    ) -> bool {
        if self.pending_relax.is_empty() {
            return true;
        }
        let pending = std::mem::take(&mut self.pending_relax);
        self.pending_members.clear();
        self.stats.wce_flushes = self.stats.wce_flushes.saturating_add(1);
        self.stats.wce_relaxed_cores = self
            .stats
            .wce_relaxed_cores
            .saturating_add(pending.len() as u64);
        self.stats.wce_max_flush_batch = self.stats.wce_max_flush_batch.max(pending.len() as u64);
        if debug_trace() {
            eprintln!(
                "c wce flush: {} pending cores (delay={}) lb={} ub={}",
                pending.len(),
                delay,
                self.lb,
                self.ub
            );
        }
        let mut new_sels = Vec::with_capacity(pending.len());
        for (members, w_min) in &pending {
            let sel = self.relax_core(members, *w_min);
            // Suspend BEFORE any early return below: a delayed flush must
            // never leave a subset of its batch assumable.
            if delay {
                suspended.insert(sel);
            }
            new_sels.push(sel);
        }
        // Exhaust each fresh sum under the global time-share budget —
        // the same gate eager OLL applied at extraction time. Disjoint
        // batches (the overlap flush) keep this fair: batch sizes track
        // the instance's disjoint-core width, so the share is consumed at
        // the same cadence as eager extraction, not swallowed by one
        // giant deferred batch. (Both alternatives were measured on mpe:
        // OVERLAPPING batches starved 149-core batches at this gate and
        // pushed their unpaid unit-core lb to the dust level, 4.2s -> 31s;
        // UNGATED exhausts on singleton-batch instances let dust-level
        // probes dominate wall time, distorting the lb/sec stall metric
        // until the value-stall gate committed a hopeless adder descent,
        // 27s -> timeout on mpe 240-1.) Exhaust probes produce unit cores
        // only (single assumption), so no new pending entries can appear
        // mid-flush.
        for sel in new_sels {
            if should_stop() {
                return true;
            }
            if exhaust_spent.as_secs_f64() < EXHAUST_TIME_SHARE * started.elapsed().as_secs_f64() {
                let t0 = Instant::now();
                let ok = self.exhaust_sum(sel, suspended, should_stop);
                *exhaust_spent += t0.elapsed();
                if !ok {
                    return false;
                }
            }
        }
        debug_assert!(
            self.pending_relax.is_empty(),
            "flush must not requeue cores (exhaust cores are unit)",
        );
        true
    }

    /// #lp-boost: true when the lane may capture cores / run LP rounds at
    /// all (mode + instance gate + not disabled).
    fn lp_lane_open(&self) -> bool {
        if self.lp_disabled {
            return false;
        }
        match self.tuning.lp_boost {
            LpBoostMode::Off => false,
            LpBoostMode::Force => true,
            LpBoostMode::Auto => self.lp_eligible,
        }
    }

    /// #lp-boost: store `core` as a packing row iff every member maps to an
    /// original soft selector. Rows are sorted soft-index sets, deduped,
    /// capped in count and size (see the LP_BOOST_* constants).
    fn lp_capture_core(&mut self, core: &[Literal]) {
        if !self.lp_lane_open()
            || self.lp_cores.len() >= LP_BOOST_MAX_CORES
            || core.is_empty()
            || core.len() > LP_BOOST_MAX_CORE_SIZE
        {
            return;
        }
        let mut row: Vec<u32> = Vec::with_capacity(core.len());
        for sel in core {
            match self.sel_to_soft.get(sel) {
                Some(&idx) => row.push(idx),
                // Sum/set selector: the whole core is unusable (stripping it
                // instead would strengthen the row — unsound).
                None => return,
            }
        }
        row.sort_unstable();
        row.dedup();
        if self.lp_core_seen.contains(&row) {
            return;
        }
        self.lp_core_seen.insert(row.clone());
        self.lp_cores.push(row);
    }

    /// #lp-boost scheduling: first round fires at the OLL stall gate (right
    /// before any descent could commit); later rounds at most every
    /// LP_BOOST_CORE_STRIDE newly processed cores.
    fn lp_boost_due(&self, oll_stalling: bool) -> bool {
        if !self.lp_lane_open() || self.lp_cores.is_empty() {
            return false;
        }
        if self.stats.lp_boost_runs == 0 {
            oll_stalling
        } else {
            // Aggressive test tunings re-run per fresh core so the tiny
            // brute-force nets exercise many LP rounds per instance (the
            // dry-round rule still bounds the total).
            let stride = if self.tuning.lsu_stall_ms_per_core == 0 {
                1
            } else {
                LP_BOOST_CORE_STRIDE
            };
            self.stats.cores_found >= self.lp_last_run_cores + stride
        }
    }

    /// Certified lower bound used by termination tests: OLL's residual
    /// accounting lb joined with the LP packing bound. `boost_lb` is only
    /// ever COMPARED against ub here — it must not feed harden()'s
    /// `lb + w > ub` test nor process_core's `lb += w_min`, both of which
    /// rely on the residual invariant that an externally lifted lb breaks.
    fn effective_lb(&self) -> Weight {
        self.lb.max(self.boost_lb)
    }

    /// #lp-boost: build and solve the dual packing LP over the stored
    /// pure-original cores, certify the dual iterate exactly, and lift
    /// `boost_lb` when the certified bound beats the effective lower bound.
    ///
    /// SOUNDNESS — weight choice and bound composition (the load-bearing
    /// argument; do not change one side without the other):
    ///
    /// Every stored core κ was returned as an UNSAT assumption core over
    /// original soft selectors by the incremental solver. At extraction
    /// time the solver's formula contained, beyond the hard clauses:
    /// selector definitions and totalizer/descent circuitry (definitional —
    /// every model of the hard clauses extends to satisfy them, with each
    /// satisfied soft's selector true), plus ub-conditional clauses
    /// (hardened selectors, descent bound clauses, unit-core negations
    /// derived from them) which only exclude models costing >= the
    /// incumbent ub at the time they were added. ub is non-increasing, so
    /// every original model M with cost(M) < ub (current) extends to that
    /// formula with all its satisfied softs' selectors true. UNSAT of
    /// (formula ∧ κ) therefore means: M violates at least one soft in κ.
    ///
    /// Take any y >= 0 with sum_{κ∋s} y_κ <= w_s for every soft s, where
    /// w_s is the ORIGINAL post-install weight — exactly what model_cost()
    /// charges. Then for every model M with cost(M) < ub:
    ///
    ///   cost(M) - preproc_cost = sum_{s violated} w_s
    ///                          >= sum_{s violated} sum_{κ∋s} y_κ
    ///                           = sum_κ y_κ · |κ ∩ violated(M)|
    ///                          >= sum_κ y_κ.
    ///
    /// So `preproc_cost + sum(y)` lower-bounds every model cheaper than the
    /// incumbent — the same conditional semantics `lb` already carries in
    /// this engine (its cores come from the same hardened formula; see the
    /// empty-core arm of solve(), which declares the incumbent optimal on
    /// hard-UNSAT for exactly this reason). Consequences:
    ///
    /// 1. ORIGINAL weights + preproc-relative comparison. The LP bound is
    ///    preproc_cost + sum(y) and is COMPARED against lb, never added to
    ///    it. Residual weights would compose additively with lb instead,
    ///    but the stored cores include the very cores whose w_min already
    ///    moved into lb — adding would double-count. Original weights with
    ///    max-composition is the safe direction the design verdict picked.
    /// 2. `boost_lb` never enters `self.lb`: process_core/harden rely on
    ///    the invariant cost(M) >= lb + sum of violated actives' residual
    ///    weights, and the LP consumes soft-weight capacity in a different
    ///    decomposition than the residual bookkeeping, so a lifted lb would
    ///    break that inequality. Termination via effective_lb() >= ub is
    ///    sound on its own: it says no model cheaper than ub exists, hence
    ///    the incumbent is optimal.
    /// 3. Truncation-soundness: the argument above holds for ANY feasible
    ///    y, not just the LP optimum, so a budget-truncated simplex iterate
    ///    (P0b returns the best feasible iterate) yields a valid — merely
    ///    weaker — bound.
    fn run_lp_boost(&mut self, should_stop: &dyn Fn() -> bool) {
        self.lp_last_run_cores = self.stats.cores_found;
        self.stats.lp_boost_runs = self.stats.lp_boost_runs.saturating_add(1);

        // Support (distinct softs across rows) is the LP row count; skip and
        // disable beyond the cap — support only grows, so it never recovers.
        let mut support: Vec<u32> = self.lp_cores.iter().flatten().copied().collect();
        support.sort_unstable();
        support.dedup();
        if support.len() > LP_BOOST_MAX_SUPPORT {
            self.lp_disabled = true;
            return;
        }
        // Headroom guard for the exact u128 certification arithmetic (and
        // for f64 rhs sanity). sum(y) <= sum of support weights, so the
        // certified bound also stays comfortably inside u64.
        let total_w: u128 = support
            .iter()
            .map(|&s| self.soft_weights[s as usize] as u128)
            .sum();
        if total_w > (1u128 << 62) {
            self.lp_disabled = true;
            return;
        }

        // Dual packing LP: max sum y_κ, s.t. per soft s (row, RowKind::Le):
        // sum_{κ∋s} y_κ <= w_s; y_κ >= 0 free above. All rows `<=` with
        // nonnegative rhs — ay-lp starts from the native feasible slack
        // basis, no Big-M artificials involved.
        let mut problem = ay_lp::Problem::new();
        problem.sense = ay_lp::Sense::Max;
        for _ in 0..self.lp_cores.len() {
            problem.variables.push(ay_lp::Variable {
                name: String::new(),
                obj_coeff: 1.0,
                lower: 0.0,
                // Finite uppers would become extra tableau rows; the member
                // rows already bound every y_κ (cores are non-empty).
                upper: f64::INFINITY,
                kind: ay_lp::VarKind::Continuous,
            });
        }
        let mut cols_by_soft: HashMap<u32, Vec<(usize, f64)>> = HashMap::new();
        for (c, core) in self.lp_cores.iter().enumerate() {
            for &s in core {
                cols_by_soft.entry(s).or_default().push((c, 1.0));
            }
        }
        for &s in &support {
            problem.constraints.push(ay_lp::Constraint {
                name: String::new(),
                kind: ay_lp::RowKind::Le,
                coeffs: cols_by_soft.remove(&s).unwrap_or_default(),
                rhs: self.soft_weights[s as usize] as f64,
            });
        }

        let deadline = Instant::now() + LP_BOOST_CALL_BUDGET;
        let stop = || should_stop() || Instant::now() >= deadline;
        let bound_units =
            match ay_lp::solve_lp_relaxation_budgeted(&problem, LP_BOOST_MAX_ITERS, &stop) {
                Ok(relax) => self.lp_certified_bound(&relax.solution.values),
                // All-Le problems cannot fail feasibility; treat any error as a
                // zero bound (dry round).
                Err(_) => 0,
            };

        let candidate = self.preproc_cost.saturating_add(bound_units);
        let improved = candidate > self.effective_lb();
        if improved {
            // Clamp at ub: values above it carry no extra information (the
            // bound is conditional on cost < ub) and the clamp keeps any
            // reported lower bound <= ub while still triggering the
            // effective_lb() >= ub termination.
            self.boost_lb = candidate.min(self.ub);
            self.lp_dry_rounds = 0;
            self.stats.lp_boost_improvements = self.stats.lp_boost_improvements.saturating_add(1);
        } else {
            self.lp_dry_rounds += 1;
            if self.lp_dry_rounds >= LP_BOOST_MAX_DRY_ROUNDS {
                self.lp_disabled = true;
            }
        }
        if debug_trace() {
            eprintln!(
                "c lp-boost: cores={} support={} bound={}+{} lb={} boost_lb={} ub={}{}{}",
                self.lp_cores.len(),
                support.len(),
                self.preproc_cost,
                bound_units,
                self.lb,
                self.boost_lb,
                self.ub,
                if improved { " improved" } else { " dry" },
                if self.lp_disabled { " disabled" } else { "" },
            );
        }
    }

    /// #lp-boost: certify a possibly noisy / truncated dual iterate exactly
    /// and convert it into an integer bound on `cost - preproc_cost`.
    ///
    /// The iterate is floored into fixed point (shift LP_BOOST_FP_SHIFT) and
    /// every packing row `sum_{κ∋s} y_κ <= w_s` is re-checked in EXACT u128
    /// integer arithmetic; float noise from the dense simplex is repaired by
    /// shrink-and-recheck rounds (the lossy f64 shrink factor can only
    /// over-shrink — the acceptance test stays exact). Certification
    /// failure returns 0, which never lifts the bound.
    ///
    /// Rounding: fy/2^k is an exactly feasible rational dual point, so
    /// `cost(M) - preproc >= sum(fy)/2^k` for every model M cheaper than ub
    /// (see run_lp_boost). The left side is an integer, so the bound could
    /// be lifted to ceil(sum/2^k); ceiling a NOISY float objective would be
    /// the classic unsound shortcut, but here the value is exact and the
    /// integrality argument airtight. We still take the strictly more
    /// conservative epsilon-floor floor(sum/2^k + 1/64): it equals ceil on
    /// near-integer values (recovering optima computed as 4.9999...) and
    /// stays <= ceil(r) for every real r and epsilon < 1 — never a full
    /// ceil of a genuinely fractional LP value. (A gcd(w)-multiple lift on
    /// top would need all support weights' gcd; deliberately not done.)
    fn lp_certified_bound(&self, y: &[f64]) -> Weight {
        if y.len() != self.lp_cores.len() {
            return 0;
        }
        let one: u128 = 1u128 << LP_BOOST_FP_SHIFT;
        let mut fy: Vec<u128> = y
            .iter()
            .map(|&v| {
                if v.is_finite() && v > 0.0 {
                    // Cap far above any feasible packing value (sum of
                    // support weights is guarded to <= 2^62); the cap only
                    // keeps the u128 arithmetic in range.
                    (v.min(4.6e18) * one as f64) as u128
                } else {
                    0
                }
            })
            .collect();
        for _round in 0..4 {
            let mut col: HashMap<u32, u128> = HashMap::new();
            for (c, core) in self.lp_cores.iter().enumerate() {
                if fy[c] == 0 {
                    continue;
                }
                for &s in core {
                    *col.entry(s).or_insert(0) += fy[c];
                }
            }
            let mut factor: f64 = 1.0;
            for (&s, &sum) in &col {
                let cap = (self.soft_weights[s as usize] as u128) << LP_BOOST_FP_SHIFT;
                if sum > cap {
                    factor = factor.min(cap as f64 / sum as f64);
                }
            }
            if factor >= 1.0 {
                let total: u128 = fy.iter().sum();
                let units = (total + one / 64) >> LP_BOOST_FP_SHIFT;
                return Weight::try_from(units).unwrap_or(0);
            }
            let shrink = (factor * (1.0 - 1e-9)).max(0.0);
            for v in fy.iter_mut() {
                *v = (*v as f64 * shrink) as u128;
            }
        }
        0
    }

    /// Form abstraction sets (abstract cores / structure sharing, v1):
    /// partition the surviving active original selectors into uniform-weight,
    /// id-contiguous sets (competition encodings place related softs
    /// contiguously), give each set ONE shared totalizer, and swap the
    /// members' individual assumptions for the set's "no violations" bound
    /// literal. Assuming `¬O_1` is SAT-equivalent to assuming every member,
    /// so nothing is lost; what is gained is that every future core over a
    /// set speaks its count-literal language, and repeated conflicts inside
    /// a set become bound bumps on the ONE shared totalizer instead of a
    /// stack of fresh per-core totalizers. The existing sum machinery
    /// (bumping, weight splitting, hardening) applies unchanged, because a
    /// set bound IS a sum selector whose group was chosen a priori.
    /// Accounting stays exact: the set selector enters at the members'
    /// uniform weight with bound 1 and no lower-bound payment.
    fn form_abstraction_sets(&mut self) -> Vec<Literal> {
        const SET_SIZE: usize = 32;
        const MIN_SET: usize = 8;

        // Core-informed clustering (v2, CGSS-style): selectors that appeared
        // together in an observed core are unioned; sets are formed within
        // (weight class, cluster) so each shared totalizer covers selectors
        // with demonstrated shared core structure. Selectors never seen
        // co-occurring fall back to the v1 id-order pool per weight class.
        let mut sels_by_idx: Vec<Literal> = self
            .active
            .iter()
            .filter(|(sel, _)| !self.sums.contains_key(sel))
            .map(|(&sel, _)| sel)
            .collect();
        sels_by_idx.sort_unstable();
        let index: HashMap<Literal, usize> = sels_by_idx
            .iter()
            .enumerate()
            .map(|(i, &sel)| (sel, i))
            .collect();

        fn find(parent: &mut [usize], mut x: usize) -> usize {
            while parent[x] != x {
                parent[x] = parent[parent[x]];
                x = parent[x];
            }
            x
        }
        let mut parent: Vec<usize> = (0..sels_by_idx.len()).collect();
        for core in &self.core_history {
            let mut first: Option<usize> = None;
            for sel in core {
                let Some(&i) = index.get(sel) else { continue };
                match first {
                    None => first = Some(i),
                    Some(f) => {
                        let (rf, ri) = (find(&mut parent, f), find(&mut parent, i));
                        parent[rf.max(ri)] = rf.min(ri);
                    }
                }
            }
        }

        // Group by (weight, cluster root); undersized clusters pool into the
        // per-weight residue so coverage never shrinks below v1's.
        let mut groups: HashMap<(Weight, usize), Vec<Literal>> = HashMap::new();
        for (i, &sel) in sels_by_idx.iter().enumerate() {
            let w = self.active[&sel];
            let root = find(&mut parent, i);
            groups.entry((w, root)).or_default().push(sel);
        }
        let mut classes: HashMap<Weight, Vec<Vec<Literal>>> = HashMap::new();
        let mut residue: HashMap<Weight, Vec<Literal>> = HashMap::new();
        let mut group_list: Vec<((Weight, usize), Vec<Literal>)> = groups.into_iter().collect();
        group_list.sort_unstable_by_key(|((w, root), _)| (*w, *root));
        for ((w, _), members) in group_list {
            if members.len() >= MIN_SET {
                classes.entry(w).or_default().push(members);
            } else {
                residue.entry(w).or_default().extend(members);
            }
        }
        for (w, mut pool) in residue {
            pool.sort_unstable();
            if pool.len() >= MIN_SET {
                classes.entry(w).or_default().push(pool);
            }
        }

        let mut formed = 0usize;
        let mut new_sets: Vec<Literal> = Vec::new();
        let mut class_list: Vec<(Weight, Vec<Vec<Literal>>)> = classes.into_iter().collect();
        class_list.sort_unstable_by_key(|(w, _)| *w);
        for (w, sel_groups) in class_list {
            for mut sels in sel_groups {
                sels.sort_unstable();
                for chunk in sels.chunks(SET_SIZE) {
                    if chunk.len() < MIN_SET {
                        continue;
                    }
                    let inputs: Vec<Literal> = chunk.iter().map(|l| l.negated()).collect();
                    let mut root = TotNode::build(&inputs);
                    let next_var = &mut self.next_var;
                    let mut fresh = |sat: &mut SatSolver| {
                        let var = sat.new_var();
                        *next_var = var.id() + 1;
                        sat.set_phase(var, false);
                        Literal::positive(var)
                    };
                    root.extend(1, &mut self.sat, &mut fresh, None);
                    let sum_sel = root.outs[0].negated();
                    self.sat.freeze(sum_sel.variable());
                    for l in chunk {
                        self.active.remove(l);
                    }
                    self.totalizers.push(root);
                    self.tot_base_w.push(w);
                    self.tot_top_bound.push(1);
                    self.sums.insert(
                        sum_sel,
                        SumRef {
                            tot: self.totalizers.len() - 1,
                            bound: 1,
                        },
                    );
                    *self.active.entry(sum_sel).or_insert(0) += w;
                    formed += 1;
                    new_sets.push(sum_sel);
                }
            }
        }
        self.stats.abstraction_sets = self.stats.abstraction_sets.saturating_add(formed as u64);
        if debug_trace() && formed > 0 {
            eprintln!(
                "c abstraction: formed {} sets (active now {})",
                formed,
                self.active.len()
            );
        }
        new_sets
    }

    /// Try to raise the lower bound by repeatedly probing a freshly created
    /// sum selector alone under a small wall-clock budget ("core
    /// exhaustion", RC2 `-x` / EvalMaxSAT). Each UNSAT probe proves one
    /// more forced violation in the group and unlocks the next bound.
    ///
    /// Returns `false` if the formula was proven globally UNSAT (empty
    /// core), which the caller must handle as terminal.
    fn exhaust_sum(
        &mut self,
        mut sel: Literal,
        suspended: &mut HashSet<Literal>,
        should_stop: &dyn Fn() -> bool,
    ) -> bool {
        loop {
            if should_stop() || !self.active.contains_key(&sel) {
                return true;
            }
            let probe_deadline = Instant::now() + EXHAUST_PROBE_BUDGET;
            let probe_stop = || should_stop() || Instant::now() >= probe_deadline;
            self.stats.sat_calls = self.stats.sat_calls.saturating_add(1);
            let result = self
                .sat
                .solve_with_assumptions_interruptible(&[sel], &probe_stop)
                .into_inner();
            match result {
                AssumeResult::Unsat(core, _) => {
                    if core.is_empty() {
                        return false;
                    }
                    self.stats.exhaust_steps = self.stats.exhaust_steps.saturating_add(1);
                    let lb_pre = self.lb;
                    let new_sums = self.process_core(&core, CoreOrigin::Search);
                    self.record_sat_core(&core, lb_pre);
                    suspended.extend(new_sums.iter().copied());
                    match new_sums.last() {
                        Some(&next) => sel = next,
                        None => return true,
                    }
                }
                AssumeResult::Sat(model) => {
                    // Free feasible model: keep it if it improves the
                    // incumbent, then stop exhausting.
                    let cost = self.model_cost(&model);
                    if cost < self.ub {
                        self.ub = cost;
                        self.ub_last_improved = Instant::now();
                        self.best_model = Some(model);
                    }
                    return true;
                }
                _ => return true,
            }
        }
    }

    /// Uniform weight over the live (non-hardened) original softs, if every
    /// such soft shares one positive weight — exactly the condition under which
    /// `ensure_descent_enc` builds the cheap totalizer descent (rather than a
    /// GTE/adder). Cheap O(softs) scan; consulted only at the descent entry
    /// gate (#expensive-core-descent), so it never enters a per-core hot path.
    fn residual_uniform_weight(&self) -> Option<Weight> {
        let mut w0: Option<Weight> = None;
        for i in 0..self.softs.len() {
            if self.hardened_sels.contains(&self.soft_selectors[i]) {
                continue;
            }
            let w = self.soft_weights[i];
            match w0 {
                None => w0 = Some(w),
                Some(prev) if prev == w => {}
                _ => return None,
            }
        }
        w0.filter(|&w| w > 0)
    }

    /// #cold-core-descent: THE DROUGHT CLOCK. Time already banked toward the
    /// current drought, plus the segment currently running (nothing, if the
    /// clock is paused).
    ///
    /// The drought must measure time the engine spent LOOKING FOR CORES and
    /// finding none. A plain `last_core.elapsed()` does not: the wall clock
    /// keeps running while the engine is inside [`OllEngine::descend`], where
    /// no core can arrive BY CONSTRUCTION (the descent walks the ub side and
    /// never calls `process_core`). That charged descent time as evidence of a
    /// core drought, so a descent slice manufactured the very drought that
    /// justified the next, stronger entry — a self-triggering ratchet.
    /// `pause_core_drought`/`resume_core_drought` bracket that span.
    fn core_drought(&self) -> Duration {
        match self.core_drought_since {
            Some(t) => self.core_drought.saturating_add(t.elapsed()),
            None => self.core_drought,
        }
    }

    /// #cold-core-descent: stop charging drought time (entering a span in
    /// which no core CAN arrive). Idempotent.
    fn pause_core_drought(&mut self) {
        self.pause_core_drought_at(Instant::now());
    }

    /// #cold-core-descent: resume charging drought time. Idempotent, and it
    /// does NOT clear what was already banked — the drought that preceded the
    /// paused span is still real evidence.
    fn resume_core_drought(&mut self) {
        self.resume_core_drought_at(Instant::now());
    }

    /// [`Self::pause_core_drought`] at an explicit instant, so the clock's
    /// arithmetic is testable without sleeping.
    fn pause_core_drought_at(&mut self, at: Instant) {
        if let Some(t) = self.core_drought_since.take() {
            self.core_drought = self
                .core_drought
                .saturating_add(at.saturating_duration_since(t));
        }
    }

    /// [`Self::resume_core_drought`] at an explicit instant.
    fn resume_core_drought_at(&mut self, at: Instant) {
        if self.core_drought_since.is_none() {
            self.core_drought_since = Some(at);
        }
    }

    /// #cold-core-descent: forget the current drought and start a fresh one.
    ///
    /// Used where core discovery legitimately stops and restarting it is
    /// EXPECTED rather than evidence of collapse: a stratification level
    /// change (`activate_stratum`) re-populates the assumable set, and the
    /// gate cannot otherwise tell "the previous stratum ran out" apart from
    /// "the search went cold" — it would let the arm commit before the new
    /// stratum had produced a single core.
    fn reset_core_drought(&mut self) {
        self.core_drought = Duration::ZERO;
        self.core_drought_since = Some(Instant::now());
    }

    /// #cold-core-descent: record a SEARCH-derived core arrival — its interval
    /// joins the trailing rate baseline, and the drought clock restarts.
    ///
    /// The whole per-core cost of the rate gate: one `Instant`, one push, and
    /// one sort of at most `COLD_CORE_WINDOW` u64s.
    fn note_search_core(&mut self, at: Instant) {
        // The first search core has no predecessor, so the "interval" would be
        // the time from the start of the run — not a rate observation.
        if self.core_search_cores > 0 {
            let gap = self
                .core_drought
                .saturating_add(match self.core_drought_since {
                    Some(t) => at.saturating_duration_since(t),
                    None => Duration::ZERO,
                });
            if self.core_gaps_ms.len() == COLD_CORE_WINDOW {
                self.core_gaps_ms.remove(0);
            }
            self.core_gaps_ms.push(gap.as_millis() as u64);
            let mut sorted = self.core_gaps_ms.clone();
            sorted.sort_unstable();
            self.core_gap_median_ms = sorted[sorted.len() / 2];
        }
        self.core_search_cores = self.core_search_cores.saturating_add(1);
        self.core_drought = Duration::ZERO;
        self.core_drought_since = Some(at);
    }

    /// #cold-core-descent: the drought (ms of core-searching time since the
    /// last search-derived core) that counts as COLD on this instance —
    /// `COLD_CORE_DROUGHT_MULT` times its own TRAILING median inter-core
    /// interval, floored at `COLD_CORE_MIN_DROUGHT`.
    ///
    /// The bar is RELATIVE by construction. An absolute one cannot exist here:
    /// the corpus runs from 3 to 1,035,351 hard clauses, so a 30s lull is a
    /// catastrophe on an instance that was streaming 10 cores a second and a
    /// perfectly ordinary step on one that pays ~1s per assumption solve.
    /// TRAILING rather than "first N" is what makes that statement true in
    /// practice rather than only in the comment — see [`COLD_CORE_WINDOW`].
    fn cold_core_bar_ms(&self) -> u64 {
        self.core_gap_median_ms
            .saturating_mul(COLD_CORE_DROUGHT_MULT)
            .max(COLD_CORE_MIN_DROUGHT.as_millis() as u64)
    }

    /// #cold-core-descent: has core discovery gone COLD relative to this
    /// instance's own recent arrival rate?
    ///
    /// This is an ADDITIONAL descent entry path, disjoined with (never
    /// substituted for) the `cores_found >= lsu_min_cores` count. It carries
    /// the organic gate's other conjuncts — `gap_ok`, an incumbent, and
    /// `descent_not_before` — but deliberately NOT `oll_stalling` (see the
    /// `cold_ready` binding in `solve` for the trace that forced that choice).
    ///
    /// WHAT STOPS IT FIRING WHILE THE SLOW CORE WALK IS STILL THE WINNING PATH
    /// (rna-alignment, protein_ins — where a premature commit would lose
    /// instances AY solves today). Five independent brakes:
    ///
    ///  1. THE BAR IS THE INSTANCE'S OWN RECENT RATE. A walk that keeps
    ///     delivering a core every ~20s has a ~20s trailing median, so its bar
    ///     is ~240s: steady slowness never reads as cold, only a collapse
    ///     relative to the CURRENT trend does. Under the shipped first-N
    ///     baseline this brake was inert (see [`COLD_CORE_WINDOW`]); the
    ///     trailing window is what makes it real.
    ///  2. A DROUGHT SPENT INSIDE ONE ASSUMPTION SOLVE IS INVISIBLE. The gate
    ///     is evaluated only BETWEEN OLL iterations, so a long solve that
    ///     returns a core resets the drought before the gate ever sees it —
    ///     the arm structurally cannot preempt a solve that is about to pay.
    ///     Measured on causal n6 at 900s, whose late gaps are exactly that
    ///     shape: at the descent entry the gate reported `drought_ms=0` against
    ///     `bar_ms=30756`, in both the lever-on and lever-off legs, and the arm
    ///     never fired in either. Only droughts that span SEVERAL iterations —
    ///     churn that produces no cores — reach this gate.
    ///  3. NO FIRING ON THE FIRST FEW CORES (`COLD_CORE_MIN_SAMPLE` intervals,
    ///     all of them SEARCH-derived — see [`CoreOrigin`]) or inside the
    ///     opening `COLD_CORE_MIN_ELAPSED` of the run.
    ///  4. IT CANNOT PREEMPT THE COUNT PATH ON A FAST INSTANCE. Where cores
    ///     stream (rna: 66 by t=18.5s), the 64-core bar is reached before a
    ///     30s drought can even exist, so the count path fires first and this
    ///     one is inert. The instances it reaches are the ones the count path
    ///     reaches late (causal n6: core #64 at t=408-473s here) or never
    ///     (af-synthesis: ~16 cores, then nothing for the rest of the run).
    ///  5. THE CLOCK ONLY RUNS WHILE THE ENGINE IS LOOKING FOR CORES. Descent
    ///     slices are paused out and stratum activations reset it, so neither
    ///     the arm's own effect nor an ordinary level change can be mistaken
    ///     for evidence that discovery collapsed (see [`Self::core_drought`]).
    ///
    /// `lsu_min_cores == u64::MAX` is the tuning sentinel for "descents never
    /// engage" (the pure-OLL nets), and is honoured here too — this path must
    /// not smuggle a descent into a fixture that forbids one.
    fn core_discovery_cold(&self, started: Instant) -> bool {
        if self.tuning.lsu_min_cores == u64::MAX {
            return false;
        }
        // No incumbent => nothing for `descend` to improve on. (The caller
        // tests this too; keeping it here makes the predicate self-contained
        // and its trace honest.)
        if self.best_model.is_none() {
            return false;
        }
        if self.core_gaps_ms.len() < COLD_CORE_MIN_SAMPLE {
            return false;
        }
        if started.elapsed() < COLD_CORE_MIN_ELAPSED {
            return false;
        }
        (self.core_drought().as_millis() as u64) >= self.cold_core_bar_ms()
    }

    /// #cold-core-descent D6: can a descent encoding still be built on this
    /// instance? The cheap short-circuit the entry gate uses BEFORE paying for
    /// `flush_pending`.
    ///
    /// `descent_unavailable` is permanent; a SIZE decline is not, so it is
    /// re-tried once one of the two monotone components of the recorded
    /// signature has strictly improved (`hardened_sels` only grows and `ub`
    /// only falls — both shrink the encoding). See `descent_size_declined`.
    fn descent_reachable(&self) -> bool {
        if self.descent.is_some() {
            return true;
        }
        if self.descent_unavailable {
            return false;
        }
        match self.descent_size_declined {
            None => true,
            Some((hardened, ub)) => self.hardened_sels.len() > hardened || self.ub < ub,
        }
    }

    /// Kick-entry gap bar, in units of the objective's own granularity.
    ///
    /// `DESCENT_KICK_GAP` is an ABSOLUTE cost tested against `ub - lb` on a
    /// track whose optima span 3..3.7e10 — a dimensional error. Measured on the
    /// MSE24 exact-weighted addressable set (AY unsolved at 60s, some MSE24
    /// solver solved; 138 instances, 131 of which carry an incumbent): 57 of
    /// those 131 have `incumbent - optimum > 32`, and `lb <= optimum` makes
    /// `ub - lb > 32` for the whole run, so the kick can never fire on 44% of
    /// the target set.
    /// Traced at the constant's boundary on af-synthesis (same family, same
    /// binary, same load, 120s):
    ///
    /// | instance | cores | lb | ub | gap | descent lines |
    /// | --- | --- | --- | --- | --- | --- |
    /// | `af-synthesis_stb_50_120_5` | 17 | 83 | 115 | **32** | 1 (GTE, cap 115) |
    /// | `af-synthesis_stb_50_160_5` | 16 | 77 | 113 | **36** | **0** |
    ///
    /// `160_5` is sitting on its exact optimum (113) and is blocked from proving
    /// it by four units against a hard-coded constant; the sibling proves the
    /// encoding it would need costs nothing. Both descent paths are shut on this
    /// family at once — the organic gate needs `cores_found >= lsu_min_cores`
    /// (64) and these runs end at 16-18 — which is why AY is 0/15 here and the
    /// upper-bound-descent solvers are 15/15.
    ///
    /// The uniform arm of `gap_ok` already states the right unit:
    /// `w * lsu_min_gap_units`. The generalization to mixed weights is the
    /// MINIMUM live weight — the finest granularity the residual objective can
    /// move by — which agrees with the uniform arm exactly whenever it is
    /// defined.
    ///
    /// Widening is gated on the descent encoding being the cheap GTE. Where the
    /// projection is the wide adder instead (causal-discovery: cap 8.7e8 -> 36
    /// sum bits, one call outliving the whole 10s slice), keep the absolute bar:
    /// there the alternation is pure duty-cycle tax.
    ///
    /// Cheap O(softs) scan on the same path as `residual_uniform_weight`, i.e.
    /// the descent entry gate only, never a per-core hot path.
    fn descent_kick_gap_cap(&self) -> Weight {
        if kick_gap_abs_enabled() {
            return DESCENT_KICK_GAP;
        }
        let mut w_min: Option<Weight> = None;
        let mut wsum: Weight = 0;
        // Counts every live soft, zero-weight included, to match the
        // `inputs.len()` that `ensure_descent_enc` actually hands `gte_build`.
        let mut live: usize = 0;
        for i in 0..self.softs.len() {
            if self.hardened_sels.contains(&self.soft_selectors[i]) {
                continue;
            }
            live += 1;
            let w = self.soft_weights[i];
            if w == 0 {
                continue;
            }
            wsum = wsum.saturating_add(w);
            w_min = Some(match w_min {
                None => w,
                Some(m) => m.min(w),
            });
        }
        let Some(w_min) = w_min else {
            return DESCENT_KICK_GAP;
        };
        // `ensure_descent_enc` builds at `cap = ub - preproc_cost`; the total
        // live weight bounds the outputs a GTE can ever emit for that cap.
        let projected_outs = self.ub.saturating_sub(self.preproc_cost).min(wsum);
        if live > GTE_CHEAP_INPUTS || projected_outs > GTE_CHEAP_OUTS {
            return DESCENT_KICK_GAP;
        }
        DESCENT_KICK_GAP.max(w_min.saturating_mul(self.tuning.lsu_min_gap_units))
    }

    /// The live residual objective (`active ∪ pool`) at ANY weight shape, as
    /// `(selector, residual weight)` pairs with selectors in POSITIVE form.
    ///
    /// Generalises the retired `uniform_residual_objective`, which bailed the
    /// moment two live weights differed. That bail was an ENCODING restriction
    /// (its consumer is a counting totalizer, which can only count), never a
    /// soundness one — and it excluded exactly the mixed-weight families the
    /// residual cap pays off on.
    ///
    /// Dropped terms — hardened selectors (satisfied in every remaining model)
    /// and zero-weight entries — only make the encoded `Σ` SMALLER, which is
    /// the safe direction for `(★)` in [`Self::descent_residual_cap`]: a
    /// smaller `Σ` weakens the cut but can never exclude a cheaper model.
    /// A selector seen twice is therefore kept ONCE at its SMALLEST weight
    /// (defensive: `activate_level` moves entries out of `pool` into `active`,
    /// so nothing is in both today) — double-counting a term would INFLATE `Σ`
    /// past what `(★)` licenses, which is the unsound direction.
    fn residual_objective(&self) -> Vec<(Literal, Weight)> {
        let mut terms: Vec<(Literal, Weight)> =
            Vec::with_capacity(self.active.len() + self.pool.len());
        for (&sel, &w) in self
            .active
            .iter()
            .chain(self.pool.iter().map(|(l, w)| (l, w)))
        {
            if w == 0 || self.hardened_sels.contains(&sel) {
                continue;
            }
            terms.push((sel, w));
        }
        // `active` is a HashMap: sort so the encoding cannot depend on hash
        // iteration order. Ties sort by weight ASCENDING, so the dedup below —
        // which keeps the first entry of each run — keeps the smallest weight.
        terms.sort_unstable();
        terms.dedup_by_key(|(sel, _)| *sel);
        terms
    }

    /// #descent-residual: the EXCLUSIVE cap for a residual cut, `ub - lb`.
    /// `None` means "no residual cut" — the descent then runs on its exact
    /// original-objective encoding alone, exactly as it did before this lever.
    ///
    /// [SOUND-CRITICAL] THE INVARIANT THAT MAKES `ub - lb` A VALID CAP.
    ///
    /// OLL maintains, for every model `A` of the hard clauses (canonically
    /// extended to the auxiliary variables — see the last paragraph), the exact
    /// cost identity spelled out in full on `harden_residual_mass`:
    ///
    /// ```text
    ///   cost(A) = lb
    ///           + Σ_{sel ∈ active ∪ pool} w_sel · [sel falsified in A]      (Σ)
    ///           + Σ_t Σ_j (w0_t − W_{t,j}) · [v_t >= j]                 (ladder)
    ///           + Σ_{queued cores} w_min · (v − 1)                        (#wce)
    /// ```
    ///
    /// The last two groups are NONNEGATIVE — mass conservation on each
    /// totalizer's bound ladder makes `w0_t − W_{t,j}` a sum of current
    /// residuals, and `v >= 1` on a queued core because it was UNSAT when
    /// extracted. Dropping them leaves the only thing this cap needs:
    ///
    /// ```text
    ///   Σ  <=  cost(A) − lb                   for every model A.           (★)
    /// ```
    ///
    /// So asserting `Σ <= ub − lb − 1` excludes ONLY models with
    /// `cost(A) >= ub`, i.e. models no better than a solution this engine has
    /// already built and recorded. Every optimal model survives, and an UNSAT
    /// answer under the cap is a COMPLETE proof that `ub` is optimal — which is
    /// the whole point: the closing UNSAT call stops re-deriving from scratch
    /// the `lb` OLL has already paid cores for.
    ///
    /// WHAT WOULD BREAK IT.
    ///  1. `lb` OVER-ESTIMATED. `(★)` is an inequality about the CURRENT `lb`;
    ///     if any accounting path ever charges `lb` more than it removes from
    ///     the residual, the cap is too small, the closing call returns UNSAT
    ///     and the engine claims an optimum it has not got — a WRONG ANSWER,
    ///     which is disqualifying. `lb > ub` is arithmetically impossible (`ub`
    ///     is the cost of a model this engine actually built, hence ACHIEVABLE,
    ///     and a lower bound cannot exceed an achievable cost), so it is
    ///     checked below and FAILS CLOSED — the residual cap disarms for the
    ///     rest of the run and the descent reverts to the exact
    ///     original-objective encoding. Same discipline as the
    ///     `CORE-MINE-ABANDONED` fail-safe: an unsolved instance costs one
    ///     solve, a wrong `s OPTIMUM FOUND` costs the competition.
    ///  2. `effective_lb()` IN PLACE OF `lb`. `boost_lb` is an EXTERNAL lift
    ///     from the LP packing dual: it is not a term of the identity and does
    ///     not shrink the residual, so `ub − effective_lb()` is NOT a valid cap
    ///     even though it is a valid termination test. Use the plain `lb`.
    ///  3. ENCODING A TERM TWICE, OR ABOVE ITS RESIDUAL WEIGHT. Both inflate
    ///     the encoded `Σ` relative to `(★)`; `residual_objective` dedups and
    ///     keeps the smallest weight for exactly this reason. Encoding FEWER
    ///     terms, or at LOWER weights, is always safe — it only weakens the cut.
    ///  4. DERIVING THE BOUND FROM A MODEL instead of from `ub`. `(★)` is an
    ///     inequality, not an equality: a model with the same `Σ` can be
    ///     strictly cheaper, so "beat the `Σ` of the model I just found" is
    ///     invalid here even though it is valid for an exact encoding. One of
    ///     the two bugs behind the ten wrong answers this lever was reverted
    ///     for the first time (see [`ResidualBound`]).
    ///  5. CLAMPING AN UNREPRESENTABLE BOUND INTO RANGE. A cap larger than the
    ///     encoding can express is VACUOUS and must simply not be asserted; the
    ///     other of those two bugs. `residual_units` returns `None` for it,
    ///     `gte_build`'s capped sums match no output for it, and
    ///     `assert_sum_le` returns early on it — three encodings, none of which
    ///     may be "fixed" with a `.min(width)`.
    ///
    /// WHAT THE CUT DOES TO THE REST OF THE ENGINE. Nothing new. It excludes
    /// only models costing at least the incumbent OF THE DAY it was built, and
    /// `ub` only falls, so its excluded set stays inside "cost >= the current
    /// incumbent" — the engine-wide invariant hardening already lives under,
    /// and the one the LP-boost lane and solve()'s empty-core arm rely on
    /// (`run_lp_boost`'s soundness note spells out those conditional
    /// semantics). So cores extracted after a cut is installed carry the same
    /// meaning they always did, and a hard-UNSAT still means "the incumbent is
    /// optimal", not "the formula is unsatisfiable".
    ///
    /// CANONICAL EXTENSION. The selector definitions and totalizers are
    /// half-encoded (soft satisfied ⇒ selector MAY be true; `>= j` inputs
    /// violated ⇒ `out_j` true), so a SAT model may inflate `Σ` by setting
    /// those auxiliaries spuriously. Harmless in this direction: every
    /// assignment to the original variables extends to the EXACT auxiliary
    /// values, and it is that extension `(★)` is stated for — so no assignment
    /// of cost `< ub` is lost, which is precisely the property the cap needs.
    /// Same argument the `DescentEnc` doc comment makes for the
    /// original-objective encodings.
    fn descent_residual_cap(&mut self) -> Option<Weight> {
        if !descent_residual_enabled() || self.residual_exhausted {
            return None;
        }
        // No incumbent yet: nothing achievable to cap against. (The descent
        // entry gate already requires `best_model.is_some()`; belt and braces.)
        if self.ub == Weight::MAX || self.best_model.is_none() {
            return None;
        }
        if self.lb > self.ub {
            // [SOUND-CRITICAL] F4-style fail-safe; see (1) above.
            self.stats.descent_residual_abandoned =
                self.stats.descent_residual_abandoned.saturating_add(1);
            eprintln!(
                "c DESCENT-RESIDUAL-ABANDONED: lb {} exceeded reached cost ub {} — \
                 residual accounting is inconsistent; disarming the residual \
                 descent cap and falling back to the original objective",
                self.lb, self.ub
            );
            self.residual_exhausted = true;
            return None;
        }
        // `cap == 0` means `ub <= lb`: the incumbent is already provably
        // optimal and the caller's `effective_lb() >= ub` test owns that exit.
        // Asserting a zero cap here would be a contradiction, not a bound.
        (self.ub - self.lb > 0).then(|| self.ub - self.lb)
    }

    /// #descent-residual: build a fresh [`ResidualBound`] when one is warranted.
    ///
    /// Called at every descent entry, AFTER an exact encoding is in hand. Two
    /// reasons to (re)build rather than only tighten: the cap is
    /// `ub - lb_at_build`, so only a rebuild can bank the `lb` OLL has paid
    /// since — "the query shrinks as OLL works" — and the residual objective
    /// itself has been reformulated in the meantime, so a fresh cut is stated
    /// over the sum selectors the newest cores are about.
    ///
    /// Each cut is independently sound and the old ones stay in the solver
    /// (they only ever excluded models costing at least the incumbent of the
    /// day), so rebuilding is free of correctness conditions — it is bounded
    /// purely to stop a long run piling on clauses: a rebuild needs the cap to
    /// have HALVED, which caps the count logarithmically, and
    /// `RESIDUAL_MAX_BUILDS` backstops that.
    fn refresh_residual_bound(&mut self) {
        let Some(cap_r) = self.descent_residual_cap() else {
            return;
        };
        if let Some(rb) = &self.residual_bound {
            if cap_r.saturating_mul(2) > rb.last_cap {
                return;
            }
        }
        if self.residual_builds >= RESIDUAL_MAX_BUILDS {
            return;
        }
        let terms = self.residual_objective();
        // Same input ceiling the original-objective encodings use: an oversized
        // residual simply leaves the exact descent to work alone.
        if terms.is_empty() || terms.len() > GTE_CHEAP_INPUTS {
            if debug_trace() && !terms.is_empty() {
                eprintln!(
                    "c descent: residual objective too wide ({} live selectors) — no residual cut",
                    terms.len(),
                );
            }
            return;
        }
        // VACUOUS: no assignment can reach the cap, so there is nothing to
        // forbid. Detected here rather than after building an encoding for it.
        let mass = terms
            .iter()
            .fold(Weight::MIN, |acc, &(_, w)| acc.saturating_add(w));
        if mass < cap_r {
            return;
        }
        let lb_at_build = self.lb;
        let guard = self.descent_guard;
        // Uniform residual weights: the counting totalizer, much the cheapest
        // encoding of the three. Mixed weights fall back to the weighted pair
        // below rather than away from a residual cut entirely — that
        // restriction is what kept this lever off CSG, causal-discovery and
        // css-refactoring, the families it is worth the most on.
        // `force_adder` means the same thing here as for the exact encoding —
        // skip the cheaper encodings so the brute-force nets exercise the adder
        // arm, which tiny instances never reach through the budget path.
        let uniform_w = {
            let mut it = terms.iter().map(|&(_, w)| w);
            let first = it.next().unwrap_or(0);
            (first > 0 && it.all(|w| w == first) && !self.tuning.force_adder).then_some(first)
        };
        let enc = if let Some(w) = uniform_w {
            match Self::residual_units(cap_r, w, terms.len()) {
                Some(units) if terms.len().saturating_mul(units) <= 10_000_000 => {
                    let indicators: Vec<Literal> =
                        terms.iter().map(|&(s, _)| s.negated()).collect();
                    let mut tot = TotNode::build(&indicators);
                    let next_var = &mut self.next_var;
                    let mut fresh = |sat: &mut SatSolver| {
                        let var = sat.new_var();
                        *next_var = var.id() + 1;
                        sat.set_phase(var, false);
                        Literal::positive(var)
                    };
                    tot.extend(units, &mut self.sat, &mut fresh, guard);
                    let mut clause = vec![tot.outs[units - 1].negated()];
                    if let Some(g) = guard {
                        clause.push(g.negated());
                    }
                    self.sat.add_clause(clause);
                    if debug_trace() {
                        eprintln!(
                            "c descent: RESIDUAL cut = totalizer over {} selectors \
                             (w={w} cap={cap_r} units={units} lb={lb_at_build} ub={})",
                            terms.len(),
                            self.ub,
                        );
                    }
                    Some(ResidualBoundEnc::Tot {
                        tot,
                        w,
                        last_k: units,
                    })
                }
                // Unrepresentable (vacuous) or oversized: no cut. NEVER clamped
                // into range — that is failure mode (5) at the cap site.
                _ => None,
            }
        } else {
            let indicators: Vec<(Literal, Weight)> =
                terms.iter().map(|&(sel, w)| (sel.negated(), w)).collect();
            let next_var = &mut self.next_var;
            let mut fresh = |sat: &mut SatSolver| {
                let var = sat.new_var();
                *next_var = var.id() + 1;
                sat.set_phase(var, false);
                Literal::positive(var)
            };
            let mut out_budget: i64 = 400_000;
            let mut clause_budget: i64 = 4_000_000;
            let gte = if self.tuning.force_adder {
                None
            } else {
                gte_build(
                    &indicators,
                    cap_r,
                    &mut self.sat,
                    &mut fresh,
                    guard,
                    &mut out_budget,
                    &mut clause_budget,
                )
            };
            match gte {
                Some(outs) => {
                    // No clamp: a `cap_r` no output reaches leaves
                    // `forbidden_from == outs.len()` and forbids nothing.
                    let forbidden_from = outs.partition_point(|&(v, _)| v < cap_r);
                    for &(_, lit) in &outs[forbidden_from..] {
                        let mut clause = vec![lit.negated()];
                        if let Some(g) = guard {
                            clause.push(g.negated());
                        }
                        self.sat.add_clause(clause);
                    }
                    if debug_trace() {
                        eprintln!(
                            "c descent: RESIDUAL cut = GTE over {} selectors ({} outs, \
                             cap={cap_r} lb={lb_at_build} ub={})",
                            indicators.len(),
                            outs.len(),
                            self.ub,
                        );
                    }
                    Some(ResidualBoundEnc::Gte {
                        outs,
                        forbidden_from,
                    })
                }
                None => {
                    // GTE over budget (the partial Tseitin clauses it left are
                    // definitional — every assignment extends to satisfy them,
                    // so they exclude no model). Fall back to the adder, which
                    // is where the original objective ends up on exactly the
                    // families this cut matters most for.
                    let bits = adder_build(&indicators, &mut self.sat, &mut fresh, guard);
                    // No clamp: `assert_sum_le` returns early when the bound
                    // exceeds what these sum bits can represent.
                    assert_sum_le(&mut self.sat, &bits, cap_r - 1, guard);
                    if debug_trace() {
                        eprintln!(
                            "c descent: RESIDUAL cut = adder over {} selectors ({} sum bits, \
                             cap={cap_r} lb={lb_at_build} ub={})",
                            indicators.len(),
                            bits.len(),
                            self.ub,
                        );
                    }
                    Some(ResidualBoundEnc::Adder { bits })
                }
            }
        };
        if let Some(enc) = enc {
            self.residual_builds = self.residual_builds.saturating_add(1);
            self.residual_bound = Some(ResidualBound {
                enc,
                terms,
                lb_at_build,
                last_cap: cap_r,
            });
        }
    }

    /// #descent-residual: re-assert the residual cut at the current `ub`.
    ///
    /// The bound is `ub - lb_at_build` and comes ONLY from `ub` — never from a
    /// model, which for a relaxation would be unsound (see (4) at the cap site).
    /// A bound that cannot tighten, or that the encoding cannot represent, adds
    /// nothing: it is left alone, never clamped into range.
    fn tighten_residual_bound(&mut self) {
        if self.residual_exhausted {
            return;
        }
        // Taken out so the encoding can be mutated while `self.sat` /
        // `self.next_var` are borrowed.
        let Some(mut rb) = self.residual_bound.take() else {
            return;
        };
        let cap_r = self.ub.saturating_sub(rb.lb_at_build);
        if cap_r > 0 && cap_r < rb.last_cap {
            rb.last_cap = cap_r;
            let guard = self.descent_guard;
            match &mut rb.enc {
                ResidualBoundEnc::Tot { tot, w, last_k } => {
                    if let Some(units) = Self::residual_units(cap_r, *w, rb.terms.len()) {
                        if units < *last_k {
                            *last_k = units;
                            let next_var = &mut self.next_var;
                            let mut fresh = |sat: &mut SatSolver| {
                                let var = sat.new_var();
                                *next_var = var.id() + 1;
                                sat.set_phase(var, false);
                                Literal::positive(var)
                            };
                            tot.extend(units, &mut self.sat, &mut fresh, guard);
                            let mut clause = vec![tot.outs[units - 1].negated()];
                            if let Some(g) = guard {
                                clause.push(g.negated());
                            }
                            self.sat.add_clause(clause);
                        }
                    }
                }
                ResidualBoundEnc::Gte {
                    outs,
                    forbidden_from,
                } => {
                    let lo = outs.partition_point(|&(v, _)| v < cap_r);
                    for &(_, lit) in &outs[lo..*forbidden_from] {
                        let mut clause = vec![lit.negated()];
                        if let Some(g) = guard {
                            clause.push(g.negated());
                        }
                        self.sat.add_clause(clause);
                    }
                    *forbidden_from = lo.min(*forbidden_from);
                }
                ResidualBoundEnc::Adder { bits } => {
                    assert_sum_le(&mut self.sat, bits, cap_r - 1, guard);
                }
            }
        }
        self.residual_bound = Some(rb);
    }

    /// DEBUG-ONLY net for `(★)` (see [`Self::descent_residual_cap`]): the
    /// residual `Σ` evaluated on the CANONICAL extension of `model`, which is
    /// the only assignment `(★)` is stated for.
    ///
    /// A SAT model's RAW `Σ` is the wrong quantity to assert on. Both families
    /// of auxiliary are half-encoded — a soft's relaxation literal may be true
    /// while its clause holds (only `¬C ⇒ relax` is asserted), and a totalizer
    /// output may be true with fewer than `j` violated inputs (only
    /// `v >= j ⇒ out_j` is asserted) — so the raw `Σ` is an OVER-estimate and a
    /// raw assertion FALSE-ALARMS. Measured: on the cluster and lp-boost
    /// brute-force nets it fires with the whole excess attributable to
    /// relaxation literals set true over satisfied clauses (e.g. `Σ=2049`,
    /// `cost-lb=1056`, one spurious `w=993` term; removing it lands exactly on
    /// the budget). Neither direction is a soundness problem: an inflated `Σ`
    /// on the model the solver HAPPENED to return says nothing about whether a
    /// cheaper assignment survives the cut, and the canonical extension of
    /// every such assignment does survive it.
    ///
    /// So resolve each term exactly instead:
    ///   * original soft selector -> falsified iff its CLAUSE is unsatisfied;
    ///   * sum selector `¬out_j` of totalizer `t` -> falsified iff at least `j`
    ///     of `t`'s leaves are canonically true (a leaf is the indicator
    ///     `¬sel` of a selector created before `t`, so the recursion is over a
    ///     finite DAG and memoizes);
    ///   * anything else, or past the depth cap -> counted as SATISFIED.
    ///     Under-counting only weakens the assertion; it can never invent a
    ///     failure.
    #[cfg(debug_assertions)]
    fn canonical_sigma(
        &self,
        terms: impl Iterator<Item = (Literal, Weight)>,
        model: &[bool],
    ) -> Weight {
        let mut memo: HashMap<Literal, bool> = HashMap::new();
        let mut sigma: Weight = 0;
        for (sel, w) in terms {
            if self.canonical_falsified(sel, model, 0, &mut memo) {
                sigma = sigma.saturating_add(w);
            }
        }
        sigma
    }

    /// Exact value of "selector `sel` is falsified" under the canonical
    /// extension of `model`. See [`Self::canonical_sigma`].
    #[cfg(debug_assertions)]
    fn canonical_falsified(
        &self,
        sel: Literal,
        model: &[bool],
        depth: usize,
        memo: &mut HashMap<Literal, bool>,
    ) -> bool {
        if let Some(&v) = memo.get(&sel) {
            return v;
        }
        if depth > 64 {
            return false;
        }
        let val = if let Some(&i) = self.sel_to_soft.get(&sel) {
            !self
                .softs
                .get(i as usize)
                .iter()
                .any(|&lit| model.get(lit.variable().index()).copied() == Some(lit.is_positive()))
        } else if let Some(&SumRef { tot, bound }) = self.sums.get(&sel) {
            let mut leaves: Vec<Literal> = Vec::new();
            Self::tot_leaves(&self.totalizers[tot], &mut leaves);
            let violated = leaves
                .iter()
                .filter(|&&leaf| self.canonical_falsified(leaf.negated(), model, depth + 1, memo))
                .count();
            violated >= bound
        } else {
            false
        };
        memo.insert(sel, val);
        val
    }

    /// Input literals of a totalizer, in tree order. Leaves are the size-1
    /// nodes whose single output IS the input literal (see [`TotNode::build`]).
    #[cfg(debug_assertions)]
    fn tot_leaves(node: &TotNode, out: &mut Vec<Literal>) {
        match (node.left.as_deref(), node.right.as_deref()) {
            (None, None) => out.push(node.outs[0]),
            (l, r) => {
                if let Some(l) = l {
                    Self::tot_leaves(l, out);
                }
                if let Some(r) = r {
                    Self::tot_leaves(r, out);
                }
            }
        }
    }

    /// Test shim for [`Self::residual_units`] (an associated fn on a private
    /// type is otherwise unreachable from the test module).
    #[cfg(test)]
    pub(crate) fn residual_units_for_test(
        target_r: Weight,
        w: Weight,
        n_sels: usize,
    ) -> Option<usize> {
        Self::residual_units(target_r, w, n_sels)
    }

    /// Count bound for the residual encoding, derived ONLY from `ub`.
    ///
    /// Returns `None` when the bound is VACUOUS — `ceil((ub - lb) / w)` exceeds
    /// the number of encoded selectors, so no achievable count violates it. It
    /// must then not be asserted: clamping it into range is exactly the bug
    /// that produced ten wrong answers.
    fn residual_units(target_r: Weight, w: Weight, n_sels: usize) -> Option<usize> {
        if target_r == 0 {
            return None;
        }
        let units = target_r.div_ceil(w.max(1)) as usize;
        (units >= 1 && units <= n_sels).then_some(units)
    }

    /// DIAGNOSTIC ONLY — never changes search. Checks the engine's cost
    /// identity against a real model:
    ///
    ///   cost(A) = lb + Σ_{sel ∈ active ∪ pool} w_sel·[sel falsified] + T(A)
    ///
    /// with the ladder term `T(A) >= 0`, so the testable consequence is
    /// `Σ <= cost - lb`. A `#descent-residual` attempt that bounded `Σ` by
    /// `ub - lb` produced TEN wrong answers (all optima overshot by +1..+15 on
    /// protein_ins/rna-alignment), which means this inequality does NOT hold
    /// for the naive `active ∪ pool` scan. This prints the actual numbers so
    /// the violating term can be identified instead of guessed at.
    fn report_residual_identity(&self, model: &[bool], cost: Weight) {
        let falsified =
            |sel: Literal| model.get(sel.variable().index()).copied() != Some(sel.is_positive());
        let mut sigma_active: Weight = 0;
        let mut sigma_active_hardened: Weight = 0;
        let mut n_act = 0usize;
        for (&sel, &w) in self.active.iter() {
            if falsified(sel) {
                if self.hardened_sels.contains(&sel) {
                    sigma_active_hardened = sigma_active_hardened.saturating_add(w);
                } else {
                    sigma_active = sigma_active.saturating_add(w);
                }
                n_act += 1;
            }
        }
        let mut sigma_pool: Weight = 0;
        for (sel, w) in self.pool.iter() {
            if falsified(*sel) {
                sigma_pool = sigma_pool.saturating_add(*w);
            }
        }
        // Same quantity restricted to ORIGINAL soft selectors, to separate the
        // original-soft terms from the relax_core sum-selector terms.
        let orig: HashSet<Literal> = self.soft_selectors.iter().copied().collect();
        let mut sigma_orig: Weight = 0;
        let mut sigma_sum: Weight = 0;
        for (&sel, &w) in self.active.iter() {
            if falsified(sel) && !self.hardened_sels.contains(&sel) {
                if orig.contains(&sel) {
                    sigma_orig = sigma_orig.saturating_add(w);
                } else {
                    sigma_sum = sigma_sum.saturating_add(w);
                }
            }
        }
        let sigma = sigma_active.saturating_add(sigma_pool);
        let budget = cost.saturating_sub(self.lb);
        eprintln!(
            "c identity: cost={cost} lb={} budget=cost-lb={budget} sigma={sigma}              (active={sigma_active} pool={sigma_pool} orig={sigma_orig} sum_sel={sigma_sum}              hardened_falsified={sigma_active_hardened} n_falsified_active={n_act})              HOLDS={}",
            self.lb,
            sigma <= budget,
        );
    }

    /// Build (once) the descent encoding for this instance, plus the
    /// #descent-residual side constraint that strengthens it.
    ///
    /// The two are INDEPENDENT. `select_descent_enc` picks the EXACT encoding
    /// of the original objective — that is what makes every SAT model strictly
    /// improve `ub`, so the descent's walk keeps working. `refresh_residual_bound`
    /// then adds a redundant cut over the REFORMULATED residual objective at the
    /// far tighter cap `ub - lb`, which is what the closing UNSAT call needs.
    /// See `ResidualBound` for why this is additive rather than a replacement.
    fn ensure_descent_enc(&mut self) -> bool {
        if !self.select_descent_enc() {
            return false;
        }
        self.refresh_residual_bound();
        true
    }

    /// Pick (once) the best-fitting EXACT descent encoding for this instance:
    /// totalizer for uniform weights, GTE for small mixed-weight instances,
    /// adder network otherwise. Returns false when none is available.
    fn select_descent_enc(&mut self) -> bool {
        if self.descent.is_some() {
            return true;
        }
        if !self.descent_reachable() {
            return false;
        }
        // #cold-core-descent D6: the size budgets below are state-dependent, so
        // declining on one must NOT poison `descent_unavailable`. Record the
        // signature instead; `descent_reachable` re-opens the gate once the
        // residual has strictly shrunk.
        let size_sig = (self.hardened_sels.len(), self.ub);
        // A/B runs on both MSE 2024 tracks showed guarding the descent
        // clauses behind an activation literal costs more (weaker
        // propagation inside the descent) than it saves in OLL cleanliness;
        // descents commit anyway, so emit unguarded clauses.
        let guard: Option<Literal> = None;
        // Residual problem: hardened softs are satisfied in every remaining
        // model, contribute zero cost, and would only bloat the encodings —
        // judge weight shape and build over the live remainder. drmx-style
        // instances with weights {1, W} become uniform weight-1 after the
        // top stratum hardens, unlocking the totalizer descent.
        let soft_idx: Vec<usize> = (0..self.softs.len())
            .filter(|&i| !self.hardened_sels.contains(&self.soft_selectors[i]))
            .collect();
        if soft_idx.is_empty() {
            self.descent_unavailable = true;
            return false;
        }
        let uniform_w = {
            let mut it = soft_idx.iter().map(|&i| self.soft_weights[i]);
            let first = it.next().unwrap_or(0);
            (first > 0 && it.all(|w| w == first)).then_some(first)
        };
        if let Some(w) = uniform_w {
            let gap_units = (self
                .ub
                .saturating_sub(self.preproc_cost)
                .div_euclid(w.max(1)))
            .min(soft_idx.len() as Weight) as usize;
            if soft_idx.len().saturating_mul(gap_units) <= 10_000_000 {
                let indicators: Vec<Literal> = soft_idx
                    .iter()
                    .map(|&i| self.soft_selectors[i].negated())
                    .collect();
                if debug_trace() {
                    eprintln!(
                        "c descent: totalizer over {} residual softs (w={})",
                        indicators.len(),
                        w
                    );
                }
                self.descent = Some(DescentEnc::Tot {
                    tot: TotNode::build(&indicators),
                    w,
                    soft_idx,
                });
                return true;
            }
            // SIZE decline (#cold-core-descent D6), not a permanent one:
            // `soft_idx` shrinks with every hardened soft and `gap_units`
            // falls with every ub improvement.
            self.descent_size_declined = Some(size_sig);
            return false;
        }

        let inputs: Vec<(Literal, Weight)> = soft_idx
            .iter()
            .map(|&i| (self.soft_selectors[i].negated(), self.soft_weights[i]))
            .collect();
        if inputs.is_empty() || inputs.len() > 10_000 {
            // SIZE decline (#cold-core-descent D6): `inputs` is the live
            // residual, so hardening can bring this under the budget later.
            self.descent_size_declined = Some(size_sig);
            return false;
        }
        let cap = self.ub.saturating_sub(self.preproc_cost);
        if cap == 0 {
            // lb >= ub is handled by the caller before descending.
            self.descent_unavailable = true;
            return false;
        }

        if inputs.len() <= 10_000 && !self.tuning.force_adder && !self.tuning.force_cluster {
            // #dpw-descent: DECIDE BEFORE EMITTING. Both sizes are computed by
            // closed-form predictors that never touch the solver — `dpw_size`
            // from the bucket shape, `gte_size` as an exact mirror of
            // `gte_build`'s own recursion and budget bails. So the loser costs
            // no variables, no clauses and no rollback, and `gte_size`
            // declining is by construction the same statement as `gte_build`
            // declining.
            //
            // DPW is ADDITIONAL, never a replacement: it is taken only where
            // the GTE would have built AND is at least `DPW_MIN_ADVANTAGE`
            // times bigger. Where the GTE declines on budget, today's
            // cluster/adder fallback is left exactly as it was — extending DPW
            // into that regime is a separate, separately measurable change.
            if dpw_enabled() {
                // `cap` is `ub - preproc_cost`; the descent asserts
                // `cost < ub`, i.e. violated weight <= cap - 1, so the loosest
                // bound the structure will ever carry is `cap - 1`.
                let k_init = cap - 1;
                let live_weights: Vec<Weight> =
                    inputs.iter().map(|&(_, w)| w).filter(|&w| w > 0).collect();
                let dpw_predicted = (!live_weights.is_empty())
                    .then(|| dpw_size(&live_weights, k_init, DPW_VAR_BUDGET, DPW_CLAUSE_BUDGET))
                    .flatten();
                if let Some(dpw_predicted) = dpw_predicted {
                    let mut probe_outs: i64 = 400_000;
                    let mut probe_clauses: i64 = 4_000_000;
                    let gte_predicted = gte_size(&inputs, cap, &mut probe_outs, &mut probe_clauses);
                    let take = if self.tuning.force_dpw {
                        true
                    } else {
                        gte_predicted.is_some_and(|(_, gte_clauses, _)| {
                            dpw_beats_gte(dpw_predicted.clauses, gte_clauses)
                        })
                    };
                    if take {
                        let next_var = &mut self.next_var;
                        let mut fresh = |sat: &mut SatSolver| {
                            let var = sat.new_var();
                            *next_var = var.id() + 1;
                            sat.set_phase(var, false);
                            Literal::positive(var)
                        };
                        if let Some(enc) =
                            DpwEnc::build(&inputs, k_init, &mut self.sat, &mut fresh, guard)
                        {
                            debug_assert_eq!(
                                enc.size, dpw_predicted,
                                "DPW predictor disagreed with the emitted build; the \
                                 budget gate was decided on a fiction",
                            );
                            if debug_trace() {
                                let gte_note = match gte_predicted {
                                    Some((v, c, o)) => {
                                        format!("GTE would be {v} vars / {c} clauses / {o} outs")
                                    }
                                    None => "GTE declines on budget".to_string(),
                                };
                                eprintln!(
                                    "c descent: DPW over {} softs ({} levels, 2^{} top \
                                     granularity, {} top outs, {} vars, {} clauses, cap {}) \
                                     [{gte_note}]",
                                    inputs.len(),
                                    enc.levels(),
                                    enc.levels() - 1,
                                    enc.size.top_width,
                                    enc.size.vars,
                                    enc.size.clauses,
                                    cap,
                                );
                            }
                            // NO bound clauses here, by design: the bound is an
                            // assumption vector rebuilt every descent round.
                            self.descent = Some(DescentEnc::Dpw { enc, k_last: None });
                            return true;
                        }
                    }
                }
            }

            let next_var = &mut self.next_var;
            let mut fresh = |sat: &mut SatSolver| {
                let var = sat.new_var();
                *next_var = var.id() + 1;
                sat.set_phase(var, false);
                Literal::positive(var)
            };
            let mut out_budget: i64 = 400_000;
            let mut clause_budget: i64 = 4_000_000;
            if let Some(outs) = gte_build(
                &inputs,
                cap,
                &mut self.sat,
                &mut fresh,
                guard,
                &mut out_budget,
                &mut clause_budget,
            ) {
                // Forbid total violated weight >= cap immediately.
                let forbidden_from = outs.partition_point(|&(v, _)| v < cap);
                for &(_, lit) in &outs[forbidden_from..] {
                    let mut clause = vec![lit.negated()];
                    if let Some(g) = guard {
                        clause.push(g.negated());
                    }
                    self.sat.add_clause(clause);
                }
                if debug_trace() {
                    eprintln!(
                        "c descent: GTE over {} softs ({} outs, cap {})",
                        inputs.len(),
                        outs.len(),
                        cap
                    );
                }
                self.descent = Some(DescentEnc::Gte {
                    outs,
                    forbidden_from,
                });
                return true;
            }
        }

        // Near-uniform cluster descent (#cluster-descent): rounded-weight
        // families (correlation-clustering: 77-87% of softs within 10% of
        // the modal 50000, plus a small-weight dust tail) fail the exact
        // uniform test AND blow the GTE build budget above (~2000 distinct
        // weights at multi-million caps), previously landing on the
        // propagation-dead wide adder. Runs strictly as the GTE's fallback:
        // stride A/B showed preempting a buildable (exact) GTE loses. A count totalizer
        // over just the band members is cheap and cuts hard.
        {
            let mut mass_by_w: HashMap<Weight, Weight> = HashMap::new();
            let mut total_mass: Weight = 0;
            for &i in &soft_idx {
                let w = self.soft_weights[i];
                *mass_by_w.entry(w).or_insert(0) += w;
                total_mass = total_mass.saturating_add(w);
            }
            if let Some((&modal_w, _)) = mass_by_w.iter().max_by_key(|(_, &m)| m) {
                let band_min = modal_w.saturating_sub(modal_w / 10);
                let band_max = modal_w.saturating_add(modal_w / 10);
                let member_idx: Vec<usize> = soft_idx
                    .iter()
                    .copied()
                    .filter(|&i| {
                        let w = self.soft_weights[i];
                        w >= band_min && w <= band_max
                    })
                    .collect();
                let band_mass: Weight = member_idx
                    .iter()
                    .map(|&i| self.soft_weights[i])
                    .fold(0, |a, w| a.saturating_add(w));
                let cap = self.ub.saturating_sub(self.preproc_cost);
                let k0 = cap
                    .div_ceil(band_min.max(1))
                    .min(member_idx.len() as Weight) as usize;
                // Aggressive test tunings force tiny instances down the
                // descent paths; relax the member floor so the cluster
                // branch is exercised by the brute-force nets.
                let min_members = if self.tuning.lsu_stall_ms_per_core == 0 {
                    4
                } else {
                    64
                };
                // GTE-hostile shapes only: with few distinct weights the
                // GTE/adder handle the instance better (measured: the
                // cluster walk lost causal-discovery/haplotyping/tcp
                // stall-gate wins when allowed to intercept them). The
                // rounded-similarity families that NEED this path carry
                // hundreds-to-thousands of distinct near-modal weights.
                // DEFAULT OFF (2026-07-12 stride verdicts): the count walk
                // reaches exact-optimum INCUMBENTS on correlation-clustering
                // (previously +17%) but cannot prove them, while intercepting
                // GTE-declined instances the adder was solving (-2 net at
                // every tried gate: preempt-GTE, post-GTE, distinct>=200).
                // Machinery + nets stay in-tree; the promising continuation
                // is the PROOF side — register the cluster totalizer as an
                // OLL sum so cores/exhaustion raise lb in band_min steps
                // while the walk lowers ub over the SAME encoding.
                let distinct_hostile = self.tuning.force_cluster;
                if member_idx.len() >= min_members
                    && distinct_hostile
                    && band_mass.saturating_mul(4) >= total_mass.saturating_mul(3)
                    && band_min > 0
                    && member_idx.len().saturating_mul(k0) <= 10_000_000
                {
                    let indicators: Vec<Literal> = member_idx
                        .iter()
                        .map(|&i| self.soft_selectors[i].negated())
                        .collect();
                    if debug_trace() {
                        eprintln!(
                            "c descent: cluster totalizer over {} of {} softs \
                             (band_min={} modal={} mass {}%)",
                            member_idx.len(),
                            soft_idx.len(),
                            band_min,
                            modal_w,
                            band_mass.saturating_mul(100) / total_mass.max(1),
                        );
                    }
                    self.descent = Some(DescentEnc::ClusterTot {
                        tot: TotNode::build(&indicators),
                        band_min,
                        member_idx,
                        last_k: usize::MAX,
                    });
                    return true;
                }
            }
        }

        let next_var = &mut self.next_var;
        let mut fresh = |sat: &mut SatSolver| {
            let var = sat.new_var();
            *next_var = var.id() + 1;
            sat.set_phase(var, false);
            Literal::positive(var)
        };
        let bits = adder_build(&inputs, &mut self.sat, &mut fresh, guard);
        assert_sum_le(&mut self.sat, &bits, cap - 1, guard);
        if debug_trace() {
            eprintln!(
                "c descent: adder over {} softs ({} sum bits, cap {})",
                inputs.len(),
                bits.len(),
                cap
            );
        }
        self.descent = Some(DescentEnc::Adder { bits, bound: cap });
        true
    }

    /// One time-sliced solution-improving descent: repeatedly solve the
    /// current formula (no assumptions), keep improving models, and add a
    /// hard bound excluding costs >= the new incumbent. Returns
    /// `Some(outcome)` on a terminal answer, `None` when the slice expired
    /// (caller resumes OLL; the encoding and bounds persist).
    ///
    /// #cold-core-descent D1: the descent walks the UB side and never calls
    /// `process_core`, so no core can arrive here BY CONSTRUCTION. The drought
    /// clock is therefore stopped for the whole slice — charging descent time
    /// as "core discovery has gone cold" lets a descent slice manufacture the
    /// very drought that justifies the next, longer entry, a self-triggering
    /// ratchet. The discipline lives HERE rather than at the call site so it
    /// cannot be lost by a future caller.
    fn descend(
        &mut self,
        deadline: Instant,
        should_stop: &dyn Fn() -> bool,
        on_upper_bound: &mut dyn FnMut(Weight),
    ) -> Option<OllOutcome> {
        self.pause_core_drought();
        let outcome = self.descend_slice(deadline, should_stop, on_upper_bound);
        if outcome.is_none() {
            // Slice expired and OLL resumes: the pre-descent drought is still
            // real evidence, so the clock CONTINUES rather than restarting.
            self.resume_core_drought();
        }
        outcome
    }

    /// The descent slice proper. Call [`Self::descend`], not this.
    fn descend_slice(
        &mut self,
        deadline: Instant,
        should_stop: &dyn Fn() -> bool,
        on_upper_bound: &mut dyn FnMut(Weight),
    ) -> Option<OllOutcome> {
        let guard = self.descent_guard;
        loop {
            if should_stop() {
                return Some(OllOutcome::Unknown { best: self.best() });
            }
            if Instant::now() >= deadline {
                return None;
            }
            self.stats.sat_calls = self.stats.sat_calls.saturating_add(1);
            self.stats.lsu_steps = self.stats.lsu_steps.saturating_add(1);
            let slice_stop = || should_stop() || Instant::now() >= deadline;
            let mut assumptions: Vec<Literal> = self.descent_guard.into_iter().collect();
            // #dpw-descent: THE ONE PLACE the watchdog's bound literals may
            // appear. Every other `DescentEnc` states its bound as hard
            // clauses; DPW cannot, because the tare constant is non-monotone
            // in `k`. Recomputed from the CURRENT `ub` each round, so a round
            // that improved the incumbent tightens for free.
            //
            // The bound is `violated weight <= target - 1`, matching the GTE
            // arm's "forbid sums >= cap" exactly. An empty bound part means
            // VACUOUS — the structure cannot represent a violation of `k`, so
            // every model already costs `< ub` and the next round is
            // guaranteed to improve. It must never be clamped into range.
            if let Some(DescentEnc::Dpw { enc, .. }) = self.descent.as_ref() {
                let target = self.ub.saturating_sub(self.preproc_cost);
                if target > 0 {
                    assumptions.extend(enc.assumptions(target - 1));
                }
            }
            let result = self
                .sat
                .solve_with_assumptions_interruptible(&assumptions, &slice_stop)
                .into_inner();
            match result {
                AssumeResult::Sat(model) => {
                    let cost = self.model_cost(&model);
                    if identity_check_enabled() {
                        self.report_residual_identity(&model, cost);
                    }
                    if debug_trace() {
                        eprintln!("c descent sat: cost={} ub={}", cost, self.ub);
                    }
                    if cost < self.ub {
                        self.ub = cost;
                        self.ub_last_improved = Instant::now();
                        self.best_model = Some(model.clone());
                        on_upper_bound(cost);
                        self.harden();
                    }
                    if self.effective_lb() >= self.ub {
                        return Some(self.optimal());
                    }
                    let target = self.ub.saturating_sub(self.preproc_cost);
                    if target == 0 {
                        return Some(self.optimal());
                    }
                    // #descent-residual [SOUND-CRITICAL, debug builds]: the
                    // relaxation's defining inequality `(★)` (see
                    // `descent_residual_cap`), checked against a REAL model
                    // rather than argued on paper. The first version of this
                    // lever shipped a valid proof and ten wrong answers, and
                    // the brute-force suite passed it because its instances
                    // never enter the regime where the bound bites. Lives here,
                    // ahead of the `as_mut()` borrow below, because it needs
                    // `&self` for the canonical evaluation.
                    #[cfg(debug_assertions)]
                    {
                        if let Some(rb) = self.residual_bound.as_ref() {
                            let sigma = self.canonical_sigma(rb.terms.iter().copied(), &model);
                            assert!(
                                sigma <= cost.saturating_sub(rb.lb_at_build),
                                "residual identity violated: Σ={sigma} > cost({cost}) - \
                                 lb_at_build({}); the residual descent cut is UNSOUND \
                                 on this instance",
                                rb.lb_at_build,
                            );
                        }
                    }
                    // #descent-residual: re-assert the redundant residual cut at
                    // the new `ub`, alongside the exact tighten below.
                    self.tighten_residual_bound();
                    // Tighten the bound below the fresh model's cost.
                    match self.descent.as_mut().expect("descent encoding present") {
                        DescentEnc::Tot { tot, w, soft_idx } => {
                            // Count violations over the residual softs the
                            // encoding covers; hardened softs are satisfied
                            // and contribute zero either way.
                            let k = soft_idx
                                .iter()
                                .filter(|&&i| {
                                    !self.softs.get(i).iter().any(|&lit| {
                                        model.get(lit.variable().index()).copied()
                                            == Some(lit.is_positive())
                                    })
                                })
                                .count();
                            debug_assert_eq!(
                                cost,
                                self.preproc_cost
                                    .saturating_add(w.saturating_mul(k as Weight)),
                                "uniform-weight cost decomposition must be exact",
                            );
                            if k == 0 {
                                return Some(self.optimal());
                            }
                            // Exclude exactly cost >= ub: viols >= ceil(target/w).
                            // Rounding DOWN here would exclude models with
                            // cost in [w*floor(target/w), ub) — cheaper than
                            // the incumbent — and is unsound.
                            let incumbent_units = target.div_ceil((*w).max(1)) as usize;
                            let k_bound = k.min(incumbent_units).max(1);
                            let next_var = &mut self.next_var;
                            let mut fresh = |sat: &mut SatSolver| {
                                let var = sat.new_var();
                                *next_var = var.id() + 1;
                                sat.set_phase(var, false);
                                Literal::positive(var)
                            };
                            tot.extend(k_bound, &mut self.sat, &mut fresh, guard);
                            let mut clause = vec![tot.outs[k_bound - 1].negated()];
                            if let Some(g) = guard {
                                clause.push(g.negated());
                            }
                            self.sat.add_clause(clause);
                        }
                        DescentEnc::ClusterTot {
                            tot,
                            band_min,
                            member_idx,
                            last_k,
                        } => {
                            // Sound bound (see enum docs): cost < ub implies
                            // cluster violations < ceil(target / band_min).
                            //
                            // This is a RELAXATION — the off-band "dust" softs
                            // carry cost the cluster totalizer does not count —
                            // so the bound may only ever come from `ub`, and a
                            // bound too large to be represented is VACUOUS.
                            // Clamping it into range with `.min(member_idx.len())`
                            // would forbid "every member violated", a model that
                            // can still be cheaper than the incumbent. That is
                            // exactly the mistake that made #descent-residual
                            // produce ten wrong answers (see `ResidualBound`);
                            // it is unreachable here only because this path is
                            // gated behind `tuning.force_cluster` (default OFF).
                            // A vacuous bound falls through to the exact-adder
                            // swap below rather than being asserted.
                            let units = (target.div_ceil((*band_min).max(1)) as usize).max(1);
                            let k_bound = if units <= member_idx.len() {
                                units
                            } else {
                                usize::MAX
                            };
                            if k_bound < *last_k {
                                *last_k = k_bound;
                                let next_var = &mut self.next_var;
                                let mut fresh = |sat: &mut SatSolver| {
                                    let var = sat.new_var();
                                    *next_var = var.id() + 1;
                                    sat.set_phase(var, false);
                                    Literal::positive(var)
                                };
                                tot.extend(k_bound, &mut self.sat, &mut fresh, guard);
                                let mut clause = vec![tot.outs[k_bound - 1].negated()];
                                if let Some(g) = guard {
                                    clause.push(g.negated());
                                }
                                self.sat.add_clause(clause);
                            } else {
                                // The count bound cannot tighten further
                                // (dust-driven ub progress): swap to the
                                // exact adder so every round strictly cuts
                                // the incumbent — a same-bound re-solve
                                // would return the same model forever
                                // inside the one-way commit.
                                let inputs: Vec<(Literal, Weight)> = (0..self.softs.len())
                                    .filter(|&i| {
                                        !self.hardened_sels.contains(&self.soft_selectors[i])
                                    })
                                    .map(|i| {
                                        (self.soft_selectors[i].negated(), self.soft_weights[i])
                                    })
                                    .collect();
                                let next_var = &mut self.next_var;
                                let mut fresh = |sat: &mut SatSolver| {
                                    let var = sat.new_var();
                                    *next_var = var.id() + 1;
                                    sat.set_phase(var, false);
                                    Literal::positive(var)
                                };
                                let bits = adder_build(&inputs, &mut self.sat, &mut fresh, guard);
                                assert_sum_le(&mut self.sat, &bits, target - 1, guard);
                                if debug_trace() {
                                    eprintln!(
                                        "c descent: cluster count exhausted at k={k_bound}, \
                                         swapping to adder (target={target})"
                                    );
                                }
                                self.descent = Some(DescentEnc::Adder {
                                    bits,
                                    bound: target,
                                });
                            }
                        }
                        DescentEnc::Gte {
                            outs,
                            forbidden_from,
                        } => {
                            let lo = outs.partition_point(|&(v, _)| v < target);
                            for &(_, lit) in &outs[lo..*forbidden_from] {
                                let mut clause = vec![lit.negated()];
                                if let Some(g) = guard {
                                    clause.push(g.negated());
                                }
                                self.sat.add_clause(clause);
                            }
                            *forbidden_from = lo.min(*forbidden_from);
                        }
                        DescentEnc::Adder { bits, bound } => {
                            if target < *bound {
                                *bound = target;
                                let bits = bits.clone();
                                assert_sum_le(&mut self.sat, &bits, target - 1, guard);
                            }
                        }
                        DescentEnc::Dpw { enc: _, k_last } => {
                            // ZERO clauses — the whole reason the encoding
                            // exists. The four (generally p) assumption
                            // literals rebuilt at the top of the loop carry
                            // the new bound; `sat.add_clause` must NOT be
                            // called here, and committing the tare as units
                            // would be unsound because `T*` is non-monotone
                            // in `k`.
                            let k = target - 1;
                            debug_assert!(
                                k_last.is_none_or(|prev| k < prev),
                                "descent round did not tighten: k {k} vs {k_last:?}",
                            );
                            *k_last = Some(k);
                        }
                    }
                }
                AssumeResult::Unsat(..) => {
                    // No model beats the incumbent: it is optimal.
                    if debug_trace() {
                        eprintln!("c descent unsat: ub={} -> optimal", self.ub);
                    }
                    return Some(self.optimal());
                }
                _ => {
                    // Interrupted: global stop => terminal; slice expiry =>
                    // suspend back to OLL.
                    if should_stop() {
                        return Some(OllOutcome::Unknown { best: self.best() });
                    }
                    return None;
                }
            }
        }
    }

    /// Run OLL to optimality or interruption.
    ///
    /// `should_stop` is polled inside SAT calls and between iterations.
    /// `on_upper_bound` is invoked whenever the incumbent improves.
    /// Supply the whole-solve deadline (see `MaxSatSolver::set_deadline`).
    pub(crate) fn set_deadline(&mut self, deadline: Option<Instant>) {
        self.deadline = deadline;
    }

    /// Budget remaining, when the caller supplied a deadline.
    ///
    /// This is the one piece of information the engine historically lacked, and
    /// its absence is why every internal policy is a fixed constant tuned at a
    /// single timeout. Returns `None` when budget-blind, and callers MUST fall
    /// back to their previous fixed behaviour in that case so nothing changes
    /// for callers that never set a deadline.
    fn budget_remaining(&self) -> Option<Duration> {
        self.deadline
            .map(|d| d.saturating_duration_since(Instant::now()))
    }

    pub(crate) fn solve(
        &mut self,
        should_stop: &dyn Fn() -> bool,
        on_upper_bound: &mut dyn FnMut(Weight),
    ) -> OllOutcome {
        let started = Instant::now();
        let mut exhaust_spent = Duration::ZERO;
        let mut minimize_spent = Duration::ZERO;
        let mut am1_probe_spent = Duration::ZERO;
        let band_set = self.form_band_abstraction();
        // #climit-discipline: schedule the first level from the live weight
        // histogram. Uniform-weight instances (the unweighted track) get
        // level 1 immediately — one level, nothing ever filtered.
        self.level = self.next_level();
        self.stats.strat_levels = self.stats.strat_levels.saturating_add(1);
        self.activate_stratum(self.level);

        self.pay_mined_cores();

        // Sum selectors created since the last SAT answer. They are not
        // assumed yet ("totalizer delay"): the solver keeps discovering
        // disjoint cores among the remaining selectors without fighting the
        // freshly added cardinality bounds, and all delayed selectors are
        // activated together once the phase reaches SAT.
        let mut suspended: HashSet<Literal> = HashSet::new();

        // After abstraction sets form, give the abstracted OLL loop a grace
        // window before the descent switch may commit.
        let mut descent_not_before = started;

        // #maxsat-am1-probe eager init: the level-change probe (below, in the
        // Sat branch) never fires on single-stratum instances — uniform-weight
        // (unweighted) formulas get exactly one level, so the level never
        // changes and UP-refuted units are found only by full SAT solves
        // (MaxSATQueriesinInterpretableClassifiers: 50 size-1 cores at ~1s each
        // = timeout, vs CGSS2's up-front calc_conns sweep = 2s). Run ONE probe
        // pass after the first solve attaches watches; if it hardens units,
        // re-solve fresh so the extracted core reflects the tightened state.
        let mut initial_probe_done = false;
        // #frb-bmo-probe-after-solve: set at level changes; the AM1 probe
        // runs after the NEXT solve so its prologue attaches/propagates the
        // clauses and hardened units added at the change.
        let mut am1_probe_pending = false;
        // #fold-descent-kick: one-shot descent engagement after a clique
        // fold lands lb within the endgame band (see the probe block).
        let mut descent_kick = false;
        // #cold-core-descent: one-shot trace of the rate signal (see the gate).
        let mut cold_signal_traced = false;

        // Exhaust the band set immediately: each UNSAT probe proves one more
        // forced violation among the band members and lifts lb by band_min.
        if let Some(sel) = band_set {
            if self.active.contains_key(&sel) {
                let t0 = Instant::now();
                if !self.exhaust_sum(sel, &mut suspended, should_stop) {
                    return match self.best_model {
                        Some(_) => self.optimal(),
                        None => OllOutcome::Unsatisfiable,
                    };
                }
                exhaust_spent += t0.elapsed();
            }
        }

        loop {
            if should_stop() {
                return OllOutcome::Unknown { best: self.best() };
            }

            // Value-based stall gate (#value-stall-gate): judge OLL by the
            // lb it actually delivers, not by time-per-core. The old flat
            // wall-clock test (elapsed >= 30ms * max(cores, 64)) fired at
            // 1.92s on 0.5-2M-clause formulas whose FIRST SAT call is that
            // slow (descent then committed with lb ~ 0) and never fired on
            // tiny mpe instances streaming thousands of near-worthless
            // w_min 2-6 cores. Now: roll a ~5s lb observation window;
            // stalling when the last completed window gained less than
            // gap/12 (the close-within-a-minute pace). No completed window
            // yet => not stalling, so slow first solves cannot trip it.
            // `lsu_stall_ms_per_core == 0` (aggressive test tunings) still
            // forces the descent path so the brute-force nets exercise the
            // LSU/GTE/adder encodings on tiny instances. The old formula's
            // `lsu_min_cores` floor lives on as a separate conjunct of the
            // descent entry gate below.
            let now_gate = Instant::now();
            match self.lb_window {
                None => self.lb_window = Some((now_gate, self.lb)),
                Some((t0, lb0)) => {
                    if now_gate.duration_since(t0) >= Duration::from_secs(5) {
                        self.lb_last_window_gain = Some(self.lb.saturating_sub(lb0));
                        self.lb_window = Some((now_gate, self.lb));
                    }
                }
            }
            let oll_stalling = self.tuning.lsu_stall_ms_per_core == 0
                || match self.lb_last_window_gain {
                    Some(gain) => gain < (self.ub.saturating_sub(self.lb) / 12).max(1),
                    None => false,
                };
            let gap_ok = match self.descent {
                // Uniform totalizer descent keeps the original entry bar.
                None => {
                    let mut it = self.soft_weights.iter();
                    let first = it.next().copied().unwrap_or(0);
                    if first > 0 && it.all(|&w| w == first) {
                        self.ub.saturating_sub(self.lb)
                            > first.saturating_mul(self.tuning.lsu_min_gap_units)
                    } else {
                        self.ub > self.lb
                    }
                }
                Some(_) => self.ub > self.lb,
            };
            // Abstract cores (v3 trigger): form sets EARLY — as soon as
            // enough core structure is observed — rather than one-shot at
            // stall (v1/v2 measured neutral there: the recorded cores were
            // already consumed and a descent commit was ~15s away). Then
            // exhaust each fresh set selector immediately so forced
            // violations inside a set raise the lower bound before search
            // resumes at the set level.
            if !self.abstraction_done && self.stats.cores_found >= self.tuning.abstraction_min_cores
            {
                self.abstraction_done = true;
                let new_sets = self.form_abstraction_sets();
                if !new_sets.is_empty() {
                    for sel in new_sets {
                        if should_stop() {
                            break;
                        }
                        if !self.exhaust_sum(sel, &mut suspended, should_stop) {
                            return match self.best_model {
                                Some(_) => self.optimal(),
                                None => OllOutcome::Unsatisfiable,
                            };
                        }
                    }
                    descent_not_before = Instant::now() + Duration::from_secs(15);
                    continue;
                }
            }

            // #lp-boost: certified dual-packing bound over the stored
            // pure-original cores. First round at the stall gate — before
            // any (one-way) descent commit below — then at most every
            // LP_BOOST_CORE_STRIDE cores; auto-disables after
            // LP_BOOST_MAX_DRY_ROUNDS rounds without improvement. Each call
            // is budgeted (P0b) so a stuck simplex cannot eat the run.
            if self.lp_boost_due(oll_stalling) {
                // #wce flush (c): run the LP round against the materialized
                // encoding, with any lb/ub motion from the flush exhausts
                // already applied (see flush_pending for the flush-point
                // rationale).
                if !self.flush_pending(
                    &mut suspended,
                    true,
                    started,
                    &mut exhaust_spent,
                    should_stop,
                ) {
                    return match self.best_model {
                        Some(_) => self.optimal(),
                        None => OllOutcome::Unsatisfiable,
                    };
                }
                self.run_lp_boost(should_stop);
                if self.best_model.is_some() && self.effective_lb() >= self.ub {
                    return self.optimal();
                }
            }

            // `lsu_min_cores` survives the old formula's rework as its own
            // conjunct: the descent may not engage until at least that many
            // cores have been processed (u64::MAX in the pure-OLL test
            // tunings keeps descents away entirely; 0 in the aggressive
            // tunings imposes no core-count bar).
            // #ub-stale-descent: when the incumbent has been frozen for a
            // while with a small remaining gap, lb progress alone can never
            // finish (the optimum may lie strictly below ub, and lb cannot
            // exceed the optimum) — the run NEEDS a model improvement, which
            // only a descent provides once assumption solves all come back
            // UNSAT. The lb-stall gate misses this state when cores keep
            // paying steadily (protein_ins: lb +1.3/s, ub frozen from t≈8s,
            // optimum 15 below ub, cores_found ~26 < the 64 floor). Uses the
            // reversible KICK path (10s slice; OLL resumes on expiry) and
            // honors descent_not_before so an unproductive slice cannot
            // re-enter for 15s.
            // The kick bar is SCALE-RELATIVE (see `descent_kick_gap_cap`): a
            // flat `ub - lb <= 32` is a dimensional error against a track whose
            // optima span ten orders of magnitude, and it shuts the kick for
            // the entire run on 44% of the addressable set. This subsumes the
            // retired `#descent-gap-tile` flag, whose widening only reached the
            // uniform-weight arm and so was inert on mixed-weight families.
            let kick_gap_cap = self.descent_kick_gap_cap();
            if !descent_kick
                && self.best_model.is_some()
                && self.ub.saturating_sub(self.effective_lb()) <= kick_gap_cap
                && Instant::now() >= descent_not_before
                && (self.ub_last_improved.elapsed() > Duration::from_secs(15)
                    && started.elapsed() > Duration::from_secs(20))
            {
                descent_kick = true;
            }
            // #expensive-core-descent: the organic 20s/15s floors above are
            // calibrated for cheap-core instances; on a large hard formula each
            // assumption solve costs ~1s, so OLL neither reaches the 64-core
            // organic bar nor those floors within budget, yet the reversible
            // totalizer descent converges from the ub side in a handful of
            // solves. Bring the kick forward once cores are demonstrably
            // expensive (mean solve >= EXPENSIVE_CORE_MS over >= 8 cores), the
            // gap is already small, and the live residual is uniform-weight (so
            // the descent encoding is the cheap totalizer). A dry 10s slice
            // returns to OLL, so a mis-fire costs at most one slice.
            if !descent_kick
                && maxsat_early_descent_enabled()
                && self.best_model.is_some()
                && self.ub.saturating_sub(self.effective_lb()) <= kick_gap_cap
                && Instant::now() >= descent_not_before
                && self.stats.cores_found >= 8
                && started.elapsed() > Duration::from_secs(4)
                && (started.elapsed().as_millis() as u64)
                    >= self.stats.cores_found.saturating_mul(EXPENSIVE_CORE_MS)
                && self.residual_uniform_weight().is_some()
            {
                descent_kick = true;
                if debug_trace() {
                    eprintln!(
                        "c expensive-core descent kick: cores={} elapsed_ms={} gap={} lb={} ub={}",
                        self.stats.cores_found,
                        started.elapsed().as_millis(),
                        self.ub.saturating_sub(self.effective_lb()),
                        self.effective_lb(),
                        self.ub,
                    );
                }
            }
            // #cold-core-descent: the RATE arm of the organic gate's core
            // conjunct. Computed unconditionally (a handful of comparisons) so
            // the trace below reports the signal even in the
            // `--maxsat-no-cold-descent` leg — that is what makes the A/B
            // legible: leg A shows when the signal WOULD have fired, leg B
            // shows the descent that followed it.
            let cores_cold = self.core_discovery_cold(started);
            // The rate arm with the organic gate's remaining conjuncts — i.e.
            // "the gate is open on rate evidence alone".
            //
            // NOT conjoined with `oll_stalling`, and that is a measured choice,
            // not an oversight. The value gate asks whether lb is moving; this
            // arm asks whether CORES are arriving, and an instance can pass the
            // first by a hair while failing the second completely. Traced on
            // af-synthesis_wt-af-synthesis_stb_50_120_5 at 900s: no core after
            // #16 at t=15.0, the next loop iteration lands 70s later, and there
            // `oll_stalling` is FALSE because the window's lb gain (3) just
            // clears gap/12 (32/12 = 2.66) — 70 seconds without a core, held out
            // of the gate by three units of lb. Conjoining the two makes the rate
            // arm unreachable on exactly the family it was built for.
            let cold_ready = cores_cold
                && gap_ok
                && self.best_model.is_some()
                && Instant::now() >= descent_not_before;
            if debug_trace() && !cold_signal_traced && cold_ready {
                // The first instant the RATE arm opens the gate. Printed even in
                // the `--maxsat-no-cold-descent` leg (the predicate itself is
                // hatch-free) so an A/B shows when the arm WOULD have fired.
                cold_signal_traced = true;
                eprintln!(
                    "c cold-core signal: cores={} search_cores={} min_cores={} drought_ms={} \
                     bar_ms={} median_ms={} window={} enabled={} lb={} ub={}",
                    self.stats.cores_found,
                    self.core_search_cores,
                    self.tuning.lsu_min_cores,
                    self.core_drought().as_millis(),
                    self.cold_core_bar_ms(),
                    self.core_gap_median_ms,
                    self.core_gaps_ms.len(),
                    cold_core_descent_enabled(),
                    self.effective_lb(),
                    self.ub,
                );
            }
            let arm = classify_descent_arm(
                self.best_model.is_some(),
                cold_core_descent_enabled(),
                cold_ready,
                descent_kick,
                self.stats.cores_found >= self.tuning.lsu_min_cores
                    && oll_stalling
                    && gap_ok
                    && Instant::now() >= descent_not_before,
            );
            if arm != DescentArm::None && self.softs.len() <= 50_000 && self.descent_reachable() {
                let kick_entry = arm == DescentArm::Kick;
                descent_kick = false;
                // #cold-core-descent D9: name the arm that ACTUALLY opened the
                // gate. Labelling by core count (the first cut) reports every
                // cold-rate entry on an instance that has also passed
                // `lsu_min_cores` as a `count` entry, which is exactly the
                // attribution the planned corpus sweep depends on.
                if debug_trace() {
                    eprintln!(
                        "c descent entry: arm={} cores={} min_cores={} drought_ms={} bar_ms={}",
                        match arm {
                            DescentArm::Kick => "kick",
                            DescentArm::Cold => "cold-rate",
                            DescentArm::Count => "count",
                            DescentArm::None => unreachable!("gate is open"),
                        },
                        self.stats.cores_found,
                        self.tuning.lsu_min_cores,
                        self.core_drought().as_millis(),
                        self.cold_core_bar_ms(),
                    );
                }
                // #wce flush (c): give the descent a consistent, fully
                // materialized encoding, and let the flush exhausts' lb/ub
                // motion shape the encoding built below. `descent_reachable()`
                // above keeps the pre-flush gate equivalent to the
                // `ensure_descent_enc()` outcome on instances that cannot
                // currently descend, so those don't get their pending batches
                // drained every stalling iteration.
                if !self.flush_pending(
                    &mut suspended,
                    true,
                    started,
                    &mut exhaust_spent,
                    should_stop,
                ) {
                    return match self.best_model {
                        Some(_) => self.optimal(),
                        None => OllOutcome::Unsatisfiable,
                    };
                }
                if self.effective_lb() >= self.ub {
                    return self.optimal();
                }
                if self.ensure_descent_enc() {
                    // One-way commit (re-measured 2026-07-12): reversible
                    // doubling slices with this same value-based entry gate
                    // A/B'd at -3 weighted / -2 unweighted on stride-4 — the
                    // original "interleaving loses" verdict holds even with
                    // sane entry timing, so the ORGANIC descent keeps the
                    // irrevocable deadline. The value-based gate above still
                    // fixes both entry polarities (premature fire on slow
                    // first solves; never-fire on cheap-core churn).
                    //
                    // #fold-descent-kick entries are the exception: the kick
                    // fires right after a clique fold on a heuristic gap
                    // signal, without the stall evidence the organic gate
                    // demands. A one-way commit there strangles instances
                    // whose descent stalls (lisbon-wedding: fold + gap<=64 →
                    // committed descent never returns; OLL alone solved it in
                    // 22s). Kick entries get a bounded slice — frb-class
                    // closes within it (measured: frb30 descends in seconds),
                    // and on expiry OLL resumes with the folded encoding
                    // intact (descend() keeps encoding + bounds on None).
                    // Progress-extending slices (#ub-stale-descent): a kick
                    // slice that improved the incumbent earns another slice —
                    // the descent is converging and interrupting it wastes
                    // the warm bound clauses (protein 1bpi: gap 14 needs
                    // several 10s slices). Only a DRY slice hands control
                    // back to OLL.
                    // #descent-organic-slice: an organic entry gets a bounded,
                    // progress-extending slice too, so an UNPRODUCTIVE descent
                    // cannot own the rest of the run with lb frozen. A
                    // productive one still runs to completion via the same
                    // "improved ⇒ another slice" rule the kicks use.
                    //
                    // #cold-core-descent D5: the COLD arm is bounded too, and
                    // unconditionally. It carries the WEAKEST evidence of the
                    // three — no core count, no lb-stall test, no gap cap
                    // beyond `gap_ok` — so handing it the one-way commit gave
                    // the least-evidenced arm the most irreversible treatment.
                    // The one-way commit freezes lb for the rest of the budget
                    // (`descend` only ever moves ub), and on the slow-walk
                    // families the rate arm is most likely to misfire on
                    // (rna-alignment, protein_ins) the core walk is the
                    // PRODUCTIVE path. A dry slice hands control back; a
                    // converging one still runs to completion under the same
                    // "improved ⇒ another slice" rule. Escalating a cold entry
                    // to a one-way commit is a change that needs its own
                    // paired A/B and its own evidence, not a default.
                    // Budget-scaled when a deadline is known, fixed otherwise
                    // (budget-blind callers keep their previous behaviour).
                    let organic_len = match self.budget_remaining() {
                        Some(rem) => (rem / ORGANIC_DESCENT_BUDGET_DIVISOR)
                            .clamp(ORGANIC_DESCENT_SLICE_MIN, ORGANIC_DESCENT_SLICE_MAX),
                        None => ORGANIC_DESCENT_SLICE,
                    };
                    // #descent-kick-scale: same treatment for the kick arm,
                    // which on the expensive-core families is the ONLY reachable
                    // entry (the organic gate needs 64 cores; those runs end at
                    // ~17). Falls back to the measured 10s when disabled or
                    // budget-blind.
                    let kick_len = match (descent_kick_scale_enabled(), self.budget_remaining()) {
                        (true, Some(rem)) => (rem / ORGANIC_DESCENT_BUDGET_DIVISOR)
                            .clamp(DESCENT_KICK_SLICE, ORGANIC_DESCENT_SLICE_MAX),
                        _ => DESCENT_KICK_SLICE,
                    };
                    let slice = descent_slice_len(
                        arm,
                        descent_organic_slice_enabled(),
                        kick_len,
                        organic_len,
                    );
                    let bounded = slice.is_some();
                    // (`descend` stops the drought clock for the slice —
                    // #cold-core-descent D1.)
                    let outcome = loop {
                        let deadline = match slice {
                            Some(len) => Instant::now() + len,
                            None => Instant::now() + Duration::from_hours(8760),
                        };
                        let ub_before = self.ub;
                        let outcome = self.descend(deadline, should_stop, on_upper_bound);
                        if outcome.is_some() || !bounded || self.ub >= ub_before {
                            break outcome;
                        }
                    };
                    if let Some(outcome) = outcome {
                        return outcome;
                    }
                    // Dry slice expired: back to OLL. (Kick entries always;
                    // organic entries too under #descent-organic-slice, which
                    // is the whole point — lb resumes moving.) Keep the
                    // organic gate from immediately re-committing on the same
                    // post-fold state it never vetted.
                    //
                    // #descent-duty-cycle: the OLL window must scale with the
                    // slice it follows, or the alternation is not an
                    // alternation. The organic slice is budget-scaled
                    // (`organic_len` = clamp(remaining/8, 10s, 300s)) while this
                    // bar was a fixed 15s, making OLL's share
                    // 15/(15+organic_len) — 4.8% at a 3600s budget. That
                    // starves the lower-bound lane the lever exists to revive,
                    // and it is why the first #descent-organic-slice A/B
                    // measured inert: the descent got a bigger slice and OLL
                    // never got its turn back. Kick entries keep the measured
                    // 15s (their slice is a fixed 10s, so 15s is already a
                    // longer window than the slice).
                    let oll_window = if kick_entry {
                        // Same duty-cycle rule: the OLL window must not be
                        // shorter than the slice it follows once that slice
                        // scales, or OLL is starved exactly as it was on the
                        // organic arm.
                        kick_len.max(Duration::from_secs(15))
                    } else {
                        organic_len.max(Duration::from_secs(15))
                    };
                    descent_not_before = Instant::now() + oll_window;
                }
            }

            // Assume active selectors (minus delayed sums) whose residual
            // weight reaches the current level (#climit-discipline; sum
            // selectors obey the same rule), highest residual weight first.
            // Consequence: every member of a core extracted here carries a
            // residual >= level, so each core pays >= level into lb.
            let mut assumptions: Vec<(Literal, Weight)> = self
                .active
                .iter()
                .filter(|(l, &w)| w >= self.level && !suspended.contains(l))
                .map(|(&l, &w)| (l, w))
                .collect();
            assumptions.sort_unstable_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
            let assumption_lits: Vec<Literal> = assumptions.into_iter().map(|(l, _)| l).collect();

            // #wce flush (b): the level's assumable selectors ran out while
            // extracted cores still await relaxation. This "empty" is an
            // artifact of the deferral — the pending cores' would-be sum
            // selectors don't exist yet (each would carry weight
            // w_min >= level: every member of every pending core had
            // residual >= level at extraction, and the level only changes
            // at Sat points, where flush (a) has already drained the queue)
            // — NOT a finished level phase. Flush with immediate activation
            // (no delay: nothing is left for the delay discipline to
            // protect) and rebuild the assumption set at the same level.
            if assumption_lits.is_empty() && !self.pending_relax.is_empty() {
                if !self.flush_pending(
                    &mut suspended,
                    false,
                    started,
                    &mut exhaust_spent,
                    should_stop,
                ) {
                    return match self.best_model {
                        Some(_) => self.optimal(),
                        None => OllOutcome::Unsatisfiable,
                    };
                }
                if self.best_model.is_some() && self.effective_lb() >= self.ub {
                    return self.optimal();
                }
                continue;
            }

            self.stats.sat_calls = self.stats.sat_calls.saturating_add(1);
            let result = self
                .sat
                .solve_with_assumptions_interruptible(&assumption_lits, should_stop)
                .into_inner();

            if !initial_probe_done {
                initial_probe_done = true;
                // Watches are attached now (first solve done). Mine UP-refuted
                // units once, up front — but only on modest active sets: the
                // sweep's per-probe BCP over a million-clause formula makes even
                // the sample cost ~19s (SeanSafarpour). Phase A is read-only;
                // process_core hardens any failed selectors and pays lb. If it
                // moved lb, re-solve so `result`'s stale core isn't processed
                // against a now-hardened literal set.
                //
                // SINGLE-STRATUM ONLY (!lp_eligible OR level<=1): this is a
                // single-stratum technique — when the level never changes the
                // level-change probe never fires, which is the gap it fills.
                // That covers the unweighted track (uniform weights) AND
                // weighted instances whose stratification collapses to level 1
                // at entry (#rna-single-stratum: rna-alignment has weights
                // {1,2} but installs at threshold=1 with no model found for
                // 60s — it ground ~80 size-2 AM1-edge cores at ~2.3s each
                // with zero probing). On genuinely multi-stratum instances
                // (level > 1) the up-front harden + re-solve fights the
                // climit/WCE stratification discipline: an unconditional
                // weighted leg regressed -47 (drmx/frb/haplotyping/metro
                // across 14 families).
                // #core-mine: `pay_mined_cores` can fill `pending_relax` before
                // the first SAT call, and `run_am1_probe` opens with
                // `debug_assert!(self.pending_relax.is_empty())`. The other
                // probe site already carries this guard; without it here, any
                // mineable instance panics in debug/test builds.
                if self.active.len() <= EAGER_PROBE_MAX_ACTIVE
                    && self.pending_relax.is_empty()
                    && (!self.lp_eligible || self.level <= 1)
                {
                    let failed_before = self.stats.am1_probe_failed;
                    let groups_before = self.stats.am1_probe_groups;
                    self.run_am1_probe(started, &mut am1_probe_spent, should_stop);
                    // Stale-result invalidation (#am1-l1-stale-core, root-caused
                    // 2026-07-17): re-solve on ANY probe state motion, not just
                    // failed literals. relax_am1_clique pays lb += d*(k-1) and
                    // zeroes members' residuals (dropping exhausted members from
                    // `active`); if the in-flight `result` core is then processed,
                    // process_core's w_min filter_map silently skips the absent
                    // members and pays lb += w_min AGAIN on residual mass the
                    // clique peel already spent — a double-charge that reported
                    // 20 on privilege-escalation-task-54 (true optimum 19). With
                    // this guard the level-1 clique mining is sound (verified:
                    // same instance solves to 19 OPTIMUM with edges on, keeping
                    // the lb 0->10 clique gains).
                    if self.stats.am1_probe_failed > failed_before
                        || self.stats.am1_probe_groups > groups_before
                    {
                        if self.best_model.is_some() && self.effective_lb() >= self.ub {
                            return self.optimal();
                        }
                        self.harden();
                        continue;
                    }
                }
            }

            // #frb-bmo-probe-after-solve: a level change requested an AM1
            // probe pass; the solve above ran the prologue, so clauses and
            // hardened units added at the level change are now attached and
            // propagated — the probe finally sees them. Same stale-result
            // guard as the eager probe: if the probe moved lb or hardened
            // anything, `result`'s core may reference consumed residuals —
            // discard it and re-solve (#am1-l1-stale-core).
            if am1_probe_pending && self.pending_relax.is_empty() {
                am1_probe_pending = false;
                let failed_before = self.stats.am1_probe_failed;
                let groups_before = self.stats.am1_probe_groups;
                let lb_before_probe = self.lb;
                self.run_am1_probe(started, &mut am1_probe_spent, should_stop);
                if self.stats.am1_probe_failed > failed_before
                    || self.stats.am1_probe_groups > groups_before
                {
                    if self.best_model.is_some() && self.effective_lb() >= self.ub {
                        return self.optimal();
                    }
                    // #fold-descent-kick: a large clique fold can land lb
                    // within the endgame band of ub while leaving deep
                    // totalizer bounds for the remaining cores (frb30-15:
                    // fold pays lb 0->~400, ub=426, optimum 420; the last
                    // cores over deepened sum bounds crawl and the ub never
                    // improves — the incumbent came from a free model, not a
                    // descent). The tuned descent entry gate never fires
                    // here: steady ~1 lb/s defeats the stall window and the
                    // fold replaced the cores that would satisfy
                    // lsu_min_cores. This state did not exist before the
                    // fold landed, so the gate's A/B verdicts don't cover
                    // it; kick the descent explicitly when the fold leaves a
                    // small gap.
                    // Post-fold gaps measured on frb: 25-13 → 41, 30-15 → 45,
                    // 35-17 → ~47 (fold pays ~90% of optimum). 64 covers the
                    // family with headroom while still excluding genuinely
                    // wide-gap instances where a one-way descent commit is
                    // premature. DOMINANT-FOLD condition: the fold's own lb
                    // payment must cover the remaining gap — frb30 pays 383
                    // against a residual 45; lisbon-wedding's fold paid ~2
                    // against a gap of 30 (one incidental 2-clique) and the
                    // kick there strangled an instance OLL alone solves in
                    // 22s. Payment >= gap keeps the kick on instances where
                    // the fold did the heavy lifting and the descent only
                    // mops up.
                    let fold_payment = self.lb.saturating_sub(lb_before_probe);
                    let residual_gap = self.ub.saturating_sub(self.effective_lb());
                    if self.stats.am1_probe_groups > groups_before
                        && self.best_model.is_some()
                        && residual_gap <= 64
                        && fold_payment >= residual_gap
                    {
                        descent_kick = true;
                    }
                    self.harden();
                    continue;
                }
            }

            match result {
                AssumeResult::Sat(model) => {
                    let cost = self.model_cost(&model);
                    if cost < self.ub {
                        self.ub = cost;
                        self.ub_last_improved = Instant::now();
                        self.best_model = Some(model);
                        on_upper_bound(cost);
                        self.harden();
                    }
                    // Residual-mass hardening: sound exactly here, where the
                    // model witnesses every non-suspended >= level selector
                    // satisfied (see harden_residual_mass; pending #wce
                    // cores contribute their w_min·(k−1) slack to ub2, so
                    // this runs soundly BEFORE the flush below).
                    self.harden_residual_mass(&suspended);
                    if self.effective_lb() >= self.ub {
                        // #wce (d): no flush needed — lb payments were
                        // immediate, so lb >= ub is a complete optimality
                        // proof without the pending totalizers.
                        return self.optimal();
                    }
                    // #wce flush (a): the delay phase ends at SAT —
                    // materialize pending relaxations INTO the suspended
                    // set, so the branch below re-solves at the same level
                    // with everything activated together. The level logic
                    // after it therefore never runs with unrelaxed cores.
                    if !self.flush_pending(
                        &mut suspended,
                        true,
                        started,
                        &mut exhaust_spent,
                        should_stop,
                    ) {
                        return match self.best_model {
                            Some(_) => self.optimal(),
                            None => OllOutcome::Unsatisfiable,
                        };
                    }
                    if self.effective_lb() >= self.ub {
                        return self.optimal();
                    }
                    if !suspended.is_empty() {
                        // Delay phase over: activate all deferred sums and
                        // re-solve at the SAME level.
                        suspended.clear();
                        continue;
                    }
                    if self.level <= 1 {
                        // Terminal (#climit-discipline): level 1 filters
                        // nothing and the pool is empty, so this model
                        // satisfies every active selector — original and
                        // sum bounds alike — and cost == lb == optimum.
                        debug_assert!(self.pool.is_empty(), "pool must drain at level 1");
                        debug_assert!(
                            self.pending_relax.is_empty(),
                            "level-1 terminal with unrelaxed cores (flush (a) must run first)",
                        );
                        return self.optimal();
                    }
                    // Satisfiable with nothing suspended above level 1:
                    // recompute the level from the live residual histogram
                    // and continue (already-active residuals requalify via
                    // the assumption filter; pool selectors move over).
                    self.level = self.next_level();
                    self.stats.strat_levels = self.stats.strat_levels.saturating_add(1);
                    self.activate_stratum(self.level);
                    self.pay_mined_cores();
                    self.harden();
                    // #maxsat-am1-probe + #frb-bmo-probe-after-solve: request
                    // an AM1 probe pass, but run it only AFTER the next SAT
                    // call. probe_implications_false cannot see clauses added
                    // since the last solve (watch attach + unit enqueues are
                    // deferred to the solve prologue — see its doc comment),
                    // and the harden() above just added unit clauses for every
                    // now-unaffordable selector. Probing here would run
                    // against unassigned selectors: on BMO-shaped instances
                    // (frb: 5574 binary softs at w=221 over 220 unit softs at
                    // w=1) it found ZERO edges (probes=220 failed=0
                    // edge_nodes=0) and the engine ground ~200 size-2 cores
                    // one at a time. After the next solve's prologue the
                    // hardened units propagate, the relaxed clauses act
                    // binary, and the domain cliques fold in one pass
                    // (lb 0->200 on frb20-11).
                    am1_probe_pending = true;
                }
                AssumeResult::Unsat(core, _) => {
                    if core.is_empty() {
                        // Formula UNSAT independent of assumptions.
                        return match self.best_model {
                            // Hardening restricted the space to cost < ub;
                            // exhaustion proves the incumbent optimal.
                            Some(_) => self.optimal(),
                            None => OllOutcome::Unsatisfiable,
                        };
                    }
                    let core = self.trim_core(core, should_stop);
                    // #minimize: deletion-based minimization after trim,
                    // share-gated exactly like exhaustion. The minimized
                    // core flows through the SAME downstream path (overlap
                    // flush on the FINAL membership, process_core, WCE
                    // queueing): process_core computes w_min FRESH from the
                    // minimized members (it can only INCREASE — cheap
                    // members were dropped first), pays lb += w_min, splits
                    // residuals, and queues (members, w_min) on
                    // pending_relax, so the WCE identity slack
                    // w_min * (k - 1) uses the same consistent pair. The
                    // larger payment is sound: the minimized core is a
                    // certified UNSAT subset of the assumptions, every model
                    // falsifies at least one member, and each member carries
                    // residual >= the new w_min. The climit invariant
                    // "every core pays >= level" also survives — members
                    // are a subset of the level-filtered assumptions, so
                    // w_min >= level still holds and can only grow.
                    let core = if minimize_spent.as_secs_f64()
                        < MINIMIZE_TIME_SHARE * started.elapsed().as_secs_f64()
                    {
                        let t0 = Instant::now();
                        let core = self.minimize_core(core, should_stop);
                        minimize_spent += t0.elapsed();
                        core
                    } else {
                        core
                    };
                    // #wce overlap flush: keep every pending batch a
                    // DISJOINT core family. An overlapping core would raid
                    // residuals of members already backing a queued core,
                    // fragmenting one conflict region's weight across
                    // several totalizers whose sub-level residue is then
                    // only payable at the dust level (measured on
                    // mpe_wt-random-net-120-1_network-9: overlapping
                    // batches entered level 1 with 849 active selectors
                    // and needed 249 level-1 cores vs eager's 591/39).
                    // Disjoint batches also make the flush exhausts probe
                    // independent regions — the same information order
                    // eager extraction had. Cores over member-untouched
                    // regions (the common case on structured instances)
                    // keep batching freely.
                    if core.iter().any(|l| self.pending_members.contains(l))
                        && !self.flush_pending(
                            &mut suspended,
                            true,
                            started,
                            &mut exhaust_spent,
                            should_stop,
                        )
                    {
                        return match self.best_model {
                            Some(_) => self.optimal(),
                            None => OllOutcome::Unsatisfiable,
                        };
                    }
                    let lb_pre = self.lb;
                    let new_sums = self.process_core(&core, CoreOrigin::Search);
                    self.record_sat_core(&core, lb_pre);
                    suspended.extend(new_sums.iter().copied());

                    // Exhaust the freshest sum under a budget capped to a
                    // share of total solve time. #wce: a multi-member core's
                    // relaxation is deferred, so there is no fresh core
                    // totalizer to probe here — its exhaust now runs at
                    // flush time (flush_pending). Unit cores on sum
                    // selectors keep the immediate bump-chain exhaust
                    // (their bound extension is never deferred), exactly
                    // the pre-WCE behavior.
                    if core.len() == 1 {
                        if let Some(&sel) = new_sums.last() {
                            if exhaust_spent.as_secs_f64()
                                < EXHAUST_TIME_SHARE * started.elapsed().as_secs_f64()
                            {
                                let t0 = Instant::now();
                                let ok = self.exhaust_sum(sel, &mut suspended, should_stop);
                                exhaust_spent += t0.elapsed();
                                if !ok {
                                    return match self.best_model {
                                        Some(_) => self.optimal(),
                                        None => OllOutcome::Unsatisfiable,
                                    };
                                }
                            }
                        }
                    }

                    if self.best_model.is_some() && self.effective_lb() >= self.ub {
                        return self.optimal();
                    }
                    self.harden();
                }
                // `AssumeResult` is non-exhaustive; treat anything else as
                // an interruption and fall back to the incumbent.
                _ => {
                    return OllOutcome::Unknown { best: self.best() };
                }
            }
        }
    }

    fn optimal(&self) -> OllOutcome {
        if debug_trace() {
            eprintln!(
                "c engine: conflicts={} decisions={} propagations={} sat_calls={}",
                self.sat.num_conflicts(),
                self.sat.num_decisions(),
                self.sat.num_propagations(),
                self.stats.sat_calls,
            );
        }
        match &self.best_model {
            Some(model) => OllOutcome::Optimal {
                model: model.clone(),
                cost: self.ub,
            },
            None => OllOutcome::Unsatisfiable,
        }
    }
}

#[cfg(test)]
mod tot_tests {
    use super::*;

    /// #oneshot-dry-guard-band regression: the one-shot dry arm and
    /// `install_non_oneshot_sat_config` must agree band for band, because the
    /// dry arm's whole contract is "run on the configuration the non-one-shot
    /// path would have used".
    ///
    /// They used to be hand-copied duplicates. The dry copy hard-coded the
    /// >500k disables while asserting `hard.len() >= 1M`, an invariant broken
    /// when `BCE_ONESHOT_MIN_HARDS` (100k) lowered the gate under
    /// `--maxsat-bce`. Instances in the 100k..=500k band then ran every
    /// solve with vivify/subsume/probe/transred/sweep disabled, which produced
    /// wrong answers on `tcp_wt-tcp_students_112_it_5` (242,578 hards):
    /// `o 3441`/`3477`/`3549` against a true optimum of 3366.
    ///
    /// The band boundary is the assertion that matters: at 242,578 hards the
    /// answer must be "install nothing".
    #[test]
    fn non_oneshot_band_installs_nothing_below_500k() {
        // The failing instance's exact size — this is the regression.
        assert!(
            non_oneshot_inprocessing_profile(242_578).is_none(),
            "tcp_wt-tcp_students_112_it_5 (242,578 hards) must install NO \
             inprocessing profile; installing the >500k band here is the \
             #oneshot-dry-guard-band wrong-answer bug"
        );
        // Band edges.
        assert!(non_oneshot_inprocessing_profile(BCE_ONESHOT_MIN_HARDS).is_none());
        assert!(non_oneshot_inprocessing_profile(500_000).is_none());
        assert!(non_oneshot_inprocessing_profile(500_001).is_some());

        // >500k: the five inprocessing disables. The occurrence-list passes
        // that default ON stay ON until 2M. (`bve`/`bce`/`congruence` default
        // OFF, so they are not evidence either way here.)
        let mid = non_oneshot_inprocessing_profile(600_000).expect("500k..2M installs a profile");
        assert!(!mid.vivify && !mid.subsume && !mid.probe && !mid.transred && !mid.sweep);
        assert!(
            mid.factor && mid.sbva && mid.htr && mid.gate && mid.backbone,
            "occ-list passes must survive below 2M"
        );

        // >2M additionally disables the occurrence-list passes.
        let big = non_oneshot_inprocessing_profile(2_000_001).expect("2M+ installs a profile");
        assert!(!big.factor && !big.sbva && !big.htr && !big.gate && !big.backbone);
    }

    /// Incremental totalizer: extending the bound stepwise must produce a
    /// complete "at least t inputs true => O_t" implication set at every
    /// step. We check by assuming ¬O_t plus t chosen inputs and expecting
    /// UNSAT, and ¬O_t plus t-1 inputs and expecting SAT.
    #[test]
    fn totalizer_incremental_extension_blocks_counts() {
        for n in 2usize..=6 {
            let mut sat = SatSolver::new(0);
            let inputs: Vec<Literal> = (0..n).map(|_| Literal::positive(sat.new_var())).collect();
            let mut root = TotNode::build(&inputs);

            for k in 2..=n {
                let mut fresh = |sat: &mut SatSolver| Literal::positive(sat.new_var());
                root.extend(k, &mut sat, &mut fresh, None);
                let out_k = root.outs[k - 1];

                // ¬O_k with k inputs forced true: must be UNSAT.
                let mut assumptions = vec![out_k.negated()];
                assumptions.extend(inputs.iter().take(k).copied());
                let result = sat
                    .solve_with_assumptions_interruptible(&assumptions, || false)
                    .into_inner();
                assert!(
                    result.is_unsat(),
                    "n={n} k={k}: {k} true inputs must force O_{k}"
                );

                // ¬O_k with k-1 inputs true and the rest false: must be SAT.
                let mut assumptions = vec![out_k.negated()];
                assumptions.extend(inputs.iter().take(k - 1).copied());
                assumptions.extend(inputs.iter().skip(k - 1).map(|l| l.negated()));
                let result = sat
                    .solve_with_assumptions_interruptible(&assumptions, || false)
                    .into_inner();
                assert!(
                    result.is_sat(),
                    "n={n} k={k}: {} true inputs must be consistent with not-O_{k}",
                    k - 1
                );
            }
        }
    }
}

#[cfg(test)]
mod lsu_tests {
    use super::*;

    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0 >> 33
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    fn brute_force(num_vars: u32, hard: &[Vec<i32>], soft: &[Vec<i32>]) -> Option<u64> {
        let clause_sat = |clause: &[i32], bits: u64| {
            clause.iter().any(|&lit| {
                let var = lit.unsigned_abs();
                let val = (bits >> (var - 1)) & 1 == 1;
                (lit > 0) == val
            })
        };
        let mut best: Option<u64> = None;
        for bits in 0..(1u64 << num_vars) {
            if hard.iter().any(|c| !clause_sat(c, bits)) {
                continue;
            }
            let cost = soft.iter().filter(|c| !clause_sat(c, bits)).count() as u64;
            best = Some(best.map_or(cost, |b: u64| b.min(cost)));
        }
        best
    }

    /// Cross-check with thresholds forced to zero so the LSU descent runs
    /// on every satisfiable instance with a nonzero gap. This is the
    /// regression net for the class of bug where LSU bounded the wrong
    /// quantity (violated *selectors* instead of violated *softs*) and
    /// declared false optima.
    #[test]
    fn random_cross_check_lsu_aggressive() {
        let mut lsu_exercised = 0u64;
        for seed in 0..300u64 {
            let mut rng = Lcg(seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(7));
            let num_vars = 3 + rng.below(6) as u32;
            let num_hard = rng.below(6) as usize;
            let num_soft = 1 + rng.below(12) as usize;

            let gen_clause = |rng: &mut Lcg| -> Vec<i32> {
                let len = 1 + rng.below(3) as usize;
                (0..len)
                    .map(|_| {
                        let v = 1 + rng.below(num_vars as u64) as i32;
                        if rng.below(2) == 0 {
                            v
                        } else {
                            -v
                        }
                    })
                    .collect()
            };

            let hard: Vec<Vec<i32>> = (0..num_hard).map(|_| gen_clause(&mut rng)).collect();
            let soft: Vec<Vec<i32>> = (0..num_soft).map(|_| gen_clause(&mut rng)).collect();
            let expected = brute_force(num_vars, &hard, &soft);

            let mut hard_store = ClauseStore::new();
            for c in &hard {
                hard_store.push_from_iter(c.iter().map(|&l| Literal::from(l)));
            }
            let mut soft_store = ClauseStore::new();
            for c in &soft {
                soft_store.push_from_iter(c.iter().map(|&l| Literal::from(l)));
            }
            let weights = vec![1u64; soft.len()];
            let mut engine = OllEngine::new(num_vars + 1, hard_store, soft_store, weights);
            engine.set_tuning(OllTuning {
                lsu_min_cores: 0,
                lsu_min_gap_units: 0,
                lsu_stall_ms_per_core: 0,
                force_adder: false,
                abstraction_min_cores: 0,
                force_cluster: false,
                force_dpw: false,
                lp_boost: LpBoostMode::Auto,
                // #tot-eqs pinned ON so the reverse-direction clauses are exercised
                // wherever the fixture has >= 2 distinct soft weights. Production also
                // defaults ON (env gate AY_AB_MAXSAT_TOT_EQS != "0"); `tot_eq_budget`
                // is 0 on uniform weights, so the pin is inert on unit-weight fixtures.
                tot_eqs: Some(true),
                core_clause: Some(true),
            });

            let outcome = engine.solve(&|| false, &mut |_| {});
            lsu_exercised += engine.stats().lsu_steps;
            // #lp-boost unweighted identity gate: uniform (unit) weights
            // must keep the lane fully inert even under aggressive tuning.
            assert_eq!(
                engine.stats().lp_boost_runs,
                0,
                "seed {seed}: LP-boost lane ran on a uniform-weight instance",
            );
            assert!(
                engine.lp_cores.is_empty(),
                "seed {seed}: LP-boost captured cores on a uniform-weight instance",
            );
            match (outcome, expected) {
                (OllOutcome::Optimal { cost, .. }, Some(exp)) => {
                    assert_eq!(
                        cost, exp,
                        "seed {seed}: LSU-aggressive cost {cost} != brute force {exp}\nhard: {hard:?}\nsoft: {soft:?}",
                    );
                }
                (OllOutcome::Unsatisfiable, None) => {}
                (got, exp) => panic!(
                    "seed {seed}: {got:?} vs brute force {exp:?}\nhard: {hard:?}\nsoft: {soft:?}",
                ),
            }
        }
        assert!(
            lsu_exercised > 0,
            "aggressive tuning must actually drive instances through LSU",
        );
    }

    /// Weighted counterpart of the aggressive cross-check: mixed weights
    /// drive the GTE descent path on every instance with a nonzero gap.
    #[test]
    fn random_cross_check_gte_aggressive() {
        let mut lsu_exercised = 0u64;
        for seed in 0..300u64 {
            let mut rng = Lcg(seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(13));
            let num_vars = 3 + rng.below(6) as u32;
            let num_hard = rng.below(6) as usize;
            let num_soft = 1 + rng.below(12) as usize;

            let gen_clause = |rng: &mut Lcg| -> Vec<i32> {
                let len = 1 + rng.below(3) as usize;
                (0..len)
                    .map(|_| {
                        let v = 1 + rng.below(num_vars as u64) as i32;
                        if rng.below(2) == 0 {
                            v
                        } else {
                            -v
                        }
                    })
                    .collect()
            };

            let hard: Vec<Vec<i32>> = (0..num_hard).map(|_| gen_clause(&mut rng)).collect();
            let soft: Vec<Vec<i32>> = (0..num_soft).map(|_| gen_clause(&mut rng)).collect();
            // Every third seed: uniform non-unit weights, exercising the
            // uniform-w totalizer descent's ceil(target/w) bound rounding.
            let weights: Vec<u64> = if seed % 3 == 0 {
                let w = 2 + rng.below(5);
                vec![w; num_soft]
            } else {
                (0..num_soft).map(|_| 1 + rng.below(20)).collect()
            };

            let clause_sat = |clause: &[i32], bits: u64| {
                clause.iter().any(|&lit| {
                    let var = lit.unsigned_abs();
                    let val = (bits >> (var - 1)) & 1 == 1;
                    (lit > 0) == val
                })
            };
            let mut expected: Option<u64> = None;
            for bits in 0..(1u64 << num_vars) {
                if hard.iter().any(|c| !clause_sat(c, bits)) {
                    continue;
                }
                let cost: u64 = soft
                    .iter()
                    .zip(&weights)
                    .filter(|(c, _)| !clause_sat(c, bits))
                    .map(|(_, w)| *w)
                    .sum();
                expected = Some(expected.map_or(cost, |b: u64| b.min(cost)));
            }

            let mut hard_store = ClauseStore::new();
            for c in &hard {
                hard_store.push_from_iter(c.iter().map(|&l| Literal::from(l)));
            }
            let mut soft_store = ClauseStore::new();
            for c in &soft {
                soft_store.push_from_iter(c.iter().map(|&l| Literal::from(l)));
            }
            let mut engine = OllEngine::new(num_vars + 1, hard_store, soft_store, weights.clone());
            engine.set_tuning(OllTuning {
                lsu_min_cores: 0,
                lsu_min_gap_units: 0,
                lsu_stall_ms_per_core: 0,
                force_adder: false,
                abstraction_min_cores: 0,
                force_cluster: false,
                force_dpw: false,
                lp_boost: LpBoostMode::Auto,
                // #tot-eqs pinned ON so the reverse-direction clauses are exercised
                // wherever the fixture has >= 2 distinct soft weights. Production also
                // defaults ON (env gate AY_AB_MAXSAT_TOT_EQS != "0"); `tot_eq_budget`
                // is 0 on uniform weights, so the pin is inert on unit-weight fixtures.
                tot_eqs: Some(true),
                core_clause: Some(true),
            });

            let outcome = engine.solve(&|| false, &mut |_| {});
            lsu_exercised += engine.stats().lsu_steps;
            match (outcome, expected) {
                (OllOutcome::Optimal { cost, .. }, Some(exp)) => {
                    assert_eq!(
                        cost, exp,
                        "seed {seed}: GTE-aggressive cost {cost} != brute force {exp}\nhard: {hard:?}\nsoft: {soft:?}\nweights: {weights:?}",
                    );
                }
                (OllOutcome::Unsatisfiable, None) => {}
                (got, exp) => panic!(
                    "seed {seed}: {got:?} vs brute force {exp:?}\nhard: {hard:?}\nsoft: {soft:?}",
                ),
            }
        }
        assert!(
            lsu_exercised > 0,
            "aggressive tuning must actually drive instances through the GTE descent",
        );
    }

    /// #dpw-descent END-TO-END. The same mixed-weight fixture as
    /// `random_cross_check_gte_aggressive`, with `force_dpw` pinning the
    /// watchdog descent in place of the GTE, cross-checked against weighted
    /// brute force.
    ///
    /// This is the net for the INTEGRATION rather than the encoding (which
    /// `crate::dpw`'s own nets cover exhaustively): the bound lives entirely
    /// in the assumption vector rebuilt each round, so a target computed from
    /// the wrong quantity, a bound left stale after an `ub` improvement, or a
    /// tighten arm that quietly stopped cutting all show up here as a cost
    /// mismatch or a hang.
    ///
    /// Kill mutation (`descent_bound_too_strong`): in `descend_slice`, change
    /// the DPW assumption injection `enc.assumptions(target - 1)` to
    /// `enc.assumptions(target.saturating_sub(2))`. Measured: seed 19 then
    /// reports cost 10 against a brute-force optimum of 9 — a WRONG ANSWER,
    /// which is the direction that disqualifies at MSE, off a one-line change
    /// to the bound.
    ///
    /// (The mirror-image slip `enc.assumptions(target)` is NOT caught by this
    /// test, and that is the honest situation rather than a gap worth closing
    /// here: an over-LOOSE bound cannot make the descent claim an optimum it
    /// has not got, it only makes the descent stop cutting, and OLL still
    /// proves the instance by core enumeration. Release builds lose a lever,
    /// not an answer. Debug builds do catch it — measured — on
    /// `DpwEnc::assumptions`'s `k <= k_init` assertion, since the first
    /// descent round asks for exactly `k_init + 1`.)
    #[test]
    fn random_cross_check_dpw_aggressive() {
        let mut dpw_exercised = 0u64;
        for seed in 0..900u64 {
            let mut rng = Lcg(seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(13));
            let num_vars = 3 + rng.below(6) as u32;
            let num_hard = rng.below(6) as usize;
            let num_soft = 1 + rng.below(12) as usize;

            let gen_clause = |rng: &mut Lcg| -> Vec<i32> {
                let len = 1 + rng.below(3) as usize;
                (0..len)
                    .map(|_| {
                        let v = 1 + rng.below(num_vars as u64) as i32;
                        if rng.below(2) == 0 {
                            v
                        } else {
                            -v
                        }
                    })
                    .collect()
            };

            let hard: Vec<Vec<i32>> = (0..num_hard).map(|_| gen_clause(&mut rng)).collect();
            let soft: Vec<Vec<i32>> = (0..num_soft).map(|_| gen_clause(&mut rng)).collect();
            // Mixed weights across several bit-widths so `p` (and with it the
            // tare vector and the carry chain) varies seed to seed. Uniform
            // weights never reach here: they are claimed by the count
            // totalizer well before the mixed-weight block.
            let weights: Vec<u64> = {
                let w_max = [3u64, 9, 17, 33][rng.below(4) as usize];
                (0..num_soft).map(|_| 1 + rng.below(w_max)).collect()
            };

            let clause_sat = |clause: &[i32], bits: u64| {
                clause.iter().any(|&lit| {
                    let var = lit.unsigned_abs();
                    let val = (bits >> (var - 1)) & 1 == 1;
                    (lit > 0) == val
                })
            };
            let mut expected: Option<u64> = None;
            for bits in 0..(1u64 << num_vars) {
                if hard.iter().any(|c| !clause_sat(c, bits)) {
                    continue;
                }
                let cost: u64 = soft
                    .iter()
                    .zip(&weights)
                    .filter(|(c, _)| !clause_sat(c, bits))
                    .map(|(_, w)| *w)
                    .sum();
                expected = Some(expected.map_or(cost, |b: u64| b.min(cost)));
            }

            let mut hard_store = ClauseStore::new();
            for c in &hard {
                hard_store.push_from_iter(c.iter().map(|&l| Literal::from(l)));
            }
            let mut soft_store = ClauseStore::new();
            for c in &soft {
                soft_store.push_from_iter(c.iter().map(|&l| Literal::from(l)));
            }
            let mut engine = OllEngine::new(num_vars + 1, hard_store, soft_store, weights.clone());
            engine.set_tuning(OllTuning {
                lsu_min_cores: 0,
                lsu_min_gap_units: 0,
                lsu_stall_ms_per_core: 0,
                force_adder: false,
                abstraction_min_cores: 0,
                force_cluster: false,
                force_dpw: true,
                lp_boost: LpBoostMode::Auto,
                tot_eqs: Some(true),
                core_clause: Some(true),
            });

            let outcome = engine.solve(&|| false, &mut |_| {});
            // Not every seed reaches the watchdog: the count totalizer claims
            // any instance whose LIVE residual has become uniform-weight
            // (hardening can produce that from a mixed fixture), and an
            // instance with no gap never builds a descent at all. The bar
            // below is that the path is genuinely exercised, in the style of
            // `random_cross_check_cluster_aggressive`.
            if matches!(engine.descent, Some(DescentEnc::Dpw { .. })) {
                dpw_exercised += 1;
            }
            // What must NEVER happen: `force_dpw` reaching the mixed-weight
            // block and still landing on the GTE. The watchdog either builds
            // or the instance never got that far.
            assert!(
                !matches!(engine.descent, Some(DescentEnc::Gte { .. })),
                "seed {seed}: force_dpw fell through to the GTE\nweights: {weights:?}",
            );
            match (outcome, expected) {
                (OllOutcome::Optimal { cost, .. }, Some(exp)) => {
                    assert_eq!(
                        cost, exp,
                        "seed {seed}: DPW-aggressive cost {cost} != brute force {exp}\nhard: {hard:?}\nsoft: {soft:?}\nweights: {weights:?}",
                    );
                }
                (OllOutcome::Unsatisfiable, None) => {}
                (got, exp) => panic!(
                    "seed {seed}: {got:?} vs brute force {exp:?}\nhard: {hard:?}\nsoft: {soft:?}",
                ),
            }
        }
        assert!(
            dpw_exercised > 50,
            "force_dpw must actually drive instances through the watchdog \
             descent: only {dpw_exercised} of 900",
        );
    }

    /// #dpw-descent SELECTION. With the production gate (no `force_dpw`), the
    /// watchdog may only displace a GTE it is `DPW_MIN_ADVANTAGE` times
    /// smaller than — DPW is a strictly weaker propagator, so a marginal size
    /// win is not a reason to take it. Checked directly on the predictors,
    /// which is what `select_descent_enc` decides on.
    ///
    /// Kill mutation (`advantage_ignored`): in [`dpw_beats_gte`], change
    /// `dpw_clauses.saturating_mul(DPW_MIN_ADVANTAGE) <= gte_clauses` to
    /// `dpw_clauses <= gte_clauses` (DPW is 51 clauses against the GTE's 54 on
    /// the small fixture, so dropping the margin flips it).
    #[test]
    fn dpw_selection_requires_a_decisive_size_win() {
        // The real af-synthesis shape (170 unit softs, weights 1..9, cap 115):
        // the family DPW exists for.
        let hist: [(Weight, usize); 9] = [
            (1, 17),
            (2, 20),
            (3, 20),
            (4, 16),
            (5, 15),
            (6, 18),
            (7, 22),
            (8, 23),
            (9, 19),
        ];
        let mut af_synthesis: Vec<Weight> = Vec::new();
        for (w, count) in hist {
            for _ in 0..count {
                af_synthesis.push(w);
            }
        }
        // GTE size is ORDER-SENSITIVE — its balanced split gives subtrees far
        // fewer distinct sums when the weights arrive sorted (45,341 clauses
        // here) than in any realistic order (117,870-120,363 over five random
        // permutations; 118,460 in the instance's own file order, which is the
        // order `select_descent_enc` actually hands `gte_build`). Shuffle, so
        // the fixture is not measuring an artefact of how it was constructed.
        {
            let mut rng = Lcg(0x5EED);
            for i in (1..af_synthesis.len()).rev() {
                af_synthesis.swap(i, rng.below(i as u64 + 1) as usize);
            }
        }

        let decide = |weights: &[Weight], cap: Weight| -> Option<(usize, usize, bool)> {
            let inputs: Vec<(Literal, Weight)> = weights
                .iter()
                .map(|&w| (Literal::positive(Variable::new(1)), w))
                .collect();
            let dpw = dpw_size(weights, cap - 1, DPW_VAR_BUDGET, DPW_CLAUSE_BUDGET)?;
            let mut ob = 400_000i64;
            let mut cb = 4_000_000i64;
            let (_, gte_clauses, _) = gte_size(&inputs, cap, &mut ob, &mut cb)?;
            Some((
                dpw.clauses,
                gte_clauses,
                dpw_beats_gte(dpw.clauses, gte_clauses),
            ))
        };

        let (dpw_c, gte_c, take) = decide(&af_synthesis, 115).expect("both encodings fit");
        assert!(
            take,
            "af-synthesis_stb_50_120_5 is the target shape: DPW {dpw_c} vs GTE \
             {gte_c} clauses must select the watchdog",
        );
        assert!(
            gte_c >= dpw_c * 6,
            "the family's measured advantage is 6.0x-11.0x; got {}x (DPW {dpw_c}, \
             GTE {gte_c})",
            gte_c / dpw_c.max(1),
        );

        // A tiny mixed-weight instance: GTE is cheap here and DPW's advantage
        // is asymptotic in the cap, so today's encoding must be kept.
        let tiny: Vec<Weight> = vec![1, 2, 3, 4, 5, 6];
        let (dpw_c, gte_c, take) = decide(&tiny, 8).expect("both encodings fit");
        assert!(
            !take,
            "a small cap must keep the GTE (DPW {dpw_c} vs GTE {gte_c})",
        );
    }

    /// Cluster-descent counterpart (#cluster-descent): near-uniform weights
    /// (a modal band plus small dust) drive the ClusterTot path — the sound
    /// bound is count < ceil(target/band_min) over BAND MEMBERS ONLY, and
    /// the non-tightening round must swap to the exact adder instead of
    /// livelocking. Cross-checked against weighted brute force.
    #[test]
    fn random_cross_check_cluster_aggressive() {
        let mut cluster_exercised = 0u64;
        for seed in 0..300u64 {
            let mut rng = Lcg(seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(29));
            let num_vars = 3 + rng.below(6) as u32;
            let num_hard = rng.below(6) as usize;
            let num_soft = 5 + rng.below(10) as usize;

            let gen_clause = |rng: &mut Lcg| -> Vec<i32> {
                let len = 1 + rng.below(3) as usize;
                (0..len)
                    .map(|_| {
                        let v = 1 + rng.below(num_vars as u64) as i32;
                        if rng.below(2) == 0 {
                            v
                        } else {
                            -v
                        }
                    })
                    .collect()
            };

            let hard: Vec<Vec<i32>> = (0..num_hard).map(|_| gen_clause(&mut rng)).collect();
            let soft: Vec<Vec<i32>> = (0..num_soft).map(|_| gen_clause(&mut rng)).collect();
            // Modal band around 1000 (within 10%) for most softs, small
            // dust weights for every fifth: the rounded-similarity shape.
            let weights: Vec<u64> = (0..num_soft)
                .map(|i| {
                    if i % 5 == 4 {
                        1 + rng.below(5)
                    } else {
                        950 + rng.below(100)
                    }
                })
                .collect();

            let clause_sat = |clause: &[i32], bits: u64| {
                clause.iter().any(|&lit| {
                    let var = lit.unsigned_abs();
                    let val = (bits >> (var - 1)) & 1 == 1;
                    (lit > 0) == val
                })
            };
            let mut expected: Option<u64> = None;
            for bits in 0..(1u64 << num_vars) {
                if hard.iter().any(|c| !clause_sat(c, bits)) {
                    continue;
                }
                let cost: u64 = soft
                    .iter()
                    .zip(&weights)
                    .filter(|(c, _)| !clause_sat(c, bits))
                    .map(|(_, w)| *w)
                    .sum();
                expected = Some(expected.map_or(cost, |b: u64| b.min(cost)));
            }

            let mut hard_store = ClauseStore::new();
            for c in &hard {
                hard_store.push_from_iter(c.iter().map(|&l| Literal::from(l)));
            }
            let mut soft_store = ClauseStore::new();
            for c in &soft {
                soft_store.push_from_iter(c.iter().map(|&l| Literal::from(l)));
            }
            let mut engine = OllEngine::new(num_vars + 1, hard_store, soft_store, weights.clone());
            engine.set_tuning(OllTuning {
                lsu_min_cores: 0,
                lsu_min_gap_units: 0,
                lsu_stall_ms_per_core: 0,
                force_adder: false,
                abstraction_min_cores: 0,
                force_cluster: true,
                force_dpw: false,
                lp_boost: LpBoostMode::Auto,
                // #tot-eqs pinned ON so the reverse-direction clauses are exercised
                // wherever the fixture has >= 2 distinct soft weights. Production also
                // defaults ON (env gate AY_AB_MAXSAT_TOT_EQS != "0"); `tot_eq_budget`
                // is 0 on uniform weights, so the pin is inert on unit-weight fixtures.
                tot_eqs: Some(true),
                core_clause: Some(true),
            });

            let outcome = engine.solve(&|| false, &mut |_| {});
            if matches!(engine.descent, Some(DescentEnc::ClusterTot { .. }))
                || matches!(engine.descent, Some(DescentEnc::Adder { .. }))
            {
                cluster_exercised += 1;
            }
            match (outcome, expected) {
                (OllOutcome::Optimal { cost, .. }, Some(exp)) => {
                    assert_eq!(
                        cost, exp,
                        "seed {seed}: cluster-aggressive cost {cost} != brute force {exp}\nhard: {hard:?}\nsoft: {soft:?}\nweights: {weights:?}",
                    );
                }
                (OllOutcome::Unsatisfiable, None) => {}
                (got, exp) => panic!(
                    "seed {seed}: {got:?} vs brute force {exp:?}\nhard: {hard:?}\nsoft: {soft:?}",
                ),
            }
        }
        assert!(
            cluster_exercised > 0,
            "cluster weights must actually drive instances through ClusterTot",
        );
    }

    /// Weighted counterpart of the aggressive cross-check: mixed weights
    /// drive the GTE descent path on every instance with a nonzero gap.
    #[test]
    fn random_cross_check_adder_aggressive() {
        let mut lsu_exercised = 0u64;
        for seed in 0..300u64 {
            let mut rng = Lcg(seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(29));
            let num_vars = 3 + rng.below(6) as u32;
            let num_hard = rng.below(6) as usize;
            let num_soft = 1 + rng.below(12) as usize;

            let gen_clause = |rng: &mut Lcg| -> Vec<i32> {
                let len = 1 + rng.below(3) as usize;
                (0..len)
                    .map(|_| {
                        let v = 1 + rng.below(num_vars as u64) as i32;
                        if rng.below(2) == 0 {
                            v
                        } else {
                            -v
                        }
                    })
                    .collect()
            };

            let hard: Vec<Vec<i32>> = (0..num_hard).map(|_| gen_clause(&mut rng)).collect();
            let soft: Vec<Vec<i32>> = (0..num_soft).map(|_| gen_clause(&mut rng)).collect();
            // Every third seed: uniform non-unit weights, exercising the
            // uniform-w totalizer descent's ceil(target/w) bound rounding.
            let weights: Vec<u64> = if seed % 3 == 0 {
                let w = 2 + rng.below(5);
                vec![w; num_soft]
            } else {
                (0..num_soft).map(|_| 1 + rng.below(20)).collect()
            };

            let clause_sat = |clause: &[i32], bits: u64| {
                clause.iter().any(|&lit| {
                    let var = lit.unsigned_abs();
                    let val = (bits >> (var - 1)) & 1 == 1;
                    (lit > 0) == val
                })
            };
            let mut expected: Option<u64> = None;
            for bits in 0..(1u64 << num_vars) {
                if hard.iter().any(|c| !clause_sat(c, bits)) {
                    continue;
                }
                let cost: u64 = soft
                    .iter()
                    .zip(&weights)
                    .filter(|(c, _)| !clause_sat(c, bits))
                    .map(|(_, w)| *w)
                    .sum();
                expected = Some(expected.map_or(cost, |b: u64| b.min(cost)));
            }

            let mut hard_store = ClauseStore::new();
            for c in &hard {
                hard_store.push_from_iter(c.iter().map(|&l| Literal::from(l)));
            }
            let mut soft_store = ClauseStore::new();
            for c in &soft {
                soft_store.push_from_iter(c.iter().map(|&l| Literal::from(l)));
            }
            let mut engine = OllEngine::new(num_vars + 1, hard_store, soft_store, weights.clone());
            engine.set_tuning(OllTuning {
                lsu_min_cores: 0,
                lsu_min_gap_units: 0,
                lsu_stall_ms_per_core: 0,
                force_adder: true,
                abstraction_min_cores: 0,
                force_cluster: false,
                force_dpw: false,
                lp_boost: LpBoostMode::Auto,
                // #tot-eqs pinned ON so the reverse-direction clauses are exercised
                // wherever the fixture has >= 2 distinct soft weights. Production also
                // defaults ON (env gate AY_AB_MAXSAT_TOT_EQS != "0"); `tot_eq_budget`
                // is 0 on uniform weights, so the pin is inert on unit-weight fixtures.
                tot_eqs: Some(true),
                core_clause: Some(true),
            });

            let outcome = engine.solve(&|| false, &mut |_| {});
            lsu_exercised += engine.stats().lsu_steps;
            match (outcome, expected) {
                (OllOutcome::Optimal { cost, .. }, Some(exp)) => {
                    assert_eq!(
                        cost, exp,
                        "seed {seed}: adder-aggressive cost {cost} != brute force {exp}\nhard: {hard:?}\nsoft: {soft:?}\nweights: {weights:?}",
                    );
                }
                (OllOutcome::Unsatisfiable, None) => {}
                (got, exp) => panic!(
                    "seed {seed}: {got:?} vs brute force {exp:?}\nhard: {hard:?}\nsoft: {soft:?}",
                ),
            }
        }
        assert!(
            lsu_exercised > 0,
            "aggressive tuning must actually drive instances through the adder descent",
        );
    }

    /// The `lsu_min_cores` conjunct of the descent entry gate: a tuning
    /// that stalls immediately (`lsu_stall_ms_per_core == 0`, zero gap
    /// bar — the aggressive nets above descend under exactly these
    /// settings) but demands more processed cores than any run can
    /// produce must never engage the descent. The exact optimum has to
    /// come from pure leveled OLL, with zero LSU steps.
    ///
    /// The instance is built so a SAT point occurs while lb < ub (the
    /// window where the descent gate can fire): stratification assumes
    /// only the w=10 soft first, the forced unit core lifts lb to 10, and
    /// the follow-up SAT model still violates the unassumed w=1 soft
    /// (ub = 11). Only then does the level drop and close the gap.
    #[test]
    fn lsu_min_cores_blocks_descent() {
        let mut hard_store = ClauseStore::new();
        hard_store.push_from_iter([-1i32].iter().map(|&l| Literal::from(l)));
        hard_store.push_from_iter([-2i32].iter().map(|&l| Literal::from(l)));
        let mut soft_store = ClauseStore::new();
        soft_store.push_from_iter([1i32].iter().map(|&l| Literal::from(l)));
        soft_store.push_from_iter([2i32].iter().map(|&l| Literal::from(l)));
        let weights = vec![10u64, 1u64];
        let mut engine = OllEngine::new(3, hard_store, soft_store, weights);
        engine.set_tuning(OllTuning {
            lsu_min_cores: u64::MAX,
            lsu_min_gap_units: 0,
            lsu_stall_ms_per_core: 0,
            force_adder: false,
            abstraction_min_cores: u64::MAX,
            force_cluster: false,
            force_dpw: false,
            lp_boost: LpBoostMode::Off,
            // #tot-eqs pinned ON so the reverse-direction clauses are exercised
            // wherever the fixture has >= 2 distinct soft weights. Production also
            // defaults ON (env gate AY_AB_MAXSAT_TOT_EQS != "0"); `tot_eq_budget`
            // is 0 on uniform weights, so the pin is inert on unit-weight fixtures.
            tot_eqs: Some(true),
            core_clause: Some(true),
        });
        match engine.solve(&|| false, &mut |_| {}) {
            OllOutcome::Optimal { cost, .. } => assert_eq!(cost, 11),
            other => panic!("expected optimal, got {other:?}"),
        }
        assert_eq!(
            engine.stats().lsu_steps,
            0,
            "descent must not engage before lsu_min_cores cores are processed",
        );
    }

    /// #descent-residual [SOUND-CRITICAL]. `residual_objective` feeds the cut's
    /// `Σ`, and `(★)` only licenses `Σ <= cost - lb` for terms taken ONCE at
    /// their residual weight. Encoding a selector twice, or above its residual,
    /// inflates `Σ` and starts excluding models CHEAPER than the incumbent —
    /// i.e. wrong answers. Dropping terms, or taking a lower weight, only
    /// weakens the cut. So the dedup keeps one entry per selector at the
    /// SMALLEST weight seen, and hardened / zero-weight terms are dropped.
    #[test]
    fn residual_objective_dedups_a_selector_at_its_smallest_weight() {
        let mut soft_store = ClauseStore::new();
        soft_store.push_from_iter([1i32].iter().map(|&l| Literal::from(l)));
        let mut engine = OllEngine::new(6, ClauseStore::new(), soft_store, vec![1u64]);
        let (a, b, c, d) = (
            Literal::from(2i32),
            Literal::from(3i32),
            Literal::from(4i32),
            Literal::from(5i32),
        );
        engine.active.clear();
        engine.pool.clear();
        engine.hardened_sels.clear();
        // `a` in both stores at different weights (defensive: activate_level
        // moves entries, so nothing is in both today).
        engine.active.insert(a, 40);
        engine.pool.push((a, 7));
        engine.active.insert(b, 5);
        // Dropped: zero residual weight, and hardened (satisfied in every
        // remaining model).
        engine.active.insert(c, 0);
        engine.active.insert(d, 9);
        engine.hardened_sels.insert(d);

        let terms = engine.residual_objective();
        assert_eq!(
            terms.iter().filter(|&&(s, _)| s == a).count(),
            1,
            "a selector must be encoded at most once: {terms:?}",
        );
        assert_eq!(
            terms.iter().find(|&&(s, _)| s == a).map(|&(_, w)| w),
            Some(7),
            "a duplicated selector must take its SMALLEST weight: {terms:?}",
        );
        assert_eq!(
            terms.iter().find(|&&(s, _)| s == b).map(|&(_, w)| w),
            Some(5)
        );
        assert!(
            !terms.iter().any(|&(s, _)| s == c),
            "zero-weight terms carry no cost: {terms:?}",
        );
        assert!(
            !terms.iter().any(|&(s, _)| s == d),
            "hardened selectors are satisfied in every remaining model: {terms:?}",
        );
        // Sorted, so the encoding cannot depend on `active`'s hash order.
        assert!(terms.windows(2).all(|w| w[0].0 < w[1].0), "{terms:?}");
    }
}

#[cfg(test)]
mod level_tests {
    use super::*;

    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0 >> 33
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    /// Pure-OLL tuning: descents and abstraction sets fully out of the way,
    /// so instances run the adaptive leveling (#climit-discipline) all the
    /// way to the level-1 terminal — assumption filtering, per-level cores,
    /// residual-mass hardening, exhaustion and suspension included.
    fn pure_oll_tuning() -> OllTuning {
        OllTuning {
            lsu_min_cores: u64::MAX,
            lsu_min_gap_units: Weight::MAX,
            lsu_stall_ms_per_core: 30,
            force_adder: false,
            abstraction_min_cores: u64::MAX,
            force_cluster: false,
            force_dpw: false,
            lp_boost: LpBoostMode::Auto,
            // #tot-eqs pinned ON so the reverse-direction clauses are exercised
            // wherever the fixture has >= 2 distinct soft weights. Production also
            // defaults ON (env gate AY_AB_MAXSAT_TOT_EQS != "0"); `tot_eq_budget`
            // is 0 on uniform weights, so the pin is inert on unit-weight fixtures.
            tot_eqs: Some(true),
            core_clause: Some(true),
        }
    }

    /// 300-seed brute-force net for the climit discipline: the mpe shape —
    /// weights spanning 1..2000, mostly unique, so nearly every soft is its
    /// own weight level and the adaptive level scheduler (strat + BLO rules,
    /// terminal level 1) drives the whole run. Descents are disabled: the
    /// run must reach the exact optimum through leveled OLL alone, making
    /// the level-1 terminal argument (cost == lb when nothing is filtered
    /// and nothing suspended) the load-bearing exit on every SAT instance.
    #[test]
    fn random_cross_check_level_discipline_aggressive() {
        let mut multi_level = 0u64;
        for seed in 0..300u64 {
            let mut rng = Lcg(seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(53));
            let num_vars = 3 + rng.below(6) as u32;
            let num_hard = rng.below(6) as usize;
            let num_soft = 6 + rng.below(12) as usize;

            let gen_clause = |rng: &mut Lcg| -> Vec<i32> {
                let len = 1 + rng.below(3) as usize;
                (0..len)
                    .map(|_| {
                        let v = 1 + rng.below(num_vars as u64) as i32;
                        if rng.below(2) == 0 {
                            v
                        } else {
                            -v
                        }
                    })
                    .collect()
            };

            let hard: Vec<Vec<i32>> = (0..num_hard).map(|_| gen_clause(&mut rng)).collect();
            let soft: Vec<Vec<i32>> = (0..num_soft).map(|_| gen_clause(&mut rng)).collect();
            // The mpe weight shape: wide span, mostly distinct.
            let weights: Vec<u64> = (0..num_soft).map(|_| 1 + rng.below(2000)).collect();

            let clause_sat = |clause: &[i32], bits: u64| {
                clause.iter().any(|&lit| {
                    let var = lit.unsigned_abs();
                    let val = (bits >> (var - 1)) & 1 == 1;
                    (lit > 0) == val
                })
            };
            let mut expected: Option<u64> = None;
            for bits in 0..(1u64 << num_vars) {
                if hard.iter().any(|c| !clause_sat(c, bits)) {
                    continue;
                }
                let cost: u64 = soft
                    .iter()
                    .zip(&weights)
                    .filter(|(c, _)| !clause_sat(c, bits))
                    .map(|(_, w)| *w)
                    .sum();
                expected = Some(expected.map_or(cost, |b: u64| b.min(cost)));
            }

            let mut hard_store = ClauseStore::new();
            for c in &hard {
                hard_store.push_from_iter(c.iter().map(|&l| Literal::from(l)));
            }
            let mut soft_store = ClauseStore::new();
            for c in &soft {
                soft_store.push_from_iter(c.iter().map(|&l| Literal::from(l)));
            }
            let mut engine = OllEngine::new(num_vars + 1, hard_store, soft_store, weights.clone());
            engine.set_tuning(pure_oll_tuning());

            let outcome = engine.solve(&|| false, &mut |_| {});
            if engine.stats().strat_levels > 1 {
                multi_level += 1;
            }
            match (outcome, expected) {
                (OllOutcome::Optimal { cost, .. }, Some(exp)) => {
                    assert_eq!(
                        cost, exp,
                        "seed {seed}: level-discipline cost {cost} != brute force {exp}\nhard: {hard:?}\nsoft: {soft:?}\nweights: {weights:?}",
                    );
                }
                (OllOutcome::Unsatisfiable, None) => {}
                (got, exp) => panic!(
                    "seed {seed}: {got:?} vs brute force {exp:?}\nhard: {hard:?}\nsoft: {soft:?}",
                ),
            }
        }
        // Tiny instances often go terminal on the first schedule (few softs
        // means the strat rule seldom fires — exactly CGSS2's behavior);
        // measured 96/300 walk 2+ levels under these seeds.
        assert!(
            multi_level > 50,
            "many-distinct-weight instances must actually walk multiple levels (got {multi_level})",
        );
    }

    /// UNWEIGHTED/uniform identity: uniform weights collapse to a single
    /// scheduled level — the terminal level 1 — from the very first SAT
    /// call, so nothing is ever filtered and the engine behaves exactly
    /// like the pre-leveling one.
    #[test]
    fn uniform_weights_schedule_single_level() {
        // x1..x4 pairwise-conflicting units: optimum violates 3 of 4.
        let n: i32 = 4;
        let mut hard_store = ClauseStore::new();
        for a in 1..=n {
            for b in (a + 1)..=n {
                hard_store.push_from_iter([-a, -b].iter().map(|&l| Literal::from(l)));
            }
        }
        let mut soft_store = ClauseStore::new();
        for i in 1..=n {
            soft_store.push_from_iter([i].iter().map(|&l| Literal::from(l)));
        }
        let weights = vec![7u64; n as usize];
        let mut engine = OllEngine::new(n as u32 + 1, hard_store, soft_store, weights);
        engine.set_tuning(pure_oll_tuning());
        match engine.solve(&|| false, &mut |_| {}) {
            OllOutcome::Optimal { cost, .. } => assert_eq!(cost, 21),
            other => panic!("expected optimal, got {other:?}"),
        }
        assert_eq!(
            engine.stats().strat_levels,
            1,
            "uniform weights must schedule exactly one level",
        );
        assert_eq!(engine.level, 1, "the single uniform level is terminal");
    }

    /// Two-scale weights walk at least two levels and still land on the
    /// exact optimum: heavy pairwise-conflicting units force two heavy
    /// violations at the top level (each core paying the full 1000 into
    /// lb), and the dust is only assumed after the level drops.
    #[test]
    fn two_scale_weights_walk_levels() {
        let mut hard_store = ClauseStore::new();
        for a in 1..=3i32 {
            for b in (a + 1)..=3i32 {
                hard_store.push_from_iter([-a, -b].iter().map(|&l| Literal::from(l)));
            }
        }
        // x4, x5, x6 cannot all hold: some dust must be paid too.
        hard_store.push_from_iter([-4i32, -5, -6].iter().map(|&l| Literal::from(l)));
        let mut soft_store = ClauseStore::new();
        for i in 1..=6i32 {
            soft_store.push_from_iter([i].iter().map(|&l| Literal::from(l)));
        }
        let weights = vec![1000u64, 1000, 1000, 1, 2, 3];
        let mut engine = OllEngine::new(7, hard_store, soft_store, weights);
        engine.set_tuning(pure_oll_tuning());
        match engine.solve(&|| false, &mut |_| {}) {
            // Two heavy violations (2000) + the cheapest dust violation (1).
            OllOutcome::Optimal { cost, .. } => assert_eq!(cost, 2001),
            other => panic!("expected optimal, got {other:?}"),
        }
        assert!(
            engine.stats().strat_levels >= 2,
            "two weight scales must walk at least two levels (got {})",
            engine.stats().strat_levels,
        );
        assert_eq!(engine.level, 1, "run must end at the terminal level");
    }
}

#[cfg(test)]
mod wce_tests {
    use super::*;

    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0 >> 33
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    /// Pure-OLL tuning with the LP lane hard-off: descents never fire (no
    /// completed 5s stall window on these instant instances) and no LP
    /// round can trigger the (c) flush, so every WCE flush in this net
    /// comes from the load-bearing phase-end triggers — (a) the Sat arm
    /// and (b) the empty-assumption rebuild.
    fn wce_tuning() -> OllTuning {
        OllTuning {
            lsu_min_cores: u64::MAX,
            lsu_min_gap_units: Weight::MAX,
            lsu_stall_ms_per_core: 30,
            force_adder: false,
            abstraction_min_cores: u64::MAX,
            force_cluster: false,
            force_dpw: false,
            lp_boost: LpBoostMode::Off,
            // #tot-eqs pinned ON so the reverse-direction clauses are exercised
            // wherever the fixture has >= 2 distinct soft weights. Production also
            // defaults ON (env gate AY_AB_MAXSAT_TOT_EQS != "0"); `tot_eq_budget`
            // is 0 on uniform weights, so the pin is inert on unit-weight fixtures.
            tot_eqs: Some(true),
            core_clause: Some(true),
        }
    }

    /// 300-seed brute-force net for weight-aware core extraction (#wce):
    /// core-rich instances (the lp-boost net's clause shape) with the mpe
    /// weight profile (1..2000, mostly distinct), so multi-member cores
    /// queue on `pending_relax` and materialize in batches at the Sat-arm
    /// and empty-assumption flush points, interleaved with the climit
    /// level walk. Every seed must land on the exact brute-force optimum,
    /// and the net must witness actual BATCHING — some seed flushing >= 2
    /// deferred cores in a single flush — or WCE has degenerated into
    /// eager relaxation with extra steps.
    #[test]
    fn random_cross_check_wce_batches_cores() {
        let mut flushes = 0u64;
        let mut relaxed = 0u64;
        let mut batched_seeds = 0u64;
        for seed in 0..300u64 {
            let mut rng = Lcg(seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(97));
            let num_vars = 4 + rng.below(5) as u32;
            let num_hard = 2 + rng.below(8) as usize;
            let num_soft = 8 + rng.below(12) as usize;

            let gen_clause = |rng: &mut Lcg| -> Vec<i32> {
                let len = 1 + rng.below(3) as usize;
                (0..len)
                    .map(|_| {
                        let v = 1 + rng.below(num_vars as u64) as i32;
                        if rng.below(2) == 0 {
                            v
                        } else {
                            -v
                        }
                    })
                    .collect()
            };

            let hard: Vec<Vec<i32>> = (0..num_hard).map(|_| gen_clause(&mut rng)).collect();
            let soft: Vec<Vec<i32>> = (0..num_soft).map(|_| gen_clause(&mut rng)).collect();
            // The mpe weight shape: wide span, mostly distinct weights.
            let weights: Vec<u64> = (0..num_soft).map(|_| 1 + rng.below(2000)).collect();

            let clause_sat = |clause: &[i32], bits: u64| {
                clause.iter().any(|&lit| {
                    let var = lit.unsigned_abs();
                    let val = (bits >> (var - 1)) & 1 == 1;
                    (lit > 0) == val
                })
            };
            let mut expected: Option<u64> = None;
            for bits in 0..(1u64 << num_vars) {
                if hard.iter().any(|c| !clause_sat(c, bits)) {
                    continue;
                }
                let cost: u64 = soft
                    .iter()
                    .zip(&weights)
                    .filter(|(c, _)| !clause_sat(c, bits))
                    .map(|(_, w)| *w)
                    .sum();
                expected = Some(expected.map_or(cost, |b: u64| b.min(cost)));
            }

            let mut hard_store = ClauseStore::new();
            for c in &hard {
                hard_store.push_from_iter(c.iter().map(|&l| Literal::from(l)));
            }
            let mut soft_store = ClauseStore::new();
            for c in &soft {
                soft_store.push_from_iter(c.iter().map(|&l| Literal::from(l)));
            }
            let mut engine = OllEngine::new(num_vars + 1, hard_store, soft_store, weights.clone());
            engine.set_tuning(wce_tuning());

            let outcome = engine.solve(&|| false, &mut |_| {});
            flushes += engine.stats().wce_flushes;
            relaxed += engine.stats().wce_relaxed_cores;
            if engine.stats().wce_max_flush_batch >= 2 {
                batched_seeds += 1;
            }
            match (outcome, expected) {
                (OllOutcome::Optimal { cost, .. }, Some(exp)) => {
                    assert_eq!(
                        cost, exp,
                        "seed {seed}: wce cost {cost} != brute force {exp}\nhard: {hard:?}\nsoft: {soft:?}\nweights: {weights:?}",
                    );
                }
                (OllOutcome::Unsatisfiable, None) => {}
                (got, exp) => panic!(
                    "seed {seed}: {got:?} vs brute force {exp:?}\nhard: {hard:?}\nsoft: {soft:?}",
                ),
            }
        }
        assert!(
            flushes > 0 && relaxed >= flushes,
            "net must exercise WCE flushes (flushes={flushes} relaxed={relaxed})",
        );
        assert!(
            batched_seeds > 0,
            "some seeds must batch >= 2 deferred cores in one flush (got {batched_seeds})",
        );
    }
}

#[cfg(test)]
mod minimize_tests {
    use super::*;

    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0 >> 33
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    /// Pure-OLL tuning (descents and LP lane off) so every core flows
    /// through the trim -> minimize -> process_core path of the main loop.
    fn minimize_tuning() -> OllTuning {
        OllTuning {
            lsu_min_cores: u64::MAX,
            lsu_min_gap_units: Weight::MAX,
            lsu_stall_ms_per_core: 30,
            force_adder: false,
            abstraction_min_cores: u64::MAX,
            force_cluster: false,
            force_dpw: false,
            lp_boost: LpBoostMode::Off,
            // #tot-eqs pinned ON so the reverse-direction clauses are exercised
            // wherever the fixture has >= 2 distinct soft weights. Production also
            // defaults ON (env gate AY_AB_MAXSAT_TOT_EQS != "0"); `tot_eq_budget`
            // is 0 on uniform weights, so the pin is inert on unit-weight fixtures.
            tot_eqs: Some(true),
            core_clause: Some(true),
        }
    }

    /// One REDUNDANT-FORCER gadget instance: m unit-soft selectors
    /// p_1..p_m over a wide-clause conflict where exactly one selector is
    /// semantically removable.
    ///
    ///   - forcers p_j -> a_{perm(j)} covering a_1..a_{m-1}, plus a
    ///     REDUNDANT forcer p_r -> a_m;
    ///   - wide clause (!a_1 v ... v !a_m) — the conflict;
    ///   - hidden chain (!a_1 v ... v !a_{m-1} v t), (!t v a_m) — makes
    ///     p_r removable: without its forcer a_m is still chain-forced.
    ///
    /// {p_1..p_m} is UNSAT; {p_1..p_m} \ {p_r} is UNSAT (the chain forces
    /// a_m through t); dropping any OTHER selector leaves its auxiliary
    /// free and the wide clause satisfiable. So the unique minimal core is
    /// the (m-1)-member set without p_r, and any core containing p_r is
    /// non-minimal. The chain hides behind the fresh variable t because a
    /// single-clause chain resolves with the wide clause on a_m and clause
    /// strengthening would erase the redundancy inside the SAT solver.
    ///
    /// The redundant selector gets weight w_lo, everyone else w_hi > w_lo:
    /// removing p_r RAISES the core's w_min — the exact payoff deletion
    /// minimization exists for. Optimum is analytic: at least one
    /// non-redundant soft must fall (falsifying only p_r leaves a_m
    /// chain-forced into the wide clause) and exactly one suffices, so the
    /// optimum cost is w_hi.
    #[allow(clippy::type_complexity)]
    fn gadget(
        rng: &mut Lcg,
    ) -> (
        Vec<Vec<i32>>,
        Vec<Vec<i32>>,
        Vec<u64>,
        usize,
        usize,
        u64,
        u64,
    ) {
        // m in 10..=13 keeps every core above the len > 8 minimize gate
        // even after the removal.
        let m = (10 + rng.below(4)) as usize;
        // Vars: p_1..p_m = 1..=m, a_1..a_m = m+1..=2m, t = 2m+1.
        let a = |i: usize| (m + 1 + i) as i32; // a_(i+1) for i in 0..m
        let w_hi = 3 + rng.below(6);
        let w_lo = 1 + rng.below(w_hi - 2);
        // Redundant selector index, strictly inside 1..=m-2 so it sits in
        // the middle of both assumption orders.
        let r = 1 + rng.below(m as u64 - 2) as usize;
        // Random assignment of the m-1 chain forcers to the non-redundant
        // selectors (Fisher-Yates on the target list).
        let mut targets: Vec<usize> = (0..m - 1).collect();
        for i in (1..targets.len()).rev() {
            let j = rng.below(i as u64 + 1) as usize;
            targets.swap(i, j);
        }

        let mut hard: Vec<Vec<i32>> = Vec::new();
        let mut ti = 0;
        for j in 0..m {
            let p = (j + 1) as i32;
            if j == r {
                hard.push(vec![-p, a(m - 1)]); // redundant forcer -> a_m
            } else {
                hard.push(vec![-p, a(targets[ti])]);
                ti += 1;
            }
        }
        // Wide conflict clause over all auxiliaries.
        hard.push((0..m).map(|i| -a(i)).collect());
        // Hidden chain: a_1..a_{m-1} force t, t forces a_m.
        let t = (2 * m + 1) as i32;
        let mut chain: Vec<i32> = (0..m - 1).map(|i| -a(i)).collect();
        chain.push(t);
        hard.push(chain);
        hard.push(vec![-t, a(m - 1)]);

        let soft: Vec<Vec<i32>> = (1..=m as i32).map(|p| vec![p]).collect();
        let weights: Vec<u64> = (0..m).map(|j| if j == r { w_lo } else { w_hi }).collect();
        (hard, soft, weights, m, r, w_hi, w_lo)
    }

    fn stores(hard: &[Vec<i32>], soft: &[Vec<i32>]) -> (ClauseStore, ClauseStore) {
        let mut hard_store = ClauseStore::new();
        for c in hard {
            hard_store.push_from_iter(c.iter().map(|&l| Literal::from(l)));
        }
        let mut soft_store = ClauseStore::new();
        for c in soft {
            soft_store.push_from_iter(c.iter().map(|&l| Literal::from(l)));
        }
        (hard_store, soft_store)
    }

    /// 300-seed net for deletion-based core minimization (#minimize), two
    /// halves per seed on the same randomized gadget instance:
    ///
    /// (1) DIRECT: hand `minimize_core` the full m-member core exactly as
    ///     the solve loop would after trim. Whether the engine's own first
    ///     extraction is fat is a solver-heuristic accident (measured: the
    ///     backward core BFS plus preprocessing usually reach the minimal
    ///     core on propagation-only conflicts, and clause strengthening
    ///     erases syntactic redundancy — fat non-minimal cores are a
    ///     deep-search phenomenon that cannot be produced deterministically
    ///     at test scale), so the net constructs the non-minimal core
    ///     explicitly and asserts the deletion sweep repairs it: the
    ///     weight-ascending order probes the CHEAP redundant member first,
    ///     the solver-returned replacement core drops it, both stats
    ///     counters fire, and the surviving w_min RISES from w_lo to w_hi.
    ///     process_core is then invoked on the minimized core and must pay
    ///     the RAISED w_min into lb and queue (members, w_hi) on the WCE
    ///     pending list — the downstream-soundness wiring of #minimize.
    ///
    /// (2) END-TO-END: a fresh engine solves the same instance through the
    ///     full OLL loop (trim -> minimize -> WCE -> climit level walk;
    ///     len > 8 cores flow through minimize probes every seed) and must
    ///     land exactly on the analytic optimum w_hi.
    #[test]
    fn minimize_gadget_fires_and_stays_exact() {
        let mut minimized = 0u64;
        let mut removed = 0u64;
        for seed in 0..300u64 {
            let mut rng = Lcg(seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(151));
            let (hard, soft, weights, m, r, w_hi, w_lo) = gadget(&mut rng);
            let num_vars = (2 * m + 1) as u32;

            // ---- (1) direct minimize_core on the constructed fat core.
            let (hard_store, soft_store) = stores(&hard, &soft);
            let mut engine = OllEngine::new(num_vars + 1, hard_store, soft_store, weights.clone());
            // Selectors of unit softs are the literals themselves; activate
            // them at their weights as the solve loop's stratum would.
            let core: Vec<Literal> = (1..=m as i32).map(Literal::from).collect();
            for (j, &sel) in core.iter().enumerate() {
                engine.active.insert(sel, weights[j]);
            }
            let p_r = core[r];
            let out = engine.minimize_core(core.clone(), &|| false);
            assert_eq!(
                out.len(),
                m - 1,
                "seed {seed}: minimize must certify the unique minimal core\nhard: {hard:?}",
            );
            assert!(
                !out.contains(&p_r),
                "seed {seed}: the redundant selector must be the one removed",
            );
            assert_eq!(engine.stats().cores_minimized, 1, "seed {seed}");
            assert_eq!(engine.stats().minimize_removed_literals, 1, "seed {seed}");
            let w_min_after = out
                .iter()
                .map(|sel| engine.active[sel])
                .min()
                .expect("nonempty core");
            assert_eq!(
                w_min_after, w_hi,
                "seed {seed}: dropping the cheap member must raise w_min from {w_lo} to {w_hi}",
            );
            // Downstream wiring: the lb payment and the WCE queue entry use
            // the POST-minimization w_min.
            engine.process_core(&out, CoreOrigin::Search);
            assert_eq!(
                engine.lb, w_hi,
                "seed {seed}: lb must be paid at the post-minimization w_min",
            );
            let (pending, pending_w) = engine.pending_relax.last().expect("core queued for WCE");
            assert_eq!(pending.len(), m - 1, "seed {seed}");
            assert_eq!(*pending_w, w_hi, "seed {seed}");
            minimized += engine.stats().cores_minimized;
            removed += engine.stats().minimize_removed_literals;

            // ---- (2) end-to-end solve on a fresh engine, exact optimum.
            let (hard_store, soft_store) = stores(&hard, &soft);
            let mut engine = OllEngine::new(num_vars + 1, hard_store, soft_store, weights.clone());
            engine.set_tuning(minimize_tuning());
            match engine.solve(&|| false, &mut |_| {}) {
                OllOutcome::Optimal { cost, .. } => {
                    assert_eq!(
                        cost, w_hi,
                        "seed {seed}: gadget cost {cost} != analytic optimum {w_hi}\nhard: {hard:?}\nweights: {weights:?}",
                    );
                }
                got => panic!("seed {seed}: {got:?} on a satisfiable gadget"),
            }
        }
        assert!(
            minimized == 300 && removed == 300,
            "every seed must witness deletion minimization firing (cores_minimized={minimized} removed={removed})",
        );
    }
}

#[cfg(test)]
mod lp_boost_tests {
    use super::*;

    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0 >> 33
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    /// 300-seed brute-force net for the LP-boost lane (#lp-boost): weighted
    /// random instances with the lane force-enabled and aggressive stall
    /// tuning, so the dual packing LP is built, budget-solved, certified,
    /// and consulted by the termination tests mid-run on every instance
    /// that yields pure-original cores. The lane must NEVER cause a wrong
    /// optimum claim: exact equality against weighted brute force.
    #[test]
    fn random_cross_check_lp_boost_aggressive() {
        let mut boost_ran = 0u64;
        for seed in 0..300u64 {
            let mut rng = Lcg(seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(41));
            // Core-richer shape than the sibling nets: more hard clauses and
            // more softs per variable so most seeds extract several
            // pure-original cores before converging, driving LP rounds.
            let num_vars = 4 + rng.below(5) as u32;
            let num_hard = 2 + rng.below(8) as usize;
            let num_soft = 8 + rng.below(12) as usize;

            let gen_clause = |rng: &mut Lcg| -> Vec<i32> {
                let len = 1 + rng.below(3) as usize;
                (0..len)
                    .map(|_| {
                        let v = 1 + rng.below(num_vars as u64) as i32;
                        if rng.below(2) == 0 {
                            v
                        } else {
                            -v
                        }
                    })
                    .collect()
            };

            let hard: Vec<Vec<i32>> = (0..num_hard).map(|_| gen_clause(&mut rng)).collect();
            let soft: Vec<Vec<i32>> = (0..num_soft).map(|_| gen_clause(&mut rng)).collect();
            // Wide weight spread: the shape the lane is built for (many
            // distinct weights, overlapping cores across weight classes).
            let weights: Vec<u64> = (0..num_soft)
                .map(|i| match i % 3 {
                    0 => 1 + rng.below(4),
                    1 => 5 + rng.below(15),
                    _ => 20 + rng.below(80),
                })
                .collect();

            let clause_sat = |clause: &[i32], bits: u64| {
                clause.iter().any(|&lit| {
                    let var = lit.unsigned_abs();
                    let val = (bits >> (var - 1)) & 1 == 1;
                    (lit > 0) == val
                })
            };
            let mut expected: Option<u64> = None;
            for bits in 0..(1u64 << num_vars) {
                if hard.iter().any(|c| !clause_sat(c, bits)) {
                    continue;
                }
                let cost: u64 = soft
                    .iter()
                    .zip(&weights)
                    .filter(|(c, _)| !clause_sat(c, bits))
                    .map(|(_, w)| *w)
                    .sum();
                expected = Some(expected.map_or(cost, |b: u64| b.min(cost)));
            }

            let mut hard_store = ClauseStore::new();
            for c in &hard {
                hard_store.push_from_iter(c.iter().map(|&l| Literal::from(l)));
            }
            let mut soft_store = ClauseStore::new();
            for c in &soft {
                soft_store.push_from_iter(c.iter().map(|&l| Literal::from(l)));
            }
            let mut engine = OllEngine::new(num_vars + 1, hard_store, soft_store, weights.clone());
            engine.set_tuning(OllTuning {
                lsu_min_cores: 0,
                lsu_min_gap_units: 0,
                lsu_stall_ms_per_core: 0,
                force_adder: false,
                // Keep abstraction sets out so original selectors stay
                // original and the pure-original store fills up.
                abstraction_min_cores: u64::MAX,
                force_cluster: false,
                force_dpw: false,
                lp_boost: LpBoostMode::Force,
                // #tot-eqs pinned ON so the reverse-direction clauses are exercised
                // wherever the fixture has >= 2 distinct soft weights. Production also
                // defaults ON (env gate AY_AB_MAXSAT_TOT_EQS != "0"); `tot_eq_budget`
                // is 0 on uniform weights, so the pin is inert on unit-weight fixtures.
                tot_eqs: Some(true),
                core_clause: Some(true),
            });

            let outcome = engine.solve(&|| false, &mut |_| {});
            boost_ran += engine.stats().lp_boost_runs;
            match (outcome, expected) {
                (OllOutcome::Optimal { cost, .. }, Some(exp)) => {
                    assert_eq!(
                        cost, exp,
                        "seed {seed}: lp-boost-aggressive cost {cost} != brute force {exp}\nhard: {hard:?}\nsoft: {soft:?}\nweights: {weights:?}",
                    );
                }
                (OllOutcome::Unsatisfiable, None) => {}
                (got, exp) => panic!(
                    "seed {seed}: {got:?} vs brute force {exp:?}\nhard: {hard:?}\nsoft: {soft:?}",
                ),
            }
        }
        assert!(
            boost_ran > 0,
            "force-enabled lane must actually run LP rounds across the net",
        );
    }

    /// The lane must not activate on uniform weights under Auto (default
    /// mode): unweighted-track behavior stays identical to the lane-free
    /// engine. Aggressive stall tuning makes the stall trigger fire on the
    /// first loop iteration, so a missing gate would be caught here.
    #[test]
    fn lp_boost_gated_off_on_uniform_weights() {
        // x1..x4 pairwise-conflicting units: optimum violates 3 of 4.
        let n: i32 = 4;
        let mut hard_store = ClauseStore::new();
        for a in 1..=n {
            for b in (a + 1)..=n {
                hard_store.push_from_iter([-a, -b].iter().map(|&l| Literal::from(l)));
            }
        }
        let mut soft_store = ClauseStore::new();
        for i in 1..=n {
            soft_store.push_from_iter([i].iter().map(|&l| Literal::from(l)));
        }
        let weights = vec![7u64; n as usize];
        let mut engine = OllEngine::new(n as u32 + 1, hard_store, soft_store, weights);
        engine.set_tuning(OllTuning {
            lsu_min_cores: 0,
            lsu_min_gap_units: 0,
            lsu_stall_ms_per_core: 0,
            force_adder: false,
            abstraction_min_cores: u64::MAX,
            force_cluster: false,
            force_dpw: false,
            lp_boost: LpBoostMode::Auto,
            // #tot-eqs pinned ON so the reverse-direction clauses are exercised
            // wherever the fixture has >= 2 distinct soft weights. Production also
            // defaults ON (env gate AY_AB_MAXSAT_TOT_EQS != "0"); `tot_eq_budget`
            // is 0 on uniform weights, so the pin is inert on unit-weight fixtures.
            tot_eqs: Some(true),
            core_clause: Some(true),
        });
        match engine.solve(&|| false, &mut |_| {}) {
            OllOutcome::Optimal { cost, .. } => assert_eq!(cost, 21),
            other => panic!("expected optimal, got {other:?}"),
        }
        assert_eq!(
            engine.stats().lp_boost_runs,
            0,
            "lane must not run on uniform weights in Auto mode",
        );
        assert_eq!(engine.boost_lb, 0);
        assert!(engine.lp_cores.is_empty(), "capture must be gated too");
    }

    /// Deterministic injection: two disjoint single-soft packing rows with
    /// weights 7 and 9 have LP optimum exactly 16; run_lp_boost must solve,
    /// certify (exact fixed-point check), and inject it into boost_lb /
    /// effective_lb. Rows are stuffed directly — this tests the LP plumbing
    /// only, so solve() is deliberately NOT called afterwards.
    #[test]
    fn lp_boost_injects_certified_disjoint_core_bound() {
        let mut soft_store = ClauseStore::new();
        soft_store.push_from_iter([1i32].iter().map(|&l| Literal::from(l)));
        soft_store.push_from_iter([2i32].iter().map(|&l| Literal::from(l)));
        // Equal weights: keeps the packing bound at 16 while staying outside
        // #maxsat-bmo-promote's boundary rule (a lone dominating weight would
        // be promoted to hard at construction, shifting the raw soft indices
        // this white-box fixture injects below).
        let mut engine = OllEngine::new(3, ClauseStore::new(), soft_store, vec![8, 8]);
        engine.set_tuning(OllTuning {
            lp_boost: LpBoostMode::Force,
            // #tot-eqs pinned ON so the reverse-direction clauses are exercised
            // wherever the fixture has >= 2 distinct soft weights. Production also
            // defaults ON (env gate AY_AB_MAXSAT_TOT_EQS != "0"); `tot_eq_budget`
            // is 0 on uniform weights, so the pin is inert on unit-weight fixtures.
            tot_eqs: Some(true),
            core_clause: Some(true),
            ..OllTuning::default()
        });
        engine.lp_cores.push(vec![0]);
        engine.lp_cores.push(vec![1]);

        engine.run_lp_boost(&|| false);
        assert_eq!(engine.boost_lb, 16, "packing bound of disjoint rows");
        assert_eq!(engine.effective_lb(), 16);
        assert_eq!(engine.stats().lp_boost_runs, 1);
        assert_eq!(engine.stats().lp_boost_improvements, 1);

        // Re-running without new information is a dry round; three of them
        // must auto-disable the lane.
        for _ in 0..LP_BOOST_MAX_DRY_ROUNDS {
            assert!(!engine.lp_disabled);
            engine.run_lp_boost(&|| false);
        }
        assert!(engine.lp_disabled, "dry-round rule must disable the lane");
        assert_eq!(engine.boost_lb, 16, "bound survives disablement");
    }

    /// The exact certifier must (a) repair infeasible float noise by
    /// shrinking (never accept a column above its weight capacity), (b)
    /// recover near-integer values via the epsilon-floor, and (c) never
    /// exceed ceil(true packing value) on genuinely fractional inputs.
    #[test]
    fn lp_certified_bound_repairs_noise_and_never_overshoots() {
        let mut soft_store = ClauseStore::new();
        for i in 1..=3i32 {
            soft_store.push_from_iter([i].iter().map(|&l| Literal::from(l)));
        }
        // Weights: s0 = 5, s1 = 3, s2 = 3 (unit softs on x1, x2, x3).
        let mut engine = OllEngine::new(4, ClauseStore::new(), soft_store, vec![5, 3, 3]);
        engine.lp_cores.push(vec![0, 1]); // y0: rows s0, s1
        engine.lp_cores.push(vec![0, 2]); // y1: rows s0, s2

        // Slightly infeasible noise on the shared s0 row (3 + 2.0000002 > 5):
        // must certify at most 5 and, after repair, exactly 5.
        assert_eq!(engine.lp_certified_bound(&[3.0000001, 2.0000002]), 5);
        // Near-integer from below: epsilon-floor recovers 5.
        assert_eq!(engine.lp_certified_bound(&[2.9999999, 1.9999999]), 5);
        // Grossly infeasible input: scaled back to the s0 capacity.
        assert_eq!(engine.lp_certified_bound(&[10.0, 10.0]), 5);
        // Non-finite garbage is dropped, not propagated.
        assert_eq!(engine.lp_certified_bound(&[f64::NAN, 2.0]), 2);
        assert_eq!(engine.lp_certified_bound(&[f64::INFINITY, 1.0]), 1);
        // Length mismatch is rejected outright.
        assert_eq!(engine.lp_certified_bound(&[1.0]), 0);

        // Fractional packing (triangle): true LP optimum 1.5 must round
        // DOWN to 1 — a raw ceil here would be the unsound footgun.
        let mut soft_store = ClauseStore::new();
        for i in 1..=3i32 {
            soft_store.push_from_iter([i].iter().map(|&l| Literal::from(l)));
        }
        let mut tri = OllEngine::new(4, ClauseStore::new(), soft_store, vec![1, 1, 1]);
        tri.lp_cores.push(vec![0, 1]);
        tri.lp_cores.push(vec![1, 2]);
        tri.lp_cores.push(vec![0, 2]);
        assert_eq!(tri.lp_certified_bound(&[0.5, 0.5, 0.5]), 1);
    }

    /// The kick gap bar is scale-relative, and its floor is the old absolute
    /// constant. Three properties, in the order they protect something:
    ///
    /// 1. It is NEVER below `DESCENT_KICK_GAP`. That is the structural reason
    ///    this change cannot take a descent entry away from an instance that
    ///    had one, i.e. it cannot un-solve any of the 334 currently solved.
    /// 2. It measures the gap in the finest granularity the residual objective
    ///    can move by — the MINIMUM live weight — and hardened softs are not
    ///    live, matching what `ensure_descent_enc` will actually encode over.
    /// 3. It does NOT widen where the projected encoding is the wide adder
    ///    rather than the cheap GTE, because there the extra alternation is
    ///    pure duty-cycle tax with no descent to show for it.
    #[test]
    fn descent_kick_gap_bar_is_scale_relative_and_never_narrows() {
        let mk = |weights: Vec<Weight>| {
            let mut soft_store = ClauseStore::new();
            for i in 1..=weights.len() as i32 {
                soft_store.push_from_iter([i].iter().map(|&l| Literal::from(l)));
            }
            OllEngine::new(
                weights.len() as u32 + 1,
                ClauseStore::new(),
                soft_store,
                weights,
            )
        };

        // Mixed weights {7, 5, 5}: min live weight 5, tiny objective, so the
        // descent projection is a cheap GTE and the bar scales to 5 * 128.
        // No weight dominates the rest (7 < 5 + 5), so #maxsat-bmo-promote
        // leaves the raw soft indices this white-box fixture relies on alone.
        let mut engine = mk(vec![7, 5, 5]);
        let units = engine.tuning.lsu_min_gap_units;
        assert_eq!(engine.descent_kick_gap_cap(), 5 * units);
        assert!(engine.descent_kick_gap_cap() >= DESCENT_KICK_GAP);

        // Hardened softs are satisfied in every remaining model, so they leave
        // the residual: the granularity becomes the weight-7 soft's.
        engine.hardened_sels.insert(engine.soft_selectors[1]);
        engine.hardened_sels.insert(engine.soft_selectors[2]);
        assert_eq!(engine.descent_kick_gap_cap(), 7 * units);

        // Everything hardened => no live granularity to speak of => the floor.
        engine.hardened_sels.insert(engine.soft_selectors[0]);
        assert_eq!(engine.descent_kick_gap_cap(), DESCENT_KICK_GAP);

        // Weights whose live mass blows the GTE output budget project onto the
        // propagation-dead wide adder. Widening there would buy alternation and
        // no descent, so the bar stays absolute — note the scaled bar would
        // have been 300_000 * 128, i.e. this is not a coincidence of clamping.
        let wide = mk(vec![500_000, 300_000, 300_000]);
        assert!(wide.soft_weights.iter().copied().sum::<Weight>() > GTE_CHEAP_OUTS);
        assert_eq!(wide.descent_kick_gap_cap(), DESCENT_KICK_GAP);

        // The A/B escape restores the pre-2026-08-02 absolute bar. It reads the
        // process environment through a OnceLock, so this asserts the default
        // (unset => scale-relative) rather than flipping it mid-process.
        assert!(!kick_gap_abs_enabled(), "escape hatch must default OFF");
    }

    /// #cold-core-descent: the tuned constants, pinned to LITERALS.
    ///
    /// Stating an expectation in terms of the constant it is meant to pin
    /// (`assert_eq!(bar, COLD_CORE_MIN_DROUGHT.as_millis())`) is a tautology
    /// that survives any retuning, so three of the four constants were
    /// effectively unpinned. Every number below is written out, so changing a
    /// tuned value is a deliberate act that must edit this test too.
    #[test]
    fn cold_core_tuned_constants_are_pinned() {
        assert_eq!(COLD_CORE_WINDOW, 16, "trailing rate-baseline window");
        assert_eq!(COLD_CORE_MIN_SAMPLE, 8, "minimum search-derived intervals");
        assert_eq!(
            COLD_CORE_DROUGHT_MULT, 12,
            "multiple of the own-rate median"
        );
        assert_eq!(
            COLD_CORE_MIN_DROUGHT,
            Duration::from_secs(30),
            "absolute floor under the relative bar (one organic descent slice)",
        );
        assert_eq!(
            COLD_CORE_MIN_ELAPSED,
            Duration::from_secs(20),
            "no rate entry inside the opening of a run",
        );
        // The window must leave room for the minimum sample, or the gate can
        // never open.
        const {
            assert!(COLD_CORE_WINDOW >= COLD_CORE_MIN_SAMPLE);
        }
    }

    /// Builds synthetic history without relying on platform-specific `Instant`
    /// subtraction panics.
    fn checked_test_instant_sub(
        instant: Instant,
        duration: Duration,
    ) -> Result<Instant, &'static str> {
        instant
            .checked_sub(duration)
            .ok_or("test fixture exceeds the platform Instant range")
    }

    /// #cold-core-descent. The rate gate's whole job is to be RELATIVE: the
    /// same 30s drought must read as a collapse on an instance that was mining
    /// cores in milliseconds and as ordinary progress on one that pays seconds
    /// per core. The second half is the safety half — rna-alignment and
    /// protein_ins win by walking cores slowly, and a premature entry there
    /// would lose instances AY solves today — so it is asserted as tightly as
    /// the firing half.
    ///
    /// It also asserts that the relative term BINDS. Under the shipped first-N
    /// baseline it did not: measured over every core of 117 runs it bound on 1
    /// of 63 traces, and there by 2.5%, so `cold_core_bar_ms` was in practice
    /// the flat 30s floor while its doc claimed adaptivity.
    ///
    /// Also pins the brakes that keep the gate off the opening of a run: a
    /// minimum interval sample, a minimum elapsed time, an incumbent to
    /// improve, and the `lsu_min_cores == u64::MAX` "descents never engage"
    /// tuning sentinel.
    #[test]
    fn cold_core_gate_measures_the_drought_against_the_instances_own_rate(
    ) -> Result<(), &'static str> {
        // An engine with an incumbent and a synthetic search history: `n`
        // intervals of `gap_ms`, then a drought of exactly `drought` running
        // right now.
        let mk = |gap_ms: u64, n: usize, drought: Duration| {
            let mut soft_store = ClauseStore::new();
            for i in 1..=3i32 {
                soft_store.push_from_iter([i].iter().map(|&l| Literal::from(l)));
            }
            // {7,5,5}: no weight dominates the rest, so #maxsat-bmo-promote
            // leaves this white-box fixture alone.
            let mut engine = OllEngine::new(4, ClauseStore::new(), soft_store, vec![7, 5, 5]);
            engine.best_model = Some(vec![false; 4]);
            let last = checked_test_instant_sub(Instant::now(), drought)?;
            let base = checked_test_instant_sub(last, Duration::from_millis(gap_ms * n as u64))?;
            for i in 0..=n {
                engine.note_search_core(base + Duration::from_millis(gap_ms * i as u64));
            }
            Ok(engine)
        };
        let started = |elapsed: Duration| checked_test_instant_sub(Instant::now(), elapsed);
        let run = Duration::from_mins(5);

        // Cheap cores (200ms trailing median): 12 * 200ms is a lull, not a
        // collapse, so the absolute floor is the binding bar. 30_000 written
        // out, not `COLD_CORE_MIN_DROUGHT.as_millis()`.
        let fast = mk(200, 16, Duration::from_secs(5))?;
        assert_eq!(fast.core_gap_median_ms, 200);
        assert_eq!(fast.cold_core_bar_ms(), 30_000);
        assert!(
            !fast.core_discovery_cold(started(run)?),
            "a 5s lull on a 200ms-median instance is not a collapse",
        );
        assert!(
            mk(200, 16, Duration::from_secs(45))?.core_discovery_cold(started(run)?),
            "225x the instance's own interval must read as cold",
        );

        // Expensive cores (5s trailing median, the rna-alignment/protein_ins
        // shape): the RELATIVE term takes over and the floor goes inert.
        let slow = mk(5_000, 16, Duration::from_secs(30))?;
        assert_eq!(slow.core_gap_median_ms, 5_000);
        assert_eq!(
            slow.cold_core_bar_ms(),
            60_000,
            "the bar must scale with the instance's own median interval",
        );
        assert!(
            slow.cold_core_bar_ms() > 30_000,
            "the relative term must actually BIND on a slow-walk instance — a \
             bar that is the 30s floor everywhere is a constant wearing an \
             adaptive comment",
        );
        assert!(
            !slow.core_discovery_cold(started(run)?),
            "30s without a core is ordinary on a 5s-per-core instance: firing \
             here is the premature entry that costs the slow-walk families",
        );
        assert!(
            mk(5_000, 16, Duration::from_secs(90))?.core_discovery_cold(started(run)?),
            "18x its own interval is a collapse even on a slow instance",
        );

        // Brakes, all with written-out numbers.
        assert!(
            !mk(200, 7, Duration::from_mins(5))?.core_discovery_cold(started(run)?),
            "must not fire on 7 observed intervals (the minimum sample is 8)",
        );
        assert!(
            mk(200, 8, Duration::from_mins(5))?.core_discovery_cold(started(run)?),
            "8 intervals is the minimum sample, so the gate is live there",
        );
        assert!(
            !mk(200, 16, Duration::from_mins(5))?
                .core_discovery_cold(started(Duration::from_secs(10))?),
            "must not enter 10s into a run (the opening floor is 20s)",
        );
        let mut no_incumbent = mk(200, 16, Duration::from_mins(5))?;
        no_incumbent.best_model = None;
        assert!(
            !no_incumbent.core_discovery_cold(started(run)?),
            "no incumbent => nothing for the descent to improve",
        );
        let mut never = mk(200, 16, Duration::from_mins(5))?;
        never.tuning.lsu_min_cores = u64::MAX;
        assert!(
            !never.core_discovery_cold(started(run)?),
            "u64::MAX is the tuning sentinel for 'descents never engage'",
        );

        // Default-ON escape hatch, read through a OnceLock (assert the
        // default rather than flipping the process environment mid-test).
        assert!(cold_core_descent_enabled(), "lever must default ON");
        Ok(())
    }

    /// #cold-core-descent: the rate baseline must TRACK THE RECENT WALK, not
    /// the opening burst.
    ///
    /// The first cut kept only the FIRST 64 intervals, on the argument that a
    /// baseline over all intervals drifts upward as discovery decelerates and
    /// so cancels itself. Measured, that cure was worse: on this corpus the
    /// opening cores fall out of propagation-level conflicts in milliseconds
    /// almost everywhere, so the baseline was ~0 and the relative term never
    /// bound — the gate was the flat 30s floor.
    ///
    /// A TRAILING window cannot cancel itself, because a drought contributes no
    /// interval until a core actually arrives: the moment discovery stops, the
    /// baseline freezes and the drought grows past it. Both halves are asserted
    /// here.
    #[test]
    fn cold_core_rate_baseline_tracks_the_recent_walk_not_the_opening_burst(
    ) -> Result<(), &'static str> {
        let mut soft_store = ClauseStore::new();
        soft_store.push_from_iter([1i32].iter().map(|&l| Literal::from(l)));
        let mut engine = OllEngine::new(2, ClauseStore::new(), soft_store, vec![1]);
        engine.best_model = Some(vec![false; 2]);
        let mut at = checked_test_instant_sub(Instant::now(), Duration::from_hours(1))?;

        // A fast opening fills the window: 16 intervals of 500ms.
        for _ in 0..=16 {
            engine.note_search_core(at);
            at += Duration::from_millis(500);
        }
        assert_eq!(engine.core_gaps_ms.len(), 16);
        assert_eq!(engine.core_gap_median_ms, 500);
        assert_eq!(
            engine.cold_core_bar_ms(),
            30_000,
            "the floor binds while the walk is fast",
        );

        // Then the walk decelerates to 40s per core. The baseline MUST follow
        // it: if it stayed at the opening burst the bar would still be 30s, and
        // a 31s gap on a 40s-per-core walk would read as a collapse.
        for _ in 0..16 {
            at += Duration::from_secs(40);
            engine.note_search_core(at);
        }
        assert_eq!(
            engine.core_gaps_ms.len(),
            16,
            "the window stays capped at COLD_CORE_WINDOW",
        );
        assert_eq!(
            engine.core_gap_median_ms, 40_000,
            "the baseline must track the RECENT walk, not the opening burst",
        );
        assert_eq!(engine.cold_core_bar_ms(), 480_000);
        engine.pause_core_drought_at(at + Duration::from_mins(1));
        assert!(
            !engine.core_discovery_cold(checked_test_instant_sub(
                Instant::now(),
                Duration::from_hours(1),
            )?),
            "60s without a core on a 40s-per-core walk is one slow step, not a \
             collapse — this is the brake that protects rna-alignment",
        );

        // Anti-self-cancellation: once cores STOP, no further interval is
        // recorded, so the baseline freezes and the drought overtakes it.
        engine.core_drought = Duration::from_mins(10);
        engine.core_drought_since = None;
        assert_eq!(
            engine.core_gap_median_ms, 40_000,
            "a drought contributes no interval, so it cannot raise its own bar",
        );
        assert!(
            engine.core_discovery_cold(checked_test_instant_sub(
                Instant::now(),
                Duration::from_hours(1),
            )?),
            "10 minutes with no core against a 40s walk is a collapse",
        );
        Ok(())
    }

    /// #cold-core-descent D1: the drought clock must not run while the engine
    /// is inside a descent slice.
    ///
    /// No core can arrive in `descend` — it walks the ub side and never calls
    /// `process_core` — so charging its wall time as "core discovery has gone
    /// cold" lets a descent slice MANUFACTURE the drought that justifies the
    /// next, longer entry. The 300s span below is exactly that ratchet: with it
    /// charged the drought is 329s and the arm fires; with the clock stopped it
    /// is the 29s of OLL time that genuinely failed to produce a core, and the
    /// arm stays shut.
    #[test]
    fn cold_core_drought_clock_stops_across_a_descent_slice() -> Result<(), &'static str> {
        let mut soft_store = ClauseStore::new();
        soft_store.push_from_iter([1i32].iter().map(|&l| Literal::from(l)));
        let mut engine = OllEngine::new(2, ClauseStore::new(), soft_store, vec![1]);
        engine.best_model = Some(vec![false; 2]);
        let mut at = checked_test_instant_sub(Instant::now(), Duration::from_secs(1_000))?;
        // 16 intervals of 200ms => bar is the 30s floor. `at` ends ON the last
        // arrival, so the offsets below are measured from it exactly.
        engine.note_search_core(at);
        for _ in 0..16 {
            at += Duration::from_millis(200);
            engine.note_search_core(at);
        }
        assert_eq!(engine.cold_core_bar_ms(), 30_000);

        // 25s of OLL search with no core, then a 300s descent slice, then 4s
        // more of OLL: 29s of core-searching time, under the 30s bar.
        engine.pause_core_drought_at(at + Duration::from_secs(25));
        engine.resume_core_drought_at(at + Duration::from_secs(325));
        engine.pause_core_drought_at(at + Duration::from_secs(329));
        assert_eq!(
            engine.core_drought(),
            Duration::from_secs(29),
            "the 300s descent slice must contribute nothing to the drought",
        );
        assert!(
            !engine.core_discovery_cold(checked_test_instant_sub(
                Instant::now(),
                Duration::from_secs(1_000),
            )?),
            "a descent slice must not manufacture the drought that justifies \
             the next entry",
        );

        // The clock is stopped, not dead: 2s more of OLL crosses the bar.
        engine.resume_core_drought_at(at + Duration::from_secs(329));
        engine.pause_core_drought_at(at + Duration::from_secs(331));
        assert_eq!(engine.core_drought(), Duration::from_secs(31));
        assert!(
            engine.core_discovery_cold(checked_test_instant_sub(
                Instant::now(),
                Duration::from_secs(1_000),
            )?),
            "31s of genuine core-searching time is past the 30s bar",
        );
        Ok(())
    }

    include!("oll/lp_boost_cold_core_tests.rs");

    /// #cold-core-descent D4: a stratification level change must reset the
    /// drought.
    ///
    /// A level change legitimately pauses core discovery — the previous
    /// stratum ran out of assumable selectors and the next one has not been
    /// searched yet — and the rate gate cannot tell that apart from discovery
    /// collapsing. Without the reset the arm can take the entry before the
    /// fresh stratum has had a single chance to produce a core.
    #[test]
    fn cold_core_level_activation_resets_the_drought() -> Result<(), &'static str> {
        let mut soft_store = ClauseStore::new();
        soft_store.push_from_iter([1i32].iter().map(|&l| Literal::from(l)));
        let mut engine = OllEngine::new(2, ClauseStore::new(), soft_store, vec![1]);
        engine.best_model = Some(vec![false; 2]);
        let mut at = checked_test_instant_sub(Instant::now(), Duration::from_mins(10))?;
        for _ in 0..=16 {
            engine.note_search_core(at);
            at += Duration::from_millis(200);
        }
        engine.core_drought = Duration::from_mins(5);
        engine.core_drought_since = None;
        assert!(
            engine.core_discovery_cold(checked_test_instant_sub(
                Instant::now(),
                Duration::from_mins(10),
            )?),
            "precondition: the gate is open before the level change",
        );

        engine.activate_stratum(1);
        assert!(
            engine.core_drought() < Duration::from_secs(1),
            "a stratum activation must clear the accumulated drought",
        );
        assert!(
            engine.core_drought_since.is_some(),
            "and leave the clock running for the new stratum",
        );
        assert!(
            !engine.core_discovery_cold(checked_test_instant_sub(
                Instant::now(),
                Duration::from_mins(10),
            )?),
            "the arm must not commit before the fresh stratum has had a chance",
        );
        Ok(())
    }

    /// #cold-core-descent D7: the descent entry gate's WIRING, not just the
    /// predicates it consumes.
    ///
    /// Before `classify_descent_arm` existed, all three of the one-line
    /// mutations that undo this lever left the suite green: dropping the cold
    /// arm from the entry disjunction, forcing `cold_entry = false`, and
    /// reverting `kick_entry = descent_kick && !cold_entry` to
    /// `kick_entry = descent_kick`. Each is now a test failure.
    #[test]
    fn descent_arm_classification_pins_the_gate_wiring() {
        use DescentArm::{Cold, Count, Kick, None as NoArm};
        // (incumbent, cold_enabled, cold_ready, kick_armed, count_ready)
        let cases: &[(bool, bool, bool, bool, bool, DescentArm)] = &[
            // The rate arm opens the gate on its own — this is the lever.
            (true, true, true, false, false, Cold),
            // PRECEDENCE: with a kick armed in the same iteration the cold arm
            // still wins, so the entry gets the longer (still reversible)
            // slice instead of a 10s kick slice.
            (true, true, true, true, false, Cold),
            (true, true, true, true, true, Cold),
            // Kill switch off => bit-identical to the pre-lever gate.
            (true, false, true, false, false, NoArm),
            (true, false, true, true, false, Kick),
            (true, false, true, false, true, Count),
            // The other arms are untouched.
            (true, true, false, true, false, Kick),
            (true, true, false, true, true, Kick),
            (true, true, false, false, true, Count),
            (true, true, false, false, false, NoArm),
            // No incumbent: nothing for the descent to improve, every arm shut.
            (false, true, true, true, true, NoArm),
        ];
        for &(incumbent, enabled, cold, kick, count, want) in cases {
            assert_eq!(
                classify_descent_arm(incumbent, enabled, cold, kick, count),
                want,
                "incumbent={incumbent} cold_enabled={enabled} cold_ready={cold} \
                 kick={kick} count={count}",
            );
        }
    }

    /// #cold-core-descent D5: the cold arm gets a REVERSIBLE slice.
    ///
    /// It carries the weakest evidence of the three arms (no core count, no
    /// lb-stall test, no gap cap beyond `gap_ok`), and the one-way commit
    /// freezes lb for the rest of the budget because `descend` only ever moves
    /// ub. On rna-alignment and protein_ins — the families a rate misfire is
    /// most likely on — the slow core walk is the PRODUCTIVE path, so an
    /// unbounded commit there forfeits instances AY solves today.
    #[test]
    fn cold_descent_entry_takes_a_reversible_slice() {
        let kick = Duration::from_secs(10);
        let organic = Duration::from_mins(2);

        // The cold arm is bounded REGARDLESS of #descent-organic-slice, and at
        // the organic length: its evidence earns a longer slice than a kick,
        // not an irrevocable one.
        for organic_slice in [false, true] {
            assert_eq!(
                descent_slice_len(DescentArm::Cold, organic_slice, kick, organic),
                Some(organic),
                "cold entry must be reversible with organic_slice={organic_slice}",
            );
        }
        // Kicks keep their measured slice.
        assert_eq!(
            descent_slice_len(DescentArm::Kick, false, kick, organic),
            Some(kick),
        );
        // The historical count arm is untouched: one-way unless
        // #descent-organic-slice is on.
        assert_eq!(
            descent_slice_len(DescentArm::Count, false, kick, organic),
            None,
            "the count arm's one-way commit is the measured status quo",
        );
        assert_eq!(
            descent_slice_len(DescentArm::Count, true, kick, organic),
            Some(organic),
        );
    }

    /// #cold-core-descent D6: a SIZE decline must not permanently forfeit the
    /// descent.
    ///
    /// `select_descent_enc`'s budgets are state-dependent — the residual soft
    /// set shrinks as softs harden, and the cap falls as the incumbent improves
    /// — so an encoding too large at t=25s can fit at t=200s. The rate arm
    /// fires EARLIER than the count arm by construction, i.e. exactly when the
    /// encoding is at its largest, so poisoning the sticky `descent_unavailable`
    /// flag on a size decline is how an early entry loses the descent for the
    /// whole run.
    #[test]
    fn descent_size_decline_is_retried_when_the_residual_shrinks() {
        let mut soft_store = ClauseStore::new();
        for i in 1..=3i32 {
            soft_store.push_from_iter([i].iter().map(|&l| Literal::from(l)));
        }
        let mut engine = OllEngine::new(4, ClauseStore::new(), soft_store, vec![7, 5, 5]);
        engine.ub = 100;
        assert!(engine.descent_reachable(), "no decline recorded yet");

        // A size decline at the current (hardened, ub) signature.
        engine.descent_size_declined = Some((engine.hardened_sels.len(), engine.ub));
        assert!(
            !engine.descent_reachable(),
            "nothing has changed, so re-running the build would decline again",
        );

        // A better incumbent shrinks the cap: re-try.
        engine.ub = 99;
        assert!(
            engine.descent_reachable(),
            "a lower ub shrinks the encoding — the decline must be re-tried",
        );

        // So does hardening a soft.
        engine.ub = 100;
        engine.hardened_sels.insert(engine.soft_selectors[0]);
        assert!(
            engine.descent_reachable(),
            "a hardened soft shrinks the residual — re-try",
        );

        // The PERMANENT flag still short-circuits everything.
        engine.descent_unavailable = true;
        assert!(
            !engine.descent_reachable(),
            "descent_unavailable stays sticky for the structural declines",
        );
    }
}

#[cfg(test)]
mod abstraction_tests {
    use super::*;

    /// Abstraction sets must form on group-structured instances and leave
    /// the optimum exact: 8 uniform softs under an at-most-2 hard
    /// constraint (all 3-subsets blocked) has optimum cost 6, and the
    /// co-occurring cores over those selectors should coalesce into a
    /// shared counting set.
    /// #tot-eqs: the reverse-direction pass must actually FIRE (otherwise the
    /// cross-checks above pass vacuously) and must not move the optimum. The
    /// instance is an at-most-2-of-8 clique with all 8 softs wanted, so OLL
    /// relaxes a core and then hardens bounds on it — hitting both
    /// force_true call sites (relax_core and the unit-core branch).
    #[test]
    fn tot_eqs_emit_reverse_clauses_and_stay_exact() {
        let n: i32 = 8;
        // #tot-eqs is WEIGHTED-ONLY (uniform weights leave the budget at 0 so the
        // unweighted track stays bit-identical), so this instance must carry >= 2
        // distinct weights for the lever to be active at all. Making one soft
        // weight 2 keeps the optimum at 6: at most 2 of the 8 softs can hold, and
        // satisfying the weight-2 soft plus one weight-1 soft leaves 6 violated.
        let mut weights = vec![1u64; n as usize];
        weights[(n - 1) as usize] = 2;

        let run = |tot_eqs: Option<bool>| {
            let mut hs = ClauseStore::new();
            for a in 1..=n {
                for b in (a + 1)..=n {
                    for c in (b + 1)..=n {
                        hs.push_from_iter([-a, -b, -c].iter().map(|&l| Literal::from(l)));
                    }
                }
            }
            let mut ss = ClauseStore::new();
            for i in 1..=n {
                ss.push_from_iter([i].iter().map(|&l| Literal::from(l)));
            }
            let mut engine = OllEngine::new(n as u32 + 1, hs, ss, weights.clone());
            engine.set_tuning(OllTuning {
                lsu_min_cores: u64::MAX,
                lsu_min_gap_units: Weight::MAX,
                lsu_stall_ms_per_core: 0,
                force_adder: false,
                abstraction_min_cores: u64::MAX,
                force_cluster: false,
                force_dpw: false,
                lp_boost: LpBoostMode::Off,
                tot_eqs,
                core_clause: Some(false),
            });
            let cost = match engine.solve(&|| false, &mut |_| {}) {
                OllOutcome::Optimal { cost, .. } => cost,
                other => panic!("expected optimal, got {other:?}"),
            };
            (
                cost,
                engine.stats().tot_eq_clauses,
                engine.stats().tot_eq_forced,
            )
        };

        // At most 2 of the 8 softs can hold => optimum violates 6.
        let (cost_on, eq_clauses, eq_forced) = run(Some(true));
        let (cost_off, off_clauses, off_forced) = run(Some(false));
        assert_eq!(cost_on, 6, "reverse clauses must not move the optimum");
        assert_eq!(cost_off, 6);
        assert!(
            eq_forced > 0,
            "force_true must fire on a core-relaxing instance",
        );
        assert!(
            eq_clauses > 0,
            "the pass must emit reverse-direction clauses (got 0: gate or budget \
             is silently swallowing them, making the cross-checks vacuous)",
        );
        assert_eq!(
            (off_clauses, off_forced),
            (0, 0),
            "gated off must be bit-identical: no reverse clauses, no forced outputs",
        );
    }

    #[test]
    fn abstraction_sets_form_and_stay_exact() {
        let n: i32 = 8;
        let mut hard_store = ClauseStore::new();
        for a in 1..=n {
            for b in (a + 1)..=n {
                for c in (b + 1)..=n {
                    hard_store.push_from_iter([-a, -b, -c].iter().map(|&l| Literal::from(l)));
                }
            }
        }
        let mut soft_store = ClauseStore::new();
        for i in 1..=n {
            soft_store.push_from_iter([i].iter().map(|&l| Literal::from(l)));
        }
        let weights = vec![1u64; n as usize];
        let mut engine = OllEngine::new(n as u32 + 1, hard_store, soft_store, weights);
        engine.set_tuning(OllTuning {
            lsu_min_cores: u64::MAX, // keep descents out of the way
            lsu_min_gap_units: Weight::MAX,
            lsu_stall_ms_per_core: 0,
            force_adder: false,
            abstraction_min_cores: 0,
            force_cluster: false,
            force_dpw: false,
            lp_boost: LpBoostMode::Auto,
            // #tot-eqs pinned ON so the reverse-direction clauses are exercised
            // wherever the fixture has >= 2 distinct soft weights. Production also
            // defaults ON (env gate AY_AB_MAXSAT_TOT_EQS != "0"); `tot_eq_budget`
            // is 0 on uniform weights, so the pin is inert on unit-weight fixtures.
            tot_eqs: Some(true),
            core_clause: Some(true),
        });
        // #core-mine SUPERSEDES abstraction on this fixture, so clear the mined
        // batch to keep this test measuring what it is named for.
        //
        // The fixture is 8 unit softs with every hard clause ternary over their
        // negations — i.e. 100% mineable, the exact shape `#core-mine` targets.
        // With mining live, those cores are paid at install and the in-loop
        // `form_abstraction_sets()` never sees the core traffic it forms from,
        // so `abstraction_sets` stays 0. The COST assertion below still passes
        // either way (mining reaches the same optimum more cheaply), so this is
        // a capability-coverage question, not a soundness one — but the
        // abstraction path must stay tested, and silently letting this assert
        // lapse would retire it.
        //
        // Worth noting for the campaign: abstraction (`cgss_abst_cg` scores 415
        // using it) and `#core-mine` compete for the same structure. Production
        // has abstraction OFF by default (`abstraction_min_cores = u64::MAX`),
        // so mining is currently the only lane exploiting this shape.
        engine.mined_cores.clear();

        match engine.solve(&|| false, &mut |_| {}) {
            OllOutcome::Optimal { cost, .. } => assert_eq!(cost, 6),
            other => panic!("expected optimal, got {other:?}"),
        }
        assert!(
            engine.stats().abstraction_sets > 0,
            "group-structured instance must form at least one abstraction set",
        );
    }
}

#[cfg(test)]
mod am1_probe_tests {
    use super::*;

    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0 >> 33
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    /// Pure leveled OLL with every other lane out of the way (descents,
    /// abstraction, LP-boost off), so the UP-probe AM1 pass is the only thing
    /// folding at-most-one structure and the run walks to the level-1 terminal.
    fn am1_probe_tuning() -> OllTuning {
        OllTuning {
            lsu_min_cores: u64::MAX,
            lsu_min_gap_units: Weight::MAX,
            lsu_stall_ms_per_core: 30,
            force_adder: false,
            abstraction_min_cores: u64::MAX,
            force_cluster: false,
            force_dpw: false,
            lp_boost: LpBoostMode::Off,
            // #tot-eqs pinned ON so the reverse-direction clauses are exercised
            // wherever the fixture has >= 2 distinct soft weights. Production also
            // defaults ON (env gate AY_AB_MAXSAT_TOT_EQS != "0"); `tot_eq_budget`
            // is 0 on uniform weights, so the pin is inert on unit-weight fixtures.
            tot_eqs: Some(true),
            core_clause: Some(true),
        }
    }

    fn brute_force(
        num_vars: u32,
        hard: &[Vec<i32>],
        soft: &[Vec<i32>],
        weights: &[u64],
    ) -> Option<u64> {
        let clause_sat = |clause: &[i32], bits: u64| {
            clause.iter().any(|&lit| {
                let var = lit.unsigned_abs();
                let val = (bits >> (var - 1)) & 1 == 1;
                (lit > 0) == val
            })
        };
        let mut expected: Option<u64> = None;
        for bits in 0..(1u64 << num_vars) {
            if hard.iter().any(|c| !clause_sat(c, bits)) {
                continue;
            }
            let cost: u64 = soft
                .iter()
                .zip(weights)
                .filter(|(c, _)| !clause_sat(c, bits))
                .map(|(_, w)| *w)
                .sum();
            expected = Some(expected.map_or(cost, |b: u64| b.min(cost)));
        }
        expected
    }

    fn run(
        num_vars: u32,
        hard: &[Vec<i32>],
        soft: &[Vec<i32>],
        weights: Vec<u64>,
    ) -> (OllOutcome, MaxSatStats) {
        let mut hard_store = ClauseStore::new();
        for c in hard {
            hard_store.push_from_iter(c.iter().map(|&l| Literal::from(l)));
        }
        let mut soft_store = ClauseStore::new();
        for c in soft {
            soft_store.push_from_iter(c.iter().map(|&l| Literal::from(l)));
        }
        let mut engine = OllEngine::new(num_vars + 1, hard_store, soft_store, weights);
        engine.set_tuning(am1_probe_tuning());
        let outcome = engine.solve(&|| false, &mut |_| {});
        (outcome, engine.stats().clone())
    }

    /// #core-mine SOUNDNESS NET — the invariant is ALL-MEMBERS-ACTIVE, not
    /// disjointness, and this test is the executable form of that claim.
    ///
    /// The hazard: a not-all-true clause has NO valid proper subset.
    /// `(!s1|!s2|!s3)` does not entail `(!s1|!s2)`. So if a mined core is
    /// SHRUNK when a member is exhausted — the idiom `relax_am1_clique` uses
    /// legitimately, because every subset of an at-most-one set is still
    /// at-most-one — `lb` is charged for weight the absent member no longer
    /// carries, and `s OPTIMUM FOUND` fires above the true optimum.
    ///
    /// Minimal witness, from the adversarial review of `#core-mine`:
    ///   hard (!x1 | !x2);  softs (x1)=7 (x2)=2;  OPTIMUM = 2
    /// `adapt_am1` spends x2 to zero first. Shrinking the mined core to {x1}
    /// then pays lb = 2 + 5 = 7 — the #stale-core wrong answer recorded in this
    /// file (privilege-escalation-task-54: reported 20, optimum 19).
    #[test]
    fn core_mine_never_pays_above_the_optimum() {
        // (a) the exact witness from the review
        let (outcome, _) = run(2, &[vec![-1, -2]], &[vec![1], vec![2]], vec![7, 2]);
        match outcome {
            OllOutcome::Optimal { cost, .. } => assert_eq!(
                cost, 2,
                "mined core was shrunk: lb charged for an exhausted member"
            ),
            other => panic!("expected Optimal(2), got {other:?}"),
        }

        // (b) randomized net over small mineable instances. Every hard clause
        // is built ENTIRELY from negated unit-soft literals, so #core-mine
        // fires on all of them; overlapping cores, mixed weights and multiple
        // strata are exactly the conditions under which an over-payment would
        // appear. Brute force is ground truth.
        let mut seed: u64 = 0x9E3779B97F4A7C15;
        let mut next = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for case in 0..200u32 {
            let n = 3 + (next() % 4) as usize; // 3..6 vars, all unit softs
            let weights: Vec<u64> = (0..n).map(|_| 1 + next() % 9).collect();
            let softs: Vec<Vec<i32>> = (1..=n as i32).map(|v| vec![v]).collect();
            let nclauses = 1 + (next() % 5) as usize;
            let mut hard: Vec<Vec<i32>> = Vec::new();
            for _ in 0..nclauses {
                let k = 2 + (next() % 2) as usize; // arity 2..3
                let mut c: Vec<i32> = Vec::new();
                while c.len() < k.min(n) {
                    let v = 1 + (next() % n as u64) as i32;
                    if !c.contains(&-v) {
                        c.push(-v);
                    }
                }
                hard.push(c);
            }
            // brute-force optimum over all assignments
            let mut best = u64::MAX;
            for mask in 0u32..(1 << n) {
                let val = |v: i32| (mask >> (v.unsigned_abs() as usize - 1)) & 1 == 1;
                if hard
                    .iter()
                    .any(|c| c.iter().all(|&l| if l > 0 { !val(l) } else { val(l) }))
                {
                    continue; // hard clause falsified
                }
                let cost: u64 = (0..n)
                    .filter(|&i| (mask >> i) & 1 == 0)
                    .map(|i| weights[i])
                    .sum();
                best = best.min(cost);
            }
            if best == u64::MAX {
                continue; // hards unsatisfiable; not the property under test
            }
            let (outcome, _) = run(n as u32, &hard, &softs, weights.clone());
            if let OllOutcome::Optimal { cost, .. } = outcome {
                assert_eq!(
                    cost, best,
                    "case {case}: hard={hard:?} weights={weights:?} — AY reported \
                     {cost}, brute force says {best}. A cost ABOVE the optimum is \
                     an over-paid lower bound."
                );
            }
        }
    }

    /// 300-seed brute-force net for the UP-probe AM1 pass (#maxsat-am1-probe).
    ///
    /// Each seed builds a chain-conflict clique of `k` unit-soft selectors that
    /// conflict ONLY through unit-propagation chains — never a direct binary
    /// hard clause: for member i, `s_i => m_i` (clause ¬s_i ∨ m_i) plus a
    /// pairwise mutex among the intermediates (¬m_i ∨ ¬m_j). Then s_i ⇒ m_i ⇒
    /// ¬m_j ⇒ ¬s_j, so at most one selector is satisfied — but there is no
    /// (¬s_i ∨ ¬s_j) clause, so install-time adapt_am1 (direct binary edges
    /// only) sees nothing. A high-weight top soft yields a level-changing SAT,
    /// after which the clique activates at a middle level and the pass probes
    /// it. Low-weight dust rounds out the strata.
    ///
    /// The net asserts: every seed hits the exact brute-force optimum; the pass
    /// actually FIRES (folds >= 1 semantic clique); and adapt_am1 folds NOTHING
    /// (aggregate install am1_groups == 0), proving the conflicts are reachable
    /// only through propagation, not direct binaries.
    #[test]
    fn random_cross_check_am1_probe_chain_conflicts() {
        let mut total_probe_groups = 0u64;
        let mut total_probe_passes = 0u64;
        let mut total_install_am1 = 0u64;
        let mut firing_seeds = 0u64;
        for seed in 0..300u64 {
            let mut rng = Lcg(seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(0xA11));
            let k = 2 + rng.below(2) as usize; // 2 or 3 clique members
            let n_dust = 1 + rng.below(3) as usize; // 1..3 dust softs
            let w_clique = 300 + 100 * rng.below(4); // equal within a seed
            let w_high = 10_000; // clearly the top stratum

            // var layout (1-indexed):
            //   selectors  1 ..= k
            //   intermediates  k+1 ..= 2k
            //   high  2k+1
            //   dust  2k+2 ..= 2k+1+n_dust
            let sel = |i: usize| i as i32;
            let mid = |i: usize| (k + i) as i32;
            let high = (2 * k + 1) as i32;
            let dust = |t: usize| (2 * k + 1 + t) as i32;
            let num_vars = (2 * k + 1 + n_dust) as u32;

            let mut hard: Vec<Vec<i32>> = Vec::new();
            for i in 1..=k {
                hard.push(vec![-sel(i), mid(i)]); // s_i => m_i
            }
            for i in 1..k {
                for j in (i + 1)..=k {
                    hard.push(vec![-mid(i), -mid(j)]); // intermediates mutex
                }
            }

            let mut soft: Vec<Vec<i32>> = Vec::new();
            let mut weights: Vec<u64> = Vec::new();
            soft.push(vec![high]);
            weights.push(w_high);
            for i in 1..=k {
                soft.push(vec![sel(i)]);
                weights.push(w_clique);
            }
            for t in 1..=n_dust {
                soft.push(vec![dust(t)]);
                weights.push(1 + rng.below(10));
            }

            let expected = brute_force(num_vars, &hard, &soft, &weights);
            let (outcome, stats) = run(num_vars, &hard, &soft, weights.clone());
            total_probe_groups += stats.am1_probe_groups;
            total_probe_passes += stats.am1_probe_passes;
            total_install_am1 += stats.am1_groups;
            if stats.am1_probe_groups > 0 {
                firing_seeds += 1;
            }
            match (outcome, expected) {
                (OllOutcome::Optimal { cost, .. }, Some(exp)) => {
                    assert_eq!(
                        cost, exp,
                        "seed {seed}: am1-probe cost {cost} != brute force {exp}\nhard: {hard:?}\nsoft: {soft:?}\nweights: {weights:?}",
                    );
                }
                (OllOutcome::Unsatisfiable, None) => {}
                (got, exp) => panic!(
                    "seed {seed}: {got:?} vs brute force {exp:?}\nhard: {hard:?}\nsoft: {soft:?}",
                ),
            }
        }
        assert!(
            total_probe_groups > 0 && total_probe_passes > 0,
            "the AM1 probe pass must fire and fold cliques (passes={total_probe_passes} groups={total_probe_groups})",
        );
        assert!(
            firing_seeds > 200,
            "the chain-conflict gadget must fire on the vast majority of seeds (got {firing_seeds}/300)",
        );
        assert_eq!(
            total_install_am1, 0,
            "install-time adapt_am1 must fold NOTHING: the conflicts are chain-only, so all AM1 folding is the probe pass's ({total_install_am1} direct groups leaked)",
        );
    }

    /// Deterministic: a 3-selector clique whose only conflicts are UP chains
    /// (no direct binaries) folds to the exact optimum and the fold is credited
    /// to the probe pass, not adapt_am1.
    #[test]
    fn chain_clique_folds_via_up_probe() {
        // selectors 1,2,3; intermediates 4,5,6; high 7; dust 8.
        let hard = vec![
            vec![-1, 4],
            vec![-2, 5],
            vec![-3, 6],
            vec![-4, -5],
            vec![-4, -6],
            vec![-5, -6],
        ];
        let soft = vec![vec![7], vec![1], vec![2], vec![3], vec![8]];
        let weights = vec![10_000u64, 500, 500, 500, 3];
        let expected = brute_force(8, &hard, &soft, &weights).unwrap();
        assert_eq!(
            expected, 1000,
            "at most one of the three 500-softs is satisfiable"
        );
        let (outcome, stats) = run(8, &hard, &soft, weights);
        match outcome {
            OllOutcome::Optimal { cost, .. } => assert_eq!(cost, 1000),
            other => panic!("expected optimal, got {other:?}"),
        }
        assert!(
            stats.am1_probe_groups >= 1,
            "the UP-probe pass must fold the chain clique (groups={})",
            stats.am1_probe_groups,
        );
        assert_eq!(
            stats.am1_groups, 0,
            "no direct binary edges exist, so adapt_am1 must fold nothing",
        );
    }

    /// Deterministic: a selector that unit-propagates to a conflict when
    /// assumed satisfied is a failed literal — the probe pass must harden it
    /// (pay its weight, add the hard unit) exactly like the unit-core path.
    #[test]
    fn failed_selector_hardened_by_probe() {
        // soft [1] cannot be satisfied: 1 => 2 and 1 => ¬2. high [3] tops the
        // strata (level-changing SAT) and dust [4] sits below [1], so the
        // failed selector [1] activates at a MIDDLE level (> 1) where the
        // probe pass runs — rather than the skipped terminal level 1.
        let hard = vec![vec![-1, 2], vec![-1, -2]];
        let soft = vec![vec![3], vec![1], vec![4]];
        let weights = vec![10_000u64, 100, 5];
        let expected = brute_force(4, &hard, &soft, &weights).unwrap();
        assert_eq!(expected, 100, "soft [1] is always violated");
        let (outcome, stats) = run(4, &hard, &soft, weights);
        match outcome {
            OllOutcome::Optimal { cost, .. } => assert_eq!(cost, 100),
            other => panic!("expected optimal, got {other:?}"),
        }
        assert!(
            stats.am1_probe_failed >= 1,
            "the probe pass must harden the failed selector (failed={})",
            stats.am1_probe_failed,
        );
    }
}
