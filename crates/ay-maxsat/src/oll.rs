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

use crate::solver::MaxSatStats;

/// Diagnostics gate: set `AY_MAXSAT_DEBUG=1` to trace engine decisions on
/// stderr. Zero cost when unset.
fn debug_trace() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("AY_MAXSAT_DEBUG").is_some())
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
/// quantum, spot5): `AY_AB_MAXSAT_BMO=0` disables. Uniform-weight
/// (unweighted-track) instances are structurally unaffected — the boundary
/// rule requires a non-empty strictly-lower mass, which a single distinct
/// weight never has.
fn maxsat_bmo_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var("AY_AB_MAXSAT_BMO").as_deref() != Ok("0"))
}

/// Conflict budget for one BMO joint-satisfiability check
/// (#maxsat-bmo-promote). Exhaustion = no promotion (fail-open, sound).
const BMO_CHECK_CONFLICTS: u64 = 200_000;
/// Wall-clock cap for one BMO check.
const BMO_CHECK_WALL: Duration = Duration::from_secs(8);
/// Skip the BMO throwaway check entirely above this many clauses
/// (hards + candidate softs) — the throwaway build would cost more than the
/// promotion is worth.
const BMO_MAX_CHECK_CLAUSES: usize = 2_000_000;

/// Kill switch for the one-shot MaxSAT preprocessor. DEFAULT ON since the
/// net-positive full-track leg (fired subset +3/-0 at the 1M-hards gate, zero
/// wrong): `AY_AB_MAXSAT_PREPROC=0` disables. Matches the ay-sat `AY_AB_*`
/// convention's kill-switch form.
/// Opt-in gate for the BCE-first one-shot config (#maxsat-bce-preprocess).
/// When AY_AB_MAXSAT_BCE=1 the one-shot fires from this lower hard-clause
/// threshold (so the LP-extracted mid-size families qualify) AND arms BCE.
const BCE_ONESHOT_MIN_HARDS: usize = 100_000;

/// Opt-in switch for BCE-first one-shot preprocessing
/// (#maxsat-bce-preprocess): `AY_AB_MAXSAT_BCE=1`. DEFAULT OFF — net-negative
/// under bench jobs=10 contention, net-positive at the jobs=1 competition
/// protocol (metro x4 etc.). Use for competition submissions.
fn maxsat_bce_preproc_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var("AY_AB_MAXSAT_BCE").as_deref() == Ok("1"))
}

fn maxsat_oneshot_preproc_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var("AY_AB_MAXSAT_PREPROC").as_deref() != Ok("0"))
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
    /// LP-boost lane mode (#lp-boost). Default Auto (on, gated to
    /// non-uniform weights).
    pub(crate) lp_boost: LpBoostMode,
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
            lp_boost: LpBoostMode::Auto,
        }
    }
}

/// One node of a lazily-built totalizer tree.
///
/// `outs[j]` is a literal that is implied true whenever at least `j + 1` of
/// the leaf input literals are true. Only the input→output direction is
/// encoded (sufficient for enforcing upper bounds via assuming `¬outs[j]`).
struct TotNode {
    outs: Vec<Literal>,
    size: usize,
    /// Bound this node's clause set is complete up to (`min(k, size)`).
    built_k: usize,
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

/// OLL engine state over one persistent incremental SAT solver.
pub(crate) struct OllEngine {
    sat: SatSolver,
    /// Next fresh raw variable id (variable ids are used raw; id 0 unused).
    next_var: u32,
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
    /// True when no descent encoding is available (build too large).
    descent_unavailable: bool,
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
        // (The interim #maxsat-domain-bcp-regression-workaround that disabled
        // domain BCP for +5 is now REMOVED: the underlying regression is fixed
        // directly — see #maxsat-domain-bcp-fix (propagate_domain_bcp's fused
        // out-of-domain skip) in propagation_bcp.rs. Domain BCP is re-enabled and
        // recovers the full regression. Escape hatch to force full BCP still
        // exists via AY_AB_NO_DOMAIN_BCP.)
        if std::env::var_os("AY_AB_NO_DOMAIN_BCP").is_some() {
            sat.set_domain_bcp_min_vars(100_000_000);
        }
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
        // #maxsat-bce-preprocess (opt-in, AY_AB_MAXSAT_BCE=1): the BCE-first
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
        // Binary hard clauses feed intrinsic at-most-one detection below.
        let mut binary: Vec<(Literal, Literal)> = Vec::new();
        for clause in hard.iter() {
            if clause.len() == 2 && clause[0].variable() != clause[1].variable() {
                binary.push((clause[0], clause[1]));
            }
            sat.add_clause(clause.to_vec());
        }
        if oneshot_preproc {
            // Run the single BVE+subsumption pass now (hards added, softs not
            // yet). Soundness note: this may report UNSAT (empty hards); the
            // first OLL solve will then return Unsatisfiable. Reconstruction
            // over eliminated hard vars runs automatically on every later solve.
            let clauses_before = sat.active_clause_count();
            let _ = sat.preprocess_once();
            let clauses_after = sat.active_clause_count();
            if std::env::var("AY_MAXSAT_DEBUG").is_ok() {
                eprintln!("c ONESHOT-PREPROC: clauses {clauses_before} -> {clauses_after}");
            }
            // #oneshot-dry-guard: on binary-dense formulas BVE finds nothing
            // (rna-alignment: 1002441 -> 1002441). Require a reduction larger
            // than floor(1% of the input) to commit to one-shot mode (all
            // inprocessing off).
            // A dry pass instead falls back to EXACTLY the size-banded
            // profile the non-oneshot path installs at this scale — no third
            // behavior.
            let oneshot_paid = clauses_after < clauses_before.saturating_sub(clauses_before / 100);
            let mut off = ay_sat::InprocessingFeatureProfile::default();
            if oneshot_paid {
                // One-shot mode proper: the pass simplified the formula; stop
                // ALL further inprocessing (this is what makes it a ONE-shot
                // and dodges the per-solve rehash storm).
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
            } else {
                // Mirror the non-oneshot >500k band (hard.len() >= 1M here),
                // including the >2M occurrence-list extension.
                off.vivify = false;
                off.subsume = false;
                off.probe = false;
                off.transred = false;
                off.sweep = false;
                off.congruence = false;
                if hard.len() > 2_000_000 {
                    off.bve = false;
                    off.bce = false;
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
                }
            }
            sat.set_inprocessing_profile(&off);
            // preprocess_once already set preprocess_enabled=false.
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
        drop(hard);

        // #lp-boost instance gate, judged on the ORIGINAL input weights
        // (before install-time merging can turn duplicate unit softs of a
        // uniform instance into merged non-uniform weights): uniform-weight
        // instances — the unweighted track in particular — must behave
        // bit-identically to the lane-free engine.
        let lp_eligible = {
            let mut distinct: Vec<Weight> =
                soft_weights.iter().copied().filter(|&w| w > 0).collect();
            distinct.sort_unstable();
            distinct.dedup();
            distinct.len() >= 2
        };

        let mut engine = OllEngine {
            sat,
            next_var: num_vars,
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
            descent_guard: None,
            hardened_sels: HashSet::new(),
            abstraction_done: false,
            lb_window: None,
            lb_last_window_gain: None,
            core_history: Vec::new(),
            lp_cores: Vec::new(),
            lp_core_seen: HashSet::new(),
            sel_to_soft: HashMap::new(),
            boost_lb: 0,
            lp_eligible,
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
            // Prefer candidates sharing the most neighbors with the seed:
            // in one-hot/domain encodings (frb: 25 disjoint 13-cliques plus
            // random CSP cross-edges) plain id order lets a cross-edge
            // vertex enter first and fragment the true clique — greedy then
            // finds covers worth lb=254 where the clean partition is worth
            // the optimum 300. Guarded to sparse graphs where the
            // intersection scan is cheap; skipping it only costs bound
            // quality, never correctness.
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

            // Iterated extraction (CGSS/RC2 style): peel the clique level
            // by level so the full unavoidable cost — sum of weights minus
            // the maximum — lands in the lower bound, not just
            // w_min * (k - 1). Each level applies the exact identity
            //   sum_i w[l_i violated] over an AM1 group
            //   = d * (k - 1) + d * [all violated] + residuals
            // with d the level's minimum remaining weight, emitting one
            // disjunction soft per level.
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
                // Max-weight member's residual survives as a unit soft.
                let entry = merged.entry(vec![m]).or_insert(0);
                *entry = entry.saturating_add(w);
            }
            self.stats.am1_groups = self.stats.am1_groups.saturating_add(1);
        }
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
    /// `adapt_am1` (`relax_am1_clique`): a clique of k selectors forces >= k−1
    /// violations, so lb += d·(k−1) at each peel level d, plus one disjunction
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
                self.process_core(&[s]);
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

        // Greedy clique cover over the semantic edges, then exact peel
        // accounting per clique.
        let cliques = Self::greedy_clique_cover(&adj);
        if debug_trace() {
            eprintln!(
                "c am1-probe: probes={} failed={} edge_nodes={} cliques={} lb={} ub={}",
                probes.len(),
                failed.len(),
                adj.len(),
                cliques.len(),
                self.lb,
                self.ub,
            );
        }
        for clique in cliques {
            self.relax_am1_clique(&clique);
        }
        *am1_probe_spent += t0.elapsed();
    }

    /// Greedy disjoint-clique cover over a symmetric conflict graph
    /// (`adapt_am1`'s degree-ordered greedy, standalone for the semantic AM1
    /// edges). Vertices are consumed by the first clique that claims them;
    /// only cliques of size >= 2 are returned. Missing a clique costs
    /// lower-bound quality, never correctness.
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
            // Densest candidates first, id tiebreak — same bias adapt_am1 uses
            // so overlapping cliques peel the richest structure first.
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

    /// Exact iterated-peeling relaxation of one semantic AM1 clique (the same
    /// accounting as install-time `adapt_am1`, applied to live `active`
    /// residuals). Members sorted weight-ascending; while >= 2 remain, the
    /// minimum residual `d` pays lb += d·(members−1) and emits one disjunction
    /// soft over the members at weight `d`, then `d` is subtracted from each
    /// member's residual (exhausted members leave). The maximum-weight member
    /// keeps its surviving residual in `active`.
    ///
    /// Identity preservation (per peel level, under the entailed AM1
    /// "at most one satisfied"): Δlb = d·(k−1); the plain-selector sum loses
    /// d·Σ_i[s_i falsified] and gains d·[all s_i falsified] from the new
    /// disjunction selector, and (k−1) − Σ_i[falsified] + [all falsified] = 0
    /// for both feasible cases (exactly one satisfied → Σ=k−1, all-false term
    /// 0; none satisfied → Σ=k, all-false term 1). So cost(A) is unchanged for
    /// every model and lb stays valid.
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
    fn activate_stratum(&mut self, threshold: Weight) {
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
    fn process_core(&mut self, core: &[Literal]) -> Vec<Literal> {
        self.stats.cores_found = self.stats.cores_found.saturating_add(1);
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
        let sum_sel = root.outs[1].negated();
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
                    let new_sums = self.process_core(&core);
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

    /// Build (once) the best-fitting descent encoding for this instance:
    /// totalizer for uniform weights, GTE for small mixed-weight instances,
    /// adder network otherwise. Returns false when none is available.
    fn ensure_descent_enc(&mut self) -> bool {
        if self.descent.is_some() {
            return true;
        }
        if self.descent_unavailable {
            return false;
        }
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
            self.descent_unavailable = true;
            return false;
        }

        let inputs: Vec<(Literal, Weight)> = soft_idx
            .iter()
            .map(|&i| (self.soft_selectors[i].negated(), self.soft_weights[i]))
            .collect();
        if inputs.is_empty() || inputs.len() > 10_000 {
            self.descent_unavailable = true;
            return false;
        }
        let cap = self.ub.saturating_sub(self.preproc_cost);
        if cap == 0 {
            // lb >= ub is handled by the caller before descending.
            self.descent_unavailable = true;
            return false;
        }

        if inputs.len() <= 10_000 && !self.tuning.force_adder && !self.tuning.force_cluster {
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
    fn descend(
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
            let assumptions: Vec<Literal> = self.descent_guard.into_iter().collect();
            let result = self
                .sat
                .solve_with_assumptions_interruptible(&assumptions, &slice_stop)
                .into_inner();
            match result {
                AssumeResult::Sat(model) => {
                    let cost = self.model_cost(&model);
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
                            let k_bound = (target.div_ceil((*band_min).max(1)) as usize)
                                .min(member_idx.len())
                                .max(1);
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
            if !descent_kick
                && self.best_model.is_some()
                && self.ub.saturating_sub(self.effective_lb()) <= 32
                && self.ub_last_improved.elapsed() > Duration::from_secs(15)
                && Instant::now() >= descent_not_before
                && started.elapsed() > Duration::from_secs(20)
            {
                descent_kick = true;
            }
            if self.best_model.is_some()
                && (descent_kick
                    || (self.stats.cores_found >= self.tuning.lsu_min_cores
                        && oll_stalling
                        && gap_ok
                        && Instant::now() >= descent_not_before))
                && self.softs.len() <= 50_000
                && !self.descent_unavailable
            {
                let kick_entry = descent_kick;
                descent_kick = false;
                // #wce flush (c): the descent is a one-way commit — give it
                // a consistent, fully materialized encoding, and let the
                // flush exhausts' lb/ub motion shape the encoding built
                // below. `!descent_unavailable` above keeps the pre-flush
                // gate equivalent to the old `ensure_descent_enc()` outcome
                // on instances that can never descend, so those don't get
                // their pending batches drained every stalling iteration.
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
                    let outcome = loop {
                        let deadline = if kick_entry {
                            Instant::now() + Duration::from_secs(10)
                        } else {
                            Instant::now() + Duration::from_hours(8760)
                        };
                        let ub_before = self.ub;
                        let outcome = self.descend(deadline, should_stop, on_upper_bound);
                        if outcome.is_some() || !kick_entry || self.ub >= ub_before {
                            break outcome;
                        }
                    };
                    if let Some(outcome) = outcome {
                        return outcome;
                    }
                    // Dry slice expired (kick entries only): back to OLL.
                    // Keep the organic gate from immediately re-committing on
                    // the same post-fold state it never vetted.
                    descent_not_before = Instant::now() + Duration::from_secs(15);
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
                if self.active.len() <= EAGER_PROBE_MAX_ACTIVE
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
                    let new_sums = self.process_core(&core);
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
                lp_boost: LpBoostMode::Auto,
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
                lp_boost: LpBoostMode::Auto,
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
                lp_boost: LpBoostMode::Auto,
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
                lp_boost: LpBoostMode::Auto,
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
            lp_boost: LpBoostMode::Off,
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
            lp_boost: LpBoostMode::Auto,
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
            lp_boost: LpBoostMode::Off,
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
            lp_boost: LpBoostMode::Off,
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
            engine.process_core(&out);
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
                lp_boost: LpBoostMode::Force,
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
            lp_boost: LpBoostMode::Auto,
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
}

#[cfg(test)]
mod abstraction_tests {
    use super::*;

    /// Abstraction sets must form on group-structured instances and leave
    /// the optimum exact: 8 uniform softs under an at-most-2 hard
    /// constraint (all 3-subsets blocked) has optimum cost 6, and the
    /// co-occurring cores over those selectors should coalesce into a
    /// shared counting set.
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
            lp_boost: LpBoostMode::Auto,
        });

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
            lp_boost: LpBoostMode::Off,
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
