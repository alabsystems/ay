// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The float lane: a bounded-variable revised primal simplex in `f64`.
//!
//! It descends from the revised simplex in `ay-pb`'s
//! `optimize/safe_lp_bound.rs` (product-form inverse, sparse FTRAN/BTRAN,
//! periodic refactorization, Dantzig pricing with a Bland fallback, bounded-
//! variable ratio test with bound flips), generalized off the PB `{0,1}`/`>=`
//! box onto arbitrary column and row bounds.
//!
//! ## What this lane is allowed to decide: nothing
//!
//! It computes in `f64`, so it is **advice, never authority**. Its output is a
//! *candidate basis* — a combinatorial object, not a number. [`crate::certify`]
//! then replays that basis in exact rationals and either accepts it or rejects
//! it, at which point the caller falls back to the exact rim. Final pruning and
//! optimality decisions do not consume an uncertified floating-point bound.
//!
//! ## Warm reoptimization
//!
//! Branching changes a BOUND — not the matrix, not the costs. So a child inherits a
//! basis that is still DUAL feasible (every reduced cost still points the right way)
//! and is only PRIMAL infeasible. The bounded dual-simplex path repairs inherited
//! bases while preserving dual feasibility. If it exhausts its budget or fails
//! the post-checks, the solver discards that result and uses the fallback path.
//!
//! ## Computational form
//!
//! The model `lb_r <= a_r·x <= ub_r`, `l_j <= x_j <= u_j` is solved as
//!
//! ```text
//!   minimize  c·x   subject to   A x - s = 0,   l <= x <= u,   lb <= s <= ub
//! ```
//!
//! with one *logical* column `s_r` per row carrying that row's bounds. So
//! `M = [A | -I]`, the right-hand side is `0`, and the all-logical starting
//! basis has `B = -I` — which is exactly the `B_0^{-1} = -I` the product-form
//! inverse below assumes. Rows and columns are then the same kind of thing (a
//! bounded variable), which is what collapses range rows, equalities,
//! one-sided rows and free variables into one uniform pivot loop.

use crate::model::{Col, Model, Sense};

mod bounded_setup;

/// A column's resting place when non-basic.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum NbBound {
    /// At its (finite) lower bound.
    Lower,
    /// At its (finite) upper bound.
    Upper,
    /// Free in both directions, resting at zero. Such a column may only stay
    /// non-basic while its reduced cost is zero.
    Zero,
}

/// Why the pivot loop stopped.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum SimplexStatus {
    /// Phase II priced out: no eligible entering column.
    Optimal,
    /// Phase I could not drive the infeasibility to zero.
    PrimalInfeasible,
    /// An improving direction is blocked by nothing.
    Unbounded,
    /// Iteration cap or deadline. No claim either way.
    Stopped,
    /// The LU factorization DECLINED: its fill would have crossed the memory
    /// budget (`the lu-max-fill-nnz knob`). No claim either way — the caller maps
    /// this to `Outcome::Unknown{MemoryLimit}` at the root and treats it like
    /// `Stopped` (undisproved, unbounded) at an interior node. Distinct from
    /// `Stopped` so the top-level lanes can name the reason honestly.
    OutOfMemory,
    /// The warm dual walk stopped early because its monotone bound reached the
    /// caller's objective cutoff: the basis is dual-feasible (its duals certify a
    /// bound >= the cutoff) but NOT primal-feasible, so it may be PRUNED but never
    /// branched on. The caller re-derives the bound rigorously before pruning.
    Cutoff,
}

/// How a bounded solve should consume an adopted warm basis.
///
/// `PrimalAdvice` is deliberately narrower than the adaptive warm-dual policy:
/// it is a typed, per-call request for locally capped setup work whose stopped
/// candidate will only seed a later proof-bearing solve. It skips the
/// transactional warm-dual attempt so the cap advances primal phase I instead
/// of spending the whole slice on a dual walk that is then rolled back.
///
/// `PrimalProofContinuation` shares that direct-primal preamble, but is
/// explicitly verdict-bearing: callers must apply their ordinary exact
/// optimality/weak-row/Farkas gates to its result.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum WarmSolveMode {
    /// Historical bounded-solve behavior.
    Normal,
    /// Preserve the adopted warm basis but continue directly with primal work.
    PrimalAdvice,
    /// Continue a stopped primal prefix into one fully checked proof solve.
    PrimalProofContinuation,
}

impl WarmSolveMode {
    fn continues_primal(self) -> bool {
        matches!(self, Self::PrimalAdvice | Self::PrimalProofContinuation)
    }
}

/// The float lane's proposal: a basis, and where each non-basic column rests.
/// `Clone` exists for the node-cut admission trial (`bab.rs`): the pre-trial
/// candidate is saved so a rejected cut can restore the node's state exactly.
#[derive(Clone)]
pub(crate) struct Candidate {
    /// Basic column index per row slot.
    pub basis: Vec<usize>,
    /// Resting bound of every column (meaningless for basic ones).
    pub at: Vec<NbBound>,
    /// The f64 primal value of every column. ADVICE ONLY — it decides which
    /// column to branch on and whether a relaxation looks integral, never what
    /// the answer is.
    pub values: Vec<f64>,
    /// The f64 row duals. Advice for the same reason: they are rounded to exact
    /// rationals and fed through weak duality, which turns ANY dual vector into
    /// a rigorous bound, so their inaccuracy costs tightness and never validity.
    pub duals: Vec<f64>,
    /// The phase-I duals at the point infeasibility was declared — a candidate
    /// Farkas ray. Advice: the caller re-derives the contradiction exactly, and
    /// any `y` that fails to produce one is simply discarded.
    pub farkas: Vec<f64>,
    /// `farkas` already passed `safe_farkas_proves_empty` against exactly this
    /// solve's bounds (the dual's noenter exit verifies before it declares —
    /// see `noenter_ray`), so the caller may skip re-running the same check.
    pub farkas_verified: bool,
    pub status: SimplexStatus,
}

/// How often the dual lane actually settles a warm child. Diagnostic only.
/// Dual-simplex accounting for iterations-per-node traces (Gurobi's log prints ~7 it/node
/// on the dense-binary ladder; these say where we stand against that). The warm/cold split
/// is tallied per SOLVE in `solve_bounded` — it answers whether the iterations live in
/// warm node re-solves (basis distance) or in cold heuristic/root solves.
pub(crate) static DUAL_CALLS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub(crate) static DUAL_ITERS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
/// LU-factor diagnostics (--trace): count, summed factor nnz, summed factor nanos.
pub(crate) static LU_FACT_COUNT: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static LU_FACT_NNZ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub(crate) static LU_FACT_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
/// Count of factorizations that returned singular (kept the old factor + deferred retry).
pub(crate) static LU_FACT_FAIL: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
/// LATE LU PROMOTIONS (`Simplex::refactorize`): solves that started on the eta
/// file and were switched to the FT engine mid-flight because their measured
/// eta-rebuild count crossed `cold_lu_eta_rebuilds()`.
pub(crate) static LU_LATE_PROMOTE: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
/// Eta rebuilds across the process, and the largest number any ONE solve paid
/// (`--trace`). Process-global and so NOT decision inputs — they exist to
/// calibrate `the cold-lu-eta-rebuilds knob` against a corpus without a rebuild,
/// and the per-solve maximum is the one that matters because the budget is a
/// per-solve threshold.
pub(crate) static ETA_REBUILD_TOTAL: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static ETA_REBUILD_MAX: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
/// FT-adoption diagnostics (Lever A, `refactorize`): adoptions absorbed as
/// Forrest–Tomlin updates instead of a full base factor / attempts rejected
/// (singular intermediate or update rejection; the full factor then runs) /
/// nanos spent inside successful absorptions.
pub(crate) static ADOPT_FT_OK: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub(crate) static ADOPT_FT_REJ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
/// Of the rejections, the swap-cycle bails (no admissible order; no FTRAN spent).
pub(crate) static ADOPT_FT_CYC: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub(crate) static ADOPT_FT_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static WARM_SOLVES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub(crate) static WARM_ITERS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub(crate) static COLD_SOLVES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub(crate) static COLD_ITERS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub(crate) static DUAL_OK: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
pub(crate) static DUAL_FAIL: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
/// Why it failed: budget exhausted, no eligible entering column, or the post-checks.
pub(crate) static DUAL_BUDGET: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
pub(crate) static DUAL_NOENTER: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
// FUSED BFRT RATIO-TEST PROFILER (`AY_MILP_ITER_PROFILE`, trace-gated). Splits the
// dual ratio test into its BUILD phase (the O(cols) breakpoint scan) and its
// SELECT phase (min-scan + long-step walk + Harris band). Reported as us/pivot so
// phase costs can be compared without relying on noisy end-to-end wall time.
// `RT_DEFERRED` counts Stage-B pivots that entered the argmin directly, never
// materialising `self.bp`. Every timer read is guarded by the flag: zero cost off.
pub(crate) static RT_BUILD_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static RT_SELECT_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static RT_PIVOTS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub(crate) static RT_DEFERRED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
// SELECT-PHASE SUB-BREAKDOWN (`AY_MILP_ITER_PROFILE`, trace-gated). The RTPROFILE
// `select` figure is dominated on wide set-partitioning LPs by ONE cost: the
// long-step (BFRT) breakpoint SORT. This splits the slow-path select into sort /
// walk / band us-per-pivot plus `slow` (pivots that took the sort path) and
// `bp_avg` (mean breakpoints sorted). Every read is flag-guarded: zero cost off.
pub(crate) static SEL_SORT_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static SEL_WALK_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static SEL_BAND_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static SEL_BP_LEN_SUM: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static SEL_SLOW: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

// BASIS-UPDATE PROFILER (`AY_MILP_ITER_PROFILE`, trace-gated). Splits the dual
// per-pivot UPDATE phase (the 42% block that follows FTRAN) into its parts:
//   TAU  = the DSE steepest-edge solve τ = B⁻¹ρ (a second FTRAN),
//   AXPY = the O(cols) dense dual-cost roll d[j] -= θ·arow[j],
//   DSE  = the Forrest–Goldfarb weight roll over the FTRAN support,
//   REST = flips + LU update + xb roll + bookkeeping + alpha clear
//          (= total update minus the three timed parts).
// AROW_NNZ_SUM/UPD_PIVOTS gives the mean pivot-row density — the input that
// decides whether sparsifying the dense AXPY over arow's support is a win.
// Every read is guarded by the flag: zero cost off.
pub(crate) static UPD_TAU_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static UPD_AXPY_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static UPD_DSE_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static UPD_TOTAL_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static UPD_PIVOTS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub(crate) static AROW_NNZ_SUM: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub(crate) static UPD_LU_NANOS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub(crate) static RHO_NNZ_SUM: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub(crate) static ALPHA_NNZ_SUM: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
// REST SUB-DECOMPOSITION (`AY_MILP_ITER_PROFILE`, trace-gated). The UPDPROFILE
// `rest` figure (= total minus tau/lu/axpy/dse) was the biggest opaque chunk.
// These split it exhaustively into its parts so `rest == flip + flipcommit +
// book`:
//   FLIP       = the long-step flip AGGREGATE build (O(m) wflip re-zero + the
//                scatter over the flip set + a THIRD FTRAN, wflip = B⁻¹·Σδ),
//   FLIPCOMMIT = the O(m) `xb -= wflip` roll + the flip-set bound toggles,
//   BOOK       = everything else (step calc, the sparse xb roll over `nz`, the
//                eta append on the no-LU path, the O(1) basis/status/dual writes,
//                and the sparse alpha re-zero over `nz`) — computed as the
//                residual so the three always sum to `rest`.
// FLIP_PIVOTS/FLIP_COLS report how often the flip path fires and its mean width.
// Every read is guarded by the flag: zero cost off.
pub(crate) static UPD_FLIP_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static UPD_FLIPCOMMIT_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static UPD_FLIP_PIVOTS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static UPD_FLIP_COLS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

// PIVOT-EXTRA (PRICE) CENSUS PROFILER (`AY_MILP_ITER_PROFILE`, trace-gated). The
// RTPROFILE (build/select) and UPDPROFILE (tau/lu/axpy/dse/rest) timers leave TWO
// per-pivot chunks UNTIMED: the pre-ratio-test PRICE phase (leaving-variable
// steepest-edge scan + the pivot-row BTRAN ρ = B⁻ᵀe_row + the arow gather ρᵀA) and
// the PRIMARY α = B⁻¹a_q FTRAN that sits between select-end and update-start. This
// closes the census: LEAVE / BTRAN / AROW / ALPHA us-per-pivot (normalised by
// RT_PIVOTS, the per-iteration count). Every read is flag-guarded: zero cost off.
pub(crate) static PX_LEAVE_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static PX_BTRAN_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static PX_AROW_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static PX_ALPHA_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

// PER-SOLVE FIXED-OVERHEAD PROFILER (`AY_MILP_ITER_PROFILE`, trace-gated). The
// RT/UPD/PX profilers all normalise by PIVOT count; they say nothing about the
// per-SOLVE fixed cost that a tiny-basis huge-tree instance (mas74's 13-row LP,
// pk1's 45-row) pays on EVERY `solve_bounded` regardless of how few pivots the
// warm re-solve then takes. This splits `solve_bounded`'s wall into SETUP (pool
// adopt + `reset` + LU-install decision + `warm_start` refactor — everything
// before `sx.run`) and EXTRACT (`extract` + farkas unscale + `Candidate` build
// with its basis/at clones + the three cache write-backs). `run` itself is the
// residual (SOLVE_NANOS − setup − extract) and is what the per-pivot profilers
// already dissect. Normalised by SB_SOLVES (this profiler's own solve count, so
// it is independent of whether `probe_duals` also ran). Every read is
// flag-guarded: zero cost off.
pub(crate) static SB_SETUP_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static SB_EXTRACT_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static SB_TOTAL_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static SB_SOLVES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
// Setup sub-split (part of SBPROFILE): POOL = pool adopt + `reset`; WARM =
// `warm_start` (basis adopt + conditional refactor). The residual of setup is
// the LU-install / crash decision block between them.
pub(crate) static SB_POOL_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static SB_WARM_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

/// Machine-readable one-liner for the per-solve fixed-overhead profiler
/// (`AY_MILP_ITER_PROFILE`). Empty when no `solve_bounded` calls were sampled.
/// `setup`/`extract` are us/solve; `run` is the residual per-solve wall the
/// per-pivot profilers cover. `total` is the full entry-to-return solve wall
/// (a superset of `stats::SOLVE_NANOS`, which stops before the `Candidate`
/// build's basis/at clones).
pub fn sb_profile_line() -> String {
    use std::sync::atomic::Ordering::Relaxed;
    let s = SB_SOLVES.load(Relaxed);
    if s == 0 {
        return String::new();
    }
    let sf = s as f64;
    let setup = SB_SETUP_NANOS.load(Relaxed) as f64;
    let extract = SB_EXTRACT_NANOS.load(Relaxed) as f64;
    let total = SB_TOTAL_NANOS.load(Relaxed) as f64;
    let pool = SB_POOL_NANOS.load(Relaxed) as f64;
    let warm = SB_WARM_NANOS.load(Relaxed) as f64;
    let run = (total - setup - extract).max(0.0);
    format!(
        "SBPROFILE sb_solves={s} setup={:.3}us (pool={:.3}us warm={:.3}us) run={:.3}us extract={:.3}us total={:.3}us (setup {:.1}% extract {:.1}%)",
        setup / sf / 1e3,
        pool / sf / 1e3,
        warm / sf / 1e3,
        run / sf / 1e3,
        extract / sf / 1e3,
        total / sf / 1e3,
        100.0 * setup / total.max(1.0),
        100.0 * extract / total.max(1.0),
    )
}

/// Machine-readable one-liner for the pivot-extra (price + alpha-FTRAN) census
/// profiler (`AY_MILP_ITER_PROFILE`). Empty when no pivots were sampled. Averages
/// are cumulative us/pivot over the process, normalised by `RT_PIVOTS`.
pub fn px_profile_line() -> String {
    use std::sync::atomic::Ordering::Relaxed;
    let p = RT_PIVOTS.load(Relaxed);
    if p == 0 {
        return String::new();
    }
    let pf = p as f64;
    let leave = PX_LEAVE_NANOS.load(Relaxed) as f64;
    let btran = PX_BTRAN_NANOS.load(Relaxed) as f64;
    let arow = PX_AROW_NANOS.load(Relaxed) as f64;
    let alpha = PX_ALPHA_NANOS.load(Relaxed) as f64;
    format!(
        "PXPROFILE px_pivots={p} leave={:.3}us btran={:.3}us arow={:.3}us alpha_ftran={:.3}us price_total={:.3}us",
        leave / pf / 1e3,
        btran / pf / 1e3,
        arow / pf / 1e3,
        alpha / pf / 1e3,
        (leave + btran + arow + alpha) / pf / 1e3,
    )
}

/// Machine-readable one-liner for the fused-ratio-test profiler (`AY_MILP_ITER_PROFILE`).
/// Empty when no pivots were sampled. Averages are cumulative over the process.
pub fn rt_profile_line() -> String {
    use std::sync::atomic::Ordering::Relaxed;
    let p = RT_PIVOTS.load(Relaxed);
    if p == 0 {
        return String::new();
    }
    let b = RT_BUILD_NANOS.load(Relaxed) as f64;
    let s = RT_SELECT_NANOS.load(Relaxed) as f64;
    let d = RT_DEFERRED.load(Relaxed);
    let di = DUAL_ITERS.load(Relaxed);
    let pf = p as f64;
    let sort = SEL_SORT_NANOS.load(Relaxed) as f64;
    let walk = SEL_WALK_NANOS.load(Relaxed) as f64;
    let band = SEL_BAND_NANOS.load(Relaxed) as f64;
    let slow = SEL_SLOW.load(Relaxed);
    let bplen = SEL_BP_LEN_SUM.load(Relaxed) as f64;
    let selsub = if slow > 0 {
        format!(
            " || SELSUB slow={slow} bp_avg={:.0} sort={:.3}us walk={:.3}us band={:.3}us (per-pivot)",
            bplen / slow as f64,
            sort / pf / 1e3,
            walk / pf / 1e3,
            band / pf / 1e3,
        )
    } else {
        String::new()
    };
    format!(
        "RTPROFILE pivots={p} dual_iters={di} build={:.3}us select={:.3}us total={:.3}us deferred={d} ({:.1}%){selsub}",
        b / pf / 1e3,
        s / pf / 1e3,
        (b + s) / pf / 1e3,
        d as f64 / pf * 100.0,
    )
}
/// Machine-readable one-liner for the basis-UPDATE profiler (`AY_MILP_ITER_PROFILE`).
/// Empty when no update was sampled. Averages are cumulative us/pivot over the
/// process; `nnz` is the mean pivot-row density over `cols`.
pub fn upd_profile_line() -> String {
    use std::sync::atomic::Ordering::Relaxed;
    let p = UPD_PIVOTS.load(Relaxed);
    if p == 0 {
        return String::new();
    }
    let pf = p as f64;
    let tau = UPD_TAU_NANOS.load(Relaxed) as f64;
    let axpy = UPD_AXPY_NANOS.load(Relaxed) as f64;
    let dse = UPD_DSE_NANOS.load(Relaxed) as f64;
    let tot = UPD_TOTAL_NANOS.load(Relaxed) as f64;
    let lu = UPD_LU_NANOS.load(Relaxed) as f64;
    let rest = (tot - tau - axpy - dse - lu).max(0.0);
    let flip = UPD_FLIP_NANOS.load(Relaxed) as f64;
    let flipc = UPD_FLIPCOMMIT_NANOS.load(Relaxed) as f64;
    let flip_piv = UPD_FLIP_PIVOTS.load(Relaxed);
    let flip_cols = UPD_FLIP_COLS.load(Relaxed);
    // BOOK is the residual: rest minus the two timed flip sub-costs. It absorbs
    // the step/xb-roll/eta/bookkeeping/alpha-clear so the three sum to `rest`.
    let book = (rest - flip - flipc).max(0.0);
    let restsub = if flip + flipc > 0.0 {
        format!(
            " || RESTSUB flip={:.3}us flipcommit={:.3}us book={:.3}us flip_pivots={flip_piv} ({:.1}%) flip_cols_avg={:.0}",
            flip / pf / 1e3,
            flipc / pf / 1e3,
            book / pf / 1e3,
            flip_piv as f64 / pf * 100.0,
            if flip_piv > 0 { flip_cols as f64 / flip_piv as f64 } else { 0.0 },
        )
    } else {
        String::new()
    };
    let nnz = AROW_NNZ_SUM.load(Relaxed) as f64;
    let rho = RHO_NNZ_SUM.load(Relaxed) as f64;
    let anz = ALPHA_NNZ_SUM.load(Relaxed) as f64;
    let spike = crate::lu::FT_SPIKE_NANOS.load(Relaxed) as f64;
    let elim = crate::lu::FT_ELIM_NANOS.load(Relaxed) as f64;
    let commit = crate::lu::FT_COMMIT_NANOS.load(Relaxed) as f64;
    let ftsplit = if spike + elim + commit > 0.0 {
        format!(
            " || FT spike={:.3}us elim={:.3}us commit={:.3}us",
            spike / pf / 1e3,
            elim / pf / 1e3,
            commit / pf / 1e3,
        )
    } else {
        String::new()
    };
    format!(
        "UPDPROFILE upd_pivots={p} total={:.3}us tau={:.3}us lu={:.3}us axpy={:.3}us dse={:.3}us rest={:.3}us arow_nnz={:.1} rho_nnz={:.1} alpha_nnz={:.1}{ftsplit}{restsub}",
        tot / pf / 1e3,
        tau / pf / 1e3,
        lu / pf / 1e3,
        axpy / pf / 1e3,
        dse / pf / 1e3,
        rest / pf / 1e3,
        nnz / pf,
        rho / pf,
        anz / pf,
    )
}
/// How many `noenter` walks took the verified-Farkas shortcut (skipping the
/// rollback + primal phase-1 re-proof). Split so the scaled/unscaled A/B is
/// visible in the trace dump: `[0]` = unscaled frame, `[1]` = scaled frame
/// (the equilibration-safe unscale-then-verify path).
pub(crate) static DUAL_NOENTER_SHORTCUT: [std::sync::atomic::AtomicUsize; 2] = [
    std::sync::atomic::AtomicUsize::new(0),
    std::sync::atomic::AtomicUsize::new(0),
];
pub(crate) static REFAC_COUNT: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
pub(crate) static REFAC_NANOS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
/// Per-call-site refactorize trigger census (trace only). Indexed by call site:
/// which caller provoked the rebuild. Counts CALLS (before the rep_basis/`same`
/// skips), so on an eta-only instance it equals actual rebuilds and on an LU
/// instance the skip rate is `sum(calls) - REFAC_COUNT - LU_FACT_COUNT`.
pub(crate) static REFAC_REASON: [std::sync::atomic::AtomicU64; 9] = [
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
];
/// Call-site labels for `REFAC_REASON`, in index order.
pub(crate) const REFAC_REASON_LABELS: [&str; 9] = [
    "warm",    // 0: warm_start adopt
    "dcad",    // 1: dual_simplex cadence
    "dverify", // 2: dual_simplex verify-reask (no column enters)
    "ddrift",  // 3: post-dual DRIFT_REFACTOR (kept basis)
    "epert",   // 4: eager-perturb polish
    "pert",    // 5: stopped-perturb retry polish
    "round",   // 6: rounds() round>0 drift
    "pcad",    // 7: primal loop cadence / nnz cap
    "pverify", // 8: primal loop verify-reask (no column enters)
];
#[inline]
pub(crate) fn refac_reason(i: usize) {
    REFAC_REASON[i].fetch_add(1, std::sync::atomic::Ordering::Relaxed);
}
/// Rebuilds that found the basis singular at working precision and REPAIRED it
/// (kicked the dependent columns, filled the uncovered rows with logicals).
pub(crate) static REFAC_REPAIRS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
pub(crate) static DUAL_POSTCHK: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
/// Dual walks abandoned by the divergence guard (violation bloom).
pub(crate) static DUAL_BLOOM: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
/// Warm solves whose dual walk the adaptive bypass skipped (primal-first).
pub(crate) static DUAL_SKIP: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
/// Anatomy of the remaining dual-walk aborts (trace accounting only): a
/// vanishing FTRAN pivot, an LU update rejection, the deadline, or the
/// work-meter. The `_IT` sums record the walk iteration each abort fired at,
/// so the trace can print an average burn per abort kind.
pub(crate) static DUAL_VANISH: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
pub(crate) static DUAL_LUREJ: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
pub(crate) static DUAL_DEADLINE: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
pub(crate) static DUAL_SPEND: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
pub(crate) static DUAL_VANISH_IT: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static DUAL_LUREJ_IT: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static DUAL_BLOOM_IT: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
/// POSITIONAL basis-diff histogram at `refactorize` when an LU operator cache is
/// present but its `rep_basis` does not match the adopted basis (trace-only
/// diagnostics for the warm-start refactorization economics: bucket k counts
/// refactorizations whose diff-in-positions was 1, 2, 3, 4-7, 8-15, 16-31, 32+,
/// or length-mismatched). A positional diff of d is exactly d bounded LU column
/// UPDATES away from reuse.
pub(crate) static BASIS_DIFF_HIST: [std::sync::atomic::AtomicU64; 8] = [
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
];

/// LANE + CALLER ATTRIBUTION of eta rebuilds (`--trace`; diagnostics only,
/// the delta read is skipped entirely unless trace is enabled). Answers the
/// question the LU-lane-extension arm must answer FIRST: of the O(m·nnz) eta
/// rebuilds (`REFAC_COUNT`), which LANE and which CALLER provoked them —
/// because the lane can only be widened where the eta rebuilds actually live.
///
/// LANE buckets (a solve's lane is fixed at entry by whether an LU engine was
/// installed and, if not, whether it warm-started and whether it is
/// `plain_cold`):
///   0 LU        — an LU operator backs the solve (rep_basis reuse / FT lane)
///   1 eta-warm  — no LU engine, warm-started (adopts a parent basis)
///   2 eta-cold-plain  — no LU engine, cold, `plain_cold` (VERTEX-SEEDING:
///                       the pump/dive/RINS chain reads this vertex; moving its
///                       lane changes the seed — the documented landmine)
///   3 eta-cold-other  — no LU engine, cold, not `plain_cold`
///   4 probe-LU  — `probe_duals` (strong-branch), LU operator present
///   5 probe-eta — `probe_duals` (strong-branch), eta lane
pub(crate) static LANE_SOLVES: [std::sync::atomic::AtomicU64; 6] = [
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
];
/// Eta rebuilds (`REFAC_COUNT` delta) attributed to each LANE bucket above.
pub(crate) static LANE_ETA: [std::sync::atomic::AtomicU64; 6] = [
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
];
pub(crate) const LANE_LABELS: [&str; 6] = [
    "LU",
    "eta-warm",
    "eta-cold-plain",
    "eta-cold-other",
    "probe-LU",
    "probe-eta",
];
/// CALLER attribution — the search phase that issued the solve, tagged by
/// `CallerScope` at the heuristic/tree entry points. Same 8 slots for solve
/// count and eta-rebuild delta.
pub(crate) static CALLER_SOLVES: [std::sync::atomic::AtomicU64; 8] = [
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
];
pub(crate) static CALLER_ETA: [std::sync::atomic::AtomicU64; 8] = [
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
];
pub(crate) const CALLER_LABELS: [&str; 8] = [
    "root/other",
    "tree-node",
    "sb-probe",
    "pump",
    "dive",
    "flip-lns",
    "rins-sub",
    "root-lp",
];
thread_local! {
    /// Which search phase the current thread is solving on behalf of (index into
    /// `CALLER_*`). Set by `CallerScope`; defaults to 0 (root/other).
    static CALLER_TAG: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
/// Scoped setter for the current caller tag: install on entry, restore the
/// previous value on drop (so nested phases — a dive inside the root, a probe
/// inside a node — nest correctly). The guard only writes a thread-local
/// `Cell`; the eta-delta read it feeds is itself trace-gated.
pub(crate) struct CallerScope(usize);
impl CallerScope {
    #[inline]
    pub(crate) fn new(tag: usize) -> Self {
        let prev = CALLER_TAG.with(|c| c.replace(tag));
        CallerScope(prev)
    }
}
impl Drop for CallerScope {
    #[inline]
    fn drop(&mut self) {
        CALLER_TAG.with(|c| c.set(self.0));
    }
}
#[inline]
fn caller_tag() -> usize {
    CALLER_TAG.with(std::cell::Cell::get)
}
/// `CALLER_LABELS` index for the flip-LNS primal heuristic (`CallerScope::new(5)`
/// at its entry). The tall_lu bloom-cap relaxation is a TREE-node throughput
/// lever and is held OFF this lane: flip-LNS ranks its switch flips off the warm
/// dual's reduced-cost advice, so changing the warm walk's degenerate vertex
/// re-routes its descent and slows convergence to the incumbent basin (qiu
/// measured: −132.873 reached at kick 77/34.2s WITH the relax vs kick 63/22.3s
/// without — no reclaimable tail left for the saturation-stop). Keeping flip-LNS
/// on the capped baseline walk preserves its tuned trajectory while the tree
/// still gets the relaxed cap.
pub(crate) const CALLER_FLIP_LNS: usize = 5;
/// Record one solve into the lane/caller attribution: `lane` bucket, and the
/// `eta_delta` eta rebuilds it provoked (snapshot difference of `REFAC_COUNT`).
/// Trace-gated by the caller.
#[inline]
fn record_lane(lane: usize, eta_delta: u64) {
    use std::sync::atomic::Ordering::Relaxed;
    LANE_SOLVES[lane].fetch_add(1, Relaxed);
    LANE_ETA[lane].fetch_add(eta_delta, Relaxed);
    let c = caller_tag();
    CALLER_SOLVES[c].fetch_add(1, Relaxed);
    CALLER_ETA[c].fetch_add(eta_delta, Relaxed);
}

// ============================ THE ITERATION LEDGER ============================
//
// `--iter-ledger`. Attributes every simplex ITERATION this process runs to
// the SOLVE PHASE that asked for it, and splits each phase's iterations by KIND
// (dual pivot / primal phase-I / primal phase-II).
//
// WHY THIS EXISTS. The measured gap against Gurobi's LP is 8.2x = 4.87x
// ITERATIONS x 1.67x per-iteration. The per-iteration side is already
// instrumented to death (`AY_MILP_ITER_PROFILE`: RTPROFILE / UPDPROFILE /
// PXPROFILE / SBPROFILE all normalise BY PIVOT and answer "what does one pivot
// cost"). NOTHING attributed the pivot COUNT, so "ay takes five times too many
// steps" could not be localised: root LP, cut re-optimisation, node children,
// strong branching, heuristic sub-solves and in-solve recovery all pour into one
// global `stats::DUAL_ITERS + stats::PRIMAL_ITERS` total. Every attempt to close
// the gap so far has been aimed by guesswork and several regressed (the
// structural-presolve transplant: qnet1 4.18s -> 15.75s, nodes 372 -> 2209).
//
// WHY IT IS DETERMINISTIC. It counts ITERATIONS and SOLVES, never nanoseconds.
// Iteration counts are load-invariant: the same binary on the same input emits
// the identical ledger on an idle box and on a contended one, which is exactly
// what wall-clock attribution cannot do here.
//
// WHY IT SUMS. The two counters `stats::work()` is built from have exactly ONE
// bump site each — `stats::DUAL_ITERS` in `dual_simplex_inner`'s pivot loop and
// `stats::PRIMAL_ITERS` in `loop_phase_inner`'s. The ledger charges its deltas
// around the two functions that OWN those loops (`dual_simplex`, `loop_phase`),
// so the partition is exhaustive BY CONSTRUCTION and `Σ phases == stats::work()`
// is a real self-check, not a hope: if a future arm adds a third pivot loop, the
// residual `unattributed` field in the reported line goes non-zero and says so.
//
// PHASES ARE A FLAT PARTITION. An iteration belongs to exactly one phase — the
// innermost scope live when it ran. Heuristics fired mid-node re-tag themselves
// and restore the node tag on drop (`PhaseScope` is RAII), and the three
// in-solve recovery paths re-tag over whatever asked for the solve, because
// "which caller provoked the recovery" is a question the LANEMAP/CALLERMAP
// census already answers and "how many iterations does recovery eat" is the one
// this instrument exists for.
pub(crate) const LEDGER_PHASES: usize = 12;
/// The unattributed default. A solve issued outside every scope lands here; a
/// large `other` is itself a finding (a phase nobody tagged).
pub(crate) const PH_OTHER: usize = 0;
/// The initial ROOT LP: one cold solve of the (post-presolve, post-root-cut)
/// relaxation, before any branching.
pub(crate) const PH_ROOT_LP: usize = 1;
/// ROOT CUT re-optimisation: each root cut round's re-solve after rows are added.
pub(crate) const PH_ROOT_CUT: usize = 2;
/// A tree NODE's own LP — the warm re-solve from the parent's basis (and the
/// prepared/continuation lanes, which are the same solve by another door).
pub(crate) const PH_NODE: usize = 3;
/// A COLD retry after a warm attempt was abandoned. Both doors lead here: the
/// caller-level retry (`Stopped` warm solve -> `warm = None` re-solve) and the
/// engine's own `try_cold_dual` restart after the warm dual failed and its basis
/// was rolled back.
pub(crate) const PH_COLD_RETRY: usize = 4;
/// NODE-LEVEL cut separation's throwaway trial re-solve (the fixed-slot block).
pub(crate) const PH_NODE_CUT: usize = 5;
/// STRONG BRANCHING / pseudocost probing — both probe shapes (`probe_duals`'s
/// iteration-capped dual walk and the full `solve_bounded` child probe).
pub(crate) const PH_SB_PROBE: usize = 6;
/// The DIVE heuristics.
pub(crate) const PH_DIVE: usize = 7;
/// The feasibility PUMP.
pub(crate) const PH_PUMP: usize = 8;
/// RENS / RINS sub-MIP solves.
pub(crate) const PH_RINS: usize = 9;
/// The flip-LNS primal heuristic.
pub(crate) const PH_FLIP_LNS: usize = 10;
/// RECOVERY: iterations spent re-walking after the engine gave up on a walk it
/// had already paid for — `rounds`' drift retries (round > 0, each preceded by a
/// refactorisation), the lazy perturb-retry-and-polish after a `Stopped` walk,
/// and the chain-distress bundle retry. These are pure re-work: the LP was
/// already being solved once when they started.
pub(crate) const PH_RECOVERY: usize = 11;
pub(crate) const LEDGER_LABELS: [&str; LEDGER_PHASES] = [
    "other",
    "root-lp",
    "root-cut",
    "node",
    "cold-retry",
    "node-cut",
    "sb-probe",
    "dive",
    "pump",
    "rins",
    "flip-lns",
    "recovery",
];
/// `solve_bounded` / `probe_duals` entries charged to each phase, counted at the
/// phase live ON ENTRY. `recovery` counts EPISODES instead (it never enters a
/// solve of its own — it re-tags iterations inside somebody else's), which is
/// the more useful denominator for it anyway.
pub(crate) static PHASE_SOLVES: [std::sync::atomic::AtomicU64; LEDGER_PHASES] =
    [const { std::sync::atomic::AtomicU64::new(0) }; LEDGER_PHASES];
/// Dual-simplex pivots charged to each phase.
pub(crate) static PHASE_DUAL: [std::sync::atomic::AtomicU64; LEDGER_PHASES] =
    [const { std::sync::atomic::AtomicU64::new(0) }; LEDGER_PHASES];
/// Primal PHASE-I iterations charged to each phase.
pub(crate) static PHASE_P1: [std::sync::atomic::AtomicU64; LEDGER_PHASES] =
    [const { std::sync::atomic::AtomicU64::new(0) }; LEDGER_PHASES];
/// Primal PHASE-II iterations charged to each phase.
pub(crate) static PHASE_P2: [std::sync::atomic::AtomicU64; LEDGER_PHASES] =
    [const { std::sync::atomic::AtomicU64::new(0) }; LEDGER_PHASES];
thread_local! {
    /// The solve phase the current thread is running on behalf of (index into
    /// the `PHASE_*` arrays). Set by `PhaseScope`; defaults to `PH_OTHER`.
    /// Thread-local because the parallel prefix workers each run their own
    /// scopes; the counters they feed are process-global atomics, so a
    /// multi-worker run reports the SUM over workers.
    static LEDGER_PHASE: std::cell::Cell<usize> = const { std::cell::Cell::new(PH_OTHER) };
}
/// True for the four primal-heuristic phases. See [`PhaseScope::new`].
#[inline]
fn ledger_phase_is_heuristic(p: usize) -> bool {
    matches!(p, PH_DIVE | PH_PUMP | PH_RINS | PH_FLIP_LNS)
}
/// Scoped setter for the ledger phase: install on entry, restore the previous
/// value on drop, so nested phases (a dive inside a node, a recovery inside a
/// dive) nest correctly and an early return still releases.
///
/// THE OUTERMOST HEURISTIC OWNS EVERYTHING UNDER IT. RINS and RENS run a NESTED
/// `bab_solve` on a sub-model — with its own root LP, its own cut rounds, its
/// own tree and its own strong branching. Left to re-tag freely, that sub-tree
/// pours into `root-lp`/`node`/`sb-probe` and the ledger reports the root LP of
/// a 30-second mas74 run as 271 solves, which is not a root LP by any reading;
/// worse, "what does RINS cost" becomes unanswerable because RINS' own spend is
/// scattered across five other phases. So `new` DECLINES to re-tag while a
/// heuristic phase is live, and a heuristic's number is inclusive of its whole
/// nested search. The two RE-WORK phases are the deliberate exception and use
/// [`Self::new_forced`]: "how many iterations go into redoing a walk we already
/// paid for" is a question worth answering wherever it happens, heuristic
/// included.
///
/// ZERO COST WHEN OFF. Both constructors return `None` unless
/// `--iter-ledger` is set, so the default path pays one relaxed atomic bool
/// load per scope entry (NOT per iteration) and never writes the thread-local.
pub(crate) struct PhaseScope(usize);
impl PhaseScope {
    /// Enter `phase` unless a heuristic phase is already live (see the type note).
    #[inline]
    pub(crate) fn new(phase: usize) -> Option<Self> {
        if !iter_ledger_enabled() {
            return None;
        }
        let prev = ledger_phase();
        if ledger_phase_is_heuristic(prev) {
            return None;
        }
        LEDGER_PHASE.with(|c| c.set(phase));
        Some(PhaseScope(prev))
    }

    /// Enter `phase` unconditionally — for the re-work phases, which are broken
    /// out even inside a heuristic.
    #[inline]
    pub(crate) fn new_forced(phase: usize) -> Option<Self> {
        if !iter_ledger_enabled() {
            return None;
        }
        Some(PhaseScope(LEDGER_PHASE.with(|c| c.replace(phase))))
    }
}
impl Drop for PhaseScope {
    #[inline]
    fn drop(&mut self) {
        LEDGER_PHASE.with(|c| c.set(self.0));
    }
}
#[inline]
fn ledger_phase() -> usize {
    LEDGER_PHASE.with(std::cell::Cell::get)
}
/// Charge one solve (or one recovery episode) to the phase now live.
#[inline]
pub(crate) fn ledger_note_solve() {
    if iter_ledger_enabled() {
        PHASE_SOLVES[ledger_phase()].fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }
}
/// One parseable line per run, in the shape of `ROOTCLOSURE` / `LPSTAT` /
/// `RTPROFILE`: `key=value` tokens a script can split on whitespace.
///
/// Per phase, `<label>=<solves>s/<dual>d/<p1>+<p2>p/<total>i@<iters-per-solve>`.
/// Phases with no traffic are omitted. Both the COUNT and the SOLVES are
/// reported because iterations-per-SOLVE is the diagnostic ratio: a phase with
/// 40% of the iterations is a different problem depending on whether it ran 10
/// solves or 100,000.
///
/// `total` is the ledger's own sum and `engine` is `stats::work()`; `unattributed`
/// is their difference and MUST be 0. A non-zero value means a pivot loop exists
/// that neither `dual_simplex` nor `loop_phase` owns — the ledger is wrong, and
/// the line says so rather than quietly under-reporting.
#[must_use]
pub fn iter_ledger_line() -> String {
    use std::sync::atomic::Ordering::Relaxed;
    let engine = stats::work();
    let mut parts: Vec<String> = Vec::new();
    let mut sum = 0u64;
    for p in 0..LEDGER_PHASES {
        let (s, d, p1, p2) = (
            PHASE_SOLVES[p].load(Relaxed),
            PHASE_DUAL[p].load(Relaxed),
            PHASE_P1[p].load(Relaxed),
            PHASE_P2[p].load(Relaxed),
        );
        let it = d + p1 + p2;
        sum += it;
        if s == 0 && it == 0 {
            continue;
        }
        parts.push(format!(
            "{}={s}s/{d}d/{p1}+{p2}p/{it}i@{:.1}",
            LEDGER_LABELS[p],
            it as f64 / s.max(1) as f64,
        ));
    }
    if parts.is_empty() {
        return String::new();
    }
    format!(
        "ITERLEDGER total={sum} engine={engine} unattributed={} | {}",
        engine as i64 - sum as i64,
        parts.join(" "),
    )
}

/// PER-WALK DUAL ANATOMY (`AY_MILP_DUAL_ANATOMY`; trace-accounting only, off by
/// default and skipped entirely unless the env is set). Answers WHERE a long
/// degenerate dual walk spends its iterations, PARTITIONED BY HOW THE WALK
/// EXITED — because on qiu the long walks end in `noenter` (an infeasibility
/// proof) and score as wins, so the aggregate `it/call` hides which regime is
/// long and whether the iterations move the bound or just shuffle a degenerate
/// face. Bucket index (`DUAL_ANAT_LABELS`): 0 = noenter (Farkas / primal
/// infeasible), 1 = optimum reached, 2 = other (budget/abort/deadline/cutoff/
/// spend). Each metric array is summed over its bucket's walks:
///   WALKS   — number of walks that exited this way
///   ITERS   — dual pivots taken
///   DTHETA  — pivots whose dual step `theta≈0` (dual-degenerate shuffle)
///   DSTEP   — pivots whose primal `|step|≈0` AND no bound flip (stall pivot)
///   FLIP    — pivots that flipped ≥1 bound (a long-step / BFRT pivot)
///   ZFLAT   — walks whose dual objective `z` rose by < `DUAL_ANAT_ZTOL` over
///             the WHOLE walk (reached the verdict without moving the bound)
/// A walk that is genuinely FAR shows ITERS≈moving pivots (low DTHETA/DSTEP);
/// a walk that CYCLES on a degenerate face shows most iters in DTHETA/DSTEP.
pub(crate) static DUAL_ANAT_WALKS: [std::sync::atomic::AtomicU64; 3] = [
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
];
pub(crate) static DUAL_ANAT_ITERS: [std::sync::atomic::AtomicU64; 3] = [
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
];
pub(crate) static DUAL_ANAT_DTHETA: [std::sync::atomic::AtomicU64; 3] = [
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
];
pub(crate) static DUAL_ANAT_DSTEP: [std::sync::atomic::AtomicU64; 3] = [
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
];
pub(crate) static DUAL_ANAT_FLIP: [std::sync::atomic::AtomicU64; 3] = [
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
];
pub(crate) static DUAL_ANAT_ZFLAT: [std::sync::atomic::AtomicU64; 3] = [
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
];
/// Walk-length histogram for NOENTER-exiting walks only (the qiu class), so the
/// trace shows whether the length is a tight cluster or a spread. Buckets:
/// 0, 1-8, 9-32, 33-64, 65-128, 129-256, 257+.
pub(crate) static DUAL_ANAT_NOENTER_HIST: [std::sync::atomic::AtomicU64; 7] = [
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
];
pub(crate) const DUAL_ANAT_LABELS: [&str; 3] = ["noenter", "opt", "other"];
/// `AY_MILP_DUAL_ANATOMY` gate — the per-walk anatomy accounting is skipped
/// entirely unless this is set (the hot loop pays one bool load per walk).
fn dual_anatomy_enabled() -> bool {
    // B12: caller-layer switch; the never-set AY_MILP_DUAL_ANATOMY env read is gone.
    crate::tune::on(crate::tune::Knob::DualAnatomy)
}
/// Threshold below which a whole-walk dual-objective rise counts as "flat"
/// (see `DUAL_ANAT_ZFLAT`).
const DUAL_ANAT_ZTOL: f64 = 1e-7;

/// Output of `FloatLp::factor_probe`: the FTRAN/BTRAN images a basis produces on
/// one forced factorization lane, plus the lane's fill and singular-repair kick
/// count. The differential harness (`diag_bump_lu_diff`, `tests/bump_lu_diff.rs`)
/// runs it on requested lane pairs and asserts the images and repairs agree,
/// including the opt-in block-triangular-factor (BTF) lane.
pub(crate) struct FactorProbe {
    /// One dense `B⁻¹·M_j` (length m) per requested FTRAN column, remapped to
    /// CANONICAL basis-column order (pivot/scaled frame) — lane-invariant.
    pub ftran: Vec<Vec<f64>>,
    /// One dense row of `B⁻¹` (length m, constraint-row indexed, original frame)
    /// per requested basis column — the dual functional of that column.
    pub btran: Vec<Vec<f64>>,
    /// `sx.etas.entries()` — the eta-file fill after the forced factorization.
    pub fill: usize,
    /// Whether the final successful rebuild actually used the bump-LU segment.
    /// A requested lane is not proof of execution because the peel/floor gate
    /// may decline it or the fill guard may retry in slot order.
    pub bump_lu_used: bool,
    /// Dependent columns kicked to their bounds during the factorization.
    pub kicked: usize,
    /// Exact original-basis columns kicked to their bounds. Comparing only the
    /// count can hide two lanes repairing different singular columns.
    pub kicked_columns: Vec<usize>,
    /// The post-refactorize basis order (`sx.basis`): which basis column sits in
    /// each row slot. The two lanes pivot the bump differently, so this DIFFERS
    /// between them even though they invert the same operator — the evidence that
    /// the column-keyed comparison is doing real work.
    pub basis_order: Vec<usize>,
    /// Wall time of the whole probe (warm_start + FTRAN + BTRAN).
    pub secs: f64,
}

/// The LP in computational form. Columns `0..n` are structural, `n..n+m`
/// logical (one per row).
#[derive(Clone)]
pub(crate) struct FloatLp {
    pub n: usize,
    pub m: usize,
    pub cols: usize,
    /// One top-level native MILP solve's measurement-only exclusion latch.
    /// Cloned LPs share it; standalone LPs carry `None`.
    ft_adoption_solve_latch: Option<crate::sepstat::FtAdoptionSolveLatch>,
    /// CSC of `A`: column `j` occupies `col_ptr[j]..col_ptr[j + 1]`.
    col_ptr: Vec<usize>,
    col_idx: Vec<usize>,
    col_val: Vec<f64>,
    /// CSR of the SAME `A`. The dual simplex needs the pivot ROW every iteration, and
    /// building it column-by-column means a scattered gather of `rho` per column. Row-wise
    /// it is a sequential sweep the compiler can vectorise: same flops, and the cache
    /// stops fighting. On a dense matrix that is the whole difference.
    row_ptr: Vec<usize>,
    row_idx: Vec<u32>,
    row_val: Vec<f64>,
    /// Row-major DENSE mirror of the structural matrix — row `r` is
    /// `dense_rows[r * n..(r + 1) * n]` — built only when the matrix is dense
    /// enough (and small enough) that the CSR walks' per-entry index loads are
    /// the real cost. The hot row kernels (`arow` build, `recompute_xb`,
    /// `fill_yta`) then run as straight-line dense passes the compiler
    /// vectorises. Empty when not built; every user falls back to the CSR/CSC.
    ///
    /// Padding a row with its zeros is VALUE-identical to walking its
    /// non-zeros: for any column `j` the contributions still arrive in
    /// ascending row order, and the extra terms are exact `±0.0`s, which
    /// change no finite accumulator (only, at worst, the sign of a zero — and
    /// every consumer treats a zero entry as "absent" via magnitude tests).
    dense_rows: Vec<f64>,
    /// Bounds of every column, structural then logical (a logical carries its
    /// row's bounds). May be `±INFINITY`.
    pub lower: Vec<f64>,
    pub upper: Vec<f64>,
    /// Minimize-form cost of every column (logicals cost nothing).
    pub cost: Vec<f64>,
    /// The sense the caller asked for. `cost` is always the MINIMIZE form, so a
    /// Maximize objective is stored negated; this records the negation so the
    /// exact lane can recover the caller's own coefficients.
    pub sense: Sense,
    /// Largest magnitude in the data; scales the tolerances.
    scale: f64,
    /// Cross-solve LU cache (see `LuCache`).
    lu_cache: LuCacheCell,
    /// Cross-solve `Simplex` pool: the whole solver state (a couple dozen
    /// vectors) is reset-in-place per solve instead of reallocated — see
    /// `Simplex::reset`. Same take/put + Clone-to-None protocol as the caches.
    sx_cache: SxCell,
    /// Dual steepest-edge weights from the previous solve on this LP — reference
    /// weights for the next warm solve (a unit restart burns the first pivots of
    /// every child re-learning the same row norms). Cold solves reset to units.
    /// Cross-probe LU reuse for a bounded strong-branch sweep (see
    /// `ProbeReuse`). Armed explicitly around one probe loop; otherwise inert.
    probe_reuse: ProbeReuseCell,
    /// TRUE once a cut-slot REWRITE has changed this LP's matrix in place
    /// (`reload_rows`) — i.e. warm bases stored elsewhere in the tree may predate
    /// the matrix they will be adopted against. The dual simplex consults it to
    /// run its entry bound-flip repair (see `dual_simplex`); every LP that never
    /// rewrites rows keeps that path off and its walks bit-for-bit unchanged.
    pub(crate) cut_slots_live: std::cell::Cell<bool>,
    /// ADAPTIVE WARM-DUAL BYPASS state: `(attempts, wins, skips_since_probe)`.
    /// See `warm_dual_should_attempt`. Per-LP-instance (`Cell`, like the solver
    /// pool): the policy is a property of the model's regime, not of the
    /// process.
    dual_adapt: std::cell::Cell<(u32, u32, u32)>,
    /// CHAIN-SHAPE class verdict, decided once on the first cold eta-path solve
    /// (0 = undecided, 1 = chain, 2 = not). A tall, nearly singleton-peelable
    /// matrix enables the triangular equality crash, peel preorder, and Devex
    /// from iteration zero. The broad size class keeps its existing path;
    /// `--no-chain-shape` disables this structural gate.
    chain_shape: std::cell::Cell<u8>,
    /// Typed per-instance override for the cold affine-chain distress-probe
    /// iteration budget. `None` preserves the historical
    /// `the chain-probe knob`/20,000-iteration policy.
    chain_distress_probe_iters: Option<u64>,
    /// Per-instance advice to try the triangular equality crash immediately on
    /// a cold solve, without changing the global size/shape policy.  The LP
    /// harvest lane sets this for affine-chain relaxations; every other caller
    /// leaves the default `false` and keeps its historical path.  The crash
    /// still validates equality density, peel depth, pivots, and fill before it
    /// installs anything, and falls back to the all-logical basis on a decline.
    eager_affine_crash: bool,
    /// Per-instance typed request to retain bounded-range rows' logicals in a
    /// triangular-crash basis. The effective policy also honors the historical
    /// exact `AY_MILP_RANGE_LOGICAL_CRASH=1` environment opt-in.
    range_logical_triangular_crash: bool,
    /// COLD solves on this instance take the CLASSIC path: no cold dual-simplex
    /// start, no LU engine — the eta-file primal, bit-for-bit as before those
    /// existed. Set by branch-and-bound on ITS OWN `FloatLp` (and inherited by
    /// the heuristics' clones of it), because the ROOT VERTEX seeds every
    /// heuristic: air05's optimal face is enormously degenerate, the feasibility
    /// pump's landing is a function of WHICH optimal vertex it starts from, and
    /// switching the seeding solve to the cold dual moved the 60s incumbent
    /// 27875 -> 28321 with the bound unchanged (measured, three configurations).
    /// The speed the cold dual buys belongs to the CUT LOOP's per-round LPs and
    /// the warm-failure fallbacks at nodes, which keep it: this flag only
    /// pins the solves whose ANSWER IS A VERTEX CHOICE, not a number. WARM
    /// solves of a WIDE-AND-TALL instance are likewise not pinned (their
    /// answer is a child bound, and the eta path's per-`warm_start` rebuild
    /// is the measured refactor storm) — see `classic_pin` in `solve_bounded`.
    pub(crate) plain_cold: bool,
    /// PER-INSTANCE eager anti-degeneracy (see `eager_perturb_mode`): perturb the box
    /// before the walk, restore before judging — path-only, never the answer. Set by
    /// callers whose LPs are KNOWN degenerate crawls (the lift-and-project CGLP: measured
    /// on rout, 8/12 solves ground 20k+ degenerate pivots lazily; 12/12 solve in 0.1-0.3s
    /// eagerly). Default `false`: every other instance keeps its path bit-for-bit.
    pub(crate) eager_perturb: bool,
    /// ARMED-EAGER state (see `eager_perturb_mode`): this LP has already had a
    /// COLD, unperturbed walk come back `Stopped`. Set once, never cleared —
    /// a model whose crash-basis phase I cycles once cycles again, and the
    /// point of the arm is that the SECOND cold solve does not re-pay the
    /// stall before perturbing. `Cell`, like `dual_adapt`/`chain_shape`: the
    /// verdict is a property of the model's regime, not of the process.
    cold_stalled: std::cell::Cell<bool>,
    /// The three magnitudes kept APART, because they are in different units and the tolerances
    /// that use them are too. Lumping them into one `max` means a large right-hand side inflates
    /// the DUAL tolerance, which is how `gen` (max |rhs| ~ 2e9) came to demand a reduced cost
    /// above 2.0 before a column would price in -- nothing did, and phase I called a feasible LP
    /// infeasible on its first iteration.
    mat_scale: f64,
    rhs_scale: f64,
    cost_scale: f64,
    /// OBJECTIVE CUTOFF (minimize form) for warm node solves: the incumbent value
    /// the relaxation must beat. The bounded dual simplex holds a dual-feasible
    /// basis whose objective is a monotone-increasing lower bound on the node's LP
    /// min, so once that objective reaches the cutoff the node is provably prunable
    /// and the walk can stop — no need to reach primal feasibility. `INFINITY`
    /// means "no cutoff". Consumed (reset to INFINITY) at the top of each solve so
    /// it applies to exactly the one solve the caller armed it for.
    pub(crate) cutoff: std::cell::Cell<f64>,
    /// POWER-OF-2 EQUILIBRATION (empty ⇒ off). The cifar100 NN matrices span 13
    /// orders of magnitude and the simplex walked ~10k iterations per cold solve on
    /// them; geometric row/column scaling compresses that and was measured at 12×
    /// fewer iterations, verdict-preserving 30/30 (the milp_profile prototype).
    /// Scales are powers of two — applying them is a pure exponent shift, EXACT —
    /// and integer/binary columns keep C_j = 1 so branching bounds, integrality
    /// tests and no-good comparisons see identical values in both frames.
    ///
    /// THE FRAME CONTRACT: only the pivot kernels see scaled data (via the private
    /// `p_*` mirrors and the per-solve scaled bounds/cost in `Simplex`); every
    /// public read — `column`/`row`/`lower`/`upper`/`cost` — serves the ORIGINAL
    /// model bits, so the certification rim, the safe/exact bounds, the Farkas
    /// replay and `check_point` are structurally unable to read the scaled frame.
    /// `Candidate` crosses back at the boundary: `basis`/`at` are frame-invariant
    /// combinatorial objects; `values`/`duals`/`farkas` are unscaled on extract.
    /// `bnd_mul[j]` maps an original bound INTO the scaled frame (structural:
    /// 2^-cexp, logical: 2^rexp); `val_mul[j]` maps a scaled value back OUT.
    rexp: Vec<i16>,
    cexp: Vec<i16>,
    bnd_mul: Vec<f64>,
    val_mul: Vec<f64>,
    scol_val: Vec<f64>,
    srow_val: Vec<f64>,
    sdense_rows: Vec<f64>,
    /// Tolerance stats of the SCALED data — the whole point: the tolerances that
    /// misprice a 13-orders matrix are sized off these when scaling is on.
    sscale: f64,
    smat_scale: f64,
    srhs_scale: f64,
    scost_scale: f64,
}

/// Equilibration mode from `the scale knob`: unset/`0` off, `1` force-on, `auto` =
/// scale when the matrix exponent span exceeds `AUTO_SPAN_BITS`.
///
/// DEFAULT OFF — a measured negative, not caution: on today's engine the scaled
/// frame STALLS the cold wide phase 1 on the cifar100 w2 window (6,465 iterations,
/// `moved=1`, `Stopped`) while the unscaled solve finishes in 9.4s/5,831 iters —
/// and the model-level prototype (`MILP_EQUILIBRATE`) now stalls IDENTICALLY
/// (7,746 iters, `moved=2`), so the 2026-07-14 "12× fewer iterations" premise
/// predates the wide-tall eager-perturbation/stall-abort work and no longer
/// transfers. The frame plumbing here is verified (full suite green with scaling
/// FORCED on) and stays as the substrate for a future phase-1-robust scaling.
fn equil_mode() -> u8 {
    match crate::tune::count_opt(crate::tune::Knob::Scale) {
        Some(1) => 1,
        Some(2) => 2,
        _ => 0,
    }
}

/// AUTO threshold: scale when max/min nonzero |a| exceeds 2^24 (~7 orders).
const AUTO_SPAN_BITS: i32 = 24;

/// The raw binary exponent of a finite nonzero f64 — the cheap `log2` proxy the
/// equilibration passes run on (geometric means to within a factor of 2).
#[inline]
fn bexp(v: f64) -> i32 {
    (((v.abs().to_bits() >> 52) & 0x7ff) as i32) - 1023
}

/// Iteration cap. Generous: the ratio test plus the Bland fallback guarantee
/// termination, so this only bounds pathological instances.
/// The iteration cap on one phase.
///
/// THE OPEN BLOCKER IS PHASE I, AND IT IS NOT THE PRICING RULE. Four MIPLIB instances -- air03,
/// air05, mod010, nw04 -- lose because their ROOT LP comes back `Stopped`, so branch-and-bound
/// never leaves its root node. There are two distinct faults behind that, both in phase I:
///
/// 1. IT GRINDS. air03 (124 rows, 10,757 columns) hits this cap with `stall = 199,906`: the total
///    infeasibility is frozen at 66.0 and has not moved in almost two hundred thousand
///    consecutive pivots, with Bland's rule already engaged. air03 is set partitioning -- every
///    row is `= 1` -- so the all-logical crash basis starts every basic variable FIXED
///    (`lo == up` for an equality row's logical) and phase I begins maximally degenerate. Bland's
///    anti-cycling guarantee assumes a FIXED cost vector, and the phase-I costs are rebuilt every
///    iteration from which basics currently violate which bound, so it guarantees nothing here.
///
/// 2. IT GIVES UP INSTANTLY. air05 and nw04 return `Stopped` in 0.00s: phase I prices in a column
///    whose ratio test is UNBOUNDED and bails (`!min_t.is_finite() => Stopped`). A column that
///    moves no basic variable should not have priced in at all, so this is an inconsistency
///    between the phase-I pricing and its ratio test, not a real unboundedness.
///
/// THINGS ALREADY MEASURED AGAINST THIS THAT DO NOT FIX IT -- do not re-try them blind:
///   * Devex pricing (helps the grind, changes no verdict; see `DEVEX_WIDTH`).
///   * Partial pricing (no measurable effect at all).
///   * A Harris two-pass ratio test (largest pivot among the ties widened by a feasibility
///     tolerance -- the textbook answer to exactly this symptom). It cut air03's phase I from
///     5.7s to 3.2s and still ended `Stopped`, and cost the dense case 9.1s -> 9.7s.
///
/// What this actually needs is an anti-degeneracy procedure for phase I -- bound
/// perturbation/EXPAND -- and a crash basis that does not start every equality row's logical
/// fixed and basic. Fault 2 should be settled first: it is a bug, not a hard problem.
const MAX_ITERS: usize = 200_000;
/// Eta updates that must have accumulated before a declared optimum is worth re-checking against a
/// freshly factorised basis -- see the note where it is used.
fn verify_after() -> usize {
    // B12: caller-layer value; the never-set AY_MILP_VERIFY_AFTER env read is
    // gone.
    crate::tune::count(crate::tune::Knob::VerifyAfter, VERIFY_AFTER)
}
const VERIFY_AFTER: usize = 20;

/// Env toggles consulted on EVERY solve (~70k times a proof) — `getenv` walks
/// the environment block each call, so the answer is cached. None of these
/// change mid-process (no test or caller sets them at runtime).
/// Attribution-only RAII stamp charging one `solve_bounded` to its tree level
/// (see `crate::attrib`). Measurement only.
struct AttribLpStamp(std::time::Instant, usize);
impl Drop for AttribLpStamp {
    fn drop(&mut self) {
        use std::sync::atomic::Ordering::Relaxed;
        crate::attrib::LP_NANOS_BY_LEVEL[self.1]
            .fetch_add(self.0.elapsed().as_nanos() as u64, Relaxed);
        crate::attrib::LP_CALLS_BY_LEVEL[self.1].fetch_add(1, Relaxed);
    }
}

fn trace_enabled() -> bool {
    static B: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *B.get_or_init(|| crate::debug_flags::milp_debug_flags().trace)
}
/// EAGER anti-degeneracy: perturb the box BEFORE the phase-II cleanup, not only after a `Stopped`.
/// Set-partitioning LPs (air05: 426 equality rows) reach a primal-feasible-but-not-dual-optimal
/// basis and pay a long, degenerate phase-II walk to price it out; nudging the bounds apart first
/// makes those steps non-degenerate. Sound by construction — it restores the true box before
/// optimality is judged, so it can change the PATH but never the admitted verdict.
///
/// THREE MODES, because "path only" is not the same as "free". `--eager-perturb-mode`:
/// * `0`   — never (the `wide_tall` gate and a caller's own `lp.eager_perturb` still apply).
/// * unset / `1` — ARMED (the default): a COLD solve of an LP whose cold, unperturbed walk has
///   ALREADY come back `Stopped` at least once. See `eager_perturb_applies`.
/// * `2` — every solve. This is the blanket default that shipped 2026-07-20
///   (`d82673540`) and it is the downstream optimization consumer's documented lever for the 540-binary diff-net root
///   LP (the development design notes).
///
/// WHY THE BLANKET DEFAULT WAS RETIRED. Its own commit message asked for exactly this pass:
/// "Large MIPLIB-scale general instances are not checked into the repo; recommend a confirming
/// pass on the local MIPLIB tuning set before considering the gate fully retired." The pass was
/// run and the blanket gate is a NET LOSS on the tuning set. Measured 60 s serial, same binary,
/// `--sym-branch-band`:
///
/// | model  | mode 2 (the 2026-07-20 default) | armed (this default) |
/// |--------|---------------------------------|----------------------|
/// | rout   | FEASIBLE 1109.61, 64,138 nodes  | **OPTIMAL 1077.56, 30/30 @14.45-15.22 s**, 17,616 nodes |
/// | noswot | FEASIBLE -41 (bound -43)        | **OPTIMAL -41 @51.2 s** |
/// | qiu    | OPTIMAL -132.873136947          | OPTIMAL -132.873136947 @45.9 s |
/// | misc07 | OPTIMAL 2810                    | OPTIMAL 2810 @5.4 s |
///
/// The damage is on the COLD solves, not the warm node LPs: restricting the blanket gate to
/// cold solves alone still loses BOTH proofs (rout FEASIBLE 38,563-38,971 nodes; noswot
/// FEASIBLE, 628,469 nodes). That is the `plain_cold` argument in this same struct — the root
/// vertex seeds every heuristic, so perturbing the solve whose answer is a VERTEX CHOICE moves
/// the whole search. Arming on a demonstrated stall keeps the eager path for the class that
/// needs it (a crash-basis phase I that cycles once cycles again) and leaves every model whose
/// cold walk never stalls bit-for-bit as it was before 2026-07-20.
fn eager_perturb_mode() -> u8 {
    // B29: caller-layer value (0 off | 1 armed-on-stall | 2 all walks,
    // builder-validated); out-of-domain reads as the default.
    match crate::tune::count_opt(crate::tune::Knob::EagerPerturbMode) {
        Some(m @ (0 | 2)) => m as u8,
        _ => 1,
    }
}

/// The armed gate itself, as a pure predicate over `(mode, warm, stalled)`.
fn eager_perturb_applies_to(mode: u8, warm_started: bool, cold_stalled: bool) -> bool {
    match mode {
        0 => false,
        1 => !warm_started && cold_stalled,
        _ => true,
    }
}
/// Does the eager path apply to THIS solve? 0 = never, 1 = ARMED, 2 = every solve.
///
/// ARMED is "the lazy retry's trigger, one solve earlier". The lazy path already
/// perturbs after a `Stopped` — the complaint that motivated the blanket default was
/// that it "fires too late (budget already burned)". So: pay the stall ONCE, record
/// it on the LP (`cold_stalled`), and every LATER cold solve of that LP perturbs up
/// front. the downstream optimization consumer's diff-net root LP is solved four times and stalls on the first, so it
/// keeps the eager path for three of them; rout and noswot never arm at all, which
/// is why they get their pre-2026-07-20 search back.
///
/// WARM solves are excluded in both directions (they neither arm nor consume the
/// arm): a warm node LP starts from a parent's optimal basis, and its `Stopped` is
/// the warm-start-drift regime the `try_cold_dual` fallback exists for, not the
/// crash-basis phase-I cycling this perturbation answers.
fn eager_perturb_applies(warm_started: bool, lp: &FloatLp) -> bool {
    eager_perturb_applies_to(eager_perturb_mode(), warm_started, lp.cold_stalled.get())
}
/// FUSED SINGLE-PASS BFRT RATIO TEST (`AY_MILP_FUSED_RT`). The dual ratio test
/// does two O(cols) passes: a BUILD loop that materialises the breakpoint Vec
/// `self.bp`, then a separate min-scan over it. Stage A folds that min-scan INTO
/// the build loop — same argmin, same entering column, so byte-identical pivot
/// stream / node count / verdict (walk-invariant). Stage B, on the warm no-flip
/// fast path of a NON-churn-band shape (where `self.bp` is not needed for a
/// Harris band or a long-step sort), defers materialising `self.bp` entirely and
/// enters the argmin directly; a genuine long step re-scans to fill `self.bp`.
/// Gated so the original two-pass path is the A/B baseline; the entering column —
/// hence every exact verdict — is identical either way.
fn fused_rt_enabled() -> bool {
    // Stage A is PROVEN walk-invariant (byte-identical pivot stream / node counts /
    // verdict off-vs-on across the whole corpus + k124 cert), and a uniform speedup,
    // so it ships DEFAULT-ON. `AY_MILP_NO_FUSED_RT` restores the two-pass A/B baseline.
    // B12: caller-layer switch; the never-set AY_MILP_NO_FUSED_RT env read
    // is gone.
    !crate::tune::on(crate::tune::Knob::NoFusedRt)
}
/// MASKED / BRANCHLESS BUILD experiment (`AY_MILP_RT_MASKED`, requires fused_rt).
/// Splits the fused BUILD into (1) a branch-free `rt_ratio[j] = |d[j]/arow[j]|`
/// pass over ALL columns (vectorisable — the division is the same IEEE op per
/// column, so eligible columns get byte-identical breakpoints) and (2) the same
/// filtered push+argmin pass reading `rt_ratio[j]` instead of dividing inline.
/// Byte-identical by construction (same bp, same first-minimal kmin), VERIFIED:
/// air05 cold-LP dual pivots = 2904 IDENTICAL on/off.
///
/// MEASURED A DEAD-END (kept opt-in, byte-identical & harmless, to spare the next
/// arm the re-derivation — cf. `tau_nz_enabled`). The masked form is ~6% SLOWER:
/// air05 build 23.36us → 24.75us/pivot. It divides over ALL columns (air05: 7,195)
/// instead of only the eligible subset the fused single pass reaches (~half), and
/// vector-divide throughput on this box does not recover the doubled division
/// count. The fused single-pass build (Stage A) stays the default.
fn rt_masked_enabled() -> bool {
    static B: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *B.get_or_init(|| false)
}
/// INCREMENTAL ELIGIBILITY BITMASK for the dual ratio-test build (`rt_kind`; kill
/// switch `AY_MILP_NO_RT_KIND`). Default-ON: the bitmask scan reads one `u8` per
/// column in place of the 16-byte `basic_row` `Option` load + the `at` load + the
/// 5-arm eligibility match, and is byte-identical to the 4-stream build (same
/// breakpoints, same first-minimal argmin, same pivot stream). See `rt_kind`.
fn rt_kind_enabled() -> bool {
    // B12: caller-layer switch; the never-set AY_MILP_NO_RT_KIND env read is gone.
    !crate::tune::on(crate::tune::Knob::NoRtKind)
}
/// Correctness harness for `rt_kind` (`AY_MILP_RT_KIND_VERIFY`): recompute the
/// eligibility bitmask from scratch before every ratio-test scan and assert it
/// matches the incrementally-maintained one. O(cols) per pivot — testing only;
/// proves the incremental maintenance never drifts from the ground truth.
fn rt_kind_verify_enabled() -> bool {
    // B6: the AY_MILP_RT_KIND_VERIFY env switch is deleted. The O(cols)
    // ground-truth verifier is testing-only; enable by editing this constant.
    false
}
/// Per-iteration ratio-test profiler (`AY_MILP_ITER_PROFILE`). See `rt_profile_line`.
fn iter_profile_enabled() -> bool {
    // B12: caller-layer switch; the never-set AY_MILP_ITER_PROFILE env read is gone.
    crate::tune::on(crate::tune::Knob::IterProfile)
}
/// Per-phase ITERATION LEDGER (`--iter-ledger`). See `iter_ledger_line`.
/// Read once per SCOPE ENTRY and once per dual/primal WALK — never inside a
/// pivot loop, so the default path pays a relaxed atomic load a few times per
/// solve and nothing per iteration.
///
/// Process-global like the phase counters it gates, and enabled by
/// [`enable_iter_ledger`] at driver CLI parse — deliberately NOT a
/// caller-layer knob: the ledger must also cover the root-closure and
/// LP-only diagnostic paths, which run outside any active solve profile
/// (B38 left this reading an env name nothing sets, so the flag printed an
/// empty ledger).
static ITER_LEDGER_ON: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Turn on the per-phase iteration ledger for this process (`--iter-ledger`
/// in the drivers). Call before solving; the counters accumulate from here on
/// and [`iter_ledger_line`] reports them.
pub fn enable_iter_ledger() {
    ITER_LEDGER_ON.store(true, std::sync::atomic::Ordering::Relaxed);
}

fn iter_ledger_enabled() -> bool {
    ITER_LEDGER_ON.load(std::sync::atomic::Ordering::Relaxed)
}
/// BREAKPOINT-SORT INTEGER-KEY comparator (`AY_MILP_NO_RT_BITS_KEY` kills it).
/// The dual long-step (BFRT) select phase sorts `self.bp: Vec<(f64,u32)>` by the
/// ratio with `sort_unstable_by(|x,y| x.0.total_cmp(&y.0))`. Every ratio is
/// `(d[j]/a).abs()` — non-negative, finite, never NaN and never `-0.0` (`a` is
/// `> pivot_tol`, `d[j]` finite; `.abs()` yields `+0.0` or positive). Over that
/// domain `f64::total_cmp` is BITWISE-EQUIVALENT to comparing `to_bits()` as `u64`
/// (positive IEEE-754 floats are monotone in their bit pattern, and `total_cmp`'s
/// sign-flip XOR is a no-op when the sign bit is clear). So `sort_unstable_by_key`
/// on `x.0.to_bits()` yields the IDENTICAL comparison result for EVERY pair pdqsort
/// evaluates — hence pdqsort makes the IDENTICAL branch/swap decisions and emits the
/// byte-identical permutation INCLUDING the arrangement of equal-ratio ties (the u32
/// column rides along untouched). The walk, flip set, stop breakpoint and Harris
/// band that read the sorted `bp` are therefore unchanged: byte-identical pivot
/// stream. The only difference is the comparator drops `total_cmp`'s two conditional
/// sign-flip XORs (dead for our non-negative keys) for a bare `u64` compare.
fn rt_bits_key_enabled() -> bool {
    // B12: caller-layer switch; the never-set AY_MILP_NO_RT_BITS_KEY env read is gone.
    !crate::tune::on(crate::tune::Knob::NoRtBitsKey)
}
/// Sparse DSE τ = B⁻¹ρ solve (OPT-IN, `AY_MILP_TAU_NZ`; default dense). The
/// steepest-edge weight update needs τ = B⁻¹ρ, where ρ = B⁻ᵀe_r is the pivot row
/// (support `ynz`, from the same-iter BTRAN). `ftran_nz` (Gilbert–Peierls) prunes
/// to ρ's reachable pattern and is BYTE-IDENTICAL to the dense `ftran` (same
/// L/eta/U ops, same order, zeros skipped). MEASURED A DEAD-END: on the network
/// bases this program targets, ρ's reachable closure is near-dense (the LU-fill
/// arm's "B⁻¹ 54% dense" result), so the DFS + two reach-sorts cost MORE than the
/// flat dense sweep they replace — qiu tau 4.44→6.67us, air05 tau 7.57→20.1us.
/// Kept behind the flag (byte-identical, harmless) to spare a future arm the
/// re-derivation; the default stays dense.
fn tau_nz_enabled() -> bool {
    static B: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *B.get_or_init(|| false)
}
/// Sparse flip-aggregate solve wflip = B⁻¹·Σδ. The dual long-step commits a
/// flip SET whose aggregate column movement is solved against the OLD basis.
/// `ftran_nz` (Gilbert–Peierls) is BYTE-IDENTICAL to the dense `ftran` (same
/// L/eta/U ops in the same order, structural zeros skipped; the input support
/// may carry duplicates harmlessly, as `ftran_nz` zeroes each input row after
/// reading it, so a repeat gathers `+= 0.0`) — the dual bound is bit-for-bit
/// unchanged (air05 25941 either way).
///
/// On the near-dense network/set-partition bases this program targets the
/// sparse arm LOSES — exactly like the DSE τ solve (see `tau_nz_enabled`):
/// on air05's ~54%-dense B⁻¹ even a tiny RHS closes near-dense through
/// Gilbert–Peierls, so the symbolic DFS + two O(m) count-sorts cost MORE than
/// the flat dense sweep they replace (air05 flip 5.0→11.4us, 2.3× slower).
/// B19: the opt-in env lever is retired; the arm is AUTO-DECIDED per commit
/// by the same predicted-marked-set test the FT spike build proved out
/// (`est·(m+unnz)·2 < m·m`, dense on ties so air05-class bases are
/// unchanged), with `--flip-solve=<auto|sparse|dense>` as the typed override.
/// The uccase12/physiciansched6-2 sparse-basis A/B is still QUEUED — the
/// auto arm has not yet been measured at this fork.
fn flip_solve_mode() -> usize {
    // 0 = auto, 1 = sparse, 2 = dense.
    crate::tune::count_opt(crate::tune::Knob::FlipSolve).unwrap_or(0)
}
/// STAGE B opt-in (`AY_MILP_FUSED_RT_DEFER`, requires `AY_MILP_FUSED_RT`). Deferring
/// `self.bp` on the no-flip step turned out to be a WASH-to-LOSS: a Vec push is cheap
/// next to the per-column division, so skipping pushes saves little, while a genuine
/// long step must RE-SCAN (a second O(cols) division pass) — measured net-negative on
/// rout (24% long steps: ratio-test 3.24us→3.41us) and marginal elsewhere. Stage A
/// (the min-scan fold) is the real, uniform win, so `AY_MILP_FUSED_RT` ships Stage A
/// alone; this flag keeps the deferral available for A/B. Byte-identical either way.
fn fused_defer_enabled() -> bool {
    static B: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *B.get_or_init(|| false)
}
/// Kill switch for the WIDE-AND-TALL warm-dual divergence-guard relaxation (see the
/// `bloom_cap` note in `dual_simplex`): restores the `(4·entry_viol).max(64)` cap so
/// a wide set-partitioning node re-solve bloom-aborts and falls back to the cold
/// re-crash byte-for-byte.
fn no_wide_bloom() -> bool {
    // B12: caller-layer switch; the never-set AY_MILP_NO_WIDE_BLOOM env read is gone.
    crate::tune::on(crate::tune::Knob::NoWideBloom)
}

/// Kill switch for the TALL-DEGENERATE bloom-cap relaxation (the tall_lu arm of
/// the `bloom_cap` match). `no_wide_bloom` already lifts the divergence guard on
/// the WIDE set-partition class (`wide_tall`); this extends the SAME lift to the
/// TALL-degenerate class (`tall_lu`, m ≥ 1,000 — qiu's capacity==demand network,
/// whose warm dual is 83–88% degenerate-θ≈0 and CONVERGES, but blooms a few
/// hundred violated rows on the way and gets aborted at `(4·entry_viol).max(64)`
/// into a wasteful cold primal re-solve). Setting `--no-bloom-relax`
/// restores the `wide_tall`-only uncap, so a tall_lu warm-dual walk bloom-aborts
/// byte-for-byte. Verdict-neutral either way (only the float pivot SEQUENCE and
/// thus the walk length change; every exit is re-checked, every leaf re-derived
/// exactly — `safe_bound` is rigorous for ANY float duals).
///
/// The process-wide `OnceLock` cache this used to hold is gone, and its
/// removal is the point rather than a side effect: caching the first read made
/// the switch per-*process*, so an in-process consumer could not disable the
/// relaxation for one solve and keep it for another. `tune` resolves the
/// caller's per-solve setting first and the environment from a snapshot taken
/// once, so the environment read the cache was avoiding does not happen here
/// either way.
fn no_bloom_relax() -> bool {
    crate::tune::on(crate::tune::Knob::NoBloomRelax)
}
/// DUAL COST PERTURBATION (anti-degeneracy). The qiu class (`tall_lu`, a
/// capacity==demand network) runs warm-child dual walks that are ~80% DUAL
/// degenerate (θ≈0 pivots — the entering column's reduced cost is already ≈0,
/// so the dual objective does not move and the basis churns). The tie source is
/// the DUAL RATIO TEST: many nonbasic columns sit at reduced cost exactly 0, so
/// the minimum ratio |d_j/a_j| is 0 and every such pivot is θ≈0. The textbook
/// fix (Wolfe / EXPAND) is to perturb the costs so no reduced cost sits exactly
/// at 0: the ratio test then has a strictly positive minimum and the walk makes
/// monotone progress instead of cycling on the degenerate face.
///
/// The perturbation is applied ONLY to the entry-nonbasic columns and ORIENTED
/// into dual feasibility (a column resting at its lower bound needs d_j ≥ 0, so
/// its cost is nudged UP; at upper, DOWN). Because basic costs are untouched the
/// duals y = c_B B⁻¹ are unchanged, so every nonbasic reduced cost shifts by
/// exactly its own δ_j and the warm start stays dual-feasible for the perturbed
/// costs c' = c + δ — the walk is a valid dual simplex on a fixed, well-defined
/// LP. The magnitude (`dual_perturb_mag`, ~1e-8·frame) is far below the
/// `priced_out` acceptance tolerance (`DUAL_ACCEPT_TOL`, 1e-7), so the
/// perturbed optimum still prices out against the TRUE costs after restore — no
/// wasted rollback. Float-advisory only: the costs are restored bit-exactly on
/// exit and every node bound is re-derived by `safe_bound` in exact rationals.
///
/// MEASURED A DEAD END ON qiu (2026-07-20; default 0.0 = OFF, byte-identical to
/// the un-perturbed walk). It works AS DESIGNED — the `opt`-exit walks' θ≈0
/// fraction dropped 76%→36% at mag 1e-8 — but it does NOT cut the pivot count.
/// qiu's θ≈0 pivots are PRIMAL-PRODUCTIVE: the dual objective sits flat on an
/// optimal FACE while the pivots drive the primal toward feasibility (step0=0%,
/// so none are true stall pivots). Removing the dual degeneracy therefore only
/// re-labels those pivots (θ small-but-nonzero) without removing them, and it
/// LENGTHENS the Farkas/`noenter` infeasibility proofs (109→124–172 pivots/walk
/// across mags 1e-10…3e-9) because the shifted reduced costs delay the
/// no-entering-column verdict. qiu's pivot count is a primal CASCADE (churn),
/// not dual-degeneracy cycling — so this lever is the wrong tool for it. Kept
/// behind the opt-in flag (sound, gated) to spare a future arm the re-derivation.
fn dual_perturb_mag() -> f64 {
    static M: std::sync::OnceLock<f64> = std::sync::OnceLock::new();
    // DEFAULT 0.0 = OFF. Opt in with `--dual-perturb` (e.g. 1e-8).
    *M.get_or_init(|| crate::tune::real_opt(crate::tune::Knob::DualPerturb).unwrap_or(0.0))
}
/// Kill switch for the dual cost perturbation (`AY_MILP_NO_DUAL_PERTURB`);
/// restores the un-perturbed warm/cold dual walk byte-for-byte for A/B.
fn no_dual_perturb() -> bool {
    static B: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *B.get_or_init(|| false)
}
/// Width factor of the dual anti-churn Harris band, in units of `cost_tol`
/// (`AY_MILP_CHURN_BAND`, default 0.5 — the shipped value). A WIDER band lets the
/// ratio test reach past the min-ratio breakpoint to a LARGER pivot magnitude,
/// which reduces the churn a small pivot kicks onto other basics (`(xb−t)/piv`),
/// at the cost of leaving the passed-over columns' reduced costs wrong-signed by
/// up to `band·|a_j|` — sound only while that stays inside the `priced_out`
/// acceptance tolerance (`DUAL_ACCEPT_TOL`, 1e-7). Only fires on `dual_churn_band`
/// shapes (qiu / air05). WALK-CHANGING — re-cert on any non-default value.
fn churn_band_factor() -> f64 {
    // B6: the AY_MILP_CHURN_BAND env override is deleted; 0.5 is the shipped,
    // WALK-CHANGING-if-touched value (re-cert on any change).
    0.5
}
/// Historical force-everywhere lever for the LU / Forrest-Tomlin engine.
/// RETIRED: the LU engine auto-engages by shape (`warm_lu_enabled` &&
/// `wide_tall`/`tall_lu`, plus the node/cold-root LU knobs), and the force
/// lever's producer never survived the B38 CLI migration — the read here was
/// an env name nothing sets, i.e. constant `false`. Kept as a function so
/// the six decision sites keep their shape; a future measurement arm can
/// force LU everywhere again by editing this constant or adding a typed
/// carrier (the phase-2 flag table's "keep-override-only" verdict).
fn lu_enabled() -> bool {
    false
}

/// Kill switch for CROSS-SOLVE ETA REUSE (see `warm_start`): `AY_MILP_NO_ETA_REUSE`
/// restores the unconditional per-warm-solve rebuild for A/B.
fn no_eta_reuse() -> bool {
    // B12: caller-layer switch; the never-set AY_MILP_NO_ETA_REUSE env read is gone.
    crate::tune::on(crate::tune::Knob::NoEtaReuse)
}

/// Warm solves whose eta rebuild the cross-solve reuse skipped (trace).
pub(crate) static ETA_REUSE_COUNT: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
fn no_devex() -> bool {
    // B12: caller-layer switch; the never-set AY_MILP_NO_DEVEX env read is gone.
    crate::tune::on(crate::tune::Knob::NoDevex)
}
/// Per-phase iteration-economics lines (`LPSTAT phase...`) on stderr. Diagnostic only.
fn lp_stats_enabled() -> bool {
    static B: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *B.get_or_init(|| crate::tune::caller_flag(crate::tune::Knob::LpStats) == Some(true))
}
/// Kill switch for the COLD dual-simplex start on wide-and-tall LPs (A/B lever).
fn no_cold_dual() -> bool {
    // B12: caller-layer switch; the never-set AY_MILP_NO_COLD_DUAL env read is gone.
    crate::tune::on(crate::tune::Knob::NoColdDual)
}

/// Measurement arm: try the cold dual start on EVERY shape, not just `wide_tall`.
/// Default off, so the shipped path is byte-identical. See the call site for why.
fn cold_dual_all() -> bool {
    static B: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *B.get_or_init(|| crate::tune::caller_flag(crate::tune::Knob::ColdDualAll) == Some(true))
}
/// Kill switch for the triangular equality crash on big cold LPs (A/B lever).
fn no_tri_crash() -> bool {
    // B12: caller-layer switch; the never-set AY_MILP_NO_TRI_CRASH env read is gone.
    crate::tune::on(crate::tune::Knob::NoTriCrash)
}
/// Force the triangular crash regardless of size (tests / small-LP A/B).
fn force_tri_crash() -> bool {
    static B: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *B.get_or_init(|| crate::tune::caller_flag(crate::tune::Knob::TriCrashAll) == Some(true))
}
/// Parse the historical range-logical crash environment opt-in.
///
/// Exact `"1"` only: malformed or merely truthy-looking values remain off.
#[cfg(test)]
fn range_logical_crash_env_value(value: Option<&str>) -> bool {
    value == Some("1")
}

/// Admit a fully peeled equality block even when bounded-range rows are the
/// majority. The range rows retain their own logicals in the crash basis.
///
/// Exact `"1"` only: this is a default-off measurement lever, not a new
/// production policy.
fn range_logical_crash_env_enabled() -> bool {
    // B22: the env spelling is retired; the typed per-session carrier
    // (SolveOpts::with_range_logical_triangular_crash) is the override.
    false
}

/// Kill switch for the CHAIN-SHAPE class gate (`FloatLp::chain_shape`):
/// `--no-chain-shape` restores the pure size gate byte-for-byte.
fn chain_shape_enabled() -> bool {
    // B29: typed carrier; per-solve, so the process-wide latch is gone too.
    crate::tune::caller_flag(crate::tune::Knob::NoChainShape).map_or(true, |no| !no)
}
/// `--shape-census` + trace: print the peel census for every LP that
/// reaches a cold eta-path solve, even when the candidate pre-filter fails
/// (diagnostic only; never changes the verdict).
fn shape_census_enabled() -> bool {
    static B: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *B.get_or_init(|| crate::debug_flags::milp_debug_flags().shape_census)
}
/// Chain-shape Devex reach (`AY_MILP_CHAIN_DEVEX`): `0` = chain never drives
/// Devex, `1` = every primal walk on a chain LP, unset = COLD walks only
/// (default). The cold walks are where Dantzig dies (k=546 root: Stopped at
/// its 46s budget vs Optimal 3.7s); the warm node repairs are ~30-50-iteration
/// walks where all-walks Devex was measured certification-LOSING on k=124
/// (dual postchk fails 114 -> 410, rim 0 -> 77.7s, unknown @592s vs unsat
/// 222s off — the drifted walks fall into the exact rim).
fn chain_devex_mode() -> u8 {
    // B12: caller-layer value (0 | 1 | 2, builder-validated); the never-set
    // AY_MILP_CHAIN_DEVEX env read is gone. Out-of-domain reads as the
    // default, exactly as the env parse did.
    match crate::tune::count_opt(crate::tune::Knob::ChainDevex) {
        Some(m @ (0 | 1)) => m as u8,
        _ => 2,
    }
}
/// `--no-chain-preorder`: the chain verdict stops driving the
/// `refactorize` peel preorder (A/B lever; default on).
fn chain_preorder() -> bool {
    crate::tune::caller_flag(crate::tune::Knob::NoChainPreorder).map_or(true, |no| !no)
}
/// The DISTRESS PROBE budget (primal iterations) for cold eta-path walks on a
/// chain-ARMED LP (`chain_shape == 3`): a walk that has not settled inside the
/// budget is declared distressed — the bundle arms and the solve retries. The
/// healthy walks of this class settle in a few thousand iterations (k=124:
/// 4,953 the largest cold walk anywhere in its certified 48,123-node run;
/// k=63: 3,400), while the k=546 grind runs >100,000 iterations into its
/// Stopped deadline slice without converging — the order-of-magnitude gap
/// makes the threshold safe. `0` disables the probe (armed LPs never promote:
/// measurement / kill lever `the chain-probe knob`).
fn chain_probe_iters() -> u64 {
    static N: std::sync::OnceLock<u64> = std::sync::OnceLock::new();
    *N.get_or_init(|| {
        crate::tune::count_opt(crate::tune::Knob::ChainProbe)
            .map(|n| n as u64)
            .unwrap_or(20_000)
    })
}

/// Resolve the typed LP-local chain-probe budget before consulting the
/// historical process policy. Keeping the fallback lazy means a configured LP
/// is independent of process-global environment.
fn resolve_chain_distress_probe_iters(typed: Option<u64>, historical: impl FnOnce() -> u64) -> u64 {
    typed.unwrap_or_else(historical)
}
/// Kill switch for the BUMP LU base factor inside `refactorize` (A/B lever).
fn no_bump_lu() -> bool {
    crate::tune::caller_flag(crate::tune::Knob::NoBumpLu) == Some(true)
}
/// `AY_MILP_NO_FILL_TRIP=1`: restore the pure column floor, byte-for-byte.
///
/// The A/B arm for `Simplex::maybe_trip_bump_fill`. Per the repo rule a shipped
/// optimisation keeps a switch that restores prior behaviour exactly; with this
/// set the latch never arms, so `bump_active` reduces to
/// `!forced.is_empty() && peel_nb >= bump_lu_min()` — the historical expression.
/// The (biased, provisional) fill-rate trip opt-in — B22: env spelling retired.
/// Unset, `maybe_trip_bump_fill` returns immediately and the lane is the historical
/// column floor byte-for-byte. See that function for why this is not on by default.
fn fill_trip_optin() -> bool {
    // B22: retired env spelling (never set); the fill-trip lane stays off.
    false
}
fn no_fill_trip() -> bool {
    // B22: retired with its opt-in lane.
    false
}
/// `the bump-btf knob`: route the bump base factor through the BLOCK-TRIANGULAR
/// lane (lane 2) instead of the monolithic Markowitz LU (lane 1). Opt-in until
/// proven: unset, `refactorize` is byte-identical to before. The bump decomposes
/// near-triangularly (a few small SCC blocks + ~20k singletons), so factoring
/// only the diagonal SCC blocks — off-diagonals riding as L content — drops fill
/// from the monolithic ~47M toward O(bump nnz), the full-depth FTRAN-cost lever.
fn bump_btf_env() -> bool {
    static B: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *B.get_or_init(|| crate::tune::caller_flag(crate::tune::Knob::BumpBtf) == Some(true))
}
/// Bump-size floor for the LU base factor in `refactorize`: below it the PFI
/// segment stays (small bumps rebuild near-zero-fill anyway — the crash-walk
/// bases run 130-160 bump columns; the mid-walk SCC runs ~10.2k). Measurement
/// lever `the bump-lu-min knob`.
fn bump_lu_min() -> usize {
    static N: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *N.get_or_init(|| crate::tune::count_opt(crate::tune::Knob::BumpLuMin).unwrap_or(512))
}
/// `--bump-diag`: per-rebuild peel-segment anatomy lines (entry and
/// time split across fronts / bump / backs). Diagnostic only.
fn bump_diag_enabled() -> bool {
    static B: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *B.get_or_init(|| crate::tune::caller_flag(crate::tune::Knob::BumpDiag) == Some(true))
}
/// Kill switch for the objective-cutoff early stop in the warm dual walk (A/B lever).
fn no_cutoff() -> bool {
    // B12: caller-layer switch; the never-set AY_MILP_NO_CUTOFF env read is gone.
    crate::tune::on(crate::tune::Knob::NoCutoff)
}
/// Kill switch for the WARM-solve LU engine on wide-tall `plain_cold` instances
/// (A/B lever). See the gate in `solve_bounded`: node re-solves on a set-partition
/// LP grind on the eta inverse's drift; the LU engine's accuracy repays itself in
/// far fewer pivots (the same reason `try_cold_dual` installs one at the root).
fn no_node_lu() -> bool {
    // B12: caller-layer switch; the never-set AY_MILP_NO_NODE_LU env read is gone.
    crate::tune::on(crate::tune::Knob::NoNodeLu)
}

/// Kill switch for the TALL LU gate (`FloatLp::tall_lu`; A/B lever).
fn no_tall_lu() -> bool {
    // B12: caller-layer switch; the never-set AY_MILP_NO_TALL_LU env read is gone.
    crate::tune::on(crate::tune::Knob::NoTallLu)
}

/// Kill switch for the COLD-ROOT LU band (`FloatLp::cold_root_lu`): restores the
/// historical `plain_cold` eta-file cold root byte-for-byte. This is the A/B
/// lever the band's measurements were taken against — NEVER delete it.
///
/// Resolved through `tune`, so it is a PER-SOLVE decision reached from
/// [`EngineEconomics::with_cold_root_lu`]. It was a process-global `OnceLock`
/// over `--no-cold-lu`, which is precisely why it could not be one: the
/// first solve in a process latched the lane for every later solve, and a
/// consumer forbidden from exporting `AY_MILP_*` could not reach it at all.
fn no_cold_lu() -> bool {
    crate::tune::on(crate::tune::Knob::NoColdLu)
}

/// Row floor of the cold-root LU band (formerly `AY_MILP_COLD_LU_ROWS`).
///
/// 3 000, not `TALL_LU_ROWS` (1 000): the measured crossover is between
/// binkar10_1 (m = 2 298, mixed: better incumbent, fewer nodes, no clear win)
/// and nursesched-sprint02 (m = 3 522, 3.5× pivots/s and a bound that did not
/// exist). Under the floor the eta rebuild is cheap enough that the FT engine's
/// per-pivot cost is pure loss — and it MOVES THE VERTEX, which is how the
/// force-lever A/B turned air05's proven bound into a bare incumbent. The floor
/// is deliberately NOT tuned any finer than that: on a contended box the
/// deadline-truncated instances between 1 000 and 3 000 rows swing more from
/// machine load than from the lane (air05, same arm, four runs: 374/374/374 vs
/// 2 340 eta rebuilds). See `FloatLp::cold_root_lu` for the table.
/// A floor of zero would silently open the band to every in-band `plain_cold`
/// solve. That is sound but measurably costs verdicts (gt2 and qiu both fall
/// OPTIMAL -> FEASIBLE, timtab1 loses its incumbent), because under the floor
/// the FT engine's per-pivot cost is pure loss and it moves the vertex. B25
/// retired the value override, leaving the compiled floor as the sole value;
/// edit `COLD_LU_MIN_ROWS` to repeat the measurement. Use the separate
/// `--no-cold-lu` kill switch to turn the band off.
fn cold_lu_min_rows() -> usize {
    // B25: env override retired; the named constant is the value.
    COLD_LU_MIN_ROWS
}

/// Row ceiling of the cold-root LU band (formerly `AY_MILP_COLD_LU_MAX_ROWS`), default
/// `REFACTOR_TALL_ROWS`. Above it `LuEngine::update`'s O(m) dense sweeps replace
/// the refactorisation wall rather than removing it (measured 1.85 ms/update at
/// m = 40 962, 3.57 ms at m = 69 608 — 23–34 % of LP time); raise it to re-run
/// that experiment after `lu.rs::update` is sparsified.
///
/// THAT EXPERIMENT HAS NOW BEEN RUN, AND THE CEILING STAYS AT 8 192.
/// `LuEngine::update_nz` sparsified the spike build (5.31x per update on
/// uccase12, 1.71x on physiciansched6-2 — see `SPIKE_SPARSE_MARGIN`), and the
/// four above-ceiling models that emit no dual bound were re-run at 400 s with
/// the ceiling at 400 000, in three arms: shipped, raised+dense, raised+sparse.
///
/// ```text
///   model              root LP bound: shipped ->   raised+dense ->  raised+sparse
///   ex9                        19.169281        62.120038         53.301826
///   ex10                       11.689389        14.782647         14.480692
///   uccase12                44578.338559     66344.077189      76226.248267
///   physiciansched6-2       13070.500000     13070.500000      13070.500000
/// ```
///
/// The partial root bound gets much tighter (uccase12 +71 %, ex9 3.2x) — but
/// the root LP is `Stopped` in EVERY arm, no rigorous tree bound is emitted in
/// any of them, and the verdict is `UNKNOWN` 4/4 throughout. Zero verdicts
/// gained. Meanwhile the raise would move the seeding vertex for all 106
/// above-ceiling corpus models, so it is a large blast radius bought with no
/// measured verdict.
///
/// The reason is that `update` was never the binding constraint up there. With
/// the sparse arm, uccase12's update is 13.57 s of a ~398 s solve (3 %), and
/// the LP still does not converge. Its cost has moved to BTRAN: 171 780 calls
/// at avg_reach 53 583 of m = 121 161 (44 % dense) ≈ 9.2e9 slot touches, and
/// `btran` is untouched by the spike work. That — not the ceiling — is the
/// next lever for this class.
fn cold_lu_max_rows() -> usize {
    // B25: env override retired; the named constant is the value.
    REFACTOR_TALL_ROWS
}

/// LATE LU PROMOTION BUDGET: how many eta rebuilds ONE SOLVE may pay before
/// `refactorize` switches it to the Forrest–Tomlin engine. `0` (the default)
/// disables the lane. Promotion additionally requires `FloatLp::tall_lu()` and
/// `!FloatLp::cold_root_lu()` — see "Why there is still a row floor" below.
///
/// # Why the row band needed a companion, and why this is not another row rule
///
/// The shipped band `[COLD_LU_MIN_ROWS, REFACTOR_TALL_ROWS)` is keyed on `m`,
/// and `m` does not predict what the FT engine costs. Measured over 39 corpus
/// models (`--lu`, 60 s, deterministic `LU_FTRAN_REACH`/`LUFACT`
/// counters), Spearman against ns per FT update per row:
///
/// ```text
///   spike density (LU_FTRAN_REACH / m)   0.841
///   factor fill   (LUFACT avg_nnz / m)   0.598
///   m                                   -0.045   <-- the band's own variable
///   m  vs. spike density                -0.429   <-- and BACKWARDS: bigger m, SPARSER spikes
/// ```
///
/// uccase12 (m = 121 161, spike 0.0004) costs 0.56 ns/update/row; ex9
/// (m = 40 962, spike 0.57) costs 39.50 — 70x more per row at a THIRD of the
/// rows. So the ceiling excludes the cheapest models in the corpus and the
/// floor excludes the downstream optimization consumer's entire sub-3 000-row mip-diff corpus.
///
/// # Why the trigger is the eta rebuild count and not the spike density
///
/// It has to be. Spike density is a property of `B^{-1}` UNDER THE FT ENGINE:
/// `LU_FTRAN_REACH` only exists once the LU lane is running. A solve on the eta
/// file has no reach to read, so the quantity that best predicts FT cost is
/// exactly the one a promotion trigger cannot observe. (A 5 s prefix predicts
/// the full-solve spike density well — Spearman 0.943, N = 38 — but only from
/// inside the LU arm, so it can inform a DEMOTION, never this promotion.)
///
/// Statically it is no better: over the same 39 models, out-of-sample on 1 000
/// random 2/3-1/3 splits, no MPS-derived feature predicts spike density at all
/// (best mean R2 = +0.018, for raw density; `m` alone is -0.090, i.e. worse
/// than predicting the corpus mean). Even a Gilbert-Peierls symbolic FTRAN
/// reach computed on the greedy triangular CRASH basis — literally this
/// quantity with the crash basis substituted for the optimal one — classifies
/// dense-vs-sparse worse (AUC 0.621) than the ratio `n/m` (0.755). The crash
/// basis does not carry the optimal basis's fill.
///
/// What IS observable from the eta lane is the thing the band was actually
/// buying. The band's +6 verdicts came from the O(m*nnz) refactorisation bill
/// it REMOVES, not from cheap FT updates: in-band, 89 220 -> 21 264 eta
/// rebuilds and 861.2 s -> 99.3 s of REFAC. Rebuilds are countable while they
/// are being paid, so this lane counts them.
///
/// # Why a plain COUNT, after three better-looking units failed
///
/// Wall time is not deterministic and this decision changes the pivot sequence,
/// hence the vertex, hence the tree — a load-dependent trigger would make node
/// counts irreproducible. So the unit must be a counter, and the obvious move is
/// a counter that estimates the rebuild's COST. Three were tried against the
/// eta-arm census (14 models, `REFAC count`/`time`, plus per-rebuild traces) and
/// all three rank the real cost BACKWARDS:
///
/// ```text
///   unit          contradiction
///   m * nnz       aflow40b charges 19x LESS than drayage-100-23 and takes 1.35x
///                 MORE time; cvs16r70-62 charges a seventh of drayage and takes 43x
///   entries + m   uccase12 rebuilds 11 200 entries in 0.17 s; ex9 rebuilds 605 154
///                 — 54x the fill — in 0.05 s, 3.4x FASTER
///   m             drayage 0.12 us/row vs nursesched-sprint02 13.7 us/row, a 114x
///                 spread at nearly equal m (4 630 vs 3 522)
/// ```
///
/// The pattern is the one this whole investigation keeps returning: what a
/// rebuild costs is a property of the BASIS it is rebuilding, and no function of
/// the model or of the file's size recovers it. Only the clock does, and the
/// clock is disqualified.
///
/// So the trigger stops trying to size the bill. It does not need to. The FT
/// engine's entire proposition is to replace N rebuilds with one factorisation
/// plus N updates, so the rebuild COUNT is precisely the multiplier on whatever
/// the per-event difference turns out to be — and that difference is measured
/// FAVOURABLE on 13 of 14 paired models (median 9.97x, min 0.82x). A count
/// threshold therefore fires exactly when the trade is taken often enough to
/// matter, without needing to know how much each one is worth.
///
/// # Why there is still a row floor, and why it is `tall_lu()` and not 3 000
///
/// A count alone would promote gt2 (m = 29) and air05 (m = 426), which rebuild
/// thousands of times for microseconds each. That is measured harmful, not
/// merely pointless: setting the band's floor to 0 turned air05's PROVEN bound
/// into a bare incumbent and dropped gt2 and qiu from OPTIMAL to FEASIBLE. So
/// promotion reuses `tall_lu()` (m >= `TALL_LU_ROWS`), which is already this
/// crate's line for "the FT engine is the trusted operator on this shape" — the
/// same reuse-one-boundary argument that put the band's ceiling at
/// `REFACTOR_TALL_ROWS` rather than inventing a second number.
///
/// The band's own range is excluded outright (`!cold_root_lu()`), because the
/// in-band models still run eta-lane solves that rebuild hard enough to clear
/// any budget — per-solve maxima of 839 (drayage-100-23), 524 (cvs16r89-60),
/// 385 (cvs16r70-62), 299 (nursesched-sprint02) at the shipped default. Letting
/// the count reach those would move trees the band already owns, so this lane is
/// confined to the two ranges the band leaves unserved.
///
/// # MEASURED, AND IT DOES NOT WIN — WHICH IS WHY THE DEFAULT IS 0
///
/// 52 models, 60 s, 5 concurrent, ONE frozen binary, both arms (unset vs
/// `=20`). The mechanism does exactly what it was built to do:
///
/// ```text
///   over the 18 promoted models:  eta rebuilds 29 338 -> 2 383   (12.3x)
///                                 REFAC time      271.3s -> 59.7s
///   uccase12   68 -> 35 rebuilds     atlanta-ip 525 -> 40
///   app1-2    277 -> 60              comp21-2idx 588 -> 123
///   opm2-z10-s4 159 -> 54            neos-827175 195 -> 60
///   root LP Stopped -> Optimal: 1 (neos-4722843-widden)
/// ```
///
/// And the verdict ledger is NET NEGATIVE: +3 gained (air05, seymour1,
/// neos-4722843-widden), -6 lost (nursesched-sprint02, neos-960392,
/// hypothyroid-k1, glass-sc, decomp2, comp21-2idx). Zero `ref_obj`
/// disagreements — the losses are tightness and throughput, never a wrong
/// answer, exactly as the advice-lane contract promises.
///
/// THE REASON IS THE FINDING THAT STARTED ALL OF THIS, now visible at the
/// decision itself. The promotion buys down the rebuild bill and pays an FT
/// UPDATE bill, and the update bill is set by spike density — which the trigger
/// cannot see. Measured `LU_FTRAN_REACH`/m and ns/update in the promoted arm:
///
/// ```text
///   uccase12           0.1% dense      71 690 ns/update   cheap, as predicted
///   physiciansched6-2  2.5%           470 773
///   aflow40b           5.6%             5 327
///   ex9               67.6%         4 787 213   <-- 4.8 ms PER UPDATE
///   ex10              57.1%         4 646 100
///   cvs16r70-62       74.5%            47 240
/// ```
///
/// On the dense-spike models the trade is a loss, and their partial root bounds
/// get WORSE for it (ex9 7.459 -> 6.218, ex10 4.748 -> 3.862, atlanta-ip
/// 2522.74 -> 1998.49, uccase12 -0.840 -> -1.355). A rebuild-count trigger fires
/// on rebuild PRESSURE, which both classes have, and is blind to the one
/// quantity that decides whether relieving it pays.
///
/// So this is kept as a measured ARM, not promoted. Closing it needs the demotion
/// half: promote on pressure, then read the now-observable `LU_FTRAN_REACH`/m and
/// fall BACK to the eta file when the spike turns out dense. The mechanism for
/// that already ships (`FactorFail::Singular` drops `self.lu` and rebuilds), and
/// the 5 s-prefix probe scores 0.943 Spearman against the full-solve density, so
/// the signal is there — it just does not exist until after the switch.
///
/// ⚠ THE VERDICT LEDGER ABOVE IS NOT SETTLED, AND THE ARMS THEMSELVES PROVE IT.
/// 17 of the 50 compared models moved their node counts WITHOUT EVER BEING
/// PROMOTED — `promotions=0`, no LU engine, the lane provably inert on them:
///
/// ```text
///   f2gap801600         27 094 -> 47 929 nodes    neos-3118745-obra 54 893 -> 73 023
///   timtab1            357 016 -> 238 324         neos-3611689-kaihu 58 004 -> 100 242
///   rout                14 843 -> 17 583          neos-3046615-murg 205 125 -> 199 394
/// ```
///
/// With the budget unset the promotion is unreachable, so these runs differ ONLY
/// in wall-clock truncation at the 60 s cap on a contended box — 30–70 % swings
/// from machine load alone, the same effect the band's floor note records (air05,
/// identical arm, four runs: 374/374/374 vs 2 340 rebuilds, 17 vs 35 nodes). So
/// the +3/-6 is within the noise this harness can resolve and must NOT be quoted
/// as the lane's cost. What IS safe to quote is the per-solve rebuild counts and
/// the reach/update census: those are deterministic, and they are what the
/// conclusion above actually rests on. A settled ledger needs an
/// uncontended box and a same-arm repeat control.
///
/// ⚠ THIS DOES NOT REACH the downstream optimization consumer's mip-diff CORPUS, which is the one thing the brief
/// hoped for. Those models are hundreds of rows, i.e. below `TALL_LU_ROWS`, and
/// nothing measured supports admitting them — the only evidence there is the
/// floor-of-0 experiment above, and it is negative. What this lane does open is
/// the range `[TALL_LU_ROWS, COLD_LU_MIN_ROWS)` and everything above the
/// ceiling, on demonstrated rebuild pressure rather than on row count.
fn cold_lu_eta_rebuilds() -> u32 {
    static N: std::sync::OnceLock<u32> = std::sync::OnceLock::new();
    *N.get_or_init(|| {
        crate::tune::count_opt(crate::tune::Knob::ColdLuEtaRebuilds)
            .and_then(|n| u32::try_from(n).ok())
            .unwrap_or(LATE_LU_ETA_REBUILDS)
    })
}

/// Default late-promotion budget. `0` = OFF; see `cold_lu_eta_rebuilds`.
const LATE_LU_ETA_REBUILDS: u32 = 0;

/// LU-LANE EXTENSION for `WarmSolver` (`--warm-lu`; A/B lever, DEFAULT
/// OFF). The pooled bound-change re-solver (the dive/flip-LNS loop) keeps its
/// `Simplex` — and, with this on, its LU operator — ALIVE across solves. On the
/// tall-LU class that is the largest single eta consumer on qiu: the census
/// (`LANEMAP`/`CALLERMAP`) charges ~88% of the O(m·nnz) eta rebuilds to
/// flip-LNS's `WarmSolver` eval loop, all on the eta lane because `Simplex::new`
/// installs no engine. With an engine, a re-solve whose basis is unchanged
/// since the last (the common case after a bound-only kick) gets the `rep_basis`
/// match-skip; the rest factor as LU instead of rebuilding the eta file.
///
/// DEFAULT OFF because it is a NUMERICS change on an INCUMBENT-FINDING lane: the
/// LU inverse is not bitwise the eta inverse, so it can move which LP vertex the
/// flip-LNS lands on and therefore which incumbent it rounds — the
/// vertex-seeding-family landmine. Only promote the default after the qiu
/// incumbent (−132.873) and the whole corpus's exact values are shown to hold.
/// Gated to `tall_lu` (below), so every square-ish/dense-ladder instance keeps
/// the eta path bit-for-bit whether the lever is on or off.
///
/// Per-solve, not per-process: see `no_bloom_relax` above for why the
/// first-read cache had to go with the move to `tune`.
pub(crate) fn warm_lu_enabled() -> bool {
    crate::tune::on(crate::tune::Knob::WarmLu)
}

/// Kill switch for the tall-LP extension of the dual anti-churn band (restores
/// the historical `wide_tall`-only gate). See `FloatLp::dual_churn_band`.
fn no_dual_churn_band() -> bool {
    // B12: caller-layer switch; the never-set AY_MILP_NO_DUAL_CHURN_BAND env read is gone.
    crate::tune::on(crate::tune::Knob::NoDualChurnBand)
}

/// Kill switch for the EQUILIBRATION-SAFE `noenter` Farkas shortcut (`run`'s
/// unscale-then-verify path). Set `AY_MILP_NO_NOENTER_UNSCALE` to restore the
/// historical `!lp.scaled()` gate — scaled solves then fall through to the
/// rollback + primal phase-1 re-proof, exactly as before this lever. A/B only;
/// the unscaled-frame shortcut is unaffected either way.
fn no_noenter_unscale() -> bool {
    static B: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *B.get_or_init(|| false)
}

/// Verify/skip staleness trigger when the FT LU ENGINE backs a TALL-class LP
/// (Lever A1; `AY_MILP_LU_VERIFY` overrides, `=20` restores the historical
/// behavior byte-for-byte). `VERIFY_AFTER = 20` was tuned for the product-form
/// eta file, whose per-update drift is what the "refactorize and re-ask"
/// verification exists to catch. The Forrest–Tomlin engine's updates are
/// growth-guarded (`lu.rs::FT_REL_PIVOT_TOL` rejects element growth past
/// ~1e12) and `REFACTOR_EVERY_TALL = 400` already trusts them for a full w5
/// cadence — yet on the ACAS diff-leaf class the 20-update trigger made the
/// ~39-pivot warm node solve pay a FULL base factor at its optimum on a basis
/// the engine represented exactly: 51,660 of 73,118 base factors in the k=124
/// certification run were d=0 stale-match rebuilds (~34s of 47.9s LUFACT +
/// a recompute_xb + a re-pricing pass each). Raising the trigger past
/// `refactor_every` (50 here) hands staleness control to the cadence rebuild,
/// which this class's solves stay under. Gated to `tall_lu` BELOW the
/// `REFACTOR_TALL_ROWS` band so the w5/cifar wide-tall regime and every
/// corpus/ladder instance keep their historical trajectory bit-identically.
fn lu_verify_after() -> usize {
    // B25: env override retired; the named cadence stands.
    64
}

/// Refactor CADENCE when the FT LU engine backs a tall-not-wide LP
/// (`AY_MILP_LU_REFACTOR`; measurement lever, default = the historical 50).
/// LANDMINE, measured on the k=124 ACAS certification: raising this to 128
/// (the "w5 trusts 400" argument) COLLAPSED the run — the class's degenerate
/// bases (genuine 1e-9 pivots) accumulate FT error much faster than w5's, the
/// drifted walks started failing their postchecks, and the failures cascaded
/// into the EXACT-RATIONAL rim: rim=203.7s (off: 0.0s), eta-arm REFAC 6.1K ->
/// 23.6K, certification lost (unknown @602s, was certified @326s). The LUFACT
/// saving it bought (47.9s -> 20.8s) was real and irrelevant. Cadence stays
/// 50; the trigger that IS safely relaxable on this class is the
/// end-of-solve verify (`lu_verify_after`).
///
/// 50 -> 20 (2026-08-11). NOTE THE DIRECTION: the landmine above is about RAISING
/// the cadence, which lets Forrest-Tomlin error accumulate across more updates.
/// LOWERING it refactors MORE often and therefore carries STRICTLY LESS FT drift,
/// so it sits on the safe side of that failure, not near it.
///
/// WHY. On qiu the eta UPDATE, not refactorisation, is the cost: `REFAC 1.44s` against
/// `LUSOLVE update 5.77s` over 460k calls at ~12.5us, with ftran `avg_reach 695` of
/// 1192 rows -- the basis LU runs 58% DENSE, so every extra eta makes every subsequent
/// solve dearer. Shortening the eta file attacks the dominant term directly:
///
/// ```text
///   cadence   qiu wall   nodes   LUSOLVE   avg_reach
///     100      33.259s   4133     6.27s      783
///      60      41.990s   7563     7.52s      723
///      50      34.985s   5752     5.81s      695   (old default)
///      40      27.996s   4155     4.36s      709
///      20      25.834s   4116     2.96s      622
/// ```
///
/// FULL CORPUS at 20, serial, idle, best-of-3 on misc07:
///
/// ```text
///   qiu    33.693 -> 25.279s  (-8.414s, 1.33x)   nodes 5782 -> 4120
///   15 of 17 instances keep BYTE-IDENTICAL node counts -- the change is INERT on them
///   only qiu and misc07 move at all, and misc07's nodes IMPROVE (7415 -> 7308)
///   every other delta is sub-50ms wall noise on an unchanged tree
///   TOTAL 93.220 -> 85.099s  (-8.121s, 8.7%)
/// ```
///
/// That inertness is what distinguishes this from the walk-changing knobs this file
/// has rejected. `the cut-warm knob` also showed a headline gain and was refused because
/// it moved REAL trees (blend2 3882 -> 5940 nodes, p0201 110 -> 798); Devex was 1.95x
/// on its target instance and +91.6s over fourteen. This one leaves fifteen trees
/// bit-for-bit alone.
///
/// The cadence sweep is NON-MONOTONE (60 is worse than both 40 and 100), so 20 is not
/// claimed as an optimum -- it is the best of {20,40,50,60,100} and the lowest value
/// tried. A finer sweep below 20, and a per-class cadence for the dense-LU regime
/// (qiu/qnet1/gen/khb05250 are 73.6% of the corpus gap by wall), are both open.
fn lu_refactor_every() -> usize {
    static N: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *N.get_or_init(|| 20)
}

/// FT-ADOPTION distance cap (Lever A2; `AY_MILP_ADOPT_FT` overrides, `=0`
/// kills). A warm adoption whose basis differs from the live LU operator in
/// `d <= cap` positions is absorbed as `d` Forrest–Tomlin updates (one sparse
/// FTRAN + `LuEngine::update` each) instead of a full base factor. Same
/// class gate as `lu_verify_after`.
/// Row CEILING for FT ADOPTION (`the adopt-ft-max-rows knob`), default
/// `REFACTOR_TALL_ROWS`.
///
/// # Why this override exists
///
/// The eligibility test below shared `REFACTOR_TALL_ROWS` with the cold-root LU
/// band, and — unlike that band, which has `AY_MILP_COLD_LU_MAX_ROWS` — it had **no
/// override at all**. The consequence is the one a gate audit flagged as its second
/// confirmed finding: *the doc's own measurement lever cannot reach the excluded
/// population.* **106 of 379 corpus instances sit above the ceiling**, and there was
/// no way to run any of them with adoption on, so the ceiling's premise could not be
/// checked even in principle.
///
/// This is the sibling of the cold-root LU band finding that paid **+6 verdicts**
/// once its lane was reachable.
///
/// The default is DELIBERATELY UNCHANGED. Making a gate measurable and moving it are
/// different acts, and the audit's recommendation was explicitly the first: an
/// unmeasurable gate must not be re-tuned by guess, which is how the original
/// size-gate defects were introduced.
fn adopt_ft_max_rows() -> usize {
    static N: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *N.get_or_init(|| {
        crate::tune::count_opt(crate::tune::Knob::AdoptFtMaxRows).unwrap_or(REFACTOR_TALL_ROWS)
    })
}

fn adopt_ft_max() -> usize {
    static N: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *N.get_or_init(|| 31)
}

/// Warm-dual bypass policy constants — see `FloatLp::warm_dual_should_attempt`.
const DUAL_BYPASS_MIN_ATTEMPTS: u32 = 32;
const DUAL_BYPASS_WIN_DEN: u32 = 8;
const DUAL_BYPASS_PROBE_EVERY: u32 = 64;
const DUAL_BYPASS_FORGET_AT: u32 = 512;

/// `--dual-bypass-mode`: `0` = never bypass (the old behavior), `2` = always
/// bypass warm duals (measurement lever), unset = 1 (adaptive, the default).
fn dual_bypass_mode() -> u8 {
    // B29: caller-layer value (0 never | 1 adaptive | 2 force,
    // builder-validated); out-of-domain reads as the default.
    match crate::tune::count_opt(crate::tune::Knob::DualBypassMode) {
        Some(m @ (0 | 2)) => m as u8,
        _ => 1,
    }
}

/// A/B override for the dual divergence guard's bloom cap
/// (`AY_MILP_DUAL_BLOOM_CAP`): an absolute violated-row cap replacing the
/// `max(4·entry, 64)` policy; `0` disables the guard entirely. Unset keeps the
/// default policy byte-identically.
fn dual_bloom_cap_override() -> Option<usize> {
    // B12: caller-layer value; the never-set AY_MILP_DUAL_BLOOM_CAP env read
    // is gone.
    crate::tune::count_opt(crate::tune::Knob::DualBloomCap)
}

/// Rebuild the product-form inverse every this many basis changes.
///
/// Size-gated: tall LPs default to the w5-measured 400. On the cifar100 w5
/// window (m = 18,692) the root LP took 1,738.7s at the MIPLIB-tuned 50 and
/// 620.9s at 400 with the same walk (23,909 vs 24,399 iterations) — the eta
/// rebuild is O(m·nnz), and at that height it was 78% of the run. The cadence
/// is trajectory-dependent (100 measured WORSE than either on w5), so the bump
/// is confined to the measured regime, m >= REFACTOR_TALL_ROWS; smaller models
/// keep 50 byte-identically. `the refactor-every knob` overrides both. A caller
/// with no LP in scope passes m = 0 for the conservative small-m policy.
/// The operator's `the refactor-every knob` override, or `None`.
///
/// Split out of [`refactor_every`] so it is NULLARY and therefore primeable. The
/// combined form cached its environment read behind a size argument, which meant
/// `prime_env` could not force it and its first `getenv` still landed at an
/// arbitrary point mid-solve — one of the two cached holes an independent review
/// identified after the priming pass. The size-dependent default is pure and needs
/// no caching, so separating the two costs nothing and closes the hole.
fn refactor_every_override() -> Option<usize> {
    static N: std::sync::OnceLock<Option<usize>> = std::sync::OnceLock::new();
    *N.get_or_init(|| crate::tune::count_opt(crate::tune::Knob::RefactorEvery))
}

fn refactor_every(m: usize) -> usize {
    refactor_every_override().unwrap_or(if m >= REFACTOR_TALL_ROWS {
        REFACTOR_EVERY_TALL
    } else {
        REFACTOR_EVERY
    })
}
const REFACTOR_EVERY: usize = 50;
/// See `refactor_every`: the w5-measured cadence for tall LPs, and its gate.
const REFACTOR_EVERY_TALL: usize = 400;
const REFACTOR_TALL_ROWS: usize = 8192;
/// Size gate for the BIG-LP float-kernel economies (blocked `btran`, the
/// triangular crash, the refactorize peel preorder): BOTH dimensions must be
/// large. Small-or-flat LPs — the whole ladder/corpus band, including the
/// 10,757-column/124-row air03 — keep their historical float paths
/// bit-for-bit (the 80x60 pace-window landmine); the cifar100 windows
/// (26.8k structurals × 18.7k rows) are far above both.
const BIG_LP_COLS: usize = 8192;
const BIG_LP_ROWS: usize = 8192;
/// Recompute basic values from scratch this often, to damp drift.
const REFRESH_EVERY: usize = 200;
/// Diagnostic counters -- what the search actually spends its simplex on. `--trace` prints
/// them; nothing else reads them.
pub(crate) mod stats {
    use std::sync::atomic::{AtomicU64, Ordering};
    pub(crate) static DUAL_ITERS: AtomicU64 = AtomicU64::new(0);
    pub(crate) static PRIMAL_ITERS: AtomicU64 = AtomicU64::new(0);
    /// Iteration ECONOMICS (diagnostic, `--lp-stats`): degenerate primal
    /// steps (ratio test blocked at zero), bound flips, and iterations that
    /// actually MOVED this phase's objective. Together with `PRIMAL_ITERS`
    /// they answer "is the walk moving or shuffling" — the air05 question.
    pub(crate) static PRIMAL_DEGEN: AtomicU64 = AtomicU64::new(0);
    pub(crate) static PRIMAL_FLIPS: AtomicU64 = AtomicU64::new(0);
    pub(crate) static PRIMAL_MOVED: AtomicU64 = AtomicU64::new(0);
    /// Dual pivots whose dual step `theta` was (near-)zero — dual-degenerate
    /// shuffles, the signature of duplicate-cost columns.
    pub(crate) static DUAL_DEGEN: AtomicU64 = AtomicU64::new(0);
    pub(crate) static REFACTORS: AtomicU64 = AtomicU64::new(0);
    pub(crate) static SOLVES: AtomicU64 = AtomicU64::new(0);
    pub(crate) static SOLVE_NANOS: AtomicU64 = AtomicU64::new(0);
    pub(crate) fn bump(c: &AtomicU64) {
        c.fetch_add(1, Ordering::Relaxed);
    }
    pub(crate) fn get(c: &AtomicU64) -> u64 {
        c.load(Ordering::Relaxed)
    }

    /// THE WORK CLOCK. Every simplex iteration this process has run, whoever asked for it.
    ///
    /// This exists to be spent INSTEAD OF wall-clock time. A budget denominated in seconds makes the
    /// search's decisions depend on how fast the machine happened to be running, and those decisions
    /// choose the branching, which chooses the tree -- so the same binary on the same input proves
    /// qnet1 in 16.7s on one run and not at all in 20s on the next. A budget denominated in
    /// iterations buys the same thing and is the same on every run.
    ///
    /// ⚠ DIAGNOSTICS ONLY. This is a PROCESS total and is never reset, so under an
    /// in-process consumer running concurrent solves it counts other solves' work
    /// as well. A *budget* must use [`solve_work`]; see its documentation for the
    /// defect that distinction fixes.
    pub(crate) fn work() -> u64 {
        get(&DUAL_ITERS) + get(&PRIMAL_ITERS)
    }

    thread_local! {
        /// Simplex iterations charged to the top-level solve running on this thread.
        ///
        /// Bumped at the same two sites as [`DUAL_ITERS`]/[`PRIMAL_ITERS`] and rebased
        /// by [`SolveWorkFrame`]. A `Cell<u64>` rather than an atomic: it is per-thread
        /// by construction, and a non-atomic increment is cheaper than the `fetch_add`
        /// beside it.
        static SOLVE_ITERS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
        /// Nesting depth of [`SolveWorkFrame`]. Only the OUTERMOST frame rebases: a
        /// sub-MIP (RINS/RENS/local branching) re-enters the solver on the same thread
        /// and must keep spending the enclosing solve's budget, not open a fresh one.
        static SOLVE_DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
    }

    /// Charge one iteration to the current solve. Paired with every `bump` of
    /// [`DUAL_ITERS`] / [`PRIMAL_ITERS`], which are the only two pivot loops.
    #[inline]
    pub(crate) fn bump_solve() {
        SOLVE_ITERS.with(|c| c.set(c.get().wrapping_add(1)));
    }

    /// THE BUDGET CLOCK. Simplex iterations spent by the current top-level solve on
    /// this thread.
    ///
    /// # The defect this exists to fix
    ///
    /// [`work()`] is a process-global `AtomicU64` pair that is never reset, and
    /// `bab.rs`'s strong-branching and bound-moving budgets were denominated in it
    /// under a comment claiming the resulting budgets are *"the same on every run, on
    /// every machine"*. That holds for a one-solve-per-process harness and fails for
    /// ay-milp's primary consumer: the development design notes §M1
    /// records a heavily multi-threaded verifier whose workers *"can be inside an ay
    /// solve while another thread configures the next one"*. There, solve A's
    /// strong-branching allowance grows with solves B..H's iterations — and strong
    /// branching chooses the branching, which chooses the tree.
    ///
    /// The wall→work conversion was itself a fix for machine-load dependence. It
    /// removed that dependence and substituted OTHER-SOLVE dependence; this removes
    /// the second without reintroducing the first.
    ///
    /// # Why per TOP-LEVEL solve
    ///
    /// A sub-MIP re-enters `solve_milp_*` on the same thread while its parent is live.
    /// Rebasing there would hand every sub-search a fresh full budget, which is a
    /// behaviour change on every instance that runs one. Only the outermost frame
    /// rebases, so a sub-MIP keeps drawing on the budget its parent has been spending.
    ///
    /// # Byte-identity
    ///
    /// On the one-solve-per-process measurement harness this is equal to [`work()`]
    /// at every read: the counter starts at zero, one thread bumps it, and nothing
    /// else runs. That is what makes the change free to validate against the corpus.
    pub(crate) fn solve_work() -> u64 {
        SOLVE_ITERS.with(std::cell::Cell::get)
    }

    /// Rebases [`solve_work`] for the duration of one TOP-LEVEL solve.
    ///
    /// `!Send` for the same reason `tune::Active` is: its `Drop` mutates a
    /// thread-local, so a guard created on one thread and dropped on another would
    /// restore the wrong thread's baseline.
    #[must_use = "the solve's work frame is active only while this guard is held"]
    pub(crate) struct SolveWorkFrame {
        /// The value to restore. `None` on a nested frame, which does nothing.
        restore: Option<u64>,
        _not_send: std::marker::PhantomData<*const ()>,
    }

    impl SolveWorkFrame {
        /// Enter a solve. Rebases only if this is the outermost frame on the thread.
        pub(crate) fn enter() -> Self {
            let outermost = SOLVE_DEPTH.with(|d| {
                let was = d.get();
                d.set(was.saturating_add(1));
                was == 0
            });
            let restore = outermost.then(|| SOLVE_ITERS.with(|c| c.replace(0)));
            Self {
                restore,
                _not_send: std::marker::PhantomData,
            }
        }
    }

    impl Drop for SolveWorkFrame {
        fn drop(&mut self) {
            SOLVE_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
            if let Some(v) = self.restore {
                SOLVE_ITERS.with(|c| c.set(v));
            }
        }
    }
}

thread_local! {
    /// Iterations the CURRENT solve may still spend; `u64::MAX` means "no work limit".
    static ITER_BUDGET: std::cell::Cell<u64> = const { std::cell::Cell::new(u64::MAX) };
}

/// A SIMPLEX KEPT ALIVE ACROSS BOUND CHANGES.
///
/// `solve_bounded` builds a fresh `Simplex` every call -- allocating several vectors the width of
/// the model -- and `warm_start` then REFACTORISES from scratch, which is O(m·nnz). For a caller
/// that changes nothing but BOUNDS between solves, all of that is waste: the basis is the same, so
/// `B` is the same, so `B⁻¹` is the same. Measured on air05 (426 rows, 7,195 columns, 59,318
/// nonzeros): a dive step is ONE simplex iteration and takes 21ms, essentially all of it setup. A
/// dive that needs thousands of steps therefore cannot be afforded, and air05 needs one -- it is
/// pure set partitioning and finds no feasible point at 20s, 60s or 120s.
///
/// So keep the solver, and just tell it the new box.
pub(crate) struct WarmSolver<'a> {
    lp: &'a FloatLp,
    sx: Simplex,
    seeded: bool,
}

impl<'a> WarmSolver<'a> {
    pub(crate) fn new(
        lp: &'a FloatLp,
        lower: &[f64],
        upper: &[f64],
        warm: Option<(&[usize], &[NbBound])>,
    ) -> Self {
        let mut sx = Simplex::new(lp, lower, upper);
        let seeded = warm.is_some();
        // LU-LANE EXTENSION (`--warm-lu`, default off; gated `tall_lu`).
        // Install an LU engine so this pooled re-solver's bound-change solves run
        // the FT lane: the engine survives across `solve` calls with the basis,
        // so a re-solve on an unchanged basis takes the `rep_basis` match-skip
        // instead of a full O(m·nnz) eta rebuild — the dominant eta consumer on
        // qiu (flip-LNS's eval loop). A fresh engine represents B = -I (the
        // all-logical basis Simplex::new starts on), so no reset is needed here;
        // `warm_start` below (if warm) refactorizes the adopted basis into it.
        if warm_lu_enabled() && (lp.wide_tall() || lp.tall_lu()) {
            sx.lu = Some(LuCache {
                eng: crate::lu::LuEngine::new(lp.m),
                rep_basis: (lp.n..lp.n + lp.m).collect(),
            });
            sx.sync_lu_counters();
        }
        if let Some((b, a)) = warm {
            sx.warm_start(lp, b, a, lower, upper);
        }
        Self { lp, sx, seeded }
    }

    /// Re-solve on a new box, reusing the basis and its factorisation.
    pub(crate) fn solve(
        &mut self,
        lower: &[f64],
        upper: &[f64],
        deadline: Option<std::time::Instant>,
    ) -> Candidate {
        stats::bump(&stats::SOLVES);
        // ITERATION LEDGER: the pooled bound-change re-solve is a third door
        // into the pivot loops (the dive/flip-LNS eval loop lives on it), so it
        // charges a solve like the other two or its phase's iterations-per-solve
        // would read as infinite.
        ledger_note_solve();
        let t = std::time::Instant::now();
        // LANE/CALLER ATTRIBUTION (trace only). A `WarmSolver` never installs an
        // LU engine (`Simplex::new`), so it is ALWAYS the eta lane, warm — the
        // pooled bound-change re-solve loop the dive/flip-LNS run on. This is the
        // largest single eta consumer on qiu; the LU-lane extension targets it.
        let trace_lane = trace_enabled();
        let eta_before = if trace_lane {
            REFAC_COUNT.load(std::sync::atomic::Ordering::Relaxed) as u64
        } else {
            0
        };
        self.sx.rebound(self.lp, lower, upper);
        self.sx.farkas = None;
        self.sx.farkas_verified = false;
        let status = self
            .sx
            .run(self.lp, self.seeded, WarmSolveMode::Normal, deadline);
        if trace_lane {
            let eta_delta = (REFAC_COUNT.load(std::sync::atomic::Ordering::Relaxed) as u64)
                .wrapping_sub(eta_before);
            // Lane 0 (LU) when the extension installed an engine, else eta-warm (1).
            record_lane(usize::from(self.sx.lu.is_none()), eta_delta);
        }
        self.seeded = true; // whatever happened, we now hold a basis worth carrying
        let (values, duals) = self.sx.extract(self.lp);
        let mut farkas = self.sx.farkas.clone().unwrap_or_default();
        if self.lp.scaled() {
            for (r, f) in farkas.iter_mut().enumerate() {
                *f *= self.lp.bnd_mul[self.lp.n + r];
            }
        }
        stats::SOLVE_NANOS.fetch_add(
            t.elapsed().as_nanos() as u64,
            std::sync::atomic::Ordering::Relaxed,
        );
        Candidate {
            basis: self.sx.basis.clone(),
            at: self.sx.at.clone(),
            values,
            duals,
            farkas,
            farkas_verified: self.sx.farkas_verified,
            status,
        }
    }
}

/// Bound the next solve by WORK rather than by the clock. Restores the previous budget on drop, so
/// it nests.
pub(crate) struct IterCap(u64);

impl IterCap {
    pub(crate) fn set(n: u64) -> Self {
        IterCap(ITER_BUDGET.with(|c| c.replace(n)))
    }
}

impl Drop for IterCap {
    fn drop(&mut self) {
        let prev = self.0;
        ITER_BUDGET.with(|c| c.set(prev));
    }
}

/// Spend one iteration. `false` once the budget is gone.
fn spend_iter() -> bool {
    ITER_BUDGET.with(|c| {
        let v = c.get();
        if v == 0 {
            return false;
        }
        if v != u64::MAX {
            c.set(v - 1);
        }
        true
    })
}

/// Non-improving iterations tolerated before switching to Bland's rule.
/// How long a phase may stall before Bland's rule takes over.
///
/// Bland's rule always terminates and always crawls: it enters the smallest-index eligible
/// column, which on a model with 10,757 of them is a scan by index rather than a search. It is
/// the anti-cycling backstop, and it was being reached for far too readily -- the trigger was
/// `min(m, 8000) + 50`, which on a 52-row instance is 102 non-improving iterations. A small
/// degenerate LP stalls for a few hundred iterations and then gets on with it; handing it to
/// Bland at 102 makes the rest of the solve a crawl for nothing. Measured: 70 binaries 13.7s ->
/// 9.0s from delaying it alone, with 60 binaries unchanged and no verdict moving on MIPLIB.
///
/// DEVEX PRICING WAS TRIED HERE AND EARNS NOTHING. The diagnosis it answers is real -- Dantzig
/// re-picks a column blocked at zero on a degenerate LP, and air03 (124 rows, 10,757 columns,
/// set-partitioning) grinds into `MAX_ITERS` -- and Devex does fix that stall. It just does not
/// pay: as the DEFAULT rule (a BTRAN plus a pass over every non-zero per iteration) it made 70
/// binaries 73% slower and left the 80-binary incumbent worse; as the stall ESCAPE, isolating it
/// against a plain Bland delay gave 9.1s vs 9.0s and the same incumbents -- i.e. the delay was
/// the whole win and Devex was riding on it. air03 stays at one node either way, because its
/// time then moves out of the simplex and into the root heuristics.
const STALL_BEFORE_BLAND: usize = 8_000;

/// No phase counts as stalled before this many non-improving iterations, however few rows it has.
const STALL_FLOOR: usize = 2_000;

/// Slack on top of the stall threshold before the backstop engages.
const BLAND_GRACE: usize = 20_000;

/// Iterations Bland's rule is given to move the objective before the phase
/// gives up (`Stopped`). Bland guarantees no CYCLE under a fixed cost vector,
/// but phase I's costs are rebuilt every iteration, so it guarantees nothing
/// there — and a phase that has not improved in `bland_after + this` pivots is
/// not converging, it is burning the caller's budget. Measured on an air05
/// RENS sub-LP (6,950 of 7,195 columns fixed, 44 rows unsatisfiable): phase I
/// ran 163,521 iterations with the infeasibility frozen at 44.0 and 52,307
/// bound flips — 11.2s for an answer ("Stopped") this abort produces in a
/// third of the pivots. `Stopped` is always safe advice: no verdict rides on
/// it, the caller falls back exactly as it does for `MAX_ITERS`.
const STALL_ABORT_GRACE: usize = 10_000;

/// How far a bound is nudged to break a degenerate tie. Far below `feas_tol`, so a point that
/// satisfies the perturbed box is within tolerance of the true one — and the true box is restored
/// and re-checked before anything is called `Optimal` regardless.
const PERTURB: f64 = 1e-9;

/// How many pivots the dual may have taken before its basis is worth rebuilding rather than
/// carrying onward. See the note at its use.
const DRIFT_REFACTOR: usize = 16;

/// The largest right-hand side that may inflate the primal tolerance. Past this, a bigger number in
/// the model buys no more slack -- see `feas_tol`.
const FEAS_SCALE_CAP: f64 = 1e4;

/// How dual-feasible a basis has to be before the dual simplex's answer is kept. See
/// `dual_feasible`: this is a "was it worth it" test, not a correctness one.
const DUAL_ACCEPT_TOL: f64 = 1e-7;

/// A Devex weight past this has stopped meaning anything; reset the reference framework.
const DEVEX_RESET: f64 = 1e7;

/// Ceiling on a dual steepest-edge weight — the mirror image of the 1e-4 floor. See the
/// Forrest–Goldfarb update in `dual_simplex` for why the ceiling is load-bearing.
const DSE_WEIGHT_CAP: f64 = 1e12;

/// Cell cap on the dense row mirror (`FloatLp::dense_rows`): 2^20 f64s = 8 MiB.
/// Everything on the dense ladder is a few thousand cells; sparse instances
/// (which the mirror would only slow down) fail the density gate anyway.
const DENSE_ROWS_MAX_CELLS: usize = 1 << 20;

/// How many columns per row make an LP "wide" enough for Devex pricing to pay. See the note at
/// its use: this is the regime where degeneracy explodes the iteration count.
const DEVEX_WIDTH: usize = 10;

/// Row floor for DEFAULT eager anti-degeneracy perturbation on wide LPs — see
/// the journal note at its use in `run`. Sits between the wide-but-short
/// family members that prove fine lazily (air03: 124 rows, mod010: 146,
/// khb05250: 101, mas76: 12) and the one that starves (air05: 426).
const EAGER_PERTURB_MIN_ROWS: usize = 200;

/// Row floor for the TALL warm-solve LU engine (`FloatLp::tall_lu`). Lowered
/// from the historical 1,200 (which sat one row ABOVE qiu deliberately, to keep
/// the measured corpus byte-identical) to 1,000, so qiu's 1,192-row degenerate
/// basis joins the LU lane. Measured: qiu's warm node solves were paying ~4.8
/// FULL O(m·nnz) eta rebuilds each (REFAC = 48% of node_lp), because the
/// eta path has no cross-solve operator reuse — `eta_reuse` fired ~12-32 times
/// in a 60s window while the LU cache's `rep_basis` match-skip fires ~4,300x
/// on the same tree. Effect: qiu reaches 200 nodes in 11.3s vs 16.0s and 400
/// in 19.7s vs 28.6s (~1.45x node-LP throughput), same incumbent, tree
/// near-identical (the LU lane changes SPEED, never the LP verdict). The floor
/// still clears every OTHER ladder/corpus instance — the next-tallest is gen at
/// 780 rows, a 220-row margin — so only qiu changes lanes, and the ACAS class
/// (≥1,425 rows) is untouched. See the journal at `tall_lu`.
///
/// NOT RUNTIME-SETTABLE, and deliberately so. The 1,200→1,000 commit shipped an
/// `AY_MILP_TALL_LU_ROWS` override "(=1200 restores byte-for-byte)"; B6 deleted
/// the read (`46e5eae53`) on the decision table's explicit verdict — a threshold
/// that DEFINES a class must not be settable per process, because the gate that
/// mirrors the same number (the node-propagation cap raise in `bab.rs`) cannot
/// follow it and would drift apart silently. It drifted anyway, from a plain edit
/// — that gate still reads 1_200; the note there says why re-tracking it is a
/// behaviour change, not a tidy-up. Recover the pre-qiu boundary by editing this
/// constant to 1_200 and rebuilding, not by exporting anything. The `no_tall_lu`
/// kill switch still disables the lane entirely, and it IS reachable per solve —
/// as the caller-layer `Knob::NoTallLu` (`EngineEconomics::with_tall_lu`, wired to
/// the `ay-milp` engine flag `no-tall-lu`), not as an env var. That is the shape a
/// lever is supposed to have here; the row floor simply is not a lever.
const TALL_LU_ROWS: usize = 1_000;

/// The cold-root LU band membership test, extracted from `FloatLp::cold_root_lu`
/// so the WINDOW itself is unit-testable without standing up a 5,000-row LP.
/// Half-open on purpose: the ceiling is a class boundary shared with
/// `REFACTOR_TALL_ROWS`, and a model sitting exactly on it belongs to the class
/// ABOVE (the w5/cifar regime), which is where the rest of the code puts it.
#[inline]
fn cold_root_lu_band(m: usize, min_rows: usize, max_rows: usize) -> bool {
    m >= min_rows && m < max_rows
}

/// Row floor of the COLD-ROOT LU band (`FloatLp::cold_root_lu`). Deliberately
/// 3× `TALL_LU_ROWS`: admitting a WARM node re-solve to the LU lane risks only
/// a child bound that is re-derived downstream, while admitting the COLD root
/// changes which optimal VERTEX seeds every heuristic. The higher bar is the
/// price of that asymmetry, and the A/B says it is the right bar — see the
/// measurement table on `FloatLp::cold_root_lu`.
const COLD_LU_MIN_ROWS: usize = 3_000;

/// Row floor for `FloatLp::tall_lu`: `TALL_LU_ROWS`, unconditionally.
///
/// B6: make-constant; the never-set AY_MILP_TALL_LU_ROWS env read is gone, and
/// the `OnceLock` that cached its parse went with it — a process-global latch
/// over a `const` buys nothing and reads as a runtime knob to the next person.
/// A/B the LU-engine boundary by editing `TALL_LU_ROWS` (see the retirement note
/// there); there is no runtime override to reach for.
#[inline]
fn tall_lu_rows() -> usize {
    TALL_LU_ROWS
}

/// Pivot allowance per row for the COLD dual-simplex start (`try_cold_dual`).
/// Sized from the air05 measurements at its use site: the root LP lands in
/// ~6.8·m pivots on the LU engine (HiGHS's dual: ~3.5·m on the same LP), the
/// cut-extended rounds in ~11·m — 30·m covers those with slack while still
/// bounding a flailing walk to a fraction of the primal grind it replaces.
const COLD_DUAL_BUDGET_PER_ROW: usize = 30;

/// Relative pivot floor for RATIO-TEST CANDIDACY: an `alpha` entry below this
/// fraction of the column's largest entry is treated as round-off, not as a
/// blocking row — see the journal note at its use in `loop_phase`. Sized from
/// the air05 measurements there: the noise being excluded is ~1e-8 against an
/// honest entry of 1.0, and no honest pivot ratio on the corpus is anywhere
/// near 1e6.
const REL_RATIO_PIVOT: f64 = 1e-6;

impl FloatLp {
    /// Lower `model` into computational form under an EXPLICIT objective.
    ///
    /// The objective is a parameter rather than `model`'s own because the W2
    /// surface re-solves one model against hundreds of per-column objectives
    /// (`tighten_col_bounds`); the certificate carries its own objective for the
    /// same reason.
    ///
    /// `None` if the model carries data this lane cannot represent (a NaN, or no
    /// columns).
    pub(crate) fn from_model(
        model: &Model,
        objective: &[(u32, f64)],
        sense: Sense,
    ) -> Option<Self> {
        Self::from_model_with_deadline(model, objective, sense, None)
    }

    /// Route-local bounded lowering. Every matrix construction pass shares
    /// `deadline`; equilibration is skipped because its repeated full-matrix
    /// passes have no independently useful verdict and the exact certificate
    /// rim remains authoritative over the unscaled model.
    pub(crate) fn from_model_with_deadline(
        model: &Model,
        objective: &[(u32, f64)],
        sense: Sense,
        deadline: Option<std::time::Instant>,
    ) -> Option<Self> {
        let expired = || deadline.is_some_and(|limit| std::time::Instant::now() >= limit);
        let n = model.num_cols();
        let m = model.num_rows();
        if n == 0 || expired() {
            return None;
        }
        let cols = n + m;

        let mut scale = 1.0f64;
        let (mut mat_scale, mut rhs_scale, mut cost_scale) = (1.0f64, 1.0f64, 1.0f64);
        let mut counts = vec![0usize; n];
        for r in 0..m {
            if r & 0x3f == 0 && expired() {
                return None;
            }
            let (coeffs, lb, ub) = model.row(crate::model::Row(r as u32));
            for (entry, &(c, a)) in coeffs.iter().enumerate() {
                if entry & 0x3ff == 0 && expired() {
                    return None;
                }
                if a.is_nan() {
                    return None;
                }
                counts[c as usize] += 1;
                scale = scale.max(a.abs());
                mat_scale = mat_scale.max(a.abs());
            }
            for b in [lb, ub] {
                if b.is_finite() {
                    scale = scale.max(b.abs());
                    rhs_scale = rhs_scale.max(b.abs());
                }
            }
        }

        let mut col_ptr = vec![0usize; n + 1];
        for j in 0..n {
            if j & 0x3ff == 0 && expired() {
                return None;
            }
            col_ptr[j + 1] = col_ptr[j] + counts[j];
        }
        let nnz = col_ptr[n];
        let mut col_idx = vec![0usize; nnz];
        let mut col_val = vec![0.0f64; nnz];
        let mut cursor = col_ptr.clone();
        for r in 0..m {
            if r & 0x3f == 0 && expired() {
                return None;
            }
            let (coeffs, _, _) = model.row(crate::model::Row(r as u32));
            for (entry, &(c, a)) in coeffs.iter().enumerate() {
                if entry & 0x3ff == 0 && expired() {
                    return None;
                }
                let p = cursor[c as usize];
                col_idx[p] = r;
                col_val[p] = a;
                cursor[c as usize] = p + 1;
            }
        }

        let mut lower = vec![0.0f64; cols];
        let mut upper = vec![0.0f64; cols];
        let mut cost = vec![0.0f64; cols];
        // Maximize is solved as minimize of the negated objective; the exact lane
        // un-negates. Keeping ONE direction inside the engine removes a whole
        // class of sign bugs from the pricing and ratio-test code.
        let flip = matches!(sense, Sense::Maximize);
        for j in 0..n {
            if j & 0x3ff == 0 && expired() {
                return None;
            }
            let (lb, ub) = model.col_bounds(Col(j as u32));
            if lb.is_nan() || ub.is_nan() {
                return None;
            }
            lower[j] = lb;
            upper[j] = ub;
        }
        for (index, &(c, a)) in objective.iter().enumerate() {
            if index & 0x3ff == 0 && expired() {
                return None;
            }
            if !a.is_finite() || (c as usize) >= n {
                return None;
            }
            cost[c as usize] = if flip { -a } else { a };
            scale = scale.max(a.abs());
            cost_scale = cost_scale.max(a.abs());
        }
        for r in 0..m {
            if r & 0x3f == 0 && expired() {
                return None;
            }
            let (_, lb, ub) = model.row(crate::model::Row(r as u32));
            lower[n + r] = lb;
            upper[n + r] = ub;
        }

        // CSR of the same matrix.
        let mut rcounts = vec![0usize; m];
        for (index, &r) in col_idx.iter().enumerate() {
            if index & 0x3ff == 0 && expired() {
                return None;
            }
            rcounts[r] += 1;
        }
        let mut row_ptr = vec![0usize; m + 1];
        for r in 0..m {
            if r & 0x3f == 0 && expired() {
                return None;
            }
            row_ptr[r + 1] = row_ptr[r] + rcounts[r];
        }
        let mut row_idx = vec![0u32; nnz];
        let mut row_val = vec![0.0f64; nnz];
        let mut rcursor = row_ptr.clone();
        for j in 0..n {
            if j & 0x3ff == 0 && expired() {
                return None;
            }
            for p in col_ptr[j]..col_ptr[j + 1] {
                let r = col_idx[p];
                let q = rcursor[r];
                row_idx[q] = j as u32;
                row_val[q] = col_val[p];
                rcursor[r] = q + 1;
            }
        }

        // Dense row mirror: only when at least half the cells are non-zero
        // (below that the padding costs more flops than the index loads it
        // removes) and the whole mirror stays cache-friendly small.
        let cells = m.saturating_mul(n);
        let mut dense_rows = Vec::new();
        if cells > 0 && cells <= DENSE_ROWS_MAX_CELLS && nnz * 2 >= cells {
            dense_rows = vec![0.0f64; cells];
            for r in 0..m {
                if r & 0x3f == 0 && expired() {
                    return None;
                }
                for q in row_ptr[r]..row_ptr[r + 1] {
                    if q & 0x3ff == 0 && expired() {
                        return None;
                    }
                    dense_rows[r * n + row_idx[q] as usize] = row_val[q];
                }
            }
        }

        let mut lp = Self {
            n,
            m,
            cols,
            ft_adoption_solve_latch: model.ft_adoption_solve_latch(),
            col_ptr,
            col_idx,
            col_val,
            row_ptr,
            row_idx,
            row_val,
            dense_rows,
            lower,
            upper,
            cost,
            sense,
            scale,
            lu_cache: LuCacheCell(std::cell::RefCell::new(None)),
            sx_cache: SxCell(std::cell::RefCell::new(None)),
            probe_reuse: ProbeReuseCell(std::cell::RefCell::new(ProbeReuse {
                armed: false,
                pristine: None,
            })),
            cut_slots_live: std::cell::Cell::new(false),
            dual_adapt: std::cell::Cell::new((0, 0, 0)),
            chain_shape: std::cell::Cell::new(0),
            chain_distress_probe_iters: None,
            eager_affine_crash: false,
            range_logical_triangular_crash: false,
            plain_cold: false,
            eager_perturb: false,
            cold_stalled: std::cell::Cell::new(false),
            mat_scale,
            rhs_scale,
            cost_scale,
            cutoff: std::cell::Cell::new(f64::INFINITY),
            rexp: Vec::new(),
            cexp: Vec::new(),
            bnd_mul: Vec::new(),
            val_mul: Vec::new(),
            scol_val: Vec::new(),
            srow_val: Vec::new(),
            sdense_rows: Vec::new(),
            sscale: 1.0,
            smat_scale: 1.0,
            srhs_scale: 1.0,
            scost_scale: 1.0,
        };
        if expired() {
            return None;
        }
        if deadline.is_none() {
            lp.equilibrate(model);
        }
        Some(lp)
    }

    /// Rebuild this LP's matrix, bounds and scaling from `model` IN PLACE — same
    /// dimensions, same identity. This is the CUT-SLOT swap primitive (`bab.rs`):
    /// the model's row COUNT is fixed (cut slots are reserved up front as free
    /// rows), only row CONTENTS change, so every warm basis stored anywhere in the
    /// tree keeps its length and stays adoptable.
    ///
    /// What survives the reload and what must not:
    ///   * the pooled `Simplex` scratch (`sx_cache`) survives — it is keyed on
    ///     dimensions only and fully reset per solve;
    ///   * the LU operator and DSE weights must NOT survive: they represent the OLD
    ///     matrix, and `refactorize`'s basis-match skip would then price against
    ///     stale numbers. Dropping them costs exactly one refactorization on the
    ///     next solve — which the eta path pays per warm solve anyway.
    ///
    /// `false` (and no change) if the model no longer lowers or its dimensions
    /// drifted — the caller keeps the old LP, which is still a valid relaxation.
    pub(crate) fn reload_rows(
        &mut self,
        model: &Model,
        objective: &[(u32, f64)],
        sense: Sense,
    ) -> bool {
        let Some(mut fresh) = Self::from_model(model, objective, sense) else {
            return false;
        };
        if fresh.m != self.m || fresh.n != self.n {
            return false;
        }
        fresh.plain_cold = self.plain_cold;
        fresh.eager_affine_crash = self.eager_affine_crash;
        fresh.range_logical_triangular_crash = self.range_logical_triangular_crash;
        fresh.chain_distress_probe_iters = self.chain_distress_probe_iters;
        // The census frame belongs to the solve, not to whichever temporary
        // model supplied this row reload.
        fresh.ft_adoption_solve_latch = self.ft_adoption_solve_latch.clone();
        // A cut-slot rewrite does not change the model's class: keep the
        // chain-shape verdict (recomputing on the cut-laden matrix could only
        // flip it noisily; the verdict is a property of the model's identity).
        fresh.chain_shape.set(self.chain_shape.get());
        std::mem::swap(&mut fresh.sx_cache, &mut self.sx_cache);
        *self = fresh;
        // The pooled scratch's eta file was built against the OLD matrix: kill its
        // cross-solve liveness so the next warm solve rebuilds instead of skipping
        // (same staleness rule as dropping the LU operator above).
        if let Some(sx) = self.sx_cache.0.borrow_mut().as_mut() {
            sx.factor_live = false;
        }
        // Warm bases elsewhere in the tree now predate this matrix: arm the dual
        // simplex's entry bound-flip repair for every later solve on this LP.
        self.cut_slots_live.set(true);
        true
    }

    /// Compute the power-of-2 equilibration and its scaled mirrors — or leave them
    /// empty (scaling off). See the field comment on `rexp` for the frame contract.
    fn equilibrate(&mut self, model: &Model) {
        let mode = equil_mode();
        if mode == 0 || self.m == 0 || self.col_val.is_empty() {
            return;
        }
        // Exponent span of the matrix: AUTO scales only genuinely ill-scaled data.
        let (mut emin, mut emax) = (i32::MAX, i32::MIN);
        for &v in &self.col_val {
            if v != 0.0 {
                let e = bexp(v);
                emin = emin.min(e);
                emax = emax.max(e);
            }
        }
        if emin > emax || (mode == 2 && emax - emin < AUTO_SPAN_BITS) {
            return;
        }
        let (n, m) = (self.n, self.m);
        let mut rexp = vec![0i32; m];
        let mut cexp = vec![0i32; n];
        // Alternating geometric passes on the EXPONENTS: each pass drives every
        // column's (then row's) scaled magnitude range to be centered on 2^0,
        // using the midpoint of the min/max binary exponent (= the geometric
        // mean to within a factor of two). Integer/binary columns stay C_j = 1.
        for _pass in 0..3 {
            for j in 0..n {
                if model.col_kind(Col(j as u32)).is_integral() {
                    continue;
                }
                let (mut lo, mut hi) = (i32::MAX, i32::MIN);
                for p in self.col_ptr[j]..self.col_ptr[j + 1] {
                    if self.col_val[p] != 0.0 {
                        let e = bexp(self.col_val[p]) + rexp[self.col_idx[p]];
                        lo = lo.min(e);
                        hi = hi.max(e);
                    }
                }
                if lo <= hi {
                    cexp[j] = -((lo + hi) >> 1);
                }
            }
            for r in 0..m {
                let (mut lo, mut hi) = (i32::MAX, i32::MIN);
                for q in self.row_ptr[r]..self.row_ptr[r + 1] {
                    if self.row_val[q] != 0.0 {
                        let e = bexp(self.row_val[q]) + cexp[self.row_idx[q] as usize];
                        lo = lo.min(e);
                        hi = hi.max(e);
                    }
                }
                if lo <= hi {
                    rexp[r] = -((lo + hi) >> 1);
                }
            }
        }
        // SAFETY CLAMP, then verify: every scaled entry, bound and cost must stay a
        // normal f64 (an overflow to inf or an underflow to zero would CHANGE the
        // problem the pivot lane sees — sparsity, finiteness of a bound). Scaling is
        // advice, so on any violation the whole thing is simply declined.
        for e in rexp.iter_mut().chain(cexp.iter_mut()) {
            *e = (*e).clamp(-300, 300);
        }
        const SAFE: i32 = 900;
        for j in 0..n {
            for p in self.col_ptr[j]..self.col_ptr[j + 1] {
                if self.col_val[p] != 0.0 {
                    let e = bexp(self.col_val[p]) + rexp[self.col_idx[p]] + cexp[j];
                    if e.abs() > SAFE {
                        return;
                    }
                }
            }
            for b in [self.lower[j], self.upper[j]] {
                if b.is_finite() && b != 0.0 && (bexp(b) - cexp[j]).abs() > SAFE {
                    return;
                }
            }
            if self.cost[j] != 0.0 && (bexp(self.cost[j]) + cexp[j]).abs() > SAFE {
                return;
            }
        }
        for r in 0..m {
            for b in [self.lower[n + r], self.upper[n + r]] {
                if b.is_finite() && b != 0.0 && (bexp(b) + rexp[r]).abs() > SAFE {
                    return;
                }
            }
        }
        // Build the mirrors: pure exponent shifts, exact.
        let pw = |e: i32| -> f64 { 2f64.powi(e) };
        let mut scol_val = self.col_val.clone();
        for j in 0..n {
            for p in self.col_ptr[j]..self.col_ptr[j + 1] {
                scol_val[p] *= pw(rexp[self.col_idx[p]] + cexp[j]);
            }
        }
        let mut srow_val = self.row_val.clone();
        for r in 0..m {
            for q in self.row_ptr[r]..self.row_ptr[r + 1] {
                srow_val[q] *= pw(rexp[r] + cexp[self.row_idx[q] as usize]);
            }
        }
        let mut sdense_rows = Vec::new();
        if !self.dense_rows.is_empty() {
            sdense_rows = self.dense_rows.clone();
            for r in 0..m {
                for j in 0..n {
                    sdense_rows[r * n + j] *= pw(rexp[r] + cexp[j]);
                }
            }
        }
        let mut bnd_mul = vec![1.0f64; self.cols];
        let mut val_mul = vec![1.0f64; self.cols];
        for j in 0..n {
            bnd_mul[j] = pw(-cexp[j]);
            val_mul[j] = pw(cexp[j]);
        }
        for r in 0..m {
            bnd_mul[n + r] = pw(rexp[r]);
            val_mul[n + r] = pw(-rexp[r]);
        }
        // Tolerance stats of the scaled frame.
        let mut smat = 1.0f64;
        for &v in &scol_val {
            smat = smat.max(v.abs());
        }
        let mut srhs = 1.0f64;
        let mut sscale = smat;
        for j in 0..self.cols {
            for b in [self.lower[j] * bnd_mul[j], self.upper[j] * bnd_mul[j]] {
                if b.is_finite() {
                    srhs = srhs.max(b.abs());
                    sscale = sscale.max(b.abs());
                }
            }
        }
        let mut scost = 1.0f64;
        for j in 0..n {
            let c = self.cost[j] * val_mul[j]; // c'_j = c_j·C_j = c_j·2^cexp
            scost = scost.max(c.abs());
            sscale = sscale.max(c.abs());
        }
        if crate::debug_flags::milp_debug_flags().trace {
            let (rmin, rmax) = (
                rexp.iter().min().unwrap_or(&0),
                rexp.iter().max().unwrap_or(&0),
            );
            let (cmin, cmax) = (
                cexp.iter().min().unwrap_or(&0),
                cexp.iter().max().unwrap_or(&0),
            );
            eprintln!(
                "--trace equilibrate: span 2^{emin}..2^{emax} rexp [{rmin},{rmax}] cexp [{cmin},{cmax}] smat={smat:.2e} srhs={srhs:.2e} scost={scost:.2e} sscale={sscale:.2e}"
            );
        }
        self.rexp = rexp.iter().map(|&e| e as i16).collect();
        self.cexp = cexp.iter().map(|&e| e as i16).collect();
        self.bnd_mul = bnd_mul;
        self.val_mul = val_mul;
        self.scol_val = scol_val;
        self.srow_val = srow_val;
        self.sdense_rows = sdense_rows;
        self.smat_scale = smat;
        self.srhs_scale = srhs;
        self.scost_scale = scost;
        self.sscale = sscale;
    }

    /// Deterministic structural estimate of this engine's heap footprint: the
    /// byte capacity of every owned matrix / bound / cost / scaling vector.
    /// A fresh clone has empty interior caches. The proof-first prefix scheduler
    /// conservatively multiplies this estimate before admitting owned workers;
    /// the serial node driver and simplex hot loop never call it.
    pub(crate) fn approx_bytes(&self) -> usize {
        use std::mem::size_of;
        self.col_ptr.capacity() * size_of::<usize>()
            + self.col_idx.capacity() * size_of::<usize>()
            + self.col_val.capacity() * size_of::<f64>()
            + self.row_ptr.capacity() * size_of::<usize>()
            + self.row_idx.capacity() * size_of::<u32>()
            + self.row_val.capacity() * size_of::<f64>()
            + self.dense_rows.capacity() * size_of::<f64>()
            + self.lower.capacity() * size_of::<f64>()
            + self.upper.capacity() * size_of::<f64>()
            + self.cost.capacity() * size_of::<f64>()
            + self.rexp.capacity() * size_of::<i16>()
            + self.cexp.capacity() * size_of::<i16>()
            + self.bnd_mul.capacity() * size_of::<f64>()
            + self.val_mul.capacity() * size_of::<f64>()
            + self.scol_val.capacity() * size_of::<f64>()
            + self.srow_val.capacity() * size_of::<f64>()
            + self.sdense_rows.capacity() * size_of::<f64>()
    }

    /// Is the pivot lane running on scaled data?
    #[inline]
    pub(crate) fn scaled(&self) -> bool {
        !self.scol_val.is_empty()
    }

    /// The pivot lane's matrix views: scaled mirrors when scaling is on.
    #[inline]
    fn p_col_val(&self) -> &[f64] {
        if self.scol_val.is_empty() {
            &self.col_val
        } else {
            &self.scol_val
        }
    }
    #[inline]
    fn p_row_val(&self) -> &[f64] {
        if self.srow_val.is_empty() {
            &self.row_val
        } else {
            &self.srow_val
        }
    }
    #[inline]
    fn p_dense_rows(&self) -> &[f64] {
        if self.sdense_rows.is_empty() && self.scol_val.is_empty() {
            &self.dense_rows
        } else {
            &self.sdense_rows
        }
    }
    /// Original→scaled multiplier for column `j`'s VALUES/violations (1.0 when
    /// scaling is off). A scaled-frame violation of column `j` compares against
    /// `tol_base * bmul(j)` — the exact frame image of the unscaled engine's
    /// absolute-tolerance test (see the per-column tolerance notes on `rexp`).
    #[inline]
    fn bmul(&self, j: usize) -> f64 {
        if self.bnd_mul.is_empty() {
            1.0
        } else {
            self.bnd_mul[j]
        }
    }
    /// Scaled→original multiplier for column `j` (1.0 when off): converts a
    /// scaled violation into ORIGINAL units (the phase-1 metric), and carries
    /// the reduced-cost frame (d'_j = d_j · vmul(j)) for cost tolerances.
    #[inline]
    fn vmul(&self, j: usize) -> f64 {
        if self.val_mul.is_empty() {
            1.0
        } else {
            self.val_mul[j]
        }
    }

    /// The structural column `j` of `A` as `(row, coeff)` pairs.
    /// The largest coefficient magnitude, for diagnostics.
    pub(crate) fn scale_for_trace(&self) -> (f64, f64, f64) {
        (self.mat_scale, self.rhs_scale, self.cost_scale)
    }

    /// WIDE-AND-TALL: a set-partitioning-like regime where degeneracy and
    /// eta-file drift make the default walk expensive. This gate enables eager
    /// anti-degeneracy perturbation, a cold dual-simplex start, and sparse-LU
    /// basis maintenance. The row floor leaves wide-but-short models on the
    /// default path.
    pub(crate) fn wide_tall(&self) -> bool {
        self.n >= DEVEX_WIDTH * self.m.max(1) && self.m >= EAGER_PERTURB_MIN_ROWS
    }

    /// TALL: enough rows that rebuilding the eta representation can dominate
    /// warm node and probe solves even when the matrix is not wide. Sparse LU
    /// can reuse a matching basis and absorb updates. This lane changes basis
    /// maintenance, not the LP admission checks or verdict semantics.
    pub(crate) fn tall_lu(&self) -> bool {
        self.m >= tall_lu_rows() && !no_tall_lu()
    }

    /// Charge the current top-level solve's first actual FT-adoption
    /// exclusion. Called from the excluded branch of every refactorization;
    /// the shared latch makes all later calls in this solve no-ops.
    #[inline]
    pub(crate) fn charge_ft_adoption_exclusion(&self) -> bool {
        self.ft_adoption_solve_latch
            .as_ref()
            .is_some_and(|latch| latch.charge(self.m as u64))
    }

    /// COLD-ROOT LU BAND: the row window where the FT engine is measured to beat
    /// the product-form eta file on the *vertex-seeding* solve as well as on the
    /// warm ones, so `plain_cold` may hand it the cold root LP too.
    ///
    /// # Why a band and not a floor
    ///
    /// `plain_cold` (see the field's note) pins COLD solves to the eta file
    /// because the root vertex seeds the pump/dive/RINS chain. That pin is
    /// correct policy and wrong at one size class. Measured, 2026-07-27/28,
    /// 60–120 s caps, `--lu` as the force-lever (deterministic counters
    /// first, wall indicative — the box was contended):
    ///
    /// | m | instance | eta lane | LU lane |
    /// |---|----------|----------|---------|
    /// | 12–780 | mas76…gen (9 instances) | REFAC 0.06–0.88 s, i.e. <20 % of LP time | 1.4–2.7× wall, 1.15–2.5× nodes, **air05 LOSES its proven bound** |
    /// | 1 192 | qiu | 4 541 nodes / 38.1 s | 2 986 nodes / 55.9 s (mixed) |
    /// | 2 298 | binkar10_1 | 44 645 nodes | 40 477 nodes (mixed) |
    /// | 3 522 | nursesched-sprint02 | root LP 59.2 s, REFAC **2 611 / 39.3 s**, 899 piv/s, UNKNOWN 4 nodes | root LP 17.4 s, REFAC 424 / 3.1 s, 3 117 piv/s (**3.5×**), **BOUND 55**, 31 nodes |
    /// | 4 744 | neos-960392 | REFAC 819 / 9.7 s, **2 nodes** | REFAC 33 / 0.02 s, **287 nodes (143×)** |
    /// | 5 195 | hypothyroid-k1 | REFAC **687 / 89.7 s = 76 % of LP time**, root LP **stopped, NO BOUND** | root LP Optimal @34.6 s, **bound −2902.852586** |
    /// | 40 962–168 336 | ex9/ex10/uccase12/physiciansched6-2 | REFAC 23–87 s (38–74 %) | REFAC falls 30–166× **but** `LuEngine::update` is O(m) dense per pivot (1.85 ms/update at m=40 962, 3.57 ms at m=69 608) and eats 23–34 % back; net pivots/s 0.79–1.31×, no lane converges |
    ///
    /// So the win is a WINDOW, not a ray. Below the floor the eta rebuild is
    /// O(m·nnz) with a tiny `m` and is already free, while the FT engine's
    /// per-pivot cost is pure loss AND moves the vertex (air05, rout). Above the
    /// ceiling the refactorisation wall is genuinely removed and the bound does
    /// improve (ex9 10.64 → 16.36, uccase12 1954 → 2385) but a NEW O(m) wall
    /// takes its place, so the lane change is not yet a win to bank — that is a
    /// `lu.rs::update` sparsification job, not a dispatch job.
    ///
    /// # What the band bought, A/B'd against `--no-cold-lu` at 60 s
    ///
    /// 61 instance pairs (40 in band, 21 outside), one binary, both arms.
    /// In-band totals: 89,220 → 21,264 eta rebuilds, 861.2 s → 99.3 s of REFAC,
    /// and 4,245,309 → 6,445,155 simplex pivots — 1.52× the LP work done inside
    /// the same 60 s budget, bought entirely from the refactorisation bill.
    ///
    /// * ELEVEN in-band models complete their FIRST root LP where the eta lane
    ///   cannot finish it at all — cvs16r70-62 / r89-60 / r128-89, glass-sc,
    ///   hypothyroid-k1, milo-v12-6-r2-40-1, peg-solitaire-a3, seymour,
    ///   seymour1, nursesched-sprint02, cmflsp50-24-8-8. Deterministic
    ///   counters, eta → LU: peg-solitaire-a3 7,034 rebuilds/36.71 s → 66/0.70 s
    ///   with 41,732 → 219,065 pivots; seymour 3,670/48.21 s → 0/0.00 s with
    ///   20,612 → 74,770; cvs16r70-62 3,183/49.85 s → 439/6.12 s with
    ///   17,927 → 161,725. Sweep totals: 158,126 → 88,116 eta rebuilds,
    ///   987.0 s → 223.4 s of REFAC.
    /// * +7 verdicts (cvs16r70-62, cvs16r89-60, cvs16r128-89, glass-sc,
    ///   nursesched-sprint02, peg-solitaire-a3, seymour1), −1 (cmflsp50-24-8-8,
    ///   whose root LP the LU lane PROVES Optimal at 40.2 s where the eta lane
    ///   is still `Stopped` at 50.7 s — the verdict is lost in the tree-bound
    ///   REPORTER, which forfeits the global claim when an open node cannot
    ///   re-derive its own bound, not in this lane).
    /// * ZERO verdict disagreements against `manifest.json` `ref_obj`, and zero
    ///   lane disagreements: on all 38 pairs where BOTH lanes solve the pure LP
    ///   relaxation (`cut round 0`, the identical LP in both arms) the bounds
    ///   are bit-identical — worst relative deviation exactly 0.0.
    /// * OUT OF BAND, all 9 pairs that reach a proof are bit-identical in
    ///   verdict, objective, node count AND eta-rebuild count (mas76 909,442
    ///   nodes, misc07 4,702, qnet1 373, qiu 4,541, decomp2 6,513, gen 11,
    ///   p0201 168, flugpl 1,582, markshare1 0). Deadline-truncated
    ///   out-of-band runs differ by less than SAME-ARM repeat noise on a
    ///   contended box: air05 alone spans 374/374/374 vs 2,340 eta rebuilds and
    ///   17 vs 35 nodes across four runs of the IDENTICAL arm, which is why the
    ///   floor is not tuned on truncated instances.
    /// * ABOVE the ceiling nothing moves, checked rather than assumed: ex9
    ///   (m = 40,962) 242 vs 243 eta rebuilds with the identical root LP bound
    ///   9.028183 and `LUFACT count=0` in both arms, and neos-827175
    ///   (m = 14,187) 371 vs 373 with its triangular crash intact in both —
    ///   which is the confound the `--lu` force-lever could not avoid.
    /// * `AY_MILP_LU_VERIFY=1` — refactorize-from-scratch and re-ask after EVERY
    ///   single Forrest–Tomlin update, the strictest cross-check the crate has,
    ///   and in class here because the band sits inside `verify_after_for`'s
    ///   `tall_lu() && m < REFACTOR_TALL_ROWS` gate — reproduces the root LP
    ///   bound EXACTLY on all six band winners tried (nursesched-sprint02
    ///   54.416667, peg-solitaire-a3 1.000000, seymour1 403.846474, glass-sc
    ///   14.080296, cvs16r70-62 −70.000000, and hypothyroid-k1 −2902.852586 once
    ///   given 150 s) at 1.5–2.0× wall, with `singular_deferred=0` throughout.
    ///   A wrong factorisation would have to be wrong the SAME way with 1 update
    ///   between refactorisations as with 64 to survive that.
    ///
    /// # Why the ceiling is `REFACTOR_TALL_ROWS`
    ///
    /// 8 192 is already the class boundary for `lu_verify_after`, `adopt_ft_max`
    /// and the tall refactor cadence: below it the FT engine is the trusted
    /// operator and its staleness/adoption policy is tuned; above it the code
    /// hands control back to the w5/cifar wide-tall regime. Reusing that line
    /// keeps ONE notion of "the FT-trusted band" instead of two, and it happens
    /// to sit above every measured winner (max 5 195) and below the measured
    /// wash (min 40 962). `AY_MILP_COLD_LU_MAX_ROWS` moves it for the follow-up
    /// experiment once `update` is sparse.
    ///
    /// WARM solves are untouched here: they already take the LU lane through
    /// `node_lu` (`warm.is_some() && tall_lu()`), which is why the only measured
    /// gap was the cold root. `--no-cold-lu` restores the historical
    /// eta-file cold root byte-for-byte.
    pub(crate) fn cold_root_lu(&self) -> bool {
        !no_cold_lu() && cold_root_lu_band(self.m, cold_lu_min_rows(), cold_lu_max_rows())
    }

    /// Gate for the DUAL RATIO-TEST ANTI-CHURN (Harris) BAND: at a degenerate
    /// stop the ratio test has many breakpoints tied at ratio ≈ 0, and entering
    /// at whichever the scan met first takes an ARBITRARY (often small) pivot;
    /// a small pivot maximizes the churn it kicks onto other basics (the primal
    /// step is `(xb−target)/piv`, so `|piv|` ↓ ⇒ every other row's movement ↑),
    /// which on a degenerate face bounces the infeasibility around and lengthens
    /// the walk. Picking the LARGEST pivot magnitude within a reduced-cost
    /// tolerance band of the stop is the textbook anti-churn fix.
    ///
    /// Historically this was `wide_tall()` only — the set-partitioning shape
    /// (air05). But the qiu class (1,192 × 840, a capacity==demand network) is
    /// TALL not wide, so `wide_tall` never fired, and its warm dual walks were
    /// measured 83–88 % dual-degenerate (θ≈0) with only ~3 % bound-flips
    /// (`AY_MILP_DUAL_ANATOMY`): a pure degenerate churn the band is built for.
    /// `tall_lu()` (m ≥ 1,000) catches qiu — and, in the corpus, ONLY qiu — so
    /// every exact-value instance keeps its pivot stream byte-for-byte
    /// (air05 is already `wide_tall`; the dense ladder is square and < 1,000
    /// rows). ACAS (≥ 1,425 rows) also clears `tall_lu`, so it is A/B-checked.
    /// `AY_MILP_NO_DUAL_CHURN_BAND` restores the `wide_tall`-only gate.
    pub(crate) fn dual_churn_band(&self) -> bool {
        if no_dual_churn_band() {
            return self.wide_tall();
        }
        self.wide_tall() || self.tall_lu()
    }

    /// TRUE once this LP has been PROMOTED (distress state 1): a chain whose
    /// cold walk actually stalled. Reads the cached verdict only.
    pub(crate) fn chain_lp(&self) -> bool {
        self.chain_shape.get() == 1
    }

    /// Request the self-validating affine-chain crash on this LP's next cold
    /// solve.  This is local advice: it does not alter environment policy,
    /// process defaults, warm solves, or any other [`FloatLp`].
    pub(crate) fn request_eager_affine_crash(&mut self) {
        self.eager_affine_crash = true;
    }

    /// Set the typed, per-instance range-logical triangular-crash request.
    ///
    /// The historical environment opt-in is resolved separately at the crash
    /// attempt so an explicit request never mutates process-global policy.
    pub(crate) fn request_range_logical_triangular_crash(&mut self) {
        self.range_logical_triangular_crash = true;
    }

    /// Set the typed, per-instance cold affine-chain distress-probe budget.
    ///
    /// `None` retains the historical environment/default policy. The value
    /// survives row reloads and ordinary `FloatLp` clones.
    pub(crate) fn set_chain_distress_probe_iters(&mut self, iters: Option<u64>) {
        self.chain_distress_probe_iters = iters;
    }

    /// Restore the top-level census frame when an internal model
    /// transformation rebuilt `Model` from scratch instead of cloning it.
    pub(crate) fn set_ft_adoption_solve_latch(
        &mut self,
        latch: crate::sepstat::FtAdoptionSolveLatch,
    ) {
        self.ft_adoption_solve_latch = Some(latch);
    }

    /// Typed per-instance override, excluding the environment compatibility
    /// fallback.
    #[cfg(test)]
    pub(crate) fn chain_distress_probe_iters_override(&self) -> Option<u64> {
        self.chain_distress_probe_iters
    }

    /// Effective range-logical policy for this LP instance.
    fn range_logical_triangular_crash_enabled(&self) -> bool {
        self.range_logical_triangular_crash || range_logical_crash_env_enabled()
    }

    /// Typed per-instance request, excluding the environment compatibility
    /// fallback. Test-only so production callers cannot confuse the two.
    #[cfg(test)]
    pub(crate) fn range_logical_triangular_crash_requested(&self) -> bool {
        self.range_logical_triangular_crash
    }

    /// TRUE once this LP has been CLASSIFIED as a layered-affine chain — whether
    /// merely ARMED (state 3) or promoted on distress (state 1). Distinct from
    /// `chain_lp` (distress ONLY): the k124 ACAS diff-leaf class has healthy cold
    /// walks and so never leaves state 3, yet it is exactly the badly-scaled
    /// chain whose warm dual THRASHES if the bloom cap is lifted — so the tall_lu
    /// bloom-cap relaxation must key off THIS predicate, not `chain_lp`. State 2
    /// (classified NOT-chain, e.g. qiu) and state 0 (unclassified) are false.
    pub(crate) fn chain_class(&self) -> bool {
        matches!(self.chain_shape.get(), 1 | 3)
    }

    /// The bloom-cap RELAXATION predicate (see the tall_lu bloom arm in
    /// `dual_simplex`). The divergence guard must be RELAXED only for a
    /// POSITIVELY-classified non-chain LP (state 2, e.g. qiu, whose warm-dual
    /// bloom genuinely converges). It must stay ARMED for the chain class
    /// (states 1/3, which thrash) AND for the UNCLASSIFIED state 0 — which is
    /// where the BIG size class (cifar100 NN windows/full-depth) sits, because
    /// BIG skips classification entirely. The old predicate `!chain_class()`
    /// was true for state 0 too, silently disabling the guard on exactly the
    /// NN-thrash class it was built for; keying on state 2 positively fixes it.
    /// Verdict-neutral: only the warm walk's length/bail changes (every exit is
    /// post-checked primal_feasible+priced_out; bounds rigorous for any duals).
    pub(crate) fn bloom_relax_class(&self) -> bool {
        self.chain_shape.get() == 2
    }

    /// The EQUALITY-ROW TRIANGULAR PEEL census — `triangular_crash`'s own peel
    /// (column with exactly one unpeeled equality-row incidence pins that row;
    /// cascade), run as a COUNT ONLY (no eta build, no basis change). Returns
    /// `(neq, peeled)`: equality-row count and how many of them peel
    /// triangularly. A layered affine chain peels its equality rows
    /// near-completely — every pre-activation row has a private output column
    /// (k=546: 1,235/1,235) — while a generic MILP's equality rows share
    /// columns and jam. O(nnz + n + m), deterministic (index-ordered queue,
    /// FIFO growth), identical admissibility to the crash (free column,
    /// `|a| > TINY`). `lo`/`up` are the per-solve SCALED bounds
    /// (`Simplex::reset` frame — equality and fixedness are scale-invariant).
    fn chain_peel_census(&self, lo: &[f64], up: &[f64]) -> (usize, usize) {
        const TINY: f64 = 1e-11;
        let n = self.n;
        let m = self.m;
        let mut eq = vec![false; m];
        let mut neq = 0usize;
        for r in 0..m {
            if lo[n + r] == up[n + r] {
                eq[r] = true;
                neq += 1;
            }
        }
        if neq == 0 {
            return (0, 0);
        }
        let rvals = self.p_row_val();
        let cvals = self.p_col_val();
        // count[j] = number of unpeeled equality rows column j is incident to
        // (entries above TINY, columns that can rest basic, i.e. not fixed).
        let mut count = vec![0u32; n];
        for r in 0..m {
            if !eq[r] {
                continue;
            }
            for p in self.row_ptr[r]..self.row_ptr[r + 1] {
                let j = self.row_idx[p] as usize;
                if lo[j] < up[j] && rvals[p].abs() > TINY {
                    count[j] += 1;
                }
            }
        }
        let mut queue: std::collections::VecDeque<u32> =
            (0..n as u32).filter(|&j| count[j as usize] == 1).collect();
        let mut placed = vec![false; m];
        let mut peeled = 0usize;
        while let Some(j32) = queue.pop_front() {
            let j = j32 as usize;
            if count[j] != 1 {
                continue;
            }
            // The single unpeeled admissible equality row of column j.
            let mut row = usize::MAX;
            for p in self.col_ptr[j]..self.col_ptr[j + 1] {
                let r = self.col_idx[p];
                if eq[r] && !placed[r] && cvals[p].abs() > TINY {
                    row = r;
                    break;
                }
            }
            if row == usize::MAX {
                continue; // count says 1 but no admissible row: stale entry
            }
            placed[row] = true;
            peeled += 1;
            count[j] = 0;
            for p in self.row_ptr[row]..self.row_ptr[row + 1] {
                let jj = self.row_idx[p] as usize;
                if lo[jj] < up[jj] && rvals[p].abs() > TINY {
                    let c = &mut count[jj];
                    if *c > 0 {
                        *c -= 1;
                        if *c == 1 {
                            queue.push_back(jj as u32);
                        }
                    }
                }
            }
        }
        (neq, peeled)
    }

    /// ADAPTIVE WARM-DUAL BYPASS: should this warm solve attempt the dual walk?
    ///
    /// A dual-feasible parent basis often re-solves a bound-change child
    /// cheaply, but some model regimes repeatedly hit the divergence guard and
    /// then pay for a primal repair as well. The policy is measured per LP
    /// instance: once enough warm walks have been scored and the win rate is
    /// low, go primal-first while periodically probing so a regime shift can
    /// re-enable the dual walk. Exponential forgetting at `FORGET_AT` prevents
    /// old history from pinning the choice. A walk is scored a WIN when its work
    /// is used: it settles
    /// (Optimal/Cutoff/verified-infeasible) or its basis is kept for the primal
    /// cleanup; a rolled-back walk is a LOSS. Deterministic (counters, no
    /// clocks), self-gating (a class that keeps winning never bypasses), and
    /// fail-closed as ever: this chooses which float walk runs, never what is
    /// believed. `--dual-bypass-mode 0` kills it (always attempt);
    /// `--dual-bypass-mode 2` always bypasses (measurement lever).
    pub(crate) fn warm_dual_should_attempt(&self) -> bool {
        match dual_bypass_mode() {
            0 => true,
            2 => false,
            _ => {
                let (att, wins, skips) = self.dual_adapt.get();
                if att < DUAL_BYPASS_MIN_ATTEMPTS
                    || (wins as u64) * DUAL_BYPASS_WIN_DEN as u64 >= att as u64
                {
                    return true;
                }
                if skips + 1 >= DUAL_BYPASS_PROBE_EVERY {
                    self.dual_adapt.set((att, wins, 0));
                    true
                } else {
                    self.dual_adapt.set((att, wins, skips + 1));
                    false
                }
            }
        }
    }

    /// Score a warm dual walk for the bypass policy (see
    /// `warm_dual_should_attempt`): `win` = the walk's work was used.
    pub(crate) fn note_warm_dual(&self, win: bool) {
        let (mut att, mut wins, skips) = self.dual_adapt.get();
        att += 1;
        wins += win as u32;
        if att >= DUAL_BYPASS_FORGET_AT {
            att /= 2;
            wins /= 2;
        }
        self.dual_adapt.set((att, wins, skips));
    }

    /// Row `r` of `A`, as `(column, coefficient)` pairs.
    pub(crate) fn row(&self, r: usize) -> impl Iterator<Item = (usize, f64)> + '_ {
        (self.row_ptr[r]..self.row_ptr[r + 1])
            .map(move |p| (self.row_idx[p] as usize, self.row_val[p]))
    }

    /// The number of rows.
    pub(crate) fn rows(&self) -> usize {
        self.m
    }

    pub(crate) fn column(&self, j: usize) -> impl Iterator<Item = (usize, f64)> + '_ {
        (self.col_ptr[j]..self.col_ptr[j + 1]).map(move |p| (self.col_idx[p], self.col_val[p]))
    }

    /// The `M`-column of `j`, applied to a dense vector: `out += M_j * v`.
    /// Structural columns come from the CSC; logical `n + r` is `-e_r`.
    /// Unchecked scatter under the CSC invariants (`col_idx` entries `< m`),
    /// asserted in debug builds — `recompute_xb` runs this per non-basic column
    /// on every node re-solve.
    #[inline]
    fn axpy(&self, j: usize, v: f64, out: &mut [f64]) {
        if j < self.n {
            let (s, e) = (self.col_ptr[j], self.col_ptr[j + 1]);
            debug_assert!(e <= self.col_idx.len() && s <= e);
            // SAFETY: `s..e` bounds the aligned CSC index/value arrays, and
            // every stored row is less than `out.len()` by construction.
            unsafe {
                let ci = self.col_idx.as_ptr();
                let cv = self.p_col_val().as_ptr();
                let op = out.as_mut_ptr();
                for q in s..e {
                    let r = *ci.add(q);
                    debug_assert!(r < out.len());
                    *op.add(r) += *cv.add(q) * v;
                }
            }
        } else {
            out[j - self.n] -= v;
        }
    }

    /// Solve under the model's own bounds.
    pub(crate) fn solve(&self, deadline: Option<std::time::Instant>) -> Candidate {
        self.solve_bounded(&self.lower.clone(), &self.upper.clone(), None, deadline)
    }

    /// Solve under TIGHTENED bounds, optionally WARM-STARTED from a basis.
    ///
    /// This is the branch-and-bound entry point, and the warm start is what makes
    /// node throughput possible at all: a child differs from its parent in the
    /// bound of exactly one column, so the parent's optimal basis is already
    /// almost right for it. Starting there costs a handful of pivots; starting
    /// from the all-logical crash basis costs a full phase I and phase II, and
    /// that is the difference between a millisecond a node and a microsecond.
    /// Rows of `B^{-1}`, in FLOATS -- the multipliers that produce a tableau row.
    ///
    /// Separation does not need these EXACTLY. Any rational vector `u` gives an exact equation
    /// `uᵀ M z = 0`, because `M z = 0` holds for every point of the model whatever `u` is -- so the
    /// multipliers may be computed however cheaply one likes, snapped to rationals, and the
    /// combination taken exactly. Deriving them from an exactly-factored basis instead costs an
    /// `O(m³)` rational LU, and that -- not the LP -- is what makes a cut loop unaffordable: on rout
    /// it is 1.94s in round zero, 9.13s in round one, 16.36s in round two.
    ///
    /// A BTRAN is `O(nnz)`.
    pub(crate) fn btran_rows(&self, cand: &Candidate, rows: &[usize]) -> Option<Vec<Vec<f64>>> {
        let mut sx = Simplex::new(self, &self.lower, &self.upper);
        sx.warm_start(self, &cand.basis, &cand.at, &self.lower, &self.upper);
        let mut out = Vec::with_capacity(rows.len());
        for &i in rows {
            if i >= self.m {
                return None;
            }
            sx.y_is_duals = false;
            sx.y.fill(0.0);
            sx.y[i] = 1.0;
            sx.btran();
            let mut row = sx.y.clone();
            // Scaled frame: B' = R·B·D with D the basis columns' scales, so
            // row_i(B⁻¹) = d_i · row'_i(B'⁻¹) ∘ R — exact power-of-two fixups.
            if self.scaled() {
                let d_i = self.val_mul[cand.basis[i]];
                for (r, v) in row.iter_mut().enumerate() {
                    *v *= d_i * self.bnd_mul[self.n + r];
                }
            }
            out.push(row);
        }
        Some(out)
    }

    /// DIFFERENTIAL-CORRECTNESS PROBE (the BTF de-risking scaffold). Factor
    /// `cand`'s basis through `refactorize` on a FORCED bump-LU lane (`lane` = 0
    /// PFI slot-order, 1 Markowitz bump-LU, 2 block-triangular bump-LU), then
    /// capture the `B⁻¹` images that let a differential caller confirm the
    /// lanes represent the SAME inverse operator.
    ///
    /// PERMUTATION-INVARIANT INDEXING (the load-bearing subtlety). `refactorize`
    /// finalizes `self.basis = rf_new_basis` (simplex.rs) — it PERMUTES the basis
    /// into the factorization's pivot-order row slots, and the two lanes pivot the
    /// bump in DIFFERENT orders, so lane 0 and lane 1 assign the same basis column
    /// to DIFFERENT row slots. Comparing FTRAN/BTRAN vectors by raw row slot would
    /// then compare permuted vectors and report a spurious O(1) disagreement even
    /// though both operators are identical. So this probe keys everything off
    /// COLUMN IDENTITY, which is lane-invariant:
    ///   * FTRAN: `alpha = B⁻¹·M_j` is remapped from row-slot to canonical
    ///     basis-column order via `basic_row` — `out[k]` is the coefficient of the
    ///     basis column `cand.basis[k]` in `M_j`'s expansion, the UNIQUE (hence
    ///     lane-invariant) solution of `B x = M_j`. Recorded in the pivot (scaled)
    ///     frame; both lanes share the scaling, so the differential cancels it.
    ///   * BTRAN: for each basis column `c` in `btran_cols`, the row of `B⁻¹` DUAL
    ///     to `c` = `e_{slot(c)}ᵀ·B⁻¹` where `slot(c) = basic_row[c]`. Its output is
    ///     indexed by CONSTRAINT ROW (already lane-invariant), and the scaled-frame
    ///     fixup uses `c`'s own column scale.
    ///
    /// Returns `None` on a shape mismatch. This is measurement scaffolding: a bug
    /// here can only mis-report, never touch a verdict (nothing on the solve path
    /// calls it).
    pub(crate) fn factor_probe(
        &self,
        cand: &Candidate,
        ftran_cols: &[usize],
        btran_cols: &[usize],
        lane: u8,
    ) -> Option<FactorProbe> {
        if lane > 2 || cand.basis.len() != self.m || cand.at.len() != self.cols {
            return None;
        }
        let mut seen_basis_columns = vec![false; self.cols];
        for &column in &cand.basis {
            if column >= self.cols || std::mem::replace(&mut seen_basis_columns[column], true) {
                return None;
            }
        }
        let t0 = std::time::Instant::now();
        let mut sx = Simplex::new(self, &self.lower, &self.upper);
        // Pin the lane BEFORE warm_start — warm_start triggers the refactorize
        // that reads the gate. A fresh Simplex crashes to its own basis, so the
        // warm hint is never `same` and the rebuild always runs on this lane.
        sx.bump_lu_override = Some(lane);
        sx.warm_start(self, &cand.basis, &cand.at, &self.lower, &self.upper);

        // FTRAN: B⁻¹·(column j of M) into sx.alpha over sx.nz, then REMAP to the
        // canonical basis-column order. `ftran` accumulates onto `alpha` and
        // assumes it is zero at rest, so restore the support afterwards.
        let mut ftran = Vec::with_capacity(ftran_cols.len());
        for &j in ftran_cols {
            if j >= self.cols {
                return None;
            }
            sx.ftran(self, j);
            // out[k] = coefficient of basis column cand.basis[k] = alpha[slot(c_k)].
            // Slots absent from the support read 0.0 (that column's coefficient is
            // zero). `basic_row[c]` is `Some` for every un-kicked basis column.
            let mut col = vec![0.0f64; self.m];
            for (k, &c) in cand.basis.iter().enumerate() {
                if let Some(slot) = sx.basic_row[c] {
                    col[k] = sx.alpha[slot];
                }
            }
            let nz = std::mem::take(&mut sx.nz);
            for &i in &nz {
                sx.alpha[i] = 0.0; // restore rest state for the next ftran
            }
            sx.nz = nz;
            sx.nz.clear();
            ftran.push(col);
        }

        // BTRAN: the row of B⁻¹ dual to each requested basis column, indexed by
        // constraint row (lane-invariant), with that column's own scaled fixup.
        let mut btran = Vec::with_capacity(btran_cols.len());
        for &c in btran_cols {
            if c >= self.cols {
                return None;
            }
            let Some(slot) = sx.basic_row[c] else {
                // Column not basic in this factorization (kicked); record zeros so
                // the two lanes stay index-aligned (a kick is itself a differential
                // invariant the caller checks separately).
                btran.push(vec![0.0f64; self.m]);
                continue;
            };
            sx.y_is_duals = false;
            sx.y.fill(0.0);
            sx.y[slot] = 1.0;
            sx.btran();
            let mut row = sx.y.clone();
            if self.scaled() {
                let d_c = self.val_mul[c];
                for (r, v) in row.iter_mut().enumerate() {
                    *v *= d_c * self.bnd_mul[self.n + r];
                }
            }
            btran.push(row);
        }

        let mut kicked_columns = cand
            .basis
            .iter()
            .copied()
            .filter(|&column| sx.basic_row[column].is_none())
            .collect::<Vec<_>>();
        kicked_columns.sort_unstable();
        if kicked_columns.len() != sx.refactor_kicked {
            return None;
        }

        Some(FactorProbe {
            ftran,
            btran,
            fill: sx.etas.entries(),
            bump_lu_used: sx.refactor_bump_lu_used,
            kicked: sx.refactor_kicked,
            kicked_columns,
            basis_order: sx.basis.clone(),
            secs: t0.elapsed().as_secs_f64(),
        })
    }

    #[track_caller]
    pub(crate) fn solve_bounded(
        &self,
        lower: &[f64],
        upper: &[f64],
        warm: Option<(&[usize], &[NbBound])>,
        deadline: Option<std::time::Instant>,
    ) -> Candidate {
        self.solve_bounded_with_mode(lower, upper, warm, WarmSolveMode::Normal, deadline)
    }

    /// Solve under tightened bounds with an explicit warm-basis policy.
    ///
    /// [`WarmSolveMode::PrimalAdvice`] is bounded preparatory work only.
    /// [`WarmSolveMode::PrimalProofContinuation`] takes the same direct-primal
    /// path but returns a verdict candidate that its caller must exactify just
    /// like a [`WarmSolveMode::Normal`] result.
    #[track_caller]
    pub(crate) fn solve_bounded_with_mode(
        &self,
        lower: &[f64],
        upper: &[f64],
        warm: Option<(&[usize], &[NbBound])>,
        warm_mode: WarmSolveMode,
        deadline: Option<std::time::Instant>,
    ) -> Candidate {
        debug_assert!(
            warm.is_some() || warm_mode == WarmSolveMode::Normal,
            "direct-primal warm modes require an adopted warm basis"
        );
        // ATTRIBUTION (measurement only, gated): charge this solve to the exact
        // `file:line` that asked for it. `#[track_caller]` chains through the
        // `solve_bounded` shim, so the location is the real search call site.
        // NOTE: `Location::caller()` must be called DIRECTLY in this
        // `#[track_caller]` body — inside a closure it resolves to the closure,
        // not to the propagated caller, and the whole site census collapses.
        if crate::attrib::on() {
            crate::attrib::record_solve_site(std::panic::Location::caller());
        }
        let _attrib = crate::attrib::on()
            .then(|| AttribLpStamp(std::time::Instant::now(), crate::attrib::level()));
        stats::bump(&stats::SOLVES);
        // ITERATION LEDGER: charge this solve to the phase live ON ENTRY. The
        // iterations it goes on to run are charged where they RUN, so a solve
        // that falls into recovery contributes its solve count here and part of
        // its iterations there — which is exactly the split to be shown.
        ledger_note_solve();
        let _t_solve = std::time::Instant::now();
        // Pooled solver state: reset-in-place is `Simplex::new` minus the ~25
        // allocations, at ~70k calls per proof. A warm caller keeps the pooled
        // basis + eta file across the boundary (cross-solve reuse; `warm_start`
        // validates the pair against the hint before trusting either).
        let mut sx: Box<Simplex> = match self.sx_cache.0.borrow_mut().take() {
            Some(mut b) if b.m == self.m && b.cols == self.cols => {
                b.reset(self, lower, upper, warm.is_some());
                b
            }
            _ => Box::new(Simplex::new(self, lower, upper)),
        };
        if iter_profile_enabled() {
            SB_POOL_NANOS.fetch_add(
                _t_solve.elapsed().as_nanos() as u64,
                std::sync::atomic::Ordering::Relaxed,
            );
        }
        // DSE weights CAN survive across solves the way the LU operator does — and it
        // is a mirage. The "16.1 -> 8.1 it/solve, Gurobi's level" this once measured
        // was an overflow artifact: persisted weights compounded to +inf, an infinite
        // weight scores its row 0 in the dual's leave scan, and the dual was EXITING
        // EARLY on primal-infeasible bases — the "saved" iterations were solves the
        // post-check then threw away wholesale (ok=32,757 / fail=37,362 on 70x52
        // s2026). With the weights capped (see the Forrest–Goldfarb note in
        // `dual_simplex`) the honest number is the REVERSE: stale weights price worse
        // than fresh units (22.1 vs 16.1 it/solve; wall 9.5s vs 7.3s on 70x52 s2026,
        // 10.3s vs 8.1s on 60x45 s7, 68.3s vs 54.2s on 70x52 s99) — a weight belongs
        // to a row SLOT, and the slot's meaning does not survive the basis changing
        // under it across solves. (B18: the persist arm and its env lever are
        // RETIRED — measured slower on the seeds it was tried on; the
        // overflow pathology was pre-cap and produced no wrong answers. The
        // numbers above are the surviving record of the reversal.)
        {
            // In place: identical to `vec![1.0; m]`, minus the allocation.
            sx.dse.resize(self.m, 1.0);
            sx.dse.fill(1.0);
        }
        // Adopt the cached LU operator: it represents the basis the previous
        // solve ended on — commonly exactly the warm hint the caller passes.
        sx.lu = self.lu_cache.0.borrow_mut().take();
        // TRIANGULAR CRASH FIRST — before any LU-install decision. These were
        // ordered the other way, and the crash gate's `sx.lu.is_none()` check
        // silently skipped the crash on every cold tall-LU solve that was not
        // `plain_cold`: at full depth (125,121 x 106,486 — the scale where the
        // crash matters most) the tall-LU arm installed a fresh engine and
        // phase 1 ran from the all-logical start (measured: 87k iterations in
        // 4h, unfinished, objective moved 17 times), while the same class at
        // w5 scale ran crash+eta walks 3x shorter. Layered-equality models
        // take the crash and KEEP the eta path (the operator handshake assumes
        // the identity crash, so the two cannot compose); models whose peel
        // declines — set-partition (air05: the singleton queue never seeds),
        // square-ish, everything else — fall through to exactly the historical
        // path, and the decline traces say why. The explicit `--lu`
        // force-lever keeps its meaning (LU path, no crash), as does
        // `plain_cold`'s cache-drop on success below.
        let crash_installed = warm.is_none()
            && !no_tri_crash()
            && !lu_enabled()
            && ((self.cols >= BIG_LP_COLS && self.m >= BIG_LP_ROWS)
                || force_tri_crash()
                || self.chain_lp()
                || self.eager_affine_crash)
            && {
                // The crash runs on the fresh eta state and never composes
                // with an LU operator: set any cached engine aside, and on
                // success hand it back for later warm solves (except on
                // `plain_cold`, whose documented cold-solve semantics drop it)
                // instead of losing it.
                let cached = sx.lu.take();
                let ok = sx.triangular_crash(self, self.range_logical_triangular_crash_enabled());
                if ok {
                    if !self.plain_cold {
                        *self.lu_cache.0.borrow_mut() = cached;
                    }
                } else {
                    sx.lu = cached;
                }
                ok
            };
        // A `plain_cold` instance runs the classic eta-file path bit-for-bit
        // (see the field's note): drop any engine a fallback left in the cache
        // (`try_cold_dual` installs its own when it needs one) and do not
        // create one — for its COLD (root) solve, whose optimal VERTEX seeds
        // the pump/dive/RINS chain and must stay the measured one.
        //
        // A WARM node re-solve on a WIDE-TALL LP is different: it seeds nothing
        // (it feeds a branching bound, re-derived exactly downstream), and the
        // eta inverse's DRIFT is precisely what stretches a set-partition node
        // LP — the same effect `try_cold_dual`'s note measures at the root
        // (2,904 LU pivots vs 9,886 on the eta file). So keep the LU engine for
        // wide-tall warm re-solves. Gated on `wide_tall` so the square-ish
        // ladder is byte-for-byte untouched; `AY_MILP_NO_NODE_LU` restores the
        // classic warm path for A/B. (Two streams landed this same rule
        // independently — air05 @60s measured 4,028 O(m·nnz) eta rebuilds
        // /12.84s against ~717 LU factors /0.62s; the truth tables agreed and
        // this side keeps the kill switch.)
        let node_lu = warm.is_some() && (self.wide_tall() || self.tall_lu()) && !no_node_lu();
        // COLD-ROOT LU BAND: the one place `plain_cold`'s eta pin is measured
        // WRONG. `node_lu` above already routes every WARM tall re-solve to the
        // FT engine, so on a tall model the only solve still on the eta file is
        // the cold root — and that is exactly the solve whose REFAC bill runs
        // 76% of LP time on hypothyroid-k1 (687 rebuilds / 89.7s) and returns NO
        // BOUND AT ALL inside 120s, where the same LP on the LU lane is Optimal
        // at 34.6s with bound -2902.852586. Band, not ray: see
        // `FloatLp::cold_root_lu` for the m=12..168,336 A/B behind 3,000 and
        // 8,192, and for why the ends of the range keep the eta file.
        //
        // Ordered AFTER the triangular crash on purpose. The crash and the LU
        // operator "cannot compose" (the note above), and the blunt
        // `--lu` force-lever suppresses the crash outright via
        // `!lu_enabled()` — which is what made neos-827175 (m=14,187, 10,512/
        // 10,512 equality rows peeled) look like an LU-lane loss when it was a
        // crash loss. This gate never fires when `crash_installed`, so a
        // layered-equality model keeps its crash AND its eta path.
        let cold_root_lu = warm.is_none() && self.plain_cold && self.cold_root_lu();
        if self.plain_cold && !lu_enabled() && !node_lu && !cold_root_lu {
            sx.lu = None;
        }
        if !crash_installed
            && sx.lu.is_none()
            && (lu_enabled()
                || cold_root_lu
                || ((self.wide_tall() || self.tall_lu()) && (!self.plain_cold || node_lu)))
        {
            sx.lu = Some(LuCache {
                eng: crate::lu::LuEngine::new(self.m),
                // A fresh engine represents B = -I: the all-logical basis.
                rep_basis: (self.n..self.n + self.m).collect(),
            });
        }
        bounded_setup::reset_cached_lu_basis(self, &mut sx, warm.is_none());
        let warm_started = warm.is_some();
        // LANE/CALLER ATTRIBUTION (trace only): the lane is fixed now (an LU
        // engine is installed or it is not); snapshot the eta-rebuild count so
        // the rebuilds this solve provokes can be charged to its lane + caller
        // on return. See `LANE_*`/`CALLER_*`.
        let trace_lane = trace_enabled();
        let lane_bucket = if sx.lu.is_some() {
            0 // LU operator backs the solve
        } else if warm_started {
            1 // eta-warm
        } else if self.plain_cold {
            2 // eta-cold-plain (vertex-seeding)
        } else {
            3 // eta-cold-other
        };
        let eta_before = if trace_lane {
            REFAC_COUNT.load(std::sync::atomic::Ordering::Relaxed) as u64
        } else {
            0
        };
        // Consume the caller's cutoff (arm-once). It only guides the WARM dual
        // walk's early stop; a cold solve gets no cutoff.
        let armed = self.cutoff.replace(f64::INFINITY);
        sx.cutoff = if warm_started { armed } else { f64::INFINITY };
        // CHAIN-SHAPE CLASSIFICATION (once per LP, on its first cold eta-path
        // solve — the bounds here are the root's, before branching fixes
        // anything). The BIG size class is never classified: its whole bundle
        // is already on and its path must stay byte-identical. See the
        // `chain_shape` field for the regime and the measurements.
        if let Some(census) = bounded_setup::classify_chain_shape(self, &sx, warm.is_none()) {
            if census.trace {
                eprintln!(
                    "--trace shape census: m={} n={} neq={} peeled={} \
                     candidate={} chain={}",
                    self.m,
                    self.n,
                    census.equalities,
                    census.peeled,
                    census.candidate,
                    census.is_chain
                );
            }
            self.chain_shape.set(if census.is_chain { 3 } else { 2 });
        }
        // (The triangular-crash attempt for cold big-LP / chain-shape solves
        // happens ABOVE, before the LU-install decision — see `crash_installed`.
        // It used to sit here, after it, and the `sx.lu.is_none()` gate then
        // silently skipped the crash on cold tall-LU solves.)
        if let Some((basis, at)) = warm {
            let _tw = iter_profile_enabled().then(std::time::Instant::now);
            sx.warm_start(self, basis, at, lower, upper);
            if let Some(tw) = _tw {
                SB_WARM_NANOS.fetch_add(
                    tw.elapsed().as_nanos() as u64,
                    std::sync::atomic::Ordering::Relaxed,
                );
            }
        }
        let iters_before = DUAL_ITERS.load(std::sync::atomic::Ordering::Relaxed);
        // CHAIN DISTRESS PROBE: the bundle is a RESCUE, not an optimization.
        // A chain-shaped LP (armed state 3) keeps the default path bit-for-bit
        // — but its cold eta-path walks run under a bounded iteration probe.
        // A healthy walk never notices (k=124's largest certified-run cold
        // walk: 4,953 iterations against the 20,000 budget); the k=546 grind
        // blows the budget in seconds instead of eating its whole deadline
        // slice (the deadline-Stopped variant was built first and measured
        // useless: every distress event consumed its full slice — 27s cut
        // round + 148s root — before promoting, and the retry inherited an
        // expired clock). On distress the bundle arms for the life of the LP
        // and THIS solve retries once from scratch: triangular-crash attempt +
        // `refactorize` peel preorder + Devex-from-0 on cold walks (k=546
        // root: Optimal in ~3.7s on the retry; either half alone leaves it
        // Stopped). The unconditional-fire variants were measured WORSE on
        // k=124, whose cold walks succeed: all-walks Devex loses
        // certification outright (postchk 114 -> 410, rim 77.7s, unknown
        // @592s) and cold-only Devex keeps it but grows the tree 48,123 ->
        // 92,015 / 222 -> 319s.
        let chain_distress_probe_iters = (warm.is_none()
            && sx.lu.is_none()
            && self.chain_shape.get() == 3
            && !no_tri_crash())
        .then(|| {
            resolve_chain_distress_probe_iters(self.chain_distress_probe_iters, chain_probe_iters)
        });
        let chain_probe = chain_distress_probe_iters.is_some_and(|iters| iters > 0);
        if let Some(iters) = chain_distress_probe_iters.filter(|&iters| iters > 0) {
            sx.probe_iters_left = iters;
        }
        let primal_before = stats::get(&stats::PRIMAL_ITERS);
        // SBPROFILE: everything above (pool adopt + `reset` + LU-install +
        // `warm_start`) is the per-solve SETUP; charge it before `run`.
        if iter_profile_enabled() {
            SB_SETUP_NANOS.fetch_add(
                _t_solve.elapsed().as_nanos() as u64,
                std::sync::atomic::Ordering::Relaxed,
            );
        }
        let mut status = sx.run(self, warm_started, warm_mode, deadline);
        if chain_probe {
            sx.probe_iters_left = u64::MAX;
            if trace_enabled() {
                eprintln!(
                    "--trace chain probe: cold walk {:?} after {} primal iters",
                    status,
                    stats::get(&stats::PRIMAL_ITERS) - primal_before
                );
            }
            if status == SimplexStatus::Stopped {
                // DISTRESS. Promote for the life of the LP; retry in-solve
                // only with time still on the clock (a genuine deadline stop
                // hands the armed bundle to the caller's own retry instead).
                self.chain_shape.set(1);
                if deadline.is_none_or(|d| std::time::Instant::now() < d) {
                    // ITERATION LEDGER: the probe walk above already spent its
                    // budget; this retry re-solves the same LP from scratch.
                    let _ledger_recover = PhaseScope::new_forced(PH_RECOVERY);
                    ledger_note_solve();
                    sx.reset(self, lower, upper, false);
                    if !no_tri_crash() {
                        sx.triangular_crash(self, self.range_logical_triangular_crash_enabled());
                    }
                    status = sx.run(self, false, WarmSolveMode::Normal, deadline);
                    if trace_enabled() {
                        eprintln!(
                            "--trace chain probe: bundle retry {:?} ({} primal iters total)",
                            status,
                            stats::get(&stats::PRIMAL_ITERS) - primal_before
                        );
                    }
                }
            }
        }
        {
            use std::sync::atomic::Ordering::Relaxed;
            let spent = DUAL_ITERS.load(Relaxed).wrapping_sub(iters_before);
            let (s, i) = if warm_started {
                (&WARM_SOLVES, &WARM_ITERS)
            } else {
                (&COLD_SOLVES, &COLD_ITERS)
            };
            s.fetch_add(1, Relaxed);
            i.fetch_add(spent, Relaxed);
        }
        // SBPROFILE: from here to return is EXTRACT (values/duals build, farkas
        // unscale, `Candidate` build with its basis/at clones, cache writes).
        // Gated so the timer read is not paid when the profiler is off.
        let _t_extract = iter_profile_enabled().then(std::time::Instant::now);
        let (values, duals) = sx.extract(self);
        let mut farkas = sx.farkas.take().unwrap_or_default();
        // The phase-I ray is per-row like the duals: y_r = R_r·y'_r. (Rigorous
        // consumers are sound for ANY ray — an unscaled one would only fail to
        // prove — but the unscale keeps the proof rate.)
        if self.scaled() {
            for (r, f) in farkas.iter_mut().enumerate() {
                *f *= self.bnd_mul[self.n + r];
            }
        }
        stats::SOLVE_NANOS.fetch_add(
            _t_solve.elapsed().as_nanos() as u64,
            std::sync::atomic::Ordering::Relaxed,
        );
        // The factorization survives to the next solve on this LP.
        *self.lu_cache.0.borrow_mut() = sx.lu.take();
        // (B18: the DSE persist cache write went with its arm; the default
        // path keeps the weights inside the pooled solver instead of
        // round-tripping an allocation per solve.)
        let out = Candidate {
            basis: sx.basis.clone(),
            at: sx.at.clone(),
            values,
            duals,
            farkas,
            farkas_verified: sx.farkas_verified,
            status,
        };
        if trace_lane {
            let eta_delta = (REFAC_COUNT.load(std::sync::atomic::Ordering::Relaxed) as u64)
                .wrapping_sub(eta_before);
            record_lane(lane_bucket, eta_delta);
        }
        *self.sx_cache.0.borrow_mut() = Some(sx);
        if let Some(te) = _t_extract {
            use std::sync::atomic::Ordering::Relaxed;
            SB_EXTRACT_NANOS.fetch_add(te.elapsed().as_nanos() as u64, Relaxed);
            SB_TOTAL_NANOS.fetch_add(_t_solve.elapsed().as_nanos() as u64, Relaxed);
            SB_SOLVES.fetch_add(1, Relaxed);
        }
        out
    }

    /// A LIMITED-ITERATION PROBE: run the dual simplex for at most `max_iters` pivots
    /// from `warm` and hand back the DUALS of whatever basis it holds when it stops.
    ///
    /// This is strong branching's LP, priced as what it is — ADVICE. `solve_bounded`
    /// answers "what is this child's optimum", and on a cut-laden degenerate LP that
    /// answer costs the dual's whole `2m+50` budget and then a primal fallback from
    /// scratch (qnet1 with the MIR extension: 294 iterations and 10.4ms per probe
    /// PAIR, and strong branching became the solve). Ranking candidates only needs
    /// the bound MOVEMENT a few pivots buy: the dual simplex holds dual feasibility
    /// at every iteration boundary, so stopping it early leaves a basis whose duals
    /// are a valid Neumaier–Shcherbina certificate — `safe_bound` is rigorous for
    /// ANY dual vector — just a weaker one. Weaker is fine: the number feeds
    /// pseudocost seeding and candidate comparison, never a prune.
    ///
    /// So: no primal fallback (that is the expensive thing being priced out), no
    /// optimality post-check (a BTRAN plus an O(nnz) sweep to certify a claim the
    /// caller does not need), no transactional rollback (a mid-pivot abort is
    /// already transactional per pivot, and the parent's basis would only make the
    /// duals STALER). The budget is a pure iteration COUNT — the probe's cost is the
    /// same on every run and every machine, which the tree's determinism requires.
    /// Arm cross-probe LU reuse for a bounded strong-branching sweep
    /// (`ProbeReuse`).
    /// The returned guard disarms and drops the snapshot on scope exit (RAII, so an
    /// early return in the caller still releases it). No-op unless this LP is on the
    /// wide/tall LU probe path and the kill switch is unset — the reuse is inert
    /// (byte-identical) on every other instance. Selection-lane only: it changes the
    /// probe's factor WORK, never its duals, its ranked pick, or any verdict.
    pub(crate) fn arm_probe_reuse(&self) -> Option<ProbeReuseGuard<'_>> {
        if !probe_lu_reuse_enabled() || !(self.wide_tall() || self.tall_lu()) {
            return None;
        }
        let mut r = self.probe_reuse.0.borrow_mut();
        r.armed = true;
        r.pristine = None;
        drop(r);
        Some(ProbeReuseGuard(self))
    }

    pub(crate) fn probe_duals(
        &self,
        lower: &[f64],
        upper: &[f64],
        warm: Option<(&[usize], &[NbBound])>,
        max_iters: u64,
        deadline: Option<std::time::Instant>,
    ) -> Vec<f64> {
        self.probe_duals_with_memory_status(lower, upper, warm, max_iters, deadline)
            .0
    }

    /// [`Self::probe_duals`] with a fail-closed memory verdict.
    ///
    /// Ordinary branch-selection advice may keep a stale-but-rigorous dual
    /// when an LU rebuild declines. The target-FSB harvest has an explicit
    /// memory contract instead: it discards that probe and therefore the whole
    /// fused selection attempt when the simplex memory guard fires.
    pub(crate) fn probe_duals_fail_closed(
        &self,
        lower: &[f64],
        upper: &[f64],
        warm: Option<(&[usize], &[NbBound])>,
        max_iters: u64,
        deadline: Option<std::time::Instant>,
    ) -> Option<Vec<f64>> {
        let (duals, out_of_memory) =
            self.probe_duals_with_memory_status(lower, upper, warm, max_iters, deadline);
        (!out_of_memory).then_some(duals)
    }

    fn probe_duals_with_memory_status(
        &self,
        lower: &[f64],
        upper: &[f64],
        warm: Option<(&[usize], &[NbBound])>,
        max_iters: u64,
        deadline: Option<std::time::Instant>,
    ) -> (Vec<f64>, bool) {
        stats::bump(&stats::SOLVES);
        // ITERATION LEDGER: every probe is strong-branching / pseudocost advice
        // by construction (that is the whole contract of this entry point), so
        // it tags itself rather than relying on each of its half-dozen call
        // sites to remember. The scope also covers the `dual_simplex` walk below,
        // so the probe's pivots land in `sb-probe` and not in the caller's phase.
        let _ledger = PhaseScope::new(PH_SB_PROBE);
        ledger_note_solve();
        let _t_solve = std::time::Instant::now();
        let mut sx: Box<Simplex> = match self.sx_cache.0.borrow_mut().take() {
            Some(mut b) if b.m == self.m && b.cols == self.cols => {
                // Same cross-solve keep as `solve_bounded`: a probe's FIRST pair
                // warm-starts the parent basis the pool still holds, so its
                // rebuild is skippable too (later probes pivot away and rebuild).
                b.reset(self, lower, upper, warm.is_some());
                b
            }
            _ => Box::new(Simplex::new(self, lower, upper)),
        };
        sx.dse.resize(self.m, 1.0);
        sx.dse.fill(1.0);
        // Adopt the cached LU operator exactly as `solve_bounded` does: the probe
        // warm-starts, and `warm_start`'s refactorize is free on a basis match.
        sx.lu = self.lu_cache.0.borrow_mut().take();
        // Probes are WARM solves — same rule as `solve_bounded`: the classic
        // pin protects vertex-choice (cold) answers, and a wide-and-tall LP's
        // probes take the engine (each probe re-warms the SAME parent basis,
        // which the engine's basis-match skip makes nearly free where the eta
        // path pays a full rebuild per probe).
        let classic_pin =
            self.plain_cold && (warm.is_none() || !(self.wide_tall() || self.tall_lu()));
        if classic_pin && !lu_enabled() {
            sx.lu = None; // classic instance: probes stay on the eta path too
        }
        if sx.lu.is_none()
            && (lu_enabled() || ((self.wide_tall() || self.tall_lu()) && !classic_pin))
        {
            sx.lu = Some(LuCache {
                eng: crate::lu::LuEngine::new(self.m),
                rep_basis: (self.n..self.n + self.m).collect(),
            });
        }
        // CROSS-PROBE LU REUSE (see `ProbeReuse`): while a strong-branch sweep
        // is armed, restore the pristine parent factorization into the working
        // operator so this probe's `warm_start` takes the `rep_basis` match-skip
        // instead of re-factoring the basis the PREVIOUS probe's dual walk pivoted
        // away from. The snapshot is a fresh `factor()` output, so the restored
        // operator is bit-identical to the re-factor it replaces. `armed` is set
        // only inside an explicit RAII guard, so every other solve skips this.
        let reuse_armed = self.probe_reuse.0.borrow().armed;
        if reuse_armed {
            if let Some(cache) = sx.lu.as_mut() {
                let r = self.probe_reuse.0.borrow();
                if let Some(p) = r.pristine.as_ref() {
                    cache.eng.clone_from(&p.eng);
                    cache.rep_basis.clone_from(&p.rep_basis);
                }
            }
        }
        // Warm path only, so `solve_bounded`'s cold reset-to-identity dance is not needed.
        if sx.lu.is_some() {
            sx.sync_lu_counters();
        }
        // LANE/CALLER ATTRIBUTION (trace only): probes are their own lane
        // buckets (4 = LU-backed, 5 = eta) and their own caller (sb-probe),
        // charged the eta rebuilds this probe provokes.
        let trace_lane = trace_enabled();
        let lane_bucket = if sx.lu.is_some() { 4 } else { 5 };
        let _caller = trace_lane.then(|| CallerScope::new(2));
        let eta_before = if trace_lane {
            REFAC_COUNT.load(std::sync::atomic::Ordering::Relaxed) as u64
        } else {
            0
        };
        if let Some((basis, at)) = warm {
            sx.warm_start(self, basis, at, lower, upper);
            // CROSS-PROBE LU REUSE: capture the FIRST fresh factorization of the
            // parent basis (`updates() == 0` means `warm_start` just factored it,
            // not skipped-with-updates or FT-adopted) as the pristine snapshot every
            // later probe restores. All fresh factors of one basis are bit-identical,
            // so this makes the reuse a no-op on the numbers — only the work moves.
            if reuse_armed {
                let mut r = self.probe_reuse.0.borrow_mut();
                if r.pristine.is_none() {
                    if let Some(cache) = sx.lu.as_ref() {
                        if cache.eng.updates() == 0 && cache.rep_basis == sx.basis {
                            r.pristine = Some(LuCache {
                                eng: cache.eng.clone(),
                                rep_basis: cache.rep_basis.clone(),
                            });
                        }
                    }
                }
            }
            sx.recompute_xb(self);
            let _cap = IterCap::set(max_iters);
            // The return value is deliberately ignored: "finished" and "stopped" both
            // leave a consistent basis, and the duals below certify a valid bound
            // either way. (Returning the flag so the caller records only finished-or-
            // moved probes was built and measured WORSE — see the recording site in
            // `bab.rs`: the truncated zeros turn out to be load-bearing.)
            let budget = 2 * self.m + 50;
            let _ = sx.dual_simplex(self, deadline, budget);
        }
        let (_values, duals) = sx.extract(self);
        stats::SOLVE_NANOS.fetch_add(
            _t_solve.elapsed().as_nanos() as u64,
            std::sync::atomic::Ordering::Relaxed,
        );
        if trace_lane {
            let eta_delta = (REFAC_COUNT.load(std::sync::atomic::Ordering::Relaxed) as u64)
                .wrapping_sub(eta_before);
            record_lane(lane_bucket, eta_delta);
        }
        let out_of_memory = sx.oom;
        *self.lu_cache.0.borrow_mut() = sx.lu.take();
        *self.sx_cache.0.borrow_mut() = Some(sx);
        (duals, out_of_memory)
    }
}

/// The LU engine plus the basis its operator currently represents — cached on
/// the `FloatLp` so a factorization SURVIVES across node re-solves. A child
/// adopts its parent's final basis, which is exactly what the cached operator
/// (base factorization plus absorbed updates) represents, so the per-node
/// refactorization is skipped on basis match — the whole point of
/// Forrest–Tomlin over a rebuild-every-time scheme.
struct LuCache {
    eng: crate::lu::LuEngine,
    /// The basis (column per row slot) the operator represents.
    rep_basis: Vec<usize>,
}

/// Cache cell: cloning an LP (the pump does, per call) yields an EMPTY cache —
/// a fresh engine costs one peel-fast factor, a deep clone costs fill-size
/// memory for a lane that immediately diverges.
struct LuCacheCell(std::cell::RefCell<Option<LuCache>>);

/// Same take/put + Clone-to-None protocol as `LuCacheCell`, for the pooled `Simplex`.
struct SxCell(std::cell::RefCell<Option<Box<Simplex>>>);
impl Clone for SxCell {
    fn clone(&self) -> Self {
        SxCell(std::cell::RefCell::new(None))
    }
}

impl Clone for LuCacheCell {
    fn clone(&self) -> Self {
        LuCacheCell(std::cell::RefCell::new(None))
    }
}

/// CROSS-PROBE LU REUSE for a bounded strong-branching sweep.
///
/// A strong-branch node probes k candidate row-splits, two children each, and
/// EVERY one of those 2k probes warm-starts the SAME parent basis. But each
/// probe's bounded dual walk pivots the shared cached operator away from the
/// parent basis, so the NEXT probe's `warm_start` finds a mismatched `rep_basis`
/// and pays a full O(m·nnz) re-factor — measured on air05 as ~1,876 factors of
/// ~1,920 probes (BASISDIFF 16-31 + 32+), the throughput half of the node cost.
///
/// This caches ONE fresh factorization of the parent basis (captured the first
/// time a probe factors it, i.e. `updates() == 0`), so every later probe restores
/// it with an O(fill) `clone_from` and takes the `rep_basis` match-skip instead of
/// re-factoring. BIT-IDENTICAL by construction: the snapshot is exactly what
/// `factor()` produces for that basis, and all fresh factors of one basis are
/// bit-identical, so the restored operator equals the re-factor it replaces —
/// the probe's duals, the ranked pick, and the resulting tree are unchanged;
/// only the factor WORK is saved. Armed only around an explicit caller probe
/// loop (`wide_tall`/`tall_lu` path), so every other solve is byte-identical
/// and never consults it.
struct ProbeReuse {
    /// Set around one bounded probe loop; probes reuse only while armed.
    armed: bool,
    /// A fresh factorization of the parent basis, captured on the first probe that
    /// factors it (`updates() == 0`). `None` until then and after disarm.
    pristine: Option<LuCache>,
}

struct ProbeReuseCell(std::cell::RefCell<ProbeReuse>);
impl Clone for ProbeReuseCell {
    fn clone(&self) -> Self {
        // Same Clone-to-empty protocol as the other caches: a cloned LP starts
        // disarmed with no snapshot.
        ProbeReuseCell(std::cell::RefCell::new(ProbeReuse {
            armed: false,
            pristine: None,
        }))
    }
}

/// Kill switch for cross-probe LU reuse (`AY_MILP_NO_PROBE_LU_REUSE=1`). Default
/// on: the reuse is bit-identical, so the only reason to disable it is A/B timing.
fn probe_lu_reuse_enabled() -> bool {
    // B22: retired; the reuse is bit-identical and stays on.
    true
}

/// RAII arm/disarm guard for cross-probe LU reuse, so an early return or panic
/// still releases the snapshot.
pub(crate) struct ProbeReuseGuard<'a>(&'a FloatLp);
impl Drop for ProbeReuseGuard<'_> {
    fn drop(&mut self) {
        let mut r = self.0.probe_reuse.0.borrow_mut();
        r.armed = false;
        r.pristine = None;
    }
}

/// The product-form inverse, `B^{-1} = E_k ··· E_1 (-I)`, stored FLAT.
///
/// One eta used to be its own struct with its own heap `Vec` of `(usize, f64)`
/// pairs — an allocation per pivot and a pointer chase per eta on every
/// FTRAN/BTRAN, which is the hottest loop in the engine. The flat layout keeps
/// the SAME etas with the SAME entries in the SAME order (so every float op is
/// bit-identical); only the memory moved: entries live in one `idx`/`val` pair
/// of arrays, delimited per eta by `start`.
#[derive(Default)]
struct EtaFile {
    /// Pivot row slot of each eta.
    p: Vec<u32>,
    /// `1 / alpha[p]` of each eta.
    diag: Vec<f64>,
    /// Eta `k`'s entries occupy `idx[start[k]..start[k + 1]]` (and `val` alike).
    /// Always `len() + 1` long, `start[0] == 0`.
    start: Vec<u32>,
    /// Row of each entry — `(row, -alpha[row]/alpha[p])` for non-zeros with `row != p`.
    idx: Vec<u32>,
    val: Vec<f64>,
}

impl EtaFile {
    fn new() -> Self {
        Self {
            p: Vec::new(),
            diag: Vec::new(),
            start: vec![0],
            idx: Vec::new(),
            val: Vec::new(),
        }
    }

    fn len(&self) -> usize {
        self.p.len()
    }

    /// Total entry count across all etas (the old `sum(e.vec.len())`).
    fn entries(&self) -> usize {
        self.idx.len()
    }

    fn clear(&mut self) {
        self.p.clear();
        self.diag.clear();
        self.start.clear();
        self.start.push(0);
        self.idx.clear();
        self.val.clear();
    }

    /// Append one entry of the eta currently being built.
    #[inline]
    fn push_entry(&mut self, i: usize, v: f64) {
        self.idx.push(i as u32);
        self.val.push(v);
    }

    /// Seal the eta whose entries were just pushed.
    #[inline]
    fn finish_eta(&mut self, p: usize, diag: f64) {
        self.p.push(p as u32);
        self.diag.push(diag);
        self.start.push(self.idx.len() as u32);
    }
}

/// Result of `bump_eliminate` — a sparse LU factorization of the peel's
/// non-triangular core ("bump"), destined for ETA-FILE EMISSION (see the
/// call site in `refactorize`): the file gains one L-eta per pivot in stage
/// order (unit diagonal, entries `-l_ik`), then one U-eta per pivot in
/// REVERSED stage order (diagonal `1/u_kk`, entries `-u_ik/u_kk` at earlier
/// pivot rows). Applied in file order to a bump column that sequence yields
/// exactly its unit vector — the same operator contract as the PFI segment it
/// replaces — at `nnz(L) + nnz(U)` entries instead of product-form fill.
struct BumpFactor {
    /// Pivot sequence: (pivot row, local column index, pivot value `u_kk`).
    stages: Vec<(u32, u32, f64)>,
    /// L entries per stage: (row, multiplier `v_row / u_kk`), rows both open
    /// (later-stage pivots) and spectator (reserved back rows, front dust).
    lcols: Vec<Vec<(u32, f64)>>,
    /// U history per LOCAL COLUMN: (stage index that removed it, value
    /// `u_ik`). Only pivoted columns' histories are emitted.
    uhist: Vec<Vec<(u32, f64)>>,
    /// Local column indexes with no admissible pivot (numerically dependent);
    /// the caller's logical repair covers their rows, as in the PFI path.
    kicked: Vec<u32>,
}

/// `AY_MILP_BUMP_SCC=1`: print the SCC-size histogram of the bump block on
/// each rebuild. Diagnostic-only; gates the BTF block-factor program (many
/// medium SCCs ⇒ block substitution wins, one giant SCC ⇒ it does not).
fn bump_scc_enabled() -> bool {
    // B22: retired (diagnostic served its BTF-gating purpose).
    false
}

/// The block-triangular structure of the bump `acols` (transformed bump
/// columns): greedy bipartite matching (col → open row; augment the few misses
/// with an iterative Kuhn DFS), then the directed dependency digraph (col `c` →
/// col `c′` when `c` has a nonzero in `c′`'s matched row) whose SCCs are the
/// Dulmage–Mendelsohn fine blocks — the irreducible cores the BTF block factor
/// isolates. Iterative Tarjan (47k-safe).
///
/// Returns `(col_block, block_topo_order, col_row)`:
/// - `col_block[c]` — SCC id of column `c`, numbered in Tarjan COMPLETION order
///   (0 = the SCC Tarjan finalized first = a condensation SINK).
/// - `block_topo_order` — the block ids in the order the BTF lane must emit them:
///   a topological order of the condensation (SOURCES first). Tarjan finalizes
///   SCCs in reverse-topological order, so this is simply the completion order
///   reversed. Emitting sources first makes each block's spill into a LATER
///   block's rows ride as sub-diagonal L content (the block-lower-triangular
///   invariant the per-block factor relies on). Direction confirmed empirically
///   by the lane-1-vs-2 differential.
/// - `col_row[c]` — the open row matched to column `c` (`usize::MAX` if the
///   augmenting search left it unmatched: structurally dependent, kicked).
///
/// The matching (and therefore the block structure and every `block_open` mask
/// the BTF lane derives from `col_row`) is restricted to the `open` rows — the
/// bump's own mid rows — exactly the pivot set `bump_eliminate` runs over. A
/// column's entries in NON-open rows (already-pivoted head rows, reserved back
/// rows) are spectators that ride along as L content; matching a bump column to
/// one of those would let a per-block factor pivot on an already-owned row and
/// strand the bump's real row uncovered.
fn bump_scc_blocks(
    m: usize,
    acols: &[Vec<(u32, f64)>],
    open: &[bool],
) -> (Vec<u32>, Vec<u32>, Vec<usize>) {
    let nb = acols.len();
    // --- bipartite matching: col -> open row (greedy, then augment misses) ---
    let mut col_row = vec![usize::MAX; nb];
    let mut row_col = vec![usize::MAX; m];
    for (c, col) in acols.iter().enumerate() {
        for &(r, _) in col {
            if open[r as usize] && row_col[r as usize] == usize::MAX {
                col_row[c] = r as usize;
                row_col[r as usize] = c;
                break;
            }
        }
    }
    // Augment the columns greedy missed (iterative Kuhn DFS).
    for c0 in 0..nb {
        if col_row[c0] != usize::MAX {
            continue;
        }
        let mut seen = vec![false; m];
        // stack frames: (col, next entry index in acols[col])
        let mut stack: Vec<(usize, usize)> = vec![(c0, 0)];
        let mut augmented = false;
        while let Some(&mut (c, ref mut ei)) = stack.last_mut() {
            let col = &acols[c];
            let mut advanced = false;
            while *ei < col.len() {
                let r = col[*ei].0 as usize;
                *ei += 1;
                if !open[r] || seen[r] {
                    continue;
                }
                seen[r] = true;
                let occ = row_col[r];
                if occ == usize::MAX {
                    // free row: unwind, flipping the alternating path
                    let mut rr = r;
                    for &(pc, pei) in stack.iter().rev() {
                        let prev = col_row[pc];
                        col_row[pc] = rr;
                        row_col[rr] = pc;
                        let _ = pei;
                        rr = prev;
                        if rr == usize::MAX {
                            break;
                        }
                    }
                    augmented = true;
                    advanced = true;
                    break;
                } else {
                    stack.push((occ, 0));
                    advanced = true;
                    break;
                }
            }
            if augmented {
                break;
            }
            if !advanced {
                stack.pop();
            }
        }
    }
    // --- directed digraph on matched columns; iterative Tarjan SCC ---
    // adjacency: c -> row_col[r] for each (r,_) in acols[c] with a matched owner.
    let mut index = vec![u32::MAX; nb];
    let mut low = vec![0u32; nb];
    let mut onstk = vec![false; nb];
    let mut stk: Vec<u32> = Vec::new();
    let mut comp = vec![u32::MAX; nb];
    let mut nblocks = 0u32;
    let mut idx = 0u32;
    // iterative Tarjan: frame (node, edge-cursor)
    for s in 0..nb {
        if index[s] != u32::MAX {
            continue;
        }
        let mut call: Vec<(u32, usize)> = vec![(s as u32, 0)];
        while let Some(&mut (v, ref mut ci)) = call.last_mut() {
            let vu = v as usize;
            if *ci == 0 {
                index[vu] = idx;
                low[vu] = idx;
                idx += 1;
                stk.push(v);
                onstk[vu] = true;
            }
            let col = &acols[vu];
            let mut recursed = false;
            while *ci < col.len() {
                let r = col[*ci].0 as usize;
                *ci += 1;
                let w = row_col[r];
                if w == usize::MAX {
                    continue;
                }
                if index[w] == u32::MAX {
                    call.push((w as u32, 0));
                    recursed = true;
                    break;
                } else if onstk[w] {
                    if index[w] < low[vu] {
                        low[vu] = index[w];
                    }
                }
            }
            if recursed {
                continue;
            }
            if low[vu] == index[vu] {
                let bid = nblocks;
                loop {
                    let w = stk.pop().unwrap();
                    onstk[w as usize] = false;
                    comp[w as usize] = bid;
                    if w == v {
                        break;
                    }
                }
                nblocks += 1;
            }
            call.pop();
            if let Some(&mut (p, _)) = call.last_mut() {
                if low[vu] < low[p as usize] {
                    low[p as usize] = low[vu];
                }
            }
        }
    }
    // Tarjan completes SCCs in reverse-topological order; emit sources first.
    let block_topo_order: Vec<u32> = (0..nblocks).rev().collect();
    (comp, block_topo_order, col_row)
}

/// READ-ONLY diagnostic (no operator change): a one-line SCC-size histogram of
/// the bump block, over the block structure `bump_scc_blocks` computes (matched
/// over the `open` rows, the same set the factor pivots on).
fn bump_scc_histogram(m: usize, acols: &[Vec<(u32, f64)>], open: &[bool]) -> String {
    let nb = acols.len();
    if nb == 0 {
        return "BUMP_SCC empty".to_string();
    }
    let (comp, block_order, col_row) = bump_scc_blocks(m, acols, open);
    let nblocks = block_order.len();
    let unmatched = col_row.iter().filter(|&&r| r == usize::MAX).count();
    let mut sizes = vec![0usize; nblocks];
    for &b in &comp {
        sizes[b as usize] += 1;
    }
    let mut buckets = [0usize; 7]; // 1, 2-9, 10-99, 100-999, 1k-5k, 5k-10k, 10k+
    let mut largest = 0usize;
    for &sz in &sizes {
        largest = largest.max(sz);
        let b = match sz {
            1 => 0,
            2..=9 => 1,
            10..=99 => 2,
            100..=999 => 3,
            1000..=4999 => 4,
            5000..=9999 => 5,
            _ => 6,
        };
        buckets[b] += 1;
    }
    format!(
        "BUMP_SCC nb={nb} unmatched={unmatched} sccs={nblocks} LARGEST={largest} | hist[1]={} [2-9]={} [10-99]={} [100-999]={} [1k-5k]={} [5k-10k]={} [10k+]={}",
        buckets[0], buckets[1], buckets[2], buckets[3], buckets[4], buckets[5], buckets[6]
    )
}

/// Right-looking Markowitz elimination of the bump block, threshold-pivoted
/// (`|v| > tol` absolute and `|v| >= 0.1 * max|open entries of the column|`
/// relative, the classical stability/sparsity trade; the PFI loop's greedy
/// max-|alpha| is the degenerate threshold 1.0). Pivots are restricted to
/// `open` rows; entries in non-open rows ride along as pure L content.
///
/// Deterministic: candidate selection is a lazy min-heap on (column nnz,
/// column index) examining at most 8 live candidates (the `lu.rs` bounded
/// Suhl search), Markowitz cost `(rcount-1)*(nnz-1)` with ties broken toward
/// larger magnitude, then smaller column, then smaller row.
///
/// Returns `None` when accumulated L+U fill exceeds `entry_cap` — the caller
/// treats that exactly like the PFI fill-guard breach (slot-order retry).
fn bump_eliminate(
    m: usize,
    mut acols: Vec<Vec<(u32, f64)>>,
    open: &[bool],
    tol: f64,
    entry_cap: usize,
) -> Option<BumpFactor> {
    use std::cmp::Reverse;
    use std::collections::BinaryHeap;
    let b = acols.len();
    let mut openw = open.to_vec();
    let mut alive = vec![true; b];
    let mut copen = vec![0u32; b];
    let mut rcount = vec![0u32; m];
    // Open-row pattern SUPERSET (stale column ids allowed, re-validated on
    // use) — the pivot-row enumeration, exactly as `lu.rs` keeps it.
    let mut arows: Vec<Vec<u32>> = vec![Vec::new(); m];
    for (c, col) in acols.iter().enumerate() {
        let mut co = 0u32;
        for &(r, _) in col {
            if openw[r as usize] {
                co += 1;
                rcount[r as usize] += 1;
                arows[r as usize].push(c as u32);
            }
        }
        copen[c] = co;
    }
    let mut kicked: Vec<u32> = Vec::new();
    let mut remaining = 0usize;
    for c in 0..b {
        if copen[c] == 0 {
            alive[c] = false;
            kicked.push(c as u32);
        } else {
            remaining += 1;
        }
    }
    let mut heap: BinaryHeap<Reverse<(u32, u32)>> = BinaryHeap::new();
    for c in 0..b {
        if alive[c] {
            heap.push(Reverse((acols[c].len() as u32, c as u32)));
        }
    }
    let mut stages: Vec<(u32, u32, f64)> = Vec::with_capacity(remaining);
    let mut lcols: Vec<Vec<(u32, f64)>> = Vec::with_capacity(remaining);
    let mut uhist: Vec<Vec<(u32, f64)>> = vec![Vec::new(); b];
    let mut wval = vec![0.0f64; m];
    let mut wtag = vec![0u8; m];
    let mut seen = vec![false; b];
    let mut lu_nnz = 0usize;

    /// Best admissible pivot in one column: `(markowitz, |v|, row, v)`.
    fn eval_col(
        ents: &[(u32, f64)],
        openw: &[bool],
        rcount: &[u32],
        tol: f64,
    ) -> Option<(u64, f64, u32, f64)> {
        let mut cmax = 0.0f64;
        for &(r, v) in ents {
            if openw[r as usize] {
                let a = v.abs();
                if a > cmax {
                    cmax = a;
                }
            }
        }
        if cmax <= tol {
            return None;
        }
        let floor = 0.1 * cmax;
        let cn = ents.len() as u64 - 1;
        let mut best: Option<(u64, f64, u32, f64)> = None;
        for &(r, v) in ents {
            if !openw[r as usize] {
                continue;
            }
            let a = v.abs();
            if a <= tol || a < floor {
                continue;
            }
            let mk = (rcount[r as usize] as u64 - 1) * cn;
            let better = match best {
                None => true,
                Some((bmk, ba, br, _)) => {
                    mk < bmk || (mk == bmk && (a > ba || (a == ba && r < br)))
                }
            };
            if better {
                best = Some((mk, a, r, v));
            }
        }
        best
    }

    while remaining > 0 {
        // ---- pivot selection (bounded Markowitz over the lazy heap) ----
        let mut cands: Vec<(u32, u32)> = Vec::with_capacity(8);
        while cands.len() < 8 {
            let Some(Reverse((cnt, c))) = heap.pop() else {
                break;
            };
            if !alive[c as usize] || acols[c as usize].len() as u32 != cnt {
                continue; // stale entry
            }
            if cands.iter().any(|&(_, cc)| cc == c) {
                continue;
            }
            cands.push((cnt, c));
        }
        // (markowitz, col, |v|, row, v); deterministic tie-breaks.
        let mut best: Option<(u64, u32, f64, u32, f64)> = None;
        let consider = |mk: u64,
                        c: u32,
                        a: f64,
                        r: u32,
                        v: f64,
                        best: &mut Option<(u64, u32, f64, u32, f64)>| {
            let better = match *best {
                None => true,
                Some((bmk, bc, ba, br, _)) => {
                    mk < bmk
                        || (mk == bmk && (a > ba || (a == ba && (c < bc || (c == bc && r < br)))))
                }
            };
            if better {
                *best = Some((mk, c, a, r, v));
            }
        };
        for &(_, c) in &cands {
            if let Some((mk, a, r, v)) = eval_col(&acols[c as usize], &openw, &rcount, tol) {
                consider(mk, c, a, r, v, &mut best);
            }
        }
        if best.is_none() {
            // None of the low-count candidates admissible: sweep everything
            // live before declaring the rest dependent.
            for c in 0..b {
                if !alive[c] {
                    continue;
                }
                if let Some((mk, a, r, v)) = eval_col(&acols[c], &openw, &rcount, tol) {
                    consider(mk, c as u32, a, r, v, &mut best);
                }
            }
        }
        let Some((_, pc32, _, pr32, piv)) = best else {
            // No admissible pivot anywhere: every remaining column is
            // (numerically) dependent — kick them all, repair fills logicals.
            for c in 0..b {
                if alive[c] {
                    alive[c] = false;
                    kicked.push(c as u32);
                }
            }
            break;
        };
        for &(cnt, c) in &cands {
            if c != pc32 {
                heap.push(Reverse((cnt, c)));
            }
        }
        let (pr, pc) = (pr32 as usize, pc32 as usize);

        // ---- commit: L multipliers from the pivot column ----------------
        openw[pr] = false;
        alive[pc] = false;
        remaining -= 1;
        let col = std::mem::take(&mut acols[pc]);
        let mut lents: Vec<(u32, f64)> = Vec::with_capacity(col.len().saturating_sub(1));
        for &(r, v) in &col {
            if r as usize == pr {
                continue;
            }
            if openw[r as usize] {
                rcount[r as usize] -= 1; // column pc leaves the active block
            }
            lents.push((r, v / piv));
        }

        // ---- pivot row: extract U entries from every live column --------
        let pat = std::mem::take(&mut arows[pr]);
        let mut urow: Vec<(u32, f64)> = Vec::new();
        for &c in &pat {
            let ci = c as usize;
            if !alive[ci] || seen[ci] {
                continue;
            }
            seen[ci] = true;
            if let Some(k) = acols[ci].iter().position(|&(r, _)| r as usize == pr) {
                let (_, uval) = acols[ci].swap_remove(k);
                copen[ci] -= 1;
                uhist[ci].push((stages.len() as u32, uval));
                urow.push((c, uval));
            }
            // else: stale pattern id (cancelled earlier) — skip.
        }
        for &c in &pat {
            seen[c as usize] = false;
        }
        lu_nnz += lents.len() + urow.len();
        if lu_nnz > entry_cap {
            return None;
        }

        // ---- right-looking update: col_c -= u_val * lents ---------------
        for &(c, uval) in &urow {
            let ci = c as usize;
            if !lents.is_empty() {
                let colvec = std::mem::take(&mut acols[ci]);
                let mut tlist: Vec<u32> = Vec::with_capacity(colvec.len() + lents.len());
                for &(r, v) in &colvec {
                    wval[r as usize] = v;
                    wtag[r as usize] = 1;
                    tlist.push(r);
                }
                for &(r, lm) in &lents {
                    let ri = r as usize;
                    if wtag[ri] == 0 {
                        wtag[ri] = 2;
                        wval[ri] = -lm * uval;
                        tlist.push(r);
                    } else {
                        wval[ri] -= lm * uval;
                    }
                }
                let mut newcol = Vec::with_capacity(tlist.len());
                let mut co = copen[ci];
                for &r in &tlist {
                    let ri = r as usize;
                    let v = wval[ri];
                    let tag = wtag[ri];
                    wval[ri] = 0.0;
                    wtag[ri] = 0;
                    if v != 0.0 {
                        if tag == 2 && openw[ri] {
                            rcount[ri] += 1; // genuine fill in the active block
                            arows[ri].push(c);
                            co += 1;
                        }
                        newcol.push((r, v));
                    } else if tag == 1 && openw[ri] {
                        rcount[ri] -= 1; // exact cancellation drops out
                        co -= 1;
                    }
                }
                copen[ci] = co;
                acols[ci] = newcol;
            }
            if copen[ci] == 0 {
                // No open entries left: dependent on the pivots taken so far.
                alive[ci] = false;
                remaining -= 1;
                kicked.push(c);
            } else {
                heap.push(Reverse((acols[ci].len() as u32, c)));
            }
        }

        stages.push((pr32, pc32, piv));
        lcols.push(lents);
    }
    Some(BumpFactor {
        stages,
        lcols,
        uhist,
        kicked,
    })
}

struct Simplex {
    m: usize,
    cols: usize,
    /// The bounds THIS solve runs under — the model's own, or a branch-and-bound
    /// node's tightened ones. Every bound test below reads these, never the
    /// matrix's, so a node never sees its parent's box.
    lo: Vec<f64>,
    up: Vec<f64>,
    /// Dual steepest-edge reference weights, one per row slot. Seeded by
    /// `solve_bounded` from the LP's cache on warm solves; units otherwise.
    dse: Vec<f64>,
    etas: EtaFile,
    /// `refactorize`'s stash of the previous eta file (restored on a singular
    /// rebuild) — a field so its buffers are reused instead of reallocated.
    etas_spare: EtaFile,
    /// Value of the basic variable in each row slot.
    xb: Vec<f64>,
    /// Basic column of each row slot.
    basis: Vec<usize>,
    /// Row slot each column is basic in, else `None`.
    basic_row: Vec<Option<usize>>,
    /// Resting bound of each column.
    at: Vec<NbBound>,
    /// Scratch.
    y: Vec<f64>,
    cb: Vec<f64>,
    /// DEVEX reference weights: an estimate of the step length along each column. Used ONLY once
    /// a phase has stalled — see `STALL_BEFORE_BLAND`.
    w: Vec<f64>,
    since_refactor: usize,
    eta_nnz: usize,
    eta_nnz_cap: usize,
    /// Phase-I duals captured the moment infeasibility was declared.
    farkas: Option<Vec<f64>>,
    /// The leaving row's inverse row `B⁻ᵀe_r`, captured when the dual simplex
    /// found NO entering column (dual unbounded ⇒ primal infeasible). A Farkas
    /// candidate: `run` verifies it with the same rigorous interval check the
    /// tree uses before pruning, and on success skips the rollback-and-primal
    /// re-proof of an emptiness the dual already established. Fail-closed —
    /// a ray that does not verify falls through to the old path untouched.
    noenter_ray: Option<Vec<f64>>,
    /// Set when `farkas` passed `safe_farkas_proves_empty` against this solve's
    /// bounds inside `run` — exported on the Candidate so the tree does not pay
    /// for the same verification twice.
    farkas_verified: bool,
    /// The sparse LU / Forrest–Tomlin basis engine (`--lu`), replacing
    /// the eta file as the representation of `B^{-1}`. Installed by
    /// `solve_bounded` from the LP's cross-solve cache; advice-lane only, like
    /// everything here: a defect costs speed or tightness, never soundness.
    lu: Option<LuCache>,
    /// Eta rebuilds this SOLVE has completed — the trigger for the late LU
    /// promotion in `refactorize` (see `cold_lu_eta_rebuilds`). A count, not a
    /// cost estimate, because no deterministic cost unit survived measurement.
    ///
    /// Reset on every `reset`, INCLUDING `keep_factor=true`. A pooled warm
    /// solver's rebuild bill is a different lane's problem (`--warm-lu`,
    /// default off, and a documented incumbent-moving landmine); charging its
    /// cross-solve total to one solve's budget would promote the flip-LNS eval
    /// loop, which is not what any of this was measured on.
    eta_rebuilds: u32,
    /// Latched once this solve has finished with late promotion — either
    /// because it promoted, or because a promoted engine was dropped again
    /// (singular basis / fill decline). Without it, a solve whose LU factor
    /// keeps failing would re-install and re-drop an engine at every rebuild.
    lu_late_locked: bool,
    /// Support scratch for the LU-mode sparse BTRAN.
    ynz: Vec<usize>,
    /// Does `y` currently hold `c_B B^{-1}` under the TRUE costs for the
    /// current basis and inverse? Set by the sites that compute exactly that
    /// (`priced_out`, `dual_violations`, `extract`), cleared by anything that
    /// scribbles on `y` or changes the basis/inverse — so `extract` can REUSE
    /// the vector `priced_out` just computed instead of recomputing the very
    /// same floats (one full BTRAN per warm solve).
    y_is_duals: bool,
    /// FTRAN scratch — `alpha` (all-zero at rest) and its support `nz`.
    /// Shared by the pivot loops and `refactorize`; every user restores the
    /// rest-state before returning, so making them fields (instead of per-call
    /// allocations at ~70k solves a second) changes nothing about what is
    /// computed.
    alpha: Vec<f64>,
    nz: Vec<usize>,
    /// `recompute_xb`'s dense mirror of the nonbasic structural values
    /// (`lp.n` long; fully rebuilt on every use, no rest-state invariant).
    xtmp: Vec<f64>,
    /// Dual-simplex per-iteration scratch (see `dual_simplex` for each role).
    rho: Vec<f64>,
    arow: Vec<f64>,
    /// Ratio-test scratch for the masked/branchless BUILD (`AY_MILP_RT_MASKED`):
    /// `|d[j]/arow[j]|` for every column, computed in one branch-free pass so the
    /// per-column division vectorises, then read by the filtered push pass. Same
    /// IEEE division per column ⇒ byte-identical breakpoints. Default path unused.
    rt_ratio: Vec<f64>,
    /// Incremental DUAL RATIO-TEST ELIGIBILITY bitmask (`AY_MILP_NO_RT_KIND` kills
    /// it). The dual ratio-test build's per-column eligibility splits into a
    /// BASIS-STABLE part (`basic_row[j].is_none() && at[j] != Zero`, plus which
    /// bound the nonbasic column rests at) that changes ONLY on a basis change,
    /// and a per-pivot sign test on `arow[j]`. `rt_kind[j]` caches the stable part
    /// as `0` = ineligible (basic OR free-at-zero), `1` = nonbasic at LOWER, `2` =
    /// nonbasic at UPPER, so the pivot-hot scan reads ONE `u8` stream instead of
    /// the 16-byte `Option<usize>` `basic_row` load + the `at` load + the 5-arm
    /// match. Rebuilt once per `dual_simplex` entry (`rebuild_rt_kind`, before the
    /// pivot loop) and maintained incrementally at the two in-loop basis mutations
    /// (the bound-flip commit and the pivot commit); every other basis mutation
    /// (crash/warm-start/cold-dual/primal) precedes the next dual entry's rebuild.
    /// The entering column — hence every exact verdict — is byte-identical: the
    /// scan pushes the SAME `(d[j]/arow[j]).abs()` breakpoints, in the same
    /// ascending-`j` order, with the same first-minimal argmin.
    rt_kind: Vec<u8>,
    d: Vec<f64>,
    /// Partial-pricing cursor: the column where the next pricing sweep begins
    /// (cyclic). Persisting it across iterations is what makes sectional
    /// pricing scan the whole column range over time instead of re-scanning
    /// the same prefix.
    price_cursor: usize,
    /// Candidate-list pricing pool: columns a MAJOR (full) pricing pass found
    /// improving, re-priced cheaply on MINOR iterations until none improves,
    /// which forces the next major pass. Cleared on reset; survives rebound
    /// (a stale pool only hastens a refresh — every use re-prices).
    price_pool: Vec<u32>,
    /// The pivot lane's cost view: `lp.cost` scaled into the pivot frame
    /// (c'_j = c_j·2^cexp_j; a straight copy when scaling is off). Filled per
    /// `reset`, which also covers the pump's in-place cost mutation on its clone.
    pcost: Vec<f64>,
    /// DUAL COST PERTURBATION save buffer (`dual_perturb_mag`): the exact `pcost`
    /// slice at a perturbed dual walk's entry, restored on exit so the true costs
    /// come back bit-for-bit. Empty/unused on the un-perturbed path.
    pcost_save: Vec<f64>,
    /// TRUE while a `dual_simplex` walk is running on perturbed costs — the
    /// wrapper restores `pcost` from `pcost_save` on exit iff this is set.
    dual_perturb_active: bool,
    bp: Vec<(f64, u32)>,
    flips: Vec<u32>,
    wflip: Vec<f64>,
    /// Matrix-row support of `wflip` after the flip-set scatter, so the flip
    /// aggregate solve can go through the sparse `ftran_nz` (Gilbert–Peierls)
    /// instead of a dense O(m) `ftran`. May carry harmless duplicates (a row
    /// two flip columns both touch); `ftran_nz` reads each input row once and
    /// zeroes it, so a repeat gathers `+= 0.0` — byte-identical to the dense solve.
    wflipnz: Vec<usize>,
    tau: Vec<f64>,
    /// `run`'s warm-start snapshot buffers (rollback on a failed dual attempt).
    snap_basis: Vec<usize>,
    snap_at: Vec<NbBound>,
    /// `refactorize` scratch.
    rf_new_basis: Vec<usize>,
    rf_row_used: Vec<bool>,
    rf_cols: Vec<usize>,
    rf_deferred: Vec<usize>,
    /// Columns whose PIVOT-FRAME cost is non-zero (ascending), rebuilt with
    /// `pcost` in `reset`. The dual walk's per-iteration cutoff check sums
    /// `c·x` over the nonbasics through this list instead of scanning every
    /// column: a zero-cost nonbasic contributes exactly `0.0` to the sum (its
    /// value is finite — basics carry the infinities), so skipping it leaves
    /// the float result bit-identical while the scan drops from O(cols) to
    /// O(objective support) — on the market-split family that is 131 -> 1.
    nzcost: Vec<u32>,
    /// Objective cutoff (minimize form) for THIS solve; `INFINITY` = none. See
    /// `FloatLp::cutoff`. Copied out of the LP at the top of `solve_bounded`.
    cutoff: f64,
    /// Set by the dual when its monotone bound reached `cutoff` — the node is
    /// prunable and the walk stopped early.
    hit_cutoff: bool,
    /// TRUE while this solve was warm-started (set at the top of `run`).
    /// Read by the chain-shape Devex gate: COLD walks on a chain LP price
    /// Devex from iteration 0, warm repairs keep Dantzig (see
    /// `chain_devex_mode`).
    warm_run: bool,
    /// Per-walk DUAL ANATOMY accumulators (see `DUAL_ANAT_WALKS`). Live only
    /// while `AY_MILP_DUAL_ANATOMY` is set; reset at each `dual_simplex` entry
    /// and folded into the global buckets at every walk exit by
    /// `dual_anat_commit`. Ordinary (anatomy-off) runs never touch them.
    anat_dtheta: u64,
    anat_dstep: u64,
    anat_flip: u64,
    anat_z0: f64,
    /// Remaining primal iterations before this solve's walk is declared
    /// DISTRESSED (`u64::MAX` = no probe). Armed per solve in `solve_bounded`
    /// for cold eta-path walks on a chain-armed LP; see `chain_probe_iters`.
    probe_iters_left: u64,
    /// Does the ETA FILE currently represent `self.basis`? The engine's own
    /// invariant makes this true through every pivot (the eta is appended in the
    /// same act that moves the basis) and through every successful rebuild; the
    /// only desync sites are the ones that write `basis` WITHOUT touching the
    /// file — `warm_start` adopting a different hint (set false there; the
    /// rebuild it triggers sets it back) and a deferred singular rebuild after
    /// such an adoption (stays false; the file still represents the pre-hint
    /// basis). Carried across solves by `reset(keep_factor=true)`, this is what
    /// licenses CROSS-SOLVE ETA REUSE — see `warm_start`.
    factor_live: bool,
    /// This LP successfully installed the opt-in mixed
    /// `[B_EE 0; B_RE -I]` crash basis at least once.  Only that successful,
    /// instance-local event licenses the range-logical refactor preorder:
    /// reading the process-wide experiment flag here would make a declined
    /// crash perturb unrelated LPs and contaminate the A/B.
    range_logical_crash_installed: bool,
    /// How many solve boundaries the current eta file has been reused across
    /// since its last true rebuild (rebuild -> 0, each `warm_start` skip -> +1).
    /// `AY_MILP_ETA_GEN` caps it (chains compound: a reused file carries its
    /// parent's whole file plus its pivots, and each generation's FTRAN/BTRAN
    /// walks the longer file) — see the A/B journal at the skip.
    chain_gen: u32,
    /// STICKY out-of-memory flag: set the instant `refactorize`'s LU factor
    /// DECLINES (`FactorFail::OutOfBudget`) because its fill would cross the
    /// memory budget. Once set: `refactorize` becomes a no-op (it must NOT fall
    /// through to the eta rebuild — that is its own unbounded fill bomb), every
    /// pivot loop bails with `SimplexStatus::OutOfMemory`, and the solve is
    /// reported `Unknown{MemoryLimit}`. Cleared per solve in `reset`. Never set
    /// on any shipping instance (the 200M default is far above their factor
    /// fill), so every guard reading it is a dead branch on the corpus —
    /// byte-identical.
    oom: bool,
    /// DIFFERENTIAL-HARNESS SEAM (`factor_probe`): forces the `refactorize`
    /// bump-LU base-factor lane for this solve, bypassing the `--no-bump-lu`
    /// env read. `None` = production (the env expression decides — BYTE-IDENTICAL
    /// to the pre-seam gate); `Some(1)` = force the Markowitz bump-LU lane on
    /// (still subject to the peel being active AND the bump above `bump_lu_min`);
    /// `Some(0)` = force the PFI slot-order lane off. Never set on any shipping
    /// path — only `FloatLp::factor_probe` writes it, so every production solve
    /// reads `None` and the gate is unchanged.
    bump_lu_override: Option<u8>,
    /// THE FILL-RATE TRIP (`#bump-fill-trip`). Latched once this solve has SEEN a
    /// product-form bump whose fill rate contradicts the floor's premise.
    ///
    /// `bump_lu_min` gates the Markowitz bump lane on a COLUMN COUNT, justified by
    /// a claim about FILL: *"the crash-walk bases (~160-column bumps, already
    /// near-zero-fill) keep the measured PFI path"*. A forgone-cost census charged
    /// the entries the product form actually produced on that branch and measured
    /// **>= 326 per bump column**, so the premise is false for the charged
    /// population — and a paired root-LP A/B found the response NON-MONOTONE in the
    /// floor (512 -> 256 regresses neos-1582420, 256 -> 64 transforms it, while
    /// mzzv42z has the whole win by 256). No column threshold is right for both,
    /// which is what a mis-keyed gate looks like.
    ///
    /// So key on the quantity the claim is about. See `maybe_trip_bump_fill`.
    bump_fill_latched: bool,
    /// The number of dependent columns the last `refactorize` KICKED to their
    /// bounds (singular-basis repair). Surfaced so `factor_probe` can report it
    /// per lane — a differential invariant (both lanes factor the SAME basis, so
    /// they must kick the same count). Advisory diagnostic; nothing reads it on
    /// the production path.
    refactor_kicked: usize,
    /// Whether the final successful `refactorize` attempt used the bump-LU
    /// segment. Diagnostic provenance for `factor_probe`; production never
    /// reads it.
    refactor_bump_lu_used: bool,
}

/// Eta-file fill-cap multiplier (`the eta-cap-mult knob`, default 4 = the
/// shipped `4 * nnz` cap, byte-identical unset). MEASUREMENT LEVER for the
/// w5/full-depth root-LP refactorization wall: measured w5 fill is ≈365k
/// nnz/pivot, so `4 × nnz` on a 7.5M-nnz model forces a rebuild every ~85
/// pivots — prop885's w5 root LP measured REFAC = 87% of a 10,856s timeout
/// (1,271 rebuilds, ~7.3s each), the fill trigger, not cadence. Raising the
/// mult trades rebuild FREQUENCY against FTRAN/BTRAN cost over a denser eta
/// file; default unchanged pending a ladder. Advice-lane/perf-only: the eta
/// file's contents stay exact per-pivot algebra at any cap, and drift is
/// still guarded by the `primal_feasible`/`priced_out` post-checks plus
/// `verify_after`.
fn eta_cap_mult() -> usize {
    static N: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *N.get_or_init(|| crate::tune::count_opt(crate::tune::Knob::EtaCapMult).unwrap_or(4))
}

/// Generation cap for the cross-solve skip (`AY_MILP_ETA_GEN`, default in code).
fn eta_gen_cap() -> u32 {
    static N: std::sync::OnceLock<u32> = std::sync::OnceLock::new();
    *N.get_or_init(|| u32::MAX)
}

/// Age cap (absorbed pivots) for the cross-solve skip (`AY_MILP_ETA_AGE`). NOT
/// bound by the verify-loop deadlock contract that pins `refactorize`'s LU skip
/// to `verify_after()` — the verify loops call `refactorize` directly and this
/// skip lives only at `warm_start` (solve entry) — so the cap is a pure
/// drift/chain-length tradeoff, never allowed past `refactor_every()` (the
/// within-solve drift policy the reuse borrows its license from). Default 48,
/// measured monotone on pk1 (interleaved pairs, quiet machine): 20 -> 20.06/19.83,
/// 32 -> 19.98/19.80, 48 -> 19.91/19.72.
fn eta_reuse_age() -> usize {
    static N: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *N.get_or_init(|| {
        48
            // m = 0: this cache is process-wide with no LP in scope, so the cap
            // is the conservative small-m drift policy, as before the size gate.
            .min(refactor_every(0))
    })
}

impl Simplex {
    fn new(lp: &FloatLp, lower: &[f64], upper: &[f64]) -> Self {
        let nnz = lp.col_val.len();
        let mut s = Self {
            m: lp.m,
            cols: lp.cols,
            lo: lower.to_vec(),
            up: upper.to_vec(),
            dse: Vec::new(),
            etas: EtaFile::new(),
            etas_spare: EtaFile::new(),
            xb: vec![0.0; lp.m],
            basis: vec![0; lp.m],
            basic_row: vec![None; lp.cols],
            at: vec![NbBound::Zero; lp.cols],
            y: vec![0.0; lp.m],
            cb: vec![0.0; lp.m],
            w: vec![1.0; lp.cols],
            since_refactor: 0,
            eta_nnz: 0,
            farkas: None,
            noenter_ray: None,
            farkas_verified: false,
            lu: None,
            ynz: Vec::new(),
            y_is_duals: false,
            // Refactor early once the eta-file's fill rivals the matrix itself:
            // that is when a single FTRAN stops being cheap. The multiplier is
            // env-tunable (`the eta-cap-mult knob`, default 4 — see
            // `eta_cap_mult` for the measured w5 economics this lever probes).
            eta_nnz_cap: (eta_cap_mult() * nnz).max(16 * lp.m).max(1024),
            alpha: vec![0.0; lp.m],
            nz: Vec::with_capacity(64),
            xtmp: vec![0.0; lp.n],
            rho: vec![0.0; lp.m],
            arow: vec![0.0; lp.cols],
            rt_ratio: Vec::new(),
            rt_kind: vec![0u8; lp.cols],
            d: vec![0.0; lp.cols],
            pcost: vec![0.0; lp.cols],
            pcost_save: Vec::new(),
            dual_perturb_active: false,
            price_cursor: 0,
            price_pool: Vec::new(),
            bp: Vec::with_capacity(64),
            flips: Vec::with_capacity(16),
            wflip: vec![0.0; lp.m],
            wflipnz: Vec::with_capacity(64),
            tau: vec![0.0; lp.m],
            snap_basis: Vec::new(),
            snap_at: Vec::new(),
            rf_new_basis: Vec::new(),
            rf_row_used: Vec::new(),
            rf_cols: Vec::new(),
            rf_deferred: Vec::new(),
            nzcost: Vec::new(),
            cutoff: f64::INFINITY,
            hit_cutoff: false,
            warm_run: false,
            anat_dtheta: 0,
            anat_dstep: 0,
            anat_flip: 0,
            anat_z0: 0.0,
            probe_iters_left: u64::MAX,
            factor_live: false,
            range_logical_crash_installed: false,
            chain_gen: 0,
            oom: false,
            bump_lu_override: None,
            bump_fill_latched: false,
            refactor_kicked: 0,
            refactor_bump_lu_used: false,
            eta_rebuilds: 0,
            lu_late_locked: false,
        };
        s.reset(lp, lower, upper, false);
        s
    }

    /// Re-initialize to exactly the state `new` builds — the crash basis under
    /// the given bounds — reusing every allocation. This is what lets one
    /// `Simplex` be pooled across the ~70k `solve_bounded` calls of a proof:
    /// same values everywhere, zero mallocs.
    ///
    /// `keep_factor` (warm callers only): keep the pooled basis + eta file
    /// instead of crashing them. A warm child adopts its parent's FINAL basis,
    /// which is exactly the basis the pooled file still represents after the
    /// parent's solve — `warm_start` then skips its rebuild on a verified match
    /// (CROSS-SOLVE ETA REUSE, the classic-path twin of the LU arm's
    /// `rep_basis` skip). A cold caller (`keep_factor=false`) gets the crash
    /// basis, whose inverse the EMPTY eta file represents exactly.
    fn reset(&mut self, lp: &FloatLp, lower: &[f64], upper: &[f64], keep_factor: bool) {
        debug_assert!(self.m == lp.m && self.cols == lp.cols);
        // The big-LP rebuild-floor raise in `refactorize` is per-solve state…
        // `eta_cap_mult()` (not a literal 4) so `the eta-cap-mult knob` is a
        // LIVE lever: `new` seeds the cap through it but immediately calls
        // this, and every per-solve entry lands here — a hardcoded 4 made the
        // env ladder a silent no-op (the queued prop885 REFAC-wall ladder
        // would have measured nothing). Default 4 = byte-identical unset.
        self.eta_nnz_cap = (eta_cap_mult() * lp.col_val.len()).max(16 * lp.m).max(1024);
        // …but a warm caller carrying a live file past the static cap must
        // not re-trigger the nnz rebuild on entry (a heavy-basis file is its
        // own floor — the same storm `refactorize`'s raise kills, seen at the
        // w5 bound-closing nodes: every warm node adopted a 42M-entry file
        // against the 29.9M static cap).
        if keep_factor && self.factor_live && self.cols >= BIG_LP_COLS && self.m >= BIG_LP_ROWS {
            let floor = self.etas.entries() + (self.etas.entries() / 4).max(16 * self.m);
            if floor > self.eta_nnz_cap {
                self.eta_nnz_cap = floor;
            }
        }
        // The caller's box is ORIGINAL-frame; the solver runs in the pivot frame.
        // Multiplying by a power of two is exact; ±inf and lo==up are preserved.
        self.lo.clear();
        self.up.clear();
        if lp.scaled() {
            self.lo
                .extend((0..self.cols).map(|j| lower[j] * lp.bnd_mul[j]));
            self.up
                .extend((0..self.cols).map(|j| upper[j] * lp.bnd_mul[j]));
        } else {
            self.lo.extend_from_slice(lower);
            self.up.extend_from_slice(upper);
        }
        // The late-promotion budget is PER SOLVE (see the field's note): each
        // solve gets its own eta bill and its own one-shot switch.
        self.eta_rebuilds = 0;
        self.lu_late_locked = false;
        // Per solve, INCLUDING `keep_factor = true`. A pooled warm solver must not
        // inherit a predecessor's lane, or a node's factorization depends on which
        // nodes happened to run before it on the same `FloatLp` -- the same rule
        // `eta_rebuilds` states two fields up, for the same reason.
        self.bump_fill_latched = false;
        self.price_cursor = 0;
        self.price_pool.clear();
        self.pcost.clear();
        if lp.scaled() {
            // c'_j = c_j·C_j (logical costs are zero either way).
            self.pcost
                .extend((0..self.cols).map(|j| lp.cost[j] * lp.val_mul[j]));
        } else {
            self.pcost.extend_from_slice(&lp.cost);
        }
        self.nzcost.clear();
        self.nzcost.extend(
            self.pcost
                .iter()
                .enumerate()
                .filter(|&(_, &c)| c != 0.0)
                .map(|(j, _)| j as u32),
        );
        // Crash basis: every logical basic, every structural resting on a bound.
        // B is then -I, whose inverse is itself — the identity the eta-file is
        // seeded with, so the first FTRAN is already correct with zero etas.
        // Under `keep_factor` (a warm caller with a live file) the basis and its
        // file survive the pool boundary instead; `warm_start` re-validates the
        // pair against the hint before any of it is trusted.
        if !(keep_factor && self.factor_live) {
            self.basic_row.fill(None);
            for r in 0..self.m {
                self.basis[r] = lp.n + r;
                self.basic_row[lp.n + r] = Some(r);
            }
            self.etas.clear();
            self.since_refactor = 0;
            self.eta_nnz = 0;
            self.factor_live = true; // the empty file IS the crash inverse
            self.chain_gen = 0;
        }
        for j in 0..self.cols {
            self.at[j] = if lower[j].is_finite() {
                NbBound::Lower
            } else if upper[j].is_finite() {
                NbBound::Upper
            } else {
                NbBound::Zero
            };
        }
        self.xb.fill(0.0);
        self.y.fill(0.0);
        self.cb.fill(0.0);
        self.w.fill(1.0);
        self.farkas = None;
        self.noenter_ray = None;
        self.farkas_verified = false;
        self.lu = None;
        self.ynz.clear();
        self.y_is_duals = false;
        self.cutoff = f64::INFINITY;
        self.hit_cutoff = false;
        // Each solve starts with a fresh memory verdict: a prior solve's decline
        // must not leak into an unrelated (smaller) LP on the pooled `Simplex`.
        self.oom = false;
        // Scratch rest-state (all-zero), re-asserted cheaply.
        self.alpha.fill(0.0);
        self.nz.clear();
    }

    /// Adopt the cached engine's staleness counters, so the refactor triggers
    /// see the operator's true age rather than a fresh zero.
    fn sync_lu_counters(&mut self) {
        if let Some(cache) = self.lu.as_ref() {
            self.since_refactor = cache.eng.updates();
            self.eta_nnz = cache.eng.nnz();
        }
    }

    fn pivot_tol(&self) -> f64 {
        1e-9
    }
    /// The DUAL tolerance: how large a reduced cost has to be before a column is worth entering.
    /// A reduced cost is in OBJECTIVE units, so it is sized off the objective -- not off the
    /// largest number anywhere in the model. Sizing it off that made `gen`'s dual tolerance 2.0
    /// (its costs reach 2e9), so nothing ever priced in and phase I called a feasible LP
    /// infeasible on its first iteration.
    fn cost_tol(&self, lp: &FloatLp) -> f64 {
        // ORIGINAL-frame base: under equilibration the frame conversion is the
        // per-column vmul(j) at each comparison, so basing this on the scaled
        // stats would double-count the frame.
        1e-9 * (1.0 + lp.cost_scale)
    }
    /// The PRIMAL tolerance: how far outside its bound a variable may sit and still count as
    /// feasible. That is in row-activity units, so it is sized off the bounds.
    /// The PRIMAL tolerance: how far outside its bound a variable may sit and still count as
    /// feasible.
    ///
    /// Sized off the right-hand sides -- but with a CAP, because it is sized off the LARGEST of
    /// them and a single big number then licenses a big violation everywhere. Cuts are where this
    /// bites: a cut's right-hand side is relaxed to pay for whatever the derivation rounded, and
    /// those relaxations can be large. On qnet1 with a cut pool this tolerance reached 45 -- so the
    /// simplex accepted the CRASH BASIS, which violates a row bound by 45, as OPTIMAL, returned an
    /// all-zero point and a bound of zero for an LP whose optimum is 14274, and every cut separated
    /// from that round was separated from garbage.
    fn feas_tol(&self, lp: &FloatLp) -> f64 {
        // ORIGINAL-frame base — the per-column bmul(j) supplies the frame at
        // each comparison (basing this on scaled stats would double-count).
        1e-7 * (1.0 + lp.rhs_scale.min(FEAS_SCALE_CAP))
    }

    #[inline]
    fn nb_value(&self, _lp: &FloatLp, j: usize) -> f64 {
        match self.at[j] {
            NbBound::Lower => self.lo[j],
            NbBound::Upper => self.up[j],
            NbBound::Zero => 0.0,
        }
    }

    /// `w <- B^{-1} w`, in place — in split-borrow form, so callers may hand
    /// in one of `self`'s own vectors (`xb`, `tau`, `wflip`) without a clone.
    ///
    /// The eta walk is the hottest loop in the engine, so it runs UNCHECKED:
    /// every index it reads is an invariant of `EtaFile` construction (`p` and
    /// each entry row came out of an `nz` list of rows `< m == w.len()`, and
    /// `start` is maintained by `finish_eta`), asserted in debug builds.
    fn apply_inverse_parts(lu: Option<&mut LuCache>, etas: &EtaFile, w: &mut [f64]) {
        if let Some(cache) = lu {
            cache.eng.ftran(w);
            return;
        }
        for wi in w.iter_mut() {
            *wi = -*wi; // B_0^{-1} = -I.
        }
        debug_assert_eq!(etas.start.len(), etas.len() + 1);
        let n = etas.len();
        // SAFETY: `EtaFile` keeps `p`/`diag` at `n`, `start` at `n + 1`, and
        // its ranges within aligned `idx`/`val`; all stored rows index `w`.
        unsafe {
            let ps = etas.p.as_ptr();
            let ds = etas.diag.as_ptr();
            let ss = etas.start.as_ptr();
            let ix = etas.idx.as_ptr();
            let vs = etas.val.as_ptr();
            let wp = w.as_mut_ptr();
            for k in 0..n {
                let p = *ps.add(k) as usize;
                debug_assert!(p < w.len());
                let t = *wp.add(p);
                if t == 0.0 {
                    continue;
                }
                let s = *ss.add(k) as usize;
                let e = *ss.add(k + 1) as usize;
                // 4-wide: an eta's entry rows are DISTINCT (they came from an
                // `nz` support list), so the four updates touch four different
                // slots — same values in any order, and the CPU overlaps them
                // instead of stepping the loop once per entry.
                let mut q = s;
                while q + 4 <= e {
                    let i0 = *ix.add(q) as usize;
                    let i1 = *ix.add(q + 1) as usize;
                    let i2 = *ix.add(q + 2) as usize;
                    let i3 = *ix.add(q + 3) as usize;
                    debug_assert!(i0.max(i1).max(i2).max(i3) < w.len());
                    *wp.add(i0) += *vs.add(q) * t;
                    *wp.add(i1) += *vs.add(q + 1) * t;
                    *wp.add(i2) += *vs.add(q + 2) * t;
                    *wp.add(i3) += *vs.add(q + 3) * t;
                    q += 4;
                }
                while q < e {
                    let i = *ix.add(q) as usize;
                    debug_assert!(i < w.len());
                    *wp.add(i) += *vs.add(q) * t;
                    q += 1;
                }
                *wp.add(p) = *ds.add(k) * t;
            }
        }
    }

    /// `self.alpha <- B^{-1} M_q`, gathering the non-zero rows into `self.nz`.
    /// `alpha` must be all-zero on entry (the rest-state invariant every user
    /// restores). `nz` comes back sorted ascending and duplicate-free — it is
    /// rebuilt by one linear scan of `alpha` after the walk, not maintained
    /// during it (the eta-file walk is the engine's hottest loop, and the old
    /// per-entry `marked` dedup mask cost a byte load, a branch and a possible
    /// push on every entry).
    fn ftran(&mut self, lp: &FloatLp, q: usize) {
        let alpha = &mut self.alpha[..];
        let nz = &mut self.nz;
        if let Some(cache) = self.lu.as_mut() {
            // LU path: gather the RAW column (no -I fold — the engine factors B
            // itself) and run the reachability-sparse solve. `nz` comes back as
            // the solution's true support, preserving the shared-scratch
            // protocol verbatim — and the callers' per-pivot walks stay sparse.
            nz.clear();
            if q < lp.n {
                for p in lp.col_ptr[q]..lp.col_ptr[q + 1] {
                    let r = lp.col_idx[p];
                    if alpha[r] == 0.0 {
                        nz.push(r);
                    }
                    alpha[r] += lp.p_col_val()[p];
                }
            } else {
                alpha[q - lp.n] -= 1.0;
                nz.push(q - lp.n);
            }
            cache.eng.ftran_nz(alpha, nz);
            return;
        }
        if q < lp.n {
            for p in lp.col_ptr[q]..lp.col_ptr[q + 1] {
                alpha[lp.col_idx[p]] -= lp.p_col_val()[p]; // (-I) folded in.
            }
        } else {
            alpha[q - lp.n] += 1.0; // -(-1), the logical's -e_r through -I.
        }
        // Unchecked for the same reason and under the same invariants as
        // `apply_inverse_parts` — this is the per-pivot FTRAN. The walk keeps
        // NO support bookkeeping (the old `marked`/`nz` dance cost a byte
        // load, a branch and a possible push per entry): `alpha` is dense
        // scratch anyway, so the support is rebuilt afterwards by one linear
        // scan of its `m` slots — ascending, so the etas the pivot loops
        // build from `nz` come out row-sorted (a value change only in the
        // ORDER downstream dot products sum, which is a legal float-path
        // change; sets and per-entry values are identical, rows that cancel
        // to exact 0.0 were skipped by every consumer's `!= 0.0` guard
        // before and now simply never enter `nz`).
        let etas = &self.etas;
        debug_assert_eq!(etas.start.len(), etas.len() + 1);
        let n = etas.len();
        // SAFETY: `EtaFile` keeps `p`/`diag` at `n`, `start` at `n + 1`, and
        // its ranges within aligned `idx`/`val`; all stored rows index `alpha`.
        unsafe {
            let ps = etas.p.as_ptr();
            let ds = etas.diag.as_ptr();
            let ss = etas.start.as_ptr();
            let ix = etas.idx.as_ptr();
            let vs = etas.val.as_ptr();
            let ap = alpha.as_mut_ptr();
            for k in 0..n {
                let p = *ps.add(k) as usize;
                debug_assert!(p < alpha.len());
                let t = *ap.add(p);
                if t == 0.0 {
                    continue;
                }
                let s = *ss.add(k) as usize;
                let e = *ss.add(k + 1) as usize;
                // 4-wide over distinct rows — see `apply_inverse_parts`.
                let mut q = s;
                while q + 4 <= e {
                    let i0 = *ix.add(q) as usize;
                    let i1 = *ix.add(q + 1) as usize;
                    let i2 = *ix.add(q + 2) as usize;
                    let i3 = *ix.add(q + 3) as usize;
                    debug_assert!(i0.max(i1).max(i2).max(i3) < alpha.len());
                    *ap.add(i0) += *vs.add(q) * t;
                    *ap.add(i1) += *vs.add(q + 1) * t;
                    *ap.add(i2) += *vs.add(q + 2) * t;
                    *ap.add(i3) += *vs.add(q + 3) * t;
                    q += 4;
                }
                while q < e {
                    let i = *ix.add(q) as usize;
                    debug_assert!(i < alpha.len());
                    *ap.add(i) += *vs.add(q) * t;
                    q += 1;
                }
                *ap.add(p) = *ds.add(k) * t;
            }
        }
        nz.clear();
        for (i, &a) in alpha.iter().enumerate() {
            if a != 0.0 {
                nz.push(i);
            }
        }
    }

    /// `y <- y B^{-1}` (a row vector), in place: etas in reverse, then `-I`.
    fn btran(&mut self) {
        if let Some(cache) = self.lu.as_mut() {
            // LU path: `y` is usually a sparse cost gather (on sparse models
            // most basics are zero-cost logicals), so scan out its support
            // and run the reachability-sparse solve — one O(m) sequential
            // read instead of the full dense factor chain.
            let mut nzv = std::mem::take(&mut self.ynz);
            nzv.clear();
            for (i, &v) in self.y.iter().enumerate() {
                if v != 0.0 {
                    nzv.push(i);
                }
            }
            cache.eng.btran_nz(&mut self.y, &mut nzv);
            self.ynz = nzv;
            return;
        }
        // Unchecked under the `EtaFile` construction invariants — see
        // `apply_inverse_parts`.
        //
        // Each eta is one dot product — a serial FP-add LATENCY chain. A
        // 4-accumulator blocked version was built and MEASURED here (btran's
        // self-share halved; reassociation is legal now), but the engine-wide
        // pace it bought pushed the 80x60 @60s primal run's wall-clock
        // endgame schedule out of its converging window (252 -> 249 on seed
        // 99, reproducibly — the schedule maps onto baseline wall as
        // outcome(60s) = baseline_outcome(60s x pace), and the 252-plateau's
        // edge sits at ~1.17x). The single chain stays for SMALL LPs until the
        // endgame is node-budgeted rather than wall-budgeted.
        //
        // BIG LPs (`cols >= BIG_LP_COLS && m >= BIG_LP_ROWS`, the cifar100 w5 class: 26,831
        // structurals / 7.47M nnz) take the blocked form below: btran is 66%
        // of the sampled cold-walk profile there (24.4k phase-1 iterations,
        // eta files 400 deep under the m>=8192 REFACTOR_EVERY default), the
        // ladder/corpus instances never reach the gate (their float paths and
        // pace are byte-identical), and the walk it changes is ADVICE — the
        // verdict rests on the exact rim (`refine_incumbent`/`check_point`/
        // exact bounds) either way.
        let big = self.cols >= BIG_LP_COLS && self.m >= BIG_LP_ROWS;
        let etas = &self.etas;
        let y = &mut self.y[..];
        debug_assert_eq!(etas.start.len(), etas.len() + 1);
        // SAFETY: `EtaFile` keeps `p`/`diag` aligned, `start` at `len + 1`, and
        // its ranges within aligned `idx`/`val`; all stored rows index `y`.
        unsafe {
            let ps = etas.p.as_ptr();
            let ds = etas.diag.as_ptr();
            let ss = etas.start.as_ptr();
            let ix = etas.idx.as_ptr();
            let vs = etas.val.as_ptr();
            let yp = y.as_mut_ptr();
            if big {
                for k in (0..etas.len()).rev() {
                    let p = *ps.add(k) as usize;
                    debug_assert!(p < y.len());
                    let s = *ss.add(k) as usize;
                    let e = *ss.add(k + 1) as usize;
                    // 4 independent chains; entry rows are DISTINCT (ftran
                    // support list), so the gathers overlap in the LSU.
                    let (mut a0, mut a1, mut a2, mut a3) = (0.0f64, 0.0f64, 0.0f64, 0.0f64);
                    let mut q = s;
                    while q + 4 <= e {
                        let i0 = *ix.add(q) as usize;
                        let i1 = *ix.add(q + 1) as usize;
                        let i2 = *ix.add(q + 2) as usize;
                        let i3 = *ix.add(q + 3) as usize;
                        debug_assert!(i0.max(i1).max(i2).max(i3) < y.len());
                        a0 += *vs.add(q) * *yp.add(i0);
                        a1 += *vs.add(q + 1) * *yp.add(i1);
                        a2 += *vs.add(q + 2) * *yp.add(i2);
                        a3 += *vs.add(q + 3) * *yp.add(i3);
                        q += 4;
                    }
                    // (clippy's suspicious-groupings lint misreads this:
                    // diag[k] multiplies y[PIVOT ROW p], not y[k].)
                    #[allow(clippy::suspicious_operation_groupings)]
                    let mut acc = *ds.add(k) * *yp.add(p) + ((a0 + a1) + (a2 + a3));
                    while q < e {
                        let i = *ix.add(q) as usize;
                        debug_assert!(i < y.len());
                        acc += *vs.add(q) * *yp.add(i);
                        q += 1;
                    }
                    *yp.add(p) = acc;
                }
            } else {
                for k in (0..etas.len()).rev() {
                    let p = *ps.add(k) as usize;
                    debug_assert!(p < y.len());
                    let mut acc = *ds.add(k) * *yp.add(p);
                    let s = *ss.add(k) as usize;
                    let e = *ss.add(k + 1) as usize;
                    for q in s..e {
                        let i = *ix.add(q) as usize;
                        debug_assert!(i < y.len());
                        acc += *vs.add(q) * *yp.add(i);
                    }
                    *yp.add(p) = acc;
                }
            }
        }
        for v in y.iter_mut() {
            *v = -*v;
        }
    }

    /// Maintain the DEVEX weights across a pivot (Forrest–Goldfarb).
    ///
    /// ```text
    ///   w_j       <- max( w_j,  (alpha_pj / alpha_pq)^2 * w_q )
    ///   w_leaving <- max( w_q / alpha_pq^2,  1 )
    /// ```
    ///
    /// `alpha_pj` is row `p` of `B^{-1} M`, which needs `rho = B^{-T} e_p` — one BTRAN — and then
    /// a dot product per column. Signs are irrelevant: the ratio is squared, so `btran` negating
    /// its result negates both halves.
    fn update_devex(&mut self, lp: &FloatLp, q: usize, p: usize, piv: f64) {
        if !piv.is_finite() || piv.abs() <= 1e-12 {
            return;
        }
        self.y_is_duals = false; // `y` becomes rho below
        let wq = self.w[q];
        // rho = B^{-T} e_p, borrowing `y`: pricing has already run this iteration, and the next
        // one rebuilds it from the basic costs.
        self.y.fill(0.0);
        self.y[p] = 1.0;
        self.btran();

        let inv2 = 1.0 / (piv * piv);
        for j in 0..self.cols {
            if self.basic_row[j].is_some() || j == q {
                continue;
            }
            // alpha_pj = rho · M_j. A logical's column is -e_r, so it reads straight off rho.
            let a_pj = if j < lp.n {
                let mut dot = 0.0;
                for idx in lp.col_ptr[j]..lp.col_ptr[j + 1] {
                    dot += self.y[lp.col_idx[idx]] * lp.p_col_val()[idx];
                }
                dot
            } else {
                -self.y[j - lp.n]
            };
            if a_pj == 0.0 {
                continue;
            }
            let cand = a_pj * a_pj * inv2 * wq;
            if cand > self.w[j] {
                self.w[j] = cand;
            }
        }
        let leaving = self.basis[p];
        self.w[leaving] = (wq * inv2).max(1.0);

        // The estimates drift upward; past a point they say nothing, so start over.
        if self.w[leaving] > DEVEX_RESET || wq > DEVEX_RESET {
            self.w.fill(1.0);
        }
    }

    /// `xb <- B^{-1} (0 - sum_{j nonbasic} M_j val_j)`.
    /// NEW BOUNDS, SAME BASIS -- so the same `B⁻¹`.
    ///
    /// The basis matrix `B` is decided by WHICH columns are basic, and a bound change does not
    /// change that. So the factorisation this solver is carrying is still exactly right, and the
    /// only thing that actually moved is where the NONBASIC columns are resting -- which changes
    /// `x_B` through `B·x_B = b − N·x_N`, and nothing else.
    ///
    /// This is the whole point of `WarmSolver`. `warm_start` rebuilds the factorisation from scratch
    /// (O(m·nnz)), and a dive step, a strong-branching probe and a node re-solve all change nothing
    /// but bounds -- so all three were paying for a factorisation they already had. On air05 a dive
    /// step is ONE simplex iteration and cost 21ms.
    fn rebound(&mut self, lp: &FloatLp, lower: &[f64], upper: &[f64]) {
        if lp.scaled() {
            for j in 0..self.cols {
                self.lo[j] = lower[j] * lp.bnd_mul[j];
                self.up[j] = upper[j] * lp.bnd_mul[j];
            }
        } else {
            self.lo.copy_from_slice(lower);
            self.up.copy_from_slice(upper);
        }
        // A nonbasic column rests on a bound, and that bound has to still be there.
        for j in 0..self.cols {
            if self.basic_row[j].is_some() {
                continue;
            }
            let (lo, up) = (self.lo[j], self.up[j]);
            self.at[j] = match self.at[j] {
                NbBound::Lower if !lo.is_finite() => {
                    if up.is_finite() {
                        NbBound::Upper
                    } else {
                        NbBound::Zero
                    }
                }
                NbBound::Upper if !up.is_finite() => {
                    if lo.is_finite() {
                        NbBound::Lower
                    } else {
                        NbBound::Zero
                    }
                }
                NbBound::Zero if lo.is_finite() => NbBound::Lower,
                NbBound::Zero if up.is_finite() => NbBound::Upper,
                keep => keep,
            };
        }
        self.recompute_xb(lp);
    }

    fn recompute_xb(&mut self, lp: &FloatLp) {
        if !lp.p_dense_rows().is_empty() {
            // Row-major: mirror the nonbasic structural values densely once,
            // then each `xb[r]` is one straight dot product over the dense
            // row. SEQUENTIAL accumulation, deliberately: for a fixed row the
            // old column-scatter added the very same products in the very
            // same ascending-`j` order, so this reproduces its bits (IEEE
            // negation is exact, so `-(Σ a·x)` equals the old `Σ a·(-x)`);
            // a blocked dot here bought ~nothing and moved the search path.
            let n = lp.n;
            for j in 0..n {
                self.xtmp[j] = if self.basic_row[j].is_none() {
                    let x = self.nb_value(lp, j);
                    if x.is_finite() {
                        x
                    } else {
                        0.0
                    }
                } else {
                    0.0
                };
            }
            let xt = &self.xtmp[..n];
            for (r, dr) in lp.p_dense_rows().chunks_exact(n).enumerate() {
                let mut acc = 0.0f64;
                for (&a, &x) in dr.iter().zip(xt) {
                    acc += a * x;
                }
                self.xb[r] = -acc;
            }
            for r in 0..self.m {
                let j = n + r;
                if self.basic_row[j].is_none() {
                    let x = self.nb_value(lp, j);
                    if x != 0.0 && x.is_finite() {
                        self.xb[r] += x; // the logical column is -e_r, negated
                    }
                }
            }
        } else {
            // Accumulate straight into `xb` (nothing reads it during the
            // build), so the fresh per-call vector and its copy-out are gone.
            self.xb.fill(0.0);
            for j in 0..self.cols {
                if self.basic_row[j].is_some() {
                    continue;
                }
                let x = self.nb_value(lp, j);
                if x == 0.0 || !x.is_finite() {
                    continue;
                }
                lp.axpy(j, -x, &mut self.xb);
            }
        }
        Self::apply_inverse_parts(self.lu.as_mut(), &self.etas, &mut self.xb);
    }

    /// The staleness trigger this solve verifies against: the historical
    /// `VERIFY_AFTER` on the eta file and on every regime outside the tall
    /// LU band, `lu_verify_after()` (Lever A1) when the FT engine backs a
    /// tall-not-wide LP. Every re-check site AND `refactorize`'s skip cap
    /// must read the SAME value — the skip cap being tighter than a caller's
    /// trigger is the verify-loop deadlock documented at the skip.
    fn verify_after_for(&self, lp: &FloatLp) -> usize {
        if self.lu.is_some() && lp.tall_lu() && self.m < REFACTOR_TALL_ROWS {
            lu_verify_after()
        } else {
            verify_after()
        }
    }

    /// The refactor cadence this solve pivots under: `lu_refactor_every()`
    /// (Lever A1b) when the FT engine backs a tall-not-wide LP, the
    /// historical size policy everywhere else.
    fn refactor_cadence(&self, lp: &FloatLp) -> usize {
        if self.lu.is_some() && lp.tall_lu() && self.m < REFACTOR_TALL_ROWS {
            lu_refactor_every()
        } else {
            refactor_every(self.m)
        }
    }

    /// Rebuild `B^{-1}` from the current basis: Gaussian elimination in product
    /// form with partial pivoting. If a basis column has no acceptable pivot
    /// (round-off made the basis look singular) the previous eta-file is kept —
    /// a stale but self-consistent inverse costs tightness, never soundness,
    /// because nothing this lane produces is trusted anyway.
    /// Arm the fill-rate trip if THIS rebuild's bump contradicts the floor's premise.
    ///
    /// # The comparison is measured against measured, with no fitted constant
    ///
    /// The floor's justification is that small bumps are *"already near-zero-fill"*.
    /// The peel splits the rebuild into three runs of columns — fronts, bump, backs —
    /// and the FRONT/BACK runs are the triangular part, i.e. near-zero-fill **by
    /// construction**. They are therefore a baseline for "near-zero-fill" measured in
    /// the same rebuild, in the same unit, on the same basis.
    ///
    /// So the trip is: does the bump produce fill per column at a rate the triangular
    /// part of the SAME rebuild does not? That is a self-relative test. It borrows the
    /// shape of `euf::maybe_latch_undo`, which replaced its own size gate with
    /// `rebuild_work > undo_work` — two measured quantities, no constant.
    ///
    /// A genuinely near-zero-fill bump — the ~160-column crash-walk bases the floor
    /// exists to protect — cannot trip this, because its rate is the triangular rate.
    /// That is the point: **the protected class is now protected by the property it is
    /// claimed to have, rather than by a column count standing in for it.**
    ///
    /// # Why a latch, and why it is deterministic
    ///
    /// The fill is only known after the bump is built, so the decision it informs is
    /// the NEXT rebuild's. Counts only — `Etas::entries()` differences — so the arming
    /// point is identical on every run and on every machine, which
    /// `refactor_every`'s own history says is the property that matters here.
    ///
    /// One-way: once armed it stays armed for the solve. A flapping lane choice would
    /// make the eta file's provenance depend on rebuild history in a way nothing
    /// downstream expects.
    fn maybe_trip_bump_fill(
        &mut self,
        seg_ef: usize,
        seg_eb: usize,
        peel_nf: usize,
        peel_nb: usize,
    ) {
        // ⛔ OPT-IN, AND THE PREDICATE BELOW IS KNOWN TO BE BIASED. Default OFF, so
        // the shipped path is byte-identical to the pure column floor.
        //
        // The comparison looked constant-free and is not commensurable. `tri_fill`
        // is the SINGLETON PEEL's fill, and fronts are selected precisely BECAUSE
        // they place fill-free on an already-available row; bump columns are
        // additionally FTRAN'd through every front eta before placement. So the
        // baseline is a structurally easier set of DIFFERENT columns, and a strict
        // `>` with no margin arms on one extra entry per column -- which would fire
        // on the 130-160-column crash-walk bases the floor exists to protect, i.e.
        // exactly the population there is no evidence for.
        //
        // That is not the `euf::maybe_latch_undo` shape after all: `rebuild_work` and
        // `undo_work` are two costings of ONE operation, kept comparable on purpose.
        //
        // THE COMMENSURABLE TEST DOES EXIST and is the real design: `nnz(L)+nnz(U)`
        // is exactly the `Etas::entries()` delta the LU lane would produce, so running
        // `bump_eliminate` and DISCARDING the factor yields the other lane's number
        // for the same bump, same basis, same unit. `lu_entries < pfi_entries` is then
        // a true sign test. It still needs one constant -- entries price the repeated
        // FTRAN/BTRAN walk but not the one-off build, and LU pays a Markowitz
        // elimination on top of the same FTRANs, so equal entries means LU is strictly
        // worse -- but a dimensionless margin on the LU side is a threshold on the
        // quantity the claim is ABOUT, and its failure mode is monotone
        // (margin -> infinity is today's behaviour exactly).
        //
        // Shipping that needs a probe schedule so the discarded factorisations are
        // bounded. Until then the lane stays off (B22: env spelling retired).
        if self.bump_fill_latched || no_fill_trip() || !fill_trip_optin() {
            return;
        }
        // Need a non-empty triangular run to have a baseline at all, and a non-empty
        // bump to have something to judge. Abstain otherwise — an unmeasurable rebuild
        // must not arm a lane switch.
        if peel_nf == 0 || peel_nb == 0 || seg_eb < seg_ef {
            return;
        }
        let tri_fill = seg_ef as u64;
        let bump_fill = (seg_eb - seg_ef) as u64;
        // Cross-multiplied to stay in integers: bump_fill/peel_nb > tri_fill/peel_nf.
        // Strictly greater, so a bump matching the triangular rate exactly does not arm.
        if bump_fill.saturating_mul(peel_nf as u64) > tri_fill.saturating_mul(peel_nb as u64) {
            self.bump_fill_latched = true;
        }
    }

    fn refactorize(&mut self, lp: &FloatLp) {
        // Fail closed for diagnostic provenance even when an early return
        // (OOM/cache hit) means no rebuild lane ran.
        self.refactor_kicked = 0;
        self.refactor_bump_lu_used = false;
        // Once the LU factor has DECLINED (fill over budget) this solve is
        // giving up: do NOT rebuild anything. The eta-file arm below is itself
        // an unbounded fill bomb, and re-attempting the LU factor would just
        // decline again. Making `refactorize` inert after a decline is what
        // contains the bomb even at the call sites this lever does not guard
        // individually — the pivot loops still bail on `self.oom`. (Dead branch
        // on every shipping instance: `oom` never gets set there.)
        if self.oom {
            return;
        }
        stats::bump(&stats::REFACTORS);
        // A rebuilt inverse computes (bitwise) different duals — never reuse
        // a `y` from before it.
        self.y_is_duals = false;
        // LATE LU PROMOTION (`cold_lu_eta_rebuilds`): this solve started on the
        // eta file — because the row band declined it — and has now paid for
        // more O(m*nnz) rebuilds than the budget allows. Switch lanes.
        //
        // THIS IS THE ONLY PLACE THE SWITCH CAN HAPPEN, and it is free here.
        // `B^{-1}` has exactly two representations and `apply_inverse_parts`
        // picks ONE — an installed engine short-circuits, the eta file is not
        // consulted — so the lanes never compose and a switch is not a merge.
        // It is a re-derivation of `B^{-1}` from `self.basis`, which is
        // precisely what the code below this line was about to do anyway. So
        // the switch costs the DIFFERENCE between the two rebuild kinds, not a
        // rebuild on top of one; and paired 60 s runs over 14 models make the
        // LU factor the cheaper of the two on 13 of them (ms per rebuild,
        // eta / LU: decomp2 22.35x, cvs16r70-62 18.89x, tbfp-network 16.26x,
        // comp21-2idx 14.02x, dano3_3 13.32x, atlanta-ip 9.97x, seymour 5.68x,
        // neos-960392 5.40x, glass-sc 2.59x, aflow40b 2.23x, neos-1456979
        // 1.27x, hypothyroid-k1 1.22x, drayage-100-23 0.82x — median 9.97x).
        // Nothing is reconstructed, no basis is re-crashed and no vertex
        // invariant is restored: `LuEngine::factor` preserves position binding,
        // so `basis` and `basic_row` are untouched by the swap.
        //
        // ⚠ IT STILL MOVES THE VERTEX. The LU inverse is not bitwise the eta
        // inverse, so every pivot after this one may differ, and on a
        // `plain_cold` solve that vertex seeds pump/dive/RINS. That is the same
        // blast radius the row band already accepted, not a new one — which is
        // why this shares the band's kill switch rather than adding a second.
        //
        // Placed BEFORE `verify_cap`/`cadence`/`ft_max` so all three are
        // computed against the lane that will actually run. `rep_basis` is left
        // EMPTY on purpose: it cannot match `self.basis`, so the match-skip is
        // declined and the FT-adoption diff is declined (`same_len` false), and
        // control falls to the full factor — the correct first act for an
        // engine that represents nothing yet.
        // TWO GATES, both measured rather than chosen.
        //
        // `tall_lu()` is the row FLOOR, and it is the crate's EXISTING one — see
        // `cold_lu_eta_rebuilds`. Without it a pure count promotes gt2 (m = 29)
        // and air05 (m = 426), which the band's floor-of-0 experiment measured
        // as a lost proof and two lost OPTIMALs.
        //
        // `!cold_root_lu()` keeps this lane OUT OF THE BAND'S TERRITORY, and it
        // is not defensive tidiness — without it the band regresses. An in-band
        // model's cold root and warm nodes are already on the FT engine, but its
        // remaining eta-lane solves (a crash basis declines the install; a
        // singular factor demotes) still rebuild hard: measured per-solve maxima
        // at the shipped default are drayage-100-23 839, cvs16r89-60 524,
        // cvs16r70-62 385, nursesched-sprint02 299. Every one of those clears any
        // useful budget, so an ungated count would promote a solve inside the
        // band, move its vertex and move its tree — turning a lane built to reach
        // the models the band EXCLUDES into a silent edit of the models it
        // includes. Outside the band nothing owns these solves, which is the
        // whole gap this lane exists to close.
        if self.lu.is_none()
            && !self.lu_late_locked
            && !no_cold_lu()
            && lp.tall_lu()
            && !lp.cold_root_lu()
        {
            let budget = cold_lu_eta_rebuilds();
            if budget > 0 && self.eta_rebuilds >= budget {
                self.lu = Some(LuCache {
                    eng: crate::lu::LuEngine::new(self.m),
                    rep_basis: Vec::new(),
                });
                self.lu_late_locked = true;
                // The eta file stops being maintained from here (its append is
                // guarded on `self.lu.is_none()`), so it no longer represents
                // the basis — say so now rather than at the first LU pivot, or
                // a later `reset(keep_factor=true)` would take the CROSS-SOLVE
                // ETA REUSE skip against a file that has been dead for a whole
                // solve.
                self.factor_live = false;
                LU_LATE_PROMOTE.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            }
        }
        // Did this call ENTER with an operator? Only then is a fall-through to
        // the eta rebuild below a DEMOTION worth latching against. Reading it
        // after the promotion above means a just-promoted engine counts as
        // present, which is what makes a failed first factor latch correctly.
        let had_lu = self.lu.is_some();
        // Computed before the cache borrow (it reads `self.lu.is_some()`).
        let verify_cap = self.verify_after_for(lp).min(self.refactor_cadence(lp));
        let cadence = self.refactor_cadence(lp);
        // FORGONE COST (Lever A1's class gate). `verify_after_for`/`refactor_cadence`
        // raise the verify trigger only BELOW `REFACTOR_TALL_ROWS`; at or above it an
        // LU-backed tall solve is pinned to VERIFY_AFTER = 20, so `REFACTOR_EVERY_TALL`
        // (400) never applies on the class it was measured for. Unlike the FT-adoption
        // ceiling one gate down, this ceiling has NO override. Charged below, on the
        // rebuilds where the operator represented the basis EXACTLY (d = 0) and the
        // 20-trigger forced a base factor anyway — the population lu_verify_after's own
        // doc quantifies (51,660 of 73,118 base factors in the k=124 certification).
        let verify_ceiling_class =
            self.lu.is_some() && lp.tall_lu() && self.m >= REFACTOR_TALL_ROWS;
        let ceiling_rows = self.m as u64;
        // FT-adoption eligibility (Lever A2): same class gate as A1.
        let ft_max = if self.lu.is_some() && lp.tall_lu() && self.m < adopt_ft_max_rows() {
            adopt_ft_max()
        } else {
            // FORGONE COST. The ceiling's claim is that FT adoption stops
            // paying up here. Ask this top-level solve's shared latch to charge
            // its FIRST actual exclusion; refactorization, node and worker
            // multiplicity must not turn one model solve into many census
            // entries.
            if self.lu.is_some() && lp.tall_lu() {
                lp.charge_ft_adoption_exclusion();
            }
            0
        };
        if let Some(cache) = self.lu.as_mut() {
            // The operator already represents EXACTLY this basis (base factor
            // plus absorbed updates) whenever the basis is unchanged since the
            // cache last saw it — the common case for a warm child, which
            // adopts its parent's final basis. Then the only reason to factor
            // is staleness — but "fresh enough" is measured against the
            // TIGHTEST trigger any caller re-checks after this returns, which
            // is `verify_after()`, NOT `REFACTOR_EVERY`.
            //
            // It was `REFACTOR_EVERY`, and that deadlocked the "refactorise
            // and ask once more" verify loops (primal no-enter, dual optimum):
            // their termination argument is "`refactorize` zeroes
            // `since_refactor`", and a match-skip with `updates()` in
            // [verify_after(), REFACTOR_EVERY) returns with `since_refactor`
            // still >= the trigger — so the loop re-asks forever, one full
            // pricing pass per spin. Measured on the 30x20 dense-binary
            // knapsack: 4,801,453 refactorize calls answered by this skip
            // against 1 real factorization and 476 actual pivots, every node
            // LP grinding to MAX_ITERS (~310ms/node, `stopped=11`) with the
            // operator numerically PERFECT the whole time (ftran residuals
            // clean, zero update rejections). Capping the skip at
            // `verify_after()` restores the contract: any refactorize call
            // that a trigger provoked now leaves `since_refactor` strictly
            // below that trigger, so every re-ask happens at most once per
            // clean basis. (The `min` guards an env override setting
            // AY_MILP_VERIFY_AFTER above the refactor-every knob.)
            let basis_match = cache.rep_basis == self.basis;
            if basis_match && cache.eng.updates() < verify_cap && cache.eng.nnz() < self.eta_nnz_cap
            {
                self.eta_nnz = cache.eng.nnz();
                self.since_refactor = cache.eng.updates();
                return;
            }
            // The skip was declined and the ONLY failing condition was `updates() <
            // verify_cap` — i.e. this rebuild exists solely because the ceiling kept the
            // 20-trigger. Hits are per-rebuild here, NOT per-solve (contrast the
            // FT-adoption latch two gates up, which deliberately de-multiplies).
            if verify_ceiling_class && basis_match && cache.eng.nnz() < self.eta_nnz_cap {
                crate::sepstat::gate_charge(crate::sepstat::GATE_LU_VERIFY_CEILING, ceiling_rows);
            }
            // Basis-diff diagnostics (see BASIS_DIFF_HIST): how far is the operator's
            // basis from the one just adopted, in positions? The changed positions
            // double as Lever A2's work list (collected only while they could fit).
            let mut adopt_pos: Vec<usize> = Vec::new();
            let same_len = cache.rep_basis.len() == self.basis.len();
            let d = if same_len {
                let mut d = 0usize;
                for (p, (a, b)) in cache.rep_basis.iter().zip(&self.basis).enumerate() {
                    if a != b {
                        d += 1;
                        if d <= ft_max {
                            adopt_pos.push(p);
                        }
                    }
                }
                d
            } else {
                usize::MAX
            };
            {
                let bucket = match d {
                    0 => 0,
                    1 => 1,
                    2 => 2,
                    3 => 3,
                    4..=7 => 4,
                    8..=15 => 5,
                    16..=31 => 6,
                    _ => 7,
                };
                BASIS_DIFF_HIST[bucket].fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            }
            // FT ADOPTION (Lever A2): absorb a NEARBY adopted basis as `d`
            // Forrest–Tomlin updates instead of a full base factor. License:
            // this lane is advice — a rejected or numerically poor update is
            // caught by `LuEngine::update`'s transactional growth guards, and
            // the fallback below is the full factor that would have run anyway.
            //
            // Order matters when the diff contains replacement CHAINS (the new
            // column of one changed slot is the old column of another): the
            // slot whose old column is still wanted elsewhere must be replaced
            // first or the intermediate basis holds a duplicate column and the
            // update rejects on a vanishing pivot. Greedy selection: each round
            // takes a pending slot whose entering column is no pending slot's
            // OLD column. Pure swap cycles admit no such order — bail before
            // wasting FTRANs (the full factor handles them).
            if (1..=ft_max).contains(&d) && cache.eng.updates() + d < cadence && {
                // nnz headroom: the spikes add fill; demand the same cap the
                // within-solve update path enforces at its triggers.
                cache.eng.nnz() < self.eta_nnz_cap
            } {
                let _tf = std::time::Instant::now();
                let mut buf = std::mem::take(&mut self.wflip); // m-length, zeroed scratch
                buf.fill(0.0);
                let mut nz: Vec<usize> = Vec::with_capacity(32);
                // Pending slots, swept in slot order; a slot whose entering
                // column is still held by another pending slot (a replacement
                // CHAIN) is deferred to a later sweep — after its holder is
                // replaced, its update becomes admissible. A sweep with no
                // progress is a pure swap cycle: bail to the full factor. A
                // NUMERICAL rejection bails IMMEDIATELY: retrying rejected
                // slots after other replacements was built and MEASURED
                // CATASTROPHIC on k=124 (adoption "success" 46% -> 78%, but
                // the extra successes commit near-threshold pivots on this
                // degenerate class — drifted walks failed their postchecks
                // and cascaded into the exact rim: rim=203.7s, certification
                // lost; see the `lu_refactor_every` landmine, same run).
                let mut pending = adopt_pos;
                let mut ok = true;
                'sweeps: while ok && !pending.is_empty() {
                    let mut progress = false;
                    let mut k = 0usize;
                    while k < pending.len() {
                        let p = pending[k];
                        // Duplicate-column admissibility: the entering column
                        // must not still be held by another pending slot.
                        if pending
                            .iter()
                            .any(|&q| q != p && cache.rep_basis[q] == self.basis[p])
                        {
                            k += 1;
                            continue;
                        }
                        let j = self.basis[p];
                        nz.clear();
                        if j < lp.n {
                            for q in lp.col_ptr[j]..lp.col_ptr[j + 1] {
                                let r = lp.col_idx[q];
                                if buf[r] == 0.0 {
                                    nz.push(r);
                                }
                                buf[r] += lp.p_col_val()[q];
                            }
                        } else {
                            buf[j - lp.n] = -1.0;
                            nz.push(j - lp.n);
                        }
                        cache.eng.ftran_nz(&mut buf, &mut nz);
                        // `nz` is the solve's support (and is used two lines
                        // down to re-zero `buf`), so the LU's spike build gets
                        // its pattern for free — see `LuEngine::update_nz`.
                        let res = cache.eng.update_nz(p, &buf, &nz);
                        for &r in &nz {
                            buf[r] = 0.0;
                        }
                        if res.is_err() {
                            ok = false; // numerically rejected: full factor
                            break 'sweeps;
                        }
                        pending.swap_remove(k);
                        progress = true;
                    }
                    if !progress {
                        ok = false; // pure swap cycle
                        ADOPT_FT_CYC.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    }
                }
                self.wflip = buf;
                if ok {
                    // The operator now represents exactly `self.basis`; the
                    // absorbed updates count toward staleness like any pivot's.
                    cache.rep_basis.clear();
                    cache.rep_basis.extend_from_slice(&self.basis);
                    self.eta_nnz = cache.eng.nnz();
                    self.since_refactor = cache.eng.updates();
                    ADOPT_FT_OK.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    ADOPT_FT_NANOS.fetch_add(
                        _tf.elapsed().as_nanos() as u64,
                        std::sync::atomic::Ordering::Relaxed,
                    );
                    return;
                }
                // Partial absorption leaves a self-consistent operator for a
                // basis we can no longer name; every fallback below discards
                // it (successful factor overwrites, failed factor drops to
                // the eta rebuild via `self.lu = None`).
                ADOPT_FT_REJ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            }
            // LU path: factor the columns currently in `basis`. Position binding
            // is preserved by the engine, so `basis`/`basic_row` stay untouched.
            // On singularity the previous factorization is kept — it still
            // self-consistently represents `rep_basis` — so solves stay sound
            // and the next trigger retries.
            let mut cols: Vec<Vec<(usize, f64)>> = Vec::with_capacity(self.m);
            for &j in &self.basis {
                if j < lp.n {
                    cols.push(
                        (lp.col_ptr[j]..lp.col_ptr[j + 1])
                            .map(|p| (lp.col_idx[p], lp.p_col_val()[p]))
                            .collect(),
                    );
                } else {
                    cols.push(vec![(j - lp.n, -1.0)]);
                }
            }
            let refs: Vec<&[(usize, f64)]> = cols.iter().map(Vec::as_slice).collect();
            let _tf = std::time::Instant::now();
            match cache.eng.factor(&refs) {
                Ok(()) => {
                    cache.rep_basis.clear();
                    cache.rep_basis.extend_from_slice(&self.basis);
                    self.eta_nnz = cache.eng.nnz();
                    self.since_refactor = 0;
                    LU_FACT_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    LU_FACT_NNZ
                        .fetch_add(cache.eng.nnz() as u64, std::sync::atomic::Ordering::Relaxed);
                    LU_FACT_NANOS.fetch_add(
                        _tf.elapsed().as_nanos() as u64,
                        std::sync::atomic::Ordering::Relaxed,
                    );
                    return;
                }
                Err(crate::lu::FactorFail::OutOfBudget) => {
                    // FILL DECLINE. This is the whole point of the lever: the
                    // factorization's fill would have exhausted memory, so give
                    // up fail-closed. Do NOT fall through to the eta rebuild —
                    // it is the same unbounded blow-up, unguarded. Drop the LU
                    // (it still represents the prior basis, but we are done) and
                    // raise the sticky flag the pivot loops watch.
                    self.oom = true;
                    self.lu = None;
                    self.lu_late_locked = true; // do not re-promote into the same decline
                    return;
                }
                Err(crate::lu::FactorFail::Singular(_)) => {
                    // Singular basis: fall THROUGH to the eta rebuild, which has
                    // its own repair (kick the dependent columns). Sound and
                    // O(m·nnz)-bounded — not a bomb, unlike the fill decline.
                }
            }
            // Factor FAILED (singular basis). The eta-file arm below REPAIRS a
            // singular basis — it kicks the dependent columns to their bounds
            // and fills the uncovered rows with logicals — where this arm has
            // no repair of its own. Deferring the retry (the previous answer
            // here) is correct but ruinous on a basis that STAYS singular:
            // set partitioning hands the warm path dependent duplicate
            // columns constantly, and on air05's tree the deferral fired
            // 1,312 times against 3,340 factor calls in 60s, every deferral
            // leaving the solve pricing against an operator for a DIFFERENT
            // basis (sound — the advice-lane contract — but the walks it
            // produces are garbage, and node throughput died). So fall THROUGH
            // to the eta engine and let its repair run: the eta file is rebuilt
            // from scratch against the repaired basis, nothing else references
            // the abandoned operator, and the next solve on this LP simply
            // builds a fresh LU engine.
            LU_FACT_FAIL.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
        self.lu = None;
        // Reaching here WITH an operator in hand is a DEMOTION (singular basis).
        // Latch, so the budget — which by then is already over — cannot bounce
        // the lane back and forth once per rebuild.
        //
        // ⚠ THE `had_lu` GUARD IS LOAD-BEARING, and its absence made the whole
        // lane a no-op. A solve on the eta file reaches this line on EVERY
        // rebuild, so latching unconditionally set the flag on rebuild #1 and
        // no solve could ever reach its budget. Measured: promotions=0 on
        // uccase12, ex9, ex10 and physiciansched6-2 — precisely the models the
        // lane exists for — while their per-solve rebuild counts (50, 132, 55,
        // 39) all cleared the budget of 20.
        if had_lu {
            self.lu_late_locked = true;
        }
        REFAC_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let _t = std::time::Instant::now();
        // Stash the current file by SWAP (buffer reuse), build afresh in `etas`.
        std::mem::swap(&mut self.etas, &mut self.etas_spare);
        self.etas.clear();
        let tol = self.pivot_tol();
        // Pooled rebuild scratch. The two lists iterated across `ftran` calls
        // (which take `&mut self`) are taken out and put back; the rest are
        // plain field accesses on disjoint fields.
        let mut cols_list = std::mem::take(&mut self.rf_cols);
        let mut deferred = std::mem::take(&mut self.rf_deferred);
        cols_list.clear();
        cols_list.extend_from_slice(&self.basis);
        deferred.clear();
        self.rf_new_basis.clear();
        self.rf_new_basis.resize(self.m, usize::MAX);
        self.rf_row_used.clear();
        self.rf_row_used.resize(self.m, false);

        // Logicals still basic in their own slot are the identity: take them for
        // free, no eta.
        for &j in &cols_list {
            if j >= lp.n && !self.rf_row_used[j - lp.n] {
                let r = j - lp.n;
                self.rf_new_basis[r] = j;
                self.rf_row_used[r] = true;
            } else {
                deferred.push(j);
            }
        }
        // Slot-order copy of `deferred`, kept for the fill-guard retry below
        // (populated only when the peel reorders).
        let mut deferred_slot: Vec<usize> = Vec::new();
        // Peel segment boundaries (set when the peel reorders): deferred is
        // [0..peel_nf) fronts, [peel_nf..peel_nf+peel_nb) bump, then backs.
        let (mut peel_nf, mut peel_nb) = (0usize, 0usize);

        // TRIANGULAR PEEL PREORDER (big LPs only). The slot-order rebuild is
        // fine when most of the basis is logicals, but on an equality-chain
        // basis (the `triangular_crash` class: ~18.5k structural columns) it
        // pivots columns against rows other columns still need, and the
        // eta file FILLS — measured on the w5 cold walk as ~48% of the whole
        // phase (the rebuild's own ftrans grinding through its own fill).
        // The same peel that builds the crash orders the rebuild: process the
        // reversed peel sequence with each column FORCED onto its peel row
        // (tolerance-guarded; greedy fallback), and each ftran meets no prior
        // pivot row — zero fill, entries = the basis columns' own nonzeros.
        // Small LPs keep the historical slot order bit-for-bit (`forced` stays
        // empty; the loop below reads it through `.get()`).
        let mut forced: Vec<usize> = Vec::new();
        if ((self.cols >= BIG_LP_COLS && self.m >= BIG_LP_ROWS)
            || force_tri_crash()
            || self.range_logical_crash_installed
            || (lp.chain_lp() && chain_preorder()))
            && !no_tri_crash()
        {
            const TINY: f64 = 1e-11;
            let n = lp.n;
            // TWO-SIDED SINGLETON PEEL over the (avail rows × deferred cols)
            // basis submatrix — the classic INVERT preorder:
            //  * a ROW with one alive column (FRONT) pins that column to it;
            //    fronts in discovery order form a lower-triangular HEAD (a
            //    front column cannot appear in an earlier front's row, or
            //    that row was not a singleton);
            //  * a COLUMN with one avail row (BACK) pins likewise; backs in
            //    REVERSED discovery order form the TAIL (a back column's
            //    other rows were consumed before its discovery).
            // Order: fronts + bump (unpeeled, greedy) + reversed backs. The
            // head is exactly zero-fill; the tail is zero-fill except where a
            // back column meets a LATER-discovered front row (round-2 fronts);
            // the bump is where genuine fill lives. Col-singletons alone
            // measured 8,243/18,568 coverage mid-walk on w5 with 25-40M-entry
            // rebuilds; the row side exists precisely to absorb basis churn.
            let mut colmap = vec![u32::MAX; self.cols];
            for (k, &j) in deferred.iter().enumerate() {
                colmap[j] = k as u32;
            }
            let mut avail: Vec<bool> = self.rf_row_used.iter().map(|&u| !u).collect();
            let mut colgone = vec![false; deferred.len()];
            let mut colcount = vec![0u32; deferred.len()];
            let mut rowcount = vec![0u32; self.m];
            for (k, &j) in deferred.iter().enumerate() {
                if j < n {
                    let mut c = 0u32;
                    for p in lp.col_ptr[j]..lp.col_ptr[j + 1] {
                        let r = lp.col_idx[p];
                        if avail[r] && lp.p_col_val()[p].abs() > TINY {
                            c += 1;
                            rowcount[r] += 1;
                        }
                    }
                    colcount[k] = c;
                } else if avail[j - n] {
                    colcount[k] = 1;
                    rowcount[j - n] += 1;
                }
            }
            let mut cq: std::collections::VecDeque<u32> = (0..deferred.len() as u32)
                .filter(|&k| colcount[k as usize] == 1)
                .collect();
            let mut rq: std::collections::VecDeque<u32> = (0..self.m as u32)
                .filter(|&r| avail[r as usize] && rowcount[r as usize] == 1)
                .collect();
            let mut peel_row = vec![usize::MAX; deferred.len()];
            let mut fronts: Vec<u32> = Vec::new();
            let mut backs: Vec<u32> = Vec::new();
            // Shared removal: consume column k (index) and row r.
            // Closures can't split-borrow, so it is a macro over the locals.
            macro_rules! consume {
                ($k:expr, $r:expr) => {{
                    let (k, r) = ($k, $r);
                    colgone[k] = true;
                    avail[r] = false;
                    peel_row[k] = r;
                    // Column side: its other avail rows lose one alive col.
                    let j = deferred[k];
                    if j < n {
                        for p in lp.col_ptr[j]..lp.col_ptr[j + 1] {
                            let rr = lp.col_idx[p];
                            if avail[rr] && lp.p_col_val()[p].abs() > TINY {
                                rowcount[rr] -= 1;
                                if rowcount[rr] == 1 {
                                    rq.push_back(rr as u32);
                                }
                            }
                        }
                    }
                    // Row side: its other alive cols lose one avail row.
                    for p in lp.row_ptr[r]..lp.row_ptr[r + 1] {
                        if lp.p_row_val()[p].abs() > TINY {
                            let kk = colmap[lp.row_idx[p] as usize];
                            if kk != u32::MAX && !colgone[kk as usize] {
                                let c = &mut colcount[kk as usize];
                                if *c > 0 {
                                    *c -= 1;
                                    if *c == 1 {
                                        cq.push_back(kk);
                                    }
                                }
                            }
                        }
                    }
                    let kk = colmap[n + r];
                    if kk != u32::MAX && !colgone[kk as usize] {
                        let c = &mut colcount[kk as usize];
                        if *c > 0 {
                            *c -= 1;
                            if *c == 1 {
                                cq.push_back(kk);
                            }
                        }
                    }
                }};
            }
            loop {
                if let Some(r32) = rq.pop_front() {
                    // FRONT: row r's single alive column.
                    let r = r32 as usize;
                    if !avail[r] || rowcount[r] != 1 {
                        continue;
                    }
                    let mut kf = u32::MAX;
                    for p in lp.row_ptr[r]..lp.row_ptr[r + 1] {
                        if lp.p_row_val()[p].abs() > TINY {
                            let kk = colmap[lp.row_idx[p] as usize];
                            if kk != u32::MAX && !colgone[kk as usize] {
                                kf = kk;
                                break;
                            }
                        }
                    }
                    if kf == u32::MAX {
                        let kk = colmap[n + r];
                        if kk != u32::MAX && !colgone[kk as usize] {
                            kf = kk;
                        }
                    }
                    let Some(&j) = deferred.get(kf as usize) else {
                        continue;
                    };
                    // The column must actually reach this row admissibly.
                    let hit = if j < n {
                        (lp.col_ptr[j]..lp.col_ptr[j + 1])
                            .any(|p| lp.col_idx[p] == r && lp.p_col_val()[p].abs() > TINY)
                    } else {
                        j - n == r
                    };
                    if !hit {
                        continue;
                    }
                    fronts.push(kf);
                    consume!(kf as usize, r);
                } else if let Some(k32) = cq.pop_front() {
                    // BACK: column k's single avail row.
                    let k = k32 as usize;
                    if colgone[k] || colcount[k] != 1 {
                        continue;
                    }
                    let j = deferred[k];
                    let mut row = usize::MAX;
                    if j < n {
                        for p in lp.col_ptr[j]..lp.col_ptr[j + 1] {
                            let r = lp.col_idx[p];
                            if avail[r] && lp.p_col_val()[p].abs() > TINY {
                                row = r;
                                break;
                            }
                        }
                    } else if avail[j - n] {
                        row = j - n;
                    }
                    if row == usize::MAX {
                        continue;
                    }
                    backs.push(k32);
                    consume!(k, row);
                } else {
                    break;
                }
            }
            // Assemble: fronts (fwd) + bump (original order) + backs (rev).
            let mut ordered = Vec::with_capacity(deferred.len());
            forced.reserve(deferred.len());
            for &k32 in &fronts {
                ordered.push(deferred[k32 as usize]);
                forced.push(peel_row[k32 as usize]);
            }
            // Bump: original slot order, greedy rows. (Ascending-nnz ordering
            // was TRIED and measured WORSE — 45-49M rebuilt entries vs 40M on
            // the w5 mid-walk bump; static column nnz does not predict PFI
            // cascade fill. The bump is a genuine non-triangular core; the
            // named follow-up is an LU/Markowitz base factor, not a reorder.)
            for (k, &j) in deferred.iter().enumerate() {
                if !colgone[k] {
                    ordered.push(j);
                    forced.push(usize::MAX);
                }
            }
            for &k32 in backs.iter().rev() {
                // RESERVE the back rows: the bump's greedy scan runs before
                // the backs and must not steal their pivot rows. The forced
                // branch below fires on `rf_new_basis[want] == MAX`, and a
                // forced failure un-reserves.
                self.rf_row_used[peel_row[k32 as usize]] = true;
                ordered.push(deferred[k32 as usize]);
                forced.push(peel_row[k32 as usize]);
            }
            if trace_enabled() {
                eprintln!(
                    "--trace refactorize peel: {} fronts + {} bump + {} backs of {}",
                    fronts.len(),
                    ordered.len() - fronts.len() - backs.len(),
                    backs.len(),
                    deferred.len()
                );
            }
            peel_nf = fronts.len();
            peel_nb = ordered.len() - fronts.len() - backs.len();
            deferred_slot = deferred;
            deferred = ordered;
        }

        // PEEL-ORDER FILL GUARD. The peel order is usually (near-)zero-fill,
        // but a pathological basis can cascade SUPERLINEARLY under it — a w5
        // bound-closing node rebuild that finishes in 10.9s/42M entries in
        // slot order ran >20 minutes peel-ordered. Twice the (possibly
        // floor-raised) cap is far above every healthy rebuild; on breach,
        // start over in the historical slot order (unguarded — the pre-peel
        // behavior).
        let mut fill_cap = if forced.is_empty() {
            usize::MAX
        } else {
            self.eta_nnz_cap.saturating_mul(2)
        };
        let mut kicked;
        let mut bump_lu_used;
        'attempt: loop {
            kicked = 0;
            bump_lu_used = false;
            let mut blew = false;
            // BUMP LU BASE FACTOR. The peel's head and tail rebuild
            // (near-)zero-fill, but the mid-walk bump is a genuine ~10k-column
            // non-triangular core whose PRODUCT-FORM elimination fills to
            // 18-27M entries at 0.7-8s per rebuild (36% of the prop885 w5
            // chain, 49% of r99-67's). Factor it Markowitz instead
            // (`bump_eliminate`) and emit L-etas + reversed U-etas — the same
            // operator, `nnz(L)+nnz(U)` entries. Gated on the peel being
            // active AND the bump above `bump_lu_min` so the crash-walk bases
            // (~160-column bumps, already near-zero-fill) keep the measured
            // PFI path; `--no-bump-lu` kills it for A/B. Warm updates
            // stay PFI on top, exactly as before.
            // The `bump_lu_override` seam (default `None`) reproduces the env
            // expression BYTE-FOR-BYTE in production; `factor_probe` sets it to
            // force a specific lane for the differential harness. `bump_lane`:
            // 0 = PFI product-form (no bump segment), 1 = monolithic Markowitz
            // bump-LU (`bump_lu_segment`), 2 = block-triangular (`bump_btf_segment`).
            // The default (override `None`, `the bump-btf knob` unset) is lane 1
            // exactly as before — BTF is opt-in until proven.
            // THE FILL-RATE TRIP joins the column floor by OR: the lane arms on the
            // floor exactly as before, or once this solve has MEASURED a bump whose
            // fill contradicts the floor's own premise. See `maybe_trip_bump_fill`
            // for the comparison and `AY_MILP_NO_FILL_TRIP` for the A/B arm.
            let bump_active =
                !forced.is_empty() && (peel_nb >= bump_lu_min() || self.bump_fill_latched);
            // FORGONE COST. The floor's claim is about FILL ("small bumps rebuild
            // near-zero-fill anyway"), asserted from a COLUMN COUNT; the two figures it
            // quotes (130-160 crash-walk, ~10.2k mid-walk) straddle 512 by an order of
            // magnitude each way. Charge the fill the product-form bump segment actually
            // produced. Self-limiting against the slot-order retry: that path clears
            // `forced` before looping, so a re-entry cannot charge twice.
            // ⚠ ATTRIBUTION. The charge must land on THE FLOOR, not on an operator who
            // turned the lane off. `--no-bump-lu` and an explicit
            // `bump_lu_override` both force the product-form path regardless of
            // `peel_nb`, so charging them books an A/B arm's own kill switch as
            // forgone cost of the floor. Both are inert at the default, so this does
            // not move any published number -- it stops the counter lying the first
            // time someone runs the arm it is measured against.
            // `!bump_active` rather than `peel_nb < bump_lu_min()`: once the trip
            // latches, the LU segment runs while the column floor still reads
            // "declined", so the charge would book `nnz(L)+nnz(U)` as fill the floor
            // forced onto the PRODUCT FORM -- the exact attribution failure the note
            // above exists to prevent. Pre-latch the two are identical, since under
            // `!forced.is_empty()` we have `!bump_active == peel_nb < bump_lu_min()`.
            // (`bump_lu_now` is not in scope here; it is derived below.)
            let charge_pfi_bump = !forced.is_empty()
                && !bump_active
                && self.bump_lu_override.is_none()
                && !no_bump_lu();
            let bump_lane: u8 = match self.bump_lu_override {
                Some(1) if bump_active => 1,
                Some(2) if bump_active => 2,
                Some(_) => 0,
                None => {
                    if !bump_active {
                        0
                    } else if bump_btf_env() {
                        2
                    } else if !no_bump_lu() {
                        1
                    } else {
                        0
                    }
                }
            };
            let bump_lu_now = bump_lane != 0;
            let diag = bump_diag_enabled() && !forced.is_empty();
            // The two segment snapshots below are `Etas::entries()` = `self.idx.len()`,
            // O(1), taken at two specific `di` values — not per column.
            let snap = diag || charge_pfi_bump;
            let seg_t0 = std::time::Instant::now();
            let (mut seg_ef, mut seg_eb) = (usize::MAX, usize::MAX);
            let (mut seg_tf, mut seg_tb) = (0.0f64, 0.0f64);
            for di in 0..deferred.len() {
                if snap && di == peel_nf {
                    seg_ef = self.etas.entries();
                    seg_tf = seg_t0.elapsed().as_secs_f64();
                }
                if snap && di == peel_nf + peel_nb {
                    seg_eb = self.etas.entries();
                    seg_tb = seg_t0.elapsed().as_secs_f64();
                }
                if bump_lu_now && di >= peel_nf && di < peel_nf + peel_nb {
                    if di == peel_nf {
                        let ok = if bump_lane == 2 {
                            self.bump_btf_segment(
                                lp,
                                peel_nf,
                                peel_nb,
                                &deferred,
                                tol,
                                fill_cap,
                                &mut kicked,
                            )
                        } else {
                            self.bump_lu_segment(
                                lp,
                                peel_nf,
                                peel_nb,
                                &deferred,
                                tol,
                                fill_cap,
                                &mut kicked,
                            )
                        };
                        bump_lu_used = ok;
                        if !ok || self.etas.entries() > fill_cap {
                            blew = true;
                            break;
                        }
                    }
                    continue;
                }
                let j = deferred[di];
                self.ftran(lp, j);
                let mut best: Option<usize> = None;
                let mut best_mag = tol;
                // Peel-forced pivot row (big-LP preorder): tolerance-guarded, with
                // the greedy scan as the fallback. `rf_new_basis == MAX` (rather
                // than `!rf_row_used`) is the "row still open" test because back
                // rows are pre-RESERVED in `rf_row_used`; a forced failure hands
                // the reservation back.
                let want = forced.get(di).copied().unwrap_or(usize::MAX);
                if want != usize::MAX && self.rf_new_basis[want] == usize::MAX {
                    if self.alpha[want].abs() > tol {
                        best = Some(want);
                    } else {
                        self.rf_row_used[want] = false;
                    }
                }
                // `nz` entries are `< m` (ftran invariant, debug-asserted there),
                // bounding alpha and the row-used mask — unchecked, as in the
                // pivot loops.
                if best.is_none() {
                    for &i in &self.nz {
                        // SAFETY: `ftran` guarantees each support row is less
                        // than `m`, which is the length of `rf_row_used`.
                        if unsafe { *self.rf_row_used.get_unchecked(i) } {
                            continue;
                        }
                        // SAFETY: `ftran` guarantees each support row is less
                        // than `m`, which is the length of `alpha`.
                        let a = unsafe { self.alpha.get_unchecked(i) }.abs();
                        if a > best_mag {
                            best_mag = a;
                            best = Some(i);
                        }
                    }
                }
                let Some(p) = best else {
                    // NO ADMISSIBLE PIVOT: this column is (numerically) a linear
                    // combination of the columns already placed — the basis is
                    // singular at working precision. This is NOT hypothetical, and
                    // it is not the rebuild's ordering: on air05's root LP the
                    // dense COMPLETE-pivoting check confirmed the basis exactly
                    // singular (rank 425/426, remaining mass ~4e-16). A degenerate
                    // pivot admitted on a drifted eta-file alpha had brought in a
                    // column exactly dependent on the rest (set partitioning is
                    // full of duplicate 0/1 columns). Abandoning the rebuild here
                    // — the old behavior — leaves the singular basis IN PLACE, so
                    // every later rebuild fails identically: 13,434 failed
                    // rebuilds against 180 successes in 60s, one every 1.7
                    // iterations, while the kept eta file grew unboundedly
                    // (~98k entries) and btran ate 58% of the wall clock.
                    //
                    // So REPAIR instead of abandon: KICK the dependent column out
                    // of the basis (it resumes the resting bound recorded in
                    // `at` — every column keeps one while basic) and let the
                    // logical fill below cover the row its departure leaves
                    // uncovered. The repaired basis is nonsingular by
                    // construction, self-consistent with the eta file built here,
                    // and everything downstream re-prices against it; a repair
                    // costs the walk a few pivots, never an answer (same
                    // advice-lane contract as the rest of this function).
                    kicked += 1;
                    for &i in &self.nz {
                        self.alpha[i] = 0.0;
                    }
                    continue;
                };
                let piv = self.alpha[p];
                let inv = 1.0 / piv;
                for &i in &self.nz {
                    // SAFETY: `ftran` guarantees every `i` in `nz` is less
                    // than `m`, which is the length of `alpha`.
                    let ai = unsafe { *self.alpha.get_unchecked(i) };
                    if i != p && ai != 0.0 {
                        self.etas.push_entry(i, -ai * inv);
                    }
                }
                self.etas.finish_eta(p, inv);
                self.rf_new_basis[p] = j;
                self.rf_row_used[p] = true;
                for &i in &self.nz {
                    // SAFETY: `ftran` guarantees every `i` in `nz` is less
                    // than `m`, which is the length of `alpha`.
                    unsafe { *self.alpha.get_unchecked_mut(i) = 0.0 };
                }
                if self.etas.entries() > fill_cap {
                    blew = true;
                    break;
                }
            }
            // ... and not from a peel the `fill_cap` blow-up is about to discard: that
            // fill is never installed, so it is not capability the floor withheld.
            if charge_pfi_bump && !blew && seg_ef != usize::MAX && seg_eb != usize::MAX {
                crate::sepstat::gate_charge(
                    crate::sepstat::GATE_BUMP_LU_FLOOR,
                    seg_eb.saturating_sub(seg_ef) as u64,
                );
                self.maybe_trip_bump_fill(seg_ef, seg_eb, peel_nf, peel_nb);
            }
            if diag {
                let e_end = self.etas.entries();
                let t_end = seg_t0.elapsed().as_secs_f64();
                let (ef, tf) = if seg_ef == usize::MAX {
                    (e_end, t_end)
                } else {
                    (seg_ef, seg_tf)
                };
                let (eb, tb) = if seg_eb == usize::MAX {
                    (e_end, t_end)
                } else {
                    (seg_eb, seg_tb)
                };
                eprintln!(
                    "--bump-diag rebuild: nf={peel_nf} nb={peel_nb} nk={} | entries F={ef} B={} K={} | t F={tf:.2}s B={:.2}s K={:.2}s | lu={} kicked={kicked} blew={blew}",
                    deferred.len().saturating_sub(peel_nf + peel_nb),
                    eb.saturating_sub(ef),
                    e_end.saturating_sub(eb),
                    tb - tf,
                    t_end - tb,
                    bump_lu_now,
                );
            }
            if !blew {
                break 'attempt;
            }
            // Fill blow-up under the peel order: reset the attempt state and
            // go again in the historical slot order, unguarded.
            if trace_enabled() {
                eprintln!(
                    "--trace refactorize: peel-order fill blew {} > {fill_cap}; slot-order retry",
                    self.etas.entries()
                );
            }
            self.etas.clear();
            self.rf_new_basis.clear();
            self.rf_new_basis.resize(self.m, usize::MAX);
            self.rf_row_used.clear();
            self.rf_row_used.resize(self.m, false);
            for &jj in &cols_list {
                if jj >= lp.n && !self.rf_row_used[jj - lp.n] {
                    self.rf_new_basis[jj - lp.n] = jj;
                    self.rf_row_used[jj - lp.n] = true;
                }
            }
            deferred = std::mem::take(&mut deferred_slot);
            forced.clear();
            fill_cap = usize::MAX;
        }
        self.rf_cols = cols_list;
        self.rf_deferred = deferred;
        // Surface the singular-repair kick count for the differential harness
        // (`factor_probe`). Both lanes factor the SAME basis, so the count is a
        // lane-invariant. Advisory only — no production path reads it.
        self.refactor_kicked = kicked;
        self.refactor_bump_lu_used = bump_lu_used;

        // BASIS REPAIR: fill every uncovered row with a LOGICAL. An uncovered
        // row `r` implies logical `n + r` is NOT in the basis (had it been,
        // the free pass above would have taken row `r`), and the deferred loop
        // only places columns that were in the basis — so each uncovered row
        // has its own logical available, and each placement consumes exactly
        // one unused row and one such logical. The pivot row is chosen like
        // any other (max |alpha| over unused rows): usually `r` itself, but
        // the eta transform may move it, which is fine — only the SET of
        // basis columns matters, position is bookkeeping.
        if kicked > 0 {
            for r in 0..self.m {
                if self.rf_new_basis[r] != usize::MAX {
                    continue;
                }
                let j = lp.n + r;
                self.ftran(lp, j);
                let mut best: Option<usize> = None;
                let mut best_mag = tol;
                for &i in &self.nz {
                    // SAFETY: `ftran` guarantees each support row is less
                    // than `m`, which is the length of `rf_row_used`.
                    if unsafe { *self.rf_row_used.get_unchecked(i) } {
                        continue;
                    }
                    // SAFETY: `ftran` guarantees each support row is less
                    // than `m`, which is the length of `alpha`.
                    let a = unsafe { self.alpha.get_unchecked(i) }.abs();
                    if a > best_mag {
                        best_mag = a;
                        best = Some(i);
                    }
                }
                if let Some(p) = best {
                    let piv = self.alpha[p];
                    let inv = 1.0 / piv;
                    for &i in &self.nz {
                        // SAFETY: `ftran` guarantees every `i` in `nz` is less
                        // than `m`, which is the length of `alpha`.
                        let ai = unsafe { *self.alpha.get_unchecked(i) };
                        if i != p && ai != 0.0 {
                            self.etas.push_entry(i, -ai * inv);
                        }
                    }
                    self.etas.finish_eta(p, inv);
                    self.rf_new_basis[p] = j;
                    self.rf_row_used[p] = true;
                }
                for &i in &self.nz {
                    self.alpha[i] = 0.0;
                }
            }
            REFAC_REPAIRS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            if trace_enabled() && REFAC_REPAIRS.load(std::sync::atomic::Ordering::Relaxed) <= 5 {
                eprintln!(
                    "--trace refactorize: singular basis repaired ({kicked} dependent column(s) kicked to their bounds)"
                );
            }
        }

        if self.rf_new_basis.iter().any(|&b| b == usize::MAX) {
            // Even the logical fill found no admissible pivot (float-noise
            // pathology): keep the old, self-consistent eta file — and DEFER
            // the retry, exactly as the LU arm does on a failed factor.
            // Leaving `since_refactor`/`eta_nnz` at their trigger values made
            // the pivot loop re-attempt this same doomed rebuild EVERY
            // iteration (the air05 thrash above). The next cadence trigger
            // retries on a changed basis; refactor timing is not a soundness
            // gate.
            std::mem::swap(&mut self.etas, &mut self.etas_spare);
            self.since_refactor = 0;
            self.eta_nnz = self.etas.entries().min(self.eta_nnz_cap.saturating_sub(1));
            // The kept old file is long and drifted while the counters just reset — the
            // cross-solve reuse must never adopt it at "age 0" (audit must-fix: the deferral
            // would otherwise defeat the age cap).
            self.factor_live = false;
            return;
        }
        self.basis.copy_from_slice(&self.rf_new_basis);
        for slot in self.basic_row.iter_mut() {
            *slot = None;
        }
        for (r, &b) in self.basis.iter().enumerate() {
            self.basic_row[b] = Some(r);
        }
        self.eta_nnz = self.etas.entries();
        self.since_refactor = 0;
        // BIG-LP CAP FLOOR: the nnz trigger exists to bound UPDATE growth, but
        // a heavy basis can REBUILD past the static cap — then the trigger
        // refires every `since_refactor >= 5` and the walk becomes a rebuild
        // storm (measured on the w5 crash walk: 10-12s rebuilds every 5
        // pivots once the rebuilt file crossed ~30M entries). Keep the cap
        // above the rebuilt floor so only growth can trigger. Monotone raise,
        // big LPs only — small LPs never rebuild past their static cap.
        if self.cols >= BIG_LP_COLS && self.m >= BIG_LP_ROWS {
            let floor = self.eta_nnz + (self.eta_nnz / 4).max(16 * self.m);
            if floor > self.eta_nnz_cap {
                self.eta_nnz_cap = floor;
            }
        }
        // The fresh file represents exactly the basis just (re)installed. (The
        // deferral return above deliberately does NOT set this: after a
        // `warm_start` adoption the kept old file represents the PRE-hint basis.)
        self.factor_live = true;
        self.chain_gen = 0;
        if self.cols >= BIG_LP_COLS && self.m >= BIG_LP_ROWS && trace_enabled() {
            eprintln!(
                "--trace refactorize: rebuilt {} etas / {} entries in {:.2}s",
                self.etas.len(),
                self.etas.entries(),
                _t.elapsed().as_secs_f64()
            );
        }
        REFAC_NANOS.fetch_add(
            u64::try_from(_t.elapsed().as_nanos()).unwrap_or(0),
            std::sync::atomic::Ordering::Relaxed,
        );
        // CHARGE THE LATE-PROMOTION BUDGET (`cold_lu_eta_rebuilds`) — here, at
        // the epilogue of a rebuild that ACTUALLY COMPLETED. The deferral return
        // above deliberately misses this: a deferred rebuild kept the old file
        // and did not pay for a new one.
        //
        // A count and not a cost estimate. Two cost units were tried here first
        // and both rank the corpus backwards — the static `m * nnz` and the
        // measured fill `etas.entries() + m`; the knob's own note carries the
        // contradicting pairs. What survives is the observation that the count
        // is the MULTIPLIER on a per-event difference that is favourable on 13
        // of 14 measured models, so counting is enough and sizing is not needed.
        self.eta_rebuilds = self.eta_rebuilds.saturating_add(1);
        ETA_REBUILD_TOTAL.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        // The per-solve MAXIMUM is what the budget is actually compared against,
        // so the calibration trace reports that rather than the process total —
        // a corpus sum cannot tell you where to put a per-solve threshold.
        ETA_REBUILD_MAX.fetch_max(
            u64::from(self.eta_rebuilds),
            std::sync::atomic::Ordering::Relaxed,
        );
    }

    /// The BUMP LU segment of the peel-ordered rebuild: gather the bump
    /// columns (ftran through the front etas already in the file — near
    /// no-ops, the peel guarantees bump columns admissibly hit no front row),
    /// factor them with `bump_eliminate` over the still-open rows, and emit
    /// the factorization into the eta file as L-etas (stage order, unit
    /// diagonal) followed by U-etas (reversed stage order, `1/u_kk`
    /// diagonal). Every pivoted column's file image is exactly its unit
    /// vector, so downstream — back columns' ftrans, warm PFI updates, the
    /// repair fill — is oblivious to the segment's internal shape.
    ///
    /// Returns `false` on a fill-cap breach inside the elimination; the
    /// caller falls back to the slot-order retry exactly as for a PFI
    /// fill-guard breach.
    #[allow(clippy::too_many_arguments)]
    fn bump_lu_segment(
        &mut self,
        lp: &FloatLp,
        nf: usize,
        nb: usize,
        deferred: &[usize],
        tol: f64,
        entry_cap: usize,
        kicked: &mut usize,
    ) -> bool {
        let _t = std::time::Instant::now();
        // Gather: transformed sparse bump columns. The eta file holds only
        // the front etas at this point, so each ftran is O(column nnz) plus
        // the (rare) front-dust transforms.
        let mut acols: Vec<Vec<(u32, f64)>> = Vec::with_capacity(nb);
        let mut gathered = 0usize;
        for &j in &deferred[nf..nf + nb] {
            self.ftran(lp, j);
            let mut col: Vec<(u32, f64)> = Vec::with_capacity(self.nz.len());
            for &i in &self.nz {
                col.push((i as u32, self.alpha[i]));
                self.alpha[i] = 0.0;
            }
            gathered += col.len();
            acols.push(col);
        }
        let open: Vec<bool> = self.rf_row_used.iter().map(|&u| !u).collect();
        if bump_scc_enabled() {
            eprintln!("--trace {}", bump_scc_histogram(self.m, &acols, &open));
        }
        let Some(f) = bump_eliminate(self.m, acols, &open, tol, entry_cap) else {
            return false;
        };
        // Emit L-etas in stage order (unit diagonal, entries -l_ik) ...
        let mut lnnz = 0usize;
        for (k, &(pr, lc, _)) in f.stages.iter().enumerate() {
            if !f.lcols[k].is_empty() {
                for &(r, lm) in &f.lcols[k] {
                    self.etas.push_entry(r as usize, -lm);
                }
                lnnz += f.lcols[k].len();
                self.etas.finish_eta(pr as usize, 1.0);
            }
            self.rf_new_basis[pr as usize] = deferred[nf + lc as usize];
            self.rf_row_used[pr as usize] = true;
        }
        // ... then U-etas in REVERSED stage order (back-substitution).
        let mut unnz = 0usize;
        for &(pr, lc, piv) in f.stages.iter().rev() {
            let inv = 1.0 / piv;
            for &(si, u) in &f.uhist[lc as usize] {
                self.etas
                    .push_entry(f.stages[si as usize].0 as usize, -u * inv);
            }
            unnz += f.uhist[lc as usize].len();
            self.etas.finish_eta(pr as usize, inv);
        }
        *kicked += f.kicked.len();
        if trace_enabled() {
            eprintln!(
                "--trace refactorize bump LU: {nb} cols ({gathered} gathered nnz) -> {} pivots, L {lnnz} + U {unnz} entries, {} kicked, {:.2}s",
                f.stages.len(),
                f.kicked.len(),
                _t.elapsed().as_secs_f64()
            );
        }
        true
    }

    /// The BLOCK-TRIANGULAR (BTF) segment of the peel-ordered rebuild — lane 2.
    /// Same role and signature as `bump_lu_segment`, but instead of one
    /// monolithic Markowitz core it factors the bump SCC-BLOCK by SCC-block.
    ///
    /// `bump_scc_blocks` decomposes the transformed bump columns into their
    /// Dulmage–Mendelsohn fine blocks (the strongly-connected cores of the
    /// column-dependency digraph) and hands back a topological emission order.
    /// Each block is factored by `bump_eliminate` with ONLY that block's matched
    /// rows open — so every entry landing in another block's row (or in a head /
    /// back row) rides along as pure L content, exactly as the monolithic lane
    /// lets non-open rows ride. Because the blocks are emitted SOURCES-first,
    /// each block's spill lands only in rows pivoted LATER: sub-diagonal L, so
    /// the composed eta file is the same operator as lane 1's — at
    /// `Σ nnz(L_block)+nnz(U_block)` entries, which for a near-triangular bump
    /// (a few small SCCs + thousands of singletons) is O(bump nnz) rather than
    /// the monolithic core's dense fill. Kicked columns accumulate exactly as in
    /// lane 1; returns `false` on any block's (or the accumulated file's)
    /// fill-cap breach, and the caller retries in slot order.
    fn bump_btf_segment(
        &mut self,
        lp: &FloatLp,
        nf: usize,
        nb: usize,
        deferred: &[usize],
        tol: f64,
        entry_cap: usize,
        kicked: &mut usize,
    ) -> bool {
        let _t = std::time::Instant::now();
        // Gather the transformed sparse bump columns — identical to lane 1.
        let mut acols: Vec<Vec<(u32, f64)>> = Vec::with_capacity(nb);
        let mut gathered = 0usize;
        for &j in &deferred[nf..nf + nb] {
            self.ftran(lp, j);
            let mut col: Vec<(u32, f64)> = Vec::with_capacity(self.nz.len());
            for &i in &self.nz {
                col.push((i as u32, self.alpha[i]));
                self.alpha[i] = 0.0;
            }
            gathered += col.len();
            acols.push(col);
        }
        // OPEN rows = the bump's own mid rows (head/back already own theirs in
        // `rf_row_used`), the exact pivot set — matched here and per block below.
        let open: Vec<bool> = self.rf_row_used.iter().map(|&u| !u).collect();
        if bump_scc_enabled() {
            eprintln!("--trace {}", bump_scc_histogram(self.m, &acols, &open));
        }
        // Block-triangular decomposition + topological (sources-first) order.
        let (col_block, block_order, col_row) = bump_scc_blocks(self.m, &acols, &open);
        let nblocks = block_order.len();
        let mut cols_by_block: Vec<Vec<usize>> = vec![Vec::new(); nblocks];
        for (c, &b) in col_block.iter().enumerate() {
            cols_by_block[b as usize].push(c);
        }
        let mut total_l = 0usize;
        let mut total_u = 0usize;
        let mut largest_block = 0usize;
        let mut nk = 0usize;
        // One reusable open mask (blocks' matched rows are disjoint, so each
        // iteration sets only its own rows and resets exactly those — no
        // per-block `vec![false; m]` over thousands of tiny blocks).
        let mut block_open = vec![false; self.m];
        for &blk in &block_order {
            let members = &cols_by_block[blk as usize];
            if members.is_empty() {
                continue;
            }
            largest_block = largest_block.max(members.len());
            // This block's columns, and an open mask holding ONLY its matched
            // rows: everything else (earlier/closed blocks, head, back) rides as
            // L content. The matching is a bijection, so a block's matched rows
            // are disjoint from every other block's — no open-mask overlap.
            let mut block_acols: Vec<Vec<(u32, f64)>> = Vec::with_capacity(members.len());
            for &c in members {
                if col_row[c] != usize::MAX {
                    block_open[col_row[c]] = true;
                }
                block_acols.push(std::mem::take(&mut acols[c]));
            }
            let f = bump_eliminate(self.m, block_acols, &block_open, tol, entry_cap);
            // Reset only this block's rows before any early return / next block.
            for &c in members {
                if col_row[c] != usize::MAX {
                    block_open[col_row[c]] = false;
                }
            }
            let Some(f) = f else {
                return false;
            };
            // Emit L-etas (stage order) then U-etas (reversed) — exactly as
            // `bump_lu_segment`, remapping block-local column indices back to the
            // global `deferred[nf + ..]` slot via this block's `members`.
            for (k, &(pr, lc, _)) in f.stages.iter().enumerate() {
                if !f.lcols[k].is_empty() {
                    for &(r, lm) in &f.lcols[k] {
                        self.etas.push_entry(r as usize, -lm);
                    }
                    total_l += f.lcols[k].len();
                    self.etas.finish_eta(pr as usize, 1.0);
                }
                self.rf_new_basis[pr as usize] = deferred[nf + members[lc as usize]];
                self.rf_row_used[pr as usize] = true;
            }
            for &(pr, lc, piv) in f.stages.iter().rev() {
                let inv = 1.0 / piv;
                for &(si, u) in &f.uhist[lc as usize] {
                    self.etas
                        .push_entry(f.stages[si as usize].0 as usize, -u * inv);
                }
                total_u += f.uhist[lc as usize].len();
                self.etas.finish_eta(pr as usize, inv);
            }
            *kicked += f.kicked.len();
            nk += f.kicked.len();
            // The per-block `bump_eliminate` caps its OWN L+U; the file across
            // blocks can still overrun the peel-order guard — bail to the
            // slot-order retry, same contract as lane 1.
            if self.etas.entries() > entry_cap {
                return false;
            }
        }
        if trace_enabled() {
            eprintln!(
                "--trace refactorize bump BTF: {nb} cols ({gathered} gathered nnz) -> {nblocks} blocks (largest {largest_block}), L {total_l} + U {total_u} = {} fill, {nk} kicked, {:.2}s",
                total_l + total_u,
                _t.elapsed().as_secs_f64()
            );
        }
        true
    }

    /// Reduced cost of column `j`: `cost_j - y·M_j`. For a logical `n + r`,
    /// `M_j = -e_r` and its cost is zero, so this is simply `y_r`.
    ///
    /// Pricing calls this once per column per iteration; the gather runs
    /// unchecked under the CSC invariants (`col_idx` entries `< m == y.len()`,
    /// `col_ptr` monotone within bounds), asserted in debug builds.
    #[inline]
    fn reduced_cost(&self, lp: &FloatLp, j: usize, phase1: bool) -> f64 {
        let c = if phase1 { 0.0 } else { self.pcost[j] };
        if j < lp.n {
            let (s, e) = (lp.col_ptr[j], lp.col_ptr[j + 1]);
            debug_assert!(e <= lp.col_idx.len() && s <= e);
            let mut dot = 0.0f64;
            // SAFETY: `s..e` bounds the aligned CSC index/value arrays, and
            // every stored row is less than `self.y.len()` by construction.
            unsafe {
                let ci = lp.col_idx.as_ptr();
                let cv = lp.p_col_val().as_ptr();
                let yp = self.y.as_ptr();
                for q in s..e {
                    let r = *ci.add(q);
                    debug_assert!(r < self.y.len());
                    dot += *yp.add(r) * *cv.add(q);
                }
            }
            c - dot
        } else {
            c + self.y[j - lp.n]
        }
    }

    /// `arow[0..n] <- yᵀ A` over the structural columns, row-major: one
    /// sequential sweep of the matrix instead of a scattered gather of `y`
    /// per column. For each column the contributions arrive in ascending row
    /// order — exactly the order `reduced_cost`'s CSC gather sums them — so
    /// `cost[j] - arow[j]` reproduces its bits (modulo the sign of an exact
    /// zero, which no consumer can see: every test is against a tolerance).
    ///
    /// This exists for the FULL-SWEEP consumers (`priced_out`,
    /// `dual_violations`, the dual's reduced-cost rebuilds): they price every
    /// column anyway, so the row-major pass does the same flops with
    /// sequential loads, and the dense mirror (when built) drops the index
    /// loads too.
    fn fill_yta(&mut self, lp: &FloatLp) {
        let n = lp.n;
        for v in self.arow[..n].iter_mut() {
            *v = 0.0;
        }
        if !lp.p_dense_rows().is_empty() {
            for (r, dr) in lp.p_dense_rows().chunks_exact(n).enumerate() {
                let y_r = self.y[r];
                if y_r == 0.0 {
                    continue;
                }
                for (aj, &v) in self.arow[..n].iter_mut().zip(dr) {
                    *aj += y_r * v;
                }
            }
        } else {
            // Unchecked under the CSR invariants (`row_idx` entries `< n`,
            // `row_ptr` monotone within bounds), asserted in debug builds.
            // SAFETY: Every `row_ptr` range bounds the aligned CSR index/value
            // arrays, and each stored column is less than `n <= arow.len()`.
            unsafe {
                let ri = lp.row_idx.as_ptr();
                let rv = lp.p_row_val().as_ptr();
                let ap = self.arow.as_mut_ptr();
                for r in 0..self.m {
                    let y_r = self.y[r];
                    if y_r == 0.0 {
                        continue;
                    }
                    let (s, e) = (lp.row_ptr[r], lp.row_ptr[r + 1]);
                    debug_assert!(e <= lp.row_idx.len() && s <= e);
                    for q in s..e {
                        let j = *ri.add(q) as usize;
                        debug_assert!(j < n);
                        *ap.add(j) += y_r * *rv.add(q);
                    }
                }
            }
        }
    }

    /// The final primal values (every column) and row duals, in f64.
    fn extract(&mut self, lp: &FloatLp) -> (Vec<f64>, Vec<f64>) {
        let mut values = vec![0.0f64; self.cols];
        for j in 0..self.cols {
            values[j] = match self.basic_row[j] {
                Some(r) => self.xb[r],
                None => self.nb_value(lp, j),
            };
        }
        // y = c_B B^{-1} under the true (phase-II) costs — unless `y` already
        // holds exactly that (`priced_out` on the dual-settled path computes it
        // last thing), in which case recomputing would produce the same bits.
        if !self.y_is_duals {
            for i in 0..self.m {
                self.cb[i] = self.pcost[self.basis[i]];
            }
            self.y.copy_from_slice(&self.cb);
            self.btran();
            self.y_is_duals = true;
        }
        let mut duals = self.y.clone();
        // Cross back into the ORIGINAL frame: x_j = C_j·x'_j, s_r = s'_r/R_r,
        // y_r = R_r·y'_r — exact power-of-two multiplies. The solver's own state
        // (xb, y) stays in the pivot frame; only the exported copies convert.
        if lp.scaled() {
            for j in 0..self.cols {
                values[j] *= lp.val_mul[j];
            }
            for r in 0..self.m {
                duals[r] *= lp.bnd_mul[lp.n + r];
            }
        }
        (values, duals)
    }

    /// Adopt a parent's basis and resting bounds.
    ///
    /// The bounds this node runs under are not the parent's, so a column the
    /// parent left resting on a bound may now be resting on one that no longer
    /// exists (branching moved it). Any such column is re-seated on a bound this
    /// node actually has. Anything inconsistent is caught downstream: the basis is
    /// refactorized, the basic values recomputed, and phase I run — a warm start
    /// is a HINT, and a bad hint costs pivots, not correctness.
    fn warm_start(
        &mut self,
        lp: &FloatLp,
        basis: &[usize],
        at: &[NbBound],
        lower: &[f64],
        upper: &[f64],
    ) {
        // A SHORT BASIS FROM BEFORE CUTS GREW THE LP -- EXTEND IT, DON'T REJECT IT.
        //
        // Node-level cut separation APPENDS rows to the LP, so a warm basis captured earlier has
        // `basis.len() = old_m < self.m` and `at.len() = old_cols < self.cols`. Rejecting it forces a
        // cold start on every node after a cut is added -- the "cold-start storm" that made live node
        // cutting a 13x throughput loss. But the extension is trivial and exact: the new rows are the
        // TAIL `[old_m, m)`, and making each new row's own slack basic (`[n+old_m, n+m)`) is a valid
        // basis (block-triangular `[B_old 0; C I]`), because a bound change never moved the old
        // columns and a fresh slack absorbs its new row's activity. So pad, don't discard.
        let old_m = basis.len();
        let mut ext_basis: Vec<usize>;
        let mut ext_at: Vec<NbBound>;
        let (basis, at) = if old_m < self.m && at.len() == lp.n + old_m {
            ext_basis = Vec::with_capacity(self.m);
            ext_basis.extend_from_slice(basis);
            ext_basis.extend((lp.n + old_m)..self.cols); // the new rows' own slacks, basic
            ext_at = Vec::with_capacity(self.cols);
            ext_at.extend_from_slice(at);
            ext_at.resize(self.cols, NbBound::Lower); // new slacks are basic; `at` unused for them
            (ext_basis.as_slice(), ext_at.as_slice())
        } else {
            (basis, at)
        };
        if basis.len() != self.m || at.len() != self.cols {
            self.crash_basis(lp); // malformed hint: (re-)install the crash basis
            return;
        }
        // CROSS-SOLVE ETA REUSE: is the hint bit-identical to the basis the pooled
        // eta file still represents (`reset(keep_factor)` carried it over)? Then
        // the rebuild at the bottom is factoring what the file already IS. The
        // common case is the DFS child popped immediately after its parent: its
        // hint is the parent's final basis, which is exactly the pool's state
        // (pk1: 370k of 565k node solves; the rebuild was 2.7s of a 21s proof).
        // Freshness is capped like the LU arm's skip and for the same reason —
        // any verify-loop-triggered refactorize must genuinely rebuild (see the
        // deadlock journal there); the cap also bounds cross-solve drift to the
        // same eta-age every WITHIN-solve pivot run already tolerates.
        let same = self.factor_live && !no_eta_reuse() && basis == self.basis.as_slice();
        // The basis is about to change under `y`.
        self.y_is_duals = false;
        // A CHANGED basis: install it and rebuild the row map. When `same`, the
        // pooled `self.basis`/`self.basic_row` ALREADY are this hint — carried
        // across the pool boundary by `reset(keep_factor)`, and `same` implies
        // `factor_live`, so they were validated when last set — making the
        // copy_from_slice and the O(cols+m) clear+rebuild (and its validity
        // scan) pure redundant work that reproduces the state already in hand.
        // Byte-identical: both exits below (the reuse early-return and the
        // refactorize fall-through) read the same `self.basis`/`self.basic_row`
        // whether or not this block runs.
        if !same {
            self.factor_live = false; // adopting a basis the file does not represent
            self.basis.copy_from_slice(basis);
            for slot in self.basic_row.iter_mut() {
                *slot = None;
            }
            for r in 0..self.m {
                let b = self.basis[r];
                if b >= self.cols || self.basic_row[b].is_some() {
                    // Duplicate or out-of-range: fall back to the crash basis.
                    self.crash_basis(lp);
                    return;
                }
                self.basic_row[b] = Some(r);
            }
        }
        for j in 0..self.cols {
            self.at[j] = match at[j] {
                NbBound::Lower if lower[j].is_finite() => NbBound::Lower,
                NbBound::Upper if upper[j].is_finite() => NbBound::Upper,
                _ => {
                    if lower[j].is_finite() {
                        NbBound::Lower
                    } else if upper[j].is_finite() {
                        NbBound::Upper
                    } else {
                        NbBound::Zero
                    }
                }
            };
        }
        // The reuse skip (see `same` above). LU solves keep calling through —
        // the LU arm has its own `rep_basis` match inside `refactorize`.
        if same
            && self.lu.is_none()
            && self.chain_gen <= eta_gen_cap()
            && self.since_refactor < eta_reuse_age()
            && self.eta_nnz < self.eta_nnz_cap
        {
            self.chain_gen += 1;
            ETA_REUSE_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            return;
        }
        refac_reason(0);
        self.refactorize(lp);
    }

    /// TRIANGULAR EQUALITY CRASH — the big-LP cold-start basis.
    ///
    /// The cifar100 window MILPs (and NN-verification LPs generally) are a
    /// layered affine CHAIN: 18,533 of w5's 18,692 rows are equalities
    /// `z = Wx + b`, and the whole equality block peels TRIANGULARLY — repeat
    /// "a column incident to exactly one unpeeled equality row is that row's
    /// output" until fixpoint (measured on w5: 18,533/18,533 rows peel, all
    /// diagonal pivots ±1 except one at 0.317). The all-logical crash starts
    /// every one of those rows' logicals basic AND FIXED (`lo == up`) — the
    /// maximally-degenerate start the `MAX_ITERS` note above indicts — and
    /// phase 1 walks ~24k iterations to undo it (measured 715s on w5).
    /// Crashing the peeled outputs basic instead starts phase 1 at the
    /// FORWARD-PROPAGATED point: w5 measures 2,179 violated basics of total
    /// mass 19.6 vs 18,533 fixed logicals.
    ///
    /// The peel order is the factorization: reversed, each peeled column has
    /// no support in earlier-processed rows, so its FTRAN is the raw column
    /// and the eta build is ZERO-FILL (entries = the basis columns' own
    /// nonzeros, ~69% of matrix nnz on w5). Costs: one O(nnz) peel + one
    /// zero-fill build, once per cold big-LP solve.
    ///
    /// ADVICE-LANE: any starting basis is a valid starting basis; phase 1/2
    /// and every downstream exact check are untouched. FAIL-CLOSED: a tiny
    /// forced pivot or eta-entry growth (a non-triangular assignment on some
    /// future model) abandons the build and falls back to the all-logical
    /// crash. Gated to `cols >= BIG_LP_COLS && m >= BIG_LP_ROWS` cold solves on the eta path
    /// (`the tri-crash-all knob` forces it on small LPs for tests;
    /// `AY_MILP_NO_TRI_CRASH` kills it). The typed
    /// `SolveOpts::with_range_logical_triangular_crash()` request, or the
    /// historical exact `AY_MILP_RANGE_LOGICAL_CRASH=1` compatibility opt-in,
    /// additionally admits a fully peeled equality block when bounded-range
    /// rows are the majority, retaining those rows' logicals as the `-I`
    /// lower-right block. The ladder/corpus band never sees either opt-in,
    /// keeping their default float paths and pace byte-identical.
    ///
    /// Returns `true` if the crash basis was installed.
    fn triangular_crash(&mut self, lp: &FloatLp, retain_range_logicals: bool) -> bool {
        /// Entries below this are not trusted as structure (denormal noise).
        const TINY: f64 = 1e-11;
        /// Forced diagonal pivots below this abort the build (fail-closed).
        const MIN_PIVOT: f64 = 1e-7;
        let n = lp.n;
        let m = lp.m;
        debug_assert!(self.etas.len() == 0, "crash runs on the fresh state");
        // Equality rows (the fresh crash state has every logical basic).
        let mut eq = vec![false; m];
        let mut neq = 0usize;
        for r in 0..m {
            if self.lo[n + r] == self.up[n + r] {
                eq[r] = true;
                neq += 1;
            }
        }
        // Not an equality-chain model: peeling would place too little of the
        // basis to change the phase-1 regime; keep the all-logical start.
        if neq * 2 < m && !retain_range_logicals {
            if trace_enabled() {
                eprintln!("--trace triangular crash declined: {neq}/{m} equality rows");
            }
            return false;
        }
        // count[j] = number of unpeeled equality rows column j is incident to
        // (entries above TINY, columns that can rest basic, i.e. not fixed).
        let mut count = vec![0u32; n];
        for r in 0..m {
            if !eq[r] {
                continue;
            }
            for p in lp.row_ptr[r]..lp.row_ptr[r + 1] {
                let j = lp.row_idx[p] as usize;
                if self.lo[j] < self.up[j] && lp.p_row_val()[p].abs() > TINY {
                    count[j] += 1;
                }
            }
        }
        // Peel: a column with exactly one remaining equality row is that row's
        // output. Deterministic (index-ordered queue seeding, FIFO growth).
        let mut queue: std::collections::VecDeque<u32> =
            (0..n as u32).filter(|&j| count[j as usize] == 1).collect();
        let mut placed = vec![false; m];
        let mut assigned = vec![usize::MAX; m]; // row -> its output column
        let mut peel: Vec<u32> = Vec::with_capacity(neq);
        while let Some(j32) = queue.pop_front() {
            let j = j32 as usize;
            if count[j] != 1 {
                continue;
            }
            // The single unpeeled admissible equality row of column j.
            let mut row = usize::MAX;
            for p in lp.col_ptr[j]..lp.col_ptr[j + 1] {
                let r = lp.col_idx[p];
                if eq[r] && !placed[r] && lp.p_col_val()[p].abs() > TINY {
                    row = r;
                    break;
                }
            }
            if row == usize::MAX {
                continue; // count says 1 but no admissible row: stale entry, skip
            }
            placed[row] = true;
            assigned[row] = j;
            peel.push(row as u32);
            count[j] = 0;
            for p in lp.row_ptr[row]..lp.row_ptr[row + 1] {
                let jj = lp.row_idx[p] as usize;
                if self.lo[jj] < self.up[jj] && lp.p_row_val()[p].abs() > TINY {
                    let c = &mut count[jj];
                    if *c > 0 {
                        *c -= 1;
                        if *c == 1 {
                            queue.push_back(jj as u32);
                        }
                    }
                }
            }
        }
        let full_equality_peel = neq > 0 && peel.len() == neq;
        if peel.len() * 2 < m && !(retain_range_logicals && full_equality_peel) {
            // Peel too shallow to be worth a heavier inverse. The depth is the
            // diagnostic: a conv/DAG block whose columns all touch several
            // equality rows never seeds the singleton queue, and the peel
            // stalls at the block boundary (the same bump the refactorize
            // preorder isolates) — that number decides whether the fix is a
            // bump-capable crash or nothing.
            if trace_enabled() {
                eprintln!(
                    "--trace triangular crash declined: peel {}/{neq} eq rows (m={m})",
                    peel.len()
                );
            }
            return false;
        }
        // Install in REVERSED peel order: each column's ftran meets no prior
        // pivot row, so alpha is the raw folded column and the build is
        // zero-fill. `ftran` (not a raw column copy) keeps this correct even
        // if a future model breaks triangularity — then fill appears and the
        // entries cap below abandons the build.
        let entries_cap = 2 * lp.col_idx.len() + 16 * m;
        let mut ok = true;
        for k in (0..peel.len()).rev() {
            let r = peel[k] as usize;
            let j = assigned[r];
            self.ftran(lp, j);
            let piv = self.alpha[r];
            if piv.abs() < MIN_PIVOT {
                ok = false;
            } else {
                let inv = 1.0 / piv;
                for &i in &self.nz {
                    let ai = self.alpha[i];
                    if i != r && ai != 0.0 {
                        self.etas.push_entry(i, -ai * inv);
                    }
                }
                self.etas.finish_eta(r, inv);
                self.basis[r] = j;
                self.basic_row[j] = Some(r);
                self.basic_row[n + r] = None;
                // The displaced logical is an equality row's: fixed, resting
                // on its (coincident) bounds — `reset`'s own convention.
                self.at[n + r] = NbBound::Lower;
            }
            for &i in &self.nz {
                self.alpha[i] = 0.0;
            }
            self.nz.clear();
            if !ok || self.etas.entries() > entries_cap {
                // FAIL-CLOSED: restore the all-logical crash wholesale (basis,
                // eta file, counters); `at` mutations match `reset`'s values
                // for fixed logicals, so nothing else needs undoing.
                if trace_enabled() {
                    eprintln!(
                        "--trace triangular crash declined: {} at row {}/{} ({} eta entries, cap {entries_cap})",
                        if ok { "eta blow-up" } else { "tiny pivot" },
                        peel.len() - k,
                        peel.len(),
                        self.etas.entries()
                    );
                }
                self.crash_basis(lp);
                return false;
            }
        }
        self.eta_nnz = self.etas.entries();
        self.since_refactor = 0;
        self.factor_live = true;
        if retain_range_logicals {
            self.range_logical_crash_installed = true;
        }
        self.chain_gen = 0;
        if trace_enabled() && retain_range_logicals {
            eprintln!(
                "--trace range-logical triangular crash: equality_rows={neq} \
                 range_rows={} peeled={} retained_range_logicals={} eta_entries={}",
                m - neq,
                peel.len(),
                m - neq,
                self.etas.entries()
            );
        } else if trace_enabled() {
            eprintln!(
                "--trace triangular crash: peeled {}/{neq} equality rows ({} eta entries)",
                peel.len(),
                self.etas.entries()
            );
        }
        true
    }

    /// (Re-)install the crash basis `B = -I` with a CONSISTENT (empty) eta file —
    /// the state every fallback in `warm_start` must leave behind now that the
    /// pool can carry a live file across solves (`reset(keep_factor)`).
    fn crash_basis(&mut self, lp: &FloatLp) {
        self.y_is_duals = false;
        self.basic_row.fill(None);
        for r in 0..self.m {
            self.basis[r] = lp.n + r;
            self.basic_row[lp.n + r] = Some(r);
        }
        self.etas.clear();
        self.since_refactor = 0;
        self.eta_nnz = 0;
        self.factor_live = true; // the empty file IS the crash inverse
        self.chain_gen = 0;
        if let Some(cache) = self.lu.as_mut() {
            cache.eng.reset_to_identity();
            cache.rep_basis.clear();
            cache.rep_basis.extend(lp.n..lp.n + self.m);
        }
    }

    /// Dual-feasible objective `z = c·x` at the current basis (basics from
    /// `xb`, nonbasics resting on a bound) — the same frame-invariant sum the
    /// cutoff early-stop computes. Anatomy-only (see `dual_anat_commit`).
    fn dual_anat_z(&self, lp: &FloatLp) -> f64 {
        let mut z = 0.0f64;
        for i in 0..self.m {
            z += self.pcost[self.basis[i]] * self.xb[i];
        }
        for &ju in &self.nzcost {
            let j = ju as usize;
            if self.basic_row[j].is_none() {
                let x = self.nb_value(lp, j);
                if x.is_finite() {
                    z += self.pcost[j] * x;
                }
            }
        }
        z
    }

    /// Fold this walk's per-walk anatomy accumulators into the global bucket
    /// `b` (0 = noenter, 1 = optimum, 2 = other) and, for noenter walks, the
    /// length histogram. Anatomy-only: never called unless
    /// `dual_anatomy_enabled()`. `iters` is the pivot count at exit.
    fn dual_anat_commit(&self, lp: &FloatLp, b: usize, iters: usize) {
        use std::sync::atomic::Ordering::Relaxed;
        DUAL_ANAT_WALKS[b].fetch_add(1, Relaxed);
        DUAL_ANAT_ITERS[b].fetch_add(iters as u64, Relaxed);
        DUAL_ANAT_DTHETA[b].fetch_add(self.anat_dtheta, Relaxed);
        DUAL_ANAT_DSTEP[b].fetch_add(self.anat_dstep, Relaxed);
        DUAL_ANAT_FLIP[b].fetch_add(self.anat_flip, Relaxed);
        let z1 = self.dual_anat_z(lp);
        if (z1 - self.anat_z0).abs() < DUAL_ANAT_ZTOL {
            DUAL_ANAT_ZFLAT[b].fetch_add(1, Relaxed);
        }
        if b == 0 {
            let bucket = match iters {
                0 => 0,
                1..=8 => 1,
                9..=32 => 2,
                33..=64 => 3,
                65..=128 => 4,
                129..=256 => 5,
                _ => 6,
            };
            DUAL_ANAT_NOENTER_HIST[bucket].fetch_add(1, Relaxed);
        }
    }

    /// The BOUNDED DUAL SIMPLEX — the mechanism behind branch-and-bound node
    /// throughput.
    ///
    /// Branching changes a BOUND, not the matrix and not the costs, so a child's
    /// inherited basis is still DUAL feasible — every reduced cost still points the
    /// way its bound requires — and is only PRIMAL infeasible, in the one column that
    /// was branched on. Handing that to phase I throws the information away.
    ///
    /// This repairs the primal directly while HOLDING dual feasibility: take a basic
    /// variable outside its bounds, drive it onto the bound it violates, and let the
    /// dual ratio test pick the entering column so that no reduced cost changes sign.
    ///
    /// It is allowed to FAIL — `false` sends the caller to the primal from scratch,
    /// which is always right and merely slower. Degeneracy offers many zero-length
    /// dual steps, so Bland's rule engages after a stall (smallest index wins, which
    /// makes a cycle impossible) and a hard budget caps the rest. This lane may be
    /// slow; it may not be wrong, and it may not hang.
    /// `budget` is the pivot allowance: warm children get `2m+50` (a child far
    /// from its parent is better handed to the primal), the COLD set-partitioning
    /// start gets a multiple of that (it is doing the whole solve, not a repair).
    ///
    /// WRAPPER for `dual_simplex_inner`: on the qiu-class LP (see
    /// `should_perturb_dual`) it restores the TRUE costs (saved into `pcost_save`
    /// by the inner walk's perturbation block) on EVERY exit, so the many inner
    /// `return` points need no restore of their own. A no-op on every other LP.
    fn dual_simplex(
        &mut self,
        lp: &FloatLp,
        deadline: Option<std::time::Instant>,
        budget: usize,
    ) -> bool {
        // ITERATION LEDGER: `dual_simplex_inner`'s pivot loop owns the ONLY
        // `stats::DUAL_ITERS` bump site, so charging its delta here attributes
        // every dual pivot in the process to the phase that asked for it. One
        // flag read + two relaxed loads per WALK, nothing per pivot.
        let led = iter_ledger_enabled().then(|| stats::get(&stats::DUAL_ITERS));
        let r = self.dual_simplex_inner(lp, deadline, budget);
        if let Some(before) = led {
            PHASE_DUAL[ledger_phase()].fetch_add(
                stats::get(&stats::DUAL_ITERS).wrapping_sub(before),
                std::sync::atomic::Ordering::Relaxed,
            );
        }
        if self.dual_perturb_active {
            // Bit-exact restore of the un-perturbed costs. `pcost` is only READ
            // by the walk, never written, so the saved slice is authoritative.
            self.pcost.copy_from_slice(&self.pcost_save);
            self.dual_perturb_active = false;
        }
        r
    }

    /// Recompute the dual ratio-test eligibility bitmask `rt_kind` from scratch
    /// over every column: `0` = ineligible (basic OR nonbasic-free-at-zero), `1` =
    /// nonbasic at lower bound, `2` = nonbasic at upper bound. Called once at the
    /// top of `dual_simplex_inner` (before the pivot loop) so the incremental
    /// maintenance at the flip/pivot commits starts from a correct snapshot; every
    /// OTHER basis mutation (crash, warm-start, cold-dual, primal phase, refactor)
    /// precedes the next dual entry and is therefore captured here. Pure function
    /// of `basic_row` + `at`, so it exactly reproduces the 4-stream scan's filter.
    fn rebuild_rt_kind(&mut self) {
        let cols = self.cols;
        if self.rt_kind.len() < cols {
            self.rt_kind.resize(cols, 0);
        }
        for j in 0..cols {
            self.rt_kind[j] = if self.basic_row[j].is_some() {
                0
            } else {
                match self.at[j] {
                    NbBound::Zero => 0,
                    NbBound::Lower => 1,
                    NbBound::Upper => 2,
                }
            };
        }
    }

    /// Shape gate for the dual cost perturbation. TIGHT to the qiu class — the
    /// SAME predicate as the `tall_lu` bloom-cap relaxation: `tall_lu` (m ≥ 1,000)
    /// catches qiu and, in the corpus, ONLY qiu (air05/air03/nw04 are `wide_tall`
    /// but < 1,000 rows; the dense ladder is square and short). `!chain_class`
    /// excludes the badly-scaled layered-affine-chain class (k124 ACAS
    /// certification, big-M), whose warm dual THRASHES rather than churns and
    /// whose proof a perturbation would risk (the same exclusion the bloom relax
    /// makes). The FLIP_LNS caller is excluded like the bloom relax. A blanket
    /// perturbation once KILLED air03's proof, so the gate is deliberately narrow.
    fn should_perturb_dual(&self, lp: &FloatLp) -> bool {
        !no_dual_perturb()
            && dual_perturb_mag() > 0.0
            && lp.tall_lu()
            && !lp.chain_class()
            && caller_tag() != CALLER_FLIP_LNS
    }

    /// B19 flip-arm choice: forced sparse needs live LU; auto applies the
    /// FT-spike predicted-marked-set test and selects dense on ties.
    fn prepare_sparse_flip_solve(&mut self, lp: &FloatLp, mode: usize) -> bool {
        let sparse = match mode {
            2 => false,
            1 => self.lu.is_some(),
            _ => self.lu.as_ref().is_some_and(|cache| {
                let m = self.m;
                let unnz = cache.eng.unnz();
                let est: usize = self
                    .flips
                    .iter()
                    .map(|&ju| {
                        let j = ju as usize;
                        if j < lp.n {
                            lp.col_ptr[j + 1] - lp.col_ptr[j]
                        } else {
                            1
                        }
                    })
                    .sum();
                est.saturating_mul(m.saturating_add(unnz)).saturating_mul(2) < m.saturating_mul(m)
            }),
        };
        self.wflip.fill(0.0);
        sparse
    }

    fn dual_simplex_inner(
        &mut self,
        lp: &FloatLp,
        deadline: Option<std::time::Instant>,
        budget: usize,
    ) -> bool {
        DUAL_CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        // Per-walk anatomy (trace-only, `AY_MILP_DUAL_ANATOMY`): reset the
        // accumulators; `anat_z0` is captured just before the loop, once the
        // entry bound-flip repair has settled the starting basis.
        let anat = dual_anatomy_enabled();
        if anat {
            self.anat_dtheta = 0;
            self.anat_dstep = 0;
            self.anat_flip = 0;
        }

        let feas_tol = self.feas_tol(lp);
        let pivot_tol = self.pivot_tol();
        // Width of the Harris band in the ratio test below — reduced-cost units,
        // so sized like `cost_tol` (see the band note at its use).
        let cost_tol_band = self.cost_tol(lp);
        // Fused single-pass BFRT ratio test (Stage A: fold the min-scan into the
        // build loop; Stage B: defer `self.bp` on a non-churn-band no-flip step).
        // Read once here — the OnceLock is cheap but the ratio test runs millions
        // of times per tree. `defer_ok` gates Stage B off for churn-band shapes,
        // whose fast/slow paths BOTH need `self.bp` for the Harris band.
        let fused_rt = fused_rt_enabled();
        let rt_masked = rt_masked_enabled();
        // Stage B (deferral) is OFF by default — it is a wash-to-loss (see
        // `fused_defer_enabled`). `AY_MILP_FUSED_RT` therefore ships Stage A alone.
        let defer_ok = fused_rt && fused_defer_enabled() && !lp.dual_churn_band();
        let rt_profile = iter_profile_enabled();
        let rt_bits_key = rt_bits_key_enabled();
        let tau_nz = tau_nz_enabled();
        let flip_solve = flip_solve_mode();
        let bland_after = budget / 4;
        let mut stall = 0usize;
        // No stale Farkas candidate may survive into this walk (see `noenter_ray`).
        self.noenter_ray = None;
        // DIVERGENCE GUARD. A healthy warm dual fixes a bound change in ~tens of
        // pivots (28 it/call measured at w2 nodes). On the badly-scaled NN
        // matrices the dual can instead THRASH: the pin-probe repro enters with
        // ONE violated row (0.134) and blooms to ~1,100 violated rows by pivot
        // 500, oscillating there until the 2m+50 budget burns ~25s — after
        // which the transactional rollback lets the primal solve it anyway.
        // Count violated basics at entry; re-count every 128 pivots; if the
        // count has grown far past the entry state, the attempt has failed —
        // returning false here is exactly the failure path (snapshot rollback),
        // it just fires in ~0.3s instead of 25.
        let entry_viol = {
            let mut c = 0usize;
            for i in 0..self.m {
                let b = self.basis[i];
                let ft = feas_tol * lp.bmul(b);
                let v = self.xb[i];
                if v < self.lo[b] - ft || v > self.up[b] + ft {
                    c += 1;
                }
            }
            c
        };
        let bloom_cap = match dual_bloom_cap_override() {
            Some(0) => usize::MAX, // guard disabled
            Some(c) => c,
            // WIDE-AND-TALL SET-PARTITIONING: the divergence guard exists for the
            // badly-scaled NN matrices, where a warm dual enters with ~1 violated
            // row and BLOOMS to ~1,100 and never recovers, thrashing until the
            // budget burns 25s. Those matrices are layered affine chains — roughly
            // SQUARE (n≈m), so `wide_tall` is false and they keep the guard. A wide
            // 0/1 set-partitioning LP (air05: 426×7,195) is the opposite case: a
            // one-bound-change child's warm dual TEMPORARILY grows the violated set
            // to a few hundred rows before receding to primal feasibility in ~600
            // pivots — healthy dual behaviour the `max(64)` cap kills at pivot 127,
            // forcing a rollback and a full cold re-crash (~2-4k pivots), so the
            // node pays warm-fail + cold. These LPs are well-scaled (unit 0/1) and
            // cannot thrash the NN way; the iteration budget is the real backstop.
            // Verdict-neutral: only the walk length changes; every exit is
            // re-checked and every leaf re-derived exactly. `wide_tall` (n≥10m ∧
            // m≥floor) matches air05/air03/nw04 and NOT the NN/qiu tall shapes.
            None if lp.wide_tall() && !no_wide_bloom() => usize::MAX,
            // TALL-DEGENERATE, NON-CHAIN (Build 2). The same argument as the wide
            // arm, one shape over: a tall_lu warm dual (qiu: 1,192 rows,
            // capacity==demand network, 83–88% degenerate θ≈0) is CONVERGING even
            // as it transiently blooms a few hundred violated rows, and `max(64)`
            // aborts it at pivot ~127 into a full cold primal re-crash (measured:
            // 495/595 warm-dual fails were bloom aborts, 383K wasted primal iters).
            // Lifting the cap for tall_lu lets the walk finish warm (qiu
            // bloom-aborts 495→0, primal iters 383K→54K, nodes +110% @60s).
            //
            // BUT NOT THE CHAIN CLASS. The divergence guard was BUILT for the
            // layered-affine-chain / badly-scaled NN matrices (see the doc above),
            // where the warm dual genuinely THRASHES rather than converges. The
            // ACAS diff-leaf certification tree (k124: m=1608, `chain=true`,
            // big-M ~3.7e4) is exactly that class and clears tall_lu too — and
            // measured, lifting its cap is a REGRESSION: the warm dual thrashes
            // (dual iters 3.5→104 per solve), and k124 goes from CERTIFIED unsat
            // in 51,277 nodes to timing out at "unknown" (23,989 nodes / 400s).
            // qiu is `chain=false`, k124 `chain=true`, so `!chain_class()` keeps
            // the relax on qiu's converging bloom while the chain class keeps the
            // guard and stays certified. (k124's cold walks are healthy so it sits
            // at armed state 3, never distress state 1 — `chain_class`, not
            // `chain_lp`, is the predicate that catches it.) Verdict-neutral on
            // BOTH (only the walk length /
            // speed changes; the chain exclusion is about not LOSING a proof to a
            // slowdown, not about soundness — every exit is post-checked either way).
            None if lp.tall_lu()
                && lp.bloom_relax_class()
                && !no_bloom_relax()
                && caller_tag() != CALLER_FLIP_LNS =>
            {
                usize::MAX
            }
            None => (4 * entry_viol).max(64),
        };

        // Per-iteration scratch lives on `self` (alpha/nz, rho, arow —
        // the pivot ROW, one entry per column — plus the bound-flip ratio-test
        // trio bp/flips/wflip and the DSE solve tau): a fresh allocation per
        // call was measurable at ~70k calls per proof, and every buffer is
        // either zeroed here or fully overwritten before use, so the floats
        // are untouched.
        // DUAL STEEPEST-EDGE weights (Forrest–Goldfarb), one per basic slot. Picking the
        // leaving row by raw violation is Dantzig pricing in dual clothing, and on this
        // family it walked a steady ~23 pivots per one-bound-change child (measured, with
        // budget-burns at only 0.4% — the WALK was long, not the failures). Weighting each
        // violation by its row's steepest-edge norm is the standard 2-4x on degenerate
        // LPs; the update needs τ = B⁻¹ρ, one extra small solve per pivot.
        if self.dse.len() != self.m {
            self.dse = vec![1.0f64; self.m];
        }

        // Reduced costs, computed ONCE and then maintained.
        //
        // They were being rebuilt from scratch every iteration — a BTRAN of `c_B` plus a
        // dot product per column — and that was most of the cost of a node. It is
        // unnecessary: a dual pivot moves the duals by `θ·rho`, so every reduced cost
        // moves by `−θ·alpha_j`, and `alpha_j` is the pivot row we are ALREADY computing
        // to run the ratio test. The update is free; the recomputation was not.
        if !self.y_is_duals {
            for i in 0..self.m {
                self.cb[i] = self.pcost[self.basis[i]];
            }
            self.y.copy_from_slice(&self.cb);
            self.btran();
        }
        self.y_is_duals = false; // the loop scribbles rho over `y` and pivots
                                 // Reduced costs for EVERY column via one row-major sweep (`fill_yta`
                                 // reproduces the per-column gather's bits — see its doc). Basic slots
                                 // get their (near-zero) reduced cost instead of the old literal 0.0;
                                 // nothing reads a basic slot (the ratio test and `theta` skip basics,
                                 // and a leaver is overwritten with `-theta` on its way out).
        self.fill_yta(lp);
        for j in 0..lp.n {
            self.d[j] = self.pcost[j] - self.arow[j];
        }
        for r in 0..self.m {
            self.d[lp.n + r] = self.pcost[lp.n + r] + self.y[r];
        }

        // ENTRY BOUND-FLIP REPAIR (only on an LP whose matrix has been REWRITTEN in
        // place — the fixed-slot cut engine; every other model skips this block and
        // keeps its walk bit-for-bit). A warm basis stored before a slot rewrite was
        // dual-feasible against the OLD matrix; against the new one its nonbasic
        // reduced costs can point the wrong way, and this walk HOLDS dual feasibility
        // rather than restoring it — it would carry the violation to the exit, fail
        // the post-check, and burn the whole walk plus a primal re-solve (measured on
        // rout: 17–20% of node solves, the single largest per-node cost with cuts
        // live). A box-bounded nonbasic column is repaired for free by resting on its
        // OTHER bound — the textbook bounded-dual initialization; reduced costs do not
        // depend on which bound a nonbasic column rests at, so `d` stays valid and
        // only `xb` must be rebuilt. A column with no finite opposite bound stays
        // violated, and the post-check keeps guarding the exit as before.
        if lp.cut_slots_live.get() {
            let mut flips = 0usize;
            for j in 0..self.cols {
                if self.basic_row[j].is_some() || self.lo[j] == self.up[j] {
                    continue;
                }
                match self.at[j] {
                    NbBound::Lower if self.d[j] < -cost_tol_band && self.up[j].is_finite() => {
                        self.at[j] = NbBound::Upper;
                        flips += 1;
                    }
                    NbBound::Upper if self.d[j] > cost_tol_band && self.lo[j].is_finite() => {
                        self.at[j] = NbBound::Lower;
                        flips += 1;
                    }
                    _ => {}
                }
            }
            if flips > 0 {
                self.recompute_xb(lp);
            }
        }

        // DUAL COST PERTURBATION (anti-degeneracy; see `dual_perturb_mag`). On the
        // qiu class ONLY, break the ratio-test ties that generate θ≈0 pivots: nudge
        // every entry-NONBASIC column's cost a hair INTO dual feasibility, so no
        // reduced cost sits exactly at 0 and the minimum ratio is strictly positive.
        // Basic costs are untouched, so `y` (hence `d` for basic slots) is unchanged
        // and each nonbasic `d_j` shifts by exactly its own δ_j — the warm start
        // stays dual-feasible for the perturbed costs c' = c + δ. Applied AFTER the
        // entry bound-flip repair so the orientation reads the FINAL resting bound;
        // `pcost` AND `d` are stepped together so the refactor-refresh (which rebuilds
        // `d` from `pcost`) stays consistent. The wrapper (`dual_simplex`) restores
        // the true costs bit-for-bit on exit.
        if self.should_perturb_dual(lp) {
            let mag = dual_perturb_mag();
            self.pcost_save.clear();
            self.pcost_save.extend_from_slice(&self.pcost);
            self.dual_perturb_active = true;
            for j in 0..self.cols {
                // Nonbasic, non-fixed columns only: a fixed column has nowhere to go,
                // and a basic column would perturb `y` and break the clean per-column
                // reduced-cost shift the dual-feasible-start argument relies on.
                if self.basic_row[j].is_some() || self.lo[j] == self.up[j] {
                    continue;
                }
                let dir = match self.at[j] {
                    NbBound::Lower => 1.0,     // d_j ≥ 0 required: nudge cost UP
                    NbBound::Upper => -1.0,    // d_j ≤ 0 required: nudge cost DOWN
                    NbBound::Zero => continue, // free at 0: any nudge is infeasible
                };
                // Hashed unit in [0.5, 1.5) so no two columns move by the same amount
                // (deterministic — a re-solved node must move identically).
                let h = (j as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15);
                let u = 0.5 + ((h >> 40) as f64) / f64::from(1u32 << 24);
                let delta = dir * mag * lp.vmul(j) * u;
                self.pcost[j] += delta;
                self.d[j] += delta;
            }
        }

        // OBJECTIVE-CUTOFF EARLY STOP. The dual simplex holds a dual-feasible basis
        // at every iteration boundary, so its objective `z = c·x` is a LOWER bound on
        // this node's LP min, and — as the walk drives the primal feasible — it rises
        // MONOTONICALLY toward that min (verified: it never dips). Once `z` reaches the
        // caller's cutoff (the incumbent, minimize form) the node's LP min is provably
        // >= the incumbent, i.e. the node is prunable, and there is nothing to learn by
        // walking the primal the rest of the way to a vertex. Stop, and hand the caller
        // the dual-feasible basis whose duals certify the bound (`safe_bound` is
        // rigorous for ANY duals, so the prune it enables is re-derived exactly). The
        // check sits at the TOP of the loop, on a fully-committed basis, so the stop is
        // transactional. Off under `AY_MILP_NO_CUTOFF`.
        let cutoff_on = self.cutoff.is_finite() && !no_cutoff();
        if anat {
            self.anat_z0 = self.dual_anat_z(lp);
        }
        // Seed the dual ratio-test eligibility bitmask from the fully-settled entry
        // basis (all warm-start/crash/cold-dual/primal/entry-flip/perturbation
        // mutations are behind us). The pivot loop maintains it incrementally at the
        // flip and pivot commits, so this is the ONLY full recompute per dual entry.
        let rt_kind_on = rt_kind_enabled();
        let rt_kind_verify = rt_kind_verify_enabled();
        // Maintain the bitmask whenever it is read (ON) or checked (VERIFY); when
        // both are off the incremental writes are skipped so the kill-switch path
        // is a true byte-for-byte baseline.
        let rt_kind_maint = rt_kind_on || rt_kind_verify;
        if rt_kind_maint {
            self.rebuild_rt_kind();
        }
        for iter in 0..budget {
            // No pivot iteration may run once the factor has declined (fill over
            // budget). Returning `false` = "did not settle"; the sticky `oom`
            // flag carries the real verdict up to `run`, which maps it to
            // `OutOfMemory`. (Dead branch on every shipping instance.)
            if self.oom {
                return false;
            }
            DUAL_ITERS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            if !spend_iter() {
                DUAL_SPEND.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                if anat {
                    self.dual_anat_commit(lp, 2, iter);
                }
                return false; // out of WORK, not out of time
            }
            stats::bump(&stats::DUAL_ITERS);
            stats::bump_solve();
            // Divergence guard (see `bloom_cap` above): a thrashing walk is
            // abandoned to the rollback in ~hundreds of pivots, not thousands.
            if iter % 128 == 127 {
                let mut c = 0usize;
                for i in 0..self.m {
                    let b = self.basis[i];
                    let ft = feas_tol * lp.bmul(b);
                    let v = self.xb[i];
                    if v < self.lo[b] - ft || v > self.up[b] + ft {
                        c += 1;
                    }
                }
                if c > bloom_cap {
                    DUAL_BLOOM.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    DUAL_BLOOM_IT.fetch_add(iter as u64, std::sync::atomic::Ordering::Relaxed);
                    if anat {
                        self.dual_anat_commit(lp, 2, iter);
                    }
                    return false;
                }
            }
            if cutoff_on {
                // `z = c·x` at the current dual-feasible basis (basics carried in
                // `xb`, nonbasics resting on a bound) — a lower bound on the node LP
                // min. Cheap next to the pivot's BTRAN/FTRAN, and only armed nodes pay.
                let mut z = 0.0f64;
                for i in 0..self.m {
                    // `pcost·xb` is frame-invariant (c'ᵀx' = cᵀx); `lp.cost`
                    // against scaled values would mix frames and misprice the
                    // cutoff under equilibration.
                    z += self.pcost[self.basis[i]] * self.xb[i];
                }
                // Nonbasics through the objective's SUPPORT (`nzcost`), not a
                // full column scan: a zero-cost nonbasic adds exactly `0.0`
                // (finite value) or is skipped by the `is_finite` guard
                // (infinite bound) — either way `z` is bit-identical, and the
                // scan is O(support) instead of O(cols). This check runs every
                // dual iteration; on an objective like pk1's (one column) the
                // old scan was most of the iteration's constant cost.
                for &ju in &self.nzcost {
                    let j = ju as usize;
                    if self.basic_row[j].is_none() {
                        let x = self.nb_value(lp, j);
                        if x.is_finite() {
                            z += self.pcost[j] * x;
                        }
                    }
                }
                if z >= self.cutoff {
                    self.hit_cutoff = true;
                    if anat {
                        self.dual_anat_commit(lp, 2, iter);
                    }
                    return false;
                }
            }
            if iter % 500 == 0 && lp_stats_enabled() {
                let (mut nviol, mut sviol) = (0usize, 0.0f64);
                for i in 0..self.m {
                    let b = self.basis[i];
                    let v = self.xb[i];
                    let ft = feas_tol * lp.bmul(b);
                    if v < self.lo[b] - ft {
                        nviol += 1;
                        sviol += (self.lo[b] - v) * lp.vmul(b);
                    } else if v > self.up[b] + ft {
                        nviol += 1;
                        sviol += (v - self.up[b]) * lp.vmul(b);
                    }
                }
                eprintln!("DUALSTAT iter={iter} violrows={nviol} viol={sviol:.3}");
            }
            if iter % 64 == 0 {
                if let Some(d) = deadline {
                    if std::time::Instant::now() >= d {
                        DUAL_DEADLINE.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        if anat {
                            self.dual_anat_commit(lp, 2, iter);
                        }
                        return false;
                    }
                }
            }
            if self.since_refactor >= self.refactor_cadence(lp) {
                refac_reason(1);
                self.refactorize(lp);
                if self.oom {
                    return false;
                }
                self.recompute_xb(lp);
                // AND REFRESH THE REDUCED COSTS, for exactly the reason the basic values are
                // refreshed: they have been carried forward by an incremental update
                // (`d[j] -= theta * arow[j]`) since the solve began, and that update drifts.
                //
                // Leaving them stale makes the LP's ANSWER depend on the refactorisation cadence,
                // which is how this was found: blend2's root bound came back 214.352831 at every-50,
                // 214.360463 at every-100 and 211.476117 at every-200 -- three different "Optimal"
                // verdicts for one LP, because the entering choice, the ratio test and the
                // optimality test at the bottom of this loop all read `d`. A drifted `d` reports a
                // basis optimal that is not, and the root bound it stops at is simply weaker. At
                // every-100 blend2 stopped proving at all.
                //
                // REBUILD THE DUAL VECTOR FIRST. `reduced_cost` does not compute `y`, it READS
                // `self.y` -- and in this loop `self.y` is the scratch space the pivot row's BTRAN
                // writes into, so by here it holds `rho`, not `c_B B^-1`. Refreshing `d` against it
                // recomputes every reduced cost from the wrong vector, which is worse than the drift
                // it set out to fix: it cost rout its incumbent outright, three runs from three.
                for i in 0..self.m {
                    self.y[i] = self.pcost[self.basis[i]];
                }
                self.btran();
                // Same row-major rebuild as the loop-entry one above (and the
                // same "basic slots are never read" contract).
                self.fill_yta(lp);
                for j in 0..lp.n {
                    self.d[j] = self.pcost[j] - self.arow[j];
                }
                for r in 0..self.m {
                    self.d[lp.n + r] = self.pcost[lp.n + r] + self.y[r];
                }
            }
            let bland = stall > bland_after;

            // Leaving: a primal-infeasible basic — steepest-edge-scored. Under
            // Bland the smallest index, because arbitrary choices are what cycle.
            // (`worst` is a SCORE, not a violation: eligibility is the `continue`
            // above it, so zero is the right floor — any violated row must win
            // over "none".)
            // PXPROFILE: leaving-variable scan (untimed by RT/UPD profilers).
            let px_leave_t0 = if rt_profile {
                Some(std::time::Instant::now())
            } else {
                None
            };
            let mut leave: Option<(usize, bool)> = None;
            let mut worst = 0.0f64;
            // Unchecked: `i < m` bounds every per-row array, and `basis[i] <
            // cols` bounds `lo`/`up` (a basis invariant), debug-asserted.
            for i in 0..self.m {
                debug_assert!(i < self.basis.len() && self.basis[i] < self.lo.len());
                // SAFETY: `i < m` bounds the row arrays `basis` and `xb`.
                let (b, v) = unsafe { (*self.basis.get_unchecked(i), *self.xb.get_unchecked(i)) };
                // SAFETY: The basis invariant keeps `b` within the aligned
                // column-bound arrays `lo` and `up`, as asserted above.
                let (lo_b, up_b) =
                    unsafe { (*self.lo.get_unchecked(b), *self.up.get_unchecked(b)) };
                let ft = feas_tol * lp.bmul(b);
                let (viol, below) = if v < lo_b - ft {
                    (lo_b - v, true)
                } else if v > up_b + ft {
                    (v - up_b, false)
                } else {
                    continue;
                };
                if bland {
                    if leave.is_none_or(|(pi, _)| self.basis[i] < self.basis[pi]) {
                        leave = Some((i, below));
                    }
                } else {
                    // Steepest-edge score: violation normalised by the row's norm.
                    // SAFETY: `i < m`, and `dse` has one entry per row.
                    let score = viol * viol / unsafe { *self.dse.get_unchecked(i) };
                    if score > worst {
                        worst = score;
                        leave = Some((i, below));
                    }
                }
            }
            if let Some(t) = px_leave_t0 {
                PX_LEAVE_NANOS.fetch_add(
                    t.elapsed().as_nanos() as u64,
                    std::sync::atomic::Ordering::Relaxed,
                );
            }
            let Some((row, below)) = leave else {
                // Primal feasible, and dual feasibility never left -- so this is the optimum, and
                // its objective is the NODE'S BOUND. Ask again on a basis that is not drifting, for
                // the same reason the primal loop does: `xb` is carried by an incremental update
                // between refactorisations, and the test just above compares it against `feas_tol`.
                // A drifted `xb` ends the solve early, and an early dual simplex stops at a WEAKER
                // bound -- which is sound, and is a prune that never happens.
                // (Trigger is engine-aware — see `verify_after_for` / Lever A1.)
                if self.since_refactor >= self.verify_after_for(lp) {
                    refac_reason(2);
                    self.refactorize(lp);
                    if self.oom {
                        return false;
                    }
                    self.recompute_xb(lp);
                    continue;
                }
                if anat {
                    self.dual_anat_commit(lp, 1, iter);
                }
                return true;
            };

            // rho = e_row · B^{-1}, so alpha_j = rho · M_j is the pivot ROW.
            // PXPROFILE: unit-vector BTRAN (untimed by RT/UPD profilers).
            let px_btran_t0 = if rt_profile {
                Some(std::time::Instant::now())
            } else {
                None
            };
            self.y.fill(0.0);
            self.y[row] = 1.0;
            if let Some(cache) = self.lu.as_mut() {
                // Unit-vector BTRAN: the reachability-sparse solve touches tens
                // of stages on a sparse basis where the dense chain walks all m.
                self.ynz.clear();
                self.ynz.push(row);
                cache.eng.btran_nz(&mut self.y, &mut self.ynz);
            } else {
                self.btran();
            }
            self.rho.copy_from_slice(&self.y);
            if let Some(t) = px_btran_t0 {
                PX_BTRAN_NANOS.fetch_add(
                    t.elapsed().as_nanos() as u64,
                    std::sync::atomic::Ordering::Relaxed,
                );
            }

            // PXPROFILE: pivot-row gather arow = ρᵀA (untimed by RT/UPD profilers).
            let px_arow_t0 = if rt_profile {
                Some(std::time::Instant::now())
            } else {
                None
            };

            // `xb[row] = -Σ_j alpha_j x_j`: raising `x_j` moves it by `-alpha_j`. A
            // column at its LOWER bound may only rise, one at its UPPER only fall, so
            // eligibility is exactly "moves the violated basic the right way".
            // The pivot row, ROW-WISE: `alpha = Σ_r rho[r] · A[r, ·]`. One sequential pass
            // over the rows `rho` actually touches, instead of a scattered gather of `rho`
            // once per column.
            self.arow.fill(0.0);
            // Unchecked under the CSR invariants (`row_idx` entries `< n`,
            // `row_ptr` monotone within bounds), asserted in debug builds.
            debug_assert!(self.arow.len() == self.cols && self.rho.len() == self.m);
            if !lp.p_dense_rows().is_empty() {
                // Dense mirror: a straight AXPY per touched row — no index
                // loads, and the compiler vectorises it. Value-identical to
                // the CSR scatter below (see `dense_rows`). `chunks_exact`
                // (not `r*n..` slicing) so the row walk carries no per-row
                // multiply/overflow checks.
                let n = lp.n;
                for (r, dr) in lp.p_dense_rows().chunks_exact(n).enumerate() {
                    let y_r = self.rho[r];
                    if y_r == 0.0 {
                        continue;
                    }
                    for (aj, &v) in self.arow[..n].iter_mut().zip(dr) {
                        *aj += y_r * v;
                    }
                    self.arow[n + r] = -y_r; // the logical column is -e_r
                }
            } else {
                // SAFETY: CSR ranges bound the aligned index/value arrays;
                // `r < m` bounds `rho` and `n + r`, while every index is < `n`.
                unsafe {
                    let ri = lp.row_idx.as_ptr();
                    let rv = lp.p_row_val().as_ptr();
                    let ap = self.arow.as_mut_ptr();
                    for r in 0..self.m {
                        let y_r = *self.rho.get_unchecked(r);
                        if y_r == 0.0 {
                            continue;
                        }
                        let (s, e) = (lp.row_ptr[r], lp.row_ptr[r + 1]);
                        debug_assert!(e <= lp.row_idx.len() && s <= e);
                        for q in s..e {
                            let j = *ri.add(q) as usize;
                            debug_assert!(j < self.arow.len());
                            *ap.add(j) += y_r * *rv.add(q);
                        }
                        *ap.add(lp.n + r) = -y_r; // the logical column is -e_r
                    }
                }
            }
            if let Some(t) = px_arow_t0 {
                PX_AROW_NANOS.fetch_add(
                    t.elapsed().as_nanos() as u64,
                    std::sync::atomic::Ordering::Relaxed,
                );
            }

            // THE BOUND-FLIP (long-step) RATIO TEST. The short-step test pivots at the
            // FIRST breakpoint — the smallest |d_j/alpha_j| — and on an all-binary model
            // that is the whole reason children cost ~24 iterations while Gurobi's log
            // shows ~7: most breakpoints belong to BOXED columns, and a boxed column
            // need not enter at all. Push the dual step PAST its breakpoint and the
            // column simply flips to its other bound; the dual objective's slope along
            // the step starts at the leaving row's infeasibility and shrinks by
            // |alpha_j|·span_j per flipped column, so the walk stays an improvement
            // until the slope would turn — and THAT breakpoint's column enters. One
            // basis change retires a whole run of breakpoints. Flipped columns keep
            // their reduced costs (flips move no duals); the theta roll below crosses
            // every passed breakpoint's zero, which is exactly what re-legalises their
            // sign at the OPPOSITE bound.
            //
            // Under Bland the walk is off — arbitrary long steps are what cycle.
            //
            // MEASURED ON THE DENSE-BINARY LADDER: ~1% fewer iterations, wall flat.
            // The physics is against long walks HERE: a child's violation is a
            // fraction of a unit while one flip's slope drop is |alpha|·span ≈ 5-10
            // under the 4-16x row scaling, so the walk usually enters at the first
            // breakpoint — the family's 23.5 it/call live in warm-basis distance
            // across best-bound pops, not in the ratio test. The long step is kept
            // because it is the textbook test and it pays exactly where violations
            // dwarf single spans: warm starts after reduced-cost fixing bursts,
            // ranged rows, general integers.
            self.bp.clear();
            self.flips.clear();
            let mut enter: Option<usize> = None;
            if rt_profile {
                RT_PIVOTS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            }

            // STAGE B — DEFERRED SINGLE PASS (non-churn-band shapes only). The warm
            // no-flip step is the bulk of the tree: the minimum-ratio breakpoint
            // absorbs the whole slope, no bound flips — and because `dual_churn_band`
            // is false here, no Harris band scan needs `self.bp` either. So make ONE
            // pass that tracks only the argmin and its span/drop; if the walk stops
            // there, enter it directly and NEVER materialise the ~O(cols) breakpoint
            // Vec. A genuine long step falls through to the general build below (a
            // re-scan fills `self.bp`) — rare on warm re-solves. The entering column
            // is the SAME the two-pass path would pick (min-ratio, no band), so the
            // pivot stream — and every exact verdict — is byte-identical.
            let mut deferred_done = false;
            if defer_ok && !bland {
                let t0 = if rt_profile {
                    Some(std::time::Instant::now())
                } else {
                    None
                };
                let mut argmin_j = usize::MAX;
                let mut rmin = f64::INFINITY;
                {
                    let cols = self.cols;
                    let arow = &self.arow[..cols];
                    let at = &self.at[..cols];
                    let d = &self.d[..cols];
                    let basic_row = &self.basic_row[..cols];
                    for j in 0..cols {
                        let a = arow[j];
                        if a.abs() <= pivot_tol {
                            continue;
                        }
                        if basic_row[j].is_some() {
                            continue;
                        }
                        let eligible = match (at[j], below) {
                            (NbBound::Lower, true) => a < 0.0,
                            (NbBound::Lower, false) => a > 0.0,
                            (NbBound::Upper, true) => a > 0.0,
                            (NbBound::Upper, false) => a < 0.0,
                            (NbBound::Zero, _) => false,
                        };
                        if !eligible {
                            continue;
                        }
                        let ratio = (d[j] / a).abs();
                        if ratio < rmin {
                            rmin = ratio;
                            argmin_j = j;
                        }
                    }
                }
                if let Some(t) = t0 {
                    RT_BUILD_NANOS.fetch_add(
                        t.elapsed().as_nanos() as u64,
                        std::sync::atomic::Ordering::Relaxed,
                    );
                }
                let t1 = if rt_profile {
                    Some(std::time::Instant::now())
                } else {
                    None
                };
                if argmin_j == usize::MAX {
                    // No breakpoints — the general path's empty walk yields noenter;
                    // reproduce it (enter stays None) without building `self.bp`.
                    deferred_done = true;
                } else {
                    let b_leave = self.basis[row];
                    let slope = if below {
                        self.lo[b_leave] - self.xb[row]
                    } else {
                        self.xb[row] - self.up[b_leave]
                    };
                    let span = self.up[argmin_j] - self.lo[argmin_j];
                    let drop = self.arow[argmin_j].abs() * span;
                    let ft_leave = feas_tol * lp.bmul(b_leave);
                    if !(span.is_finite() && span > 0.0) || slope - drop <= ft_leave {
                        // Stops at the argmin, no flips, no band (non-churn-band).
                        enter = Some(argmin_j);
                        deferred_done = true;
                        RT_DEFERRED.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    }
                    // else: genuine long step — fall through to build `self.bp`.
                }
                if let Some(t) = t1 {
                    RT_SELECT_NANOS.fetch_add(
                        t.elapsed().as_nanos() as u64,
                        std::sync::atomic::Ordering::Relaxed,
                    );
                }
            }

            if !deferred_done {
                let t_build = if rt_profile {
                    Some(std::time::Instant::now())
                } else {
                    None
                };
                // STAGE A — FUSED BUILD. Materialise the breakpoints AND track the
                // minimum-ratio one inline (`kmin`/`rmin_track`) in the SAME pass, so the
                // separate O(bp) min-scan below is dropped. First-minimal wins on a tie
                // (strict `<`), exactly as the old scan (`sort_unstable`-agnostic), so
                // `kmin` — and the entering column — is identical: byte-identical stream.
                let mut kmin = 0usize;
                let mut rmin_track = f64::INFINITY;
                if rt_kind_verify {
                    // Ground-truth check: the incrementally-maintained bitmask must
                    // equal a from-scratch recompute at every scan. O(cols)/pivot,
                    // testing only — proves the flip/pivot commit updates never drift.
                    let cols = self.cols;
                    for j in 0..cols {
                        let want = if self.basic_row[j].is_some() {
                            0u8
                        } else {
                            match self.at[j] {
                                NbBound::Zero => 0,
                                NbBound::Lower => 1,
                                NbBound::Upper => 2,
                            }
                        };
                        assert_eq!(
                            self.rt_kind[j], want,
                            "rt_kind drift at col {j} (dual iter {iter})"
                        );
                    }
                }
                if rt_masked && !bland {
                    // MASKED / BRANCHLESS BUILD (A/B experiment). Pass 1 divides
                    // over ALL columns branch-free (vectorisable); pass 2 applies
                    // the SAME filters and pushes the precomputed ratio. Eligible
                    // columns divide identically (same IEEE op), so `self.bp` and
                    // `kmin` are byte-identical to the fused single pass.
                    let cols = self.cols;
                    self.rt_ratio.clear();
                    self.rt_ratio.resize(cols, 0.0);
                    {
                        let arow = &self.arow[..cols];
                        let d = &self.d[..cols];
                        let ratio = &mut self.rt_ratio[..cols];
                        for j in 0..cols {
                            ratio[j] = (d[j] / arow[j]).abs();
                        }
                    }
                    let arow = &self.arow[..cols];
                    let at = &self.at[..cols];
                    let basic_row = &self.basic_row[..cols];
                    let rt_ratio = &self.rt_ratio[..cols];
                    for j in 0..cols {
                        let a = arow[j];
                        if a.abs() <= pivot_tol {
                            continue;
                        }
                        if basic_row[j].is_some() {
                            continue;
                        }
                        let eligible = match (at[j], below) {
                            (NbBound::Lower, true) => a < 0.0,
                            (NbBound::Lower, false) => a > 0.0,
                            (NbBound::Upper, true) => a > 0.0,
                            (NbBound::Upper, false) => a < 0.0,
                            (NbBound::Zero, _) => false,
                        };
                        if !eligible {
                            continue;
                        }
                        let ratio = rt_ratio[j];
                        if fused_rt && ratio < rmin_track {
                            kmin = self.bp.len();
                            rmin_track = ratio;
                        }
                        self.bp.push((ratio, j as u32));
                    }
                } else if rt_kind_on && !bland {
                    // INCREMENTAL BITMASK BUILD (default). The basis-stable part of
                    // the eligibility test — `basic_row[j].is_none() && at[j] != Zero`
                    // and which bound the nonbasic column rests at — is pre-folded into
                    // `rt_kind[j]` (`0` ineligible, `1` lower, `2` upper) and maintained
                    // on basis change, so this pivot-hot scan reads ONE `u8` in place of
                    // the 16-byte `basic_row` `Option` load + the `at` load + the 5-arm
                    // match. The surviving per-column work — the `arow` magnitude gate,
                    // the sign test, the `(d[j]/arow[j]).abs()` breakpoint, and the
                    // first-minimal `kmin` fold — is BIT-IDENTICAL to the 4-stream build
                    // below (same push set, same ascending-`j` order, same argmin), so
                    // the pivot stream and every exact verdict are unchanged.
                    let cols = self.cols;
                    let arow = &self.arow[..cols];
                    let d = &self.d[..cols];
                    let rt_kind = &self.rt_kind[..cols];
                    for j in 0..cols {
                        let kind = rt_kind[j];
                        if kind == 0 {
                            continue;
                        }
                        let a = arow[j];
                        if a.abs() <= pivot_tol {
                            continue;
                        }
                        // kind==1 (lower): eligible iff (below ? a<0 : a>0);
                        // kind==2 (upper): eligible iff (below ? a>0 : a<0).
                        let eligible = if kind == 1 {
                            if below {
                                a < 0.0
                            } else {
                                a > 0.0
                            }
                        } else if below {
                            a > 0.0
                        } else {
                            a < 0.0
                        };
                        if !eligible {
                            continue;
                        }
                        let ratio = (d[j] / a).abs();
                        if fused_rt && ratio < rmin_track {
                            kmin = self.bp.len();
                            rmin_track = ratio;
                        }
                        self.bp.push((ratio, j as u32));
                    }
                } else {
                    // Length-pinned reborrows so `j < cols` elides every bounds check.
                    let cols = self.cols;
                    let arow = &self.arow[..cols];
                    let at = &self.at[..cols];
                    let d = &self.d[..cols];
                    let basic_row = &self.basic_row[..cols];
                    for j in 0..cols {
                        // Magnitude test FIRST: one sequential f64 load rejects
                        // most columns (exact zeros and basics' float noise)
                        // before the 16-byte `Option` load — same tests, same
                        // outcome, cheaper order. (A basic column CAN carry a
                        // large `arow` entry — the leaver's own is exactly 1 —
                        // so the basic test still runs for survivors.)
                        let a = arow[j];
                        if a.abs() <= pivot_tol {
                            continue;
                        }
                        if basic_row[j].is_some() {
                            continue;
                        }
                        let eligible = match (at[j], below) {
                            (NbBound::Lower, true) => a < 0.0,
                            (NbBound::Lower, false) => a > 0.0,
                            (NbBound::Upper, true) => a > 0.0,
                            (NbBound::Upper, false) => a < 0.0,
                            (NbBound::Zero, _) => false,
                        };
                        if !eligible {
                            continue;
                        }
                        // How far the dual may step before THIS reduced cost flips sign.
                        let ratio = (d[j] / a).abs();
                        if bland {
                            enter = Some(j);
                            break;
                        }
                        // Stage A: fold the min-scan in. `bp.len()` is this entry's index.
                        if fused_rt && ratio < rmin_track {
                            kmin = self.bp.len();
                            rmin_track = ratio;
                        }
                        self.bp.push((ratio, j as u32));
                    }
                }
                if let Some(t) = t_build {
                    RT_BUILD_NANOS.fetch_add(
                        t.elapsed().as_nanos() as u64,
                        std::sync::atomic::Ordering::Relaxed,
                    );
                }
                let t_select = if rt_profile {
                    Some(std::time::Instant::now())
                } else {
                    None
                };
                if !bland {
                    let b_leave = self.basis[row];
                    // The violation magnitude IS the slope of the dual objective in this step.
                    let mut slope = if below {
                        self.lo[b_leave] - self.xb[row]
                    } else {
                        self.xb[row] - self.up[b_leave]
                    };
                    // FAST PATH — THE WALK USUALLY STOPS AT THE FIRST BREAKPOINT. A warm node
                    // re-solve's violation (the slope) is small, so the very first (minimum-ratio)
                    // breakpoint absorbs it and no bound flips happen — and then the full
                    // ascending sort below is pure waste, paid ~1.2M times per rout tree
                    // (measured: ~17% of all simplex samples inside the sort). Find the minimum
                    // in O(n); only when the walk genuinely continues past it does the slow path
                    // sort and walk exactly as before. Tie behavior is unchanged in substance:
                    // `sort_unstable` leaves equal-ratio order unspecified, so the min-scan's
                    // first-minimal pick is just as deterministic.
                    // Stage A folds this min-scan into the build loop above; the baseline
                    // (flag off) keeps the separate scan so it is the true A/B reference.
                    // Both compute the first-minimal argmin — byte-identical `kmin`.
                    let kmin = if fused_rt {
                        kmin
                    } else {
                        let mut kmin = 0usize;
                        for (k, &(r, _)) in self.bp.iter().enumerate().skip(1) {
                            if r < self.bp[kmin].0 {
                                kmin = k;
                            }
                        }
                        kmin
                    };
                    let fast_enter = if self.bp.is_empty() {
                        None // no breakpoints: the slow path's empty walk yields noenter, as before
                    } else {
                        let (rmin, ju) = self.bp[kmin];
                        let j = ju as usize;
                        let span = self.up[j] - self.lo[j];
                        let drop = self.arow[j].abs() * span;
                        let ft_leave = feas_tol * lp.bmul(b_leave);
                        if !(span.is_finite() && span > 0.0) || slope - drop <= ft_leave {
                            // Stops immediately: no flips. The Harris band scan (anti-churn:
                            // wide-tall set-partitioning + tall degenerate networks, see
                            // `dual_churn_band`) needs no order — it takes the max pivot
                            // magnitude within the band.
                            let mut best_j = j;
                            if lp.dual_churn_band() {
                                let band = churn_band_factor() * cost_tol_band * lp.vmul(b_leave);
                                let mut best_mag = self.arow[best_j].abs();
                                for &(r, ju2) in &self.bp {
                                    if r <= rmin + band {
                                        let j2 = ju2 as usize;
                                        let mag = self.arow[j2].abs();
                                        if mag > best_mag {
                                            best_mag = mag;
                                            best_j = j2;
                                        }
                                    }
                                }
                            }
                            Some(best_j)
                        } else {
                            None
                        }
                    };
                    if let Some(j) = fast_enter {
                        enter = Some(j);
                    } else {
                        if rt_profile {
                            SEL_SLOW.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                            SEL_BP_LEN_SUM.fetch_add(
                                self.bp.len() as u64,
                                std::sync::atomic::Ordering::Relaxed,
                            );
                        }
                        let ts = if rt_profile {
                            Some(std::time::Instant::now())
                        } else {
                            None
                        };
                        if rt_bits_key {
                            // BYTE-IDENTICAL: for the non-negative finite ratios in
                            // `bp`, `to_bits()` u64 order == `total_cmp` (see
                            // `rt_bits_key_enabled`), so pdqsort emits the same
                            // permutation, ties included, for a cheaper comparator.
                            self.bp.sort_unstable_by_key(|&(r, _)| r.to_bits());
                        } else {
                            self.bp.sort_unstable_by(|x, y| x.0.total_cmp(&y.0));
                        }
                        if let Some(t) = ts {
                            SEL_SORT_NANOS.fetch_add(
                                t.elapsed().as_nanos() as u64,
                                std::sync::atomic::Ordering::Relaxed,
                            );
                        }
                        let tw = if rt_profile {
                            Some(std::time::Instant::now())
                        } else {
                            None
                        };
                        let mut stop: Option<usize> = None;
                        // `slope` lives in the LEAVING column's scaled units.
                        let ft_leave = feas_tol * lp.bmul(b_leave);
                        for (k, &(_, ju)) in self.bp.iter().enumerate() {
                            let j = ju as usize;
                            let span = self.up[j] - self.lo[j];
                            let drop = self.arow[j].abs() * span;
                            // A column without both bounds finite cannot flip; a flip that
                            // would spend the whole slope means the walk stops here either
                            // way. In both cases this breakpoint's column enters.
                            if !(span.is_finite() && span > 0.0) || slope - drop <= ft_leave {
                                stop = Some(k);
                                break;
                            }
                            self.flips.push(ju);
                            slope -= drop;
                        }
                        if let Some(t) = tw {
                            SEL_WALK_NANOS.fetch_add(
                                t.elapsed().as_nanos() as u64,
                                std::sync::atomic::Ordering::Relaxed,
                            );
                        }
                        let tb = if rt_profile {
                            Some(std::time::Instant::now())
                        } else {
                            None
                        };
                        // HARRIS-STYLE PIVOT SELECTION IN A TOLERANCE BAND. Entering at
                        // exactly the stopping breakpoint takes whatever pivot magnitude
                        // that column happens to carry, and a SMALL pivot is churn: the
                        // primal step is `(xb - target) / piv`, and every other basic in
                        // the entering column's support moves by `alpha_i · step` — so a
                        // pivot 10x smaller kicks 10x more activity onto rows that were
                        // inside their bounds, and the walk pays it back a violation at a
                        // time. Measured on air05's cold dual start (426 rows): on the
                        // eta engine, 10,333 pivots strictly-at-stop vs 9,886 with the
                        // band — a real but second-order trim (the first-order fix was
                        // the LU engine's accuracy; see `try_cold_dual`). The passed-over
                        // breakpoints' reduced costs end the step wrong-signed by at most
                        // `band · |a_j|`, i.e. inside the dual tolerance that `priced_out`
                        // (and the polish that follows any failure) already grants. Ratio
                        // ties among duplicate columns — 6,944 of air05's 7,195 share a
                        // cost — are precisely where the band earns its keep, so this is
                        // WIDE LPs only (the same gate as every anti-degeneracy device
                        // here): duplicate-column tie groups are a set-partitioning
                        // phenomenon, and the square-ish dense ladder keeps its exact
                        // pivot stream. Deterministic: a fixed tolerance over a
                        // totally-ordered scan with a strict `>` keeps the first-best
                        // on exact magnitude ties.
                        if let Some(k) = stop {
                            let mut best_j = self.bp[k].1 as usize;
                            if lp.dual_churn_band() {
                                // Breakpoint ratios r'_j = r_j · vmul(b_leave) share the
                                // leaving column's frame factor, so the band does too.
                                let band = churn_band_factor() * cost_tol_band * lp.vmul(b_leave);
                                let r_stop = self.bp[k].0;
                                let mut best_mag = self.arow[best_j].abs();
                                for &(r, ju) in &self.bp[k + 1..] {
                                    if r > r_stop + band {
                                        break;
                                    }
                                    let j = ju as usize;
                                    let mag = self.arow[j].abs();
                                    if mag > best_mag {
                                        best_mag = mag;
                                        best_j = j;
                                    }
                                }
                            }
                            enter = Some(best_j);
                        }
                        if let Some(t) = tb {
                            SEL_BAND_NANOS.fetch_add(
                                t.elapsed().as_nanos() as u64,
                                std::sync::atomic::Ordering::Relaxed,
                            );
                        }
                    } // slow path (fast_enter == None)
                }
                if let Some(t) = t_select {
                    RT_SELECT_NANOS.fetch_add(
                        t.elapsed().as_nanos() as u64,
                        std::sync::atomic::Ordering::Relaxed,
                    );
                }
            } // if !deferred_done
            let Some(col) = enter else {
                DUAL_NOENTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                // Dual unbounded => primal infeasible, and the evidence is already in
                // hand: `rho` is the leaving row's inverse row, and "no entering
                // column" says its inner product with every column is signed so the
                // box cannot satisfy the row — a Farkas candidate. Hand it to `run`,
                // which verifies it rigorously and, on success, skips the
                // rollback-and-primal re-proof (flugpl: 6,269 noenters, each one a
                // rolled-back refactorization plus a full phase-1 saying the same
                // thing). Transactional: the flip set was never applied.
                // Oriented so the verifier's FIRST sign pass succeeds: for a
                // basic below its lower bound the box-minimum argument wants
                // `+rho` (each nonbasic rests where `arow_j·z_j` is already
                // minimal, and the leaving column's own term contributes its
                // violated bound); above, the mirror.
                self.noenter_ray = Some(if below {
                    self.rho.clone()
                } else {
                    self.rho.iter().map(|v| -v).collect()
                });
                if anat {
                    self.dual_anat_commit(lp, 0, iter);
                }
                return false;
            };

            // PXPROFILE: the PRIMARY α = B⁻¹a_q FTRAN — the Mission-A target, once
            // per pivot, untimed by RT/UPD profilers (it sits between select-end
            // and update-start).
            let px_alpha_t0 = if rt_profile {
                Some(std::time::Instant::now())
            } else {
                None
            };
            self.ftran(lp, col);
            if let Some(t) = px_alpha_t0 {
                PX_ALPHA_NANOS.fetch_add(
                    t.elapsed().as_nanos() as u64,
                    std::sync::atomic::Ordering::Relaxed,
                );
            }
            let piv = self.alpha[row];
            if !piv.is_finite() || piv.abs() <= pivot_tol {
                use std::sync::atomic::Ordering::Relaxed;
                DUAL_VANISH.fetch_add(1, Relaxed);
                DUAL_VANISH_IT.fetch_add(iter as u64, Relaxed);
                if trace_enabled() && DUAL_VANISH.load(Relaxed) <= 5 {
                    eprintln!(
                        "--trace dual vanish: iter={iter} piv={piv:.3e} arow={:.3e} since_refac={}",
                        self.arow[col], self.since_refactor
                    );
                }
                for &i in &self.nz {
                    self.alpha[i] = 0.0;
                }
                if anat {
                    self.dual_anat_commit(lp, 2, iter);
                }
                return false;
            }
            // BASIS-UPDATE PROFILER: total-update wall starts here (committed path
            // only; the rare LU-reject abort below leaves it unrecorded). Trace-gated.
            let upd_t0 = if rt_profile {
                Some(std::time::Instant::now())
            } else {
                None
            };
            // The flip set's aggregate movement, solved against the OLD basis (the LU
            // update below replaces a column of B). Raw A-space; apply_inverse folds
            // the same sign convention either engine path uses. Nothing is APPLIED
            // until the update commits, so every abort below stays transactional.
            let flip_t0 = if rt_profile {
                Some(std::time::Instant::now())
            } else {
                None
            };
            if !self.flips.is_empty() {
                let flip_nz = self.prepare_sparse_flip_solve(lp, flip_solve);
                // Track wflip's matrix-row support during the scatter ONLY when
                // the sparse solve is armed (opt-in, a measured dead-end here):
                // the pushes are dead on the default dense/eta paths, so those
                // stay byte-for-byte the old walk with zero added bookkeeping.
                if flip_nz {
                    self.wflipnz.clear();
                }
                for &ju in &self.flips {
                    let j = ju as usize;
                    let delta = match self.at[j] {
                        NbBound::Lower => self.up[j] - self.lo[j],
                        NbBound::Upper => self.lo[j] - self.up[j],
                        NbBound::Zero => 0.0,
                    };
                    if j < lp.n {
                        for p in lp.col_ptr[j]..lp.col_ptr[j + 1] {
                            let r = lp.col_idx[p];
                            self.wflip[r] += lp.p_col_val()[p] * delta;
                            if flip_nz {
                                self.wflipnz.push(r);
                            }
                        }
                    } else {
                        let r = j - lp.n;
                        self.wflip[r] -= delta;
                        if flip_nz {
                            self.wflipnz.push(r);
                        }
                    }
                }
                // Sparse Gilbert–Peierls solve when the LU engine is live and the
                // lever is armed; otherwise the dense `ftran` / eta apply, exactly
                // as before. Byte-identical: same L/eta/U arithmetic, same order.
                match self.lu.as_mut() {
                    Some(cache) if flip_nz => {
                        cache.eng.ftran_nz(&mut self.wflip, &mut self.wflipnz)
                    }
                    Some(cache) => cache.eng.ftran(&mut self.wflip),
                    None => Self::apply_inverse_parts(None, &self.etas, &mut self.wflip),
                }
            }
            if let Some(t) = flip_t0 {
                use std::sync::atomic::Ordering::Relaxed;
                UPD_FLIP_NANOS.fetch_add(t.elapsed().as_nanos() as u64, Relaxed);
                if !self.flips.is_empty() {
                    UPD_FLIP_PIVOTS.fetch_add(1, Relaxed);
                    UPD_FLIP_COLS.fetch_add(self.flips.len() as u64, Relaxed);
                }
            }
            // τ = B⁻¹ρ for the steepest-edge weight update, against the OLD basis.
            let tau_t0 = if rt_profile {
                Some(std::time::Instant::now())
            } else {
                None
            };
            self.tau.copy_from_slice(&self.rho);
            match self.lu.as_mut() {
                // LU path: BYTE-IDENTICAL reachability-sparse solve. `ynz` still
                // holds ρ's support (b's nonzero pattern) from this iteration's
                // pivot-row BTRAN — and it is DEAD after τ (the DSE roll below reads
                // τ over the ENTERING column's support `self.nz`, and the next
                // iteration rebuilds `ynz` from scratch), so `ftran_nz` may clobber
                // it with τ's own support. Same L/eta/U arithmetic as the dense
                // `ftran`, in the same order, with the structural zeros skipped.
                Some(cache) if tau_nz => cache.eng.ftran_nz(&mut self.tau, &mut self.ynz),
                Some(cache) => cache.eng.ftran(&mut self.tau),
                None => Self::apply_inverse_parts(None, &self.etas, &mut self.tau),
            }
            if let Some(t) = tau_t0 {
                use std::sync::atomic::Ordering::Relaxed;
                UPD_TAU_NANOS.fetch_add(t.elapsed().as_nanos() as u64, Relaxed);
                let rnnz = self.rho.iter().filter(|&&v| v != 0.0).count() as u64;
                RHO_NNZ_SUM.fetch_add(rnnz, Relaxed);
            }
            let lu_t0 = if rt_profile {
                Some(std::time::Instant::now())
            } else {
                None
            };
            // The LU engine's update is fallible where the eta append was not:
            // it must be attempted BEFORE any bookkeeping (xb steps, basis maps)
            // so a rejection leaves the whole state untouched — the dual then
            // aborts transactionally, exactly like a vanishing pivot.
            if let Some(cache) = self.lu.as_mut() {
                // `self.nz` is `self.alpha`'s support from the FTRAN above
                // (nothing between narrows it, and the pivot loops only ever
                // zero entries, which keeps it a superset) — the pattern the
                // sparse spike build needs, at no cost. See `update_nz`.
                if cache.eng.update_nz(row, &self.alpha, &self.nz).is_err() {
                    use std::sync::atomic::Ordering::Relaxed;
                    DUAL_LUREJ.fetch_add(1, Relaxed);
                    DUAL_LUREJ_IT.fetch_add(iter as u64, Relaxed);
                    if trace_enabled() && DUAL_LUREJ.load(Relaxed) <= 5 {
                        eprintln!(
                            "--trace dual lurej: iter={iter} piv={piv:.3e} since_refac={}",
                            self.since_refactor
                        );
                    }
                    for &i in &self.nz {
                        self.alpha[i] = 0.0;
                    }
                    if anat {
                        self.dual_anat_commit(lp, 2, iter);
                    }
                    return false;
                }
                cache.rep_basis[row] = col;
                self.eta_nnz = cache.eng.nnz();
                // An LU pivot moves the basis WITHOUT an eta append: the pooled eta file no
                // longer represents it, so the cross-solve reuse must not adopt the pair
                // (audit must-fix; this was a stale-file corridor under AY_MILP_NO_NODE_LU).
                self.factor_live = false;
            }
            if let Some(t) = lu_t0 {
                UPD_LU_NANOS.fetch_add(
                    t.elapsed().as_nanos() as u64,
                    std::sync::atomic::Ordering::Relaxed,
                );
            }
            // Commit the flips: each passed column jumps to its opposite bound, and
            // every basic pays the aggregate movement. This is the long step's whole
            // yield — and it counts as progress for the stall clock even when the
            // entering pivot itself lands degenerate.
            let flipc_t0 = if rt_profile {
                Some(std::time::Instant::now())
            } else {
                None
            };
            if !self.flips.is_empty() {
                if anat {
                    self.anat_flip += 1;
                }
                for i in 0..self.m {
                    if self.wflip[i] != 0.0 {
                        self.xb[i] -= self.wflip[i];
                    }
                }
                for &ju in &self.flips {
                    let j = ju as usize;
                    let nb = match self.at[j] {
                        NbBound::Lower => NbBound::Upper,
                        NbBound::Upper => NbBound::Lower,
                        NbBound::Zero => NbBound::Zero,
                    };
                    self.at[j] = nb;
                    // A flipped column stays NONBASIC — mirror its new resting bound
                    // into the eligibility bitmask (Lower->1, Upper->2, Zero->0).
                    if rt_kind_maint {
                        self.rt_kind[j] = match nb {
                            NbBound::Lower => 1,
                            NbBound::Upper => 2,
                            NbBound::Zero => 0,
                        };
                    }
                }
            }
            if let Some(t) = flipc_t0 {
                UPD_FLIPCOMMIT_NANOS.fetch_add(
                    t.elapsed().as_nanos() as u64,
                    std::sync::atomic::Ordering::Relaxed,
                );
            }
            let leaving = self.basis[row];
            let target = if below {
                self.lo[leaving]
            } else {
                self.up[leaving]
            };
            // `xb[row] = -Σ_j alpha_j x_j`, so raising the entering column by `s` moves
            // it by `-alpha_col · s`. Landing it exactly on `target` therefore needs
            // the MINUS. Dropping it moves every OTHER row the wrong way and yields a
            // basis that passes both feasibility and pricing while not being optimal —
            // the node bound then comes out wrong and the tree explodes.
            let step = (self.xb[row] - target) / piv;
            // `step` is in the ENTERING column's scaled units.
            if step.abs() <= 1e-12 * lp.bmul(col) && self.flips.is_empty() {
                stall += 1;
                if anat {
                    self.anat_dstep += 1;
                }
            } else {
                stall = 0;
            }

            // `nz` entries are `< m`, bounding alpha/xb/tau/dse (debug-asserted
            // in `ftran`), so these support walks run unchecked.
            for &i in &self.nz {
                // SAFETY: `ftran` guarantees `i < m`, which bounds `alpha`.
                let ai = unsafe { *self.alpha.get_unchecked(i) };
                if i != row && ai != 0.0 {
                    // SAFETY: `ftran` guarantees `i < m`, which bounds `xb`.
                    unsafe { *self.xb.get_unchecked_mut(i) -= ai * step };
                }
            }
            let entering_value = self.nb_value(lp, col) + step;

            if self.lu.is_none() {
                let inv = 1.0 / piv;
                let before = self.etas.entries();
                for &i in &self.nz {
                    // SAFETY: `ftran` guarantees `i < m`, which bounds `alpha`.
                    let ai = unsafe { *self.alpha.get_unchecked(i) };
                    if i != row && ai != 0.0 {
                        self.etas.push_entry(i, -ai * inv);
                    }
                }
                self.eta_nnz += self.etas.entries() - before;
                self.etas.finish_eta(row, inv);
            }
            self.since_refactor += 1;

            // Roll the duals forward: y' = y + theta·rho, so d'_j = d_j − theta·alpha_j.
            // The entering column's reduced cost goes to zero (it is basic now) and the
            // leaving one's becomes −theta (its column meets the pivot row at 1).
            let theta = self.d[col] / self.arow[col];
            if theta.abs() <= 1e-12 {
                stats::bump(&stats::DUAL_DEGEN);
                if anat {
                    self.anat_dtheta += 1;
                }
            }
            let axpy_t0 = if rt_profile {
                Some(std::time::Instant::now())
            } else {
                None
            };
            if theta.is_finite() {
                // Branchless over ALL columns — a plain vectorisable AXPY.
                // Every d[j] the algorithm ever READS is a nonbasic one (the
                // ratio test and `theta` both skip basics), and for those this
                // is the same update: a zero `arow[j]` subtracts an exact
                // `±0.0`, changing nothing (at worst a zero's sign, and a
                // breakpoint with `|arow[j]| <= pivot_tol` is never examined).
                // Basic slots accumulate noise instead of staying 0.0 — and are
                // rewritten before they next matter: the leaver gets `-theta`
                // below, and a column entering later gets `0.0` on entry.
                // (A zipped basic_row-predicated form arrived from the parallel
                // campaign in the same window; this branchless one subsumes it
                // and was outcome-validated on the full ladder.)
                for (dj, &aj) in self.d.iter_mut().zip(&self.arow) {
                    *dj -= theta * aj;
                }
            }
            if let Some(t) = axpy_t0 {
                UPD_AXPY_NANOS.fetch_add(
                    t.elapsed().as_nanos() as u64,
                    std::sync::atomic::Ordering::Relaxed,
                );
                // Mean pivot-row density: one gated O(cols) count of arow's
                // nonzeros. Off by default, so it never taxes the hot path.
                let nnz = self.arow.iter().filter(|&&a| a != 0.0).count() as u64;
                AROW_NNZ_SUM.fetch_add(nnz, std::sync::atomic::Ordering::Relaxed);
                // Entering-column FTRAN support size (= |nz|): decides whether a
                // fused 2-RHS dense old-B solve (α with τ) could beat the sparse α.
                ALPHA_NNZ_SUM.fetch_add(self.nz.len() as u64, std::sync::atomic::Ordering::Relaxed);
            }
            self.d[leaving] = -theta;
            self.d[col] = 0.0;

            self.basic_row[leaving] = None;
            self.at[leaving] = if below {
                NbBound::Lower
            } else {
                NbBound::Upper
            };
            self.basis[row] = col;
            self.basic_row[col] = Some(row);
            // Incrementally track the ratio-test eligibility bitmask across the pivot:
            // the LEAVER goes nonbasic at its violated bound (below -> Lower=1, else
            // Upper=2), the ENTERING column becomes basic (=0). Every other column's
            // eligibility is basis-invariant, so these two writes keep `rt_kind` a
            // byte-exact mirror of `basic_row`/`at` for the next iteration's scan.
            if rt_kind_maint {
                self.rt_kind[leaving] = if below { 1 } else { 2 };
                self.rt_kind[col] = 0;
            }
            self.xb[row] = entering_value;

            // Forrest–Goldfarb: the leaving row's norm shrinks by the pivot square;
            // every touched row pays the projection. Floored — a collapsed weight
            // would make its row look infinitely attractive forever after.
            //
            // And CAPPED, for the mirror-image failure: a tiny pivot INFLATES a weight by
            // 1/piv² — up to 1e18 in one pivot at `pivot_tol` — and with nothing above it
            // the compounding overflows to +inf. An infinite weight makes its row
            // invisible forever after: the leave scan's score is `viol²/dse` = 0.0, and
            // `score > worst` never fires with `worst` floored at zero — so a basic
            // sitting UNITS outside its bound is skipped, leave comes back None, and the
            // dual exits "optimal" on a primal-infeasible basis. Fail-closed caught every
            // one (the post-check re-solved cold; no wrong answers), but under
            // AY_MILP_DSE_PERSIST the weights compound across solves and the miss rate
            // was ruinous: 70x52 s2026 ran ok=32,757 / fail=37,362, and 34,993 of those
            // failures were the primal post-check with ZERO dual violations and
            // dse[row]=inf on every dump. The cap costs nothing that matters — row
            // SELECTION is economics, and the exit test ("no basic violates feas_tol")
            // is what it always was.
            let dse_t0 = if rt_profile {
                Some(std::time::Instant::now())
            } else {
                None
            };
            let wr = self.dse[row].max(1e-10);
            for &i in &self.nz {
                // SAFETY: `ftran` guarantees `i < m`, which bounds `alpha`.
                let ai = unsafe { *self.alpha.get_unchecked(i) };
                if i != row && ai != 0.0 {
                    let ar = ai / piv;
                    // SAFETY: `ftran` guarantees `i < m`, which bounds the
                    // per-row arrays `tau` and `dse`.
                    let (ti, wi) =
                        unsafe { (*self.tau.get_unchecked(i), *self.dse.get_unchecked(i)) };
                    // NOT `clamp`: max/min maps a NaN (overflowed update) to the 1e-4
                    // floor, where clamp would propagate it into the pricing weights.
                    #[allow(clippy::manual_clamp)]
                    let nw = (wi - 2.0 * ar * ti + ar * ar * wr)
                        .max(1e-4)
                        .min(DSE_WEIGHT_CAP);
                    // SAFETY: `ftran` guarantees `i < m`, which bounds `dse`.
                    unsafe { *self.dse.get_unchecked_mut(i) = nw };
                }
            }
            // NOT `clamp`: max/min maps a NaN (overflowed update) to the 1e-4
            // floor, where clamp would propagate it into the pricing weights.
            #[allow(clippy::manual_clamp)]
            {
                self.dse[row] = (wr / (piv * piv)).max(1e-4).min(DSE_WEIGHT_CAP);
            }
            if let Some(t) = dse_t0 {
                UPD_DSE_NANOS.fetch_add(
                    t.elapsed().as_nanos() as u64,
                    std::sync::atomic::Ordering::Relaxed,
                );
            }

            for &i in &self.nz {
                // SAFETY: `ftran` guarantees `i < m`, which bounds `alpha`.
                unsafe { *self.alpha.get_unchecked_mut(i) = 0.0 };
            }
            if let Some(t) = upd_t0 {
                use std::sync::atomic::Ordering::Relaxed;
                UPD_TOTAL_NANOS.fetch_add(t.elapsed().as_nanos() as u64, Relaxed);
                UPD_PIVOTS.fetch_add(1, Relaxed);
            }
        }
        DUAL_BUDGET.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        if anat {
            self.dual_anat_commit(lp, 2, budget);
        }
        false // budget spent: hand it to the primal
    }

    /// Do the given reduced costs point the way each column's bound requires?
    /// Is the basis the dual simplex arrived at good enough to KEEP?
    ///
    /// This is not a soundness gate and must not be tuned like one. The node's bound is rigorous
    /// for ANY duals whatsoever, and every leaf is re-derived in exact rationals -- so accepting a
    /// basis that is dual feasible only to within float noise costs nothing but a slightly weaker
    /// bound. REJECTING it costs a cold primal re-solve of the whole node.
    ///
    /// So the tolerance here is deliberately looser than the one pricing uses. Sharing it was a
    /// disaster on qnet1: its objective coefficients are around 1, so `cost_tol` came out at 2e-9
    /// -- below the error of a BTRAN over 503 rows -- and the dual's answer was thrown away EVERY
    /// time (DUAL ok=0, fail=1105, all of them here). Each node then paid for a cold primal, at
    /// 810ms a node, and the search managed 16 nodes in 15 seconds.
    /// How many nonbasic columns have a reduced cost pointing the wrong way for their bound.
    fn dual_violations(&mut self, lp: &FloatLp) -> usize {
        let tol = self.cost_tol(lp).max(DUAL_ACCEPT_TOL);
        if !self.y_is_duals {
            for i in 0..self.m {
                self.cb[i] = self.pcost[self.basis[i]];
            }
            self.y.copy_from_slice(&self.cb);
            self.btran();
            self.y_is_duals = true;
        }
        self.fill_yta(lp); // full sweep either way; row-major, same bits
        (0..self.cols)
            .filter(|&j| {
                if self.basic_row[j].is_some() || self.lo[j] == self.up[j] {
                    return false; // basic, or fixed and thus not a candidate -- see `priced_out`
                }
                let rc = if j < lp.n {
                    self.pcost[j] - self.arow[j]
                } else {
                    self.pcost[j] + self.y[j - lp.n]
                };
                // Reduced costs carry the frame d'_j = d_j·vmul(j).
                let ct = tol * lp.vmul(j);
                match self.at[j] {
                    NbBound::Lower => rc < -ct,
                    NbBound::Upper => rc > ct,
                    NbBound::Zero => rc.abs() > ct,
                }
            })
            .count()
    }

    #[allow(dead_code)]
    fn dual_feasible(&self, lp: &FloatLp, d: &[f64]) -> bool {
        let cost_tol = self.cost_tol(lp).max(DUAL_ACCEPT_TOL);
        (0..self.cols).all(|j| {
            if self.basic_row[j].is_some() || self.lo[j] == self.up[j] {
                return true; // basic, or fixed -- see `priced_out`
            }
            let ct = cost_tol * lp.vmul(j);
            match self.at[j] {
                NbBound::Lower => d[j] >= -ct,
                NbBound::Upper => d[j] <= ct,
                NbBound::Zero => d[j].abs() <= ct,
            }
        })
    }

    /// Does anything price in? (Phase-II optimality, given primal feasibility.)
    fn priced_out(&mut self, lp: &FloatLp) -> bool {
        let cost_tol = self.cost_tol(lp).max(DUAL_ACCEPT_TOL);
        if !self.y_is_duals {
            for i in 0..self.m {
                self.cb[i] = self.pcost[self.basis[i]];
            }
            self.y.copy_from_slice(&self.cb);
            self.btran();
            self.y_is_duals = true;
        }
        // Row-major sweep once, then read per column — same bits as the old
        // per-column gathers (see `fill_yta`). The sweep is not conditional on
        // how far the loop below gets, but ~96% of calls price out fully
        // (measured dual outcomes), so the full sweep was the common case.
        self.fill_yta(lp);
        for j in 0..self.cols {
            if self.basic_row[j].is_some() {
                continue;
            }
            // A FIXED column is not a candidate and never was -- it has nowhere to go, so its
            // reduced cost may point wherever it likes. Pricing skips it; this must too, or the
            // two disagree about what "optimal" means.
            //
            // They did, and it was ruinous. Branching FIXES columns constantly (`x <= 0` on a
            // binary already at `lo = 0` gives the box `[0, 0]`), so on any branched node this
            // test found columns "pricing in" that pricing itself would never look at -- and the
            // dual simplex's answer was therefore rejected on EVERY node of every model here
            // (DUAL ok=0). Each rejection cost a cold primal re-solve. It is the single most
            // expensive line in the engine.
            if self.lo[j] == self.up[j] {
                continue;
            }
            let rc = if j < lp.n {
                self.pcost[j] - self.arow[j]
            } else {
                self.pcost[j] + self.y[j - lp.n]
            };
            // Frame-equivalent acceptance: d'_j = d_j·vmul(j), and the
            // DUAL_ACCEPT_TOL floor is folded into `cost_tol` BEFORE this
            // multiply — the unscaled test is |d| > max(base, floor).
            let ct = cost_tol * lp.vmul(j);
            let improving = match self.at[j] {
                NbBound::Lower => rc < -ct,
                NbBound::Upper => rc > ct,
                NbBound::Zero => rc.abs() > ct,
            };
            if improving {
                return false;
            }
        }
        true
    }

    /// Is every basic variable inside its bounds?
    ///
    /// Phase II has no machinery to notice that it is not. Its ratio test keeps
    /// basics inside their bounds only while the pivot elements are healthy: a
    /// basic whose entry in the entering column is below `pivot_tol` is skipped
    /// by the test, and over many pivots with a large step it can drift right out
    /// of its box. The loop then prices out and calls the result an optimum, and
    /// the "optimum" is a point that is not even feasible.
    /// Is every basic variable inside its own bounds?
    ///
    /// A PER-VARIABLE tolerance was tried here and it is too tight: a variable whose bound is zero
    /// then gets 1e-7 where the model-wide figure gave it 7.6e-5, and gt2 -- which this engine
    /// proves in a tenth of a second -- stopped proving at all. The float lane drifts more than
    /// 1e-7 on a real basis, and this check is what decides whether to keep it.
    ///
    /// The CAP below is what was actually needed: the tolerance is sized off the largest right-hand
    /// side, and one big number was licensing a big violation everywhere.
    fn primal_feasible(&self, lp: &FloatLp) -> bool {
        let tol = self.feas_tol(lp);
        (0..self.m).all(|i| {
            let b = self.basis[i];
            let v = self.xb[i];
            let t = tol * lp.bmul(b);
            v >= self.lo[b] - t && v <= self.up[b] + t
        })
    }

    /// THE COLD DUAL-SIMPLEX START, for the LPs whose crash basis is already
    /// dual feasible — which is set partitioning exactly. On air05's root LP
    /// (426 x 7,195, every cost >= 0) the all-logical crash basis has duals
    /// `y = 0`, so every reduced cost IS the column's cost, and resting each
    /// column on the bound its cost sign prefers makes the start dual feasible
    /// outright. From there the dual simplex (DSE + bound-flip ratio test)
    /// restores primal feasibility row by row — the same route HiGHS takes,
    /// 1,510 iterations on this LP — where the primal phase-I/phase-II walk
    /// from the same crash basis pays a degenerate grind (measured: 9,493
    /// primal iterations WITH eager perturbation, 400k+ and `Stopped` without;
    /// this path: 2,904 dual pivots, 0.37s against 2.16s).
    ///
    /// Deterministic: the resting flips depend only on cost signs, the budget
    /// is an iteration count, and the dual's own pivoting is deterministic.
    /// Transactional: on any failure (dual infeasible at rest, budget burned,
    /// post-checks) the crash basis and resting bounds are restored exactly
    /// and the caller falls through to the primal path unchanged.
    fn try_cold_dual(&mut self, lp: &FloatLp, deadline: Option<std::time::Instant>) -> bool {
        // The dual-feasibility test below reads costs AS the reduced costs,
        // which is only true under `y = 0` — every logical basic in its own
        // slot. A caller arriving on any other basis (the warm-failure
        // fallback: the parent's basis was rolled back, and it is exactly the
        // basis that already failed) is RESET to the crash start: B = -I,
        // whose inverse both engines represent exactly for free. Columns that
        // were basic keep the resting bound `at` recorded for them — any
        // finite rest is valid, and the cost-sign pass below re-seats every
        // candidate anyway.
        if (0..self.m).any(|r| self.basis[r] != lp.n + r) {
            self.y_is_duals = false;
            self.basic_row.fill(None);
            for r in 0..self.m {
                self.basis[r] = lp.n + r;
                self.basic_row[lp.n + r] = Some(r);
            }
            match self.lu.as_mut() {
                Some(cache) => {
                    cache.eng.reset_to_identity();
                    cache.rep_basis.clear();
                    cache.rep_basis.extend(lp.n..lp.n + self.m);
                    self.sync_lu_counters();
                }
                None => {
                    self.etas.clear();
                    self.eta_nnz = 0;
                    self.since_refactor = 0;
                    self.factor_live = true; // empty file == the crash basis just built
                    self.chain_gen = 0;
                }
            }
        }
        // The walk below NEEDS the LU engine's accuracy: on air05's root LP the
        // eta-file inverse's drift stretches this same start from 2,904 pivots
        // to 9,886 (the drift feeds the pivot choices, not just the arithmetic).
        // A `plain_cold` caller (the search's own LP at a node fallback) runs
        // classic everywhere else, so it arrives here without an engine —
        // install a fresh one for the price of nothing (it represents B = -I,
        // the crash basis just built, with zero factor work).
        if self.lu.is_none() && !lu_enabled() {
            self.lu = Some(LuCache {
                eng: crate::lu::LuEngine::new(self.m),
                rep_basis: (lp.n..lp.n + self.m).collect(),
            });
            self.sync_lu_counters();
        }
        // Rest every structural on the bound its cost sign wants. A column
        // whose preferred side is unbounded leaves the start dual infeasible:
        // hand the whole solve to the primal rather than repair it here.
        // (Logicals cost 0 and are basic; fixed columns are never candidates.)
        self.snap_at.clear();
        self.snap_at.extend_from_slice(&self.at);
        for j in 0..lp.n {
            if self.lo[j] == self.up[j] {
                continue;
            }
            let c = self.pcost[j];
            let want = if c > 0.0 {
                NbBound::Lower
            } else if c < 0.0 {
                NbBound::Upper
            } else {
                continue; // zero cost is dual feasible wherever it rests
            };
            if self.at[j] == want {
                continue;
            }
            let ok = match want {
                NbBound::Lower => self.lo[j].is_finite(),
                NbBound::Upper => self.up[j].is_finite(),
                NbBound::Zero => true,
            };
            if !ok {
                self.at.copy_from_slice(&self.snap_at);
                return false;
            }
            self.at[j] = want;
        }
        self.recompute_xb(lp);
        let budget = COLD_DUAL_BUDGET_PER_ROW * self.m + 200;
        let settled = self.dual_simplex(lp, deadline, budget)
            && self.primal_feasible(lp)
            && self.priced_out(lp);
        if settled {
            return true;
        }
        // Roll back to the crash start exactly: basis, resting bounds, and a
        // factorization that represents it (the dual pivots mutated all
        // three). `warm_start` refactorizes; `run` recomputes `xb` downstream.
        let at = std::mem::take(&mut self.snap_at);
        let crash: Vec<usize> = (lp.n..lp.n + self.m).collect();
        let (lo, up) = (self.lo.clone(), self.up.clone());
        self.warm_start(lp, &crash, &at, &lo, &up);
        self.snap_at = at;
        false
    }

    fn run(
        &mut self,
        lp: &FloatLp,
        warm_started: bool,
        warm_mode: WarmSolveMode,
        deadline: Option<std::time::Instant>,
    ) -> SimplexStatus {
        debug_assert!(
            warm_started || warm_mode == WarmSolveMode::Normal,
            "direct-primal warm modes require an adopted warm basis"
        );
        self.warm_run = warm_started;
        // Phase I, phase II, and then CHECK — because an optimum over an
        // infeasible point is not an optimum. On drift, refactorize (which
        // rebuilds `B^{-1}` from scratch and kills the accumulated error) and go
        // round again. If it will not settle, say `Stopped` and let the caller
        // take the exact rim: a wrong basis that is merely SLOW to discover is
        // fine, one that is silently believed is not.
        //
        // Without this check the drifted basis reports a column outside its own
        // bounds, and a branch-and-bound branching on that value produces a child
        // identical to its parent and recurses forever.
        // A warm basis is dual feasible, so try the dual simplex first. Its answer is
        // put through the SAME checks the primal's is — primal feasible AND priced out
        // — so a dual bug costs a slow node, never a wrong one.
        if warm_started && warm_mode.continues_primal() {
            // DIRECT PRIMAL: `warm_start` has already adopted and refactorized
            // the prior basis under this narrower box. Continue its primal
            // feasibility work directly. In particular, do not spend time on
            // a transactional dual walk whose failure restores the very basis
            // it started from. `PrimalAdvice` is setup-only;
            // `PrimalProofContinuation` is admitted only where the caller
            // applies the normal exact verdict gates.
            self.recompute_xb(lp);
        } else if warm_started && !lp.warm_dual_should_attempt() {
            // ADAPTIVE BYPASS (see `warm_dual_should_attempt`): the warm dual
            // keeps losing on this LP, so skip the doomed walk and hand the
            // warm basis straight to the primal — exactly the state the
            // rollback path would have handed it, minus the wasted walk.
            DUAL_SKIP.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            self.recompute_xb(lp);
        } else if warm_started {
            // The dual attempt must be TRANSACTIONAL. It pivots as it goes, so a
            // failure halfway leaves a half-pivoted basis — and handing THAT to the
            // primal is worse than never having warm-started at all: the primal then
            // repairs a basis that is neither the parent's nor an optimum. (This is
            // why shrinking the dual's budget made things dramatically WORSE rather
            // than cheaper — the failures got more frequent, and every failure was
            // poisoning the fallback.) So snapshot, and roll back on failure.
            self.snap_basis.clear();
            self.snap_basis.extend_from_slice(&self.basis);
            self.snap_at.clear();
            self.snap_at.extend_from_slice(&self.at);
            self.recompute_xb(lp);
            use std::sync::atomic::Ordering::Relaxed;
            let _dv_in = if trace_enabled() {
                self.dual_violations(lp)
            } else {
                0
            };
            // Check the reduced costs the dual has been MAINTAINING, rather than
            // re-pricing from scratch. `priced_out` costs a BTRAN plus a full O(nnz) sweep
            // to recompute the very numbers the dual already holds — and it has never once
            // disagreed with them (`postchk` has not fired). Optimality of the basis is not
            // a soundness gate anyway: a non-optimal basis makes the node's bound WEAKER,
            // never wrong (the bound is rigorous for ANY duals), and every leaf is still
            // re-derived exactly. So this check buys tightness, and it can buy it in
            // O(cols) rather than O(nnz).
            // WARM-DUAL BUDGET. The default `2m+50` is sized for a healthy
            // one-bound-change child the dual fixes in tens of pivots. On a WIDE
            // set-partitioning LP (air05: 426×7,195) whose divergence guard is
            // relaxed (see the `bloom_cap` note), the child's warm dual instead
            // needs up to a few thousand pivots to walk the parent's near-optimal
            // basis back to primal feasibility; at `2m+50=902` it is cut off,
            // ROLLS BACK, and `try_cold_dual` re-crashes to B=-I and pays the whole
            // cold solve (~2-4k pivots) anyway — warm-fail + cold, worse than cold
            // alone. Give the warm dual the cold path's own room (`30m+200`) on
            // exactly these LPs (`keep` is already unconditionally true for them —
            // they are wide — so a walk that reaches primal feasibility is KEPT and
            // phase-II-polished, and the cold re-crash never runs). Same
            // `wide_tall` gate as the bloom relaxation, so the NN/qiu tall shapes
            // are byte-for-byte untouched. Verdict-neutral: a longer walk only
            // changes the path; every exit is re-checked (primal feasible AND
            // priced out) and every leaf re-derived exactly.
            let warm_budget = if lp.wide_tall() && !no_wide_bloom() {
                COLD_DUAL_BUDGET_PER_ROW * self.m + 200
            } else {
                2 * self.m + 50
            };
            let dual_reached_opt = self.dual_simplex(lp, deadline, warm_budget);
            // If the warm dual DECLINED on memory, give up now — before the
            // hit_cutoff / noenter / cold-dual fallbacks below, all of which
            // would keep working (and one re-enters the dual). The `oom` flag is
            // authoritative over any partial verdict the walk left behind.
            if self.oom {
                return SimplexStatus::OutOfMemory;
            }
            // CUTOFF STOP: the dual's monotone bound reached the caller's cutoff, so
            // the node is prunable on the (dual-feasible) basis in hand. Hand it back
            // as `Cutoff`; the caller re-derives the bound rigorously before pruning.
            // No rollback: the basis is a clean, dual-feasible mid-walk state whose
            // duals `extract` reads directly.
            if self.hit_cutoff {
                lp.note_warm_dual(true);
                return SimplexStatus::Cutoff;
            }
            let settled = if dual_reached_opt {
                // No recompute here. The dual maintains `xb` as it pivots
                // (`xb[i] -= alpha[i]·step`), and it exits precisely BECAUSE that
                // maintained vector is within bounds — so recomputing it is asking the
                // same question twice. Drift is bounded by the refactorization cadence
                // inside the loop, and anything it could cost is caught downstream: a
                // leaf is re-derived in exact rationals, and the node's bound is
                // rigorous whatever the basis.
                // RE-PRICE; DO NOT TRUST THE MAINTAINED REDUCED COSTS.
                //
                // The dual updates `d` incrementally as it pivots, and this used to check that
                // vector directly -- on the grounds that re-pricing costs a BTRAN plus a sweep
                // over the non-zeros to recompute numbers already in hand, and that the two had
                // never disagreed. They disagree constantly on a real model: `d` DRIFTS, and by
                // more than any tolerance worth having. On qnet1 and khb05250 the dual's answer
                // was thrown away EVERY time (ok=0, fail=862, all of them right here), and each
                // rejection cost a cold primal re-solve of the node -- 810ms a node on qnet1,
                // which is why it managed sixteen nodes in fifteen seconds.
                //
                // A BTRAN is a rounding error next to that. Ask the real question.
                let ok = self.primal_feasible(lp) && self.priced_out(lp);
                if !ok {
                    DUAL_POSTCHK.fetch_add(1, Relaxed);
                    if trace_enabled() && DUAL_POSTCHK.load(Relaxed) <= 3 {
                        let out = self.dual_violations(lp);
                        eprintln!(
                            "--trace !! dual: violations IN={_dv_in} OUT={out} (of {} cols)",
                            self.cols
                        );
                    }
                }
                ok
            } else {
                false
            };
            if settled {
                DUAL_OK.fetch_add(1, Relaxed);
                lp.note_warm_dual(true);
                return SimplexStatus::Optimal;
            }
            DUAL_FAIL.fetch_add(1, Relaxed);
            // The dual exited with NO ENTERING COLUMN: dual unbounded, primal
            // infeasible, and the leaving row's inverse row is the Farkas
            // evidence. Verify it HERE with the same rigorous interval check
            // the tree runs before pruning a subtree (`safe_farkas_proves_empty`
            // — clamped, error-bounded, sign-agnostic); on success the node is
            // exactly as proven-empty as the rollback + primal phase-1 would
            // have concluded, minus the refactorization and the re-walk (flugpl:
            // 6,269 of 17,879 warm solves ended here). A ray that does not
            // verify — drift, a tolerance-starved ratio test — falls through to
            // the old path byte-for-byte.
            // Under equilibration the ray and `self.lo/up` live in the SCALED frame
            // while `safe_farkas_proves_empty` reads the ORIGINAL matrix (`lp.column`),
            // so the check cannot run on the scaled evidence directly — mixing frames
            // proves nothing, and `farkas_verified = true` licenses the caller to SKIP
            // its own rigorous check. But the mapping is exact and cheap, so we UNSCALE
            // before verifying rather than fall through:
            //   * ray:  y_r = 2^rexp_r · y'_r = bnd_mul[n+r] · ray[r] (row scaling R),
            //     the same per-row transform `solve_bounded` applies on extract. (The
            //     stored ray stays SCALED — extract() reapplies exactly this factor, so
            //     the exported Candidate.farkas lands in the original frame either way.)
            //   * box:  self.lo/up hold the scaled box lower[j]·bnd_mul[j]; multiplying
            //     back by val_mul[j] = 1/bnd_mul[j] (both powers of two) recovers the
            //     ORIGINAL node box bit-exactly — the very box the caller would re-verify
            //     against, so a shortcut PASS is identical to the caller's own check.
            // Everything here is ADVISORY (float ray, float box): the interval check is
            // the sole soundness gate, and a wrong unscale can only fail to prove — never
            // a wrong verdict (fail-closed). `AY_MILP_NO_NOENTER_UNSCALE` restores the
            // old `!lp.scaled()` gate for the A/B.
            let try_shortcut = if lp.scaled() {
                !no_noenter_unscale()
            } else {
                true
            };
            if try_shortcut {
                if let Some(ray) = self.noenter_ray.take() {
                    let n = lp.n;
                    let proven = if lp.scaled() {
                        let u: Vec<f64> = ray
                            .iter()
                            .enumerate()
                            .map(|(r, &v)| v * lp.bnd_mul[n + r])
                            .collect();
                        let olo: Vec<f64> =
                            (0..self.cols).map(|j| self.lo[j] * lp.val_mul[j]).collect();
                        let oup: Vec<f64> =
                            (0..self.cols).map(|j| self.up[j] * lp.val_mul[j]).collect();
                        crate::bab::safe_farkas_proves_empty(lp, &u, &olo, &oup)
                    } else {
                        crate::bab::safe_farkas_proves_empty(lp, &ray, &self.lo, &self.up)
                    };
                    if proven {
                        DUAL_NOENTER_SHORTCUT[lp.scaled() as usize].fetch_add(1, Relaxed);
                        self.farkas = Some(ray);
                        self.farkas_verified = true;
                        lp.note_warm_dual(true);
                        return SimplexStatus::PrimalInfeasible;
                    }
                }
            }
            // KEEP A PRIMAL-FEASIBLE BASIS EVEN WHEN IT IS NOT OPTIMAL.
            //
            // Rolling back was right for a dual that DIED mid-pivot -- a half-pivoted basis is
            // worse than never having warm-started. But a dual that RAN TO COMPLETION and merely
            // failed the optimality post-check has handed us a basis that is primal feasible, and
            // that is precisely what phase II wants. Throwing it away to restart from the parent's
            // basis -- which is primal INFEASIBLE for this child, that being the entire reason the
            // dual was called -- means paying for a phase I that has already been done.
            //
            // On qnet1 and khb05250 the dual completes every time and passes the post-check never
            // (ok=0, fail=862, all of them optimality), so every node was paying a full cold solve:
            // 810ms a node, sixteen nodes in fifteen seconds.
            // Keep the dual's basis only if phase II can be expected to finish it off quickly --
            // that is, if it is nearly dual feasible already. Keeping a basis that is a long way
            // from optimal means paying for phase II to walk all the way there, which is worse than
            // the cold start it replaced: blend2 (274 rows, square) went from a proof in 2.9s to
            // no proof at all, its node LPs taking 74ms apiece. Whereas air03 (124 rows, 10,757
            // columns) cannot AFFORD the cold start, and keeping the basis is what proves it.
            //
            // Two independent reasons to keep it, and either will do:
            //
            //   * it is NEARLY OPTIMAL already, so phase II will finish it in a few pivots; or
            //   * the LP is WIDE, where the cold start being avoided is itself the ruinous thing --
            //     air03 is 124 rows by 10,757 columns and cannot afford one, and keeping the basis
            //     however far off it is turns 'no proof in 20s' into a proof in 8.8s.
            //
            // Neither alone is enough: gating only on wide loses blend2 (square, 274 rows: 2.9s
            // proof -> none, its node LPs at 74ms apiece), and gating only on near-optimal loses
            // air03.
            let keep =
                self.dual_violations(lp) <= self.cols / 50 || lp.n >= DEVEX_WIDTH * lp.m.max(1);
            // Score the bypass policy on whether the walk's work is USED (basis
            // kept for the primal cleanup) or THROWN AWAY (rollback) — see
            // `warm_dual_should_attempt`. khb05250's dual completes and fails
            // the post-check every time, but its basis is kept and phase II
            // finishes from it: that is a win. The ACAS bloom-abort is rolled
            // back wholesale: that is the loss the policy exists to stop paying.
            lp.note_warm_dual(keep && self.primal_feasible(lp));
            if keep && self.primal_feasible(lp) {
                // Keep it -- but REBUILD B^{-1} first. The basis is the dual's, arrived at through
                // a run of pivots whose eta file has been accumulating error the whole way, and
                // the reason we are here at all is that the reduced costs came out too far off to
                // trust. Carrying that drift onward is what made the EXACT replay of a leaf fail:
                // khb05250 reached 34 leaves and `exact_point` rejected all 34, so the search had
                // nothing to show for them. A refactorisation is O(m·nnz) once, against a leaf.
                // ...rebuilding B^{-1} only if the dual actually pivoted enough to have drifted.
                // A rebuild is O(m·nnz) and on a wide model that is the whole node: doing it after
                // EVERY dual failure took air03 from a proof in 8.9s to two nodes and none. But
                // skipping it entirely lets the error ride, and it is the exact replay of a leaf
                // that pays -- khb05250 reached 34 leaves and `exact_point` rejected all 34. The
                // eta count is the honest measure of how far the basis has been carried.
                if self.since_refactor >= DRIFT_REFACTOR {
                    refac_reason(3);
                    self.refactorize(lp);
                    if self.oom {
                        return SimplexStatus::OutOfMemory;
                    }
                }
                self.recompute_xb(lp);
            } else {
                // Rare path (a few % of solves): the snapshot buffers are taken
                // out for the duration of `warm_start` and handed back after.
                let basis = std::mem::take(&mut self.snap_basis);
                let at = std::mem::take(&mut self.snap_at);
                let (lo, up) = (self.lo.clone(), self.up.clone());
                self.warm_start(lp, &basis, &at, &lo, &up);
                self.snap_basis = basis;
                self.snap_at = at;
                // WIDE-AND-TALL: restart COLD IN THE DUAL rather than hand the
                // primal a basis the dual already failed on. This branch is the
                // best-bound pop whose inherited basis is hundreds of rows from
                // the child (measured on air05: entry violations of 408 rows
                // against the healthy child's 1), and the eager-perturbed
                // primal walk from it is the catastrophic case — one such node
                // LP ran phase 2 into MAX_ITERS (200,000 iterations, 28.2s,
                // `xb` numerically diverged) plus a 27,373-iteration phase-I
                // retry, ~36s for one `Stopped` answer. The cold dual start
                // solves the same LP in ~3k pivots (~0.4s), deterministically.
                // ITERATION LEDGER: this IS the in-solve cold retry — the warm
                // dual ran, failed, and its basis was rolled back to the
                // parent's, and the walk below restarts from B = -I. Same
                // phase as the caller-level `warm = None` re-solve, because it
                // is the same thing happening one frame lower.
                //
                // The `&&` chain is split so the episode is charged only where
                // a walk actually happens. Charging it before the gates counted
                // every ROLLBACK as a cold retry, and on the square-ish corpus
                // (which is not `wide_tall`, so `try_cold_dual` never runs) the
                // ledger read `cold-retry=397 solves / 0 iterations` — a phase
                // that had not run once. Same short-circuit order, so the
                // default path is unchanged.
                // MEASUREMENT ARM (`the cold-dual-all knob`, default off, byte-identical
                // when unset): drop the `wide_tall()` shape gate so the cold dual start is
                // tried on SQUARE-ISH models too.
                //
                // Why this arm exists: the comment above records that on the square-ish
                // corpus `try_cold_dual` NEVER RUNS — and that is the corpus on which the
                // campaign's headline LP numbers were taken (iterations ay/gurobi 4.87x
                // geomean over 111 relaxations, wall 8.2x). So the cold dual start was never
                // in the measurement that concluded ay "takes 5x too many steps". Six lines
                // up, the recorded contrast on a single node LP is stark: the primal took
                // 200,000 iterations / 28.2s and diverged numerically, against ~3k pivots
                // (~0.4s) deterministically for the cold dual. If that ratio holds anywhere
                // on the square corpus, the step-count gap is partly a gating artifact
                // rather than an algorithmic deficit.
                if (lp.wide_tall() || cold_dual_all()) && !no_cold_dual() {
                    let _ledger_cold = PhaseScope::new_forced(PH_COLD_RETRY);
                    ledger_note_solve();
                    if self.try_cold_dual(lp, deadline) {
                        DUAL_OK.fetch_add(1, Relaxed);
                        return SimplexStatus::Optimal;
                    }
                }
            }
        }

        // EAGER anti-degeneracy (gated): perturb the box, run the cleanup on the perturbed problem
        // where the degenerate ties are broken, then restore the TRUE box and polish from the
        // perturbed basis — the same save/perturb/restore/polish the `Stopped` path uses below, but
        // applied BEFORE the walk instead of after it fails. The true box is restored before any
        // optimality test, so this changes only the path, never the answer.
        //
        // ON BY DEFAULT FOR WIDE-AND-TALL LPs (`n >= 10·m` — the Devex gate — AND
        // `m >= EAGER_PERTURB_MIN_ROWS`): the regime where the lazy path's MAX_ITERS degenerate
        // grind cannot be afforded even once. Measured on air05's root LP (426 x 7,195, set
        // partitioning) with the singular-basis repair and the relative ratio-test floor already
        // in: lazy perturbation ground through MAX_ITERS (200,000 iterations, stall = 187,767,
        // 171,284 of them degenerate) and only THEN perturbed, finishing at ~45s when the 60s
        // budget allowed it to finish at all; eager perturbation solved the same root to the
        // same optimum (6469.402317 internal units = 25877.609.../4) in a few thousand
        // iterations and left budget to actually branch — air05 goes UNKNOWN -> incumbent at
        // 60s.
        //
        // The row floor is measured, not aesthetic: the wide-but-SHORT members of the family
        // already win with the lazy path, and eager costs them — air03 (124 rows) lost its 60s
        // proof outright under eager (OPTIMAL 340160 @7.4s -> FEASIBLE unproven, both blanket
        // and cold-only), and mod010 (146 rows) went 3.2s -> 6.9s under blanket eager. The
        // degenerate grind this exists to prevent scales with m (every equality row's fixed
        // logical is one more tie in the crash basis), and 124/146-row members prove fine
        // lazily while 426 rows starves: the floor sits between. Square-ish LPs keep the lazy
        // path either way (the unconditional rule was measured once before and rejected — see
        // the Devex note above).
        // COLD solves on the same wide-and-tall gate: try the dual simplex from
        // the (dual-feasible, after cost-sign resting) crash basis first — see
        // `try_cold_dual`. Success ends the solve outright; failure rolled the
        // crash start back, so the primal path below runs exactly as before.
        let wide_tall = lp.wide_tall();
        if !warm_started
            && wide_tall
            && !lp.plain_cold // the vertex-seeding solves; see `FloatLp::plain_cold`
            && !no_cold_dual()
            && self.try_cold_dual(lp, deadline)
        {
            return SimplexStatus::Optimal;
        }

        let eager = eager_perturb_applies(warm_started, lp) || wide_tall || lp.eager_perturb;
        let status = if eager {
            let (save_lo, save_up) = (self.lo.clone(), self.up.clone());
            self.perturb_box(lp);
            let s = self.rounds(lp, deadline);
            self.lo.copy_from_slice(&save_lo);
            self.up.copy_from_slice(&save_up);
            if s == SimplexStatus::Optimal {
                refac_reason(4);
                self.refactorize(lp);
                if self.oom {
                    return SimplexStatus::OutOfMemory;
                }
                self.recompute_xb(lp);
                self.rounds(lp, deadline)
            } else {
                s
            }
        } else {
            self.rounds(lp, deadline)
        };
        if status == SimplexStatus::Optimal && trace_enabled() {
            let v = self.dual_violations(lp);
            if v > 0 {
                eprintln!(
                    "--trace !! a basis just declared OPTIMAL has {v} dual violations (warm={warm_started})"
                );
            }
        }
        if status != SimplexStatus::Stopped {
            return status;
        }
        // ARM the eager path for this LP's LATER cold solves: an unperturbed cold
        // walk has now demonstrably cycled, and the lazy retry below is what
        // "fires too late" on the class the eager path exists for. See
        // `eager_perturb_mode`.
        //
        // NOT ON A DEADLINE STOP. `Stopped` is also what the walk returns when the
        // clock runs out (the `iter % 64` check in `primal`), and those deadlines
        // include SUB-deadlines handed to probes and heuristics mid-tree. Arming on
        // one would make the arm — and therefore the search — a function of how
        // fast the box happened to be that second. Arming on the budget/cycling
        // exits keeps it a function of the model: those are iteration counts.
        if !warm_started && !eager && deadline.is_none_or(|d| std::time::Instant::now() < d) {
            lp.cold_stalled.set(true);
        }
        // The eager path already ran the whole walk on a perturbed box; the
        // lazy retry below would perturb a SECOND time and pay the same failed
        // grind again. Measured on air05 node fallbacks: the retry re-ground
        // 27k-200k iterations after a 200k `Stopped`, for no verdict change,
        // ever. One perturbed attempt is the eager path's whole budget.
        if eager {
            return SimplexStatus::Stopped;
        }

        // STOPPED MEANS DEGENERACY. Perturb the box and try once more.
        //
        // `Stopped` here is not "this LP is hard", it is "phase I is going round in circles". On
        // air03 it is measured: 199,950 consecutive pivots with the total infeasibility frozen,
        // 133,512 of them ZERO-LENGTH, Bland's rule already engaged and helpless — because
        // Bland's anti-cycling argument assumes a fixed cost vector and phase I's is rebuilt every
        // iteration from whichever basics are currently violating a bound.
        //
        // Degenerate ties are ties between bounds that happen to coincide. Nudge the bounds apart
        // by amounts far below any tolerance and the ties stop being ties, the steps stop being
        // zero, and the phase moves. Then put the true bounds back and polish: the perturbed
        // optimum is a warm basis a few pivots from the real one.
        //
        // This runs ONLY on the path that already fails, so it cannot cost anything that works.
        // And it cannot lie: the true bounds are restored before `primal_feasible` is consulted,
        // and that check — against the real box — is still what licenses `Optimal`.
        // ITERATION LEDGER: from here to the end of `run` is RECOVERY — the
        // whole walk above already ran and came back `Stopped`, so the perturbed
        // re-walk and the polish that follows it are re-work by definition.
        let _ledger_recover = PhaseScope::new_forced(PH_RECOVERY);
        ledger_note_solve();
        let (save_lo, save_up) = (self.lo.clone(), self.up.clone());
        self.perturb_box(lp);
        let perturbed = self.rounds(lp, deadline);
        self.lo.copy_from_slice(&save_lo);
        self.up.copy_from_slice(&save_up);
        // A memory decline must not be laundered into the `Stopped` verdict the
        // `!= Optimal` line below would return: report the honest reason.
        if self.oom {
            return SimplexStatus::OutOfMemory;
        }
        if perturbed != SimplexStatus::Optimal {
            return SimplexStatus::Stopped;
        }

        // Back to the true box, from the perturbed basis.
        refac_reason(5);
        self.refactorize(lp);
        if self.oom {
            return SimplexStatus::OutOfMemory;
        }
        self.recompute_xb(lp);
        let polished = self.rounds(lp, deadline);
        if trace_enabled() {
            eprintln!("--trace perturbed retry -> {polished:?}");
        }
        polished
    }

    /// Phase I, phase II, and the drift check — up to four times.
    fn rounds(&mut self, lp: &FloatLp, deadline: Option<std::time::Instant>) -> SimplexStatus {
        // If a prior phase of this solve already declined on memory (e.g. a warm
        // dual or cold-dual fallback), do not start a primal walk on the dropped
        // inverse — report it. (Dead branch on every shipping instance.)
        if self.oom {
            return SimplexStatus::OutOfMemory;
        }
        // ITERATION LEDGER: rounds past the first are pure RE-WORK — a round is
        // only ever reached because the drift check rejected the previous one's
        // answer, so every iteration in it re-walks an LP already walked. Held
        // for the whole tail of the loop (not per round) so the scope is entered
        // at most once. (`collection_is_never_read` reads the `Option` as a
        // container; it is an RAII guard whose whole purpose is its lifetime.)
        #[allow(clippy::collection_is_never_read)]
        let mut _ledger_retry: Option<PhaseScope> = None;
        for round in 0..4 {
            if round == 1 {
                _ledger_retry = PhaseScope::new_forced(PH_RECOVERY);
                ledger_note_solve();
            }
            // Refactorize only when there is reason to. A rebuild is O(m · nnz) —
            // on a dense 60x45 that is the dominant per-node cost, and doing it
            // unconditionally between every phase was paying it three times a node
            // to fix drift that had not happened yet. Round 0 trusts the eta-file
            // it was handed (fresh from the crash basis, or from `warm_start`'s own
            // rebuild); a later round is only ever reached BECAUSE drift was
            // detected, and that is exactly when a rebuild earns its keep.
            if round > 0 {
                refac_reason(6);
                self.refactorize(lp);
                if self.oom {
                    return SimplexStatus::OutOfMemory;
                }
            }
            self.recompute_xb(lp);
            match self.loop_phase(lp, true, deadline) {
                SimplexStatus::Optimal => {}
                other => return other,
            }
            self.recompute_xb(lp);
            let status = self.loop_phase(lp, false, deadline);
            if status != SimplexStatus::Optimal {
                return status;
            }
            self.recompute_xb(lp);
            if self.primal_feasible(lp) {
                return SimplexStatus::Optimal;
            }
        }
        SimplexStatus::Stopped
    }

    /// Widen every finite bound by a hair, so that coincident bounds stop coinciding.
    ///
    /// The shifts are DETERMINISTIC (hashed off the column index): the same LP must solve the
    /// same way twice, or a branch-and-bound that re-solves a node gets a different answer than
    /// the one it recorded. They are outward only, so the perturbed box CONTAINS the true one and
    /// a feasible LP stays feasible.
    fn perturb_box(&mut self, lp: &FloatLp) {
        let pert = PERTURB;
        for j in 0..self.cols {
            // A hashed unit in [0.5, 1.5), so no two columns move by the same amount.
            let h = (j as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15);
            let u = 0.5 + ((h >> 40) as f64) / f64::from(1u32 << 24);
            // Frame image of `1 + min(|bound|, 1e6)`: the bound term already
            // carries the column's frame; the unit floor and the cap must too,
            // or a 2^-24-scaled column gets a nudge 10^5× its tolerance.
            let bm = lp.bmul(j);
            let scale = bm + self.lo[j].abs().max(self.up[j].abs()).min(1e6 * bm);
            let d = pert * scale * u;
            if self.lo[j].is_finite() {
                self.lo[j] -= d;
            }
            if self.up[j].is_finite() {
                self.up[j] += d;
            }
        }
    }

    /// Stats shim over the pivot loop, and the ITERATION LEDGER's primal hook.
    ///
    /// When `--lp-stats` is set it prints one `LPSTAT` line per phase —
    /// iteration count, degenerate-step and bound-flip counts, objective-moving
    /// iterations, wall. Counters are relaxed atomics bumped inside the loop
    /// either way (same cost class as `PRIMAL_ITERS`, which the loop already
    /// bumps); the prints never touch the float path.
    ///
    /// When `--iter-ledger` is set it also charges this phase's primal
    /// iterations to the (solve-phase, phase-I/II) ledger cell. Both hooks are
    /// per-CALL, never per-iteration.
    fn loop_phase(
        &mut self,
        lp: &FloatLp,
        phase1: bool,
        deadline: Option<std::time::Instant>,
    ) -> SimplexStatus {
        // ITERATION LEDGER: `loop_phase_inner`'s pivot loop owns the ONLY
        // `stats::PRIMAL_ITERS` bump site, and this shim is the only door into
        // it, so charging the delta here attributes every primal iteration in
        // the process to a (phase, phase-I/II) cell. One flag read + two relaxed
        // loads per PHASE, nothing per iteration.
        let led = iter_ledger_enabled().then(|| stats::get(&stats::PRIMAL_ITERS));
        let status = self.loop_phase_stats(lp, phase1, deadline);
        if let Some(before) = led {
            let spent = stats::get(&stats::PRIMAL_ITERS).wrapping_sub(before);
            let bucket = if phase1 { &PHASE_P1 } else { &PHASE_P2 };
            bucket[ledger_phase()].fetch_add(spent, std::sync::atomic::Ordering::Relaxed);
        }
        status
    }

    /// The `--lp-stats` half of [`Self::loop_phase`]; see its note.
    fn loop_phase_stats(
        &mut self,
        lp: &FloatLp,
        phase1: bool,
        deadline: Option<std::time::Instant>,
    ) -> SimplexStatus {
        if !lp_stats_enabled() {
            return self.loop_phase_inner(lp, phase1, deadline);
        }
        let t = std::time::Instant::now();
        let (i0, d0, f0, m0) = (
            stats::get(&stats::PRIMAL_ITERS),
            stats::get(&stats::PRIMAL_DEGEN),
            stats::get(&stats::PRIMAL_FLIPS),
            stats::get(&stats::PRIMAL_MOVED),
        );
        let status = self.loop_phase_inner(lp, phase1, deadline);
        let iters = stats::get(&stats::PRIMAL_ITERS) - i0;
        if iters > 0 {
            eprintln!(
                "LPSTAT phase{} status={status:?} iters={iters} degen={} flips={} moved={} wall={:.3}s",
                if phase1 { 1 } else { 2 },
                stats::get(&stats::PRIMAL_DEGEN) - d0,
                stats::get(&stats::PRIMAL_FLIPS) - f0,
                stats::get(&stats::PRIMAL_MOVED) - m0,
                t.elapsed().as_secs_f64(),
            );
        }
        status
    }

    #[allow(clippy::too_many_lines)]
    fn loop_phase_inner(
        &mut self,
        lp: &FloatLp,
        phase1: bool,
        deadline: Option<std::time::Instant>,
    ) -> SimplexStatus {
        self.y_is_duals = false; // pricing rebuilds `y` under phase costs, then pivots
        let cost_tol = self.cost_tol(lp);
        let pivot_tol = self.pivot_tol();
        let feas_tol = self.feas_tol(lp);
        let mut bland = false;
        // PRICE BY THE SHAPE OF THE LP, not by whether it has stalled yet.
        //
        // Devex costs an extra BTRAN and a pass over every non-zero per iteration; it repays that
        // by taking fewer iterations. Whether the trade wins is decided by the shape: a WIDE LP
        // (far more columns than rows) is where degeneracy explodes the iteration count, and it is
        // exactly there that halving the iterations beats doubling their cost. On a square-ish LP
        // there is nothing to win and the overhead is pure loss -- measured, as the unconditional
        // rule it made 70 binaries 73% slower and left the 80-binary incumbent worse.
        //
        // Waiting for a stall does not work either: by the time 2,000 non-improving iterations
        // have gone by, the basis is deep inside the degenerate region and a fresh reference
        // framework started there does not recover it. air03 still ground into `MAX_ITERS`. It
        // needs Devex from the first iteration or not at all.
        //
        // The split is clean, and it is the four instances that stall: nw04 (36 rows, 87,482
        // columns), air03 (124 / 10,757), mod010 (146 / 2,655), air05 (426 / 7,195) -- against
        // every dense instance here, which sits near 1:1.
        let wide = lp.n >= DEVEX_WIDTH * lp.m.max(1);
        // `--devex` forces Devex from iteration 0 regardless of shape.
        // The corpus evidence and rejected gate are recorded in
        // `../DEVEX_MEASUREMENT.md`; mixed results keep this a caller-owned lever.
        // `--no-devex` independently disables the wide-shape default.
        let force_devex = crate::tune::caller_flag(crate::tune::Knob::Devex) == Some(true);
        // CHAIN-shape LPs (see `FloatLp::chain_shape`) need Devex from
        // iteration 0 exactly like wide ones — on their COLD walks: the k=546
        // diff-net root walks a massively degenerate phase 1 that Dantzig
        // never exits (Stopped at its 46s budget; the stall-triggered Devex
        // below starts too deep in the degenerate region to recover — the
        // same measurement as air03). Preorder alone or Devex alone both
        // leave it Stopped; together the root solves in ~3.7s. Warm repairs
        // keep Dantzig by default — see `chain_devex_mode` for the k=124
        // certification-loss measurement behind that split.
        let chain_devex = lp.chain_lp()
            && match chain_devex_mode() {
                0 => false,
                1 => true,
                _ => !self.warm_run,
            };
        let mut devex = (wide || force_devex || chain_devex) && !no_devex();
        let stalled_at = self.m.clamp(STALL_FLOOR, STALL_BEFORE_BLAND);
        let bland_after = stalled_at + BLAND_GRACE;
        let mut stall = 0usize;
        let (mut _degen, mut _flips) = (0usize, 0usize);
        let mut last_obj = f64::INFINITY;

        for iter in 0..MAX_ITERS {
            if !spend_iter() {
                return SimplexStatus::Stopped; // out of WORK, not out of time
            }
            // The chain DISTRESS PROBE (see `chain_probe_iters`): a bounded
            // walk on an armed LP that runs out of budget is handed back as
            // `Stopped` so the caller can promote and retry with the bundle
            // instead of grinding out its whole deadline slice first.
            if self.probe_iters_left == 0 {
                return SimplexStatus::Stopped;
            }
            self.probe_iters_left -= 1;
            stats::bump(&stats::PRIMAL_ITERS);
            stats::bump_solve();
            if iter % 64 == 0 {
                if let Some(d) = deadline {
                    if std::time::Instant::now() >= d {
                        return SimplexStatus::Stopped;
                    }
                }
            }
            let nnz_trigger = self.eta_nnz >= self.eta_nnz_cap && self.since_refactor >= 5;
            if self.since_refactor >= self.refactor_cadence(lp) || nnz_trigger {
                refac_reason(7);
                self.refactorize(lp);
                if self.oom {
                    return SimplexStatus::OutOfMemory;
                }
                self.recompute_xb(lp);
            } else if iter > 0 && iter % REFRESH_EVERY == 0 {
                self.recompute_xb(lp);
            }

            // Basic costs for pricing, and this phase's objective (for stall
            // detection) in the same sweep.
            //   Phase I: +1 above upper, -1 below lower — the gradient of total
            //            bound violation, which Phase I minimizes.
            //   Phase II: the column's own cost.
            let mut obj = 0.0f64;
            if phase1 {
                for i in 0..self.m {
                    let b = self.basis[i];
                    let v = self.xb[i];
                    // Per-column classification (a scaled-down row's genuine slack
                    // must not read as violation-or-degeneracy), ORIGINAL-unit sum
                    // (rows of different scale must weigh comparably in the metric
                    // and against the exit/progress thresholds).
                    let ft = feas_tol * lp.bmul(b);
                    // Gradient ±1 in the SOLVE frame. The ∓vmul(b) alternative
                    // (original-frame gradient) was built and MEASURED WORSE: on
                    // w5's 2^41 multiplier spread it re-injects the full dynamic
                    // range into the phase-1 costs — reduced costs blew past 1e19
                    // within 50 pivots. ±1 keeps the walk's costs conditioned;
                    // the METRIC below still sums in original units so the exit
                    // and progress tests measure the true infeasibility.
                    if v < self.lo[b] - ft {
                        self.cb[i] = -1.0;
                        obj += (self.lo[b] - v) * lp.vmul(b);
                    } else if v > self.up[b] + ft {
                        self.cb[i] = 1.0;
                        obj += (v - self.up[b]) * lp.vmul(b);
                    } else {
                        self.cb[i] = 0.0;
                    }
                }
                if obj <= feas_tol {
                    return SimplexStatus::Optimal; // feasible: Phase I done.
                }
            } else {
                for i in 0..self.m {
                    let b = self.basis[i];
                    self.cb[i] = self.pcost[b];
                    obj += self.pcost[b] * self.xb[i];
                }
            }

            // Progress is measured in ORIGINAL units both phases: phase 2's
            // `pcost·xb` is frame-invariant (c'ᵀx' = cᵀx), and phase 1's sum is
            // converted per-column below — so the threshold uses the original
            // magnitude. (With the scaled magnitude this test declared the
            // measured 80%-degenerate stall: genuine original-frame progress on
            // scaled-down rows never cleared a scaled-up threshold.)
            if obj < last_obj - 1e-9 * (1.0 + lp.scale) {
                last_obj = obj;
                stall = 0;
                bland = false;
                stats::bump(&stats::PRIMAL_MOVED);
            } else {
                stall += 1;
                // The ladder: Dantzig until it is demonstrably stuck, then DEVEX, and only if
                // that is stuck too, Bland — which always terminates and always crawls.
                if stall > stalled_at && !devex {
                    devex = true;
                    self.w.fill(1.0); // fresh reference framework
                }
                if stall > bland_after {
                    bland = true;
                }
                // Not converging: Bland had its grace and the objective has
                // still not moved — stop burning the caller's budget. (See
                // `STALL_ABORT_GRACE`; `Stopped` is the same safe answer
                // `MAX_ITERS` would eventually give, at a fraction of the
                // cost.) WIDE LPs only: that is where the measured monsters
                // live, and the square-ish corpus keeps its exact pivot walk.
                if wide && stall > bland_after + STALL_ABORT_GRACE {
                    return SimplexStatus::Stopped;
                }
            }

            self.y.copy_from_slice(&self.cb);
            self.btran();

            // Pricing. A column at its lower bound may enter increasing if its
            // reduced cost is negative; at its upper bound, decreasing if
            // positive; a free column may go either way.
            let mut entering: Option<(usize, f64)> = None;
            let mut best = 0.0f64;
            // BIG-LP PRICING ECONOMY. Full pricing walks every column's CSC dot —
            // O(total nnz) per iteration, ~13ms on the cifar100 w5 window
            // (26,831 structurals, 7.47M nnz) — and the cold walk there is
            // 24,399 iterations (measured to completion: Optimal at 1,739s).
            // Selection is ADVICE (any improving column is a valid pivot); the
            // OPTIMALITY claim is untouched in every mode below: `entering ==
            // None` is only ever reached off a candidate-free scan of EVERY
            // column, and the drift re-ask after it re-checks on a fresh
            // inverse. Bland mode always runs the full smallest-index scan
            // (termination argument). Small LPs keep the exact full sweep.
            // Two economies, chosen by env:
            // - CANDIDATE-LIST (default for big LPs; --full-pricing
            //   restores full): a MAJOR full pass harvests the top candidates
            //   into a pool; MINOR iterations re-price only the pool (~400×
            //   cheaper) until nothing in it improves, forcing the next major
            //   pass. Full-scan walk quality at partial-scan cost.
            // - SECTIONAL (AY_MILP_PARTIAL_PRICING=1): rotating windows;
            //   MEASURED SPLIT — w2 cold LP 9.1s→5.6s, but w5's walk collapses
            //   (moved 9,467→118) — kept as a lever, not a default.
            const PARTIAL_PRICE_MIN_COLS: usize = 8192;
            const PRICE_SECTION: usize = 2048;
            const MIN_SECTIONS_WITH_CANDIDATE: usize = 2;
            const PRICE_POOL_MAX: usize = 64;
            let big = self.cols >= PARTIAL_PRICE_MIN_COLS;
            let full_forced =
                crate::tune::caller_flag(crate::tune::Knob::FullPricing) == Some(true);
            let sectional = !bland && big && !full_forced && false; // B22: sectional pricing retired (measured-out).
                                                                    // Pool mode is ALSO measured-out as a default (w2 walk 5,831 →
                                                                    // 9,978 iterations; w5 walk collapses — phase-1's cb depends on the
                                                                    // violated SET, which shifts globally each pivot, so any cached
                                                                    // candidate list goes stale immediately). The shipping default for
                                                                    // big LPs is the SWEPT full pass below: byte-identical walk, one
                                                                    // sequential O(nnz) sweep instead of scattered per-column dots.
            let pool_mode = !bland && big && !full_forced && !sectional && false; // B7: the AY_MILP_POOL_PRICING opt-in is deleted (never shipped on)

            // MINOR iteration: re-price the pool only. A pool column that went
            // basic/fixed or stopped improving simply doesn't enter; if none
            // does, fall through to the MAJOR full pass below.
            if pool_mode && !self.price_pool.is_empty() {
                for k in 0..self.price_pool.len() {
                    let jj = self.price_pool[k] as usize;
                    if self.basic_row[jj].is_some() || self.lo[jj] == self.up[jj] {
                        continue;
                    }
                    let rc = self.reduced_cost(lp, jj, phase1);
                    let ct = if phase1 {
                        cost_tol
                    } else {
                        cost_tol * lp.vmul(jj)
                    };
                    let dir = match self.at[jj] {
                        NbBound::Lower if rc < -ct => 1.0,
                        NbBound::Upper if rc > ct => -1.0,
                        NbBound::Zero if rc < -ct => 1.0,
                        NbBound::Zero if rc > ct => -1.0,
                        _ => continue,
                    };
                    let score = if devex {
                        rc * rc / self.w[jj].max(1e-12)
                    } else {
                        rc.abs()
                    };
                    if score > best {
                        best = score;
                        entering = Some((jj, dir));
                    }
                }
            }

            // MAJOR pass (pool mode with an exhausted pool) or the sectional /
            // full sweep. In pool mode this full pass also rebuilds the pool
            // with the top candidates by score.
            if entering.is_none() {
                // ONE row-major sweep replaces every column's scattered CSC dot:
                // `fill_yta` computes yᵀA sequentially (documented bit-identical
                // to the per-column gathers), so rc reads become O(1) and the
                // full pass costs one cache-friendly O(nnz) instead of a
                // scattered one. Bland keeps per-column dots (it exits early).
                let swept = !bland && !sectional;
                if swept {
                    self.fill_yta(lp);
                }
                let mut pool_new: Vec<(f64, u32)> = Vec::new();
                let mut sections_with_candidate = 0usize;
                let mut scanned = 0usize;
                let mut j = if sectional {
                    self.price_cursor % self.cols
                } else {
                    0
                };
                while scanned < self.cols {
                    let jj = if j >= self.cols { j - self.cols } else { j };
                    j += 1;
                    scanned += 1;
                    let at_section_end = sectional && scanned.is_multiple_of(PRICE_SECTION);
                    let mut consider = true;
                    if self.basic_row[jj].is_some() || self.lo[jj] == self.up[jj] {
                        consider = false;
                    }
                    if consider {
                        let rc = if swept {
                            let c = if phase1 { 0.0 } else { self.pcost[jj] };
                            if jj < lp.n {
                                c - self.arow[jj]
                            } else {
                                c + self.y[jj - lp.n]
                            }
                        } else {
                            self.reduced_cost(lp, jj, phase1)
                        };
                        // Phase-2 reduced costs carry the frame d'_j = d_j·vmul(j);
                        // phase 1's ±1 gradient keeps its reduced costs in the solve
                        // frame, so its entry test stays unframed (selection is
                        // advice — the per-column CLASSIFICATION is correctness).
                        let ct = if phase1 {
                            cost_tol
                        } else {
                            cost_tol * lp.vmul(jj)
                        };
                        let dir = match self.at[jj] {
                            NbBound::Lower if rc < -ct => 1.0,
                            NbBound::Upper if rc > ct => -1.0,
                            NbBound::Zero if rc < -ct => 1.0,
                            NbBound::Zero if rc > ct => -1.0,
                            _ => 0.0,
                        };
                        if dir != 0.0 {
                            if bland {
                                entering = Some((jj, dir));
                                break;
                            }
                            // Devex scores `rc^2 / w`: how far the column will MOVE,
                            // not how steep it looks. On a degenerate LP the steepest
                            // column is usually blocked at zero, which is precisely
                            // why Dantzig re-picks it forever.
                            let score = if devex {
                                rc * rc / self.w[jj].max(1e-12)
                            } else {
                                rc.abs()
                            };
                            if score > best {
                                best = score;
                                entering = Some((jj, dir));
                            }
                            if pool_mode {
                                if pool_new.len() < PRICE_POOL_MAX {
                                    pool_new.push((score, jj as u32));
                                } else {
                                    // Replace the current minimum if this beats it.
                                    let mut mi = 0;
                                    for (i, &(s, _)) in pool_new.iter().enumerate() {
                                        if s < pool_new[mi].0 {
                                            let _ = s;
                                            mi = i;
                                        }
                                    }
                                    if score > pool_new[mi].0 {
                                        pool_new[mi] = (score, jj as u32);
                                    }
                                }
                            }
                        }
                    }
                    if at_section_end && entering.is_some() {
                        sections_with_candidate += 1;
                        if sections_with_candidate >= MIN_SECTIONS_WITH_CANDIDATE {
                            break;
                        }
                    }
                }
                if sectional {
                    // Resume the next sweep where this one stopped looking.
                    self.price_cursor = (self.price_cursor + scanned) % self.cols;
                }
                if pool_mode {
                    self.price_pool.clear();
                    self.price_pool.extend(pool_new.iter().map(|&(_, j)| j));
                }
            }

            let Some((col, dir)) = entering else {
                // NOTHING PRICES IN -- BUT ASK AGAIN ON A BASIS THAT IS NOT DRIFTING.
                //
                // Every reduced cost above came through a BTRAN against the product-form inverse,
                // and after tens of eta updates that inverse is approximate. An approximate `y`
                // gives approximate reduced costs, and a reduced cost that has drifted to just
                // inside `cost_tol` reports a column as priced out when it is not. The loop then
                // declares an optimum it has not reached.
                //
                // That is not a hypothetical: it made the LP's ANSWER depend on the refactorisation
                // cadence. blend2's root bound came back 214.352831 rebuilding every 50 pivots and
                // 211.476117 every 200 -- two different "Optimal" verdicts, 1.3% apart, for one LP.
                // A weaker root bound is sound (the rim still adjudicates) and it costs proofs.
                //
                // So refactorise and ask once more. This terminates: `refactorize` zeroes
                // `since_refactor`, so the re-ask happens at most once per clean basis, and if a
                // column does price in on the fresh inverse we pivot and make real progress.
                // ...but only when the inverse has actually had time to drift. A warm node re-solve
                // is SEVEN pivots long on rout, and seven eta updates do not move a reduced cost
                // anywhere near `cost_tol`; refactorising to re-ask there buys nothing and costs a
                // factorisation on every one of 24,000 node solves -- enough, measured, to lose
                // rout's incumbent outright. Drift needs accumulation, so require some.
                // (Trigger is engine-aware — see `verify_after_for` / Lever A1.)
                if self.since_refactor >= self.verify_after_for(lp) {
                    refac_reason(8);
                    self.refactorize(lp);
                    if self.oom {
                        return SimplexStatus::OutOfMemory;
                    }
                    self.recompute_xb(lp);
                    continue;
                }
                // In Phase II that is the optimum. In Phase I it means the infeasibility (still
                // > feas_tol, or we would have exited above) cannot be reduced — the LP is
                // primal infeasible.
                if phase1 {
                    // Nothing prices in while infeasibility remains: `y` is a
                    // candidate Farkas ray. Keep it — the caller can turn it into
                    // an exact proof for the price of one pass over the non-zeros,
                    // instead of an exact LP.
                    self.farkas = Some(self.y.clone());
                    return SimplexStatus::PrimalInfeasible;
                }
                return SimplexStatus::Optimal;
            };

            self.ftran(lp, col);

            // Bounded-variable ratio test. The entering column may travel at most
            // its own span (a bound flip) before some basic variable hits a bound.
            let span = self.up[col] - self.lo[col]; // +inf if either side is free
            let mut min_t = if span.is_nan() { f64::INFINITY } else { span };
            let mut leave_row: Option<usize> = None;
            let mut leave_to_upper = false;

            // A RELATIVE pivot floor for candidacy, on top of the absolute one.
            //
            // An entry of `alpha` that is dwarfed by the column's largest entry is
            // indistinguishable from accumulated FTRAN round-off, and PIVOTING ON
            // ROUND-OFF IS HOW THE BASIS GOES SINGULAR. Measured on air05's root LP
            // (set partitioning, thousands of duplicate 0/1 columns): entering a
            // duplicate of a basic column has true alpha = e_r exactly, the eta
            // file's drift dresses that with ~1e-8 noise on other rows, the
            // absolute-only test (1e-9) admits a noise row — the degenerate tie
            // then PREFERS it (fixed-first eviction) — and the resulting basis is
            // EXACTLY singular (dense complete-pivoting check: rank 425/426,
            // remaining mass 4e-16). Every subsequent refactorization then rightly
            // failed: 13,434 failed rebuilds in 60s against 180 successes.
            //
            // 1e-6 relative is far above any drift this engine accumulates in a
            // 50-pivot refactor cycle and far below any honest pivot ratio on the
            // corpus (which is small-integer data); a real entry excluded here can
            // still block at the NEXT iteration after a rebuild sharpens it, so
            // the cost of a false exclusion is one extra pivot, not an answer.
            //
            // WIDE LPs ONLY (the Devex gate again): the duplicate-column noise
            // pivot is a wide/set-partitioning phenomenon, and on square-ish
            // models the floor is not protection, it is just a different pivot
            // stream — measured: applied unconditionally it took blend2's proof
            // from 1.89s to 2.55s (reproducibly, three runs each way). The wide
            // members it does apply to (air03, air05, mod010, khb05250, mas76)
            // all hold their gate values with it on.
            let piv_floor = if wide {
                let mut amax = 0.0f64;
                for &i in &self.nz {
                    let v = self.alpha[i].abs();
                    if v > amax {
                        amax = v;
                    }
                }
                pivot_tol.max(REL_RATIO_PIVOT * amax)
            } else {
                pivot_tol
            };

            for &i in &self.nz {
                let a = self.alpha[i];
                if a.abs() <= piv_floor {
                    continue;
                }
                let bvar = self.basis[i];
                let cur = self.xb[i];
                let slope = -a * dir; // d(xb_i)/dt
                                      // WHICH BOUND DOES THIS BASIC VARIABLE BLOCK THE STEP AT?
                                      //
                                      // A variable that is already OUTSIDE a bound and moving FURTHER OUT has no bound
                                      // left to hit, and must not block at all. This is where phase I was dying. It gave
                                      // such a variable its violated bound as the target anyway -- so
                                      // `t = (lo - cur) / slope` came out NEGATIVE, `max(0.0)` clamped it to zero, and
                                      // the step was blocked at zero by a variable that was never in the way.
                                      //
                                      // air03 starts with all 124 equality logicals infeasible, so on essentially every
                                      // iteration SOME infeasible basic is drifting the wrong way and pinning the step
                                      // to zero. Measured: 133,512 of 200,000 pivots zero-length, the total infeasibility
                                      // frozen for 199,950 consecutive iterations. It was not degeneracy, and no pricing
                                      // rule, ratio-test refinement or bound perturbation could have fixed it -- all
                                      // three were tried against it and all three failed, because the step was being
                                      // blocked by a constraint that does not exist.
                let (lo_b, up_b) = (self.lo[bvar], self.up[bvar]);
                let ft = feas_tol * lp.bmul(bvar);
                let below = phase1 && cur < lo_b - ft;
                let above = phase1 && cur > up_b + ft;
                let (target, want_upper) = if slope > pivot_tol {
                    if below {
                        // Rising back toward feasibility: it stops at the bound it is under, and
                        // stopping there is what keeps the infeasibility monotone.
                        (lo_b, false)
                    } else if above {
                        continue; // already above and still rising: nothing to hit
                    } else {
                        (up_b, true)
                    }
                } else if slope < -pivot_tol {
                    if above {
                        (up_b, true)
                    } else if below {
                        continue; // already below and still falling: nothing to hit
                    } else {
                        (lo_b, false)
                    }
                } else {
                    continue;
                };
                if !target.is_finite() {
                    continue;
                }
                let t = ((target - cur) / slope).max(0.0);
                // Strictly-smaller wins. ON A TIE, EVICT A FIXED BASIC VARIABLE FIRST.
                //
                // This is the whole of the phase-I failure on air03/air05/mod010/nw04. Those are
                // equality-row models, and an equality row's LOGICAL is fixed: `lo == up`. The
                // crash basis is all-logical, so phase I starts with every basic variable fixed.
                // The moment one reaches its value it is sitting exactly on both its bounds, so
                // EVERY later pivot that touches it has ratio t = 0 and it blocks — every pivot
                // after that is degenerate.
                //
                // The tie-break decided who leaves by smallest basis index, and a structural
                // column's index is below a logical's. So it evicted structurals and left the
                // fixed logicals basic, forever: air03 ran 199,906 consecutive pivots with the
                // infeasibility frozen at 66.0.
                //
                // A fixed variable driven out of the basis never comes back — pricing above will
                // not enter a column that cannot move — so preferring it is monotone progress,
                // and there are only `m` of them. Among equally-fixed candidates Bland's
                // smallest-index rule still decides, so its termination argument is untouched.
                let fixed_here = self.lo[self.basis[i]] == self.up[self.basis[i]];
                let better = match leave_row {
                    None => t < min_t || (t <= min_t && min_t.is_finite()),
                    Some(prev) => {
                        if t < min_t {
                            true
                        } else if t == min_t {
                            let fixed_prev = self.lo[self.basis[prev]] == self.up[self.basis[prev]];
                            match (fixed_here, fixed_prev) {
                                (true, false) => true,
                                (false, true) => false,
                                _ => self.basis[i] < self.basis[prev],
                            }
                        } else {
                            false
                        }
                    }
                };
                if better && t <= min_t {
                    min_t = t;
                    leave_row = Some(i);
                    leave_to_upper = want_upper;
                }
            }

            if !min_t.is_finite() {
                if phase1 && trace_enabled() {
                    eprintln!("--trace !! simplex Stopped: phase-I ratio test unbounded on col {col} (iter {iter})");
                }
                return if phase1 {
                    SimplexStatus::Stopped
                } else {
                    SimplexStatus::Unbounded
                };
            }

            if min_t == 0.0 {
                _degen += 1;
                stats::bump(&stats::PRIMAL_DEGEN);
            }
            if leave_row.is_none() {
                _flips += 1;
                stats::bump(&stats::PRIMAL_FLIPS);
            }
            let step = dir * min_t;
            // STEP TRACE (diagnostic): --step-trace=N prints the first N
            // pivots' economics — entering column and its frame, the step in both
            // frames, and who blocked — the instrument for scaled-frame stalls.
            {
                use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
                static STEP_TRACE_LEFT: AtomicU64 = AtomicU64::new(u64::MAX);
                if STEP_TRACE_LEFT.load(Relaxed) == u64::MAX {
                    let n = crate::tune::count_opt(crate::tune::Knob::StepTraceN)
                        .map(|v| v as u64)
                        .unwrap_or(0);
                    STEP_TRACE_LEFT.store(n, Relaxed);
                }
                let left = STEP_TRACE_LEFT.load(Relaxed);
                if left > 0 && left != u64::MAX {
                    STEP_TRACE_LEFT.store(left - 1, Relaxed);
                    let (lv, lb) = match leave_row {
                        Some(p) => (self.basis[p] as i64, lp.bmul(self.basis[p])),
                        None => (-1, 0.0),
                    };
                    eprintln!(
                        "STEP iter={iter} p1={phase1} col={col} bmul_c={:.2e} rc={:.3e} t={min_t:.3e} t_orig={:.3e} leave={lv} bmul_l={lb:.2e} degen={}",
                        lp.bmul(col),
                        self.reduced_cost(lp, col, phase1),
                        min_t * lp.vmul(col),
                        min_t == 0.0
                    );
                }
            }
            if step != 0.0 {
                for &i in &self.nz {
                    if self.alpha[i] != 0.0 {
                        self.xb[i] -= self.alpha[i] * step;
                    }
                }
            }

            match leave_row {
                None => {
                    // Bound flip: the entering column swaps sides, basis unchanged.
                    self.at[col] = match self.at[col] {
                        NbBound::Lower => NbBound::Upper,
                        NbBound::Upper => NbBound::Lower,
                        NbBound::Zero => NbBound::Zero,
                    };
                }
                Some(p) => {
                    let piv = self.alpha[p];
                    // The LU update is fallible where the eta append was not; it
                    // runs at the accept decision, before any basis bookkeeping,
                    // and a rejection degrades to the same bound flip as a
                    // vanishing pivot (state untouched by the failed attempt).
                    let lu_ok = match (piv.is_finite() && piv.abs() > pivot_tol, self.lu.as_mut()) {
                        (false, _) => false,
                        (true, None) => true,
                        (true, Some(cache)) => {
                            // Same as the dual arm: `self.nz` is the FTRAN's
                            // support, so the spike build gets its pattern for
                            // free. See `LuEngine::update_nz`.
                            let ok = cache.eng.update_nz(p, &self.alpha, &self.nz).is_ok();
                            if ok {
                                cache.rep_basis[p] = col;
                                self.eta_nnz = cache.eng.nnz();
                                // As in the dual arm: an LU pivot desyncs the eta file from
                                // the basis; the cross-solve reuse must not adopt the pair.
                                self.factor_live = false;
                            }
                            ok
                        }
                    };
                    if !lu_ok {
                        // Refuse to build an eta from a vanishing pivot; treat it
                        // as a bound flip so the bookkeeping stays consistent.
                        self.at[col] = match self.at[col] {
                            NbBound::Lower => NbBound::Upper,
                            NbBound::Upper => NbBound::Lower,
                            NbBound::Zero => NbBound::Zero,
                        };
                    } else {
                        let leaving = self.basis[p];
                        let entering_value = self.nb_value(lp, col) + step;
                        let inv = 1.0 / piv;
                        if devex {
                            self.update_devex(lp, col, p, piv);
                        }
                        if self.lu.is_none() {
                            let before = self.etas.entries();
                            for &i in &self.nz {
                                if i != p && self.alpha[i] != 0.0 {
                                    self.etas.push_entry(i, -self.alpha[i] * inv);
                                }
                            }
                            self.eta_nnz += self.etas.entries() - before;
                            self.etas.finish_eta(p, inv);
                        }
                        self.since_refactor += 1;
                        self.basic_row[leaving] = None;
                        self.at[leaving] = if leave_to_upper {
                            NbBound::Upper
                        } else {
                            NbBound::Lower
                        };
                        self.basis[p] = col;
                        self.basic_row[col] = Some(p);
                        self.xb[p] = entering_value;
                    }
                }
            }

            for &i in &self.nz {
                self.alpha[i] = 0.0;
            }
        }
        if trace_enabled() {
            eprintln!(
                "--trace !! MAX_ITERS phase{} stall={stall} bland={bland} devex={devex} \
                 obj={last_obj:.4e} degenerate={_degen} boundflips={_flips} fixed_basics={}",
                u8::from(!phase1) + 1,
                (0..self.m)
                    .filter(|&i| self.lo[self.basis[i]] == self.up[self.basis[i]])
                    .count()
            );
        }
        SimplexStatus::Stopped
    }
}

#[cfg(test)]
mod ft_adoption_census_tests {
    use super::*;

    /// `charge_ft_adoption_exclusion` is the single call made by each
    /// refactorization that lands above the adoption ceiling. Two calls here
    /// therefore model two excluded refactorizations without constructing and
    /// factoring an 8,192-row LP: one top-level model solve must still add one
    /// solve and one copy of its first excluded LP's row count.
    #[test]
    fn multiple_refactorizations_charge_one_top_level_solve() {
        let _guard = crate::sepstat::adoption_test_guard();
        let mut model = Model::new();
        let x = model.add_col(0.0, 1.0);
        model.add_row(0.0, 1.0, &[(x, 1.0)]);
        model.set_ft_adoption_solve_latch(crate::sepstat::FtAdoptionSolveLatch::new());
        let lp = FloatLp::from_model(&model, &[], Sense::Minimize).expect("tiny census LP");

        let before = crate::sepstat::adoption_forgone();
        assert!(lp.charge_ft_adoption_exclusion());
        assert!(!lp.charge_ft_adoption_exclusion());
        let after = crate::sepstat::adoption_forgone();

        assert_eq!(after.0 - before.0, 1, "one solve was charged twice");
        assert_eq!(
            after.1 - before.1,
            lp.m as u64,
            "the first excluded LP's rows were charged more than once"
        );
    }
}

#[cfg(test)]
mod chain_distress_probe_tests {
    use super::resolve_chain_distress_probe_iters;

    #[test]
    fn typed_chain_probe_budget_preempts_historical_policy() {
        assert_eq!(
            resolve_chain_distress_probe_iters(Some(321), || {
                panic!("typed override must not consult the historical fallback")
            }),
            321
        );
    }

    #[test]
    fn typed_zero_disables_chain_probe_without_consulting_fallback() {
        assert_eq!(
            resolve_chain_distress_probe_iters(Some(0), || {
                panic!("typed zero must not consult the historical fallback")
            }),
            0
        );
    }

    #[test]
    fn absent_chain_probe_override_preserves_historical_policy() {
        assert_eq!(resolve_chain_distress_probe_iters(None, || 20_000), 20_000);
    }
}

#[cfg(test)]
mod warm_solve_mode_tests {
    use super::*;
    use num_rational::BigRational;

    fn independent_warm_repairs(rows: usize) -> (Model, FloatLp, Vec<Col>, Vec<Col>) {
        let mut model = Model::new();
        let mut fixed = Vec::with_capacity(rows);
        let mut objective_cols = Vec::with_capacity(rows);
        for _ in 0..rows {
            let x = model.add_col(0.0, 1.0);
            let z = model.add_col(0.0, 2.0);
            model.add_row(0.0, f64::INFINITY, &[(z, 1.0), (x, -1.0)]);
            fixed.push(x);
            objective_cols.push(z);
        }
        let objective: Vec<_> = objective_cols.iter().map(|col| (col.0, 1.0)).collect();
        let lp = FloatLp::from_model(&model, &objective, Sense::Minimize)
            .expect("independent repair LP");
        (model, lp, fixed, objective_cols)
    }

    fn fixed_box(lp: &FloatLp, fixed: &[Col]) -> (Vec<f64>, Vec<f64>) {
        prefix_box(lp, fixed, fixed.len())
    }

    fn prefix_box(lp: &FloatLp, fixed: &[Col], fixed_count: usize) -> (Vec<f64>, Vec<f64>) {
        let mut lower = lp.lower.clone();
        let mut upper = lp.upper.clone();
        for col in &fixed[..fixed_count] {
            lower[col.index()] = 1.0;
            upper[col.index()] = 1.0;
        }
        (lower, upper)
    }

    fn changed_basis_slots(before: &Candidate, after: &Candidate) -> usize {
        before
            .basis
            .iter()
            .zip(&after.basis)
            .filter(|(left, right)| left != right)
            .count()
    }

    fn assert_same_candidate(left: &Candidate, right: &Candidate) {
        assert_eq!(left.status, right.status);
        assert_eq!(left.basis, right.basis);
        assert_eq!(left.at, right.at);
        assert_eq!(
            left.values
                .iter()
                .map(|value| value.to_bits())
                .collect::<Vec<_>>(),
            right
                .values
                .iter()
                .map(|value| value.to_bits())
                .collect::<Vec<_>>()
        );
        assert_eq!(
            left.duals
                .iter()
                .map(|value| value.to_bits())
                .collect::<Vec<_>>(),
            right
                .duals
                .iter()
                .map(|value| value.to_bits())
                .collect::<Vec<_>>()
        );
        assert_eq!(
            left.farkas
                .iter()
                .map(|value| value.to_bits())
                .collect::<Vec<_>>(),
            right
                .farkas
                .iter()
                .map(|value| value.to_bits())
                .collect::<Vec<_>>()
        );
        assert_eq!(left.farkas_verified, right.farkas_verified);
    }

    #[test]
    fn capped_primal_advice_advances_and_reuses_a_stopped_basis() {
        let (_, lp, fixed, objective_cols) = independent_warm_repairs(8);
        let root = lp.solve(None);
        assert_eq!(root.status, SimplexStatus::Optimal);
        let (lower, upper) = fixed_box(&lp, &fixed);

        let first = {
            let _cap = IterCap::set(2);
            lp.solve_bounded_with_mode(
                &lower,
                &upper,
                Some((&root.basis, &root.at)),
                WarmSolveMode::PrimalAdvice,
                None,
            )
        };
        assert_eq!(first.status, SimplexStatus::Stopped);
        let first_progress = changed_basis_slots(&root, &first);
        assert!(
            first_progress > 0,
            "the capped prefix must retain completed primal pivots"
        );
        assert_eq!(
            lp.dual_adapt.get().0,
            0,
            "PrimalAdvice must not enter or score the warm-dual lane"
        );

        let second = {
            let _cap = IterCap::set(2);
            lp.solve_bounded_with_mode(
                &lower,
                &upper,
                Some((&first.basis, &first.at)),
                WarmSolveMode::PrimalAdvice,
                None,
            )
        };
        assert_eq!(second.status, SimplexStatus::Stopped);
        assert!(
            changed_basis_slots(&root, &second) > first_progress,
            "the next cap must continue from, not replay, the first stopped basis"
        );

        let completed = lp.solve_bounded(&lower, &upper, Some((&second.basis, &second.at)), None);
        assert_eq!(completed.status, SimplexStatus::Optimal);
        for col in objective_cols {
            assert!(
                completed.values[col.index()] >= 1.0 - 1e-9,
                "the proof-bearing normal solve must validate the carried basis"
            );
        }
    }

    #[test]
    fn stopped_nested_prefix_continues_to_exact_verified_optimum_without_warm_dual() {
        let (model, lp, fixed, _) = independent_warm_repairs(8);
        let root = lp.solve(None);
        assert_eq!(root.status, SimplexStatus::Optimal);

        let (prefix_lower, prefix_upper) = prefix_box(&lp, &fixed, 4);
        let prefix = {
            let _cap = IterCap::set(2);
            lp.solve_bounded_with_mode(
                &prefix_lower,
                &prefix_upper,
                Some((&root.basis, &root.at)),
                WarmSolveMode::PrimalAdvice,
                None,
            )
        };
        assert_eq!(prefix.status, SimplexStatus::Stopped);

        let (lower, upper) = fixed_box(&lp, &fixed);
        let completed = lp.solve_bounded_with_mode(
            &lower,
            &upper,
            Some((&prefix.basis, &prefix.at)),
            WarmSolveMode::PrimalProofContinuation,
            None,
        );
        assert_eq!(completed.status, SimplexStatus::Optimal);
        assert_eq!(
            lp.dual_adapt.get().0,
            0,
            "advice plus proof continuation must make zero warm-dual entries"
        );

        let mut leaf_model = model;
        for col in fixed {
            leaf_model.fix_col(col, 1.0);
        }
        let certified =
            crate::certify::certify_bounded_by(&leaf_model, &lp, &completed, &lower, &upper, None)
                .expect("the continuation basis must be exactly optimal");
        assert_eq!(
            certified.value,
            BigRational::from_integer(8.into()),
            "all eight epigraph variables are exactly one"
        );
        certified
            .cert
            .verify(&leaf_model)
            .expect("the exact optimality certificate must independently verify");
    }

    #[test]
    fn stopped_nested_prefix_continues_to_exact_verified_infeasibility_without_warm_dual() {
        let (mut model, _, fixed, objective_cols) = independent_warm_repairs(8);
        let assignment_terms: Vec<_> = fixed.iter().map(|col| (*col, 1.0)).collect();
        model.add_row(f64::NEG_INFINITY, 7.0, &assignment_terms);
        let objective: Vec<_> = objective_cols.iter().map(|col| (col.0, 1.0)).collect();
        let lp =
            FloatLp::from_model(&model, &objective, Sense::Minimize).expect("infeasible leaf LP");
        let root = lp.solve(None);
        assert_eq!(root.status, SimplexStatus::Optimal);

        let (prefix_lower, prefix_upper) = prefix_box(&lp, &fixed, 4);
        let prefix = {
            let _cap = IterCap::set(2);
            lp.solve_bounded_with_mode(
                &prefix_lower,
                &prefix_upper,
                Some((&root.basis, &root.at)),
                WarmSolveMode::PrimalAdvice,
                None,
            )
        };
        assert_eq!(prefix.status, SimplexStatus::Stopped);

        let (lower, upper) = fixed_box(&lp, &fixed);
        let completed = lp.solve_bounded_with_mode(
            &lower,
            &upper,
            Some((&prefix.basis, &prefix.at)),
            WarmSolveMode::PrimalProofContinuation,
            None,
        );
        assert_eq!(completed.status, SimplexStatus::PrimalInfeasible);
        assert_eq!(
            lp.dual_adapt.get().0,
            0,
            "infeasible proof continuation must also skip warm dual"
        );

        let mut leaf_model = model;
        for col in fixed {
            leaf_model.fix_col(col, 1.0);
        }
        let farkas = crate::tree_cert::exact_farkas_from_float_ray(&leaf_model, &completed.farkas)
            .expect("the continuation ray must exactify");
        farkas
            .verify(&leaf_model)
            .expect("the exact Farkas certificate must independently verify");
    }

    #[test]
    fn default_wrapper_is_identical_to_explicit_normal_mode() {
        let (_, default_lp, default_fixed, _) = independent_warm_repairs(8);
        let (_, explicit_lp, explicit_fixed, _) = independent_warm_repairs(8);
        let default_root = default_lp.solve(None);
        let explicit_root = explicit_lp.solve(None);
        assert_same_candidate(&default_root, &explicit_root);
        let (default_lower, default_upper) = fixed_box(&default_lp, &default_fixed);
        let (explicit_lower, explicit_upper) = fixed_box(&explicit_lp, &explicit_fixed);

        let default = {
            let _cap = IterCap::set(2);
            default_lp.solve_bounded(
                &default_lower,
                &default_upper,
                Some((&default_root.basis, &default_root.at)),
                None,
            )
        };
        let explicit = {
            let _cap = IterCap::set(2);
            explicit_lp.solve_bounded_with_mode(
                &explicit_lower,
                &explicit_upper,
                Some((&explicit_root.basis, &explicit_root.at)),
                WarmSolveMode::Normal,
                None,
            )
        };
        assert_same_candidate(&default, &explicit);
        assert_eq!(default.status, SimplexStatus::Stopped);
        assert_eq!(
            default.basis, default_root.basis,
            "the historical capped warm-dual failure remains transactional"
        );
        assert!(
            default_lp.dual_adapt.get().0 > 0 && explicit_lp.dual_adapt.get().0 > 0,
            "Normal mode must retain the historical warm-dual routing"
        );
    }
}

/// THE COLD-ROOT LU BAND, pinned to the instances it was measured on.
///
/// The band is a policy decision with a corpus behind it (see
/// `FloatLp::cold_root_lu`), and the failure mode of a factorisation dispatch is
/// not a crash — it is a silently different pivot sequence on a model class
/// nobody re-measured. So the boundaries are asserted against the ROW COUNTS of
/// the actual A/B instances, which makes an accidental widening of the window
/// fail here with the name of the instance it would have swept in.
#[cfg(test)]
mod cold_root_lu_band_tests {
    use super::*;

    /// `(m, in_band)` for every instance the 2026-07-27/28 A/B covered.
    const MEASURED: &[(usize, bool, &str)] = &[
        (12, false, "mas76: eta wins, 2.66x wall / 1.51x nodes on LU"),
        (
            18,
            false,
            "flugpl: eta wins, 1.96x wall / 2.53x nodes on LU",
        ),
        (212, false, "misc07: eta wins"),
        (
            291,
            false,
            "rout: LU lands a WORSE incumbent (1117.6 vs 1083.5)",
        ),
        (
            426,
            false,
            "air05: force-lever LU traded BOUND 26143 for a bare incumbent",
        ),
        (
            503,
            false,
            "qnet1: eta wins, 1.37x wall; verdict 16029.692681 either way",
        ),
        (780, false, "gen: eta wins"),
        (
            1_192,
            false,
            "qiu: mixed (-34% nodes, +47% wall) — not admitted",
        ),
        (2_298, false, "binkar10_1: mixed — not admitted"),
        (
            3_068,
            true,
            "cvs16r89-60: eta never finishes LP0; LU proves -89.0",
        ),
        (
            3_278,
            true,
            "cvs16r70-62: 17,927 -> 161,725 pivots, UNKNOWN -> FEASIBLE",
        ),
        (
            3_522,
            true,
            "nursesched-sprint02: 3.5x pivots/s, root LP 59.2s -> 17.4s",
        ),
        (
            4_587,
            true,
            "peg-solitaire-a3: 7,034 rebuilds/36.7s -> 66/0.70s",
        ),
        (
            4_744,
            true,
            "neos-960392: 2 -> 287 nodes, REFAC 819/9.7s -> 33/0.02s",
        ),
        (
            4_944,
            true,
            "seymour1: eta never finishes LP0; LU proves 403.846474",
        ),
        (
            5_195,
            true,
            "hypothyroid-k1: no root bound -> bound -2902.852586",
        ),
        (
            6_119,
            true,
            "glass-sc: 3,657 rebuilds/46.3s -> 167/0.30s, UNKNOWN -> FEASIBLE",
        ),
        (
            7_029,
            true,
            "bnatt500: 3,157 rebuilds/17.9s -> 294/2.6s, same BOUND 0",
        ),
        (
            8_382,
            false,
            "neos-4647030-tutaki: first instance past the ceiling",
        ),
        (
            9_499,
            false,
            "mzzv11: above the ceiling, w5/cifar regime keeps it",
        ),
        (
            14_187,
            false,
            "neos-827175: layered-equality, keeps its triangular crash",
        ),
        (
            40_962,
            false,
            "ex9: refac wall removed but O(m) FT update replaces it",
        ),
        (69_608, false, "ex10: same — net 0.79x pivots/s"),
        (121_161, false, "uccase12"),
        (168_336, false, "physiciansched6-2"),
    ];

    #[test]
    fn the_band_admits_exactly_the_instances_it_was_measured_on() {
        for &(m, want, why) in MEASURED {
            assert_eq!(
                cold_root_lu_band(m, COLD_LU_MIN_ROWS, REFACTOR_TALL_ROWS),
                want,
                "m = {m} ({why})"
            );
        }
    }

    #[test]
    fn the_band_is_half_open_at_both_ends() {
        assert!(!cold_root_lu_band(
            COLD_LU_MIN_ROWS - 1,
            COLD_LU_MIN_ROWS,
            REFACTOR_TALL_ROWS
        ));
        assert!(cold_root_lu_band(
            COLD_LU_MIN_ROWS,
            COLD_LU_MIN_ROWS,
            REFACTOR_TALL_ROWS
        ));
        assert!(cold_root_lu_band(
            REFACTOR_TALL_ROWS - 1,
            COLD_LU_MIN_ROWS,
            REFACTOR_TALL_ROWS
        ));
        // A model exactly on the ceiling belongs to the class ABOVE, the same
        // way `lu_verify_after`/`adopt_ft_max` hand it back at `m >= 8192`.
        assert!(!cold_root_lu_band(
            REFACTOR_TALL_ROWS,
            COLD_LU_MIN_ROWS,
            REFACTOR_TALL_ROWS
        ));
    }

    /// The band sits strictly INSIDE the tall-LU class, so every model it admits
    /// already had the FT engine on its WARM node solves (`node_lu`) and already
    /// falls in the class where `lu_verify_after` and `adopt_ft_max` are tuned.
    /// The dispatch therefore extends an existing lane; it never opens a new one.
    #[test]
    fn the_band_is_contained_in_the_tall_lu_class() {
        assert!(COLD_LU_MIN_ROWS > TALL_LU_ROWS);
        assert!(REFACTOR_TALL_ROWS > COLD_LU_MIN_ROWS);
    }

    /// An empty or inverted window must decline, not admit everything — this is
    /// the shape a fat-fingered `AY_MILP_COLD_LU_ROWS=99999` takes.
    #[test]
    fn an_inverted_window_admits_nothing() {
        for m in [0usize, 1, 3_000, 5_195, 1 << 20] {
            assert!(!cold_root_lu_band(m, 8_192, 3_000));
        }
    }

    /// A FLOOR OF ZERO MUST NOT OPEN THE BAND TO EVERYTHING.
    ///
    /// The inverted-window test above covers `min > max`; it does not cover
    /// `min = 0`, which is the reachable footgun: an operator writing
    /// `AY_MILP_COLD_LU_ROWS=0` means "no floor", and honouring that literally
    /// admits every in-band `plain_cold` solve. That is sound but measurably
    /// worse — gt2 and qiu both fall OPTIMAL -> FEASIBLE and timtab1 loses its
    /// incumbent — because below the floor the FT engine's per-pivot cost is
    /// pure loss and it moves the vertex. `cold_lu_min_rows` therefore filters
    /// zero back to the compiled floor, so a zero floor must still exclude the
    /// small models the floor exists to protect.
    #[test]
    fn a_zero_floor_still_excludes_the_models_the_floor_protects() {
        // What the band does with the compiled floor restored, which is what
        // `cold_lu_min_rows` yields for an explicit 0.
        for m in [1usize, 200, 1_000, 2_298, 2_999] {
            assert!(
                !cold_root_lu_band(m, COLD_LU_MIN_ROWS, 8_192),
                "m = {m} is below the floor and must stay on the eta lane",
            );
        }
        // And a literal zero floor would admit exactly those — the behaviour
        // the filter exists to prevent.
        assert!(
            cold_root_lu_band(2_298, 0, 8_192),
            "a zero floor admits binkar10_1-sized models; that is why it is filtered out",
        );
    }
}

#[cfg(test)]
mod eager_affine_crash_tests {
    use super::*;

    #[test]
    fn range_logical_crash_policy_defaults_off_and_explicit_request_turns_it_on() {
        let (mut explicit, _, _) = range_row_model(1.0, 1.0);
        let (default, _, _) = range_row_model(1.0, 1.0);

        assert!(!default.range_logical_triangular_crash);
        explicit.request_range_logical_triangular_crash();
        assert!(explicit.range_logical_triangular_crash);
    }

    #[test]
    fn range_logical_crash_env_exact_one_turns_it_on() {
        assert!(range_logical_crash_env_value(Some("1")));
    }

    #[test]
    fn range_logical_crash_malformed_env_values_stay_off() {
        for value in [
            None,
            Some(""),
            Some("0"),
            Some("01"),
            Some("true"),
            Some("on"),
        ] {
            assert!(
                !range_logical_crash_env_value(value),
                "unexpected opt-in for {value:?}"
            );
        }
    }

    #[test]
    fn typed_range_logical_crash_request_does_not_bleed_between_lps() {
        let (mut explicit, _, _) = range_row_model(1.0, 1.0);
        let (plain, _, _) = range_row_model(1.0, 1.0);

        explicit.request_range_logical_triangular_crash();

        assert!(explicit.range_logical_triangular_crash);
        assert!(
            !plain.range_logical_triangular_crash,
            "typed policy leaked to a separately lowered LP"
        );

        let mut sx = Simplex::new(&explicit, &explicit.lower, &explicit.upper);
        assert!(sx.triangular_crash(&explicit, explicit.range_logical_triangular_crash));
        assert!(sx.range_logical_crash_installed);
    }

    #[test]
    fn advisory_is_instance_local_and_installs_a_small_chain_basis() {
        // This two-column affine chain is deliberately far below the global
        // big-LP gate.  Only the explicit per-instance advice licenses the
        // immediate crash attempt.
        let mut model = Model::new();
        let x = model.add_col(0.0, 1.0);
        let z = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        model.add_row(0.0, 0.0, &[(z, 1.0), (x, -1.0)]);

        let plain = FloatLp::from_model(&model, &[(z.0, 1.0)], Sense::Minimize).expect("plain LP");
        assert!(plain.cols < BIG_LP_COLS && plain.m < BIG_LP_ROWS);
        assert!(!plain.eager_affine_crash);

        let mut advised =
            FloatLp::from_model(&model, &[(z.0, 1.0)], Sense::Minimize).expect("advised LP");
        advised.request_eager_affine_crash();
        assert!(advised.eager_affine_crash);
        assert!(!plain.eager_affine_crash, "advice leaked to another LP");

        let mut sx = Simplex::new(&advised, &advised.lower, &advised.upper);
        assert!(sx.triangular_crash(&advised, false));
        assert_eq!(sx.basis, vec![x.index()]);
    }

    fn range_row_model(first_pivot: f64, second_pivot: f64) -> (FloatLp, Col, Col) {
        let mut model = Model::new();
        let z0 = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let z1 = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        model.add_row(0.0, 0.0, &[(z0, first_pivot)]);
        model.add_row(0.0, 0.0, &[(z1, second_pivot), (z0, -1.0)]);
        // Every non-equality row sees both peeled outputs, so the installed
        // block has a genuine nonzero B_RE below its equality triangle.
        model.add_row(-2.0, 2.0, &[(z0, 1.0), (z1, 1.0)]);
        model.add_row(-3.0, 3.0, &[(z0, 2.0), (z1, -1.0)]);
        model.add_row(-4.0, 4.0, &[(z0, -1.0), (z1, 2.0)]);
        let lp =
            FloatLp::from_model(&model, &[(z1.0, 1.0)], Sense::Minimize).expect("range-row LP");
        (lp, z0, z1)
    }

    #[test]
    fn range_logical_policy_installs_the_block_basis_only_after_full_equality_peel() {
        let (lp, z0, z1) = range_row_model(1.0, 1.0);
        assert_eq!(lp.m, 5);

        let mut ordinary = Simplex::new(&lp, &lp.lower, &lp.upper);
        assert!(
            !ordinary.triangular_crash(&lp, false),
            "two equality rows remain below the historical half-row gate"
        );
        assert_eq!(ordinary.basis, (lp.n..lp.n + lp.m).collect::<Vec<_>>());
        assert_eq!(ordinary.etas.entries(), 0);

        let mut range = Simplex::new(&lp, &lp.lower, &lp.upper);
        assert!(range.triangular_crash(&lp, true));
        assert_eq!(
            range.basis,
            vec![z0.index(), z1.index(), lp.n + 2, lp.n + 3, lp.n + 4]
        );
        assert!(
            range.etas.entries() > 0,
            "range-row spill must materialize the nonzero B_RE block"
        );
        for row in 2..lp.m {
            let logical = lp.n + row;
            assert_eq!(range.basic_row[logical], Some(row));
            assert_eq!(range.basis[row], logical);
        }

        // The installed eta operator must map every basis column to the unit
        // vector of its assigned row, including all retained range logicals.
        for row in 0..lp.m {
            let col = range.basis[row];
            range.ftran(&lp, col);
            for (i, &value) in range.alpha.iter().enumerate() {
                let expected = if i == row { 1.0 } else { 0.0 };
                assert!(
                    (value - expected).abs() <= 1e-12,
                    "basis col {col} row {i}: {value}, expected {expected}"
                );
            }
            for &i in &range.nz {
                range.alpha[i] = 0.0;
            }
            range.nz.clear();
        }

        // The sticky per-LP policy must also make the first later rebuild use
        // a valid operator for the same block basis.
        assert!(range.range_logical_crash_installed);
        range.refactorize(&lp);
        for row in 2..lp.m {
            let logical = lp.n + row;
            assert_eq!(range.basic_row[logical], Some(row));
            assert_eq!(range.basis[row], logical);
        }
        for row in 0..lp.m {
            let col = range.basis[row];
            range.ftran(&lp, col);
            for (i, &value) in range.alpha.iter().enumerate() {
                let expected = if i == row { 1.0 } else { 0.0 };
                assert!(
                    (value - expected).abs() <= 1e-12,
                    "post-refactor basis col {col} row {i}: {value}, expected {expected}"
                );
            }
            for &i in &range.nz {
                range.alpha[i] = 0.0;
            }
            range.nz.clear();
        }
    }

    #[test]
    fn range_logical_policy_declines_an_incomplete_equality_peel_untouched() {
        let mut model = Model::new();
        let z = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        model.add_row(0.0, 0.0, &[(z, 1.0)]);
        // A redundant empty equality has no admissible structural pivot.  The
        // first equality peels, but the full-equality guard must reject the
        // proposed mixed block basis.
        model.add_row(0.0, 0.0, &[]);
        model.add_row(-2.0, 2.0, &[(z, 1.0)]);
        model.add_row(-3.0, 3.0, &[(z, -1.0)]);
        model.add_row(-4.0, 4.0, &[(z, 2.0)]);
        let lp =
            FloatLp::from_model(&model, &[(z.0, 1.0)], Sense::Minimize).expect("partial-peel LP");
        assert_eq!(lp.m, 5);

        let mut sx = Simplex::new(&lp, &lp.lower, &lp.upper);
        assert!(!sx.triangular_crash(&lp, true));
        assert!(!sx.range_logical_crash_installed);
        assert_eq!(sx.basis, (lp.n..lp.n + lp.m).collect::<Vec<_>>());
        assert_eq!(sx.etas.entries(), 0);
        assert_eq!(sx.eta_nnz, 0);
        for row in 0..lp.m {
            assert_eq!(sx.basic_row[lp.n + row], Some(row));
        }
    }

    #[test]
    fn range_logical_policy_rolls_back_a_tiny_equality_pivot() {
        // Reversed peel order installs z0 first, then encounters z1's tiny
        // pivot. Rollback must therefore undo an already-installed structural
        // basis column and eta, not merely reject before the first mutation.
        let (lp, _, _) = range_row_model(1.0, 1e-8);
        let mut sx = Simplex::new(&lp, &lp.lower, &lp.upper);
        assert!(!sx.triangular_crash(&lp, true));
        assert_eq!(sx.basis, (lp.n..lp.n + lp.m).collect::<Vec<_>>());
        assert_eq!(sx.etas.entries(), 0);
        assert_eq!(sx.eta_nnz, 0);
        for row in 0..lp.m {
            assert_eq!(sx.basic_row[lp.n + row], Some(row));
        }
    }
}

#[cfg(test)]
mod bump_lu_tests {
    use super::*;

    /// Emit a `BumpFactor` exactly as `bump_lu_segment` does (L-etas in stage
    /// order, U-etas reversed) into a plain eta list, then apply it with the
    /// `EtaFile` application semantics. The unit-vector property this checks
    /// IS the operator contract the eta file relies on.
    fn emit(f: &BumpFactor) -> Vec<(usize, f64, Vec<(usize, f64)>)> {
        let mut etas = Vec::new();
        for (k, &(pr, _, _)) in f.stages.iter().enumerate() {
            if !f.lcols[k].is_empty() {
                let ents: Vec<(usize, f64)> = f.lcols[k]
                    .iter()
                    .map(|&(r, lm)| (r as usize, -lm))
                    .collect();
                etas.push((pr as usize, 1.0, ents));
            }
        }
        for &(pr, lc, piv) in f.stages.iter().rev() {
            let inv = 1.0 / piv;
            let ents: Vec<(usize, f64)> = f.uhist[lc as usize]
                .iter()
                .map(|&(si, u)| (f.stages[si as usize].0 as usize, -u * inv))
                .collect();
            etas.push((pr as usize, inv, ents));
        }
        etas
    }

    fn apply(etas: &[(usize, f64, Vec<(usize, f64)>)], v: &mut [f64]) {
        for (p, d, ents) in etas {
            let t = v[*p];
            if t == 0.0 {
                continue;
            }
            for &(i, w) in ents {
                v[i] += w * t;
            }
            v[*p] = d * t;
        }
    }

    /// xorshift64* — deterministic, dependency-free test randomness.
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x >> 12;
            x ^= x << 25;
            x ^= x >> 27;
            self.0 = x;
            x.wrapping_mul(0x2545_F491_4F6C_DD1D)
        }
        fn f(&mut self) -> f64 {
            (self.next() >> 11) as f64 / (1u64 << 52) as f64 - 1.0
        }
        fn below(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }
    }

    /// Random bump blocks with spectator rows: every pivoted column's emitted
    /// image must be exactly its unit vector; kicked plus pivoted must cover
    /// all columns; pivot rows must be open and distinct.
    #[test]
    fn bump_factor_maps_columns_to_unit_vectors() {
        for seed in 1u64..6 {
            let mut rng = Rng(seed);
            let m = 40usize;
            let b = 24usize;
            // Rows 0..30 open, 30..40 spectators (reserved backs in real use).
            let open: Vec<bool> = (0..m).map(|r| r < 30).collect();
            // Nonsingular-ish core: column c holds a strong entry on open row
            // c (identity backbone) plus random off-diagonal and spectator
            // entries.
            let cols: Vec<Vec<(u32, f64)>> = (0..b)
                .map(|c| {
                    let mut col = vec![(c as u32, 1.0 + rng.f().abs())];
                    for _ in 0..4 {
                        let r = rng.below(30);
                        if col.iter().all(|&(rr, _)| rr as usize != r) {
                            col.push((r as u32, 0.6 * rng.f()));
                        }
                    }
                    for _ in 0..2 {
                        let r = 30 + rng.below(10);
                        if col.iter().all(|&(rr, _)| rr as usize != r) {
                            col.push((r as u32, 2.0 * rng.f()));
                        }
                    }
                    col
                })
                .collect();
            let f = bump_eliminate(m, cols.clone(), &open, 1e-9, usize::MAX).unwrap();
            assert_eq!(f.stages.len() + f.kicked.len(), b, "every column accounted");
            assert!(f.kicked.is_empty(), "random block should be nonsingular");
            let mut seen_rows = vec![false; m];
            for &(pr, _, _) in &f.stages {
                assert!(open[pr as usize], "pivot row must be open");
                assert!(!seen_rows[pr as usize], "pivot rows distinct");
                seen_rows[pr as usize] = true;
            }
            let etas = emit(&f);
            for &(pr, lc, _) in &f.stages {
                let mut v = vec![0.0f64; m];
                for &(r, val) in &cols[lc as usize] {
                    v[r as usize] = val;
                }
                apply(&etas, &mut v);
                for (i, &x) in v.iter().enumerate() {
                    let want = if i == pr as usize { 1.0 } else { 0.0 };
                    assert!(
                        (x - want).abs() <= 1e-8,
                        "seed {seed} col {lc}: row {i} = {x}, want {want}"
                    );
                }
            }
        }
    }

    /// A duplicate column is numerically dependent: exactly one of the pair
    /// is kicked, the rest still map to exact unit vectors.
    #[test]
    fn bump_factor_kicks_dependent_columns() {
        let m = 6usize;
        let open = vec![true; 6];
        let cols: Vec<Vec<(u32, f64)>> = vec![
            vec![(0, 2.0), (1, 1.0)],
            vec![(0, 2.0), (1, 1.0)], // duplicate of column 0
            vec![(2, 1.0), (3, 0.5)],
        ];
        let f = bump_eliminate(m, cols.clone(), &open, 1e-9, usize::MAX).unwrap();
        assert_eq!(f.kicked.len(), 1, "one of the duplicates is dependent");
        assert!(f.kicked[0] == 0 || f.kicked[0] == 1);
        assert_eq!(f.stages.len(), 2);
        let etas = emit(&f);
        for &(pr, lc, _) in &f.stages {
            let mut v = vec![0.0f64; m];
            for &(r, val) in &cols[lc as usize] {
                v[r as usize] = val;
            }
            apply(&etas, &mut v);
            for (i, &x) in v.iter().enumerate() {
                let want = if i == pr as usize { 1.0 } else { 0.0 };
                assert!((x - want).abs() <= 1e-12, "col {lc}: row {i} = {x}");
            }
        }
    }

    /// The fill cap aborts the elimination (`None`) instead of overrunning —
    /// the caller's slot-order fallback contract.
    #[test]
    fn bump_factor_respects_entry_cap() {
        let m = 30usize;
        let open = vec![true; m];
        let mut rng = Rng(9);
        // Dense-ish block: plenty of fill.
        let cols: Vec<Vec<(u32, f64)>> = (0..m)
            .map(|c| {
                let mut col = vec![(c as u32, 2.0)];
                for r in 0..m {
                    if r != c && rng.below(2) == 0 {
                        col.push((r as u32, 0.5 * rng.f()));
                    }
                }
                col
            })
            .collect();
        assert!(bump_eliminate(m, cols, &open, 1e-9, 8).is_none());
    }
}

#[cfg(test)]
mod solve_work_frame_tests {
    use super::stats;

    /// The frame's whole purpose: a budget reads THIS solve's iterations, not the
    /// process's. Two sequential solves on one thread must not see each other's work.
    #[test]
    fn sequential_solves_do_not_see_each_other() {
        {
            let _f = stats::SolveWorkFrame::enter();
            stats::bump_solve();
            stats::bump_solve();
            assert_eq!(stats::solve_work(), 2);
        }
        {
            let _f = stats::SolveWorkFrame::enter();
            assert_eq!(stats::solve_work(), 0, "solve 2 inherited solve 1's work");
            stats::bump_solve();
            assert_eq!(stats::solve_work(), 1);
        }
    }

    /// A sub-MIP re-enters `solve_milp_*` on the same thread while its parent is live.
    /// Rebasing there would hand every sub-search a fresh full budget — a behaviour
    /// change on every instance that runs one. Only the outermost frame rebases.
    #[test]
    fn a_nested_frame_does_not_rebase() {
        let _outer = stats::SolveWorkFrame::enter();
        stats::bump_solve();
        stats::bump_solve();
        stats::bump_solve();
        {
            let _sub_mip = stats::SolveWorkFrame::enter();
            assert_eq!(
                stats::solve_work(),
                3,
                "a sub-MIP opened a fresh budget instead of drawing on its parent's"
            );
            stats::bump_solve();
        }
        assert_eq!(
            stats::solve_work(),
            4,
            "the sub-MIP's work was not charged to the enclosing solve"
        );
    }

    /// The property that makes this free to validate: on the one-solve-per-process
    /// harness the frame is a no-op, because both clocks start at zero and only this
    /// thread bumps them. Every bump site raises both counters in lockstep.
    #[test]
    fn matches_the_process_clock_when_it_is_the_only_solve() {
        let base = stats::work();
        let _f = stats::SolveWorkFrame::enter();
        for _ in 0..5 {
            stats::bump(&stats::DUAL_ITERS);
            stats::bump_solve();
        }
        assert_eq!(stats::solve_work(), stats::work() - base);
    }

    /// A worker thread starts with its own zeroed clock rather than inheriting the
    /// spawning solve's count — which is what makes the budget per-solve rather than
    /// per-process in the first place.
    #[test]
    fn a_fresh_thread_starts_at_zero() {
        let _f = stats::SolveWorkFrame::enter();
        stats::bump_solve();
        assert_eq!(stats::solve_work(), 1);
        std::thread::scope(|s| {
            s.spawn(|| {
                assert_eq!(stats::solve_work(), 0);
                stats::bump_solve();
                assert_eq!(stats::solve_work(), 1);
            });
        });
        assert_eq!(
            stats::solve_work(),
            1,
            "a worker leaked into the parent's clock"
        );
    }
}

#[cfg(test)]
mod eager_perturb_gate_tests {
    use super::{eager_perturb_applies_to, eager_perturb_mode};

    /// With no caller opinion the mode must be ARMED (1) — the shipped
    /// default; the blanket arm (2) stays reachable only by explicit request
    /// (`with_eager_perturb(2)`, builder-validated).
    #[test]
    fn the_default_mode_is_armed() {
        assert_eq!(eager_perturb_mode(), 1, "unset must be ARMED");
    }

    /// The gate that carries rout's and noswot's proofs. Under the DEFAULT mode
    /// a cold solve perturbs eagerly only once this LP's own cold walk has been
    /// seen to stall; rout and noswot never stall, so they take the plain path.
    #[test]
    fn armed_mode_waits_for_a_cold_stall_and_ignores_warm_solves() {
        const OFF: u8 = 0;
        const ARMED: u8 = 1;
        const ALL: u8 = 2;
        // Not yet armed: cold or warm, the eager path stays out of the way.
        assert!(!eager_perturb_applies_to(ARMED, false, false));
        assert!(!eager_perturb_applies_to(ARMED, true, false));
        // Armed: COLD solves take the eager path...
        assert!(eager_perturb_applies_to(ARMED, false, true));
        // ...and WARM ones still do not. A warm node LP starts from the
        // parent's optimal basis; its stalls are a different fault.
        assert!(!eager_perturb_applies_to(ARMED, true, true));
        // The two explicit modes ignore the arm entirely, in both directions.
        for stalled in [false, true] {
            for warm in [false, true] {
                assert!(!eager_perturb_applies_to(OFF, warm, stalled));
                assert!(eager_perturb_applies_to(ALL, warm, stalled));
            }
        }
    }
}

/// Force every lazily-cached environment read in this module to happen NOW.
///
/// # The race this closes
///
/// `tune.rs` states the property the crate is supposed to have: *"The environment
/// layer is read **once**, into `EnvSnapshot`, and never again — so no accessor on
/// the solve path touches `std::env`."* That is true of the `tune` layer and FALSE
/// of the crate: 58 accessors here cache their value in a `OnceLock` and call
/// `env::var` **lazily**, inside `get_or_init`, the first time the solve path
/// happens to reach them — at an arbitrary point, on an arbitrary thread.
///
/// That is the exact hazard `EngineEconomics` was built to remove.
/// the development design notes records the consumer's mitigation:
/// it *"rewrites the same constant values before every window solve"*, so a
/// `set_var` on one thread can land while another thread is mid-solve taking its
/// first `getenv` here. `std::env::set_var` racing a concurrent `getenv` is why it
/// is `unsafe` in edition 2024.
///
/// Priming collapses those windows into ONE, at solve entry, before any worker is
/// spawned. It changes no value: the same `OnceLock`s resolve to the same bytes.
/// It only moves *when* they are read, from "scattered across the solve" to "once,
/// at a point the caller controls".
pub(crate) fn prime_env() {
    let _ = refactor_every_override();
    let _ = adopt_ft_max();
    let _ = adopt_ft_max_rows();
    let _ = bump_btf_env();
    let _ = bump_diag_enabled();
    let _ = bump_lu_min();
    let _ = bump_scc_enabled();
    let _ = chain_devex_mode();
    let _ = chain_preorder();
    let _ = chain_probe_iters();
    let _ = chain_shape_enabled();
    let _ = churn_band_factor();
    let _ = cold_lu_eta_rebuilds();
    let _ = cold_lu_max_rows();
    let _ = cold_lu_min_rows();
    let _ = dual_anatomy_enabled();
    let _ = dual_bloom_cap_override();
    let _ = dual_bypass_mode();
    let _ = dual_perturb_mag();
    let _ = eager_perturb_mode();
    let _ = eta_cap_mult();
    let _ = eta_gen_cap();
    let _ = eta_reuse_age();
    let _ = force_tri_crash();
    let _ = fused_defer_enabled();
    let _ = fused_rt_enabled();
    let _ = iter_ledger_enabled();
    let _ = iter_profile_enabled();
    let _ = lp_stats_enabled();
    let _ = lu_enabled();
    let _ = lu_refactor_every();
    let _ = lu_verify_after();
    let _ = no_bump_lu();
    let _ = no_fill_trip();
    let _ = fill_trip_optin();
    let _ = no_cold_dual();
    let _ = no_cold_lu();
    let _ = no_cutoff();
    let _ = no_devex();
    let _ = no_dual_churn_band();
    let _ = no_dual_perturb();
    let _ = no_eta_reuse();
    let _ = no_node_lu();
    let _ = no_noenter_unscale();
    let _ = no_tall_lu();
    let _ = no_tri_crash();
    let _ = no_wide_bloom();
    let _ = probe_lu_reuse_enabled();
    let _ = range_logical_crash_env_enabled();
    let _ = rt_bits_key_enabled();
    let _ = rt_kind_enabled();
    let _ = rt_kind_verify_enabled();
    let _ = rt_masked_enabled();
    let _ = shape_census_enabled();
    let _ = tall_lu_rows();
    let _ = tau_nz_enabled();
    let _ = trace_enabled();
    let _ = verify_after();
}

#[cfg(test)]
mod refactor_cadence_tests {
    use super::{
        refactor_every, refactor_every_override, REFACTOR_EVERY, REFACTOR_EVERY_TALL,
        REFACTOR_TALL_ROWS,
    };

    /// Pins the split of `refactor_every` into a nullary cached override plus a pure
    /// size-dependent default. The split exists so the env read can be PRIMED; it
    /// must not have moved the cadence.
    ///
    /// With no override set, the value is a pure function of `m` and the tall
    /// threshold — this is the whole behaviour the split had to preserve, and it was
    /// untested before the split touched it.
    #[test]
    fn the_cadence_is_the_size_default_when_unset() {
        // Only meaningful when the operator has not overridden it; the crate's own
        // A/B recipes may export it, and then the override legitimately wins.
        // Via the accessor, not a second `env::var`: a direct read here would add a
        // literal call site that `read_site_counts_are_derived` counts against the
        // ledger, so a test guard would silently inflate the crate's own census.
        if refactor_every_override().is_some() {
            return;
        }
        assert_eq!(refactor_every(0), REFACTOR_EVERY);
        assert_eq!(refactor_every(REFACTOR_TALL_ROWS - 1), REFACTOR_EVERY);
        assert_eq!(refactor_every(REFACTOR_TALL_ROWS), REFACTOR_EVERY_TALL);
        assert_eq!(refactor_every(usize::MAX), REFACTOR_EVERY_TALL);
        // The boundary is `>=`, and it is the same constant the FT-adoption and
        // verify ceilings key on — a gate the census currently ranks second.
        assert!(REFACTOR_EVERY_TALL > REFACTOR_EVERY);
    }
}

#[cfg(test)]
mod fill_trip_tests {
    /// THE TRIP CANNOT ARM UNLESS EXPLICITLY OPTED IN.
    ///
    /// `maybe_trip_bump_fill` ships off-by-default (B22: env retired) because its
    /// predicate is known biased — it compares the bump against the singleton peel,
    /// which is fill-free BY SELECTION rather than by measurement, so a strict `>`
    /// with no margin would arm on the ~160-column crash-walk bumps the floor exists
    /// to protect. Until the commensurable shadow-probe version replaces it, the
    /// shipped lane must be exactly the historical column floor.
    ///
    /// This pins the three-way guard. It is not a test of the predicate — the
    /// predicate is provisional — it is a test that the predicate CANNOT RUN.
    #[test]
    fn the_default_lane_is_the_column_floor_alone() {
        // B22: the opt-in is a compiled constant now — nothing ambient can
        // arm it.
        assert!(
            !super::fill_trip_optin(),
            "the fill-trip opt-in must be retired-off; the shipped default is \
             not what this test claims to pin otherwise"
        );
        // And the kill switch is independent of the opt-in: either one off is enough.
        // `no_fill_trip()` is the arm that restores prior behaviour when someone HAS
        // opted in, so the two are deliberately not the same knob.
        let armed_possible = super::fill_trip_optin() && !super::no_fill_trip();
        assert!(
            !armed_possible,
            "the trip is reachable by default; the lane is no longer the column floor"
        );
    }
}
