// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EXACT lattice proof for the market-split min-total-slack family (markshare1).
//!
//! ## The instance the whole field cannot prove
//!
//! markshare1 is 6 equality rows `a_i·x + s_i = b_i` over 50 binaries `x` and
//! nonneg continuous slacks `s`, minimising `Σ s_i`. Every `b_i` is exactly
//! `½·Σ_j a_ij`, so the LP relaxation puts `x = ½·1`, hits every equality
//! exactly, and reports objective 0 — a bound that never moves. The float
//! solvers then enumerate millions of nodes (Gurobi 4.6M at 60s) and NONE
//! proves the optimum is 1. Every exact cut family AY has (MIR, strong-CG,
//! GMI, cover) leaves the root bound at 0.000000 as well: this is not a
//! cutting problem, it is a LATTICE problem.
//!
//! ## What "optimum = 1" means, exactly
//!
//! `Σ s_i` is a nonneg integer (`a`,`x`,`b` all integer). It is 0 iff `A x = b`
//! has a 0/1 solution — the "objective-0 face". So:
//!   * the objective-0 face is EMPTY  ⟹  optimum ≥ 1  (no exact market split);
//!   * some face `A x = b − e_k` has a 0/1 point ⟹  optimum ≤ 1  (that point
//!     leaves slack 1 in row `k`, 0 elsewhere).
//! Both are decided here by exact lattice enumeration and together prove
//! OPTIMAL 1 — beating the entire field on this instance.
//!
//! ## The device (Aardal–Hurkens–Lenstra reformulation + CVP enumeration)
//!
//! For a target rhs `d` (either `b` or `b−e_k`):
//!   1. `x = x_d + K y` where `A x_d = d` (a particular integer solution) and
//!      `K` is a basis of the SATURATED integer kernel `{x∈ℤ^n : A x = 0}`,
//!      computed by column-Hermite-normal-form with unimodular tracking.
//!   2. LLL-reduce `K` and Babai-reduce `x_d` against it, so the 0/1 box maps
//!      to a well-conditioned region in `y`.
//!   3. Every 0/1 point sits EXACTLY on the sphere `‖x − ½·1‖² = n/4`.
//!      Project `τ = ½·1 − x_d` onto `span(K)` and enumerate every lattice
//!      point `K y` at projected squared distance
//!      `n/4 − ‖τ − proj(τ)‖²` (Fincke–Pohst / Schnorr–Euchner). This is the
//!      exact binary-sphere intersection with `span(K)`; the final radius is
//!      rounded outward so no feasible point is lost. Every candidate is then
//!      checked EXACTLY against the integer box `0 ≤ x_d + K y ≤ 1`.
//!
//! On markshare1 the objective-0 face enumeration visits ~43.6M nodes and
//! finds NOTHING (proving optimum ≥ 1); the `b − e_0` face yields a 0/1 point
//! of 25 ones (proving optimum ≤ 1). Both run in a few seconds.
//!
//! ## Exactness
//!
//! HNF, kernel, particular solution, Babai reduction and the per-candidate box
//! check are all exact (`BigInt` / `i64`). Enumeration uses the exact rational
//! GSO converted to outward-rounded `f64` intervals: every center, partial
//! distance and integer range encloses its exact value. Therefore a valid point
//! can never be pruned by floating arithmetic. Every point the enumeration
//! keeps is adjudicated by exact integer arithmetic, and the returned witness
//! is finally re-checked by `Model::check_point`. Anything whose interval is
//! non-finite or too wide to enumerate aborts to `None` and hands the model back
//! to the normal search untouched.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};
use std::ffi::OsStr;
use std::mem::size_of;
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::Mutex;
use std::thread::ScopedJoinHandle;
use std::time::Instant;

use crate::cert_io::{ledger as replay_ledger, ReplayClaim};
use crate::model::{exact, Col, Model, Row, Sense};
use crate::opts::SolveOpts;
use crate::outcome::Outcome;

/// THE TRUSTED COMPUTING BASE OF THIS DEVICE, named in every replay claim it
/// files.
///
/// A verdict from this file is not backed by a 200-line checker; it is backed
/// by all ~6400 lines of it — the AHL reformulation, the column-HNF, LLL/BKZ,
/// the Schnorr–Euchner sweep, and the outward-rounded interval arithmetic that
/// prunes it. That is a legitimate thing to trust and an illegitimate thing to
/// hide, so it is written into the certificate.
const TCB: &str = "crates/ay-milp/src/lattice.rs";

/// Hard cap on the enumeration so a mis-fire can never run away: past this the
/// device aborts to `None` and the normal search takes over. markshare1's
/// objective-0 face is ~43.6M nodes, so 4G is ~100× headroom. This is the
/// SERIAL budget; a parallel sweep's shared envelope is `NODE_BUDGET ×
/// workers` (each worker gets the historical serial allowance — see
/// `EnumState::shared_budget`).
const NODE_BUDGET: u64 = 4_000_000_000;

/// Parallel Fincke–Pohst enumeration: how many independent top-of-tree work
/// items to aim for PER worker thread.  The top DFS levels are enumerated
/// single-threaded into a frontier of independent subtrees (a COMPLETE
/// partition of the sweep), then handed out to workers via a shared atomic
/// work-index.  Over-decomposing well past the thread count lets dynamic
/// hand-out absorb the (large) size variance between subtrees — the top GSO
/// vector is the longest, so its subtrees are the most uneven.
const LATTICE_FRONTIER_PER_THREAD: usize = 256;

/// A split may overshoot the balance target because all nodes at the selected
/// depth belong to the same complete partition. Bound that overshoot to 4096
/// items per worker before declining the parallel device.
const LATTICE_FRONTIER_TARGET_MULTIPLIER: usize = 16;

/// Heap envelope for a parallel frontier. `WorkItem` owns two vectors, so the
/// item-count cap is derived conservatively from the full lattice dimension.
const LATTICE_FRONTIER_MAX_BYTES: usize = 64 * 1024 * 1024;

/// Nodes a parallel enumeration state reserves from the shared envelope per
/// claim. Per-node CAS on one shared cache line serializes 16 workers to below
/// a single serial thread's node rate (measured ~4M/s aggregate vs ~9M/s
/// serial); chunked reservation removes that wall while preserving the
/// envelope EXACTLY: the shared counter only ever holds nodes RESERVED
/// (visited ≤ reserved ≤ `NODE_BUDGET`), a claim that cannot fit the budget
/// aborts fail-closed, at the budget boundary the claim degrades to the exact
/// remainder (so the boundary semantics are unchanged), and a state returns
/// its unspent reservation on drop so the counter equals the true visited
/// total once a sweep's states are gone. Transient overshoot is bounded by
/// `threads × this` — an abort can only fire EARLIER, never later.
const SHARED_NODE_RESERVE: u64 = 4096;

/// Multiplicative slack applied to the box-prune error envelope. It absorbs
/// the `1/(1 − dim·u)` fixed-point factor of the accumulated-rounding bound and
/// every round-to-nearest step of the O(1) envelope computation itself, with
/// ~7 orders of magnitude to spare at any realistic `dim`.
const BOX_PRUNE_EPS_SLACK: f64 = 1.0 + 1e-9;

/// Magnitude ceiling for the box-prune envelope. Past it the running centre
/// bound is too large to rule out `f64` overflow inside the FMA chain, so the
/// test is skipped for that node (fail-closed: no prune, never a wrong prune).
/// Real faces sit ~250 orders of magnitude below this.
const BOX_PRUNE_MAX_SCALE: f64 = 1e250;

/// Per-block SVP enumeration cap inside BKZ. A block on an already-LLL-reduced
/// basis enumerates a well-conditioned ~β-dim ball, so this is generous; past it
/// the block declines to improve (reduction quality only — never soundness).
const BKZ_SVP_NODE_CAP: u64 = 60_000_000;

/// Per-block cap for the PRUNED oracle.  At full kernel dimension even the
/// pruned tree can be large, and Schnorr–Euchner finds its improvements EARLY
/// (it descends by nearest-plane first), so a tight cap converts one saturated
/// call into many cheap calls — measured on the dim-62 Cornuejols–Dawande
/// kernels, β=dim goes from oracle-bound single tours to many full tours
/// inside the same budget, which is what actually shrinks the enumeration
/// ball.  A truncated call still returns the best insertion found so far;
/// missing the block optimum is reduction quality only.
const BKZ_PRUNED_SVP_NODE_CAP: u64 = 4_000_000;

/// Adaptive BKZ policy.  Small kernels keep the historical LLL path; MEDIUM
/// kernels (dimension in `BKZ_MIN_KERNEL_DIM..BKZ_LARGE_KERNEL_DIM`) use
/// FULL-KERNEL-DIMENSION blocks with the PRUNED block-SVP oracle (BKZ
/// 2.0-style, Gama–Nguyen–Regev linear profile): the reduction converges in
/// well under a second and the measured dim-53 walls hold or improve
/// (markshare2 1.45s → 1.42s with the objective-0 EMPTY sweep at 24.5M vs
/// 22.4M nodes; cd_m7_s1 2.21s → 1.18s with the witness at 11.2M vs 58.6M
/// nodes).  Pruning may only MISS a block improvement (the block declines —
/// reduction quality); the Gram-det guard and the exact final enumeration
/// carry all soundness.  This is a deterministic product policy; the optional
/// `AY_MILP_LATTICE_BKZ` operator override (reduction quality only — never
/// soundness) is resolved separately in [`bkz_beta_override`].
const BKZ_MIN_KERNEL_DIM: usize = 49;
/// The historical exact-oracle block size — still the block size for LARGE
/// kernels (see `effective_bkz_beta`), where the full-dimension gamble
/// measurably LOSES verdicts.
const BKZ_ADAPTIVE_BETA: usize = 34;

/// Kernels of dimension ≥ this keep the proven exact β=34 path at every solve
/// slice.  The full-dimension pruned gamble was measured on this base and
/// REJECTED for them: on the dim-62 Cornuejols–Dawande family the feasible
/// face's wall is the witness's POSITION in the deterministic sweep, which
/// re-rolls with every basis change, and all three pruned β=62 variants
/// (immediate-LLL convergence, deferred-LLL convergence, immediate-LLL
/// 2-tour) rolled the cd_m8_s1 witness past 8.1e9–13.0e9 nodes — losing at
/// 300s a verdict the exact β=34 2-tour basis proves at 63s (witness at
/// 5.55e9) — even though their bases were globally BETTER (Σ‖·‖² 1799–1806 vs
/// 2000).  Medium kernels keep the pruned path: their measured walls hold or
/// improve with verdicts preserved.  `AY_MILP_LATTICE_BKZ` still exposes the
/// full-dimension pruned reduction to operators with long budgets.
const BKZ_LARGE_KERNEL_DIM: usize = 57;

/// Adaptive BKZ tour caps (see `adaptive_bkz_tours` for the measurements).
/// Exact-oracle kernels at or above the threshold stop after
/// `BKZ_TOURS_LARGE` tours; the rest run up to `BKZ_TOURS_SMALL` (markshare2
/// converges naturally at 4).  The pruned full-dimension path instead runs to
/// CONVERGENCE (an insertion-free tour) under `BKZ_TOURS_PRUNED` as a pure
/// runaway stop: its tours are much cheaper (tight per-call node cap) and
/// every extra tour shrinks the enumeration ball, so the deadline and the
/// quiet-tour test are the real terminators.
const BKZ_FEW_TOURS_MIN_DIM: usize = 58;
const BKZ_TOURS_LARGE: u64 = 2;
const BKZ_TOURS_SMALL: u64 = 8;
const BKZ_TOURS_PRUNED: u64 = 256;

/// Parallel block-SVP policy. Blocks below the minimum size enumerate serially
/// (the split overhead outweighs the win); the frontier split targets a FIXED
/// item count so the item set — and the deterministic (norm, item-index) winner
/// — is identical for every worker count and box, with the depth capped so a
/// bushy top cannot over-decompose.
const SVP_PAR_MIN_BLOCK: usize = 8;
const SVP_PAR_TARGET_ITEMS: usize = 64;
const SVP_PAR_MAX_SPLIT_LEVELS: usize = 4;

/// Fraction of the device's remaining budget that exact BKZ may consume before
/// it must yield to validation + face enumeration.  BKZ converges or plateaus
/// early on this family, so capping it here never starves reduction, but it
/// guarantees the covolume/kernel guard has time to VALIDATE the (still exact,
/// still unimodular) basis instead of declining a reduction that merely ran out
/// the clock — and it leaves the enumeration the majority of the budget.
const BKZ_BUDGET_FRACTION: f64 = 0.4;

/// Absolute ceiling on BKZ wall time.  With the incremental-GSO LLL and the
/// parallel block-SVP, BKZ terminates NATURALLY (tour cap / convergence) well
/// under this ceiling on the whole family — markshare2 in ~0.6s, the dim-62
/// Cornuejols–Dawande kernels in ~1–3s — so the ceiling is a pure safety net
/// (a deadline-truncated BKZ would make the basis depend on box speed).
/// Combined with the fraction, BKZ takes `min(0.4·remaining, this)`.
const BKZ_ABS_CAP_SECS: f64 = 15.0;

/// Absolute BKZ ceiling for the PRUNED path.  The medium-kernel default
/// converges far below it (β=53 in ~0.3s), so it exists as headroom for the
/// `AY_MILP_LATTICE_BKZ` operator lever, where β=dim tours over a dim-62+
/// kernel do NOT plateau in 15s.  The `BKZ_BUDGET_FRACTION` term still
/// reserves the strict majority of any solve slice for validation +
/// enumeration.
const BKZ_LARGE_ABS_CAP_SECS: f64 = 60.0;

/// Poll wall-clock cancellation frequently enough that float-guided lattice
/// enumeration cannot consume a meaningful fraction of a short solve slice
/// after its deadline.  The checks are several orders of magnitude cheaper
/// than the BigInt/floating work between them.
const ENUM_DEADLINE_POLL_NODES: u64 = 1 << 16;
const BKZ_DEADLINE_POLL_NODES: u64 = 1 << 14;
const GSO_DEADLINE_POLL_OPS: usize = 64;

/// Largest magnitude through which every integer is represented exactly by `f64`.
const MAX_EXACT_F64_INT: f64 = 9_007_199_254_740_992.0;

/// Size caps — the family is tiny (markshare1: 6×62). Anything wider is out of
/// the family and out of the enumeration's budget; it pays one comparison.
const MAX_ROWS: usize = 24;
const MAX_COLS: usize = 160;

/// Widened-gate caps. Bounded-integer columns must live inside ±2^20 so every
/// per-column product/bound stays comfortably inside `i64` (the enumerator's
/// hot loop is `checked_*` anyway — these caps keep the gate from even trying
/// hopeless shapes). A synthetic inequality slack wider than this range would
/// blow the enumeration ball up for no realistic gain, so the gate declines.
const MAX_INT_BOUND_ABS: i64 = 1 << 20;
const MAX_SYNTH_SLACK_RANGE: i64 = 4096;
/// Constraint rows are cleared of fractional coefficients by multiplying with
/// the LCM of the denominators (the MPS reader scales rows by powers of two);
/// anything needing a larger multiplier is out of the family.
const MAX_ROW_SCALE: u32 = 4096;

/// The (widened) market-split min-total-slack structure, compiled from a
/// [`Model`] into an EXACT extended integer equality system
///
/// ```text
///   A x = b,   x_p ∈ [lo_p, up_p] ∩ ℤ   (p = 0..n)
/// ```
///
/// where the lattice columns `x` are the model's free bounded-integer columns
/// followed by SYNTHETIC integer slacks (one per accepted pure-integer
/// inequality/range row), and the rows are the model's rows: objective rows
/// (`a·x + s_i = b_i` with a unit continuous slack `s_i`, min Σ s_i) plus
/// constraint rows rewritten `a·x + t = up'` with `t ∈ [0, up'−lo']`.
struct MarketSplit {
    /// Number of lattice columns (free integer columns + synthetic slacks).
    n: usize,
    /// Number of rows of the extended equality system (retained model rows).
    m: usize,
    /// `m × n` integer coefficient matrix over the lattice columns.
    a: Vec<Vec<i64>>,
    /// `m` integer right-hand sides (adjusted for fixed-column contributions).
    b: Vec<i64>,
    /// Per-lattice-column integer lower/upper bounds (`lo_p ≤ up_p`, both
    /// finite; the historical market-split shape is `lo = 0`, `up = 1`).
    lo: Vec<i64>,
    up: Vec<i64>,
    /// Model column index of each lattice column (`None` for a synthetic
    /// inequality slack, which exists only in the extended system).
    col_model: Vec<Option<usize>>,
    /// Indices INTO `a`/`b` of the rows carrying a unit continuous objective
    /// slack — the rows whose faces `b − e_k` witness objective value 1.
    /// Empty ⟹ pure feasibility mode (the model objective is constant).
    obj_rows: Vec<usize>,
    /// Model column index of each objective row's continuous slack (parallel
    /// to `obj_rows`).
    slack_col: Vec<usize>,
    /// Integral model columns whose bounds tighten to a single integer value
    /// (`ceil(l) == floor(u)` with `l != u`): treated as fixed in the system,
    /// recorded here so the witness point can restate them.
    singleton_cols: Vec<(usize, i64)>,
}

/// Column census result for [`detect`].
#[derive(Clone, Copy, PartialEq, Eq)]
enum ColClass {
    /// `l == u` in the model, or an integral column tightened to a point.
    Fixed,
    /// A free integral column with finite integer bounds — a lattice column.
    Int,
    /// A free continuous column on `[0, ub)` — an objective-slack candidate.
    Cont,
}

/// Detect the (widened) market-split shape, or `None`. SELF-GATING contract:
/// fires on `Minimize` models where
///   * every integral column is fixed or has FINITE bounds (0/1 or general),
///     carries objective 0, and |bounds| ≤ 2^20;
///   * every free continuous column is the unit-objective slack of exactly one
///     EQUALITY row (an "objective row", `a·x + s = b`, slack coeff > 0) —
///     so the nonconstant objective is exactly Σ s_i;
///   * every other row touches ONLY integer/fixed columns and has an exact
///     integer form `lo' ≤ a·x ≤ up'` after clearing denominators and
///     tightening to the integer hull (a·x ∈ ℤ) clamped to its box-implied
///     bounds — rewritten `a·x + t = up'` with a synthetic integer slack
///     `t ∈ [0, up'−lo']` (an EXACT bijection: `t = up' − a·x`); rows already
///     implied by the column box are dropped (they cannot cut anything).
///
/// The historical markshare1 shape (all-equality rows, unit continuous slacks,
/// all-0/1 columns) compiles to the IDENTICAL system as before the widening
/// (`lo = 0`, `up = 1`, `obj_rows = 0..m`, same `a`, `b`), so the proven path
/// is unchanged. Across the corpus the widened gate still fires only on
/// markshare1 (see `detect` trace scan): pk1 has 45 > 24 rows; mas74/misc07/
/// dcmulti/gen carry objective weight on structural columns; gt2/flugpl/noswot
/// have objective on their integer columns; qiu/air05 exceed the size caps.
fn detect(model: &Model) -> Option<MarketSplit> {
    // This device currently consumes the public f64 matrix.  A model with true
    // rational overrides must not be classified from those rounded proxies;
    // the ordinary exact rim handles it instead.
    if model.sense() != Sense::Minimize || model.has_inexact_coeffs() {
        return None;
    }
    let nc = model.num_cols();
    let nr = model.num_rows();
    if nr == 0 || nr > MAX_ROWS || nc == 0 || nc > MAX_COLS {
        // FORGONE COST. The lattice lane is the ONLY device that proves the
        // market-split family, and the doc names its own casualty: "pk1 has 45 > 24
        // rows" — an arithmetic disqualification, where every other exclusion it lists
        // is structural and permanent. `market_share_structure` (bab.rs) independently
        // classifies pk1 as the same family. Neither cap has an env override.
        //
        // CROSS-GUARDED so each counter reads a narrow population: rows-above-ceiling
        // on a column-tight model, and columns-above-ceiling on a row-tight one. A HIT
        // DOES NOT CERTIFY FAMILY MEMBERSHIP — only the post-compile counter does; read
        // this one as an upper bound, by mean-rows (mean-cols) per hit.
        if nr > MAX_ROWS && nc != 0 && nc <= MAX_COLS {
            crate::sepstat::gate_charge(crate::sepstat::GATE_LATTICE_FRONT_ROWS, nr as u64);
        }
        if nc > MAX_COLS && nr != 0 && nr <= MAX_ROWS {
            crate::sepstat::gate_charge(crate::sepstat::GATE_LATTICE_FRONT_COLS, nc as u64);
        }
        return None;
    }
    // Column census: every column is a fixed column, a free bounded-integer
    // column, or a free continuous slack candidate on `[0, ub)`.
    let mut class = vec![ColClass::Fixed; nc];
    let mut fixed_q: Vec<Option<BigRational>> = vec![None; nc];
    let mut col_lo = vec![0i64; nc];
    let mut col_up = vec![0i64; nc];
    let mut singleton_cols: Vec<(usize, i64)> = Vec::new();
    for j in 0..nc {
        let c = Col(j as u32);
        let (l, u) = model.col_bounds(c);
        if l == u {
            class[j] = ColClass::Fixed;
            fixed_q[j] = Some(exact(l)?);
        } else if model.col_kind(c).is_integral() {
            if !l.is_finite() || !u.is_finite() {
                return None; // an unbounded integer: no finite ball
            }
            // Integer hull of the bounds — exact, and sound because the
            // column only takes integer values.
            let li = exact(l)?.ceil().to_integer().to_i64()?;
            let ui = exact(u)?.floor().to_integer().to_i64()?;
            if li > ui {
                return None; // empty integer domain: not this device's verdict
            }
            if !(-MAX_INT_BOUND_ABS..=MAX_INT_BOUND_ABS).contains(&li)
                || !(-MAX_INT_BOUND_ABS..=MAX_INT_BOUND_ABS).contains(&ui)
            {
                return None;
            }
            if li == ui {
                class[j] = ColClass::Fixed;
                fixed_q[j] = Some(BigRational::from(BigInt::from(li)));
                singleton_cols.push((j, li));
            } else {
                class[j] = ColClass::Int;
                col_lo[j] = li;
                col_up[j] = ui;
            }
        } else {
            if l != 0.0 {
                return None; // a slack lives on [0, ub)
            }
            class[j] = ColClass::Cont;
        }
    }
    let int_cols: Vec<usize> = (0..nc).filter(|&j| class[j] == ColClass::Int).collect();
    let n0 = int_cols.len();
    if n0 < 2 {
        return None;
    }
    let mut int_pos = vec![usize::MAX; nc];
    for (k, &j) in int_cols.iter().enumerate() {
        int_pos[j] = k;
    }
    // A free continuous column must be the slack of EXACTLY ONE row; count first.
    let mut cont_rows = vec![0usize; nc];
    for i in 0..nr {
        let (coeffs, _, _) = model.row(Row(i as u32));
        for &(c, a) in coeffs {
            if a != 0.0 && class[c as usize] == ColClass::Cont {
                cont_rows[c as usize] += 1;
            }
        }
    }
    for j in 0..nc {
        if class[j] == ColClass::Cont && cont_rows[j] != 1 {
            return None; // a free continuous column not tied to exactly one row
        }
    }
    // Row census. Objective rows: an equality with ≥2 integer columns and one
    // free continuous unit-objective slack. The MPS reader may have scaled a
    // whole row by a power of two (markshare1's rhs 1116 > 1024, so its rows
    // arrive halved), so recover the ORIGINAL integer system by dividing each
    // such row through by its slack coefficient — which normalises the slack to
    // unit and cancels the scaling (`s_i = b_i − a_i·x` in original units
    // regardless). Constraint rows (no continuous column): clear denominators
    // by the LCM instead, then tighten to the exact integer interval.
    let mut a: Vec<Vec<i64>> = Vec::with_capacity(nr);
    let mut b: Vec<i64> = Vec::with_capacity(nr);
    let mut obj_rows: Vec<usize> = Vec::new();
    let mut slack_col: Vec<usize> = Vec::new();
    // Synthetic slack ranges, one per accepted inequality row: (row index into
    // `a`, slack range `up' − lo'`).
    let mut synth: Vec<(usize, i64)> = Vec::new();
    for i in 0..nr {
        let (coeffs, rlo, rup) = model.row(Row(i as u32));
        // Locate a free continuous slack and its (row-scaled) coefficient. Its
        // objective coefficient must be unit, so the objective is exactly Σ s_i.
        let mut slack: Option<(usize, f64)> = None;
        for &(c, coef) in coeffs {
            let cj = c as usize;
            if coef != 0.0 && class[cj] == ColClass::Cont {
                if model.obj_coeff(Col(c)) != 1.0 {
                    return None;
                }
                if slack.replace((cj, coef)).is_some() {
                    return None; // two free slacks in one row
                }
            }
        }
        if let Some((s, sc)) = slack {
            // ---- objective row: a·x + s = b, min contributes s --------------
            if rlo != rup || !rlo.is_finite() {
                return None; // an inequality/range row carrying the objective slack
            }
            if sc.partial_cmp(&0.0) != Some(std::cmp::Ordering::Greater) {
                return None; // slack must absorb the deficit side (markshare: +)
            }
            let mut nint = 0usize;
            let sc_q = exact(sc)?;
            let mut fixed_contrib = BigRational::zero();
            let mut arow = vec![0i64; n0];
            for &(c, coef) in coeffs {
                let cj = c as usize;
                if coef == 0.0 {
                    continue;
                }
                match class[cj] {
                    ColClass::Int => {
                        let ai_q = exact(coef)? / &sc_q;
                        if !ai_q.is_integer() {
                            return None;
                        }
                        let ai = ai_q.to_integer().to_i64()?;
                        arow[int_pos[cj]] = ai;
                        nint += 1;
                    }
                    ColClass::Cont => {
                        // the slack column itself (coef/sc == 1): nothing to record
                    }
                    ColClass::Fixed => {
                        // Fixed-column contribution in recovered units, exactly.  A
                        // tolerance-based integer cast is not enough here: the proof
                        // that Σs is integer requires the normalized system itself to
                        // be integer, not merely close to one.
                        fixed_contrib += (exact(coef)? / &sc_q) * fixed_q[cj].as_ref()?;
                    }
                }
            }
            if nint < 2 {
                return None;
            }
            // b_i = rhs/sc − fixed contribution, exactly integral.
            let bi = exact(rlo)? / &sc_q - fixed_contrib;
            if !bi.is_integer() {
                return None;
            }
            obj_rows.push(a.len());
            slack_col.push(s);
            b.push(bi.to_integer().to_i64()?);
            a.push(arow);
        } else {
            // ---- constraint row: pure integer/fixed, lo ≤ a·x + fc ≤ up -----
            use num_integer::Integer;
            let mut mult = BigInt::one();
            let mut terms: Vec<(usize, BigRational)> = Vec::new();
            let mut fixed_contrib = BigRational::zero();
            for &(c, coef) in coeffs {
                let cj = c as usize;
                if coef == 0.0 {
                    continue;
                }
                match class[cj] {
                    ColClass::Int => {
                        let q = exact(coef)?;
                        mult = mult.lcm(q.denom());
                        terms.push((int_pos[cj], q));
                    }
                    ColClass::Fixed => {
                        fixed_contrib += exact(coef)? * fixed_q[cj].as_ref()?;
                    }
                    ColClass::Cont => unreachable!("slack scan covered ColClass::Cont"),
                }
            }
            if terms.is_empty() {
                return None; // a constant row: nothing lattice-shaped here
            }
            if mult > BigInt::from(MAX_ROW_SCALE) || mult.is_zero() {
                return None;
            }
            let mult_q = BigRational::from(mult);
            let mut arow = vec![0i64; n0];
            for (p, q) in &terms {
                let v = q * &mult_q;
                debug_assert!(v.is_integer(), "LCM of denominators clears every term");
                arow[*p] = v.to_integer().to_i64()?;
            }
            // Box-implied exact range of a·x over the integer box.
            let mut min_ax = BigInt::zero();
            let mut max_ax = BigInt::zero();
            for (p, &v) in arow.iter().enumerate() {
                if v == 0 {
                    continue;
                }
                let j = int_cols[p];
                let t1 = BigInt::from(v) * BigInt::from(col_lo[j]);
                let t2 = BigInt::from(v) * BigInt::from(col_up[j]);
                min_ax += (&t1).min(&t2).clone();
                max_ax += t1.max(t2);
            }
            // Row bounds on a·x, scaled and net of the fixed contribution,
            // tightened to integers (a·x ∈ ℤ) and clamped to the box range.
            let base = &mult_q * &fixed_contrib;
            let blo = if rlo.is_finite() {
                (exact(rlo)? * &mult_q - &base)
                    .ceil()
                    .to_integer()
                    .max(min_ax.clone())
            } else {
                min_ax.clone()
            };
            let bup = if rup.is_finite() {
                (exact(rup)? * &mult_q - &base)
                    .floor()
                    .to_integer()
                    .min(max_ax.clone())
            } else {
                max_ax.clone()
            };
            if blo > bup {
                return None; // row infeasible over the box: not this device's verdict
            }
            if blo == min_ax && bup == max_ax {
                continue; // the box already implies this row: drop it
            }
            if blo == bup {
                // A forced equality: a·x = blo exactly.
                b.push(blo.to_i64()?);
                a.push(arow);
            } else {
                // a·x ∈ [blo, bup]  ⟺  a·x + t = bup, t ∈ [0, bup−blo] ∩ ℤ.
                let range = (&bup - &blo).to_i64()?;
                if range > MAX_SYNTH_SLACK_RANGE {
                    return None;
                }
                b.push(bup.to_i64()?);
                synth.push((a.len(), range));
                a.push(arow);
            }
        }
    }
    let m = a.len();
    if m == 0 {
        return None; // every row was box-implied: nothing to prove here
    }
    // The objective's NONCONSTANT portion lives entirely on the slacks: every
    // free integer column has objective 0, and every free continuous column was
    // proven above to be one of those slacks. Fixed-column terms and the model
    // offset are harmless constants; `prove` reports the full exact objective
    // value. With NO objective rows the model objective is constant — pure
    // feasibility mode.
    for &j in &int_cols {
        if model.obj_coeff(Col(j as u32)) != 0.0 {
            return None;
        }
    }
    // Append the synthetic slack columns to the lattice.
    let n = n0.checked_add(synth.len())?;
    if n > MAX_COLS {
        // FORGONE COST. The ONLY site in this lane that certifies market-split family
        // membership before refusing: control reaches here past the column census, the
        // continuous-slack uniqueness test, row compilation, integer-hull tightening
        // and the objective-purity loop. So every hit is an in-family model refused on
        // SIZE ALONE.
        //
        // EXPECT ZERO, and that is the point. `n0 <= nc <= MAX_COLS` (the front door
        // enforced it) and `synth.len() <= MAX_ROWS`, so `n <= 184` and reaching
        // `n > 160` needs `n0 >= 137` plus inequality rows compiling to slacks — the
        // historical all-equality markshare shape has `synth = 0` and can never get
        // here. A genuinely wide in-family model dies at the FRONT door, where
        // membership is unknown; that is what GATE_LATTICE_FRONT_COLS counts.
        crate::sepstat::gate_charge(crate::sepstat::GATE_LATTICE_POST_COLS, n as u64);
        return None;
    }
    let mut lo: Vec<i64> = int_cols.iter().map(|&j| col_lo[j]).collect();
    let mut up: Vec<i64> = int_cols.iter().map(|&j| col_up[j]).collect();
    let mut col_model: Vec<Option<usize>> = int_cols.iter().map(|&j| Some(j)).collect();
    for row in &mut a {
        row.resize(n, 0);
    }
    for (t, &(ri, range)) in synth.iter().enumerate() {
        a[ri][n0 + t] = 1;
        lo.push(0);
        up.push(range);
        col_model.push(None);
    }
    Some(MarketSplit {
        n,
        m,
        a,
        b,
        lo,
        up,
        col_model,
        obj_rows,
        slack_col,
        singleton_cols,
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LatticeSchedule {
    Disabled,
    Threads(usize),
    /// Test-only dispatch: like `Threads`, but force the BKZ block size β
    /// (the same lever `AY_MILP_LATTICE_BKZ` gives an operator) without
    /// mutating the process-wide environment while other lattice tests run in
    /// parallel.  β > `BKZ_ADAPTIVE_BETA` exercises the PRUNED oracle on
    /// kernels of any size.  Reduction quality only — every basis it can
    /// produce still passes the exact covolume/kernel guard.
    #[cfg(test)]
    ThreadsForcedBeta(usize, usize),
}

/// Public entry: if `model` is the markshare1-class shape and the lattice device
/// can decide its optimum is 0 or 1 within budget, return the proven
/// `Outcome::Optimal`; otherwise `None` (hand back to the normal search).
pub(crate) fn try_prove(model: &Model, deadline: Instant, opts: &SolveOpts) -> Option<Outcome> {
    let schedule = if crate::tune::on(crate::tune::Knob::NoLattice) {
        LatticeSchedule::Disabled
    } else {
        LatticeSchedule::Threads(lattice_threads(opts))
    };
    try_prove_configured(model, deadline, schedule)
}

/// Dispatch split out so tests can select the schedule without mutating the
/// process-wide environment while other lattice tests are proving in parallel.
fn try_prove_configured(
    model: &Model,
    deadline: Instant,
    schedule: LatticeSchedule,
) -> Option<Outcome> {
    let (threads, forced_beta) = match schedule {
        LatticeSchedule::Disabled => return None,
        LatticeSchedule::Threads(threads) => (threads.max(1), bkz_beta_override()),
        #[cfg(test)]
        LatticeSchedule::ThreadsForcedBeta(threads, beta) => (threads.max(1), Some(beta)),
    };
    let ms = detect(model)?;
    let trace = std::env::var_os("AY_MILP_TRACE").is_some();
    if trace {
        eprintln!(
            "AY_MILP_TRACE lattice: market-split shape {}x{} — building AHL reformulation",
            ms.m, ms.n
        );
    }
    // Never starve the normal search: the device may run at most HALF the
    // remaining budget, then aborts to `None` and hands the model back. On
    // markshare1 this is moot (the proof lands in ~1.4s); it only bites a
    // hypothetical hard market-split (optimum ≥ 2, or a large ball) that the
    // normal search would then get a fair share of the clock to attempt.
    let now = Instant::now();
    let sub_deadline = now + deadline.saturating_duration_since(now).mul_f64(0.5);
    let eng = Engine::build(&ms, sub_deadline, trace, threads, forced_beta)?;
    // REPLAY CLAIMS MUST NOT OUTLIVE A DECLINE. `prove` can file a sweep claim
    // and then still hand the model back (a witness hunt that finds nothing, an
    // overflow in the reconstruction). A claim left in the ledger would then
    // attach to whatever the NORMAL search later concluded — annotating a
    // certified verdict with someone else's trust. So the ledger is stashed
    // across the call and the device's own claims are committed only if it
    // actually returned a verdict.
    let stashed = replay_ledger::take();
    let out = eng.prove(model, &ms);
    let filed = replay_ledger::take();
    for c in stashed {
        replay_ledger::record(c);
    }
    if out.is_some() {
        for c in filed {
            replay_ledger::record(c);
        }
    }
    out
}

/// Closed `f64` interval with every operation rounded one ulp outward.  The
/// hardware operations are round-to-nearest; stepping the computed endpoint
/// outward encloses the corresponding real operation (including an exact
/// endpoint), which is the same directed-rounding license used by `ns.rs`.
#[derive(Clone, Copy, Debug)]
struct Interval {
    lo: f64,
    hi: f64,
}

impl Interval {
    fn from_rational(v: &BigRational) -> Option<Self> {
        let f = v.to_f64()?;
        if !f.is_finite() {
            return None;
        }
        let fv = BigRational::from_float(f)?;
        Some(if fv < *v {
            Self {
                lo: f,
                hi: f.next_up(),
            }
        } else if fv > *v {
            Self {
                lo: f.next_down(),
                hi: f,
            }
        } else {
            Self { lo: f, hi: f }
        })
    }

    fn add(self, rhs: Self) -> Option<Self> {
        if rhs.lo == 0.0 && rhs.hi == 0.0 {
            return Some(self);
        }
        if self.lo == 0.0 && self.hi == 0.0 {
            return Some(rhs);
        }
        let lo = (self.lo + rhs.lo).next_down();
        let hi = (self.hi + rhs.hi).next_up();
        (lo.is_finite() && hi.is_finite()).then_some(Self { lo, hi })
    }

    fn sub(self, rhs: Self) -> Option<Self> {
        if rhs.lo == 0.0 && rhs.hi == 0.0 {
            return Some(self);
        }
        let lo = (self.lo - rhs.hi).next_down();
        let hi = (self.hi - rhs.lo).next_up();
        (lo.is_finite() && hi.is_finite()).then_some(Self { lo, hi })
    }

    /// Multiply by an exactly-represented scalar.
    fn scale(self, scalar: f64) -> Option<Self> {
        if scalar == 0.0 {
            return Some(Self { lo: 0.0, hi: 0.0 });
        }
        let (lo, hi) = if scalar >= 0.0 {
            ((self.lo * scalar).next_down(), (self.hi * scalar).next_up())
        } else {
            ((self.hi * scalar).next_down(), (self.lo * scalar).next_up())
        };
        (lo.is_finite() && hi.is_finite()).then_some(Self { lo, hi })
    }

    /// General (sign-agnostic) interval product. Used once per face to build
    /// the box-prune anchor `base`; never on the per-node hot path.
    fn mul_general(self, rhs: Self) -> Option<Self> {
        let a = self.lo * rhs.lo;
        let b = self.lo * rhs.hi;
        let c = self.hi * rhs.lo;
        let d = self.hi * rhs.hi;
        let lo = a.min(b).min(c).min(d).next_down();
        let hi = a.max(b).max(c).max(d).next_up();
        (lo.is_finite() && hi.is_finite()).then_some(Self { lo, hi })
    }

    /// Product of two intervals already known nonnegative (distance² × norm).
    fn mul_nonnegative(self, rhs: Self) -> Option<Self> {
        debug_assert!(self.lo >= 0.0 && rhs.lo >= 0.0);
        let lo = (self.lo * rhs.lo).next_down().max(0.0);
        let hi = (self.hi * rhs.hi).next_up();
        (lo.is_finite() && hi.is_finite()).then_some(Self { lo, hi })
    }

    fn square(self) -> Option<Self> {
        if self.lo <= 0.0 && self.hi >= 0.0 {
            let m = self.lo.abs().max(self.hi.abs());
            let hi = (m * m).next_up();
            return hi.is_finite().then_some(Self { lo: 0.0, hi });
        }
        let a = self.lo * self.lo;
        let b = self.hi * self.hi;
        if !a.is_finite() || !b.is_finite() {
            return None;
        }
        Some(Self {
            lo: a.min(b).next_down().max(0.0),
            hi: a.max(b).next_up(),
        })
    }
}

/// Kill switch for the box-prefix prune. Set to any value to restore the
/// historical, radius-only sweep BYTE-IDENTICALLY (same node counts, same
/// verdicts, same witnesses).
const BOX_PRUNE_OFF_ENV: &str = "AY_MILP_NO_BOXPRUNE";

/// Face-independent tables for the BOX-PREFIX PRUNE (see `EnumState::rec`).
///
/// ## What it proves
///
/// Write the enumerated point as `x = x_d + K·y`. With `e_t` the Fincke–Pohst
/// center the loop already forms at level `t` (`tg[t] − partial[t][t]`, a
/// function of the STRICTLY HIGHER `y`s only) the exact identity
///
///   `x = base + Σ_t (y_t − e_t)·b*_t`,   `base := x_d + Σ_t tg_t·b*_t`
///
/// holds (`base = c − τ⊥`; it is the Babai continuation of the empty prefix,
/// NOT the integer prefix `x_d + Σ_{t≥L} y_t·k_t`). Splitting at level `L`,
/// everything with `t ≥ L` is already determined at the node, so
///
///   `x_k = C_k + Σ_{t<L} (y_t − e_t)·b*_t[k]`,
///   `C_k := base_k + Σ_{t≥L} (y_t − e_t)·b*_t[k]`.
///
/// The Fincke–Pohst invariant bounds what the UNASSIGNED levels may still
/// spend: any descendant leaf inside the enumeration ball satisfies
/// `Σ_{t<L} (y_t − e_t)²‖b*_t‖² ≤ radius − dist(node) =: rem`. Cauchy–Schwarz
/// on the two factors `(y_t − e_t)‖b*_t‖` and `b*_t[k]/‖b*_t‖` then gives the
/// RIGOROUS REACH BOUND
///
///   `|x_k − C_k| ≤ √(rem · S[L][k])`,  `S[L][k] := Σ_{t<L} b*_t[k]²/‖b*_t‖²`.
///
/// So if for some original coordinate `k` the center `C_k` sits farther than
/// that reach outside `[lo_k, up_k]`, NO completion of the remaining levels can
/// land the point in the box: the whole subtree is provably box-infeasible and
/// may be cut without touching the completeness of an `Empty` verdict. Every
/// float quantity below is rounded so the tested inequality is only ever
/// STRICTER than the exact one (see `EnumState::rec` for the error envelope).
struct BoxPrune {
    /// Outward `f64` enclosure of the exact GSO vector `b*_t[k]` (`dim × n`).
    /// Only used off the hot path, to build each face's `base`.
    bstar_i: Vec<Vec<Interval>>,
    /// Round-to-nearest midpoint of `bstar_i[t][k]` (`dim × n`), the hot loop's
    /// FMA multiplier. Its deviation from the exact `b*_t[k]` is covered by
    /// `bstar_halfw[t]`.
    bstar_mid: Vec<Vec<f64>>,
    /// `max_k max(|lo|,|hi|)` of `bstar_i[t][·]` — an outward bound on both
    /// `|b*_t[k]|` and `|bstar_mid[t][k]|`.
    bstar_absmax: Vec<f64>,
    /// `max_k` half-width of `bstar_i[t][·]`, rounded up.
    bstar_halfw: Vec<f64>,
    /// `√(S[l][k])` rounded UP, `l ∈ 0..=dim` (`S[0][·] = 0`: at a leaf the
    /// unassigned levels can contribute nothing).
    sqrt_s: Vec<Vec<f64>>,
    /// `max_k sqrt_s[l][k]`, for the O(1) error envelope.
    sqrt_s_max: Vec<f64>,
    /// The exact integer box as `f64` (both endpoints are exactly
    /// representable — `Engine::build` declines the prune otherwise).
    lo_f: Vec<f64>,
    up_f: Vec<f64>,
    /// `max_k max(|lo_k|, |up_k|)`, for the error envelope.
    bound_absmax: f64,
    /// `(dim + 8)·f64::EPSILON`, the linear rounding coefficient of the
    /// envelope, precomputed.
    eps_coeff: f64,
}

/// The reduced kernel lattice + exact GSO, shared across every face.
struct Engine {
    n: usize,
    /// Reduced kernel basis: `k[t]` is a vector in ℤ^n (length `n`), `t < dim`.
    k: Vec<Vec<i64>>,
    /// Kernel dimension `n − m`.
    dim: usize,
    /// Column-HNF unimodular matrix `U` (n×n) and rank, for particular solutions.
    u: Vec<Vec<BigInt>>,
    hh: Vec<Vec<BigInt>>, // A·U = [H | 0]; H = hh[:][:rank]
    rank: usize,
    /// Exact GSO of the reduced basis (for Babai): orthogonal vectors + sq norms.
    bstar_q: Vec<Vec<BigRational>>,
    cnorm_q: Vec<BigRational>,
    /// Outward-rounded mirrors of the exact GSO for the enumeration hot loop.
    /// These are enclosures, not point approximations: an `Empty` result may
    /// rely on their lower endpoints without trusting round-to-nearest.
    cnorm_i: Vec<Interval>,
    mu_i: Vec<Vec<Interval>>,
    /// Face-independent tables for the box-prefix prune. `None` disables it
    /// (kill switch, or a box whose endpoints are not exactly representable):
    /// the sweep then runs byte-identically to the historical radius-only one.
    box_prune: Option<BoxPrune>,
    /// Per-lattice-column integer bounds (copied from the compiled shape) —
    /// the exact box every candidate is adjudicated against.
    lo: Vec<i64>,
    up: Vec<i64>,
    /// EXACT box ball radius Σ((up−lo)/2)²: every integer point of the box
    /// lies within this squared distance of the box center (0/1 columns:
    /// exactly n/4, the historical binary sphere). Kept as a rational so
    /// `compute_target_geometry` can subtract the orthogonal residue exactly.
    radius_q: BigRational,
    /// Upper (outward-rounded) `f64` enclosure of `radius_q`, the belt the
    /// tightened per-face radius is clamped against.
    radius_f: f64,
    deadline: Instant,
    trace: bool,
    /// Worker-thread count for the parallel enumeration. `1` (or any tree with
    /// `dim <= 1`) takes the historical single-thread path byte-identically.
    threads: usize,
}

/// Resolve the enumeration worker count from the typed solve contract.
///
/// Deterministic solves always take the historical serial path. Otherwise
/// `SolveOpts::threads` is the requested budget, available CPUs are a ceiling,
/// and both resource-envelope variables are ceilings only: process-global
/// state may reduce a caller's typed budget but can never silently increase it.
/// A present malformed/non-positive ceiling fails closed to one worker.
fn lattice_threads(opts: &SolveOpts) -> usize {
    let available = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1);
    let nbcore = std::env::var_os("NBCORE");
    let lattice = std::env::var_os("AY_MILP_LATTICE_THREADS");
    resolve_lattice_threads(opts, available, nbcore.as_deref(), lattice.as_deref())
}

fn resolve_lattice_threads(
    opts: &SolveOpts,
    available: usize,
    nbcore: Option<&OsStr>,
    lattice: Option<&OsStr>,
) -> usize {
    if opts.determinism {
        return 1;
    }
    let mut threads = (opts.threads as usize).max(1).min(available.max(1));
    for ceiling in [nbcore, lattice].into_iter().flatten() {
        let parsed = ceiling
            .to_str()
            .and_then(|value| value.trim().parse::<usize>().ok())
            .filter(|&value| value > 0)
            .unwrap_or(1);
        threads = threads.min(parsed);
    }
    threads.max(1)
}

/// Build the face-independent box-prune tables, or `None` to run the
/// historical radius-only sweep.
///
/// Declines (fail-closed, never an abort) when the kill switch is set, when a
/// box endpoint is not an exact `f64`, or when any enclosure is non-finite —
/// the prune is an OPTIONAL accelerator, so refusing it is always safe.
fn build_box_prune(
    bstar_q: &[Vec<BigRational>],
    cnorm_i: &[Interval],
    lo: &[i64],
    up: &[i64],
    dim: usize,
    n: usize,
) -> Option<BoxPrune> {
    if std::env::var_os(BOX_PRUNE_OFF_ENV).is_some() {
        return None;
    }
    box_prune_tables(bstar_q, cnorm_i, lo, up, dim, n)
}

/// The table construction itself, with no environment lookup, so the
/// differential test can force the prune ON regardless of the ambient
/// kill-switch setting.
fn box_prune_tables(
    bstar_q: &[Vec<BigRational>],
    cnorm_i: &[Interval],
    lo: &[i64],
    up: &[i64],
    dim: usize,
    n: usize,
) -> Option<BoxPrune> {
    if dim == 0 || n == 0 || bstar_q.len() < dim || cnorm_i.len() < dim {
        return None;
    }
    // `f64` must represent every bound EXACTLY: the reach test compares against
    // `lo_f`/`up_f` directly, and a rounded endpoint could widen the box (safe)
    // or narrow it (UNSOUND). Requiring exactness removes the question.
    if lo
        .iter()
        .chain(up.iter())
        .any(|&v| v.unsigned_abs() > (1u64 << 53))
    {
        return None;
    }
    let mut bstar_i: Vec<Vec<Interval>> = Vec::with_capacity(dim);
    for row in bstar_q.iter().take(dim) {
        if row.len() < n {
            return None;
        }
        let mut r = Vec::with_capacity(n);
        for value in row.iter().take(n) {
            r.push(Interval::from_rational(value)?);
        }
        bstar_i.push(r);
    }
    let mut bstar_mid = Vec::with_capacity(dim);
    let mut bstar_absmax = Vec::with_capacity(dim);
    let mut bstar_halfw = Vec::with_capacity(dim);
    for row in &bstar_i {
        let mut mid = Vec::with_capacity(n);
        let mut amax = 0.0f64;
        let mut hw = 0.0f64;
        for iv in row {
            let m = (iv.lo + iv.hi) * 0.5;
            if !m.is_finite() {
                return None;
            }
            mid.push(m);
            amax = amax.max(iv.lo.abs().max(iv.hi.abs()));
            // Outward half-width around the ROUNDED midpoint, so
            // `|b*_t[k] − mid| ≤ hw` holds for the stored `mid` itself.
            hw = hw.max((iv.hi - m).max(m - iv.lo).next_up());
        }
        if !amax.is_finite() || !hw.is_finite() {
            return None;
        }
        bstar_mid.push(mid);
        bstar_absmax.push(amax);
        bstar_halfw.push(hw);
    }
    // S[l][k] = Σ_{t<l} b*_t[k]² / ‖b*_t‖², every step rounded UP so the stored
    // value is an upper bound on the exact Cauchy–Schwarz factor.
    let mut s = vec![vec![0.0f64; n]; dim + 1];
    for t in 0..dim {
        let denom = cnorm_i[t].lo;
        if denom.is_nan() || denom <= 0.0 {
            return None;
        }
        for kk in 0..n {
            let sq = bstar_i[t][kk].square()?.hi;
            let step = (sq / denom).next_up();
            let acc = (s[t][kk] + step).next_up();
            if !acc.is_finite() {
                return None;
            }
            s[t + 1][kk] = acc;
        }
    }
    let mut sqrt_s = Vec::with_capacity(dim + 1);
    let mut sqrt_s_max = Vec::with_capacity(dim + 1);
    for row in &s {
        let r: Vec<f64> = row.iter().map(|v| v.sqrt().next_up()).collect();
        let m = r.iter().fold(0.0f64, |a, &b| a.max(b));
        if !m.is_finite() {
            return None;
        }
        sqrt_s.push(r);
        sqrt_s_max.push(m);
    }
    let lo_f: Vec<f64> = lo.iter().take(n).map(|&v| v as f64).collect();
    let up_f: Vec<f64> = up.iter().take(n).map(|&v| v as f64).collect();
    if lo_f.len() != n || up_f.len() != n {
        return None;
    }
    let bound_absmax = lo_f
        .iter()
        .chain(up_f.iter())
        .fold(0.0f64, |a, &b| a.max(b.abs()));
    Some(BoxPrune {
        bstar_i,
        bstar_mid,
        bstar_absmax,
        bstar_halfw,
        sqrt_s,
        sqrt_s_max,
        lo_f,
        up_f,
        bound_absmax,
        eps_coeff: (dim as f64 + 8.0) * f64::EPSILON,
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FrontierLimits {
    target: usize,
    cap: usize,
}

/// Derive a complete-frontier item bound from both load-balancing demand and a
/// conservative 64 MiB payload envelope. Every checked-arithmetic failure
/// declines the parallel device instead of wrapping into an unenforced claim.
fn frontier_limits(dim: usize, n: usize, threads: usize) -> Option<FrontierLimits> {
    let desired = threads.checked_mul(LATTICE_FRONTIER_PER_THREAD)?;
    let per_thread_cap = desired.checked_mul(LATTICE_FRONTIER_TARGET_MULTIPLIER)?;
    let payload_per_item = size_of::<WorkItem>()
        .checked_add(dim.checked_mul(size_of::<i64>().checked_add(size_of::<Interval>())?)?)?
        // Box-prune payload: one `f64` per ORIGINAL coordinate (the `C` row the
        // worker resumes from). Charged unconditionally so the envelope holds
        // whether or not the prune is enabled.
        .checked_add(n.checked_mul(size_of::<f64>())?)?;
    let memory_cap = LATTICE_FRONTIER_MAX_BYTES.checked_div(payload_per_item.max(1))?;
    if memory_cap == 0 {
        return None;
    }
    let cap = per_thread_cap.min(memory_cap);
    Some(FrontierLimits {
        target: desired.min(cap),
        cap,
    })
}

fn adaptive_bkz_beta(kernel_dim: usize) -> usize {
    if kernel_dim >= BKZ_MIN_KERNEL_DIM {
        kernel_dim // full-dimension blocks, pruned oracle
    } else {
        2 // plain LLL
    }
}

/// Optional operator override for the BKZ block size: `AY_MILP_LATTICE_BKZ=<β>`
/// replaces the adaptive policy's β (values < 3 disable BKZ, i.e. plain LLL).
/// Like `AY_MILP_LATTICE_THREADS` this only steers WORK DONE — block size is
/// reduction quality; every produced basis still passes the exact
/// covolume/kernel guard before use.  Unset or unparsable keeps the policy.
fn bkz_beta_override() -> Option<usize> {
    std::env::var_os("AY_MILP_LATTICE_BKZ")?
        .to_str()?
        .trim()
        .parse::<usize>()
        .ok()
}

/// Whether the block-SVP oracle at block size `beta` uses the pruned bounding
/// profile.  One deterministic rule: the historical exact oracle up to β=34
/// (markshare2-class kernels stay byte-identical), pruning strictly above it
/// (where the exact oracle is intractable).
fn bkz_oracle_pruned(beta: usize) -> bool {
    beta > BKZ_ADAPTIVE_BETA
}

/// The adaptive policy, with LARGE kernels (dim ≥ `BKZ_LARGE_KERNEL_DIM`)
/// demoted to the proven β=34 exact path at EVERY solve slice — the
/// full-dimension pruned gamble measurably loses their verdicts (see
/// `BKZ_LARGE_KERNEL_DIM`).  Deliberately time-independent so the default
/// basis never depends on the machine's speed.  Medium kernels are never
/// demoted: their pruned reduction converges in well under a second and
/// measured at parity or better with verdicts preserved.  The
/// `AY_MILP_LATTICE_BKZ` override bypasses this demotion at the call site.
fn effective_bkz_beta(kernel_dim: usize) -> usize {
    let beta = adaptive_bkz_beta(kernel_dim);
    if kernel_dim >= BKZ_LARGE_KERNEL_DIM {
        BKZ_ADAPTIVE_BETA
    } else {
        beta
    }
}

/// Deterministic BKZ tour cap by kernel dimension — a measured product policy
/// (no environment override), like `adaptive_bkz_beta`.
///
/// More tours monotonically improve the basis (dim-53: Σ‖·‖² 1342→1273 from 4
/// to 8 tours), but on FEASIBLE faces the wall to the witness is its position
/// in the deterministic sweep, which re-rolls with every basis change. On the
/// dim-62 Cornuejols–Dawande family the face tree is ~1.1e10+ nodes and the
/// measured witness positions were: 2 tours → 5.4e9 (reachable), while 4/8/16
/// tours and β 36/38 variants all landed past 7e9–12e9 (unreachable in a
/// 120-s slice). Both frontier-order alternatives (reversed, outside-in
/// bidirectional) were measured and do NOT rescue the deeper bases — the
/// witness sits mid-frontier. Hence: small kernels take the strictly better
/// 8-tour basis; the dim-62-and-up family keeps the 2-tour basis whose witness
/// is measured reachable.
fn adaptive_bkz_tours(kernel_dim: usize, pruned: bool) -> u64 {
    if pruned {
        // The pruned full-dimension path terminates by convergence (an
        // insertion-free tour) or the deadline; this cap is a runaway stop
        // well past observed convergence.
        BKZ_TOURS_PRUNED
    } else if kernel_dim >= BKZ_FEW_TOURS_MIN_DIM {
        BKZ_TOURS_LARGE
    } else {
        BKZ_TOURS_SMALL
    }
}

/// Give BKZ a bounded share of the remaining device time.
///
/// The typed input keeps this product policy free of process-global overrides
/// and non-finite durations. For every positive `remaining`, the returned
/// budget is strictly smaller, reserving time for exact validation and face
/// enumeration.
fn bkz_budget(remaining: std::time::Duration, pruned: bool) -> std::time::Duration {
    let cap = if pruned {
        BKZ_LARGE_ABS_CAP_SECS
    } else {
        BKZ_ABS_CAP_SECS
    };
    remaining
        .mul_f64(BKZ_BUDGET_FRACTION)
        .min(std::time::Duration::from_secs_f64(cap))
}

/// Convert an exact kernel basis to the fixed-width representation used by the
/// enumerator and independently re-check every row against `A`.  A BKZ output
/// that is too wide or leaves the kernel is merely an unusable reduction; the
/// caller can still fall back to the already-validated LLL basis.
fn checked_kernel_basis_i64(
    basis: &[Vec<BigInt>],
    ms: &MarketSplit,
    deadline: Instant,
) -> Option<Vec<Vec<i64>>> {
    let dim = ms.n.checked_sub(ms.m)?;
    if basis.len() != dim || basis.iter().any(|row| row.len() != ms.n) {
        return None;
    }

    let mut converted = Vec::with_capacity(dim);
    for row in basis {
        if Instant::now() >= deadline {
            return None;
        }
        converted.push(row.iter().map(ToPrimitive::to_i64).collect::<Option<_>>()?);
    }

    for row in &converted {
        for a_row in &ms.a {
            if Instant::now() >= deadline {
                return None;
            }
            let mut dot = BigInt::zero();
            for (&a, &k) in a_row.iter().zip(row) {
                if a != 0 && k != 0 {
                    dot += BigInt::from(a) * BigInt::from(k);
                }
            }
            if !dot.is_zero() {
                return None;
            }
        }
    }
    Some(converted)
}

/// Accept a BKZ candidate only after exact covolume, fixed-width, and kernel
/// checks.  Every candidate failure falls back to the known LLL basis; it must
/// never turn an otherwise usable lattice proof into an early abort.
fn select_checked_kernel_basis(
    lll_basis: &[Vec<BigInt>],
    bkz_candidate: Option<&[Vec<BigInt>]>,
    ms: &MarketSplit,
    deadline: Instant,
    trace: bool,
) -> Option<(Vec<Vec<i64>>, bool)> {
    if let Some(candidate) = bkz_candidate {
        let gdl = gram_det(lll_basis, deadline);
        let gdc = gram_det(candidate, deadline);
        let preserves_covolume = match (&gdl, &gdc) {
            (Some(reference), Some(reduced)) => reference == reduced,
            _ => false,
        };
        if preserves_covolume {
            if let Some(converted) = checked_kernel_basis_i64(candidate, ms, deadline) {
                if trace {
                    eprintln!(
                        "AY_MILP_TRACE lattice: BKZ accepted — exact covolume and kernel preserved"
                    );
                }
                return Some((converted, true));
            }
        }
        if trace {
            // Distinguish the honest reasons so a decline is diagnosable: a real
            // covolume mismatch (would indicate a non-unimodular transform — must
            // never happen) versus the two benign cases (a gram_det that ran out
            // of budget, or a basis too wide for the i64 enumerator).
            let reason = if gdl.is_none() || gdc.is_none() {
                "validation out of budget (gram_det deadline)"
            } else if !preserves_covolume {
                "COVOLUME MISMATCH — non-unimodular transform (soundness bug!)"
            } else {
                "basis too wide for i64 enumerator / leaves kernel"
            };
            eprintln!(
                "AY_MILP_TRACE lattice: BKZ validation declined ({reason}) — falling back to LLL basis"
            );
        }
    }

    checked_kernel_basis_i64(lll_basis, ms, deadline).map(|basis| (basis, false))
}

/// File a replay claim for the solve running on this thread.
///
/// Deliberately a thin wrapper: the device cannot construct anything BUT a
/// replay claim, so there is no path from here to `SUCCINCT`.
fn file_replay(claim: ReplayClaim) {
    replay_ledger::record(claim);
}

impl Engine {
    /// Record an exhaustive-sweep claim.
    ///
    /// Everything a consumer needs to know that this is NOT a certificate:
    /// the method, the arithmetic the pruning rests on, the node count against
    /// the budget it would have declined at, and — the part a consumer will
    /// otherwise file a bug about — that the enumeration tree's SHAPE depends
    /// on the BKZ-reduced basis, and `bkz_budget` takes a fraction of REMAINING
    /// WALL CLOCK. A different machine or a different `--time-limit` produces a
    /// different basis and a different sweep. Re-running does not reproduce the
    /// object; it re-attempts the claim.
    fn file_sweep_replay(&self, claim: &str, nodes: u64) {
        let serial = self.threads <= 1 || self.dim <= 1;
        file_replay(ReplayClaim {
            claim: claim.into(),
            device: "lattice-cvp".into(),
            method: "ahl-hnf-lll+bkz+schnorr-euchner".into(),
            arithmetic: "outward-rounded-f64-interval".into(),
            // The serial sweep counts its nodes; the parallel one reports
            // through a shared envelope and is not attributed here. `unknown`
            // is written rather than a number that would be a guess.
            nodes_visited: if serial && nodes > 0 {
                Some(nodes)
            } else {
                None
            },
            node_budget: NODE_BUDGET,
            outcome: "exhausted".into(),
            nondeterminism: vec![
                "wall-clock-dependent-basis".into(),
                if serial {
                    "serial-sweep".into()
                } else {
                    "thread-count-dependent-work-split".into()
                },
            ],
            reproduce: format!(
                "ay-milp solve <model> --time-limit <secs>   # kernel dim {}, {} thread(s)",
                self.dim,
                self.threads.max(1)
            ),
            tcb: TCB.into(),
        });
    }

    fn build(
        ms: &MarketSplit,
        deadline: Instant,
        trace: bool,
        threads: usize,
        forced_beta: Option<usize>,
    ) -> Option<Engine> {
        let (n, m) = (ms.n, ms.m);
        // A as BigInt (m × n).
        let abig: Vec<Vec<BigInt>> =
            ms.a.iter()
                .map(|row| row.iter().map(|&v| BigInt::from(v)).collect())
                .collect();
        let (u, rank, hh) = col_hnf(&abig, m, n, deadline)?;
        if rank != m {
            return None; // rank-deficient equality system: out of scope
        }
        let dim = n - rank;
        if dim == 0 {
            return None;
        }
        // Raw kernel = columns rank..n of U (exact BigInt — A·U = [H|0] makes
        // every such column an exact kernel vector). LLL in BigInt so no integer
        // overflow can ever corrupt the lattice; the reduced result is tiny.
        let mut k0: Vec<Vec<BigInt>> = Vec::with_capacity(dim);
        for t in 0..dim {
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(u[i][rank + t].clone());
            }
            k0.push(v);
        }
        let t_lll0 = Instant::now();
        let lll_basis = lll(k0, deadline)?;
        if trace {
            eprintln!(
                "AY_MILP_TRACE lattice: initial LLL {:.3}s",
                t_lll0.elapsed().as_secs_f64()
            );
        }
        // Adaptive EXACT BKZ reduction on top of LLL: small kernels retain the
        // historical byte-identical LLL basis; MEDIUM kernels use
        // FULL-DIMENSION blocks with the PRUNED oracle (the exact oracle is
        // intractable at these block sizes); LARGE kernels (dim ≥
        // `BKZ_LARGE_KERNEL_DIM`) keep the proven exact BKZ(34).  The
        // deterministic policy can be overridden by `AY_MILP_LATTICE_BKZ`
        // (reduction quality only). BKZ only changes the BASIS, never
        // the lattice: every block insertion is an explicit UNIMODULAR integer
        // transform (verified invertible over ℤ inside `apply_block`). As an
        // independent soundness certificate we require the Gram determinant
        // (= covolume², a unimodular invariant) to be IDENTICAL before and
        // after; a mismatch means the lattice changed and we fall back to the
        // trusted LLL basis. Combined with the per-vector kernel check below
        // (`A·k = 0`), equal Gram det + full rank ⟹ the BKZ output is a basis
        // of the SAME lattice, so the emptiness enumeration is unchanged.
        // BKZ must STOP before the device deadline so the exact covolume/kernel
        // validation (and the subsequent face enumeration) has budget to run.
        // Otherwise a BKZ that runs to the deadline leaves gram_det with zero
        // time and it declines a perfectly valid partial reduction.
        let bkz_now = Instant::now();
        let remaining = deadline.saturating_duration_since(bkz_now);
        let beta = forced_beta.unwrap_or_else(|| effective_bkz_beta(lll_basis.len()));
        let pruned = bkz_oracle_pruned(beta);
        // The exact path terminates naturally (tour cap / convergence) in
        // ~0.6–3s on the whole family, so its budget is a pure safety net; the
        // pruned full-dimension path runs to convergence under the larger
        // pruned cap. A BKZ that stops mid-pass still returns a
        // unimodular-chain basis, which the Gram-det guard re-certifies
        // before use.
        let bkz_deadline = bkz_now
            .checked_add(bkz_budget(remaining, pruned))
            .unwrap_or(bkz_now);
        let bkz_candidate = if beta >= 3 && lll_basis.len() >= 2 {
            Some(bkz(
                lll_basis.clone(),
                beta,
                pruned,
                bkz_deadline,
                trace,
                threads,
            ))
        } else {
            None
        };
        if trace {
            eprintln!(
                "AY_MILP_TRACE lattice: BKZ wall {:.3}s",
                bkz_now.elapsed().as_secs_f64()
            );
        }
        let t_val = Instant::now();
        let (k, used_bkz) =
            select_checked_kernel_basis(&lll_basis, bkz_candidate.as_deref(), ms, deadline, trace)?;
        if trace {
            eprintln!(
                "AY_MILP_TRACE lattice: covolume/kernel validation {:.3}s",
                t_val.elapsed().as_secs_f64()
            );
        }
        // Exact GSO of the reduced basis. `gso_exact` speaks `BigInt` because the
        // root reformulation feeds it a kernel basis that has no `i64` promise;
        // the market-split basis is `i64` by construction and widens for free.
        let k_big: Vec<Vec<BigInt>> = k
            .iter()
            .map(|row| row.iter().copied().map(BigInt::from).collect())
            .collect();
        let (bstar_q, cnorm_q, mu_q) = gso_exact(&k_big, deadline)?;
        let cnorm_i: Vec<Interval> = cnorm_q
            .iter()
            .map(Interval::from_rational)
            .collect::<Option<_>>()?;
        if cnorm_i.iter().any(|v| v.lo <= 0.0) {
            return None;
        }
        let mu_i: Vec<Vec<Interval>> = mu_q
            .iter()
            .map(|r| {
                r.iter()
                    .map(Interval::from_rational)
                    .collect::<Option<Vec<_>>>()
            })
            .collect::<Option<_>>()?;
        let box_prune = build_box_prune(&bstar_q, &cnorm_i, &ms.lo, &ms.up, dim, n);
        if trace {
            eprintln!(
                "AY_MILP_TRACE lattice: box-prefix prune {}",
                if box_prune.is_some() { "ON" } else { "OFF" }
            );
            let norms: Vec<BigInt> = k
                .iter()
                .map(|v| v.iter().map(|&x| BigInt::from(x) * BigInt::from(x)).sum())
                .collect();
            let nrm: BigInt = norms.iter().cloned().sum();
            let mx = norms.into_iter().max().unwrap_or_else(BigInt::zero);
            let reduction = if used_bkz { "BKZ" } else { "LLL" };
            eprintln!(
                "AY_MILP_TRACE lattice: kernel dim {dim}, {reduction} basis Σ‖·‖²={nrm} max‖·‖²={mx}"
            );
        }
        // Exact enumeration radius: every integer point `x` of the box has
        // `(x_p − c_p)² ≤ ((up_p − lo_p)/2)²` per coordinate with `c` the box
        // center, so the ball of squared radius Σ((up−lo)/2)² around `c`
        // CONTAINS every box point. Computed exactly, then rounded OUTWARD
        // (upper endpoint) so float rounding can only widen — never shrink —
        // the sweep. For all-0/1 columns this is exactly n/4 (the historical
        // sphere), bit-identical to the previous `n as f64 / 4.0`.
        let mut radius_q = BigRational::zero();
        for p in 0..n {
            let h = BigRational::new(
                BigInt::from(ms.up[p]) - BigInt::from(ms.lo[p]),
                BigInt::from(2),
            );
            radius_q += &h * &h;
        }
        let radius_f = Interval::from_rational(&radius_q)?.hi;
        Some(Engine {
            n,
            k,
            dim,
            u,
            hh,
            rank,
            bstar_q,
            cnorm_q,
            cnorm_i,
            mu_i,
            box_prune,
            lo: ms.lo.clone(),
            up: ms.up.clone(),
            radius_q,
            radius_f,
            deadline,
            trace,
            threads,
        })
    }

    /// Solve `A x = d` for an integer `x` (or `None` if no integer solution).
    /// Uses `A·U = [H|0]`: solve `H z = d`, then `x = U·[z;0]`.
    fn particular(&self, ms: &MarketSplit, d: &[i64]) -> Option<Vec<BigInt>> {
        let db: Vec<BigInt> = d.iter().copied().map(BigInt::from).collect();
        hnf_particular(
            &self.hh,
            &self.u,
            ms.m,
            self.n,
            self.rank,
            &db,
            self.deadline,
        )
    }

    /// Babai nearest-plane: reduce `x_d` modulo the reduced lattice so its entries
    /// are small. Exact (`BigRational` GSO) — the raw `x_d` has ~1e31 entries.
    fn babai(&self, xd: &[BigInt]) -> Option<Vec<i64>> {
        if Instant::now() >= self.deadline {
            return None;
        }
        let mut x: Vec<BigRational> = xd.iter().map(|v| BigRational::from(v.clone())).collect();
        for i in (0..self.dim).rev() {
            if i & 7 == 0 && Instant::now() >= self.deadline {
                return None;
            }
            // c_i = <x, b*_i> / cnorm_i
            let mut num = BigRational::zero();
            for kk in 0..self.n {
                if !self.bstar_q[i][kk].is_zero() {
                    num += &x[kk] * &self.bstar_q[i][kk];
                }
            }
            let ci = &num / &self.cnorm_q[i];
            let q = round_rat(&ci);
            if !q.is_zero() {
                let qr = BigRational::from(q);
                for kk in 0..self.n {
                    let t = &qr * BigRational::from(BigInt::from(self.k[i][kk]));
                    x[kk] -= t;
                }
            }
        }
        // Now integral and small.
        // "Small after Babai" is a performance expectation, not a proof
        // premise.  An alien but structurally matching model may remain wider
        // than i64; decline it instead of panicking or truncating.
        x.iter().map(|v| v.to_integer().to_i64()).collect()
    }

    /// Exact GSO coordinates of `τ = c − x_d` (with `c` the box center, `c_p =
    /// (lo_p + up_p)/2`; for 0/1 columns exactly the historical `½·1`) and the
    /// tight projected radius, outward-enclosed once. Shared by the
    /// single-thread and parallel enumerations so both start from
    /// byte-identical centers and radii. `None` (→ `Aborted`) on deadline or a
    /// non-finite enclosure.
    fn compute_target_geometry(&self, xd: &[i64]) -> Option<(Vec<Interval>, f64)> {
        let dim = self.dim;
        let tau: Vec<BigRational> = xd
            .iter()
            .enumerate()
            .map(|(p, &x)| {
                BigRational::new(
                    BigInt::from(self.lo[p]) + BigInt::from(self.up[p]),
                    BigInt::from(2),
                ) - BigRational::from(BigInt::from(x))
            })
            .collect();
        let tau_norm = tau
            .iter()
            .fold(BigRational::zero(), |sum, value| sum + value * value);
        let mut projected_norm = BigRational::zero();
        let mut tg = Vec::with_capacity(dim);
        for i in 0..dim {
            if Instant::now() >= self.deadline {
                return None;
            }
            let mut dot = BigRational::zero();
            for (t, b) in tau.iter().zip(&self.bstar_q[i]) {
                if !t.is_zero() && !b.is_zero() {
                    dot += t * b;
                }
            }
            projected_norm += (&dot * &dot) / &self.cnorm_q[i];
            let q = dot / &self.cnorm_q[i];
            tg.push(Interval::from_rational(&q)?);
        }

        // TIGHT RADIUS × WIDENED BOX (the D-front composition). Every integer
        // point `x` of the box satisfies, per coordinate,
        // `(x_p − c_p)² ≤ ((up_p − lo_p)/2)²`, hence the full-space BALL bound
        // `‖x − c‖² ≤ R² := Σ((up−lo)/2)²` (= `radius_q`; for the all-0/1
        // shape this is an EQUALITY — the historical binary sphere n/4).
        // Write `x − c = K·y − τ` and decompose τ into its projection onto
        // span(K) and the orthogonal residue. Since `K·y − proj(τ) ∈ span(K)`
        // and `τ − proj(τ) ⊥ span(K)`, Pythagoras gives EXACTLY
        //
        //   ‖K·y − proj(τ)‖² = ‖x − c‖² − ‖τ − proj(τ)‖² ≤ R² − ‖τ − proj(τ)‖².
        //
        // The inequality direction is what a general box needs: the residue
        // subtraction never over-shrinks, because it is subtracted from an
        // UPPER bound on ‖x − c‖² (equality in the 0/1 case, ≤ otherwise).
        // The residue is constant for the whole face, so the outer shell is
        // provably free of box points. All terms above are exact rationals;
        // rounding the final radius upward (and clamping against the outward
        // enclosure `radius_f` of R², itself an upper bound) preserves every
        // feasible leaf — outward rounding can only ENLARGE the ball.
        let perpendicular_norm = &tau_norm - &projected_norm;
        if perpendicular_norm.is_negative() {
            // The exact orthogonal projection cannot have negative squared
            // norm. Decline if an internally inconsistent GSO ever violates
            // that invariant rather than enlarging or shrinking the proof set.
            return None;
        }
        let exact_radius = &self.radius_q - &perpendicular_norm;
        let radius = Interval::from_rational(&exact_radius)?.hi;
        if !radius.is_finite() {
            return None;
        }
        if self.trace {
            let untightened = self.radius_f;
            eprintln!(
                "AY_MILP_TRACE lattice: projected radius {radius} (box ball R\u{b2} {untightened})"
            );
        }
        Some((tg, radius.min(self.radius_f)))
    }

    /// A fresh per-enumeration mutable scratch state over the shared read-only
    /// GSO. `tg` is moved in (each worker owns its own clone), `y`/`partial`
    /// start cleared, and cancellation is off by default.
    fn fresh_state<'a>(
        &'a self,
        xd: &'a [i64],
        tg: Vec<Interval>,
        radius: f64,
        shared_nodes: Option<&'a AtomicU64>,
    ) -> EnumState<'a> {
        let dim = self.dim;
        let n = self.n;
        let zero = Interval { lo: 0.0, hi: 0.0 };
        // Per-face box-prune anchor `base_k = x_d[k] + Σ_t tg_t·b*_t[k]`
        // (= `c_k − τ⊥_k`), enclosed OUTWARD once; the hot loop then carries
        // only its rounded midpoint plus a scalar error budget. Failure to
        // enclose disables the prune for this sweep — never an abort.
        let (cflat, base_absmax, base_halfw, box_on) = match self.box_prune.as_ref() {
            Some(bp) => {
                let mut mid = vec![0.0f64; n];
                let mut absmax = 0.0f64;
                let mut halfw = 0.0f64;
                let mut ok = true;
                for (k, slot) in mid.iter_mut().enumerate() {
                    let mut acc = Interval {
                        lo: xd[k] as f64,
                        hi: xd[k] as f64,
                    };
                    for t in 0..dim {
                        match tg[t]
                            .mul_general(bp.bstar_i[t][k])
                            .and_then(|term| acc.add(term))
                        {
                            Some(next) => acc = next,
                            None => {
                                ok = false;
                                break;
                            }
                        }
                    }
                    if !ok {
                        break;
                    }
                    let m = (acc.lo + acc.hi) * 0.5;
                    if !m.is_finite() {
                        ok = false;
                        break;
                    }
                    *slot = m;
                    absmax = absmax.max(acc.lo.abs().max(acc.hi.abs()));
                    halfw = halfw.max((acc.hi - m).max(m - acc.lo).next_up());
                }
                if ok && absmax.is_finite() && halfw.is_finite() {
                    // Rows `0..dim` are scratch; row `dim` is the immutable
                    // `base` every level-`dim−1` candidate reads.
                    let mut flat = vec![0.0f64; (dim + 1) * n];
                    flat[dim * n..].copy_from_slice(&mid);
                    (flat, absmax, halfw, true)
                } else {
                    (Vec::new(), 0.0, 0.0, false)
                }
            }
            None => (Vec::new(), 0.0, 0.0, false),
        };
        EnumState {
            eng: self,
            xd,
            tg,
            radius,
            y: vec![0i64; dim],
            // Row `level` holds Σ_{j>level} y_j μ[j][k] for k≤level.
            // A child row is overwritten from its immutable parent row for
            // every candidate, so interval widths never grow from add/subtract
            // restoration roundoff.
            partial: vec![vec![zero; dim]; dim],
            cflat,
            base_absmax,
            base_halfw,
            box_on,
            nodes: 0,
            node_cap: NODE_BUDGET,
            shared_nodes,
            shared_budget: NODE_BUDGET.saturating_mul(self.threads.max(1) as u64),
            reserved: 0,
            aborted: false,
            capped: false,
            cancel: None,
            cancelled: false,
        }
    }

    /// Route to the single-thread or parallel enumeration. `threads <= 1` (or a
    /// degenerate `dim <= 1`) keeps the exact historical single-thread sweep.
    fn enumerate(&self, xd: &[i64]) -> EnumResult {
        if self.threads <= 1 || self.dim <= 1 {
            self.enumerate_serial(xd)
        } else {
            self.enumerate_parallel(xd)
        }
    }

    /// Full-budget serial enumeration used for proof-bearing faces.
    fn enumerate_serial(&self, xd: &[i64]) -> EnumResult {
        self.enumerate_serial_with_cap(xd, NODE_BUDGET).0
    }

    /// Serial enumeration with a retryable soft cap. `Empty` is returned only
    /// after a complete sweep; reaching `node_cap < NODE_BUDGET` is the
    /// distinct, inconclusive `Capped` result. The proof face always calls this
    /// with `NODE_BUDGET`; witness-only faces may use smaller caps so one hard
    /// face cannot starve later faces that contain a cheap exact witness.
    ///
    /// The visited-node count lets the completed proof face calibrate the
    /// initial witness cap without a second pass.
    fn enumerate_serial_with_cap(&self, xd: &[i64], node_cap: u64) -> (EnumResult, u64) {
        if Instant::now() >= self.deadline {
            return (EnumResult::Aborted, 0);
        }
        let dim = self.dim;
        let Some((tg, radius)) = self.compute_target_geometry(xd) else {
            return (EnumResult::Aborted, 0);
        };
        let zero = Interval { lo: 0.0, hi: 0.0 };
        let mut st = self.fresh_state(xd, tg, radius, None);
        st.node_cap = node_cap.min(NODE_BUDGET);
        let found = st.rec(dim - 1, zero, 0.0, 0.0);
        if self.trace {
            let status = if st.aborted {
                "ABORTED"
            } else if found.is_some() {
                "FEASIBLE"
            } else if st.capped {
                "CAPPED"
            } else {
                "EMPTY"
            };
            eprintln!(
                "AY_MILP_TRACE lattice: Fincke-Pohst enumeration visited {} nodes ({status})",
                st.nodes
            );
        }
        let result = if st.aborted {
            EnumResult::Aborted
        } else if let Some(y) = found {
            EnumResult::Feasible(y)
        } else if st.capped {
            EnumResult::Capped
        } else {
            EnumResult::Empty
        };
        (result, st.nodes)
    }

    /// Parallel Fincke–Pohst enumeration. Enumerate the top DFS levels
    /// single-threaded into a frontier of INDEPENDENT subtrees (a complete
    /// partition of the serial sweep — every non-pruned node lies under exactly
    /// one frontier item), then hand the subtrees to `threads` scoped workers
    /// via a shared atomic work-index. Each worker owns its `EnumState` scratch;
    /// the Engine's reduced basis / GSO is borrowed read-only by all.
    ///
    /// COMBINE (sound): the face is `Empty` iff EVERY worker completes EVERY
    /// item it pulls with no witness (i.e. no worker aborted); a witness from
    /// any worker makes the face `Feasible`; any abort (deadline/budget/interval
    /// overflow) with no witness makes it `Aborted` — NEVER `Empty`.
    fn enumerate_parallel(&self, xd: &[i64]) -> EnumResult {
        if Instant::now() >= self.deadline {
            return EnumResult::Aborted;
        }
        let dim = self.dim;
        let Some((tg, radius)) = self.compute_target_geometry(xd) else {
            return EnumResult::Aborted;
        };
        let zero = Interval { lo: 0.0, hi: 0.0 };

        // --- Frontier generation (single-threaded, deterministic) -----------
        // Enumerate the top `split_levels` levels EXACTLY as the serial sweep
        // would (same intervals, same pruning, same radius) and collect the
        // resulting subtree roots at `stop_level = dim-1-split_levels`.
        // Iterative deepening: split one more level while too few items exist
        // for good load balance. The shared node counter charges EVERY pass,
        // and the item cap bounds a bushy level before it can consume more than
        // the declared memory envelope.
        let Some(limits) = frontier_limits(dim, self.n, self.threads) else {
            return EnumResult::Aborted;
        };
        let shared_nodes = AtomicU64::new(0);
        let mut items: Vec<WorkItem> = Vec::new();
        let mut stop_level = dim - 1;
        for split in 1..dim {
            let sl = dim - 1 - split;
            let mut st = self.fresh_state(xd, tg.clone(), radius, Some(&shared_nodes));
            // The previous, shallower partition is no longer useful once this
            // pass starts. Clear it first so iterative deepening never retains
            // two capped frontiers at once.
            items.clear();
            st.collect(dim - 1, zero, sl, &mut items, limits.cap, 0.0, 0.0);
            if st.aborted {
                return EnumResult::Aborted;
            }
            stop_level = sl;
            if items.len() >= limits.target || sl == 0 {
                break;
            }
        }
        let generation_nodes = shared_nodes.load(Ordering::Relaxed);
        if items.is_empty() {
            // The top-level sweep pruned everything: the ball is empty.
            if self.trace {
                eprintln!("AY_MILP_TRACE lattice: parallel enumeration — top level empty (EMPTY)");
            }
            return EnumResult::Empty;
        }

        // --- Parallel processing of the frontier ----------------------------
        let next_idx = AtomicUsize::new(0);
        let found = AtomicBool::new(false);
        let aborted = AtomicBool::new(false);
        // Nondeterministic schedules may publish any exact witness. The typed
        // deterministic contract never reaches this path.
        let best: Mutex<Option<(usize, Vec<i64>)>> = Mutex::new(None);
        let nthreads = self.threads.min(items.len()).max(1);
        std::thread::scope(|scope| {
            let mut handles = Vec::with_capacity(nthreads);
            for worker in 0..nthreads {
                let name = format!("ay-lattice-{worker}");
                match std::thread::Builder::new()
                    .name(name)
                    .spawn_scoped(scope, || {
                        loop {
                            if found.load(Ordering::Acquire) || aborted.load(Ordering::Acquire) {
                                break;
                            }
                            let Some(idx) = next_work_index(&next_idx, items.len()) else {
                                break;
                            };
                            let item = &items[idx];
                            let mut st =
                                self.fresh_state(xd, tg.clone(), radius, Some(&shared_nodes));
                            for (offset, &value) in item.y_upper.iter().enumerate() {
                                st.y[stop_level + 1 + offset] = value;
                            }
                            for (column, &interval) in item.partial_row.iter().enumerate() {
                                st.partial[stop_level][column] = interval;
                            }
                            st.seed_box_row(stop_level, &item.c_row);
                            st.cancel = Some(&found);
                            let hit = st.rec(stop_level, item.dist, item.box_g, item.box_h);
                            match hit {
                                Some(y) => {
                                    let Ok(mut guard) = best.lock() else {
                                        aborted.store(true, Ordering::Release);
                                        break;
                                    };
                                    match guard.as_ref() {
                                        Some((best_index, _)) if *best_index <= idx => {}
                                        _ => *guard = Some((idx, y)),
                                    }
                                    found.store(true, Ordering::Release);
                                    break;
                                }
                                None => {
                                    if st.cancelled {
                                        // A confirmed witness exists elsewhere;
                                        // this partial subtree need not finish.
                                        break;
                                    }
                                    if st.aborted {
                                        aborted.store(true, Ordering::Release);
                                        break;
                                    }
                                    // Subtree fully swept, empty: pull the next
                                    // complete work item.
                                }
                            }
                        }
                    }) {
                    Ok(handle) => handles.push(handle),
                    Err(_) => {
                        aborted.store(true, Ordering::Release);
                        break;
                    }
                }
            }
            for handle in handles {
                join_lattice_worker(handle, &aborted);
            }
        });

        let witness = match best.into_inner() {
            Ok(best) => best.map(|(_, y)| y),
            Err(_) => {
                aborted.store(true, Ordering::Release);
                None
            }
        };
        if self.trace {
            let status = if witness.is_some() {
                "FEASIBLE"
            } else if aborted.load(Ordering::Acquire) {
                "ABORTED"
            } else {
                "EMPTY"
            };
            eprintln!(
                "AY_MILP_TRACE lattice: parallel Fincke-Pohst — {} frontier items (stop_level {stop_level}, gen {generation_nodes} nodes) across {nthreads} threads, {} total nodes ({status})",
                items.len(),
                shared_nodes.load(Ordering::Relaxed)
            );
        }
        combine_parallel(witness, aborted.load(Ordering::Acquire))
    }

    /// Find a value-1 witness: a box point of some face `A x = b − e_k`
    /// (slack 1 in row `k`, 0 elsewhere — objective exactly 1 for EVERY such
    /// witness, so any face's hit proves optimum ≤ 1). Returns
    /// `(k, y, xd_k)` for the winning face, or `None` when every face was
    /// COMPLETELY swept empty (optimum ≥ 2) or the hunt aborted.
    ///
    /// The single-thread engine probes each face under a soft cap, then
    /// iteratively doubles the cap for every still-inconclusive face. Thus an
    /// expensive early face cannot starve a cheap witness on a later face.
    /// `Capped` is never treated as empty, and a face at the hard ceiling must
    /// finish or abort. A multi-thread engine instead prepares ALL faces and
    /// sweeps them CONCURRENTLY through one shared worker pool: their frontier
    /// items are interleaved round-robin and the first exact witness cancels
    /// the remaining sweeps. Both routes are sound because the optimum-≤-1
    /// half of the proof needs only ONE exact witness — the EMPTY status of the
    /// other faces is not load-bearing (the optimum-≥-1 half rests solely on
    /// the objective-0 face's complete sweep, which happened before this call).
    fn witness_hunt(
        &self,
        ms: &MarketSplit,
        serial_initial_cap: u64,
    ) -> Option<(usize, Vec<i64>, Vec<i64>)> {
        if self.threads <= 1 || self.dim <= 1 {
            let (k, y, xd, capped_runs) = self.witness_hunt_serial(ms, serial_initial_cap)?;
            if self.trace && capped_runs > 0 {
                eprintln!(
                    "AY_MILP_TRACE lattice: retained {capped_runs} inconclusive witness-face runs across deepening"
                );
            }
            return Some((k, y, xd));
        }
        // Prepare every face: particular solution, Babai reduction. A face
        // whose rhs has no integer solution at all is trivially empty and
        // dropped; a Babai failure (deadline / width) declines the device,
        // as it always has.
        let mut faces: Vec<(usize, Vec<i64>)> = Vec::new();
        for &k in &ms.obj_rows {
            let mut d = ms.b.clone();
            d[k] = d[k].checked_sub(1)?;
            let Some(xdk) = self.particular(ms, &d) else {
                continue;
            };
            faces.push((k, self.babai(&xdk)?));
        }
        match self.enumerate_faces(&faces) {
            FaceSweep::Witness { pos, y } => {
                let (k, xd) = faces.swap_remove(pos);
                Some((k, y, xd))
            }
            FaceSweep::AllEmpty | FaceSweep::Aborted => None,
        }
    }

    /// Serial, fair witness ladder. The diagnostic count in the return value is
    /// used by tests and tracing to pin that capped faces remained live across
    /// retries instead of being mistaken for empty.
    fn witness_hunt_serial(
        &self,
        ms: &MarketSplit,
        initial_cap: u64,
    ) -> Option<(usize, Vec<i64>, Vec<i64>, usize)> {
        let mut cap = initial_cap.clamp(1, NODE_BUDGET);
        let mut pending: Vec<(usize, Vec<i64>)> = Vec::new();
        let mut capped_runs = 0usize;

        // Faces range over OBJECTIVE rows only — constraint rows hold exactly
        // on every face, so b−e_k is meaningless there.
        for &k in &ms.obj_rows {
            let mut d = ms.b.clone();
            d[k] = d[k].checked_sub(1)?;
            let Some(xdk) = self.particular(ms, &d) else {
                continue;
            };
            let xdk = self.babai(&xdk)?;
            match self.enumerate_serial_with_cap(&xdk, cap).0 {
                EnumResult::Feasible(y) => return Some((k, y, xdk, capped_runs)),
                EnumResult::Empty => {}
                EnumResult::Capped => {
                    capped_runs += 1;
                    pending.push((k, xdk));
                }
                EnumResult::Aborted => return None,
            }
        }

        while !pending.is_empty() {
            let next_cap = cap.saturating_mul(2).min(NODE_BUDGET);
            if next_cap <= cap {
                // At the hard ceiling a sweep must complete or abort, never
                // remain softly capped. Guard the termination invariant.
                return None;
            }
            cap = next_cap;
            let mut still_pending = Vec::with_capacity(pending.len());
            for (k, xdk) in pending {
                match self.enumerate_serial_with_cap(&xdk, cap).0 {
                    EnumResult::Feasible(y) => return Some((k, y, xdk, capped_runs)),
                    EnumResult::Empty => {}
                    EnumResult::Capped => {
                        capped_runs += 1;
                        still_pending.push((k, xdk));
                    }
                    EnumResult::Aborted => return None,
                }
            }
            pending = still_pending;
        }
        None // all faces empty ⟹ optimum ≥ 2: hand back
    }

    /// Concurrent sweep of several faces through ONE shared worker pool.
    /// Per face this reproduces `enumerate_parallel` exactly — same target
    /// geometry, same frontier generation (identical iterative deepening,
    /// identical intervals and pruning, identical item cap), same per-item
    /// worker arithmetic, and a per-face shared node envelope (each face gets
    /// the same `NODE_BUDGET` the sequential ladder would grant its own
    /// enumeration) — but the items of all faces are interleaved round-robin
    /// so every face's near-center (most witness-likely, by the
    /// Schnorr–Euchner ordering) items are reached early, and one confirmed
    /// witness cancels everything still running.
    ///
    /// COMBINE (sound): `Witness` requires an exact `box_ok`-verified point;
    /// `AllEmpty` requires EVERY item of EVERY face completely swept with no
    /// witness, no cancellation and no abort — the same completeness
    /// invariant as running `enumerate_parallel` per face and and-ing the
    /// `Empty` results; any abort without a witness is `Aborted`, never
    /// `AllEmpty`.
    fn enumerate_faces(&self, faces: &[(usize, Vec<i64>)]) -> FaceSweep {
        struct Prep {
            /// Index into `faces`.
            pos: usize,
            stop_level: usize,
            tg: Vec<Interval>,
            radius: f64,
            items: Vec<WorkItem>,
            /// Per-face node envelope, spanning this face's frontier passes
            /// and every worker subtree (the same budget contract as
            /// `enumerate_parallel`).
            shared: AtomicU64,
        }
        if faces.is_empty() {
            return FaceSweep::AllEmpty;
        }
        // Single face: the plain parallel sweep is the same computation.
        if faces.len() == 1 {
            return match self.enumerate(&faces[0].1) {
                EnumResult::Feasible(y) => FaceSweep::Witness { pos: 0, y },
                EnumResult::Empty => FaceSweep::AllEmpty,
                EnumResult::Capped | EnumResult::Aborted => FaceSweep::Aborted,
            };
        }
        let dim = self.dim;
        let zero = Interval { lo: 0.0, hi: 0.0 };
        let Some(limits) = frontier_limits(dim, self.n, self.threads) else {
            return FaceSweep::Aborted;
        };
        // --- Frontier generation per face (single-threaded, deterministic,
        // identical to `enumerate_parallel`'s) --------------------------------
        let mut preps: Vec<Prep> = Vec::new();
        for (pos, (_k, xd)) in faces.iter().enumerate() {
            if Instant::now() >= self.deadline {
                return FaceSweep::Aborted;
            }
            let Some((tg, radius)) = self.compute_target_geometry(xd) else {
                return FaceSweep::Aborted;
            };
            let shared = AtomicU64::new(0);
            let mut items: Vec<WorkItem> = Vec::new();
            let mut stop_level = dim - 1;
            for split in 1..dim {
                let sl = dim - 1 - split;
                let mut st = self.fresh_state(xd, tg.clone(), radius, Some(&shared));
                items.clear();
                st.collect(dim - 1, zero, sl, &mut items, limits.cap, 0.0, 0.0);
                if st.aborted {
                    return FaceSweep::Aborted;
                }
                stop_level = sl;
                if items.len() >= limits.target || sl == 0 {
                    break;
                }
            }
            // A face whose top-level sweep pruned everything is already
            // proven empty: it simply contributes no items.
            preps.push(Prep {
                pos,
                stop_level,
                tg,
                radius,
                items,
                shared,
            });
        }
        // Round-robin interleaving, preserving each face's internal
        // (Schnorr–Euchner, near-center-first) item order.
        let mut order: Vec<(usize, usize)> = Vec::new();
        let max_items = preps.iter().map(|p| p.items.len()).max().unwrap_or(0);
        for r in 0..max_items {
            for (pi, p) in preps.iter().enumerate() {
                if r < p.items.len() {
                    order.push((pi, r));
                }
            }
        }
        if order.is_empty() {
            if self.trace {
                eprintln!(
                    "AY_MILP_TRACE lattice: concurrent face hunt — every top level empty (ALL EMPTY)"
                );
            }
            return FaceSweep::AllEmpty;
        }

        // --- Shared worker pool over the interleaved items -------------------
        let next_idx = AtomicUsize::new(0);
        let found = AtomicBool::new(false);
        let aborted = AtomicBool::new(false);
        // Keep the witness from the lowest interleaved position among those
        // that report (every witness has objective value exactly 1, so any
        // choice is sound; nondeterministic schedules may publish any of them
        // — the typed deterministic contract never reaches this path).
        let best: Mutex<Option<(usize, usize, Vec<i64>)>> = Mutex::new(None);
        let nthreads = self.threads.min(order.len()).max(1);
        std::thread::scope(|scope| {
            let mut handles = Vec::with_capacity(nthreads);
            for worker in 0..nthreads {
                let name = format!("ay-lattice-hunt-{worker}");
                match std::thread::Builder::new()
                    .name(name)
                    .spawn_scoped(scope, || {
                        loop {
                            if found.load(Ordering::Acquire) || aborted.load(Ordering::Acquire) {
                                break;
                            }
                            let Some(idx) = next_work_index(&next_idx, order.len()) else {
                                break;
                            };
                            let (pi, ii) = order[idx];
                            let p = &preps[pi];
                            let item = &p.items[ii];
                            let mut st = self.fresh_state(
                                &faces[p.pos].1,
                                p.tg.clone(),
                                p.radius,
                                Some(&p.shared),
                            );
                            for (offset, &value) in item.y_upper.iter().enumerate() {
                                st.y[p.stop_level + 1 + offset] = value;
                            }
                            for (column, &interval) in item.partial_row.iter().enumerate() {
                                st.partial[p.stop_level][column] = interval;
                            }
                            st.seed_box_row(p.stop_level, &item.c_row);
                            st.cancel = Some(&found);
                            let hit = st.rec(p.stop_level, item.dist, item.box_g, item.box_h);
                            match hit {
                                Some(y) => {
                                    let Ok(mut guard) = best.lock() else {
                                        aborted.store(true, Ordering::Release);
                                        break;
                                    };
                                    match guard.as_ref() {
                                        Some((best_index, _, _)) if *best_index <= idx => {}
                                        _ => *guard = Some((idx, p.pos, y)),
                                    }
                                    found.store(true, Ordering::Release);
                                    break;
                                }
                                None => {
                                    if st.cancelled {
                                        // A confirmed witness exists elsewhere;
                                        // this partial subtree need not finish.
                                        // NOT an abort.
                                        break;
                                    }
                                    if st.aborted {
                                        aborted.store(true, Ordering::Release);
                                        break;
                                    }
                                    // Subtree fully swept, empty: pull the next
                                    // complete work item.
                                }
                            }
                        }
                    }) {
                    Ok(handle) => handles.push(handle),
                    Err(_) => {
                        aborted.store(true, Ordering::Release);
                        break;
                    }
                }
            }
            for handle in handles {
                join_lattice_worker(handle, &aborted);
            }
        });

        let witness = match best.into_inner() {
            Ok(best) => best,
            Err(_) => {
                aborted.store(true, Ordering::Release);
                None
            }
        };
        if self.trace {
            let status = match &witness {
                Some((_, pos, _)) => format!("FEASIBLE b−e_{}", faces[*pos].0),
                None if aborted.load(Ordering::Acquire) => "ABORTED".to_string(),
                None => "ALL EMPTY".to_string(),
            };
            let total_nodes: u64 = preps.iter().map(|p| p.shared.load(Ordering::Relaxed)).sum();
            eprintln!(
                "AY_MILP_TRACE lattice: concurrent face hunt — {} faces, {} interleaved items across {nthreads} threads, {total_nodes} total nodes ({status})",
                preps.len(),
                order.len(),
            );
        }
        if let Some((_, pos, y)) = witness {
            FaceSweep::Witness { pos, y }
        } else if aborted.load(Ordering::Acquire) {
            FaceSweep::Aborted
        } else {
            FaceSweep::AllEmpty
        }
    }

    /// Run the whole proof and, on success, build the exact outcome.
    ///
    /// With objective rows present: objective-0 face empty + a value-1 face
    /// witness ⟹ `Optimal 1`; a value-0 witness ⟹ `Optimal 0`; anything
    /// else hands back (`None`).
    ///
    /// PURE FEASIBILITY MODE (`obj_rows` empty — the model objective is
    /// constant): the model's integer feasible points are in EXACT BIJECTION
    /// with the lattice points of the face `A x = b` inside the box — every
    /// model column is a lattice column, a recorded fixed/singleton column, and
    /// every model row was compiled exactly (equality rows verbatim; pure-
    /// integer inequality rows via the synthetic slack `t = up' − a·x ∈
    /// [0, up'−lo']`; box-implied rows dropped only when the column bounds
    /// already entail them). A COMPLETE empty sweep of the face (the only way
    /// `Empty` is ever reported) therefore proves the model INFEASIBLE; a
    /// witness proves feasibility and, the objective being constant, yields
    /// `Optimal` after the independent `check_point` re-check.
    fn prove(&self, model: &Model, ms: &MarketSplit) -> Option<Outcome> {
        // Objective-0 face: A x = b.
        let xd0 = self.particular(ms, &ms.b);
        let feasibility_mode = ms.obj_rows.is_empty();
        // In feasibility mode "no integer particular solution of A x = b"
        // already proves the face (hence the model) empty — the coset is not
        // even inhabited by unconstrained integers.
        let Some(xd0) = xd0 else {
            if feasibility_mode {
                // `particular` returns None on deadline as well as on a proven
                // inconsistency; only the latter may claim INFEASIBLE. If the
                // deadline has still not passed NOW, none of `particular`'s
                // internal deadline checks can have fired during its run.
                if Instant::now() >= self.deadline {
                    return None;
                }
                if self.trace {
                    eprintln!(
                        "AY_MILP_TRACE lattice: A x = b has no integer solution — INFEASIBLE"
                    );
                }
                // This verdict carries NO exported certificate, so it files a
                // replay claim: the only honest thing a device can do when its
                // proof is "I ran a computation". Unlike the CVP sweeps below
                // this one IS deterministic (exact BigInt column-HNF, no
                // floating point and no wall-clock-dependent reduction), and it
                // is also the one replay claim here that HAS a short
                // certificate in theory — a rational `u` with `uᵀA` integral
                // and `uᵀb` non-integral. Not built yet; recorded as trusted
                // rather than dressed up as proved.
                file_replay(ReplayClaim {
                    claim: "coset-inconsistent".into(),
                    device: "lattice-hnf".into(),
                    method: "column-hnf-exact-bigint".into(),
                    arithmetic: "exact-bigint".into(),
                    nodes_visited: None,
                    node_budget: 0,
                    outcome: "inconsistent".into(),
                    nondeterminism: Vec::new(),
                    reproduce: "ay-milp solve <model>   # deterministic: exact HNF, no reduction"
                        .into(),
                    tcb: TCB.into(),
                });
                return Some(Outcome::Infeasible {
                    cert: None,
                    tree_cert: None,
                });
            }
            return None;
        };
        let xd0 = self.babai(&xd0)?;
        // The proof-bearing objective-0 face always gets the full hard budget;
        // only witness-only faces may be softly capped. Capture the completed
        // serial sweep's node count to calibrate their first fair-share probe.
        let (zero_result, zero_nodes) = if self.threads <= 1 || self.dim <= 1 {
            self.enumerate_serial_with_cap(&xd0, NODE_BUDGET)
        } else {
            (self.enumerate_parallel(&xd0), 0)
        };
        let (opt, witness_y, witness_xd) = match zero_result {
            EnumResult::Feasible(y) => (0i64, y, xd0),
            EnumResult::Empty => {
                if feasibility_mode {
                    if self.trace {
                        eprintln!(
                            "AY_MILP_TRACE lattice: feasibility face PROVEN EMPTY — model INFEASIBLE"
                        );
                    }
                    self.file_sweep_replay("feasibility-face-empty", zero_nodes);
                    return Some(Outcome::Infeasible {
                        cert: None,
                        tree_cert: None,
                    });
                }
                if self.trace {
                    eprintln!("AY_MILP_TRACE lattice: objective-0 face PROVEN EMPTY — optimum ≥ 1");
                }
                // optimum ≥ 1: hunt a value-1 witness on the b−e_k faces
                // (k ranges over the objective rows only — constraint rows
                // hold exactly on EVERY face). `None` here means every face
                // is empty (optimum ≥ 2: hand back) or the hunt aborted —
                // both decline the device.
                let initial_cap = (zero_nodes / 4).max(1_000_000);
                let (k, y, xd) = self.witness_hunt(ms, initial_cap)?;
                if self.trace {
                    eprintln!("AY_MILP_TRACE lattice: b−e_{k} face FEASIBLE — optimum = 1 witness");
                }
                // The LOWER-BOUND half of this optimum is an exhaustive sweep
                // over up to 4e9 nodes. There is no short witness for it, and
                // there will not be one: the claim is "no lattice point of this
                // coset lies in the box", and the proof IS the enumeration.
                // Filed only now, past the witness hunt, so the claim cannot be
                // orphaned onto a later verdict if the device declines.
                self.file_sweep_replay("objective-face-empty", zero_nodes);
                (1i64, y, xd)
            }
            EnumResult::Capped | EnumResult::Aborted => return None,
        };
        // Reconstruct the integer assignment x = x_d + K·y over the lattice
        // columns (free integer columns + synthetic inequality slacks).
        let mut xlat = vec![0i64; self.n];
        for kk in 0..self.n {
            let mut s = witness_xd[kk];
            for t in 0..self.dim {
                if witness_y[t] != 0 {
                    s = s.checked_add(witness_y[t].checked_mul(self.k[t][kk])?)?;
                }
            }
            xlat[kk] = s;
            debug_assert!(
                (self.lo[kk]..=self.up[kk]).contains(&s),
                "witness outside its box"
            );
        }
        // Build the full exact model point: integer columns, objective slacks
        // (= b_i − a_i·x), fixed/singleton columns at their fixed value.
        // Synthetic slack columns exist only in the extended system and are
        // dropped (their model rows are re-validated by `check_point` below).
        let nc = model.num_cols();
        let mut point = vec![BigRational::zero(); nc];
        for (kk, mc) in ms.col_model.iter().enumerate() {
            if let Some(j) = mc {
                point[*j] = BigRational::from(BigInt::from(xlat[kk]));
            }
        }
        for (idx, &i) in ms.obj_rows.iter().enumerate() {
            // slack_i = b_i − a_i·x   (≥ 0 integer)
            let mut ax = BigInt::zero();
            for kk in 0..self.n {
                ax += BigInt::from(ms.a[i][kk]) * BigInt::from(xlat[kk]);
            }
            let s = BigInt::from(ms.b[i]) - ax;
            if s.is_negative() {
                return None;
            }
            point[ms.slack_col[idx]] = BigRational::from(s);
        }
        // Integral columns tightened to a single value during detection.
        for &(j, v) in &ms.singleton_cols {
            point[j] = BigRational::from(BigInt::from(v));
        }
        // Fixed columns and any untouched column: use the model's fixed value.
        for j in 0..nc {
            if point[j].is_zero() {
                let (l, u) = model.col_bounds(Col(j as u32));
                if l == u && l != 0.0 {
                    point[j] = exact(l)?;
                }
            }
        }
        // Belt: the witness must survive an independent exact re-check.
        if model.check_point(&point).is_err() {
            if self.trace {
                eprintln!(
                    "AY_MILP_TRACE lattice: witness rejected by check_point — aborting device"
                );
            }
            return None;
        }
        let value = model.objective_value_at(&point);
        if self.trace {
            eprintln!("AY_MILP_TRACE lattice: PROVEN OPTIMAL {opt} (value {value})");
        }
        // A costless model (every objective coefficient 0, value exactly 0)
        // carries the same trivial empty-multiplier certificate the B&B
        // feasibility-objective closure ships (`0·x ≥ 0`, `combine([]) ≡ 0`),
        // so preempting the tree does not regress outcome quality. Models with
        // real objective weight (markshare: unit slack costs) ship `None`
        // exactly as before.
        let cert = if value.is_zero() && (0..nc).all(|j| model.obj_coeff(Col(j as u32)) == 0.0) {
            Some(crate::cert::OptimalityCertificate {
                sense: Sense::Minimize,
                objective: Vec::new(),
                bound: BigRational::zero(),
                multipliers: Vec::new(),
            })
        } else {
            None
        };
        Some(Outcome::Optimal {
            value,
            model_values: point,
            cert,
        })
    }
}

#[derive(Debug, PartialEq, Eq)]
enum EnumResult {
    Feasible(Vec<i64>),
    Empty,
    /// A serial witness-only sweep reached its retryable soft cap. This is
    /// inconclusive and may never be promoted to an emptiness proof.
    Capped,
    Aborted,
}

/// Result of the concurrent multi-face witness hunt (`enumerate_faces`).
enum FaceSweep {
    /// The face at position `pos` of the input slice yielded an exact,
    /// `box_ok`-verified witness `y`.
    Witness { pos: usize, y: Vec<i64> },
    /// EVERY face's ball was completely swept — no witness anywhere.
    AllEmpty,
    /// Deadline/budget/width abort with no witness. Never claimed empty.
    Aborted,
}

fn next_work_index(next: &AtomicUsize, len: usize) -> Option<usize> {
    let mut current = next.load(Ordering::Relaxed);
    loop {
        if current >= len {
            return None;
        }
        let updated = current.checked_add(1)?;
        match next.compare_exchange_weak(current, updated, Ordering::Relaxed, Ordering::Relaxed) {
            Ok(_) => return Some(current),
            Err(observed) => current = observed,
        }
    }
}

fn reserve_shared_nodes(shared: &AtomicU64, budget: u64) -> Option<u64> {
    let mut current = shared.load(Ordering::Relaxed);
    loop {
        if current >= budget {
            return None;
        }
        let updated = current.saturating_add(SHARED_NODE_RESERVE).min(budget);
        match shared.compare_exchange_weak(current, updated, Ordering::Relaxed, Ordering::Relaxed) {
            Ok(_) => return Some(updated - current),
            Err(observed) => current = observed,
        }
    }
}

fn join_lattice_worker(handle: ScopedJoinHandle<'_, ()>, aborted: &AtomicBool) {
    if handle.join().is_err() {
        aborted.store(true, Ordering::Release);
    }
}

/// Combine worker state fail-closed. A verified witness is authoritative even
/// if another worker aborted concurrently; without one, any incomplete worker
/// forbids the parallel path from claiming emptiness.
fn combine_parallel(witness: Option<Vec<i64>>, aborted: bool) -> EnumResult {
    match (witness, aborted) {
        (Some(witness), _) => EnumResult::Feasible(witness),
        (None, true) => EnumResult::Aborted,
        (None, false) => EnumResult::Empty,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum EnumSide {
    Down,
    Up,
}

/// Integer coordinates in Schnorr–Euchner order around an interval center.
///
/// `Down` includes the rounded center; `Up` starts at its successor. Together
/// they partition `[lo, hi]`, and closing one side after a monotone prune cannot
/// affect the other.
struct SchnorrEuchnerOrder {
    lo: i64,
    hi: i64,
    cmid: f64,
    down: i64,
    up: i64,
    down_done: bool,
    up_done: bool,
}

impl SchnorrEuchnerOrder {
    fn new(lo: i64, hi: i64, center: Interval) -> Self {
        debug_assert!(lo <= hi);
        let cmid = 0.5 * (center.lo + center.hi);
        let rounded = cmid.round();
        let start = if rounded.is_finite() {
            (rounded as i64).clamp(lo, hi)
        } else {
            lo
        };
        Self {
            lo,
            hi,
            cmid,
            down: start,
            up: start.saturating_add(1),
            down_done: false,
            up_done: start == i64::MAX,
        }
    }

    fn close(&mut self, side: EnumSide) {
        match side {
            EnumSide::Down => self.down_done = true,
            EnumSide::Up => self.up_done = true,
        }
    }
}

impl Iterator for SchnorrEuchnerOrder {
    type Item = (i64, EnumSide);

    fn next(&mut self) -> Option<(i64, EnumSide)> {
        let down_ok = !self.down_done && self.down >= self.lo;
        let up_ok = !self.up_done && self.up <= self.hi;
        if !down_ok && !up_ok {
            return None;
        }
        let take_down = if down_ok && up_ok {
            (self.cmid - self.down as f64).abs() <= (self.up as f64 - self.cmid).abs()
        } else {
            down_ok
        };
        if take_down {
            let value = self.down;
            match self.down.checked_sub(1) {
                Some(next) => self.down = next,
                None => self.down_done = true,
            }
            Some((value, EnumSide::Down))
        } else {
            let value = self.up;
            match self.up.checked_add(1) {
                Some(next) => self.up = next,
                None => self.up_done = true,
            }
            Some((value, EnumSide::Up))
        }
    }
}

/// One independent subtree of the DFS, produced by the top-level frontier
/// enumeration and processed by a single worker. Together the work items form a
/// COMPLETE PARTITION of the serial sweep: every non-pruned leaf lies under
/// exactly one item, and each item is enumerated with the same pruning/radius
/// as the serial path (its `dist` and `partial_row` are byte-identical to what
/// the serial recursion computed at that node).
struct WorkItem {
    /// Values of the already-fixed higher coordinates `y[stop_level+1 ..= dim-1]`.
    y_upper: Vec<i64>,
    /// Snapshot of `partial[stop_level][0 ..= stop_level]` as the parent wrote
    /// it, so the worker resumes `rec(stop_level, ..)` with identical centers.
    partial_row: Vec<Interval>,
    /// Squared-distance interval accumulated by the fixed higher coordinates,
    /// passed as `dist_above` into `rec(stop_level, dist)`.
    dist: Interval,
    /// Box-prune resume state (empty / zero when the prune is off): the parent's
    /// `C` row `cflat[stop_level + 1]` plus the two carried error accumulators,
    /// so the worker's `rec(stop_level, ..)` re-derives BYTE-IDENTICAL centers
    /// and prunes exactly where the serial sweep would. Without these the
    /// frontier and the workers would prune differently and the "complete
    /// partition of the serial sweep" invariant would no longer be checkable.
    c_row: Vec<f64>,
    box_g: f64,
    box_h: f64,
}

struct EnumState<'a> {
    eng: &'a Engine,
    xd: &'a [i64],
    tg: Vec<Interval>,
    radius: f64,
    y: Vec<i64>,
    partial: Vec<Vec<Interval>>,
    /// BOX-PRUNE scratch, flat `(dim + 1) × n` (empty when the prune is off).
    /// Row `L` holds `C^(L)_k = base_k + Σ_{t≥L} (y_t − e_t)·b*_t[k]`; row `dim`
    /// is the face's immutable `base`. A child row is rebuilt from its
    /// immutable parent row for every candidate, exactly like `partial`, so
    /// backtracking needs no restore and no error accumulates across siblings.
    cflat: Vec<f64>,
    /// `max_k |base_k|` and an outward bound on `|base_k − cflat[dim][k]|`.
    base_absmax: f64,
    base_halfw: f64,
    /// Whether this state maintains/tests `cflat` at all.
    box_on: bool,
    nodes: u64,
    /// Serial-only retryable cap. Shared parallel states use the independent
    /// `shared_budget` envelope and leave this at `NODE_BUDGET`.
    node_cap: u64,
    /// Parallel frontier passes and workers share one global node envelope.
    /// `None` preserves the serial path's local budget and byte-identical
    /// traversal.
    shared_nodes: Option<&'a AtomicU64>,
    /// Cap on the shared envelope: `NODE_BUDGET × workers`, so each parallel
    /// worker gets the historical serial budget (the dim-62 witness sits past
    /// 4G TOTAL nodes; capping the whole sweep at one serial budget would
    /// abort a face a 16-way box sweeps in under a minute). The serial path
    /// keeps `NODE_BUDGET` byte-identically, and the wall-clock deadline
    /// remains the primary runaway bound either way.
    shared_budget: u64,
    /// Nodes already RESERVED from `shared_nodes` but not yet spent by this
    /// state. Claiming in `SHARED_NODE_RESERVE` chunks keeps the shared
    /// counter off the per-node hot path; `Drop` returns the unspent part.
    reserved: u64,
    aborted: bool,
    /// A serial witness sweep stopped at `node_cap < NODE_BUDGET`.
    capped: bool,
    /// When set, a shared flag the enumeration polls (at the deadline cadence):
    /// once another worker CONFIRMS a witness it is raised, letting this worker
    /// abandon its partial subtree early. Distinct from `aborted` — a
    /// cancellation only ever happens when a witness already exists, so it can
    /// never turn a genuinely-empty face into anything but `Feasible`.
    cancel: Option<&'a AtomicBool>,
    /// True iff this sweep stopped because `cancel` was observed set.
    cancelled: bool,
}

/// Return the unspent chunk reservation to the shared envelope so the counter
/// equals the true visited total once the sweep's states are gone (no
/// underflow possible: everything returned was previously added by a claim).
impl Drop for EnumState<'_> {
    fn drop(&mut self) {
        if self.reserved > 0 {
            if let Some(shared) = self.shared_nodes {
                shared.fetch_sub(self.reserved, Ordering::Relaxed);
            }
        }
    }
}

impl EnumState<'_> {
    /// Claim one visited node without allowing either the local diagnostic
    /// count or the global parallel envelope to wrap. Failure is an abort, not
    /// an apparent empty subtree. Shared-envelope claims are made in
    /// `SHARED_NODE_RESERVE` chunks (degrading to the exact remainder at the
    /// budget boundary), so every counted node is backed by a reservation and
    /// the reserved total can never exceed `NODE_BUDGET`.
    fn record_node(&mut self) -> bool {
        // Stop BEFORE the next node, so a witness found at exactly `node_cap`
        // remains authoritative. Deadline expiry takes precedence over the
        // retryable classification. At the hard ceiling, fall through to the
        // ordinary budget check so an incomplete sweep aborts rather than caps.
        if self.shared_nodes.is_none() && self.node_cap < NODE_BUDGET && self.nodes >= self.node_cap
        {
            if Instant::now() >= self.eng.deadline {
                self.aborted = true;
            } else {
                self.capped = true;
            }
            return false;
        }
        let Some(local) = self.nodes.checked_add(1) else {
            self.aborted = true;
            return false;
        };
        if let Some(shared) = self.shared_nodes {
            if self.reserved == 0 {
                let budget = self.shared_budget;
                match reserve_shared_nodes(shared, budget) {
                    Some(reserved) => self.reserved = reserved,
                    None => {
                        self.aborted = true;
                        return false;
                    }
                }
            }
            self.reserved -= 1;
        } else if local > NODE_BUDGET {
            self.aborted = true;
            return false;
        }
        self.nodes = local;
        true
    }

    /// Restore the box-prune centre row a worker resumes from: `cflat[stop+1]`
    /// is `C^(stop+1)`, the row the frontier's parent node wrote. Seeding it
    /// makes the worker's `rec(stop, ..)` produce BIT-IDENTICAL centres to the
    /// serial sweep at the same node, so the frontier partition stays exact.
    /// A row of the wrong length (prune off on either side) leaves the state's
    /// own anchor in place, which only ever means "prune less".
    fn seed_box_row(&mut self, stop_level: usize, row: &[f64]) {
        let n = self.eng.n;
        if !self.box_on || row.len() != n {
            return;
        }
        let base = (stop_level + 1) * n;
        self.cflat[base..base + n].copy_from_slice(row);
    }

    /// ONE BOX-PREFIX PRUNE STEP, fused into the node the caller has just
    /// formed. Rebuilds the child centre row `C^(level)` from its immutable
    /// parent row `C^(level+1)` and tests EVERY original coordinate against its
    /// rigorous Cauchy–Schwarz reach bound (see `BoxPrune`).
    ///
    /// Returns `(g, h, fire)`. `fire` ⟹ the entire subtree below this node is
    /// PROVABLY box-empty: for some coordinate `k`, every completion of the
    /// unassigned levels that still fits the enumeration ball leaves `x_k`
    /// outside `[lo_k, up_k]`. `g`/`h` are the child's error accumulators,
    /// carried down the recursion beside `dist_above` (never restored on
    /// backtrack, because each node recomputes it from its own parent's value)
    /// and valid whether or not `fire` is set.
    ///
    /// The caller decides what to do with `fire`. `rec` cuts; the FRONTIER
    /// (`collect`) deliberately does NOT — it only maintains `C`, so its
    /// stop-level search, item count and partition stay BYTE-IDENTICAL to the
    /// unpruned build. Pruning the frontier instead shifts `stop_level` deeper,
    /// which reshuffles the round-robin item order and measurably delays
    /// witness discovery on feasible faces (cd8p_s101 3.8 s → timeout,
    /// cd_m8_s2 13.1 s → timeout). The frontier is only ~10⁴ nodes, so
    /// declining to cut it costs nothing, and the workers still cut everything
    /// below `stop_level` — where, per the level-mass profile, >99% of the
    /// nodes are.
    ///
    /// SOUNDNESS OF THE FLOATING POINT. `dst[k]` is a round-to-nearest FMA
    /// chain, not an interval — deliberately, since the per-operation outward
    /// form costs ~6× and buys nothing. Instead ONE outward envelope `eps`
    /// bounds the whole row's deviation from the exact centre:
    ///   * `base_halfw` — the enclosure width of the face anchor `base`;
    ///   * `h` — Σ over assigned levels of the interval widths of `y_t − e_t`
    ///     and of `b*_t[k]` (the only non-rounding error the point form drops);
    ///   * `eps_coeff · scale` with `eps_coeff = (dim + 8)·2⁻⁵²` — a Higham
    ///     bound on the ≤ `dim` FMA roundings (each ≤ `u·|C|`, and
    ///     `|C| ≤ base_absmax + g`), with 8 extra units covering the two box
    ///     subtractions, the `− eps` subtraction and the `rt · √S` product.
    /// The test then subtracts `eps` from the deviation and requires a STRICT
    /// excess, so a coordinate can only fire when the EXACT deviation exceeds
    /// the EXACT reach. Any non-finite or oversized magnitude forces
    /// `eps = ∞`, which makes every comparison false — fail-closed.
    #[inline]
    fn box_step(
        &mut self,
        bp: &BoxPrune,
        level: usize,
        diff: Interval,
        dist_lo: f64,
        g: f64,
        h: f64,
    ) -> (f64, f64, bool) {
        let n = self.eng.n;
        // Point form of `y_level − e_level` plus an outward deviation bound
        // valid for the ROUNDED midpoint itself (not for the exact midpoint).
        let dm = (diff.lo + diff.hi) * 0.5;
        let dw = (diff.hi - dm).max(dm - diff.lo).next_up();
        let amax = bp.bstar_absmax[level];
        let bw = bp.bstar_halfw[level];
        let adm = dm.abs();
        // `base_absmax + g` bounds `|C_k|` for every coordinate and every level
        // at or above this one; `h` accumulates the point form's dropped width.
        let gn = (g + (adm + dw) * amax).next_up();
        let hn = (h + ((adm + dw) * bw + dw * amax)).next_up();
        // Upper bound on the squared budget the UNASSIGNED levels may still
        // spend: every box point of the face lies in the ball, and the levels
        // at or above this one have already consumed at least `dist_lo`.
        let rem = (self.radius - dist_lo).next_up();
        let rt = if rem > 0.0 { rem.sqrt().next_up() } else { 0.0 };
        let scale = self.base_absmax + gn + bp.bound_absmax + rt * bp.sqrt_s_max[level];
        let mut eps =
            ((self.base_halfw + hn + bp.eps_coeff * scale) * BOX_PRUNE_EPS_SLACK).next_up();
        if !(scale < BOX_PRUNE_MAX_SCALE && eps > 0.0) {
            eps = f64::INFINITY;
        }
        let base = level * n;
        let (lower, upper) = self.cflat.split_at_mut(base + n);
        let dst = &mut lower[base..base + n];
        let src = &upper[..n];
        let bm = &bp.bstar_mid[level][..n];
        let sq = &bp.sqrt_s[level][..n];
        let lo_f = &bp.lo_f[..n];
        let up_f = &bp.up_f[..n];
        let mut fire = false;
        for k in 0..n {
            let c = dm.mul_add(bm[k], src[k]);
            dst[k] = c;
            let dev = (c - up_f[k]).max(lo_f[k] - c) - eps;
            fire |= dev > rt * sq[k];
        }
        (gn, hn, fire)
    }

    /// Recursion over kernel coordinate `level` (dim−1 … 0). `dist_above` is the
    /// outward interval for the squared distance accumulated by already-fixed
    /// higher coordinates; `box_g`/`box_h` are the box-prune error accumulators
    /// (both `0.0` at the root, ignored when the prune is off).
    fn rec(
        &mut self,
        level: usize,
        dist_above: Interval,
        box_g: f64,
        box_h: f64,
    ) -> Option<Vec<i64>> {
        if self.aborted || self.capped || self.cancelled {
            return None;
        }
        let eng = self.eng;
        let cnorm = eng.cnorm_i[level];
        let Some(e) = self.tg[level].sub(self.partial[level][level]) else {
            self.aborted = true;
            return None;
        };
        // Exact remaining radius is at most `radius - dist_above.lo`.
        // Use that upper enclosure and the norm's positive LOWER endpoint to
        // obtain a conservative coordinate width.
        let rem_hi = (self.radius - dist_above.lo).next_up();
        if rem_hi < 0.0 {
            return None;
        }
        let q = (rem_hi / cnorm.lo).next_up();
        let w = q.sqrt().next_up();
        let lo_f = (e.lo - w).next_down().ceil();
        let hi_f = (e.hi + w).next_up().floor();
        // Integers past 2^53 do not have exact f64 representations, so the hot
        // interval updates could not use them soundly.  Abort rather than cast
        // or silently skip such a coordinate.
        if !q.is_finite()
            || !w.is_finite()
            || !lo_f.is_finite()
            || !hi_f.is_finite()
            || lo_f < -MAX_EXACT_F64_INT
            || hi_f > MAX_EXACT_F64_INT
        {
            self.aborted = true;
            return None;
        }
        let lo = lo_f as i64;
        let hi = hi_f as i64;
        if lo > hi {
            return None;
        }
        // Schnorr–Euchner ordering.  The naive `lo..=hi` scan visits the SAME
        // set of coordinates but starts at the far edge of the ball; on a
        // FEASIBLE face the witness sits near the projected center `e`, so a
        // linear scan reaches it only after a deep detour.  Instead visit the
        // integers in order of increasing distance from `e` — start at the
        // Babai-rounded nearest integer and zig-zag outward, always taking the
        // pointer nearer the exact center first.  This changes only the ORDER
        // in which `[lo, hi]` is swept, never the coverage: an EMPTY face still
        // visits every non-pruned node (the emptiness proof is untouched, and
        // its node count is identical), while a FEASIBLE face reaches the first
        // `box_ok` far sooner (measured: it is what lets cd_m7 / dim-53 close).
        // Because the squared distance is strictly monotone in `|yi − e|`
        // OUTSIDE the enclosure `[e.lo, e.hi]`, the first prune beyond that
        // interval on a side closes the whole side (all farther points prune
        // too) — a sound early stop, equivalent to the naive scan's tail of
        // pruned iterations.
        let mut order = SchnorrEuchnerOrder::new(lo, hi, e);
        // Box-prefix prune tables, hoisted out of the candidate scan.
        let boxp = if self.box_on {
            eng.box_prune.as_ref()
        } else {
            None
        };
        while let Some((yi, side)) = order.next() {
            let yi_i = Interval {
                lo: yi as f64,
                hi: yi as f64,
            };
            // `diff = y_level − e_level`, lifted out of the `and_then` chain so
            // the box prune can reuse it. Identical operations in identical
            // order: the distance interval is bit-for-bit the historical one.
            let Some(diff) = yi_i.sub(e) else {
                self.aborted = true;
                return None;
            };
            let Some(d) = diff
                .square()
                .and_then(|v| v.mul_nonnegative(cnorm))
                .and_then(|v| dist_above.add(v))
            else {
                self.aborted = true;
                return None;
            };
            // Only a lower enclosure strictly beyond the exact sphere may
            // prune.  Equality belongs to the 0/1 sphere and is retained.
            if d.lo > self.radius {
                // Strict monotonicity beyond `[e.lo, e.hi]` lets a prune there
                // terminate the side; inside it the distance can only be
                // ≤ radius, so that branch is unreachable but still guarded.
                match side {
                    EnumSide::Down if (yi as f64) <= e.lo => order.close(side),
                    EnumSide::Up if (yi as f64) >= e.hi => order.close(side),
                    EnumSide::Down | EnumSide::Up => {}
                }
                continue;
            }
            if !self.record_node() {
                return None;
            }
            if self.nodes == 1 || self.nodes.is_multiple_of(ENUM_DEADLINE_POLL_NODES) {
                if Instant::now() >= eng.deadline {
                    self.aborted = true;
                    return None;
                }
                // A witness confirmed by another worker lets this partial sweep
                // stop early (parallel path only; `cancel` is `None` serially).
                if let Some(c) = self.cancel {
                    if c.load(Ordering::Relaxed) {
                        self.cancelled = true;
                        return None;
                    }
                }
            }
            self.y[level] = yi;
            // BOX-PREFIX PRUNE. Placed BEFORE the μ back-substitution so a cut
            // node also skips that O(level) pass. It must NOT close a
            // Schnorr–Euchner side: box infeasibility is not monotone along the
            // candidate scan (unlike the ℓ₂ distance), so only this candidate's
            // subtree is dropped.
            let (child_g, child_h) = match boxp {
                Some(bp) => {
                    let (g, h, fire) = self.box_step(bp, level, diff, d.lo, box_g, box_h);
                    if fire {
                        continue;
                    }
                    (g, h)
                }
                None => (box_g, box_h),
            };
            if level == 0 {
                match self.box_ok() {
                    Some(true) => return Some(self.y.clone()),
                    Some(false) => {}
                    None => {
                        self.aborted = true;
                        return None;
                    }
                }
            } else {
                // Push y_level into the lower centers, overwriting the child
                // row from this level's unchanged parent row.
                let mu = &eng.mu_i[level];
                for k in 0..level {
                    let Some(term) = mu[k].scale(yi as f64) else {
                        self.aborted = true;
                        return None;
                    };
                    let Some(next) = self.partial[level][k].add(term) else {
                        self.aborted = true;
                        return None;
                    };
                    self.partial[level - 1][k] = next;
                }
                let hit = self.rec(level - 1, d, child_g, child_h);
                if hit.is_some() {
                    return hit;
                }
                if self.aborted || self.capped || self.cancelled {
                    return None;
                }
            }
        }
        None
    }

    /// Frontier generation for the parallel path. A faithful mirror of `rec`
    /// restricted to the top levels: it descends `dim-1 … stop_level+1` with the
    /// IDENTICAL center/radius/pruning/Schnorr–Euchner arithmetic, but instead
    /// of recursing past `stop_level` it snapshots each surviving subtree root
    /// into `out` (the fixed higher `y`, the parent-written `partial[stop_level]`
    /// row, and the accumulated `dist`). Because every interval operation here is
    /// bit-for-bit what `rec` performs at the same node, the union of the emitted
    /// subtrees is EXACTLY the serial sweep's set of nodes below `stop_level`,
    /// pruned identically — no lattice point added or missed. Runs
    /// single-threaded (so `cancel` is unused); aborts propagate via `aborted`.
    fn collect(
        &mut self,
        level: usize,
        dist_above: Interval,
        stop_level: usize,
        out: &mut Vec<WorkItem>,
        frontier_cap: usize,
        box_g: f64,
        box_h: f64,
    ) {
        if self.aborted {
            return;
        }
        // Base case: this is a subtree root the workers will enumerate. The
        // parent has already written `partial[stop_level][0..=stop_level]`,
        // `cflat[stop_level + 1]` and every `y[stop_level+1..dim]`, exactly as
        // `rec` would have on entry to `rec(stop_level, dist_above)`.
        if level == stop_level {
            if out.len() >= frontier_cap {
                self.aborted = true;
                return;
            }
            let n = self.eng.n;
            out.push(WorkItem {
                y_upper: self.y[stop_level + 1..self.eng.dim].to_vec(),
                partial_row: self.partial[stop_level][0..=stop_level].to_vec(),
                dist: dist_above,
                c_row: if self.box_on {
                    let base = (stop_level + 1) * n;
                    self.cflat[base..base + n].to_vec()
                } else {
                    Vec::new()
                },
                box_g,
                box_h,
            });
            return;
        }
        let eng = self.eng;
        let cnorm = eng.cnorm_i[level];
        let Some(e) = self.tg[level].sub(self.partial[level][level]) else {
            self.aborted = true;
            return;
        };
        let rem_hi = (self.radius - dist_above.lo).next_up();
        if rem_hi < 0.0 {
            return;
        }
        let q = (rem_hi / cnorm.lo).next_up();
        let w = q.sqrt().next_up();
        let lo_f = (e.lo - w).next_down().ceil();
        let hi_f = (e.hi + w).next_up().floor();
        if !q.is_finite()
            || !w.is_finite()
            || !lo_f.is_finite()
            || !hi_f.is_finite()
            || lo_f < -MAX_EXACT_F64_INT
            || hi_f > MAX_EXACT_F64_INT
        {
            self.aborted = true;
            return;
        }
        let lo = lo_f as i64;
        let hi = hi_f as i64;
        if lo > hi {
            return;
        }
        let mut order = SchnorrEuchnerOrder::new(lo, hi, e);
        // The frontier MAINTAINS the box-prune centres (each work item carries
        // the row its worker resumes from) but never cuts on them, so the
        // emitted partition is exactly the unpruned one.
        let boxp = if self.box_on {
            eng.box_prune.as_ref()
        } else {
            None
        };
        while let Some((yi, side)) = order.next() {
            let yi_i = Interval {
                lo: yi as f64,
                hi: yi as f64,
            };
            let Some(diff) = yi_i.sub(e) else {
                self.aborted = true;
                return;
            };
            let Some(d) = diff
                .square()
                .and_then(|v| v.mul_nonnegative(cnorm))
                .and_then(|v| dist_above.add(v))
            else {
                self.aborted = true;
                return;
            };
            if d.lo > self.radius {
                match side {
                    EnumSide::Down if (yi as f64) <= e.lo => order.close(side),
                    EnumSide::Up if (yi as f64) >= e.hi => order.close(side),
                    EnumSide::Down | EnumSide::Up => {}
                }
                continue;
            }
            if !self.record_node() {
                return;
            }
            if (self.nodes == 1 || self.nodes.is_multiple_of(ENUM_DEADLINE_POLL_NODES))
                && Instant::now() >= eng.deadline
            {
                self.aborted = true;
                return;
            }
            self.y[level] = yi;
            // MAINTAIN-ONLY: the frontier computes the child `C` row (the
            // workers need it) but never acts on `fire`, so the emitted
            // partition is byte-identical to the unpruned build.
            let (child_g, child_h) = match boxp {
                Some(bp) => {
                    let (g, h, _fire) = self.box_step(bp, level, diff, d.lo, box_g, box_h);
                    (g, h)
                }
                None => (box_g, box_h),
            };
            // `level > stop_level >= 0`, so `level >= 1`: always the recurse
            // branch (the leaf `box_ok` is a worker's job, never the frontier's).
            let mu = &eng.mu_i[level];
            for k in 0..level {
                let Some(term) = mu[k].scale(yi as f64) else {
                    self.aborted = true;
                    return;
                };
                let Some(next) = self.partial[level][k].add(term) else {
                    self.aborted = true;
                    return;
                };
                self.partial[level - 1][k] = next;
            }
            self.collect(
                level - 1,
                d,
                stop_level,
                out,
                frontier_cap,
                child_g,
                child_h,
            );
            if self.aborted {
                return;
            }
        }
    }

    /// Exact integer box check for the fully-assigned `y`:
    /// `x = x_d + K y ∈ [lo, up]^n` (the historical shape: `{0,1}^n`).
    fn box_ok(&self) -> Option<bool> {
        let eng = self.eng;
        for k in 0..eng.n {
            let mut xk = self.xd[k];
            for t in 0..eng.dim {
                let yt = self.y[t];
                if yt != 0 {
                    xk = xk.checked_add(yt.checked_mul(eng.k[t][k])?)?;
                }
            }
            if xk < eng.lo[k] || xk > eng.up[k] {
                return Some(false);
            }
        }
        Some(true)
    }
}

// ---------------------------------------------------------------------------
// Exact integer linear algebra (column-HNF, LLL, GSO) — all one-time, tiny.
// ---------------------------------------------------------------------------

/// Column-Hermite-normal-form of `a` (m×n) with unimodular tracking. Returns
/// `(U, rank, M)` with `A·U = M = [H | 0]`; columns `rank..n` of `U` span the
/// SATURATED integer kernel of `A`.
fn col_hnf(
    a: &[Vec<BigInt>],
    m: usize,
    n: usize,
    deadline: Instant,
) -> Option<(Vec<Vec<BigInt>>, usize, Vec<Vec<BigInt>>)> {
    let mut mm: Vec<Vec<BigInt>> = a.to_vec(); // m × n
    let mut u: Vec<Vec<BigInt>> = (0..n)
        .map(|i| {
            (0..n)
                .map(|j| {
                    if i == j {
                        BigInt::one()
                    } else {
                        BigInt::zero()
                    }
                })
                .collect()
        })
        .collect(); // n × n
    let mut r = 0usize;
    for i in 0..m {
        loop {
            if Instant::now() >= deadline {
                return None;
            }
            // nonzero columns of row i among [r..n)
            let nz: Vec<usize> = (r..n).filter(|&c| !mm[i][c].is_zero()).collect();
            if nz.is_empty() {
                break;
            }
            // pivot = smallest |value|
            let p = *nz
                .iter()
                .min_by(|&&x, &&y| mm[i][x].magnitude().cmp(mm[i][y].magnitude()))
                .expect("nonempty");
            if p != r {
                col_swap(&mut mm, &mut u, p, r);
            }
            for c in (r + 1)..n {
                if !mm[i][c].is_zero() {
                    let q = &mm[i][c] / &mm[i][r];
                    if !q.is_zero() {
                        col_add(&mut mm, &mut u, c, r, &(-q));
                    }
                }
            }
            if (r + 1..n).all(|c| mm[i][c].is_zero()) {
                break;
            }
        }
        if !mm[i][r].is_zero() {
            if mm[i][r].is_negative() {
                col_neg(&mut mm, &mut u, r);
            }
            r += 1;
            if r == n {
                break;
            }
        }
    }
    Some((u, r, mm))
}

/// An INTEGER particular solution of `A x = d`, given `A`'s column-HNF data
/// `(hh, u, rank)` from [`col_hnf`] (`A·U = [H | 0]`): solve `H z = d` over ℚ,
/// require `z` integral, and return `x = U·[z; 0]`. `None` means "no integer
/// solution I can exhibit" — a rational-but-not-integral `z`, an inconsistent
/// system, or an expired deadline. A caller must therefore never read `None`
/// as INFEASIBLE.
///
/// Shared by the market-split face solver ([`Engine::particular`]) and the
/// root kernel reformulation ([`reformulate_kernel`]); they differ only in how
/// they obtained `d`.
///
/// ⚠ THE REPRESENTATIVE THIS RETURNS IS NOT SMALL. `U`'s entries are the
/// unimodular multipliers the Hermite reduction happened to accumulate, so
/// `|x|` is O(det) and has nothing to do with the model's box — MEASURED at
/// ~5.9·10¹⁵ against a `[0,5]` box. Every caller must reduce it modulo the
/// kernel lattice before using it for anything numeric: `Engine::particular`'s
/// callers pipe it through [`Engine::babai`], and [`reformulate_kernel`] through
/// [`translate_near_box`] (S4 there). Using it raw is a WRONG-ANSWER bug, not a
/// performance one.
fn hnf_particular(
    hh: &[Vec<BigInt>],
    u: &[Vec<BigInt>],
    m: usize,
    n: usize,
    rank: usize,
    d: &[BigInt],
    deadline: Instant,
) -> Option<Vec<BigInt>> {
    if Instant::now() >= deadline {
        return None;
    }
    let r = rank;
    // Augmented [H | d] over BigRational, Gaussian elimination.
    let mut hf: Vec<Vec<BigRational>> = (0..m)
        .map(|i| {
            let mut row: Vec<BigRational> = (0..r)
                .map(|j| BigRational::from(hh[i][j].clone()))
                .collect();
            row.push(BigRational::from(d[i].clone()));
            row
        })
        .collect();
    let mut piv: Vec<(usize, usize)> = Vec::new();
    let mut pr = 0usize;
    for c in 0..r {
        if Instant::now() >= deadline {
            return None;
        }
        let prow = (pr..m).find(|&i| !hf[i][c].is_zero());
        let Some(prow) = prow else { continue };
        hf.swap(pr, prow);
        let pv = hf[pr][c].clone();
        for x in &mut hf[pr] {
            *x /= &pv;
        }
        for i in 0..m {
            if i != pr && !hf[i][c].is_zero() {
                let f = hf[i][c].clone();
                for k in 0..=r {
                    let t = &f * &hf[pr][k];
                    hf[i][k] -= t;
                }
            }
        }
        piv.push((pr, c));
        pr += 1;
    }
    // Consistency: a zero row with nonzero rhs ⟹ no solution.
    for i in 0..m {
        if (0..r).all(|c| hf[i][c].is_zero()) && !hf[i][r].is_zero() {
            return None;
        }
    }
    let mut z1 = vec![BigRational::zero(); r];
    for &(pri, c) in &piv {
        z1[c] = hf[pri][r].clone();
    }
    // z must be integral.
    if z1.iter().any(|v| !v.is_integer()) {
        return None;
    }
    let z: Vec<BigInt> = z1
        .iter()
        .map(|v| v.to_integer())
        .chain(std::iter::repeat_n(BigInt::zero(), n - r))
        .collect();
    // x = U · [z; 0].
    let mut x = vec![BigInt::zero(); n];
    for (i, xi) in x.iter_mut().enumerate() {
        let mut s = BigInt::zero();
        for j in 0..n {
            if !z[j].is_zero() {
                s += &u[i][j] * &z[j];
            }
        }
        *xi = s;
    }
    Some(x)
}

fn col_swap(mm: &mut [Vec<BigInt>], u: &mut [Vec<BigInt>], a: usize, b: usize) {
    for row in mm.iter_mut() {
        row.swap(a, b);
    }
    for row in u.iter_mut() {
        row.swap(a, b);
    }
}

/// column `dst += k · column src`
fn col_add(mm: &mut [Vec<BigInt>], u: &mut [Vec<BigInt>], dst: usize, src: usize, k: &BigInt) {
    for row in mm.iter_mut() {
        let t = &row[src] * k;
        row[dst] += t;
    }
    for row in u.iter_mut() {
        let t = &row[src] * k;
        row[dst] += t;
    }
}

fn col_neg(mm: &mut [Vec<BigInt>], u: &mut [Vec<BigInt>], a: usize) {
    for row in mm.iter_mut() {
        row[a] = -std::mem::take(&mut row[a]);
    }
    for row in u.iter_mut() {
        row[a] = -std::mem::take(&mut row[a]);
    }
}

/// Float-guided LLL (δ = 0.99) over EXACT `BigInt` vectors. Only the GSO
/// decisions use `f64`; the lattice is preserved bit-exactly by unimodular
/// integer operations (no fixed-width overflow possible), so reduction quality
/// — not soundness — is all that depends on the float arithmetic.
fn lll(mut basis: Vec<Vec<BigInt>>, deadline: Instant) -> Option<Vec<Vec<BigInt>>> {
    if Instant::now() >= deadline {
        return None;
    }
    let nb = basis.len();
    if nb == 0 {
        return Some(basis);
    }
    let dim = basis[0].len();
    if basis.iter().any(|row| row.len() != dim) {
        return None;
    }
    let delta = 0.99f64;
    // GSO in f64 (from the exact vectors).  This controls reduction quality
    // only, but NaN/overflow could make the swap loop cycle forever; decline
    // any non-finite guidance rather than treating it as zero.
    //
    // The `μ`/`‖b*‖²` state is maintained INCREMENTALLY with the textbook LLL
    // update formulas (size-reduction: O(k); swap: O(nb)) instead of a full
    // O(nb²·dim) recomputation per row operation — that recomputation used to
    // dominate the whole reduction wall (~95% of BKZ time). The float state is
    // still guidance only: every basis mutation is an exact integer row
    // operation, and any non-finite or degenerate incremental value falls back
    // to a full recomputation from the exact vectors (declining outright, as
    // before, only if even that is non-finite). A periodic refresh bounds float
    // drift.
    let (mut mu, mut norm) = gso_float(&basis, deadline)?;
    let mut k = 1usize;
    let mut rounds = 0u64;
    while k < nb {
        rounds += 1;
        if rounds >= 1_000_000 || Instant::now() >= deadline {
            return None;
        }
        if rounds & 8191 == 0 {
            // Drift refresh from the exact vectors (quality hygiene, cheap at
            // this cadence).
            let g = gso_float(&basis, deadline)?;
            mu = g.0;
            norm = g.1;
        }
        for j in (0..k).rev() {
            if Instant::now() >= deadline {
                return None;
            }
            if mu[k][j].abs() > 0.5 {
                let q = mu[k][j].round();
                if q != 0.0 {
                    // Every integer row operation preserves the lattice, but a
                    // saturating float→i64 cast would not apply the chosen q.
                    if !q.is_finite() || q.abs() >= 9_223_372_036_854_775_808.0 {
                        return None;
                    }
                    let qi = BigInt::from(q as i64);
                    for t in 0..dim {
                        if t % GSO_DEADLINE_POLL_OPS == 0 && Instant::now() >= deadline {
                            return None;
                        }
                        let sub = &qi * &basis[j][t];
                        basis[k][t] -= sub;
                    }
                    // b_k −= q·b_j (j < k) leaves every b* and every other μ row
                    // unchanged; only row k's coefficients against b_0..b_{j}
                    // shift: μ_{k,j'} −= q·μ_{j,j'} (j' < j) and μ_{k,j} −= q.
                    for jp in 0..j {
                        mu[k][jp] -= q * mu[j][jp];
                    }
                    mu[k][j] -= q;
                    if mu[k][..k].iter().any(|v| !v.is_finite()) {
                        let g = gso_float(&basis, deadline)?;
                        mu = g.0;
                        norm = g.1;
                    }
                }
            }
        }
        if norm[k] >= (delta - mu[k][k - 1] * mu[k][k - 1]) * norm[k - 1] {
            k += 1;
        } else {
            basis.swap(k, k - 1);
            // Textbook swap update (Cohen Alg. 2.6.3), using the PRE-swap
            // μ/‖b*‖² values: with μ = μ_{k,k-1}, the new ‖b*_{k-1}‖² is
            // B = ‖b*_k‖² + μ²·‖b*_{k-1}‖².
            let mukk1 = mu[k][k - 1];
            let bnew = norm[k] + mukk1 * mukk1 * norm[k - 1];
            let mu_new = mukk1 * norm[k - 1] / bnew;
            let normk_new = norm[k - 1] * norm[k] / bnew;
            let ok = bnew.is_finite()
                && bnew > 0.0
                && mu_new.is_finite()
                && normk_new.is_finite()
                && normk_new > 0.0;
            if ok {
                norm[k] = normk_new;
                norm[k - 1] = bnew;
                for jp in 0..k - 1 {
                    let t = mu[k][jp];
                    mu[k][jp] = mu[k - 1][jp];
                    mu[k - 1][jp] = t;
                }
                mu[k][k - 1] = mu_new;
                let mut finite = true;
                for i in (k + 1)..nb {
                    let t = mu[i][k];
                    mu[i][k] = mu[i][k - 1] - mukk1 * t;
                    mu[i][k - 1] = t + mu_new * mu[i][k];
                    finite &= mu[i][k].is_finite() && mu[i][k - 1].is_finite();
                }
                if !finite {
                    let g = gso_float(&basis, deadline)?;
                    mu = g.0;
                    norm = g.1;
                }
            } else {
                let g = gso_float(&basis, deadline)?;
                mu = g.0;
                norm = g.1;
            }
            k = k.max(2) - 1;
        }
    }
    Some(basis)
}

// ---------------------------------------------------------------------------
// Exact BKZ (block Korkine–Zolotarev) reduction — a STRONGER reduction than
// LLL, layered on top of it. It thins the Fincke–Pohst enumeration ball by
// producing shorter, more-orthogonal basis vectors. Every transform is a
// UNIMODULAR integer operation, so the lattice is preserved bit-exactly; the
// Gram-determinant guard in `Engine::build` re-certifies that independently.
// ---------------------------------------------------------------------------

/// Exact Gram determinant `det(B·Bᵀ)` of an integer basis — the squared lattice
/// covolume, a UNIMODULAR INVARIANT. Two bases of the SAME lattice share it, so
/// comparing it before/after BKZ is a complete, exact lattice-preservation
/// certificate (equal det + full rank + every vector in `L` ⟹ same lattice).
/// Computed via exact rational Gaussian elimination on the integer Gram matrix.
fn gram_det(basis: &[Vec<BigInt>], deadline: Instant) -> Option<BigInt> {
    if Instant::now() >= deadline {
        return None;
    }
    let d = basis.len();
    if d == 0 {
        return Some(BigInt::one());
    }
    let cols = basis[0].len();
    if basis.iter().any(|row| row.len() != cols) {
        return None;
    }
    let mut g: Vec<Vec<BigRational>> = vec![vec![BigRational::zero(); d]; d];
    for i in 0..d {
        if Instant::now() >= deadline {
            return None;
        }
        for j in i..d {
            if Instant::now() >= deadline {
                return None;
            }
            let mut s = BigInt::zero();
            for c in 0..cols {
                if !basis[i][c].is_zero() && !basis[j][c].is_zero() {
                    s += &basis[i][c] * &basis[j][c];
                }
            }
            let r = BigRational::from(s);
            g[i][j] = r.clone();
            g[j][i] = r;
        }
    }
    let mut det = BigRational::one();
    for c in 0..d {
        if Instant::now() >= deadline {
            return None;
        }
        let piv = (c..d).find(|&r| !g[r][c].is_zero())?;
        if piv != c {
            g.swap(piv, c);
            det = -det;
        }
        det *= &g[c][c];
        let pv = g[c][c].clone();
        for r in (c + 1)..d {
            if Instant::now() >= deadline {
                return None;
            }
            if !g[r][c].is_zero() {
                let f = &g[r][c] / &pv;
                for k in c..d {
                    let t = &f * &g[c][k];
                    g[r][k] -= t;
                }
            }
        }
    }
    det.is_integer().then(|| det.to_integer())
}

/// Float GSO of an exact integer basis: returns `(μ, ‖b*‖²)`. Used only to
/// GUIDE the block-SVP search and the BKZ decisions — reduction quality, never
/// soundness (the emptiness proof rests on the Gram-det + kernel checks and the
/// per-candidate exact box test). Declines (`None`) on any non-finite guidance.
fn gso_float(basis: &[Vec<BigInt>], deadline: Instant) -> Option<(Vec<Vec<f64>>, Vec<f64>)> {
    if Instant::now() >= deadline {
        return None;
    }
    let nb = basis.len();
    if nb == 0 {
        return Some((vec![], vec![]));
    }
    let dim = basis[0].len();
    if basis.iter().any(|row| row.len() != dim) {
        return None;
    }
    let mut bs: Vec<Vec<f64>> = Vec::with_capacity(nb);
    let mut mu = vec![vec![0.0f64; nb]; nb];
    for i in 0..nb {
        if Instant::now() >= deadline {
            return None;
        }
        let mut bi = Vec::with_capacity(dim);
        for (k, x) in basis[i].iter().enumerate() {
            if k % GSO_DEADLINE_POLL_OPS == 0 && Instant::now() >= deadline {
                return None;
            }
            bi.push(x.to_f64().filter(|v| v.is_finite())?);
        }
        let mut v = bi.clone();
        for j in 0..i {
            if Instant::now() >= deadline {
                return None;
            }
            let mut dj = 0.0f64;
            let mut dot = 0.0f64;
            for k in 0..dim {
                if k % GSO_DEADLINE_POLL_OPS == 0 && Instant::now() >= deadline {
                    return None;
                }
                dj += bs[j][k] * bs[j][k];
                dot += bi[k] * bs[j][k];
            }
            if !dj.is_finite() || dj <= 0.0 || !dot.is_finite() {
                return None;
            }
            mu[i][j] = dot / dj;
            if !mu[i][j].is_finite() {
                return None;
            }
            for k in 0..dim {
                if k % GSO_DEADLINE_POLL_OPS == 0 && Instant::now() >= deadline {
                    return None;
                }
                v[k] -= mu[i][j] * bs[j][k];
                if !v[k].is_finite() {
                    return None;
                }
            }
        }
        bs.push(v);
    }
    let mut norm = Vec::with_capacity(nb);
    for row in &bs {
        if Instant::now() >= deadline {
            return None;
        }
        let mut squared_norm = 0.0f64;
        for (k, x) in row.iter().enumerate() {
            if k % GSO_DEADLINE_POLL_OPS == 0 && Instant::now() >= deadline {
                return None;
            }
            squared_norm += x * x;
        }
        if !squared_norm.is_finite() || squared_norm <= 0.0 {
            return None;
        }
        norm.push(squared_norm);
    }
    Some((mu, norm))
}

/// Schnorr–Euchner SVP enumeration over the PROJECTED block lattice
/// `π_j(b_j),…,π_j(b_k)`. Returns the integer coefficient vector
/// `(c_j,…,c_k)` of a NONZERO block combination whose projection is strictly
/// shorter than the current `‖b*_j‖²`, or `None` if the block is already
/// reduced. Float-guided (quality only). Restricting the top coordinate to
/// `≥ 0` halves the search without missing a shortest vector (`±v` share norm).
struct BlockEnum<'a> {
    d: usize,
    mu: &'a [Vec<f64>],
    j: usize,
    nloc: Vec<f64>,
    /// Per-level bounding profile (BKZ 2.0-style pruning): with levels
    /// `p..d-1` fixed (k = d−p coordinates), the partial norm must stay below
    /// `prune[p] · best`.  All-ones is the exact oracle.  A pruned profile may
    /// MISS an improving vector — the block then simply declines to improve
    /// (reduction QUALITY only); no probabilistic argument reaches the
    /// verdict path.
    prune: &'a [f64],
    /// Node budget for this call (`BKZ_SVP_NODE_CAP`, or the much tighter
    /// `BKZ_PRUNED_SVP_NODE_CAP` under pruning).
    cap: u64,
    best: f64,
    best_x: Option<Vec<i64>>,
    x: Vec<i64>,
    nodes: u64,
    deadline: Instant,
    aborted: bool,
}

/// Bounding profile for the block-SVP oracle.  `pruned == false`: exact
/// (all factors 1).  `pruned == true`: LINEAR pruning (Gama–Nguyen–Regev) —
/// the partial norm over k fixed coordinates is bounded by `(k/d)·R²`.
fn svp_pruning_profile(d: usize, pruned: bool) -> Vec<f64> {
    (0..d)
        .map(|p| {
            if pruned {
                (d - p) as f64 / d as f64
            } else {
                1.0
            }
        })
        .collect()
}

impl BlockEnum<'_> {
    fn rec(&mut self, level: isize, dist_above: f64) {
        if self.aborted || !dist_above.is_finite() {
            self.aborted = true;
            return;
        }
        self.nodes += 1;
        if self.nodes > self.cap {
            self.aborted = true;
            return;
        }
        if (self.nodes == 1 || self.nodes.is_multiple_of(BKZ_DEADLINE_POLL_NODES))
            && Instant::now() >= self.deadline
        {
            self.aborted = true;
            return;
        }
        if level < 0 {
            if dist_above < self.best && self.x.iter().any(|&v| v != 0) {
                self.best = dist_above;
                self.best_x = Some(self.x.clone());
            }
            return;
        }
        let p = level as usize;
        // Center: coefficient at level p is (x[p] + cp) where
        // cp = Σ_{p'>p} x[p'] · μ[j+p'][j+p]; the minimizer is x[p] = -cp.
        let mut cp = 0.0f64;
        for pp in (p + 1)..self.d {
            if self.x[pp] != 0 {
                cp += self.x[pp] as f64 * self.mu[self.j + pp][self.j + p];
            }
        }
        let center = -cp;
        let np = self.nloc[p];
        const MAX_EXACT_F64_INT: f64 = 9_007_199_254_740_992.0;
        if !center.is_finite()
            || !(-MAX_EXACT_F64_INT..MAX_EXACT_F64_INT).contains(&center)
            || !np.is_finite()
            || np <= 0.0
        {
            self.aborted = true;
            return;
        }
        let restrict_nonneg = p == self.d - 1;
        let bound = self.best * self.prune[p];
        let base = center.round();
        // Upward from the nearest integer.
        let mut t = base;
        loop {
            // At exactly 2^53, `t + 1.0 == t`; decline before the float
            // counter can stop making progress.
            if t >= MAX_EXACT_F64_INT {
                self.aborted = true;
                return;
            }
            let diff = t - center;
            let term = diff * diff * np;
            if !term.is_finite() {
                break;
            }
            if dist_above + term >= bound {
                break;
            }
            let ti = t as i64;
            if !(restrict_nonneg && ti < 0) {
                self.x[p] = ti;
                self.rec(level - 1, dist_above + term);
                if self.aborted {
                    return;
                }
            }
            t += 1.0;
        }
        // Downward.
        let mut t = base - 1.0;
        loop {
            // Likewise `t - 1.0 == t` at -2^53.
            if t <= -MAX_EXACT_F64_INT {
                self.aborted = true;
                return;
            }
            if restrict_nonneg && t < 0.0 {
                break;
            }
            let diff = t - center;
            let term = diff * diff * np;
            if !term.is_finite() {
                break;
            }
            if dist_above + term >= bound {
                break;
            }
            self.x[p] = t as i64;
            self.rec(level - 1, dist_above + term);
            if self.aborted {
                return;
            }
            t -= 1.0;
        }
    }

    /// Frontier generation for the parallel block-SVP: descend the top levels
    /// with the IDENTICAL center/zigzag/pruning arithmetic as `rec`, but at the
    /// FIXED radius `self.best` (never shrunk — `collect_top` records no
    /// solutions), snapshotting each surviving subtree root at `stop_level`
    /// into `out` as `(x[stop_level+1..], partial distance)`. The union of the
    /// emitted subtrees covers every node any shrinking-bound sweep could
    /// visit, so no candidate is lost to the split. Advisory only — a missed
    /// or cut-off subtree degrades reduction quality, never correctness.
    fn collect_top(
        &mut self,
        level: isize,
        dist_above: f64,
        stop_level: isize,
        out: &mut Vec<(Vec<i64>, f64)>,
    ) {
        if self.aborted || !dist_above.is_finite() {
            self.aborted = true;
            return;
        }
        if level == stop_level {
            out.push((
                self.x[(stop_level as usize + 1)..self.d].to_vec(),
                dist_above,
            ));
            return;
        }
        self.nodes += 1;
        if self.nodes > self.cap {
            self.aborted = true;
            return;
        }
        if (self.nodes == 1 || self.nodes.is_multiple_of(BKZ_DEADLINE_POLL_NODES))
            && Instant::now() >= self.deadline
        {
            self.aborted = true;
            return;
        }
        let p = level as usize;
        let mut cp = 0.0f64;
        for pp in (p + 1)..self.d {
            if self.x[pp] != 0 {
                cp += self.x[pp] as f64 * self.mu[self.j + pp][self.j + p];
            }
        }
        let center = -cp;
        let np = self.nloc[p];
        const MAX_EXACT_F64_INT: f64 = 9_007_199_254_740_992.0;
        if !center.is_finite()
            || !(-MAX_EXACT_F64_INT..MAX_EXACT_F64_INT).contains(&center)
            || !np.is_finite()
            || np <= 0.0
        {
            self.aborted = true;
            return;
        }
        let restrict_nonneg = p == self.d - 1;
        // The same GNR bounding profile as `rec` (all-ones when exact): the
        // frontier then covers exactly the subtrees a pruned serial sweep at
        // this fixed radius would visit. Advisory either way.
        let bound = self.best * self.prune[p];
        let base = center.round();
        let mut t = base;
        loop {
            if t >= MAX_EXACT_F64_INT {
                self.aborted = true;
                return;
            }
            let diff = t - center;
            let term = diff * diff * np;
            if !term.is_finite() {
                break;
            }
            if dist_above + term >= bound {
                break;
            }
            let ti = t as i64;
            if !(restrict_nonneg && ti < 0) {
                self.x[p] = ti;
                self.collect_top(level - 1, dist_above + term, stop_level, out);
                if self.aborted {
                    return;
                }
            }
            t += 1.0;
        }
        let mut t = base - 1.0;
        loop {
            if t <= -MAX_EXACT_F64_INT {
                self.aborted = true;
                return;
            }
            if restrict_nonneg && t < 0.0 {
                break;
            }
            let diff = t - center;
            let term = diff * diff * np;
            if !term.is_finite() {
                break;
            }
            if dist_above + term >= bound {
                break;
            }
            self.x[p] = t as i64;
            self.collect_top(level - 1, dist_above + term, stop_level, out);
            if self.aborted {
                return;
            }
            t -= 1.0;
        }
    }
}

/// Find a shorter projected block vector for block `[j, k]` (inclusive), or
/// `None` if none exists / the search was cut off.
fn block_svp(
    mu: &[Vec<f64>],
    norm: &[f64],
    j: usize,
    k: usize,
    pruned: bool,
    deadline: Instant,
    threads: usize,
) -> Option<Vec<i64>> {
    if Instant::now() >= deadline {
        return None;
    }
    let d = k - j + 1;
    let cap = if pruned {
        BKZ_PRUNED_SVP_NODE_CAP
    } else {
        BKZ_SVP_NODE_CAP
    };
    if threads <= 1 || d < SVP_PAR_MIN_BLOCK {
        let nloc: Vec<f64> = (0..d).map(|q| norm[j + q]).collect();
        let prune = svp_pruning_profile(d, pruned);
        let mut e = BlockEnum {
            d,
            mu,
            j,
            best: nloc[0],
            nloc,
            prune: &prune,
            cap,
            best_x: None,
            x: vec![0i64; d],
            nodes: 0,
            deadline,
            aborted: false,
        };
        e.rec(d as isize - 1, 0.0);
        return e.best_x;
    }
    block_svp_parallel(mu, norm, j, k, pruned, cap, deadline, threads)
}

/// Parallel block-SVP: enumerate the top levels of the projected block at the
/// FIXED radius `‖b*_j‖²` into a frontier of independent subtrees, then hand
/// the subtrees to scoped workers via an atomic work-index (the same pattern as
/// `enumerate_parallel`). Each item is enumerated INDEPENDENTLY — no shared
/// pruning bound — so every item's result depends only on `(μ, ‖b*‖², j, k)`
/// and the winner (minimal norm, ties by lowest item index) is DETERMINISTIC
/// for every worker count; the frontier split itself targets a fixed item
/// count, so the item set is machine-independent too. A fixed top radius covers
/// a superset of the serial sweep (which shrinks its bound as it finds
/// vectors), so no candidate the serial search could return is ever lost; the
/// extra breadth only costs wall time, which the workers absorb.
///
/// Soundness is unaffected either way: the result is advisory (reduction
/// quality). `apply_block` only accepts it through the exact unimodular
/// machinery and the Gram-det guard re-certifies the final basis.
#[allow(clippy::too_many_arguments)]
fn block_svp_parallel(
    mu: &[Vec<f64>],
    norm: &[f64],
    j: usize,
    k: usize,
    pruned: bool,
    cap: u64,
    deadline: Instant,
    threads: usize,
) -> Option<Vec<i64>> {
    let d = k - j + 1;
    let nloc: Vec<f64> = (0..d).map(|q| norm[j + q]).collect();
    let radius = nloc[0];
    let prune = svp_pruning_profile(d, pruned);

    // --- Frontier generation (single-threaded, deterministic) --------------
    // Iterative deepening over the top levels until the item count reaches a
    // FIXED target (independent of `threads`, so the item set — and hence the
    // deterministic winner — does not vary with the box).
    let mut items: Vec<(Vec<i64>, f64)> = Vec::new();
    let mut stop_level: isize = d as isize - 1;
    for split in 1..=SVP_PAR_MAX_SPLIT_LEVELS.min(d - 1) {
        let sl = d as isize - 1 - split as isize;
        let mut e = BlockEnum {
            d,
            mu,
            j,
            best: radius,
            nloc: nloc.clone(),
            prune: &prune,
            cap,
            best_x: None,
            x: vec![0i64; d],
            nodes: 0,
            deadline,
            aborted: false,
        };
        let mut out = Vec::new();
        e.collect_top(d as isize - 1, 0.0, sl, &mut out);
        if e.aborted {
            return None;
        }
        items = out;
        stop_level = sl;
        if items.len() >= SVP_PAR_TARGET_ITEMS || sl == 0 {
            break;
        }
    }
    if items.is_empty() {
        return None; // nothing inside the radius: block already reduced
    }

    // --- Parallel processing -----------------------------------------------
    let next_idx = AtomicUsize::new(0);
    let results: Mutex<Vec<(usize, f64, Vec<i64>)>> = Mutex::new(Vec::new());
    let spawn_failed = AtomicBool::new(false);
    let nthreads = threads.min(items.len()).max(1);
    std::thread::scope(|scope| {
        let mut handles = Vec::with_capacity(nthreads);
        for worker in 0..nthreads {
            let name = format!("ay-bkz-svp-{worker}");
            match std::thread::Builder::new()
                .name(name)
                .spawn_scoped(scope, || {
                    while let Some(idx) = next_work_index(&next_idx, items.len()) {
                        let (x_suffix, dist) = &items[idx];
                        let mut e = BlockEnum {
                            d,
                            mu,
                            j,
                            best: radius,
                            nloc: nloc.clone(),
                            prune: &prune,
                            cap,
                            best_x: None,
                            x: vec![0i64; d],
                            nodes: 0,
                            deadline,
                            aborted: false,
                        };
                        let base = stop_level as usize + 1;
                        e.x[base..d].copy_from_slice(x_suffix);
                        e.rec(stop_level, *dist);
                        if let Some(bx) = e.best_x {
                            if let Ok(mut guard) = results.lock() {
                                guard.push((idx, e.best, bx));
                            }
                            // An aborted item (deadline / node cap) simply contributes
                            // whatever it found — reduction quality only, same as the
                            // serial path returning its best-so-far on abort.
                        }
                    }
                }) {
                Ok(handle) => handles.push(handle),
                Err(_) => {
                    spawn_failed.store(true, Ordering::Release);
                    break;
                }
            }
        }
        for handle in handles {
            // A panicked SVP worker forfeits only its advisory result.
            let _ = handle.join();
        }
    });
    if spawn_failed.load(Ordering::Acquire) {
        // Spawn failure is a resource-exhaustion signal; decline the
        // (advisory) improvement outright rather than trust a degraded run.
        return None;
    }

    let mut results = results.into_inner().ok()?;
    // Deterministic winner: strictly shortest first, ties by item order.
    results.sort_by(|a, b| {
        a.1.partial_cmp(&b.1)
            .unwrap_or(std::cmp::Ordering::Equal)
            .then(a.0.cmp(&b.0))
    });
    results.into_iter().next().map(|(_, _, x)| x)
}

/// Exact inverse of a unimodular integer matrix (`det = ±1`), computed by
/// rational Gauss–Jordan. Returns `None` if any entry is non-integral (which
/// cannot happen for a genuine unimodular input) — the caller then declines the
/// block, staying sound.
fn unimodular_inverse(u: &[Vec<BigInt>], deadline: Instant) -> Option<Vec<Vec<BigInt>>> {
    if Instant::now() >= deadline {
        return None;
    }
    let d = u.len();
    if u.iter().any(|row| row.len() != d) {
        return None;
    }
    let mut a: Vec<Vec<BigRational>> = (0..d)
        .map(|i| {
            let mut row: Vec<BigRational> =
                u[i].iter().map(|x| BigRational::from(x.clone())).collect();
            for j in 0..d {
                row.push(if i == j {
                    BigRational::one()
                } else {
                    BigRational::zero()
                });
            }
            row
        })
        .collect();
    for c in 0..d {
        if Instant::now() >= deadline {
            return None;
        }
        let piv = (c..d).find(|&r| !a[r][c].is_zero())?;
        if piv != c {
            a.swap(piv, c);
        }
        let pv = a[c][c].clone();
        for x in a[c].iter_mut() {
            *x /= &pv;
        }
        for r in 0..d {
            if Instant::now() >= deadline {
                return None;
            }
            if r != c && !a[r][c].is_zero() {
                let f = a[r][c].clone();
                for kk in 0..2 * d {
                    let t = &f * &a[c][kk];
                    a[r][kk] -= t;
                }
            }
        }
    }
    let mut inv = vec![vec![BigInt::zero(); d]; d];
    for i in 0..d {
        for j in 0..d {
            let v = &a[i][d + j];
            if !v.is_integer() {
                return None;
            }
            inv[i][j] = v.to_integer();
        }
    }
    Some(inv)
}

/// Insert the short block vector `v = Σ coeffs[i]·b_{j+i}` at the front of block
/// `[j, k]` via an EXACT unimodular re-basification, returning the new full
/// basis (same lattice) or `None`.
///
/// Construction: column-HNF of the `1×d` row `coeffs` gives a unimodular `U`
/// with `coeffs·U = (g, 0,…,0)`. Its inverse `U⁻¹` is unimodular and integer;
/// row `p` of `U⁻¹` combined with the old block, `Σ_i U⁻¹[p][i]·b_{j+i}`, is the
/// new block basis, whose FIRST row is `(1/g)·v` — the primitive short vector
/// (`g = 1` for a shortest projected vector). `U⁻¹` unimodular ⟹ the new block
/// spans exactly the old block lattice, so the whole basis is a basis of `L`.
fn apply_block(
    basis: &[Vec<BigInt>],
    j: usize,
    k: usize,
    coeffs: &[i64],
    deadline: Instant,
) -> Option<Vec<Vec<BigInt>>> {
    let d = k - j + 1;
    let a = vec![coeffs.iter().map(|&c| BigInt::from(c)).collect::<Vec<_>>()];
    let (u, rank, _h) = col_hnf(&a, 1, d, deadline)?;
    if rank != 1 {
        return None;
    }
    let uinv = unimodular_inverse(&u, deadline)?;
    let cols = basis[0].len();
    let mut newblock: Vec<Vec<BigInt>> = Vec::with_capacity(d);
    for p in 0..d {
        let mut row = vec![BigInt::zero(); cols];
        for i in 0..d {
            if !uinv[p][i].is_zero() {
                for c in 0..cols {
                    if !basis[j + i][c].is_zero() {
                        row[c] += &uinv[p][i] * &basis[j + i][c];
                    }
                }
            }
        }
        newblock.push(row);
    }
    let mut out = basis.to_vec();
    for (p, row) in newblock.into_iter().enumerate() {
        out[j + p] = row;
    }
    Some(out)
}

/// Float log-potential of a basis: `Σ_i (n−i)·ln‖b*_i‖²` — the classical LLL
/// potential.  For a FIXED lattice (covolume pinned), lower means the GSO
/// profile is flatter with more mass pushed to the tail, which is exactly what
/// shrinks a Fincke–Pohst tree at any radius.  Float-only and quality-only: it
/// ranks candidate bases inside `bkz`, never touches a verdict.  It runs on a
/// small self-imposed grace budget rather than the BKZ deadline: the family's
/// kernels are tiny (dim ≤ 160), so one float GSO is microseconds, and ranking
/// must still work at the deadline boundary or an expiring clock would discard
/// the whole reduction in favor of the initial snapshot.
fn basis_log_potential(basis: &[Vec<BigInt>]) -> Option<f64> {
    let grace = Instant::now() + std::time::Duration::from_millis(100);
    let (_, norm) = gso_float(basis, grace)?;
    let n = norm.len();
    let mut p = 0.0f64;
    for (i, v) in norm.iter().enumerate() {
        p += (n - i) as f64 * v.ln();
    }
    p.is_finite().then_some(p)
}

/// Exact BKZ(β): sweep blocks of ≤ β consecutive vectors; for each, SVP-enumerate
/// the projected block lattice, and if a strictly shorter projected vector is
/// found, insert it (unimodular) and re-LLL. Terminates after `dim-1` consecutive
/// non-improving blocks (standard BKZ), a tour cap, or the deadline. Every step
/// preserves the lattice; `gram_det` re-certifies this at the call site.
///
/// `pruned` selects the BKZ 2.0-style linear bounding profile plus the tight
/// per-call node cap inside the block-SVP oracle (see `svp_pruning_profile`),
/// and enables best-snapshot selection: pruned full-dimension tours do NOT
/// improve quality monotonically (insertions reshuffle the profile and can
/// transiently worsen it), so the BEST tour-boundary snapshot by GSO
/// log-potential is returned.  The old-base variant deferred each tour's LLL
/// to the tour boundary; on THIS base the incremental-GSO LLL is cheap and
/// deferral was measured strictly worse at both corpus dimensions (dim-53
/// cd_m7_s1 5.88s vs 1.18s; dim-62 basis Σ‖·‖² 2427 vs 1799), so every
/// insertion re-LLLs immediately, exactly like the exact path.  Quality-only
/// either way: every snapshot is a genuine unimodular image of the input
/// lattice and the caller's covolume/kernel guard re-certifies whichever one
/// wins.
fn bkz(
    mut basis: Vec<Vec<BigInt>>,
    beta: usize,
    pruned: bool,
    deadline: Instant,
    trace: bool,
    threads: usize,
) -> Vec<Vec<BigInt>> {
    let dim = basis.len();
    if dim < 2 {
        return basis;
    }
    let beta = beta.min(dim);
    if let Some(b) = lll(basis.clone(), deadline) {
        basis = b;
    }
    let mut z = 0usize; // consecutive non-improving blocks
    let mut jj = 0usize;
    let mut improvements = 0u64;
    let mut svp_calls = 0u64;
    let mut tours = 0u64;
    // Trace-only wall breakdown of the loop's four components (quality/speed
    // diagnostics; no effect on the reduction itself).
    let mut t_gso = std::time::Duration::ZERO;
    let mut t_svp = std::time::Duration::ZERO;
    let mut t_apply = std::time::Duration::ZERO;
    let mut t_lll = std::time::Duration::ZERO;
    let mut best: Option<(f64, Vec<Vec<BigInt>>)> = if pruned {
        basis_log_potential(&basis).map(|p| (p, basis.clone()))
    } else {
        None
    };
    let max_tours: u64 = adaptive_bkz_tours(dim, pruned);
    while z < dim - 1 {
        if Instant::now() >= deadline {
            break;
        }
        let k = (jj + beta - 1).min(dim - 1);
        let improved = if k > jj {
            let t0 = Instant::now();
            let g = gso_float(&basis, deadline);
            t_gso += t0.elapsed();
            match g {
                Some((mu, norm)) => {
                    svp_calls += 1;
                    let t1 = Instant::now();
                    let sv = block_svp(&mu, &norm, jj, k, pruned, deadline, threads);
                    t_svp += t1.elapsed();
                    match sv {
                        Some(coeffs) => {
                            let t2 = Instant::now();
                            let ab = apply_block(&basis, jj, k, &coeffs, deadline);
                            t_apply += t2.elapsed();
                            match ab {
                                Some(newb) => {
                                    let t3 = Instant::now();
                                    let red = lll(newb, deadline);
                                    t_lll += t3.elapsed();
                                    match red {
                                        Some(red) => {
                                            basis = red;
                                            true
                                        }
                                        None => false,
                                    }
                                }
                                None => false,
                            }
                        }
                        None => false,
                    }
                }
                None => break,
            }
        } else {
            false
        };
        if improved {
            z = 0;
            improvements += 1;
        } else {
            z += 1;
        }
        jj += 1;
        if jj >= dim - 1 {
            jj = 0;
            tours += 1;
            // Pruned path: rank the tour-boundary basis by log-potential and
            // keep the best snapshot seen (tours can transiently worsen it).
            if let Some(bst) = best.as_mut() {
                if let Some(p) = basis_log_potential(&basis) {
                    if p < bst.0 {
                        *bst = (p, basis.clone());
                    }
                }
            }
            if tours >= max_tours {
                break;
            }
        }
    }
    if let Some(bst) = best.as_mut() {
        if let Some(p) = basis_log_potential(&basis) {
            if p < bst.0 {
                *bst = (p, basis.clone());
            }
        }
    }
    if let Some((_, b)) = best {
        basis = b;
    }
    if trace {
        let oracle = if pruned { "pruned" } else { "exact" };
        eprintln!(
            "AY_MILP_TRACE lattice: BKZ(β={beta}, {oracle} oracle) — {improvements} block insertions / {svp_calls} SVP calls / {tours} tours"
        );
        eprintln!(
            "AY_MILP_TRACE lattice: BKZ breakdown — gso_float {:.3}s, block_svp {:.3}s, apply_block {:.3}s, lll {:.3}s",
            t_gso.as_secs_f64(),
            t_svp.as_secs_f64(),
            t_apply.as_secs_f64(),
            t_lll.as_secs_f64()
        );
    }
    basis
}

/// Exact Gram–Schmidt of an integer basis. Returns orthogonal vectors `b*`,
/// their squared norms, and `μ[i][j]` (i>j).
#[allow(clippy::type_complexity)]
fn gso_exact(
    basis: &[Vec<BigInt>],
    deadline: Instant,
) -> Option<(
    Vec<Vec<BigRational>>,
    Vec<BigRational>,
    Vec<Vec<BigRational>>,
)> {
    if Instant::now() >= deadline {
        return None;
    }
    let nb = basis.len();
    if nb == 0 {
        return Some((vec![], vec![], vec![]));
    }
    let dim = basis[0].len();
    if basis.iter().any(|row| row.len() != dim) {
        return None;
    }
    let mut bs: Vec<Vec<BigRational>> = Vec::with_capacity(nb);
    let mut cnorm: Vec<BigRational> = Vec::with_capacity(nb);
    let mut mu = vec![vec![BigRational::zero(); nb]; nb];
    for i in 0..nb {
        if Instant::now() >= deadline {
            return None;
        }
        let mut bi = Vec::with_capacity(dim);
        for (k, x) in basis[i].iter().enumerate() {
            if k % GSO_DEADLINE_POLL_OPS == 0 && Instant::now() >= deadline {
                return None;
            }
            bi.push(BigRational::from(x.clone()));
        }
        let mut v = bi.clone();
        for j in 0..i {
            if Instant::now() >= deadline || cnorm[j].is_zero() {
                return None;
            }
            let mut dot = BigRational::zero();
            for k in 0..dim {
                if k % GSO_DEADLINE_POLL_OPS == 0 && Instant::now() >= deadline {
                    return None;
                }
                if !bi[k].is_zero() && !bs[j][k].is_zero() {
                    dot += &bi[k] * &bs[j][k];
                }
            }
            let m = &dot / &cnorm[j];
            for k in 0..dim {
                if k % GSO_DEADLINE_POLL_OPS == 0 && Instant::now() >= deadline {
                    return None;
                }
                let t = &m * &bs[j][k];
                v[k] -= t;
            }
            mu[i][j] = m;
        }
        let mut nrm = BigRational::zero();
        for k in 0..dim {
            if k % GSO_DEADLINE_POLL_OPS == 0 && Instant::now() >= deadline {
                return None;
            }
            if !v[k].is_zero() {
                nrm += &v[k] * &v[k];
            }
        }
        if nrm <= BigRational::zero() {
            return None;
        }
        bs.push(v);
        cnorm.push(nrm);
    }
    Some((bs, cnorm, mu))
}

/// Round a rational to the nearest integer (`floor(r + ½)`; ties up — irrelevant
/// to Babai correctness, which only needs *a* nearby lattice vector). `denom` is
/// always positive in `BigRational`, so `div_floor` gives the true floor.
fn round_rat(r: &BigRational) -> BigInt {
    use num_integer::Integer;
    let two = BigInt::from(2);
    let num = r.numer() * &two + r.denom();
    let den = r.denom() * &two;
    num.div_floor(&den)
}

// ---------------------------------------------------------------------------
// AARDAL–HURKENS–LENSTRA ROOT REFORMULATION
//
// Everything above proves a verdict by ENUMERATING a lattice. This section does
// something different and much cheaper: it hands the ordinary branch-and-bound
// search a different COORDINATE SYSTEM and then gets out of the way.
// ---------------------------------------------------------------------------

/// Cap on `|C|`, the block of columns re-coordinated. Every step of the build
/// (column-HNF with unimodular tracking, LLL, the exact `|C|×|C|` unimodularity
/// certificate, the exact ℚ-rank) is cubic in `BigInt`, and a change of
/// coordinates only pays off on a SMALL, tightly coupled block anyway.
const KERNEL_MAX_COLS: usize = 64;

/// Cap on `|E|`, the equality rows folded away.
const KERNEL_MAX_ROWS: usize = 32;

/// Wall-clock envelope for one reformulation attempt. `reformulate_kernel` runs
/// ONCE at the root of a solve and has no caller deadline to inherit, so it
/// carries its own: a decline costs the solve this much at worst, and on the
/// shapes the gate admits (`ej`: 1×3) the real cost is microseconds.
const KERNEL_REFORM_SECS: u64 = 10;

/// The exact rational `v` as an `f64`, or `None` when the `f64` would be a
/// ROUNDED PROXY. Identical rule to `presolve::as_exact_f64` — the reformulation
/// fails closed on every coefficient it cannot restate without loss, because a
/// rounded coefficient in the reduced model is a different model.
fn as_exact_f64(v: &BigRational) -> Option<f64> {
    let f = v.to_f64()?;
    if !f.is_finite() {
        return None;
    }
    (BigRational::from_float(f).as_ref() == Some(v)).then_some(f)
}

/// The BOX TARGET the AHL translation aims `x_p` at, one entry per member of
/// `C`: the midpoint when the column is boxed on both sides, the finite side
/// when it is boxed on one, and `0` when it is free. Deterministic, and the only
/// place the reformulation's notion of "near the box" is defined.
///
/// A one-sided column contributes its finite side rather than `0` because that
/// side is the only thing that becomes a ROW — aiming at it drives the emitted
/// `lo_j − x_p[j]` toward zero, which is the number this whole step exists to
/// keep small. (`ej` is exactly that shape: `x₀ ≥ 1`, `x₁,x₂ ≥ 0`, no upper
/// bounds, so the target is `(1,0,0)`.)
fn box_target(model: &Model, cols_c: &[usize]) -> Option<Vec<BigRational>> {
    let two = BigRational::from(BigInt::from(2));
    cols_c
        .iter()
        .map(|&j| {
            let (l, u) = model.col_bounds(Col(j as u32));
            match (l.is_finite(), u.is_finite()) {
                (true, true) => Some((exact(l)? + exact(u)?) / &two),
                (true, false) => exact(l),
                (false, true) => exact(u),
                (false, false) => Some(BigRational::zero()),
            }
        })
        .collect()
}

/// THE AARDAL–HURKENS–LENSTRA TRANSLATION STEP:
/// `x_p ← x_p − B·round(B⁺·(x_p − t))`, i.e. subtract the lattice vector nearest
/// `x_p − t` so the coset representative sits NEAR THE BOX instead of wherever
/// the Hermite solve happened to leave it.
///
/// # Why this is not cosmetic
///
/// [`hnf_particular`] returns `U·[z;0]`, whose entries are O(det) — driven by the
/// unimodular multipliers, not by the model. MEASURED on a 2×4 equality block
/// with coefficients ~5·10⁴ over a `[0,5]` box, the untranslated `x_p` sits
/// ~5.9·10¹⁵ from the box, and EVERY number the reformulation emits inherits
/// that scale: the bound-row right-hand sides `lo_j − x_p[j]`, the folded row
/// shifts `Σ a_j·x_p[j]`, and `const_delta = c_C·x_p`, which the reduced
/// objective then has to cancel back down to an answer of magnitude 9. In
/// `[2^52, 2^53)` the `f64` ULP is EXACTLY 1 — the granularity of the answer
/// itself — so the reduced LP is being asked to resolve the optimum inside its
/// own rounding error. Every such number is individually `as_exact_f64`-clean;
/// it is the CANCELLATION between them that is destroyed, which is why the S2
/// fail-closed rule never fires and the whole failure is silent.
///
/// # The computation, and why it is exact
///
/// `B` is `d × |C|` and not square, so `B⁺` is a pseudo-inverse and the honest
/// statement of `round(B⁺ v)` is "the integer coefficient vector of a lattice
/// point near `v`" — a CVP instance. Babai's nearest-plane algorithm on the
/// LLL-reduced basis is the standard answer and is EXACT when the
/// Gram–Schmidt coefficients are kept rational, which is what [`gso_exact`]
/// hands back. Sweeping `i = d−1 … 0`, take `c_i = ⟨v, b*_i⟩ / ‖b*_i‖²` and
/// subtract `round(c_i)·b_i`. NO FLOAT ENTERS THE DERIVATION OF `x_p`; the
/// rounding is [`round_rat`] (ties up), so the result is a deterministic
/// function of `(x_p, B, t)`.
///
/// The component of `x_p − t` orthogonal to `span(B) = ker(A)` is untouchable by
/// construction — it is the distance from the box target to the affine set
/// `{A x = b}`, which no choice of representative can shrink. That residue is
/// itself O(box) whenever the model has an integer point in its box (the point
/// witnesses it), so the bound this step actually delivers is
/// `‖x_p − t‖ ≤ 2^{d/2}·dist(t, x_p + L)`, Babai's LLL approximation factor
/// against the best representative that exists.
///
/// Returns `None` on a shape mismatch or an expired deadline; the caller
/// DECLINES the reformulation rather than shipping an untranslated `x_p`.
fn translate_near_box(
    xp: &[BigInt],
    basis: &[Vec<BigInt>],
    target: &[BigRational],
    deadline: Instant,
) -> Option<Vec<BigInt>> {
    let n = xp.len();
    if target.len() != n || basis.iter().any(|b| b.len() != n) {
        return None;
    }
    let d = basis.len();
    if d == 0 {
        return Some(xp.to_vec());
    }
    let (bstar, cnorm, _mu) = gso_exact(basis, deadline)?;
    // `v := x_p − t` is RATIONAL (a two-sided box has a half-integral midpoint);
    // `x_p` itself never leaves ℤ, because every vector subtracted from it below
    // is an integer multiple of an integer basis vector.
    let mut v: Vec<BigRational> = xp
        .iter()
        .zip(target)
        .map(|(x, t)| BigRational::from(x.clone()) - t)
        .collect();
    let mut w = vec![BigInt::zero(); d];
    for i in (0..d).rev() {
        if Instant::now() >= deadline {
            return None;
        }
        let mut num = BigRational::zero();
        for k in 0..n {
            if !v[k].is_zero() && !bstar[i][k].is_zero() {
                num += &v[k] * &bstar[i][k];
            }
        }
        let q = round_rat(&(num / &cnorm[i]));
        if q.is_zero() {
            continue;
        }
        let qr = BigRational::from(q.clone());
        for k in 0..n {
            if !basis[i][k].is_zero() {
                let t = &qr * BigRational::from(basis[i][k].clone());
                v[k] -= t;
            }
        }
        w[i] = q;
    }
    let mut out = xp.to_vec();
    for (i, q) in w.iter().enumerate() {
        if q.is_zero() {
            continue;
        }
        for (k, o) in out.iter_mut().enumerate() {
            if !basis[i][k].is_zero() {
                *o -= &basis[i][k] * q;
            }
        }
    }
    Some(out)
}

/// `A x == b` over `BigInt`, exactly. Used to re-check the particular solution
/// BOTH as [`hnf_particular`] returns it and again after the translation of
/// [`translate_near_box`] — `A·B = 0` makes the translation an identity on this
/// property for any integer `w`, so a failure here is a BUG in the translation
/// (or the basis), and the caller declines. That single check is what makes a
/// botched translation impossible to ship.
fn satisfies_exactly(a: &[Vec<BigInt>], b: &[BigInt], x: &[BigInt]) -> bool {
    a.len() == b.len()
        && a.iter().zip(b).all(|(arow, bi)| {
            let mut dot = BigInt::zero();
            for (av, xv) in arow.iter().zip(x) {
                if !av.is_zero() && !xv.is_zero() {
                    dot += av * xv;
                }
            }
            dot == *bi
        })
}

/// `max |v_i|`, the magnitude number the translation is judged on.
fn max_abs_big(v: &[BigInt]) -> BigInt {
    v.iter()
        .map(|x| x.magnitude().clone().into())
        .max()
        .unwrap_or_else(BigInt::zero)
}

/// Exact rank over ℚ of an integer matrix, by rational Gaussian elimination.
///
/// This is deliberately INDEPENDENT of [`col_hnf`]'s own pivot count: S1(c)
/// (see [`reformulate_kernel`]) needs the kernel dimension `|C| − rank(A)` to be
/// the truth, not the HNF's opinion of it, because a rank read one too high
/// yields one basis vector too few and silently drops a whole direction of the
/// feasible lattice.
fn rank_exact_q(a: &[Vec<BigInt>], deadline: Instant) -> Option<usize> {
    let m = a.len();
    if m == 0 {
        return Some(0);
    }
    let n = a[0].len();
    if a.iter().any(|row| row.len() != n) {
        return None;
    }
    let mut g: Vec<Vec<BigRational>> = a
        .iter()
        .map(|row| row.iter().map(|v| BigRational::from(v.clone())).collect())
        .collect();
    let mut rank = 0usize;
    for c in 0..n {
        if rank == m {
            break;
        }
        if Instant::now() >= deadline {
            return None;
        }
        let Some(prow) = (rank..m).find(|&r| !g[r][c].is_zero()) else {
            continue;
        };
        g.swap(prow, rank);
        let pv = g[rank][c].clone();
        for x in &mut g[rank] {
            *x /= &pv;
        }
        for r in 0..m {
            if r != rank && !g[r][c].is_zero() {
                let f = g[r][c].clone();
                for k in c..n {
                    let t = &f * &g[rank][k];
                    g[r][k] -= t;
                }
            }
        }
        rank += 1;
    }
    Some(rank)
}

/// Exact `A·B` over `BigInt` (`a` is `p×q`, `b` is `q×s`), or `None` on a shape
/// mismatch / expired deadline.
fn matmul_bigint(
    a: &[Vec<BigInt>],
    b: &[Vec<BigInt>],
    deadline: Instant,
) -> Option<Vec<Vec<BigInt>>> {
    let q = b.len();
    let s = if q == 0 { 0 } else { b[0].len() };
    if b.iter().any(|row| row.len() != s) || a.iter().any(|row| row.len() != q) {
        return None;
    }
    let mut out = vec![vec![BigInt::zero(); s]; a.len()];
    for (i, arow) in a.iter().enumerate() {
        if Instant::now() >= deadline {
            return None;
        }
        for (k, aik) in arow.iter().enumerate() {
            if aik.is_zero() {
                continue;
            }
            for j in 0..s {
                if !b[k][j].is_zero() {
                    out[i][j] += aik * &b[k][j];
                }
            }
        }
    }
    Some(out)
}

/// S1(c): the column-HNF really did what it claims, and `U` really is
/// unimodular — so columns `rank..|C|` of `U` are a basis of the FULL saturated
/// kernel `L = {y ∈ ℤ^|C| : A y = 0}`, not of some sublattice or superlattice.
///
/// Four exact discharges, in the order they build on each other:
///  1. `rank` equals the ℚ-rank of `A` recomputed independently ([`rank_exact_q`]);
///  2. `A·U == M` exactly over `BigInt`;
///  3. `M`'s columns `rank..n` are identically zero (so those columns of `U` lie
///     in `L` — and with (1) the first `rank` columns of `M` must then span a
///     rank-`rank` space, i.e. be independent);
///  4. `U` has an INTEGER inverse and `U·U⁻¹ == I` exactly, hence `det U = ±1`.
///
/// (4) is what upgrades "those columns lie in `L`" to "those columns GENERATE
/// `L`": `U` unimodular means its columns are a ℤ-basis of ℤ^|C|, so any
/// `y ∈ L ⊆ ℤ^|C|` is `U w` for a unique integer `w`, and `A y = M w = 0` with
/// (3)+(1) forces `w_0..w_{rank−1} = 0`.
fn hnf_kernel_invariant_holds(
    a: &[Vec<BigInt>],
    u: &[Vec<BigInt>],
    mm: &[Vec<BigInt>],
    rank: usize,
    n: usize,
    deadline: Instant,
) -> bool {
    if u.len() != n || u.iter().any(|row| row.len() != n) {
        return false;
    }
    if mm.len() != a.len() || mm.iter().any(|row| row.len() != n) {
        return false;
    }
    if rank_exact_q(a, deadline) != Some(rank) {
        return false;
    }
    let Some(au) = matmul_bigint(a, u, deadline) else {
        return false;
    };
    if au != mm {
        return false;
    }
    if mm
        .iter()
        .any(|row| row[rank..].iter().any(|v| !v.is_zero()))
    {
        return false;
    }
    let Some(inv) = unimodular_inverse(u, deadline) else {
        return false;
    };
    let Some(prod) = matmul_bigint(u, &inv, deadline) else {
        return false;
    };
    (0..n).all(|i| {
        (0..n).all(|j| {
            if i == j {
                prod[i][j].is_one()
            } else {
                prod[i][j].is_zero()
            }
        })
    })
}

/// S1(a)+(b): `candidate` is a BASIS of the same lattice as `reference`, not a
/// proper sublattice of it.
///
/// **This is the one way the whole design can be unsound, so both halves are
/// mandatory.** (a) alone — every candidate vector lies in `ker A` — is passed
/// by the DOUBLED basis `{2·b₁, b₂, …}`, which spans an index-2 sublattice: the
/// reformulated model would then be missing half the feasible integer points and
/// could report a strictly WORSE value while claiming OPTIMAL. (b) is the exact
/// covolume equality (`det(B·Bᵀ)`, a unimodular invariant) that rules that out:
/// `d` vectors of `L`, of rank `d` (a nonzero Gram determinant), whose covolume
/// equals `L`'s, generate a sublattice of INDEX 1 — that is, `L` itself.
fn kernel_basis_is_same_lattice(
    a: &[Vec<BigInt>],
    reference: &[Vec<BigInt>],
    candidate: &[Vec<BigInt>],
    n: usize,
    deadline: Instant,
) -> bool {
    if candidate.len() != reference.len() || candidate.is_empty() {
        return false;
    }
    if candidate.iter().any(|v| v.len() != n) || reference.iter().any(|v| v.len() != n) {
        return false;
    }
    // (a) every candidate vector is in the kernel, over BigInt (no i64 narrowing:
    // that is the ENUMERATOR's requirement, not a soundness one).
    for v in candidate {
        for arow in a {
            if Instant::now() >= deadline {
                return false;
            }
            let mut dot = BigInt::zero();
            for (ai, vi) in arow.iter().zip(v) {
                if !ai.is_zero() && !vi.is_zero() {
                    dot += ai * vi;
                }
            }
            if !dot.is_zero() {
                return false;
            }
        }
    }
    // (b) identical covolume. `gram_det` declines a singular Gram matrix, so a
    // rank-deficient candidate cannot pass here either.
    match (gram_det(reference, deadline), gram_det(candidate, deadline)) {
        (Some(reference_det), Some(candidate_det)) => reference_det == candidate_det,
        _ => false,
    }
}

/// What an individual row of the reduced model IS, in the caller's frame.
///
/// A certificate lift needs this and a solution lift does not, which is why it
/// arrives with [`crate::cert_lift`]: a reduced-frame multiplier on a reduced
/// row is only translatable if the row can be named as an ORIGINAL model fact.
/// The reformulation emits exactly two kinds, in this order — every surviving
/// row (folded), then one row per member of `C` with a finite bound side.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum KernelRowOrigin {
    /// The reduced row is original row `.0` with `x_C = x_p + B z` substituted.
    /// As a FACT about a feasible point it is that original row, unchanged.
    Folded(usize),
    /// The reduced row re-imposes the finite bound sides of original column
    /// `.0`: its lower side is `x_j − lo_j >= 0` and its upper side is
    /// `up_j − x_j >= 0`, written in the `z` frame.
    ColumnBound(usize),
}

/// How to lift a solution of the kernel-reformulated model back to the caller's
/// full column space, and how to correct a reported objective value.
///
/// The shape deliberately mirrors [`crate::presolve::SingletonPostsolve`]: a
/// column map for the survivors, an exact recovery rule for the columns that
/// went away, and an exact `const_delta` that NEVER travels through `f64`.
///
/// The fields are `pub(crate)` because [`crate::cert_lift`] translates reduced
/// CERTIFICATES with the same data this translates points with; see
/// `KernelPostsolve::lift_farkas` there for the algebra.
pub(crate) struct KernelPostsolve {
    pub(crate) n_orig: usize,
    /// Original column -> reduced column, or `None` for a member of `C`.
    pub(crate) map: Vec<Option<Col>>,
    /// The members of `C`, ascending — the index space of `xp` and `basis`.
    pub(crate) cols_c: Vec<usize>,
    /// `x_p`, the integer particular solution, one entry per member of `C`.
    pub(crate) xp: Vec<BigRational>,
    /// The reduced kernel basis: `basis[t][p]` is coordinate `p` of `b_t`.
    pub(crate) basis: Vec<Vec<BigRational>>,
    /// Reduced column carrying `z_t`.
    pub(crate) z: Vec<Col>,
    /// The ORIGINAL row indices of `E`, the equality rows the substitution
    /// deleted, in the order their coefficients were read. A certificate lift
    /// re-derives multipliers for exactly these.
    pub(crate) e_rows: Vec<usize>,
    /// What each reduced row is, indexed by reduced row index.
    pub(crate) reduced_rows: Vec<KernelRowOrigin>,
    /// `c_C·x_p` — the objective constant the substitution folds out. Kept as an
    /// exact `BigRational` and added at expansion time, because it need not be
    /// representable as the reduced model's `f64` offset.
    pub(crate) const_delta: BigRational,
}

impl KernelPostsolve {
    /// The constant to add to a reduced-model objective value / dual bound to
    /// recover the caller-frame value.
    pub(crate) fn const_delta(&self) -> &BigRational {
        &self.const_delta
    }

    /// Widen a reduced-model point to the caller's full column space, computing
    /// `x_C = x_p + B z` EXACTLY.
    pub(crate) fn widen(&self, reduced: &[BigRational]) -> Vec<BigRational> {
        let mut full = vec![BigRational::zero(); self.n_orig];
        for (orig, slot) in self.map.iter().enumerate() {
            if let Some(nc) = slot {
                if let Some(v) = reduced.get(nc.index()) {
                    full[orig] = v.clone();
                }
            }
        }
        for (p, &j) in self.cols_c.iter().enumerate() {
            let mut acc = self.xp[p].clone();
            for (t, bt) in self.basis.iter().enumerate() {
                if bt[p].is_zero() {
                    continue;
                }
                if let Some(v) = reduced.get(self.z[t].index()) {
                    acc += &bt[p] * v;
                }
            }
            full[j] = acc;
        }
        full
    }
}

/// AARDAL–HURKENS–LENSTRA LATTICE COLUMN-BASIS REFORMULATION, as a ROOT MODEL
/// REFORMULATION: change coordinates on a block of integer columns so that
/// ordinary single-variable branching in the new frame is branching on GENERAL
/// LATTICE DISJUNCTIONS in the old one.
///
/// # The measurement this exists for
///
/// MIPLIB `ej` is one row and three columns —
/// `min x₀ s.t. 31013·x₀ − 41014·x₁ − 51015·x₂ = 0`, all integer, `x₀ ≥ 1`,
/// `x₁,x₂ ≥ 0` and unbounded above, optimum 25508. AY loses it: 235,008 nodes,
/// 28.9 s, dual bound stuck at 1. It is NOT an unbounded-domain defect —
/// ORACLE-TIGHT bounds derived from the true optimum still fail (316,909 nodes,
/// no proof). The node LP bound is `max(1, (41014·lo(x₁) + 51015·lo(x₂))/31013)`,
/// so it moves ONLY with lower bounds, and single-variable branching needs ~1e8
/// leaves to walk them up. The reformulation below solves the same instance in
/// **5 nodes, 0.000 s** with stock branch and bound — and its new columns are
/// FREE (unbounded on BOTH sides), which is the part that makes it work rather
/// than a fresh bounding problem.
///
/// # The transform
///
/// `E` is a set of equality rows over integral columns; `C` is the block of
/// columns they touch; `A x_C = b` is that system cleared to integers. Then
/// `x_C = x_p + B z` where `A x_p = b` (an integer particular solution) and `B`
/// is an LLL-reduced basis of `L = {y ∈ ℤ^|C| : A y = 0}`. The `|C|` columns and
/// `|E|` rows go away, `d = |C| − rank(A)` FREE INTEGER columns `z` arrive, and
/// each originally-FINITE column bound side comes back as one row
/// `lo_j ≤ (x_p + B z)_j ≤ up_j` (an infinite side contributes NO row, which is
/// exactly what keeps `z` free).
///
/// # Soundness
///
/// Everything is discharged HERE, at build time; any failure returns `None` and
/// the caller solves the original model untouched. Nothing about this reasoning
/// mentions `ej` — the gate is a property of the MODEL.
///
/// * **S1 — unimodularity ⟹ bijection.** `z ↦ x_p + B z` must be a BIJECTION
///   `ℤ^d → {x ∈ ℤ^|C| : A x = b}`. (a) `A·b_t = 0` over `BigInt` for every
///   basis vector, (b) LLL preserves the covolume exactly, (c) `B` spans the
///   FULL kernel — see [`kernel_basis_is_same_lattice`] and
///   [`hnf_kernel_invariant_holds`], and read the warning in the former: (a)
///   alone is passed by a DOUBLED basis spanning an index-2 sublattice, which
///   would delete half the feasible points and report a worse value as OPTIMAL.
/// * **S2 — exact fold.** Every folded coefficient (`M·B` for a row, `c_C·B` for
///   the objective) is computed in `BigInt`/`BigRational`, and the whole
///   reformulation DECLINES if any changed coefficient or bound does not convert
///   back to `f64` EXACTLY — the identical rule `presolve::substitute_singletons`
///   enforces.
/// * **S3 — bound rows lose nothing.** Each finite column bound becomes a row on
///   `z` with identical rational content, and an infinite side becomes no row.
///   By S1 the correspondence is a bijection, so no integer point of the
///   original box is added or removed.
/// * **S4 — the representative is near the box.** S1–S3 constrain the reduced
///   feasible SET; they say nothing about the SCALE of the numbers written on
///   it, and `x_p` sets that scale for all of them. [`hnf_particular`] returns
///   whichever coset representative the Hermite solve lands on, whose entries
///   are O(det); MEASURED, that is ~5.9·10¹⁵ against a `[0,5]` box, which puts
///   `const_delta` in `[2^52, 2^53)` where the `f64` ULP is 1 and makes the
///   reduced LP resolve the objective at the granularity of the answer. Every
///   individual number stays `as_exact_f64`-clean, so S2 never fires and a wrong
///   `Optimal` comes back SILENTLY. [`translate_near_box`] moves `x_p` to the
///   representative nearest the box ([`box_target`]) by exact Babai
///   nearest-plane, and the SAME exact `A x = b` check that guards
///   [`hnf_particular`] runs again on the result: `A·B = 0` makes that an
///   identity for any integer translation, so a failure is a bug in the
///   translation and the reformulation declines.
///
/// An inexact-coefficient model is declined wholesale (same fail-closed rule as
/// `presolve.rs:87` and `detect` above): the reasoning below reads the public
/// `f64` matrix, and on a model whose true coefficients are rounded proxies that
/// is the wrong matrix. `AY_MILP_NO_KERNEL_REFORM` is the kill switch.
///
/// Returns the reduced model and its postsolve, or `None`.
pub(crate) fn reformulate_kernel(model: &Model) -> Option<(Model, KernelPostsolve)> {
    reformulate_kernel_inner(model, true)
}

/// TEST SEAM — the reformulation with the ISOLATION GATE RELAXED. Not reachable
/// from a shipped build: [`reformulate_kernel`] is the only production entry and
/// it always passes `require_isolated = true`.
///
/// It exists because the two models that exposed the missing translation step
/// are of the NON-ISOLATED shape (a surviving row touches `C`, so the folded
/// shift `Σ a_j·x_p[j]` is nonzero and carries `x_p`'s magnitude into a row that
/// stays in the model). On the isolated shape that shift is identically zero,
/// which is the whole reason the defect was unreachable — so a regression test
/// that can only see the isolated shape cannot see the defect either. Widening
/// the shipped gate is a separate, measured decision; this only lets the tests
/// look at the arithmetic.
#[cfg(test)]
pub(crate) fn reformulate_kernel_nonisolated_for_test(
    model: &Model,
) -> Option<(Model, KernelPostsolve)> {
    reformulate_kernel_inner(model, false)
}

fn reformulate_kernel_inner(
    model: &Model,
    require_isolated: bool,
) -> Option<(Model, KernelPostsolve)> {
    use num_integer::Integer;

    if crate::tune::on(crate::tune::Knob::NoKernelReform) || model.has_inexact_coeffs() {
        return None;
    }
    let deadline = Instant::now() + std::time::Duration::from_secs(KERNEL_REFORM_SECS);
    let nc = model.num_cols();
    let nr = model.num_rows();
    if nc == 0 || nr == 0 {
        return None;
    }
    let trace = std::env::var_os("AY_MILP_TRACE").is_some();

    // ---- THE GATE -------------------------------------------------------
    // E := equality rows whose support is entirely integral columns.
    let integral: Vec<bool> = (0..nc)
        .map(|j| model.col_kind(Col(j as u32)).is_integral())
        .collect();
    let mut e_rows: Vec<usize> = Vec::new();
    let mut in_c = vec![false; nc];
    for i in 0..nr {
        let (coeffs, rlo, rup) = model.row(Row(i as u32));
        if coeffs.is_empty() || !rlo.is_finite() || !rup.is_finite() || rlo != rup {
            continue;
        }
        if coeffs.iter().any(|&(c, _)| !integral[c as usize]) {
            continue;
        }
        e_rows.push(i);
        for &(c, _) in coeffs {
            in_c[c as usize] = true;
        }
    }
    // `cols_c` hoisted above the |E| test so the census can isolate the population the
    // |E| cap UNIQUELY excludes. Behaviour-identical: both branches return None, and
    // `cols_c` depends only on `in_c`/`nc`, which are final above.
    let cols_c: Vec<usize> = (0..nc).filter(|&j| in_c[j]).collect();
    if e_rows.is_empty() || e_rows.len() > KERNEL_MAX_ROWS {
        // FORGONE COST. AHL reformulation is a confirmed verdict producer (ej: 235,008
        // nodes / 28.9s with the dual bound stuck at 1, versus 5 nodes reformulated).
        // KERNEL_MAX_ROWS' doc is a bare restatement and silently inherits the sibling
        // |C| cap's cubic-BigInt rationale — but every cost named there is cubic in
        // |C|, which the NEXT test already bounds. Charge only "|C| fits, |E| does
        // not", which drops the set-partition shapes the |C| cap would decline anyway.
        if !e_rows.is_empty() && !cols_c.is_empty() && cols_c.len() <= KERNEL_MAX_COLS {
            crate::sepstat::gate_charge(crate::sepstat::GATE_KERNEL_MAX_ROWS, e_rows.len() as u64);
        }
        return None;
    }
    if cols_c.is_empty() || cols_c.len() > KERNEL_MAX_COLS {
        return None;
    }
    // Every column of C is integral by construction of E; it must ALSO be
    // touched by no row outside E, or folding E away would strand a row that
    // still mentions it.
    let mut is_e = vec![false; nr];
    for &i in &e_rows {
        is_e[i] = true;
    }
    if require_isolated {
        for i in 0..nr {
            if is_e[i] {
                continue;
            }
            let (coeffs, _, _) = model.row(Row(i as u32));
            if coeffs.iter().any(|&(c, _)| in_c[c as usize]) {
                return None;
            }
        }
    }
    // APPLICABILITY: "the box does not bound the equalities". Either some column
    // of C is unbounded on a side, or a coefficient of E is larger than the
    // widest finite column range in C — in both cases a node LP's bound on the
    // equality moves by a fraction of a unit per unit of branching, which is the
    // regime single-variable branching cannot close and a change of coordinates
    // can. Outside it, the reformulation is a coordinate change nobody asked for
    // and the ordinary search is left alone.
    let mut any_infinite_side = false;
    let mut widest_finite_range: Option<BigRational> = None;
    for &j in &cols_c {
        let (l, u) = model.col_bounds(Col(j as u32));
        if !l.is_finite() || !u.is_finite() {
            any_infinite_side = true;
            continue;
        }
        let range = exact(u)? - exact(l)?;
        if widest_finite_range.as_ref().is_none_or(|w| &range > w) {
            widest_finite_range = Some(range);
        }
    }
    let mut max_abs_coeff = BigRational::zero();
    for &i in &e_rows {
        let (coeffs, _, _) = model.row(Row(i as u32));
        for &(_, a) in coeffs {
            let m = exact(a)?.abs();
            if m > max_abs_coeff {
                max_abs_coeff = m;
            }
        }
    }
    let coefficients_outgrow_the_box = widest_finite_range
        .as_ref()
        .is_some_and(|w| &max_abs_coeff > w);
    if !any_infinite_side && !coefficients_outgrow_the_box {
        return None;
    }

    // ---- THE SYSTEM `A x_C = b`, exactly over BigInt ---------------------
    let mut pos = vec![usize::MAX; nc];
    for (p, &j) in cols_c.iter().enumerate() {
        pos[j] = p;
    }
    let n = cols_c.len();
    let m = e_rows.len();
    let mut abig: Vec<Vec<BigInt>> = Vec::with_capacity(m);
    let mut bbig: Vec<BigInt> = Vec::with_capacity(m);
    for &i in &e_rows {
        let (coeffs, rlo, _) = model.row(Row(i as u32));
        // Clear the row by the LCM of its denominators — the same technique
        // `detect` uses, and the same ceiling on how far it may scale.
        let rhs = exact(rlo)?;
        let mut mult = rhs.denom().clone();
        let mut terms: Vec<(usize, BigRational)> = Vec::with_capacity(coeffs.len());
        for &(c, a) in coeffs {
            let q = exact(a)?;
            mult = mult.lcm(q.denom());
            terms.push((pos[c as usize], q));
        }
        if mult.is_zero() || mult > BigInt::from(MAX_ROW_SCALE) {
            return None;
        }
        let mult_q = BigRational::from(mult);
        let mut arow = vec![BigInt::zero(); n];
        for (p, q) in terms {
            let v = q * &mult_q;
            debug_assert!(v.is_integer(), "LCM of denominators clears every term");
            arow[p] = v.to_integer();
        }
        let rv = rhs * &mult_q;
        debug_assert!(rv.is_integer(), "the LCM includes the rhs denominator");
        bbig.push(rv.to_integer());
        abig.push(arow);
    }

    // ---- KERNEL + PARTICULAR SOLUTION, with S1 discharged -----------------
    let (u, rank, mm) = col_hnf(&abig, m, n, deadline)?;
    if !hnf_kernel_invariant_holds(&abig, &u, &mm, rank, n, deadline) {
        return None; // S1(c)
    }
    let d = n.checked_sub(rank)?;
    if d == 0 {
        return None; // the equalities pin x_C outright: nothing to re-coordinate
    }
    let xp_raw = hnf_particular(&mm, &u, m, n, rank, &bbig, deadline)?;
    // Independent re-check of the particular solution: `A x_p == b` exactly.
    // Cheap, and it means a bug in the HNF solve cannot shift the whole feasible
    // set by a constant.
    if !satisfies_exactly(&abig, &bbig, &xp_raw) {
        return None;
    }
    let k0: Vec<Vec<BigInt>> = (0..d)
        .map(|t| (0..n).map(|i| u[i][rank + t].clone()).collect())
        .collect();
    let basis = lll(k0.clone(), deadline)?;
    if !kernel_basis_is_same_lattice(&abig, &k0, &basis, n, deadline) {
        return None; // S1(a) + S1(b)
    }

    // ---- S4 — THE AHL TRANSLATION, `x_p ← x_p − B·round(B⁺(x_p − t))` -----
    // `hnf_particular` returns the representative the Hermite solve lands on,
    // whose magnitude is O(det) and has nothing to do with the model; every
    // number emitted below is `x_p` plus something box-sized, so an untranslated
    // `x_p` sets the SCALE of the entire reduced model. See
    // [`translate_near_box`] for the measurement and for why the resulting f64
    // cancellation is silent rather than fail-closed.
    //
    // Soundness is by `A·B = 0`: subtracting an integer combination of kernel
    // vectors moves `x_p` inside its own coset, so the map `z ↦ x_p + B z` covers
    // exactly the same set — only the labelling of `z` changes. That is asserted
    // rather than argued: the SAME exact `A x == b` check runs again on the
    // translated point, and a failure declines the reformulation outright.
    let target = box_target(model, &cols_c)?;
    let xp = translate_near_box(&xp_raw, &basis, &target, deadline)?;
    if !satisfies_exactly(&abig, &bbig, &xp) {
        return None; // S4: a botched translation is not shippable
    }

    let xp_q: Vec<BigRational> = xp.iter().cloned().map(BigRational::from).collect();
    let basis_q: Vec<Vec<BigRational>> = basis
        .iter()
        .map(|v| v.iter().cloned().map(BigRational::from).collect())
        .collect();

    // ---- THE REDUCED MODEL, with S2 fail-closed on every folded number ----
    let mut out = Model::new();
    out.inherit_ft_adoption_solve_latch(model);
    let mut map: Vec<Option<Col>> = vec![None; nc];
    for j in 0..nc {
        if in_c[j] {
            continue;
        }
        let col = Col(j as u32);
        let (lb, ub) = model.col_bounds(col);
        let nj = match model.col_kind(col) {
            crate::model::ColKind::Continuous => out.add_col(lb, ub),
            crate::model::ColKind::Binary => out.add_binary_col(),
            crate::model::ColKind::Integer => out.add_int_col(lb, ub),
        };
        out.cols[nj.index()].lb = lb;
        out.cols[nj.index()].ub = ub;
        map[j] = Some(nj);
    }
    // FREE on BOTH sides. This is not an oversight to be tidied up later: the
    // measurement that validates the whole device is the free-column one, and
    // any box on `z` would re-import the bounding problem the reformulation
    // exists to dissolve. The originally-finite column bounds are re-imposed
    // below as ROWS, which is where they belong.
    let zcols: Vec<Col> = (0..d)
        .map(|_| out.add_int_col(f64::NEG_INFINITY, f64::INFINITY))
        .collect();

    // Surviving rows, with `x_C = x_p + B z` substituted. The gate guarantees no
    // surviving row touches `C`, so in practice this fold is the identity — it
    // is written out in full anyway so the transform is correct on its own terms
    // rather than on the gate's.
    //
    // `reduced_rows` records what each emitted row IS in the caller's frame, in
    // emission order. It is written HERE rather than reconstructed later because
    // only this loop knows which rows `add_row` actually received.
    let mut reduced_rows: Vec<KernelRowOrigin> = Vec::with_capacity(nr + cols_c.len());
    for i in 0..nr {
        if is_e[i] {
            continue;
        }
        let (coeffs, rlo, rup) = model.row(Row(i as u32));
        let mut terms: Vec<(Col, f64)> = Vec::with_capacity(coeffs.len() + d);
        let mut shift = BigRational::zero();
        let mut zc = vec![BigRational::zero(); d];
        for &(c, a) in coeffs {
            let cj = c as usize;
            if in_c[cj] {
                let p = pos[cj];
                let aq = exact(a)?;
                shift += &aq * &xp_q[p];
                for (t, bt) in basis_q.iter().enumerate() {
                    if !bt[p].is_zero() {
                        zc[t] += &aq * &bt[p];
                    }
                }
            } else {
                terms.push((map[cj]?, a));
            }
        }
        for (t, v) in zc.iter().enumerate() {
            if !v.is_zero() {
                terms.push((zcols[t], as_exact_f64(v)?));
            }
        }
        let nlo = if rlo.is_finite() {
            as_exact_f64(&(exact(rlo)? - &shift))?
        } else {
            f64::NEG_INFINITY
        };
        let nup = if rup.is_finite() {
            as_exact_f64(&(exact(rup)? - &shift))?
        } else {
            f64::INFINITY
        };
        let emitted = out.add_row(nlo, nup, &terms);
        debug_assert_eq!(emitted.index(), reduced_rows.len());
        reduced_rows.push(KernelRowOrigin::Folded(i));
    }

    // S3: one row per member of `C` with at least one finite bound side, with
    // identical rational content. An infinite side stays infinite, so it costs
    // nothing and constrains nothing.
    for (p, &j) in cols_c.iter().enumerate() {
        let (l, u_b) = model.col_bounds(Col(j as u32));
        if !l.is_finite() && !u_b.is_finite() {
            continue;
        }
        let mut terms: Vec<(Col, f64)> = Vec::with_capacity(d);
        for (t, bt) in basis_q.iter().enumerate() {
            if !bt[p].is_zero() {
                terms.push((zcols[t], as_exact_f64(&bt[p])?));
            }
        }
        let nlo = if l.is_finite() {
            as_exact_f64(&(exact(l)? - &xp_q[p]))?
        } else {
            f64::NEG_INFINITY
        };
        let nup = if u_b.is_finite() {
            as_exact_f64(&(exact(u_b)? - &xp_q[p]))?
        } else {
            f64::INFINITY
        };
        if terms.is_empty() {
            // `x_j` is CONSTANT at `x_p[j]` in the new frame. Its bound is then
            // either satisfied by construction (drop the row — `add_row` would
            // reject an empty one anyway) or violated, in which case the model is
            // infeasible. Emitting INFEASIBLE is not this function's job, so
            // decline and let the search adjudicate it.
            if (l.is_finite() && nlo > 0.0) || (u_b.is_finite() && nup < 0.0) {
                return None;
            }
            continue;
        }
        let emitted = out.add_row(nlo, nup, &terms);
        debug_assert_eq!(emitted.index(), reduced_rows.len());
        reduced_rows.push(KernelRowOrigin::ColumnBound(j));
    }

    // Objective: `c_C·x_C = c_C·x_p + (c_C·B)·z`. The linear part lands on `z`
    // (exact-`f64` fail-closed); the constant rides `const_delta` as an exact
    // rational and never touches an `f64`.
    let mut const_delta = BigRational::zero();
    let mut zobj = vec![BigRational::zero(); d];
    let mut obj_terms: Vec<(Col, f64)> = Vec::new();
    for j in 0..nc {
        let cf = model.obj_coeff(Col(j as u32));
        if cf == 0.0 {
            continue;
        }
        if in_c[j] {
            let p = pos[j];
            let cq = exact(cf)?;
            const_delta += &cq * &xp_q[p];
            for (t, bt) in basis_q.iter().enumerate() {
                if !bt[p].is_zero() {
                    zobj[t] += &cq * &bt[p];
                }
            }
        } else {
            obj_terms.push((map[j]?, cf));
        }
    }
    for (t, v) in zobj.iter().enumerate() {
        if !v.is_zero() {
            obj_terms.push((zcols[t], as_exact_f64(v)?));
        }
    }
    // An objective-free model must stay objective-free: `set_objective` would
    // flip `has_objective`, and the LP and MILP lanes then disagree about
    // whether the answer is `Optimal { value: 0 }` or `Feasible`.
    if model.has_objective() {
        out.set_objective(&obj_terms, model.sense());
        out.set_objective_offset(model.objective_offset());
    }

    if trace {
        eprintln!(
            "AY_MILP_TRACE kernel-reform: |E|={m} |C|={n} rank={rank} d={d}; \
             model {}r/{}c -> {}r/{}c",
            nr,
            nc,
            out.num_rows(),
            out.num_cols(),
        );
        // THE MAGNITUDE MEASUREMENT the translation exists for, raw vs
        // translated, on the three families of number that carry `x_p` into the
        // reduced model. Reported side by side because "the reduced model is
        // O(box) rather than O(det)" is the only evidence that S4 does anything;
        // if these do not shrink, the translation is wrong.
        let emitted = |x: &[BigRational]| -> (BigRational, BigRational, BigRational) {
            let mut bound_rhs = BigRational::zero();
            let mut fold_shift = BigRational::zero();
            let bump = |acc: &mut BigRational, v: BigRational| {
                let a = v.abs();
                if a > *acc {
                    *acc = a;
                }
            };
            for (p, &j) in cols_c.iter().enumerate() {
                let (l, ub) = model.col_bounds(Col(j as u32));
                for side in [l, ub] {
                    if side.is_finite() {
                        if let Some(q) = exact(side) {
                            bump(&mut bound_rhs, q - &x[p]);
                        }
                    }
                }
            }
            for i in 0..nr {
                if is_e[i] {
                    continue;
                }
                let (coeffs, _, _) = model.row(Row(i as u32));
                let mut shift = BigRational::zero();
                for &(c, a) in coeffs {
                    if in_c[c as usize] {
                        if let Some(q) = exact(a) {
                            shift += q * &x[pos[c as usize]];
                        }
                    }
                }
                bump(&mut fold_shift, shift);
            }
            let mut cd = BigRational::zero();
            for j in 0..nc {
                if in_c[j] {
                    if let Some(q) = exact(model.obj_coeff(Col(j as u32))) {
                        cd += q * &x[pos[j]];
                    }
                }
            }
            (bound_rhs, fold_shift, cd.abs())
        };
        let raw_q: Vec<BigRational> = xp_raw.iter().cloned().map(BigRational::from).collect();
        let (rb, rf, rc) = emitted(&raw_q);
        let (tb, tf, tc) = emitted(&xp_q);
        let f = |v: &BigRational| v.to_f64().unwrap_or(f64::INFINITY);
        eprintln!(
            "AY_MILP_TRACE kernel-reform-magnitude: max|x_p| {:.6e} -> {:.6e}; \
             bound-rhs {:.6e} -> {:.6e}; folded-shift {:.6e} -> {:.6e}; \
             |const_delta| {:.6e} -> {:.6e}",
            BigRational::from(max_abs_big(&xp_raw))
                .to_f64()
                .unwrap_or(f64::INFINITY),
            BigRational::from(max_abs_big(&xp))
                .to_f64()
                .unwrap_or(f64::INFINITY),
            f(&rb),
            f(&tb),
            f(&rf),
            f(&tf),
            f(&rc),
            f(&tc),
        );
    }

    Some((
        out,
        KernelPostsolve {
            n_orig: nc,
            map,
            cols_c,
            xp: xp_q,
            basis: basis_q,
            z: zcols,
            e_rows,
            reduced_rows,
            const_delta,
        },
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{Col, Model, Sense};
    use std::time::Duration;

    /// Build a market-split min-total-slack model: `A x + s = b`, `min Σ s_i`,
    /// `x ∈ {0,1}^n`, `s ≥ 0` — the markshare1 shape in miniature.
    fn market_split(a: &[Vec<i64>], b: &[i64]) -> Model {
        let n = a[0].len();
        let mut m = Model::new();
        let x: Vec<Col> = (0..n).map(|_| m.add_binary_col()).collect();
        let s: Vec<Col> = (0..a.len())
            .map(|_| m.add_col(0.0, f64::INFINITY))
            .collect();
        for (i, row) in a.iter().enumerate() {
            let mut terms: Vec<(Col, f64)> = row
                .iter()
                .enumerate()
                .filter(|&(_, &c)| c != 0)
                .map(|(j, &c)| (x[j], c as f64))
                .collect();
            terms.push((s[i], 1.0));
            m.add_row(b[i] as f64, b[i] as f64, &terms);
        }
        let obj: Vec<(Col, f64)> = s.iter().map(|&c| (c, 1.0)).collect();
        m.set_objective(&obj, Sense::Minimize);
        m
    }

    fn deadline() -> Instant {
        Instant::now() + Duration::from_secs(30)
    }

    fn bigint_basis(rows: &[&[i64]]) -> Vec<Vec<BigInt>> {
        rows.iter()
            .map(|row| row.iter().copied().map(BigInt::from).collect())
            .collect()
    }

    fn bigint_identity(dim: usize) -> Vec<Vec<BigInt>> {
        (0..dim)
            .map(|row| {
                (0..dim)
                    .map(|col| BigInt::from(if row == col { 1 } else { 0 }))
                    .collect()
            })
            .collect()
    }

    fn one_dim_enumeration_engine() -> Engine {
        let zero = Interval { lo: 0.0, hi: 0.0 };
        Engine {
            n: 2,
            k: vec![vec![1, -1]],
            dim: 1,
            u: bigint_identity(2),
            hh: vec![vec![BigInt::one(), BigInt::zero()]],
            rank: 1,
            bstar_q: vec![vec![
                BigRational::from_integer(BigInt::one()),
                BigRational::from_integer(BigInt::from(-1)),
            ]],
            cnorm_q: vec![BigRational::from_integer(BigInt::from(2))],
            cnorm_i: vec![Interval { lo: 2.0, hi: 2.0 }],
            mu_i: vec![vec![zero]],
            box_prune: None,
            lo: vec![0, 0],
            up: vec![1, 1],
            radius_q: BigRational::new(BigInt::one(), BigInt::from(2)),
            radius_f: 0.5,
            deadline: deadline(),
            trace: false,
            threads: 1,
        }
    }

    fn one_dim_enumeration_state<'a>(
        eng: &'a Engine,
        xd: &'a [i64],
        center: Interval,
        radius: f64,
    ) -> EnumState<'a> {
        let zero = Interval { lo: 0.0, hi: 0.0 };
        EnumState {
            eng,
            xd,
            tg: vec![center],
            radius,
            y: vec![0],
            partial: vec![vec![zero]],
            cflat: Vec::new(),
            base_absmax: 0.0,
            base_halfw: 0.0,
            box_on: false,
            nodes: 0,
            node_cap: NODE_BUDGET,
            shared_nodes: None,
            shared_budget: NODE_BUDGET,
            reserved: 0,
            aborted: false,
            capped: false,
            cancel: None,
            cancelled: false,
        }
    }

    fn two_dim_enumeration_engine() -> Engine {
        let zero = Interval { lo: 0.0, hi: 0.0 };
        let one = BigRational::from_integer(BigInt::one());
        let zero_q = BigRational::zero();
        Engine {
            n: 2,
            k: vec![vec![1, 0], vec![0, 1]],
            dim: 2,
            u: bigint_identity(2),
            hh: Vec::new(),
            rank: 0,
            bstar_q: vec![vec![one.clone(), zero_q.clone()], vec![zero_q, one]],
            cnorm_q: vec![
                BigRational::from_integer(BigInt::one()),
                BigRational::from_integer(BigInt::one()),
            ],
            cnorm_i: vec![Interval { lo: 1.0, hi: 1.0 }, Interval { lo: 1.0, hi: 1.0 }],
            mu_i: vec![vec![zero; 2]; 2],
            box_prune: None,
            lo: vec![0, 0],
            up: vec![1, 1],
            radius_q: BigRational::new(BigInt::one(), BigInt::from(2)),
            radius_f: 0.5,
            deadline: deadline(),
            trace: false,
            threads: 2,
        }
    }

    #[test]
    fn lattice_thread_resolver_honors_typed_budget_and_ceiling_contract() {
        let deterministic = SolveOpts::new().with_threads(64);
        assert_eq!(
            resolve_lattice_threads(
                &deterministic,
                128,
                Some(OsStr::new("32")),
                Some(OsStr::new("16")),
            ),
            1
        );

        let parallel = SolveOpts::new().with_threads(8).with_determinism(false);
        assert_eq!(resolve_lattice_threads(&parallel, 16, None, None), 8);
        assert_eq!(resolve_lattice_threads(&parallel, 4, None, None), 4);
        assert_eq!(
            resolve_lattice_threads(&parallel, 16, Some(OsStr::new("2")), None),
            2
        );
        assert_eq!(
            resolve_lattice_threads(&parallel, 16, Some(OsStr::new("12")), None),
            8,
            "NBCORE is a ceiling, not an override that can raise typed threads"
        );
        assert_eq!(
            resolve_lattice_threads(&parallel, 16, Some(OsStr::new("6")), Some(OsStr::new("4")),),
            4
        );
        assert_eq!(
            resolve_lattice_threads(&parallel, 16, Some(OsStr::new("invalid")), None),
            1
        );
        assert_eq!(
            resolve_lattice_threads(&parallel, 16, None, Some(OsStr::new("0"))),
            1
        );
        assert_eq!(
            resolve_lattice_threads(
                &SolveOpts::new().with_threads(0).with_determinism(false),
                0,
                None,
                None,
            ),
            1
        );
    }

    #[test]
    fn frontier_cap_aborts_before_emitting_an_unbounded_partition() {
        let eng = two_dim_enumeration_engine();
        let xd = [2, 2];
        let shared = AtomicU64::new(0);
        let zero = Interval { lo: 0.0, hi: 0.0 };
        let mut state = eng.fresh_state(&xd, vec![zero; 2], 8.0, Some(&shared));
        let mut items = Vec::new();
        state.collect(1, zero, 0, &mut items, 1, 0.0, 0.0);
        assert!(state.aborted, "crossing the frontier cap must fail closed");
        assert!(items.len() <= 1);

        let limits = frontier_limits(160, 180, 8).expect("bounded ordinary frontier");
        let payload_per_item =
            size_of::<WorkItem>() + 160 * (size_of::<i64>() + size_of::<Interval>());
        assert!(limits.target <= 8 * LATTICE_FRONTIER_PER_THREAD);
        assert!(limits.cap <= LATTICE_FRONTIER_MAX_BYTES / payload_per_item);
        assert!(frontier_limits(160, 180, usize::MAX).is_none());
    }

    #[test]
    fn target_geometry_removes_only_the_orthogonal_binary_sphere_shell() {
        let eng = one_dim_enumeration_engine();

        // For x_d=(0,1), τ=(1/2,-1/2) lies entirely in span(1,-1), so the
        // projected radius remains the full binary-sphere radius n/4=1/2.
        let (_, full_radius) = eng
            .compute_target_geometry(&[0, 1])
            .expect("finite target geometry");
        assert_eq!(full_radius, 0.5);

        // For x_d=(0,0), τ=(1/2,1/2) is wholly orthogonal to span(1,-1).
        // The only possible binary point on this face is already at projected
        // distance zero, so the provably empty outer shell consumes the entire
        // n/4 radius without excluding that boundary point.
        let (_, tightened_radius) = eng
            .compute_target_geometry(&[0, 0])
            .expect("finite target geometry");
        assert_eq!(tightened_radius, 0.0);
        assert!(matches!(eng.enumerate(&[0, 0]), EnumResult::Feasible(_)));

        // A negative projected radius is a proof that this affine face misses
        // the binary sphere entirely. It is an ordinary empty result, not an
        // arithmetic abort: for x_d=(2,2), the orthogonal residue alone has
        // squared norm 9/2 > n/4.
        let (_, empty_radius) = eng
            .compute_target_geometry(&[2, 2])
            .expect("finite target geometry");
        assert_eq!(empty_radius, -4.0);
        assert_eq!(eng.enumerate(&[2, 2]), EnumResult::Empty);
    }

    #[test]
    fn shared_node_budget_spans_frontier_passes_and_workers() {
        let eng = one_dim_enumeration_engine();
        let xd = [0, 1];
        let center = Interval { lo: 0.5, hi: 0.5 };
        let shared = AtomicU64::new(NODE_BUDGET - 1);

        let mut first = one_dim_enumeration_state(&eng, &xd, center, 0.5);
        first.shared_nodes = Some(&shared);
        assert!(first.record_node());
        assert_eq!(shared.load(Ordering::Relaxed), NODE_BUDGET);

        let mut second = one_dim_enumeration_state(&eng, &xd, center, 0.5);
        second.shared_nodes = Some(&shared);
        assert!(!second.record_node());
        assert!(second.aborted);
        assert_eq!(second.nodes, 0);
        assert_eq!(shared.load(Ordering::Relaxed), NODE_BUDGET);
    }

    #[test]
    fn parallel_combiner_prefers_witness_then_abort_then_empty() {
        let witness = vec![1, -2, 3];
        assert_eq!(
            combine_parallel(Some(witness.clone()), true),
            EnumResult::Feasible(witness)
        );
        assert_eq!(combine_parallel(None, true), EnumResult::Aborted);
        assert_eq!(combine_parallel(None, false), EnumResult::Empty);
    }

    #[test]
    fn scoped_worker_panic_is_joined_as_an_abort() {
        let aborted = AtomicBool::new(false);
        std::thread::scope(|scope| {
            let handle = std::thread::Builder::new()
                .name("ay-lattice-panic-test".to_owned())
                .spawn_scoped(scope, || panic!("injected lattice worker panic"))
                .expect("test worker must spawn");
            join_lattice_worker(handle, &aborted);
        });
        assert!(aborted.load(Ordering::Acquire));
    }

    #[test]
    fn adaptive_bkz_policy_uses_full_dimension_blocks() {
        assert_eq!(adaptive_bkz_beta(BKZ_MIN_KERNEL_DIM - 1), 2);
        assert_eq!(adaptive_bkz_beta(BKZ_MIN_KERNEL_DIM), BKZ_MIN_KERNEL_DIM);
        assert_eq!(adaptive_bkz_beta(53), 53);
        assert_eq!(adaptive_bkz_beta(62), 62);
        // The exact oracle serves every β up to the historical block size; the
        // pruned oracle engages strictly above it — in particular for every
        // full-dimension block the adaptive policy can pick.
        assert!(!bkz_oracle_pruned(BKZ_ADAPTIVE_BETA));
        assert!(bkz_oracle_pruned(BKZ_ADAPTIVE_BETA + 1));
        assert!(bkz_oracle_pruned(BKZ_MIN_KERNEL_DIM));
    }

    #[test]
    fn large_kernels_demote_to_the_proven_exact_path() {
        // Large kernel: always the proven exact β=34 — the full-dimension
        // pruned gamble measurably loses dim-62 verdicts (witness-position
        // re-roll), so no solve slice promotes it.
        assert_eq!(effective_bkz_beta(BKZ_LARGE_KERNEL_DIM), BKZ_ADAPTIVE_BETA);
        assert_eq!(
            effective_bkz_beta(BKZ_LARGE_KERNEL_DIM + 100),
            BKZ_ADAPTIVE_BETA
        );
        // Medium kernels take the pruned full-dimension path; small kernels
        // keep plain LLL.
        assert_eq!(effective_bkz_beta(BKZ_MIN_KERNEL_DIM), BKZ_MIN_KERNEL_DIM);
        assert_eq!(
            effective_bkz_beta(BKZ_LARGE_KERNEL_DIM - 1),
            BKZ_LARGE_KERNEL_DIM - 1
        );
        assert_eq!(effective_bkz_beta(BKZ_MIN_KERNEL_DIM - 1), 2);
        // The demoted exact path keeps the historical tour policy; the pruned
        // path terminates by convergence under the runaway cap.
        assert_eq!(
            adaptive_bkz_tours(BKZ_FEW_TOURS_MIN_DIM, false),
            BKZ_TOURS_LARGE
        );
        assert_eq!(
            adaptive_bkz_tours(BKZ_FEW_TOURS_MIN_DIM - 1, false),
            BKZ_TOURS_SMALL
        );
        assert_eq!(
            adaptive_bkz_tours(BKZ_FEW_TOURS_MIN_DIM, true),
            BKZ_TOURS_PRUNED
        );
    }

    #[test]
    fn pruning_profile_is_monotone_and_exact_at_full_depth() {
        let exact = svp_pruning_profile(5, false);
        assert_eq!(exact, vec![1.0; 5]);
        let pruned = svp_pruning_profile(5, true);
        // prune[p] bounds the partial norm with levels p..d-1 fixed; deeper
        // (smaller p, more coordinates fixed) must be LESS restrictive, and the
        // full-depth bound must be exact so accepted vectors genuinely improve.
        assert_eq!(pruned[0], 1.0);
        for p in 1..5 {
            assert!(pruned[p] < pruned[p - 1]);
            assert!(pruned[p] > 0.0);
        }
    }

    /// The BKZ budget must always STOP strictly before the device deadline so
    /// the exact covolume/kernel validation has time to run; otherwise a BKZ
    /// that ran to the deadline leaves `gram_det` with zero budget and it
    /// declines a perfectly valid (unimodular, covolume-preserving) partial
    /// reduction.  Pin the reserve invariant: `min(0.4·R, 15s) < R` for every
    /// positive remaining budget `R`.
    #[test]
    fn bkz_budget_reserves_validation_margin() {
        assert!(BKZ_BUDGET_FRACTION > 0.0 && BKZ_BUDGET_FRACTION < 1.0);
        assert!(BKZ_ABS_CAP_SECS > 0.0);
        assert!(BKZ_LARGE_ABS_CAP_SECS > 0.0);
        for pruned in [false, true] {
            assert_eq!(bkz_budget(Duration::ZERO, pruned), Duration::ZERO);
            for &r_secs in &[0.001_f64, 0.1, 1.0, 30.0, 60.0, 120.0, 600.0] {
                let r = Duration::from_secs_f64(r_secs);
                let bkz = bkz_budget(r, pruned);
                assert!(
                    bkz < r,
                    "BKZ budget {bkz:?} must leave validation margin under remaining {r:?}"
                );
            }
        }
        assert_eq!(
            bkz_budget(Duration::from_secs(600), false),
            Duration::from_secs_f64(BKZ_ABS_CAP_SECS),
            "the absolute cap must apply to long solve slices"
        );
        assert_eq!(
            bkz_budget(Duration::from_secs(600), true),
            Duration::from_secs_f64(BKZ_LARGE_ABS_CAP_SECS),
            "the large-kernel cap must apply to long pruned slices"
        );
    }

    #[test]
    fn gso_and_lll_decline_immediately_after_deadline() {
        let exact_basis = bigint_identity(3);
        let float_basis = bigint_identity(3);
        let expired = Instant::now();

        assert!(gso_exact(&exact_basis, expired).is_none());
        assert!(gso_float(&float_basis, expired).is_none());
        assert!(lll(float_basis, expired).is_none());
    }

    #[test]
    fn gram_determinant_is_exact_invariant_and_deadline_bounded() {
        let identity = bigint_basis(&[&[1, 0], &[0, 1]]);
        let sheared = bigint_basis(&[&[1, 3], &[0, 1]]);
        let scaled = bigint_basis(&[&[2, 0], &[0, 1]]);

        assert_eq!(gram_det(&identity, deadline()), Some(BigInt::one()));
        assert_eq!(gram_det(&sheared, deadline()), Some(BigInt::one()));
        assert_eq!(gram_det(&scaled, deadline()), Some(BigInt::from(4)));
        assert_eq!(
            gram_det(&[vec![BigInt::one()], vec![]], deadline()),
            None,
            "ragged input must fail closed"
        );
        assert_eq!(
            gram_det(&identity, Instant::now()),
            None,
            "expired exact work must not run past the solve slice"
        );
    }

    #[test]
    fn unimodular_inverse_is_exact_and_rejects_other_matrices() {
        let u = bigint_basis(&[&[1, 2], &[0, 1]]);
        let expected = bigint_basis(&[&[1, -2], &[0, 1]]);
        assert_eq!(unimodular_inverse(&u, deadline()), Some(expected));

        let non_unimodular = bigint_basis(&[&[2, 0], &[0, 1]]);
        assert_eq!(unimodular_inverse(&non_unimodular, deadline()), None);
        let singular = bigint_basis(&[&[1, 1], &[1, 1]]);
        assert_eq!(unimodular_inverse(&singular, deadline()), None);
        assert_eq!(unimodular_inverse(&u, Instant::now()), None);
    }

    #[test]
    fn apply_block_inserts_primitive_vector_and_preserves_lattice() {
        let basis = bigint_basis(&[&[1, 0, 0], &[0, 1, 0], &[0, 0, 1]]);
        let reduced =
            apply_block(&basis, 0, 2, &[1, 1, 0], deadline()).expect("primitive block insertion");

        assert_eq!(reduced[0], bigint_basis(&[&[1, 1, 0]])[0]);
        assert_eq!(
            gram_det(&basis, deadline()),
            gram_det(&reduced, deadline()),
            "unimodular re-basification must preserve exact covolume"
        );
        assert!(apply_block(&basis, 0, 2, &[1, 1, 0], Instant::now()).is_none());
    }

    #[test]
    fn beta_three_bkz_executes_and_preserves_the_exact_lattice() {
        let basis = bigint_basis(&[&[4, 1, 0], &[1, 3, 1], &[0, 1, 2]]);
        let reduced = bkz(basis.clone(), 3, false, deadline(), false, 1);

        assert_eq!(reduced.len(), basis.len());
        assert_eq!(
            gram_det(&basis, deadline()),
            gram_det(&reduced, deadline()),
            "BKZ(3) must preserve the lattice"
        );
    }

    #[test]
    fn pruned_bkz_executes_and_preserves_the_exact_lattice() {
        let basis = bigint_basis(&[&[9, 1, 0, 2], &[1, 8, 1, 0], &[0, 1, 7, 1], &[2, 0, 1, 6]]);
        let reduced = bkz(basis.clone(), 4, true, deadline(), false, 1);

        assert_eq!(reduced.len(), basis.len());
        assert_eq!(
            gram_det(&basis, deadline()),
            gram_det(&reduced, deadline()),
            "pruned-oracle BKZ must preserve the lattice"
        );
    }

    #[test]
    fn adaptive_beta_34_bkz_path_executes_on_threshold_dimension() {
        // The demoted large-kernel path (short slice) still runs the proven
        // exact BKZ(34); pin that the exact-oracle machinery accepts the
        // threshold dimension unchanged on an orthonormal basis.
        let basis = bigint_identity(BKZ_MIN_KERNEL_DIM);
        let reduced = bkz(
            basis.clone(),
            BKZ_ADAPTIVE_BETA,
            false,
            deadline(),
            false,
            1,
        );
        assert_eq!(
            reduced, basis,
            "orthonormal input should traverse BKZ(34) without changing its lattice basis"
        );
    }

    fn kernel_selection_fixture() -> MarketSplit {
        MarketSplit {
            n: 3,
            m: 1,
            a: vec![vec![1, 0, 0]],
            b: vec![0],
            lo: vec![0, 0, 0],
            up: vec![1, 1, 1],
            col_model: vec![Some(0), Some(1), Some(2)],
            obj_rows: vec![0],
            slack_col: vec![3],
            singleton_cols: vec![],
        }
    }

    #[test]
    fn invalid_bkz_candidates_fall_back_to_lll() {
        let ms = kernel_selection_fixture();
        let lll = bigint_basis(&[&[0, 1, 0], &[0, 0, 1]]);
        let expected = vec![vec![0, 1, 0], vec![0, 0, 1]];

        // A huge unimodular shear has the same exact Gram determinant but does
        // not fit the enumerator's i64 representation.
        let huge = BigInt::from(i64::MAX) + BigInt::one();
        let too_wide = vec![
            vec![BigInt::zero(), BigInt::one(), huge],
            vec![BigInt::zero(), BigInt::zero(), BigInt::one()],
        ];
        let (selected, used_bkz) =
            select_checked_kernel_basis(&lll, Some(&too_wide), &ms, deadline(), false)
                .expect("LLL fallback after width rejection");
        assert_eq!(selected, expected);
        assert!(!used_bkz);

        // Equal covolume alone is not enough: a candidate that leaves A's
        // kernel must likewise fall back rather than abort the device.
        let outside_kernel = bigint_basis(&[&[1, 0, 0], &[0, 0, 1]]);
        let (selected, used_bkz) =
            select_checked_kernel_basis(&lll, Some(&outside_kernel), &ms, deadline(), false)
                .expect("LLL fallback after kernel rejection");
        assert_eq!(selected, expected);
        assert!(!used_bkz);
    }

    #[test]
    fn valid_bkz_candidate_is_selected() {
        let ms = kernel_selection_fixture();
        let lll = bigint_basis(&[&[0, 1, 0], &[0, 0, 1]]);
        let candidate = bigint_basis(&[&[0, 1, 2], &[0, 0, 1]]);
        let expected = vec![vec![0, 1, 2], vec![0, 0, 1]];

        let (selected, used_bkz) =
            select_checked_kernel_basis(&lll, Some(&candidate), &ms, deadline(), false)
                .expect("valid candidate");
        assert_eq!(selected, expected);
        assert!(used_bkz);
    }

    fn assert_encloses(iv: Interval, exact: &BigRational) {
        let lo = BigRational::from_float(iv.lo).expect("finite lower endpoint");
        let hi = BigRational::from_float(iv.hi).expect("finite upper endpoint");
        assert!(
            (lo..=hi).contains(exact),
            "interval [{}, {}] does not enclose {exact}",
            iv.lo,
            iv.hi,
        );
    }

    /// Pin the directed-arithmetic premise independently of the lattice
    /// search: conversions and every hot-loop operation must enclose the same
    /// calculation performed over exact rationals.
    #[test]
    fn interval_operations_enclose_exact_rationals() {
        let vals: Vec<BigRational> = (-24..=24)
            .flat_map(|n| (1..=11).map(move |d| BigRational::new(n.into(), d.into())))
            .collect();
        for (i, a) in vals.iter().enumerate() {
            let ai = Interval::from_rational(a).expect("finite interval");
            assert_encloses(ai, a);
            assert_encloses(ai.square().expect("finite square"), &(a * a));

            let scalar = (i as i64 % 13) - 6;
            let scaled = a * BigRational::from_integer(scalar.into());
            assert_encloses(ai.scale(scalar as f64).expect("finite scale"), &scaled);

            let b = &vals[(i * 37 + 17) % vals.len()];
            let bi = Interval::from_rational(b).expect("finite interval");
            assert_encloses(ai.add(bi).expect("finite sum"), &(a + b));
            assert_encloses(ai.sub(bi).expect("finite difference"), &(a - b));

            let ap = a.abs();
            let bp = b.abs();
            let api = Interval::from_rational(&ap).expect("finite positive interval");
            let bpi = Interval::from_rational(&bp).expect("finite positive interval");
            assert_encloses(
                api.mul_nonnegative(bpi).expect("finite product"),
                &(ap * bp),
            );
        }
    }

    fn optimum_one_fixture() -> (Model, MarketSplit, Engine) {
        let model = market_split(&[vec![1, 1, 1, 1], vec![0, 1, 2, 3]], &[2, 6]);
        let split = detect(&model).expect("market-split fixture");
        let engine = Engine::build(&split, deadline(), false, 1, None).expect("lattice engine");
        (model, split, engine)
    }

    #[test]
    fn soft_cap_is_inconclusive_but_full_zero_face_is_empty() {
        // A one-dimensional primitive lattice parallel to x₀, while the face
        // fixes x₁=1 outside the box x₁=0. The wide x₀ interval leaves a
        // positive projected radius, so the complete empty proof genuinely
        // visits several nodes instead of being discharged by geometry alone.
        let mut engine = one_dim_enumeration_engine();
        engine.k = vec![vec![1, 0]];
        engine.bstar_q = vec![vec![
            BigRational::from_integer(BigInt::one()),
            BigRational::zero(),
        ]];
        engine.cnorm_q = vec![BigRational::from_integer(BigInt::one())];
        engine.cnorm_i = vec![Interval { lo: 1.0, hi: 1.0 }];
        engine.lo = vec![0, 0];
        engine.up = vec![10, 0];
        engine.radius_q = BigRational::from_integer(BigInt::from(25));
        engine.radius_f = 25.0;
        let xd = [5, 1];

        let (full, full_nodes) = engine.enumerate_serial_with_cap(&xd, NODE_BUDGET);
        assert_eq!(full, EnumResult::Empty);
        assert!(full_nodes > 0, "fixture must exercise enumeration");

        let soft_cap = full_nodes - 1;
        let (soft, soft_nodes) = engine.enumerate_serial_with_cap(&xd, soft_cap);
        assert_eq!(soft, EnumResult::Capped);
        assert_eq!(
            soft_nodes, soft_cap,
            "soft cap must stop before the node that completes the proof"
        );
        assert!(
            full_nodes > soft_nodes,
            "only the complete proof-grade run may establish emptiness"
        );
    }

    #[test]
    fn witness_at_exact_soft_cap_remains_authoritative() {
        let (_model, split, engine) = optimum_one_fixture();
        let mut rhs = split.b.clone();
        rhs[1] -= 1;
        let xd = engine
            .particular(&split, &rhs)
            .and_then(|point| engine.babai(&point))
            .expect("objective-one witness center");
        let (full, witness_nodes) = engine.enumerate_serial_with_cap(&xd, NODE_BUDGET);
        assert!(
            matches!(full, EnumResult::Feasible(_)),
            "fixture must contain a witness"
        );
        assert!(witness_nodes > 0);

        let (at_cap, at_cap_nodes) = engine.enumerate_serial_with_cap(&xd, witness_nodes);
        assert!(
            matches!(at_cap, EnumResult::Feasible(_)),
            "the node at the exact soft boundary must still be checked"
        );
        assert_eq!(at_cap_nodes, witness_nodes);

        let (below_cap, _) = engine.enumerate_serial_with_cap(&xd, witness_nodes - 1);
        assert_eq!(
            below_cap,
            EnumResult::Capped,
            "one fewer node is inconclusive, never empty"
        );
    }

    #[test]
    fn expired_deadline_takes_precedence_over_soft_cap() {
        let (_model, split, mut engine) = optimum_one_fixture();
        let xd = engine
            .particular(&split, &split.b)
            .and_then(|point| engine.babai(&point))
            .expect("objective-zero center");
        engine.deadline = Instant::now();
        assert_eq!(
            engine.enumerate_serial_with_cap(&xd, 0),
            (EnumResult::Aborted, 0)
        );
    }

    #[test]
    fn capped_witness_faces_are_retried_and_exactly_validated() {
        let (model, split, engine) = optimum_one_fixture();
        let (_k, _y, _xd, capped_runs) = engine
            .witness_hunt_serial(&split, 1)
            .expect("iterative deepening finds an objective-one witness");
        assert!(
            capped_runs > 0,
            "tiny initial cap must exercise an inconclusive retained face"
        );

        match engine.prove(&model, &split) {
            Some(Outcome::Optimal {
                value,
                model_values,
                ..
            }) => {
                assert_eq!(value, BigRational::from(BigInt::from(1)));
                assert!(
                    model.check_point(&model_values).is_ok(),
                    "deepened witness must pass the independent exact checker"
                );
            }
            other => panic!("expected exact Optimal 1 after deepening, got {other:?}"),
        }
    }

    #[test]
    fn schnorr_euchner_order_covers_interval_and_clamps_center() {
        let enclosed_center = Interval { lo: 0.25, hi: 0.75 };
        let visited: Vec<_> = SchnorrEuchnerOrder::new(-2, 3, enclosed_center).collect();
        assert_eq!(
            visited,
            vec![
                (1, EnumSide::Down),
                (0, EnumSide::Down),
                (-1, EnumSide::Down),
                (2, EnumSide::Up),
                (-2, EnumSide::Down),
                (3, EnumSide::Up),
            ]
        );
        let mut covered: Vec<i64> = visited.into_iter().map(|(value, _)| value).collect();
        covered.sort_unstable();
        assert_eq!(covered, (-2..=3).collect::<Vec<_>>());

        let clamped_low = SchnorrEuchnerOrder::new(
            5,
            7,
            Interval {
                lo: -100.0,
                hi: -100.0,
            },
        );
        assert_eq!(
            clamped_low.map(|(value, _)| value).collect::<Vec<_>>(),
            vec![5, 6, 7]
        );
        let clamped_high = SchnorrEuchnerOrder::new(
            -7,
            -5,
            Interval {
                lo: 100.0,
                hi: 100.0,
            },
        );
        assert_eq!(
            clamped_high.map(|(value, _)| value).collect::<Vec<_>>(),
            vec![-5, -6, -7]
        );
    }

    #[test]
    fn enumeration_retains_radius_equality_and_rejects_f64_integer_boundary() {
        let eng = one_dim_enumeration_engine();

        // With K=(1,-1), xd=(0,1), and center 1/2, y=1 produces the
        // binary point (1,0) at exact projected distance
        // (1 - 1/2)^2 * ||K||^2 = 1/2: equality with the radius is retained.
        let equality_xd = [0, 1];
        let mut equality =
            one_dim_enumeration_state(&eng, &equality_xd, Interval { lo: 0.5, hi: 0.5 }, 0.5);
        assert_eq!(
            equality.rec(0, Interval { lo: 0.0, hi: 0.0 }, 0.0, 0.0),
            Some(vec![1])
        );
        assert_eq!(equality.nodes, 1);
        assert!(!equality.aborted);

        // The outward-expanded integer range at either exact-f64 boundary
        // would cross beyond ±2^53. The recursion must abort before casting or
        // visiting a coordinate.
        let boundary_xd = [0, 0];
        for center in [-MAX_EXACT_F64_INT, MAX_EXACT_F64_INT] {
            let mut boundary = one_dim_enumeration_state(
                &eng,
                &boundary_xd,
                Interval {
                    lo: center,
                    hi: center,
                },
                0.0,
            );
            assert_eq!(
                boundary.rec(0, Interval { lo: 0.0, hi: 0.0 }, 0.0, 0.0),
                None
            );
            assert!(boundary.aborted);
            assert_eq!(boundary.nodes, 0);
        }
    }

    #[test]
    fn optimum_one_when_zero_face_is_empty() {
        // Row0: Σx = 2 (exactly two ones); Row1: 0·x0+1·x1+2·x2+3·x3 = 6.
        // No two-subset reaches 6 (max 5) ⟹ objective-0 face EMPTY. But b−e_1
        // = [2,5] is met by x=(0,0,1,1) ⟹ optimum = 1.
        let a = vec![vec![1, 1, 1, 1], vec![0, 1, 2, 3]];
        let b = vec![2, 6];
        let m = market_split(&a, &b);
        match try_prove(&m, deadline(), &SolveOpts::new()) {
            Some(Outcome::Optimal {
                value,
                model_values,
                ..
            }) => {
                assert_eq!(value, BigRational::from(BigInt::from(1)));
                assert!(m.check_point(&model_values).is_ok());
            }
            other => panic!("expected Optimal 1, got {other:?}"),
        }
    }

    #[test]
    fn public_certificate_policy_rejects_uncertified_lattice_optimum() {
        let a = vec![vec![1, 1, 1, 1], vec![0, 1, 2, 3]];
        let b = vec![2, 6];
        let model = market_split(&a, &b);
        assert!(matches!(
            try_prove_configured(&model, deadline(), LatticeSchedule::Threads(1)),
            Some(Outcome::Optimal { cert: None, .. })
        ));

        let opts = SolveOpts::new().with_require_certificates(true);
        let mut session = crate::BabSession::new(model, &opts).expect("valid lattice model");
        assert!(matches!(
            session.check().expect("public solve"),
            Outcome::Unknown {
                reason: crate::UnknownReason::CertificateUnavailable
            }
        ));
    }

    #[test]
    fn optimum_zero_when_a_split_exists() {
        // Two independent parity rows, each satisfiable ⟹ objective-0 face
        // NONEMPTY (e.g. x=(1,0,1,0)) ⟹ optimum = 0.
        let a = vec![vec![1, 1, 0, 0], vec![0, 0, 1, 1]];
        let b = vec![1, 1];
        let m = market_split(&a, &b);
        match try_prove(&m, deadline(), &SolveOpts::new()) {
            Some(Outcome::Optimal {
                value,
                model_values,
                ..
            }) => {
                assert_eq!(value, BigRational::from(BigInt::from(0)));
                assert!(m.check_point(&model_values).is_ok());
            }
            other => panic!("expected Optimal 0, got {other:?}"),
        }
    }

    #[test]
    fn deterministic_public_solves_return_identical_full_model_values() {
        let model = market_split(&[vec![1, 1, 0, 0], vec![0, 0, 1, 1]], &[1, 1]);
        let opts = SolveOpts::new().with_threads(4);
        assert_eq!(
            lattice_threads(&opts),
            1,
            "determinism must select the historical serial lattice traversal"
        );

        let mut expected = None;
        for _ in 0..8 {
            let mut session =
                crate::BabSession::new(model.clone(), &opts).expect("valid lattice model");
            let outcome = session.check().expect("public lattice solve");
            let (value, model_values) = match outcome {
                Outcome::Optimal {
                    value,
                    model_values,
                    ..
                } => (value, model_values),
                other => panic!("expected public Optimal 0, got {other:?}"),
            };
            assert_eq!(value, BigRational::zero());
            assert!(model.check_point(&model_values).is_ok());
            if let Some(expected) = expected.as_ref() {
                assert_eq!(&model_values, expected);
            } else {
                expected = Some(model_values);
            }
        }
    }

    #[test]
    fn kill_switch_disables_the_device() {
        let a = vec![vec![1, 1, 1, 1], vec![0, 1, 2, 3]];
        let b = vec![2, 6];
        let m = market_split(&a, &b);
        let out = try_prove_configured(&m, deadline(), LatticeSchedule::Disabled);
        assert!(out.is_none(), "kill switch must disable the device");
    }

    #[test]
    fn does_not_fire_on_maximize() {
        let mut m = market_split(&[vec![1, 1, 1, 1], vec![0, 1, 2, 3]], &[2, 6]);
        // flip to Maximize: out of the family.
        let s0 = m.col_at(4).unwrap();
        let s1 = m.col_at(5).unwrap();
        m.set_objective(&[(s0, 1.0), (s1, 1.0)], Sense::Maximize);
        assert!(detect(&m).is_none());
    }

    #[test]
    fn does_not_fire_on_inequality_rows() {
        // A pure covering model (≤ rows, no equality slack structure).
        let mut m = Model::new();
        let x: Vec<Col> = (0..4).map(|_| m.add_binary_col()).collect();
        m.add_row(f64::NEG_INFINITY, 2.0, &[(x[0], 1.0), (x[1], 1.0)]);
        m.add_row(f64::NEG_INFINITY, 2.0, &[(x[2], 1.0), (x[3], 1.0)]);
        m.set_objective(&[(x[0], 1.0)], Sense::Minimize);
        assert!(detect(&m).is_none());
    }

    #[test]
    fn recovers_original_system_under_row_scaling() {
        // The reader halves rows whose largest entry exceeds 1024. Emulate it by
        // hand: a row scaled by ½ must still be detected and solved correctly.
        let a = vec![vec![1, 1, 1, 1], vec![0, 1, 2, 3]];
        let b = vec![2, 6];
        let mut m = Model::new();
        let x: Vec<Col> = (0..4).map(|_| m.add_binary_col()).collect();
        let s: Vec<Col> = (0..2).map(|_| m.add_col(0.0, f64::INFINITY)).collect();
        for (i, row) in a.iter().enumerate() {
            // scale the whole row (coeffs + rhs + slack) by ½.
            let mut terms: Vec<(Col, f64)> = row
                .iter()
                .enumerate()
                .filter(|&(_, &c)| c != 0)
                .map(|(j, &c)| (x[j], c as f64 * 0.5))
                .collect();
            terms.push((s[i], 0.5));
            m.add_row(b[i] as f64 * 0.5, b[i] as f64 * 0.5, &terms);
        }
        m.set_objective(&[(s[0], 1.0), (s[1], 1.0)], Sense::Minimize);
        let ms = detect(&m).expect("detect under ½ scaling");
        assert_eq!(ms.a, a);
        assert_eq!(ms.b, b);
    }

    /// The lower-bound proof needs an EXACT integer normalized system.  A
    /// near-integer coefficient is not licensed by a tolerance: Σs would no
    /// longer be integer, so "zero face empty => optimum >= 1" would be false.
    #[test]
    fn declines_near_integer_normalization() {
        let mut m = Model::new();
        let x0 = m.add_binary_col();
        let x1 = m.add_binary_col();
        let s = m.add_col(0.0, f64::INFINITY);
        let near_two = 2.0 + f64::EPSILON * 2.0;
        m.add_row(3.0, 3.0, &[(x0, near_two), (x1, 2.0), (s, 1.0)]);
        m.set_objective(&[(s, 1.0)], Sense::Minimize);
        assert!(detect(&m).is_none());
    }

    /// Side-store models must be classified from their true rationals, not the
    /// rounded advice matrix.  Until the lattice compiler consumes those exact
    /// accessors directly it declines the device.
    #[test]
    fn declines_exact_side_store_models() {
        let mut m = market_split(&[vec![2, 2, 5]], &[3]);
        let row = m.row_at(0).expect("row");
        let x0 = m.col_at(0).expect("column");
        m.record_inexact_row_coeff(row, x0.0, BigRational::from_integer(3.into()));
        assert!(detect(&m).is_none());
    }

    /// Differential completeness check for both outward-interval schedules.
    /// Serial and parallel must make the same decision, and every optimum they
    /// report must match exhaustive 0/1 enumeration.
    #[test]
    fn small_random_lattice_results_match_exhaustive_optimum() {
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        let mut rnd = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for _case in 0..160 {
            let n = 4 + (rnd() % 4) as usize;
            let rows = 1 + (rnd() % 3) as usize;
            let mut a = vec![vec![0i64; n]; rows];
            let mut b = vec![0i64; rows];
            for i in 0..rows {
                for j in 0..n {
                    a[i][j] = (rnd() % 6) as i64;
                }
                // Keep at least two nonzeros so the detector's premise holds.
                a[i][0] = a[i][0].max(1);
                a[i][1] = a[i][1].max(1);
                b[i] = (rnd() % (a[i].iter().sum::<i64>() as u64 + 1)) as i64;
            }
            let model = market_split(&a, &b);
            let mut best: Option<i64> = None;
            for mask in 0..(1usize << n) {
                let mut total = 0i64;
                let mut feasible = true;
                for i in 0..rows {
                    let ax: i64 = (0..n)
                        .filter(|&j| mask & (1usize << j) != 0)
                        .map(|j| a[i][j])
                        .sum();
                    if ax > b[i] {
                        feasible = false;
                        break;
                    }
                    total += b[i] - ax;
                }
                if feasible {
                    best = Some(best.map_or(total, |old| old.min(total)));
                }
            }
            let serial = try_prove_configured(&model, deadline(), LatticeSchedule::Threads(1));
            let parallel = try_prove_configured(&model, deadline(), LatticeSchedule::Threads(4));
            match (serial, parallel) {
                (
                    Some(Outcome::Optimal {
                        value: serial_value,
                        model_values: serial_point,
                        ..
                    }),
                    Some(Outcome::Optimal {
                        value: parallel_value,
                        model_values: parallel_point,
                        ..
                    }),
                ) => {
                    let expected =
                        BigRational::from_integer(BigInt::from(best.expect("lattice witness")));
                    assert_eq!(
                        serial_value, expected,
                        "serial mismatch for A={a:?}, b={b:?}"
                    );
                    assert_eq!(
                        parallel_value, expected,
                        "parallel mismatch for A={a:?}, b={b:?}"
                    );
                    assert!(model.check_point(&serial_point).is_ok());
                    assert!(model.check_point(&parallel_point).is_ok());
                }
                (None, None) => {}
                other => panic!(
                    "serial/parallel lattice decision mismatch for A={a:?}, b={b:?}: {other:?}"
                ),
            }
        }
    }

    /// Differential soundness check for the PRUNED BKZ oracle through the FULL
    /// device: force β past the exact-oracle ceiling (the same lever
    /// `AY_MILP_LATTICE_BKZ` exposes, minus the env mutation) so every kernel
    /// here takes the pruned full-dimension path — profile bounds, tight node
    /// cap, and log-potential snapshot selection all engage — and every
    /// verdict must STILL match exhaustive 0/1 enumeration exactly.
    /// Pruning is advisory by construction (a worse basis, never a wrong one);
    /// this pins that construction end-to-end, serial and parallel.
    #[test]
    fn pruned_bkz_device_results_match_exhaustive_optimum() {
        let mut state = 0x5851_f42d_4c95_7f2du64;
        let mut rnd = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let forced = BKZ_ADAPTIVE_BETA + 6; // > 34 ⟹ pruned oracle, any dim
        for _case in 0..160 {
            let n = 4 + (rnd() % 4) as usize;
            let rows = 1 + (rnd() % 3) as usize;
            let mut a = vec![vec![0i64; n]; rows];
            let mut b = vec![0i64; rows];
            for i in 0..rows {
                for j in 0..n {
                    a[i][j] = (rnd() % 6) as i64;
                }
                a[i][0] = a[i][0].max(1);
                a[i][1] = a[i][1].max(1);
                b[i] = (rnd() % (a[i].iter().sum::<i64>() as u64 + 1)) as i64;
            }
            let model = market_split(&a, &b);
            let mut best: Option<i64> = None;
            for mask in 0..(1usize << n) {
                let mut total = 0i64;
                let mut feasible = true;
                for i in 0..rows {
                    let ax: i64 = (0..n)
                        .filter(|&j| mask & (1usize << j) != 0)
                        .map(|j| a[i][j])
                        .sum();
                    if ax > b[i] {
                        feasible = false;
                        break;
                    }
                    total += b[i] - ax;
                }
                if feasible {
                    best = Some(best.map_or(total, |old| old.min(total)));
                }
            }
            let serial = try_prove_configured(
                &model,
                deadline(),
                LatticeSchedule::ThreadsForcedBeta(1, forced),
            );
            let parallel = try_prove_configured(
                &model,
                deadline(),
                LatticeSchedule::ThreadsForcedBeta(4, forced),
            );
            match (serial, parallel) {
                (
                    Some(Outcome::Optimal {
                        value: serial_value,
                        model_values: serial_point,
                        ..
                    }),
                    Some(Outcome::Optimal {
                        value: parallel_value,
                        model_values: parallel_point,
                        ..
                    }),
                ) => {
                    let expected =
                        BigRational::from_integer(BigInt::from(best.expect("lattice witness")));
                    assert_eq!(
                        serial_value, expected,
                        "pruned serial mismatch for A={a:?}, b={b:?}"
                    );
                    assert_eq!(
                        parallel_value, expected,
                        "pruned parallel mismatch for A={a:?}, b={b:?}"
                    );
                    assert!(model.check_point(&serial_point).is_ok());
                    assert!(model.check_point(&parallel_point).is_ok());
                }
                (None, None) => {}
                other => panic!(
                    "pruned serial/parallel lattice decision mismatch for A={a:?}, b={b:?}: {other:?}"
                ),
            }
        }
    }

    /// The concurrent multi-face witness hunt and the historical sequential
    /// ladder must agree: a later-face witness (the objective-0 face and
    /// `b−e_0` are both empty here; only `b−e_1` carries a 0/1 point) is
    /// found by both paths and both produce a `check_point`-verified
    /// Optimal 1.
    #[test]
    fn concurrent_face_hunt_matches_sequential_ladder() {
        let a = vec![vec![1, 1, 1, 1], vec![0, 1, 2, 3]];
        let b = vec![2, 6];
        let m = market_split(&a, &b);
        let ms = detect(&m).expect("market-split shape");
        for threads in [1usize, 8] {
            let eng = Engine::build(&ms, deadline(), false, threads, None).expect("engine");
            match eng.prove(&m, &ms) {
                Some(Outcome::Optimal {
                    value,
                    model_values,
                    ..
                }) => {
                    assert_eq!(
                        value,
                        BigRational::from(BigInt::from(1)),
                        "threads={threads}"
                    );
                    assert!(m.check_point(&model_values).is_ok(), "threads={threads}");
                }
                other => panic!("expected Optimal 1 with {threads} threads, got {other:?}"),
            }
        }
    }

    /// An optimum-2 ladder (objective-0 face AND every `b−e_k` face empty)
    /// must make BOTH hunt paths decline the device — the concurrent path's
    /// `AllEmpty` requires every item of every face completely swept, the
    /// same invariant as the sequential ladder.
    #[test]
    fn optimum_two_ladder_declines_on_both_paths() {
        // Row0: Σx = 2; Row1: 0·x0+1·x1+2·x2+3·x3 = 7. No pair reaches 7
        // (obj-0 empty), no single reaches 7 (e_0 empty), no pair reaches 6
        // (e_1 empty; max pair is 5) ⟹ optimum = 2: out of the device's scope.
        let a = vec![vec![1, 1, 1, 1], vec![0, 1, 2, 3]];
        let b = vec![2, 7];
        let m = market_split(&a, &b);
        let ms = detect(&m).expect("market-split shape");
        for threads in [1usize, 8] {
            let eng = Engine::build(&ms, deadline(), false, threads, None).expect("engine");
            assert!(
                eng.prove(&m, &ms).is_none(),
                "opt≥2 must decline the device (threads={threads})"
            );
        }
    }

    /// The widening must be STRICTLY ADDITIVE: the historical markshare shape
    /// compiles to the byte-identical extended system (same `a`, `b`, all-0/1
    /// box, every row an objective row, no synthetic columns).
    #[test]
    fn widened_gate_compiles_markshare_shape_identically() {
        let a = vec![vec![1, 1, 1, 1], vec![0, 1, 2, 3]];
        let b = vec![2, 6];
        let ms = detect(&market_split(&a, &b)).expect("markshare shape");
        assert_eq!(ms.n, 4);
        assert_eq!(ms.m, 2);
        assert_eq!(ms.a, a);
        assert_eq!(ms.b, b);
        assert_eq!(ms.lo, vec![0; 4]);
        assert_eq!(ms.up, vec![1; 4]);
        assert_eq!(ms.obj_rows, vec![0, 1]);
        assert_eq!(ms.slack_col, vec![4, 5]);
        assert_eq!(ms.col_model, vec![Some(0), Some(1), Some(2), Some(3)]);
        assert!(ms.singleton_cols.is_empty());
    }

    /// Enumerate every point of the integer box (mixed-radix counter).
    fn for_each_box_point(lo: &[i64], up: &[i64], mut f: impl FnMut(&[i64])) {
        let n = lo.len();
        let mut x: Vec<i64> = lo.to_vec();
        loop {
            f(&x);
            let mut p = 0;
            loop {
                if p == n {
                    return;
                }
                if x[p] < up[p] {
                    x[p] += 1;
                    break;
                }
                x[p] = lo[p];
                p += 1;
            }
        }
    }

    /// Differential completeness for widening (2): GENERAL bounded-integer
    /// columns. Random small min-total-slack systems over `x_j ∈ [l_j, u_j]`
    /// (negative bounds and coefficients included) are compared against
    /// exhaustive product-of-ranges enumeration whenever the device speaks —
    /// on BOTH the serial and the parallel schedule.
    #[test]
    fn widened_general_integer_results_match_exhaustive_optimum() {
        let mut state = 0xdead_beef_1234_5678u64;
        let mut rnd = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for _case in 0..120 {
            let n = 3 + (rnd() % 3) as usize;
            let rows = 1 + (rnd() % 2) as usize;
            let lo: Vec<i64> = (0..n).map(|_| (rnd() % 4) as i64 - 2).collect();
            let up: Vec<i64> = lo.iter().map(|&l| l + 1 + (rnd() % 3) as i64).collect();
            let mut a = vec![vec![0i64; n]; rows];
            let mut b = vec![0i64; rows];
            for i in 0..rows {
                for j in 0..n {
                    a[i][j] = (rnd() % 7) as i64 - 3;
                }
                // ≥2 nonzeros so the objective-row premise holds.
                if a[i][0] == 0 {
                    a[i][0] = 1;
                }
                if a[i][1] == 0 {
                    a[i][1] = -1;
                }
                let (mut mn, mut mx) = (0i64, 0i64);
                for j in 0..n {
                    mn += (a[i][j] * lo[j]).min(a[i][j] * up[j]);
                    mx += (a[i][j] * lo[j]).max(a[i][j] * up[j]);
                }
                b[i] = mn + (rnd() % (mx - mn + 1) as u64) as i64;
            }
            let mut m = Model::new();
            let x: Vec<Col> = (0..n)
                .map(|j| m.add_int_col(lo[j] as f64, up[j] as f64))
                .collect();
            let s: Vec<Col> = (0..rows).map(|_| m.add_col(0.0, f64::INFINITY)).collect();
            for i in 0..rows {
                let mut terms: Vec<(Col, f64)> = (0..n)
                    .filter(|&j| a[i][j] != 0)
                    .map(|j| (x[j], a[i][j] as f64))
                    .collect();
                terms.push((s[i], 1.0));
                m.add_row(b[i] as f64, b[i] as f64, &terms);
            }
            let obj: Vec<(Col, f64)> = s.iter().map(|&c| (c, 1.0)).collect();
            m.set_objective(&obj, Sense::Minimize);
            let mut best: Option<i64> = None;
            for_each_box_point(&lo, &up, |pt| {
                let mut total = 0i64;
                let mut feasible = true;
                for i in 0..rows {
                    let ax: i64 = (0..n).map(|j| a[i][j] * pt[j]).sum();
                    if ax > b[i] {
                        feasible = false;
                        break;
                    }
                    total += b[i] - ax;
                }
                if feasible {
                    best = Some(best.map_or(total, |old| old.min(total)));
                }
            });
            for schedule in [LatticeSchedule::Threads(1), LatticeSchedule::Threads(4)] {
                if let Some(Outcome::Optimal {
                    value,
                    model_values,
                    ..
                }) = try_prove_configured(&m, deadline(), schedule)
                {
                    assert!(m.check_point(&model_values).is_ok());
                    assert_eq!(
                        value,
                        BigRational::from_integer(BigInt::from(best.expect("lattice witness"))),
                        "mismatch ({schedule:?}) for A={a:?}, b={b:?}, lo={lo:?}, up={up:?}"
                    );
                }
            }
        }
    }

    /// Differential completeness for widening (1): pure-integer INEQUALITY /
    /// RANGE rows compiled through synthetic bounded slacks, mixed with
    /// objective rows. Whenever the device speaks, its optimum must match
    /// exhaustive enumeration restricted to the inequality-feasible points.
    #[test]
    fn widened_inequality_rows_match_exhaustive_optimum() {
        let mut state = 0x0123_4567_89ab_cdefu64;
        let mut rnd = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for _case in 0..120 {
            let n = 4 + (rnd() % 2) as usize; // binaries
            let lo = vec![0i64; n];
            let up = vec![1i64; n];
            // One objective row (equality + unit slack), one pure-integer row.
            let mut arow = vec![0i64; n];
            let mut crow = vec![0i64; n];
            for j in 0..n {
                arow[j] = (rnd() % 5) as i64;
                crow[j] = (rnd() % 5) as i64 - 2;
            }
            arow[0] = arow[0].max(1);
            arow[1] = arow[1].max(1);
            if crow[0] == 0 {
                crow[0] = 2;
            }
            let asum: i64 = arow.iter().sum();
            let bo = (rnd() % (asum as u64 + 1)) as i64;
            let (mut cmn, mut cmx) = (0i64, 0i64);
            for j in 0..n {
                cmn += crow[j].min(0);
                cmx += crow[j].max(0);
            }
            // Random row form: ≤ / ≥ / range.
            let cb = cmn + (rnd() % (cmx - cmn + 1) as u64) as i64;
            let form = rnd() % 3;
            let (clo, cup) = match form {
                0 => (f64::NEG_INFINITY, cb as f64),
                1 => (cb as f64, f64::INFINITY),
                _ => ((cb - 1) as f64, (cb + 1) as f64),
            };
            let mut m = Model::new();
            let x: Vec<Col> = (0..n).map(|_| m.add_binary_col()).collect();
            let s = m.add_col(0.0, f64::INFINITY);
            let mut terms: Vec<(Col, f64)> = (0..n)
                .filter(|&j| arow[j] != 0)
                .map(|j| (x[j], arow[j] as f64))
                .collect();
            terms.push((s, 1.0));
            m.add_row(bo as f64, bo as f64, &terms);
            let cterms: Vec<(Col, f64)> = (0..n)
                .filter(|&j| crow[j] != 0)
                .map(|j| (x[j], crow[j] as f64))
                .collect();
            m.add_row(clo, cup, &cterms);
            m.set_objective(&[(s, 1.0)], Sense::Minimize);
            let mut best: Option<i64> = None;
            for_each_box_point(&lo, &up, |pt| {
                let cx: i64 = (0..n).map(|j| crow[j] * pt[j]).sum();
                if (cx as f64) < clo || (cx as f64) > cup {
                    return;
                }
                let ax: i64 = (0..n).map(|j| arow[j] * pt[j]).sum();
                if ax > bo {
                    return;
                }
                let total = bo - ax;
                best = Some(best.map_or(total, |old| old.min(total)));
            });
            for schedule in [LatticeSchedule::Threads(1), LatticeSchedule::Threads(4)] {
                if let Some(Outcome::Optimal {
                    value,
                    model_values,
                    ..
                }) = try_prove_configured(&m, deadline(), schedule)
                {
                    assert!(m.check_point(&model_values).is_ok());
                    assert_eq!(
                        value,
                        BigRational::from_integer(BigInt::from(best.expect("lattice witness"))),
                        "mismatch ({schedule:?}) for a={arow:?}, b={bo}, c={crow:?} in [{clo},{cup}]"
                    );
                }
            }
        }
    }

    /// Differential completeness for FEASIBILITY MODE (constant objective, no
    /// slack rows): the device's Optimal/Infeasible verdicts must match
    /// exhaustive enumeration exactly — in BOTH directions, on BOTH schedules.
    #[test]
    fn widened_feasibility_mode_matches_exhaustive() {
        let mut state = 0xfeed_face_cafe_beefu64;
        let mut rnd = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for _case in 0..160 {
            let n = 3 + (rnd() % 3) as usize;
            let rows = 1 + (rnd() % 3) as usize;
            let lo: Vec<i64> = (0..n).map(|_| (rnd() % 2) as i64 - 1).collect();
            let up: Vec<i64> = lo.iter().map(|&l| l + 1 + (rnd() % 2) as i64).collect();
            let mut a = vec![vec![0i64; n]; rows];
            let mut blo = vec![0f64; rows];
            let mut bup = vec![0f64; rows];
            for i in 0..rows {
                for j in 0..n {
                    a[i][j] = (rnd() % 9) as i64 - 4;
                }
                if a[i][0] == 0 {
                    a[i][0] = 3;
                }
                let (mut mn, mut mx) = (0i64, 0i64);
                for j in 0..n {
                    mn += (a[i][j] * lo[j]).min(a[i][j] * up[j]);
                    mx += (a[i][j] * lo[j]).max(a[i][j] * up[j]);
                }
                // Aim near the middle so both feasible and infeasible cases occur.
                let t = mn + (rnd() % (mx - mn + 1) as u64) as i64;
                match rnd() % 3 {
                    0 => {
                        blo[i] = t as f64;
                        bup[i] = t as f64;
                    }
                    1 => {
                        blo[i] = f64::NEG_INFINITY;
                        bup[i] = t as f64;
                    }
                    _ => {
                        blo[i] = t as f64;
                        bup[i] = (t + (rnd() % 2) as i64) as f64;
                    }
                }
            }
            let mut m = Model::new();
            let x: Vec<Col> = (0..n)
                .map(|j| m.add_int_col(lo[j] as f64, up[j] as f64))
                .collect();
            for i in 0..rows {
                let terms: Vec<(Col, f64)> = (0..n)
                    .filter(|&j| a[i][j] != 0)
                    .map(|j| (x[j], a[i][j] as f64))
                    .collect();
                m.add_row(blo[i], bup[i], &terms);
            }
            m.set_objective(&[], Sense::Minimize);
            let mut feasible = false;
            for_each_box_point(&lo, &up, |pt| {
                if feasible {
                    return;
                }
                feasible = (0..rows).all(|i| {
                    let ax: i64 = (0..n).map(|j| a[i][j] * pt[j]).sum();
                    (ax as f64) >= blo[i] && (ax as f64) <= bup[i]
                });
            });
            for schedule in [LatticeSchedule::Threads(1), LatticeSchedule::Threads(4)] {
                match try_prove_configured(&m, deadline(), schedule) {
                    Some(Outcome::Optimal { model_values, .. }) => {
                        assert!(
                            feasible,
                            "device ({schedule:?}) claimed feasible for A={a:?} in [{blo:?},{bup:?}]"
                        );
                        assert!(m.check_point(&model_values).is_ok());
                    }
                    Some(Outcome::Infeasible { .. }) => {
                        assert!(
                            !feasible,
                            "device ({schedule:?}) claimed INFEASIBLE for A={a:?} in [{blo:?},{bup:?}], lo={lo:?}, up={up:?}"
                        );
                    }
                    Some(other) => panic!("unexpected outcome {other:?}"),
                    None => {}
                }
            }
        }
    }

    /// Deterministic feasibility-mode INFEASIBLE via the coset branch: an
    /// equality whose integer particular solution does not exist (2x ≡ 3).
    #[test]
    fn feasibility_mode_proves_parity_infeasible() {
        let mut m = Model::new();
        let x: Vec<Col> = (0..3).map(|_| m.add_binary_col()).collect();
        m.add_row(3.0, 3.0, &[(x[0], 2.0), (x[1], 2.0), (x[2], 2.0)]);
        m.set_objective(&[], Sense::Minimize);
        assert!(matches!(
            try_prove_configured(&m, deadline(), LatticeSchedule::Threads(1)),
            Some(Outcome::Infeasible { .. })
        ));
    }

    /// Deterministic feasibility-mode INFEASIBLE via a COMPLETE empty sweep:
    /// the coset has integer points, none inside the 0/1 box.
    #[test]
    fn feasibility_mode_proves_subset_sum_gap_infeasible() {
        let mut m = Model::new();
        let x: Vec<Col> = (0..3).map(|_| m.add_binary_col()).collect();
        // 2,2,3 subset sums: {0,2,3,4,5,7} — 6 is a gap.
        m.add_row(6.0, 6.0, &[(x[0], 2.0), (x[1], 2.0), (x[2], 3.0)]);
        m.set_objective(&[], Sense::Minimize);
        assert!(matches!(
            try_prove_configured(&m, deadline(), LatticeSchedule::Threads(1)),
            Some(Outcome::Infeasible { .. })
        ));
        // The kill switch must silence feasibility mode too.
        assert!(try_prove_configured(&m, deadline(), LatticeSchedule::Disabled).is_none());
    }

    /// Integral columns whose bounds tighten to a single value must be restated
    /// in the witness point (they are lattice-fixed, not model-fixed).
    #[test]
    fn singleton_integral_columns_are_restated_in_the_witness() {
        let mut m = Model::new();
        let x0 = m.add_binary_col();
        let x1 = m.add_binary_col();
        let z = m.add_int_col(0.5, 1.5); // forced to 1
        m.add_row(2.0, 2.0, &[(x0, 1.0), (x1, 1.0), (z, 1.0)]);
        m.set_objective(&[], Sense::Minimize);
        match try_prove_configured(&m, deadline(), LatticeSchedule::Threads(1)) {
            Some(Outcome::Optimal { model_values, .. }) => {
                assert_eq!(model_values[z.0 as usize], BigRational::from(BigInt::one()));
                assert!(m.check_point(&model_values).is_ok());
            }
            other => panic!("expected Optimal, got {other:?}"),
        }
    }

    /// ADVERSARIAL verification fuzz (added by the gate-widening verifier):
    /// feasibility mode under the shapes the shipped differentials do NOT
    /// exercise — dyadic fractional coefficients (LCM clearing), fixed
    /// continuous columns with fractional values, singleton integral columns
    /// (fractional bounds tightening to a point), `>=`-only rows, and
    /// fractional row bounds (ceil/floor integer-hull tightening). Every
    /// INFEASIBLE claim is checked against exhaustive enumeration (measured
    /// non-vacuous: the device speaks Optimal 218 / Infeasible 161 of 400).
    #[test]
    fn adversarial_feasibility_fuzz_fixed_singleton_fractional() {
        let mut state = 0x5eed_5eed_5eed_5eedu64;
        let mut rnd = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let mut spoke_inf = 0usize;
        let mut spoke_opt = 0usize;
        for _case in 0..400 {
            let n = 3 + (rnd() % 3) as usize; // free int cols
            let rows = 1 + (rnd() % 3) as usize;
            let lo: Vec<i64> = (0..n).map(|_| (rnd() % 3) as i64 - 1).collect();
            let up: Vec<i64> = lo.iter().map(|&l| l + 1 + (rnd() % 3) as i64).collect();
            // coefficients in quarters: a[i][j]/4
            let mut a4 = vec![vec![0i64; n]; rows];
            let mut blo = vec![0f64; rows];
            let mut bup = vec![0f64; rows];
            // one fixed continuous column with fractional value, netted into rows
            let fixv4 = (rnd() % 9) as i64 - 4; // fixed value = fixv4/4
            let mut fcoef4 = vec![0i64; rows]; // its per-row coefficient /4
            for i in 0..rows {
                for j in 0..n {
                    a4[i][j] = (rnd() % 17) as i64 - 8;
                }
                if a4[i][0] == 0 {
                    a4[i][0] = 4;
                }
                if a4[i][1] == 0 {
                    a4[i][1] = -3;
                }
                fcoef4[i] = (rnd() % 5) as i64 - 2;
                let (mut mn, mut mx) = (0i64, 0i64);
                for j in 0..n {
                    mn += (a4[i][j] * lo[j]).min(a4[i][j] * up[j]);
                    mx += (a4[i][j] * lo[j]).max(a4[i][j] * up[j]);
                }
                // row activity in 1/16 units: a4/4 · x + (fcoef4/4)(fixv4/4)
                let t = mn + (rnd() % (mx - mn + 1) as u64) as i64; // /4 units over int cols
                let base16 = fcoef4[i] * fixv4; // /16 units
                let t16 = t * 4 + base16; // total activity target in /16 units
                                          // fractional bound jitter: 0..7 sixteenths
                let j1 = (rnd() % 8) as i64;
                let j2 = (rnd() % 8) as i64;
                match rnd() % 4 {
                    0 => {
                        blo[i] = t16 as f64 / 16.0;
                        bup[i] = blo[i];
                    }
                    1 => {
                        blo[i] = f64::NEG_INFINITY;
                        bup[i] = (t16 + j1) as f64 / 16.0;
                    }
                    2 => {
                        blo[i] = (t16 - j2) as f64 / 16.0;
                        bup[i] = f64::INFINITY;
                    }
                    _ => {
                        blo[i] = (t16 - j2) as f64 / 16.0;
                        bup[i] = (t16 + j1) as f64 / 16.0;
                    }
                }
            }
            let mut m = Model::new();
            let x: Vec<Col> = (0..n)
                .map(|j| m.add_int_col(lo[j] as f64, up[j] as f64))
                .collect();
            let f = m.add_col(fixv4 as f64 / 4.0, fixv4 as f64 / 4.0); // fixed cont col
                                                                       // singleton integral column: bounds (v-0.25, v+0.25) force value v
            let sv = (rnd() % 3) as i64 - 1;
            let z = m.add_int_col(sv as f64 - 0.25, sv as f64 + 0.25);
            let zcoef4 = (rnd() % 5) as i64 - 2; // /4 coefficient on z
            for i in 0..rows {
                let mut terms: Vec<(Col, f64)> = (0..n)
                    .filter(|&j| a4[i][j] != 0)
                    .map(|j| (x[j], a4[i][j] as f64 / 4.0))
                    .collect();
                if fcoef4[i] != 0 {
                    terms.push((f, fcoef4[i] as f64 / 4.0));
                }
                if zcoef4 != 0 && i == 0 {
                    terms.push((z, zcoef4 as f64 / 4.0));
                }
                m.add_row(blo[i], bup[i], &terms);
            }
            m.set_objective(&[], Sense::Minimize);
            // Exhaustive truth over the integer box (z forced to sv).
            let mut feasible = false;
            for_each_box_point(&lo, &up, |pt| {
                if feasible {
                    return;
                }
                feasible = (0..rows).all(|i| {
                    // activity in exact /16 units
                    let mut act16: i64 = (0..n).map(|j| a4[i][j] * pt[j] * 4).sum();
                    act16 += fcoef4[i] * fixv4;
                    if i == 0 {
                        act16 += zcoef4 * sv * 4;
                    }
                    let act = act16 as f64 / 16.0;
                    act >= blo[i] && act <= bup[i]
                });
            });
            match try_prove_configured(&m, deadline(), LatticeSchedule::Threads(1)) {
                Some(Outcome::Optimal { model_values, .. }) => {
                    spoke_opt += 1;
                    assert!(
                        feasible,
                        "device claimed feasible for a4={a4:?} f={fixv4}/4 z={sv} in [{blo:?},{bup:?}]"
                    );
                    assert!(m.check_point(&model_values).is_ok());
                }
                Some(Outcome::Infeasible { .. }) => {
                    spoke_inf += 1;
                    assert!(
                        !feasible,
                        "device claimed INFEASIBLE for a4={a4:?} fc4={fcoef4:?} f={fixv4}/4 zc4={zcoef4} z={sv} in [{blo:?},{bup:?}], lo={lo:?}, up={up:?}"
                    );
                }
                Some(other) => panic!("unexpected outcome {other:?}"),
                None => {}
            }
        }
        assert!(
            spoke_inf > 10,
            "vacuous fuzz: only {spoke_inf} INFEASIBLE claims"
        );
        assert!(
            spoke_opt > 10,
            "vacuous fuzz: only {spoke_opt} Optimal claims"
        );
    }

    // -----------------------------------------------------------------------
    // BOX-PREFIX PRUNE — differential + brute-force soundness
    // -----------------------------------------------------------------------

    /// Deterministic 64-bit PRNG (SplitMix64) so the fuzz corpus is fixed.
    fn split_mix(state: &mut u64) -> u64 {
        *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = *state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A random 0/1 market-split shape: `m` dense rows over `n` binaries.
    fn random_market_split(rng: &mut u64, n: usize, m: usize, coef_max: i64) -> MarketSplit {
        let a: Vec<Vec<i64>> = (0..m)
            .map(|_| {
                (0..n)
                    .map(|_| (split_mix(rng) % (coef_max as u64) + 1) as i64)
                    .collect()
            })
            .collect();
        MarketSplit {
            n,
            m,
            b: vec![0; m],
            a,
            lo: vec![0; n],
            up: vec![1; n],
            col_model: (0..n).map(Some).collect(),
            obj_rows: (0..m).collect(),
            slack_col: (0..m).map(|i| n + i).collect(),
            singleton_cols: vec![],
        }
    }

    /// Ground truth: every `x ∈ {0,1}^n` with `A·x = d` (exhaustive, `n ≤ 20`).
    fn brute_force_face(ms: &MarketSplit, d: &[i64]) -> Vec<Vec<i64>> {
        let n = ms.n;
        assert!(n <= 20, "brute force is exponential");
        let mut hits = Vec::new();
        for mask in 0u32..(1u32 << n) {
            let x: Vec<i64> = (0..n).map(|j| ((mask >> j) & 1) as i64).collect();
            if ms
                .a
                .iter()
                .zip(d)
                .all(|(row, &rhs)| row.iter().zip(&x).map(|(&c, &v)| c * v).sum::<i64>() == rhs)
            {
                hits.push(x);
            }
        }
        hits
    }

    /// Map an enumerated kernel vector back to the original coordinates.
    fn lattice_point(eng: &Engine, xd: &[i64], y: &[i64]) -> Vec<i64> {
        (0..eng.n)
            .map(|k| {
                let mut v = xd[k];
                for t in 0..eng.dim {
                    v += y[t] * eng.k[t][k];
                }
                v
            })
            .collect()
    }

    fn clone_box_prune(bp: &BoxPrune) -> BoxPrune {
        BoxPrune {
            bstar_i: bp.bstar_i.clone(),
            bstar_mid: bp.bstar_mid.clone(),
            bstar_absmax: bp.bstar_absmax.clone(),
            bstar_halfw: bp.bstar_halfw.clone(),
            sqrt_s: bp.sqrt_s.clone(),
            sqrt_s_max: bp.sqrt_s_max.clone(),
            lo_f: bp.lo_f.clone(),
            up_f: bp.up_f.clone(),
            bound_absmax: bp.bound_absmax,
            eps_coeff: bp.eps_coeff,
        }
    }

    /// THE UNSOUND-PRUNE CATCHER.
    ///
    /// For a corpus of random small market splits and several right-hand sides
    /// each, run the SAME serial enumeration twice — once with the box-prefix
    /// prune ON, once with it OFF — and require:
    ///   * identical verdicts (an unsound prune turns `Feasible` into `Empty`,
    ///     i.e. "no solution found" into a WRONG "proven optimal");
    ///   * identical witnesses (the prune must not reorder or lose the first
    ///     box-feasible leaf, since it may only cut box-INfeasible subtrees);
    ///   * agreement with an exhaustive `{0,1}^n` brute force, so a prune that
    ///     drops the only solution is caught even if BOTH paths were wrong.
    /// Both `Empty` and `Feasible` outcomes are required to occur, and the
    /// prune is required to actually fire, so the test cannot pass vacuously.
    #[test]
    fn box_prefix_prune_matches_unpruned_sweep_and_brute_force() {
        let mut rng = 0x5EED_1234_ABCD_0001u64;
        let mut saw_empty = 0usize;
        let mut saw_feasible = 0usize;
        let mut saw_prune_active = 0usize;
        for case in 0..24usize {
            let n = 10 + (case % 5);
            let m = 2 + (case % 2);
            let ms = random_market_split(&mut rng, n, m, 24);
            let Some(mut eng) = Engine::build(&ms, deadline(), false, 1, None) else {
                continue;
            };
            let tables =
                box_prune_tables(&eng.bstar_q, &eng.cnorm_i, &eng.lo, &eng.up, eng.dim, eng.n)
                    .expect("0/1 box tables always build");

            // Targets: the balanced rhs (½·Σ a — the hard face) and its
            // neighbours, which mixes provably-EMPTY faces with witnesses.
            let half: Vec<i64> = ms.a.iter().map(|row| row.iter().sum::<i64>() / 2).collect();
            for shift in -2i64..=2 {
                let d: Vec<i64> = half.iter().map(|&v| v + shift).collect();
                let Some(xd) = eng.particular(&ms, &d) else {
                    // No integer solution of A·x = d at all: nothing to compare.
                    assert!(
                        brute_force_face(&ms, &d).is_empty(),
                        "particular() declined a face that has a 0/1 point"
                    );
                    continue;
                };
                let Some(xd) = eng.babai(&xd) else { continue };

                eng.box_prune = Some(clone_box_prune(&tables));
                let pruned = eng.enumerate_serial(&xd);
                eng.box_prune = None;
                let plain = eng.enumerate_serial(&xd);

                assert_eq!(
                    pruned, plain,
                    "box prune changed the verdict/witness on case {case} shift {shift}"
                );

                let truth = brute_force_face(&ms, &d);
                match &pruned {
                    EnumResult::Empty => {
                        saw_empty += 1;
                        assert!(
                            truth.is_empty(),
                            "UNSOUND: face proven EMPTY but brute force found {} 0/1 point(s) \\
                             (case {case}, shift {shift}, a={:?}, d={d:?})",
                            truth.len(),
                            ms.a
                        );
                    }
                    EnumResult::Feasible(y) => {
                        saw_feasible += 1;
                        let x = lattice_point(&eng, &xd, y);
                        assert!(
                            truth.contains(&x),
                            "witness {x:?} is not a 0/1 point of the face (case {case})"
                        );
                    }
                    EnumResult::Capped | EnumResult::Aborted => {}
                }
            }
            // Confirm the prune is not silently inert on this corpus: with the
            // tables installed the sweep must visit strictly fewer nodes on at
            // least one face.
            if let Some(xd) = eng.particular(&ms, &half).and_then(|v| eng.babai(&v)) {
                eng.box_prune = Some(clone_box_prune(&tables));
                let (_, with) = eng.enumerate_serial_with_cap(&xd, NODE_BUDGET);
                eng.box_prune = None;
                let (_, without) = eng.enumerate_serial_with_cap(&xd, NODE_BUDGET);
                assert!(with <= without, "the prune may only REMOVE nodes");
                if with < without {
                    saw_prune_active += 1;
                }
            }
        }
        assert!(saw_empty > 0, "vacuous: no EMPTY face in the corpus");
        assert!(saw_feasible > 0, "vacuous: no FEASIBLE face in the corpus");
        assert!(
            saw_prune_active > 0,
            "vacuous: the prune never removed a single node"
        );
    }

    /// The kill switch must produce a BYTE-IDENTICAL sweep: same node count,
    /// same verdict, same witness as an engine that never built the tables.
    #[test]
    fn box_prune_kill_switch_is_byte_identical() {
        let mut rng = 0x00C0_FFEE_0BAD_F00Du64;
        let ms = random_market_split(&mut rng, 12, 2, 20);
        let mut eng = Engine::build(&ms, deadline(), false, 1, None).expect("engine builds");
        let half: Vec<i64> = ms.a.iter().map(|row| row.iter().sum::<i64>() / 2).collect();
        let xd = eng
            .particular(&ms, &half)
            .and_then(|v| eng.babai(&v))
            .expect("balanced face is inhabited over the integers");

        eng.box_prune = None;
        let (a_result, a_nodes) = eng.enumerate_serial_with_cap(&xd, NODE_BUDGET);
        let (b_result, b_nodes) = eng.enumerate_serial_with_cap(&xd, NODE_BUDGET);
        assert_eq!(a_result, b_result);
        assert_eq!(a_nodes, b_nodes, "the disabled path must be deterministic");

        // With the tables installed the node count may only shrink.
        let tables = box_prune_tables(
            &eng.bstar_q.clone(),
            &eng.cnorm_i.clone(),
            &eng.lo.clone(),
            &eng.up.clone(),
            eng.dim,
            eng.n,
        );
        eng.box_prune = tables;
        let (c_result, c_nodes) = eng.enumerate_serial_with_cap(&xd, NODE_BUDGET);
        assert_eq!(a_result, c_result, "the prune changed the verdict");
        assert!(c_nodes <= a_nodes);
    }

    /// A box endpoint outside the exactly-representable `f64` integers must
    /// DECLINE the prune rather than test against a rounded bound.
    #[test]
    fn box_prune_declines_inexact_bounds() {
        let eng = two_dim_enumeration_engine();
        assert!(box_prune_tables(
            &eng.bstar_q,
            &eng.cnorm_i,
            &[0, 0],
            &[1, (1i64 << 53) + 1],
            eng.dim,
            eng.n
        )
        .is_none());
        assert!(
            box_prune_tables(&eng.bstar_q, &eng.cnorm_i, &[0, 0], &[1, 1], eng.dim, eng.n)
                .is_some()
        );
    }

    /// PARALLEL PATH OBLIGATION. The frontier and its workers must prune with
    /// the IDENTICAL centres, which means `WorkItem` has to carry the `C` row
    /// and the two error accumulators. If it does not, a worker resumes from a
    /// zeroed centre row, prunes on nonsense, and can cut a real witness — so
    /// this compares the parallel verdict against the serial one face by face.
    #[test]
    fn box_prune_parallel_frontier_agrees_with_serial() {
        let mut rng = 0x0BAD_5EED_1357_9BDFu64;
        let mut saw_empty = 0usize;
        let mut saw_feasible = 0usize;
        for case in 0..8usize {
            let ms = random_market_split(&mut rng, 12 + (case % 3), 2, 22);
            let Some(mut eng) = Engine::build(&ms, deadline(), false, 4, None) else {
                continue;
            };
            eng.box_prune =
                box_prune_tables(&eng.bstar_q, &eng.cnorm_i, &eng.lo, &eng.up, eng.dim, eng.n);
            assert!(eng.box_prune.is_some());
            let half: Vec<i64> = ms.a.iter().map(|row| row.iter().sum::<i64>() / 2).collect();
            for shift in -1i64..=1 {
                let d: Vec<i64> = half.iter().map(|&v| v + shift).collect();
                let Some(xd) = eng.particular(&ms, &d).and_then(|v| eng.babai(&v)) else {
                    continue;
                };
                let par = eng.enumerate_parallel(&xd);
                let ser = eng.enumerate_serial(&xd);
                let truth = brute_force_face(&ms, &d);
                match (&par, &ser) {
                    (EnumResult::Empty, EnumResult::Empty) => {
                        saw_empty += 1;
                        assert!(
                            truth.is_empty(),
                            "UNSOUND: parallel+serial proved EMPTY, brute force found {}",
                            truth.len()
                        );
                    }
                    (EnumResult::Feasible(y), EnumResult::Feasible(_)) => {
                        saw_feasible += 1;
                        // Any witness may win the race, but it must be exact.
                        let x = lattice_point(&eng, &xd, y);
                        assert!(
                            truth.contains(&x),
                            "parallel witness {x:?} is not a face point"
                        );
                    }
                    (EnumResult::Aborted, _) | (_, EnumResult::Aborted) => {}
                    (EnumResult::Capped, _) | (_, EnumResult::Capped) => {}
                    other => panic!("parallel/serial verdicts diverged: {other:?}"),
                }
            }
        }
        assert!(saw_empty > 0 && saw_feasible > 0, "vacuous parallel corpus");
    }
}

#[cfg(test)]
mod kernel_reform_tests {
    use super::*;
    use crate::model::{Col, Model, Sense};
    use ay_test_support::env::lock_env;
    use std::time::Duration;

    /// EVERY SOLVING TEST IN THIS MODULE TAKES THE ENVIRONMENT LOCK, and it is not
    /// because any of them mutates the environment. `lock_env` serialises
    /// MUTATORS; it does nothing for a READER, and a solve is a reader of a couple
    /// of dozen `AY_*` names. Sibling tests in this binary legitimately set knobs
    /// around their own solves (`bab::tests::solve_node_capped` installs
    /// `AY_MILP_MAX_NODES` while it runs, exactly as its doc says), and a solve on
    /// another thread inside that window silently inherits the cap.
    ///
    /// That is not hypothetical here: with the cap leaked in, this module's
    /// differential saw `Feasible { incumbent_only: true, dual_bound: None }` on a
    /// three-column model — a tree stopped at node 0 — and the seed it landed on
    /// moved between runs (65, then 66), which is the signature of a race and not
    /// of a model. Joining the same lock puts these readers and those writers in
    /// one order. It costs suite wall time and buys a suite whose failures mean
    /// something.
    fn solve_lock() -> std::sync::MutexGuard<'static, ()> {
        lock_env()
    }

    fn deadline() -> Instant {
        Instant::now() + Duration::from_secs(30)
    }

    fn int(v: i64) -> BigRational {
        BigRational::from(BigInt::from(v))
    }

    /// MIPLIB `ej` verbatim: `min x₀` subject to
    /// `31013·x₀ − 41014·x₁ − 51015·x₂ = 0`, all three columns integer, `x₀ ≥ 1`,
    /// `x₁,x₂ ≥ 0` with NO upper bound. Optimum 25508 (attained at
    /// `x = (25508, 1, 15506)`).
    fn ej_model() -> Model {
        let mut m = Model::new();
        let x0 = m.add_int_col(1.0, f64::INFINITY);
        let x1 = m.add_int_col(0.0, f64::INFINITY);
        let x2 = m.add_int_col(0.0, f64::INFINITY);
        m.add_row(0.0, 0.0, &[(x0, 31013.0), (x1, -41014.0), (x2, -51015.0)]);
        m.set_objective(&[(x0, 1.0)], Sense::Minimize);
        m
    }

    /// THE MEASUREMENT THE DEVICE EXISTS FOR. Stock branch and bound loses `ej`
    /// at 235,008 nodes / 28.9 s with the dual bound pinned at 1; in the
    /// reformulated frame it proves the exact optimum 25508 immediately. Both
    /// halves are asserted here: the exact value, and that the widened witness is
    /// feasible for the ORIGINAL model at exactly that objective value.
    #[test]
    fn ej_is_proven_optimal_at_25508_in_the_reformulated_frame() {
        let _env = solve_lock();
        let m = ej_model();
        let (reduced, post) = reformulate_kernel(&m).expect("ej is exactly this shape");
        // One equality over three columns of rank 1: two new columns, and they
        // are FREE — the property the whole reformulation rests on.
        assert_eq!(reduced.num_cols(), 2);
        for j in 0..reduced.num_cols() {
            let c = Col(j as u32);
            assert_eq!(
                reduced.col_bounds(c),
                (f64::NEG_INFINITY, f64::INFINITY),
                "reformulated column {j} must be free on both sides"
            );
            assert!(reduced.col_kind(c).is_integral());
        }
        // Three finite bound sides (x₀ ≥ 1, x₁ ≥ 0, x₂ ≥ 0) become three rows;
        // the equality row is gone.
        assert_eq!(reduced.num_rows(), 3);

        let opts = SolveOpts::new().with_time_limit(Duration::from_secs(30));
        match crate::bab::solve_milp(&reduced, &opts) {
            Outcome::Optimal {
                value,
                model_values,
                ..
            } => {
                let full = post.widen(&model_values);
                let recovered = value + post.const_delta();
                assert_eq!(recovered, int(25508), "ej optimum");
                assert!(
                    m.check_point(&full).is_ok(),
                    "widened witness must be feasible for the ORIGINAL model: {full:?}"
                );
                assert_eq!(m.objective_value_at(&full), recovered);
            }
            other => panic!("expected Optimal 25508 on the reformulated ej, got {other:?}"),
        }
    }

    /// The same proof through the PUBLIC solve entry, so the `bab.rs` hook and
    /// its `expand_kernel_outcome` are exercised end to end: the value comes back
    /// in the caller's frame, the witness in the caller's column space.
    ///
    /// `with_tree_cert_leaves(0)` USED TO BE LOAD-BEARING AND NO LONGER IS. This
    /// reduction — and duplicate-column dedup — was gated on
    /// `opts.tree_cert_leaves == 0` at its `bab::solve_milp` call site, because
    /// neither one's TREE lifts: the kernel's splits are on `z` columns, so
    /// `z_t <= k` pulled back through `x_C = x_p + B z` is a lattice disjunction
    /// `TreeNode` cannot express. `SolveOpts` DEFAULTS that field to 256, so on
    /// default options the reformulation was never reached and `ej` was still lost.
    /// The gates are now decoupled from capture (`bab::cert_decouple_enabled`,
    /// `bab::harvest_tree_cert_by_resolve`), which is what makes the sibling test
    /// `ej_is_proven_on_default_options` below possible; this one keeps the explicit
    /// `0` so the pre-decoupling path stays covered too. See the note on
    /// `crate::bab::expand_kernel_outcome`.
    #[test]
    fn ej_is_proven_through_the_public_solve_entry() {
        let _env = solve_lock();
        let m = ej_model();
        let opts = SolveOpts::new()
            .with_tree_cert_leaves(0)
            .with_time_limit(Duration::from_secs(30));
        match crate::bab::solve_milp(&m, &opts) {
            Outcome::Optimal {
                value,
                model_values,
                ..
            } => {
                assert_eq!(value, int(25508));
                assert_eq!(model_values.len(), 3);
                assert!(m.check_point(&model_values).is_ok());
            }
            other => panic!("expected Optimal 25508 from the public entry, got {other:?}"),
        }
    }

    /// THE POINT OF THE DECOUPLING, as one assertion: `ej` on DEFAULT options.
    ///
    /// `SolveOpts::new()` arms tree-certificate capture (`tree_cert_leaves` 256),
    /// and that alone used to switch the reformulation off — so this exact solve
    /// returned `Unknown` after burning the whole budget on 271,642 nodes with the
    /// dual bound stuck at 1. Nothing about `ej` is infeasible, so there was never
    /// a tree certificate on offer to justify the trade; the artifact slot the
    /// reduction was surrendered for cannot be filled by an `Optimal` verdict at
    /// all (`tree_cert` lives on `Outcome::Infeasible` and nowhere else).
    ///
    /// A 30 s limit and not a tight one: what is being asserted is the REDUCTION
    /// firing, and the reformulated instance proves in 3 nodes, so a failure here
    /// means the gate stopped firing rather than that the box was slow.
    #[test]
    fn ej_is_proven_on_default_options() {
        let _env = solve_lock();
        let m = ej_model();
        let opts = SolveOpts::new().with_time_limit(Duration::from_secs(30));
        match crate::bab::solve_milp(&m, &opts) {
            Outcome::Optimal {
                value,
                model_values,
                ..
            } => {
                assert_eq!(value, int(25508));
                assert_eq!(model_values.len(), 3);
                assert!(m.check_point(&model_values).is_ok());
            }
            other => panic!("expected Optimal 25508 on DEFAULT options, got {other:?}"),
        }
    }

    /// BRUTE-FORCE BIJECTION. `2x₀ + 3x₁ + 5x₂ = 11` over `x ∈ [0,4]³ ∩ ℤ³`:
    /// enumerate every integer point of the ORIGINAL box-and-equality, enumerate
    /// every `z` of the reformulated frame whose widening lands in the box, and
    /// assert the two sets correspond EXACTLY — same points, and one `z` per
    /// point (so the map is injective as well as onto).
    #[test]
    fn reformulated_integer_points_are_in_exact_bijection_with_the_original() {
        let mut m = Model::new();
        let cols: Vec<Col> = (0..3).map(|_| m.add_int_col(0.0, 4.0)).collect();
        m.add_row(
            11.0,
            11.0,
            &[(cols[0], 2.0), (cols[1], 3.0), (cols[2], 5.0)],
        );
        m.set_objective(&[(cols[0], 1.0)], Sense::Minimize);

        let mut brute: Vec<[i64; 3]> = Vec::new();
        for a in 0..=4i64 {
            for b in 0..=4i64 {
                for c in 0..=4i64 {
                    if 2 * a + 3 * b + 5 * c == 11 {
                        brute.push([a, b, c]);
                    }
                }
            }
        }
        assert!(brute.len() >= 3, "the fixture must have several points");

        let (reduced, post) = reformulate_kernel(&m).expect("max|a| = 5 exceeds the range 4");
        assert_eq!(reduced.num_cols(), 2, "3 columns, rank 1 ⟹ kernel dim 2");

        // Every z in a range comfortably wider than the box can reach.
        let mut image: Vec<[i64; 3]> = Vec::new();
        for z0 in -100..=100i64 {
            for z1 in -100..=100i64 {
                let full = post.widen(&[int(z0), int(z1)]);
                let pt: Vec<i64> = full
                    .iter()
                    .map(|v| {
                        assert!(v.is_integer(), "x_p + Bz is integral for integral z");
                        v.to_integer().to_i64().expect("small")
                    })
                    .collect();
                if pt.iter().all(|&v| (0..=4).contains(&v))
                    && 2 * pt[0] + 3 * pt[1] + 5 * pt[2] == 11
                {
                    image.push([pt[0], pt[1], pt[2]]);
                }
                // Whatever the widening produces, it must satisfy the equality —
                // that is S1(a) observed end to end.
                assert_eq!(2 * pt[0] + 3 * pt[1] + 5 * pt[2], 11);
            }
        }
        let mut sorted_image = image.clone();
        sorted_image.sort_unstable();
        sorted_image.dedup();
        assert_eq!(
            sorted_image.len(),
            image.len(),
            "two distinct z widened to the same point: the map is not injective"
        );
        let mut sorted_brute = brute.clone();
        sorted_brute.sort_unstable();
        assert_eq!(
            sorted_image, sorted_brute,
            "the reformulated feasible set must be exactly the original one"
        );
    }

    // ---------------------------------------------------------------------
    // S4 — THE AHL TRANSLATION STEP `x_p ← x_p − B·round(B⁺(x_p − t))`
    //
    // THE EXISTING SUITE IS BLIND TO THIS CLASS OF DEFECT AND SO IS THE 40-
    // INSTANCE CORPUS: 433 lib tests and a full corpus run were green with the
    // translation missing entirely. What the missing step breaks is not the
    // reduced FEASIBLE SET — that is provably intact — but the SCALE of the
    // numbers written on it, and no assertion about verdicts on the shapes the
    // shipped gate admits can see that. Hence the three tests below: a magnitude
    // bound with a PROOF behind it, the two models from the review that actually
    // returned a wrong `Optimal`, and a brute-force differential wide enough to
    // have found the defect on its own.
    // ---------------------------------------------------------------------

    /// `ceil(√x)` for a non-negative `BigInt`, exactly.
    fn isqrt_ceil(x: &BigInt) -> BigInt {
        let r = num_integer::Roots::sqrt(x);
        if &r * &r == *x {
            r
        } else {
            r + BigInt::one()
        }
    }

    fn norm_sq(v: &[BigInt]) -> BigInt {
        v.iter().map(|x| x * x).sum()
    }

    /// Re-run the reformulation's own front half so the RAW (untranslated)
    /// `x_p` — the thing that used to ship — is observable next to the translated
    /// one. Returns `(x_p_raw, x_p_translated, B)`.
    fn raw_and_translated_xp(
        a: &[Vec<i64>],
        b: &[i64],
        target: &[BigRational],
    ) -> (Vec<BigInt>, Vec<BigInt>, Vec<Vec<BigInt>>) {
        let m = a.len();
        let n = a[0].len();
        let abig: Vec<Vec<BigInt>> = a
            .iter()
            .map(|r| r.iter().copied().map(BigInt::from).collect())
            .collect();
        let bbig: Vec<BigInt> = b.iter().copied().map(BigInt::from).collect();
        let (u, rank, mm) = col_hnf(&abig, m, n, deadline()).expect("column HNF");
        let raw =
            hnf_particular(&mm, &u, m, n, rank, &bbig, deadline()).expect("an integer solution");
        assert!(
            satisfies_exactly(&abig, &bbig, &raw),
            "the raw particular solution must already solve A x = b"
        );
        let d = n - rank;
        let k0: Vec<Vec<BigInt>> = (0..d)
            .map(|t| (0..n).map(|i| u[i][rank + t].clone()).collect())
            .collect();
        let basis = lll(k0, deadline()).expect("LLL");
        let tr = translate_near_box(&raw, &basis, target, deadline()).expect("translation");
        assert!(
            satisfies_exactly(&abig, &bbig, &tr),
            "S4: the translated x_p must STILL satisfy A x = b exactly"
        );
        (raw, tr, basis)
    }

    /// THE MAGNITUDE TEST, with the bound it asserts actually proved rather than
    /// eyeballed.
    ///
    /// Babai's nearest-plane sweep leaves `x_p − t = Σ μ_i·b*_i + r` with every
    /// `|μ_i| ≤ ½`, where `r` is the component orthogonal to `span(B) = ker(A)`.
    /// `r` is not a property of the representative at all — for ANY `x*` with
    /// `A x* = b`, `x* − x_p ∈ ker(A)`, so `x*− t` has the SAME orthogonal
    /// component and `‖r‖ ≤ ‖x*− t‖`. With `‖b*_i‖ ≤ ‖b_i‖` that gives the exact,
    /// checkable statement
    ///
    /// ```text
    ///   ‖x_p − t‖ ≤ ½·√(Σ‖b_i‖²) + ‖x*− t‖     for any feasible x*
    /// ```
    ///
    /// which this asserts over `BigInt` (squared, in half-units, with `√` taken
    /// as `ceil√`). Taking `x*` to be a brute-force point INSIDE THE BOX makes
    /// the right-hand side O(box) + O(reduced basis) — which is what "near the
    /// box" means and is the whole content of the step.
    ///
    /// The equality block is `fz135`'s: coefficients ~5·10⁴ over a `[0,5]⁴` box.
    /// MEASURED: the raw `x_p` has max entry 5.9·10¹⁵ and MISSES this bound by
    /// eleven orders of magnitude; the translated one has max entry 5 and meets
    /// it. Both halves are asserted, so the test cannot pass with the step
    /// disabled.
    #[test]
    fn the_translation_pulls_x_p_from_o_det_down_to_o_box() {
        let a = vec![
            vec![-11051i64, 23397, -25319, -12664],
            vec![-14689, 50015, -19553, -24374],
        ];
        let b = vec![-136042i64, -131964];
        // t = box midpoints of `[0,5]⁴`, i.e. 5/2 each.
        let half = BigRational::new(BigInt::from(5), BigInt::from(2));
        let target = vec![half.clone(), half.clone(), half.clone(), half];
        let (raw, tr, basis) = raw_and_translated_xp(&a, &b, &target);

        // A brute-force feasible point of the equality block inside the box —
        // the `x*` the bound is stated against.
        let mut xstar: Option<Vec<i64>> = None;
        'outer: for p0 in 0..=5i64 {
            for p1 in 0..=5i64 {
                for p2 in 0..=5i64 {
                    for p3 in 0..=5i64 {
                        let p = [p0, p1, p2, p3];
                        if a.iter().zip(&b).all(|(row, &rhs)| {
                            row.iter().zip(&p).map(|(c, v)| c * v).sum::<i64>() == rhs
                        }) {
                            xstar = Some(p.to_vec());
                            break 'outer;
                        }
                    }
                }
            }
        }
        let xstar = xstar.expect("the fixture's equality block has a point in its box");

        // Everything below is in HALF-UNITS (`2·(x − t)`), which clears the ½ in
        // the midpoints and keeps the whole comparison in ℤ.
        let dbl = |x: &[BigInt]| -> Vec<BigInt> {
            x.iter()
                .zip(&target)
                .map(|(v, t)| {
                    let q = BigRational::from(v.clone()) * BigInt::from(2) - t * BigInt::from(2);
                    assert!(
                        q.is_integer(),
                        "2·(x − t) is integral for a half-integral t"
                    );
                    q.to_integer()
                })
                .collect()
        };
        let u_tr = norm_sq(&dbl(&tr));
        let u_raw = norm_sq(&dbl(&raw));
        let s_x = norm_sq(&dbl(&xstar
            .iter()
            .copied()
            .map(BigInt::from)
            .collect::<Vec<_>>()));
        let s_b: BigInt = basis.iter().map(|v| norm_sq(v)).sum();
        // (½√S + ‖x*−t‖)² in half-units: U ≤ S + Sx + 2·√(S·Sx).
        let bound = &s_b + &s_x + BigInt::from(2) * isqrt_ceil(&(&s_b * &s_x));

        println!(
            "S4 magnitude: max|x_p| raw={} translated={} bound_sq={bound} \
             raw_sq={u_raw} translated_sq={u_tr}",
            max_abs_big(&raw),
            max_abs_big(&tr),
        );
        assert!(
            u_tr <= bound,
            "translated x_p must satisfy the Babai bound: {u_tr} > {bound}"
        );
        assert!(
            max_abs_big(&tr) <= BigInt::from(5),
            "on this block the translated x_p lands INSIDE the [0,5] box; got {}",
            max_abs_big(&tr)
        );
        // NON-VACUITY: the untranslated representative misses the same bound by
        // orders of magnitude. If this ever stops holding the fixture has gone
        // stale and the test above proves nothing.
        assert!(
            u_raw > bound,
            "the raw x_p is supposed to VIOLATE the bound; the fixture is stale"
        );
        assert!(
            max_abs_big(&raw) > BigInt::from(10).pow(12),
            "the raw x_p is supposed to be astronomically far from the box; got {}",
            max_abs_big(&raw)
        );
    }

    /// `fz135` from the adversarial review, verbatim. MAXIMIZE, a 2×4 equality
    /// block with ~5·10⁴ coefficients over `[0,5]`, and two surviving rows that
    /// TOUCH `C` — the non-isolated shape, which is why it needs the test seam.
    ///
    /// With the translation missing this model reported `Optimal −10` against a
    /// true optimum of `−9`: a feasible point, a worse value, and `Trust`
    /// unbothered. The mechanism is entirely arithmetic — `const_delta` ran at
    /// −6.77·10¹⁵, inside `[2^52, 2^53)` where the `f64` ULP is exactly 1, so the
    /// reduced LP was resolving the objective at the granularity of the answer.
    /// Build a fixture from the review: integral columns with `[0, up_j]` boxes,
    /// an objective, and rows given as `(lo, up, terms)` with `None` for an
    /// infinite side.
    fn review_fixture(
        ups: &[i64],
        obj: &[i64],
        sense: Sense,
        rows: &[(Option<i64>, Option<i64>, &[(usize, i64)])],
    ) -> Model {
        let mut m = Model::new();
        let cols: Vec<Col> = ups.iter().map(|&u| m.add_int_col(0.0, u as f64)).collect();
        for &(lo, up, terms) in rows {
            let t: Vec<(Col, f64)> = terms.iter().map(|&(j, a)| (cols[j], a as f64)).collect();
            m.add_row(
                lo.map_or(f64::NEG_INFINITY, |v| v as f64),
                up.map_or(f64::INFINITY, |v| v as f64),
                &t,
            );
        }
        let o: Vec<(Col, f64)> = obj
            .iter()
            .enumerate()
            .filter(|&(_, &c)| c != 0)
            .map(|(j, &c)| (cols[j], c as f64))
            .collect();
        m.set_objective(&o, sense);
        m
    }

    /// `fz135` from the adversarial review, verbatim. MAXIMIZE, a 2x4 equality
    /// block with ~5e4 coefficients over `[0,5]`, and two surviving rows that
    /// TOUCH `C` -- the non-isolated shape, which is why it needs the test seam.
    ///
    /// With the translation missing this model reported `Optimal -10` against a
    /// true optimum of `-9`: a feasible point, a worse value, and `Trust`
    /// unbothered. The mechanism is entirely arithmetic -- `const_delta` ran at
    /// -6.77e15, inside `[2^52, 2^53)` where the `f64` ULP is exactly 1, so the
    /// reduced LP was resolving the objective at the granularity of the answer.
    fn fz135() -> Model {
        review_fixture(
            &[5, 5, 5, 5, 3, 2],
            &[-1, -5, -12, 0, 13, 1],
            Sense::Maximize,
            &[
                (
                    Some(-136042),
                    Some(-136042),
                    &[(0, -11051), (1, 23397), (2, -25319), (3, -12664)],
                ),
                (
                    Some(-131964),
                    Some(-131964),
                    &[(0, -14689), (1, 50015), (2, -19553), (3, -24374)],
                ),
                (Some(-10), None, &[(1, -3), (2, -1), (5, -1)]),
                (
                    Some(-42),
                    None,
                    &[(0, -7), (1, -7), (2, -4), (4, 3), (5, -8)],
                ),
            ],
        )
    }

    /// `fz2169` from the same review: MINIMIZE, a 2x4 block over `[0,4]`, three
    /// surviving rows touching `C`. Reported `Optimal 20` against a true optimum
    /// of `15`.
    fn fz2169() -> Model {
        review_fixture(
            &[4, 4, 4, 4, 2, 2],
            &[20, 12, -11, -18, -2, -5],
            Sense::Minimize,
            &[
                (
                    Some(-243560),
                    Some(-243560),
                    &[(0, 33989), (1, -46812), (2, -49007), (3, -29035)],
                ),
                (
                    Some(-26654),
                    Some(-26654),
                    &[(0, 8009), (1, -24511), (2, 12216), (3, -6898)],
                ),
                (Some(1), None, &[(0, -5), (3, 8), (4, 2)]),
                (None, Some(18), &[(1, 3), (2, 1), (4, 7), (5, -2)]),
                (Some(-12), None, &[(0, 1), (3, -7), (4, 6), (5, -3)]),
            ],
        )
    }

    /// Enumerate every integer point of `model`'s (finite, integral) box and
    /// return the best objective value among the feasible ones, plus the count of
    /// feasible points. The reference the reformulation is judged against.
    fn brute_force_optimum(model: &Model) -> (Option<BigRational>, usize) {
        let nc = model.num_cols();
        let mut lo = Vec::with_capacity(nc);
        let mut up = Vec::with_capacity(nc);
        for j in 0..nc {
            let (l, u) = model.col_bounds(Col(j as u32));
            assert!(l.is_finite() && u.is_finite(), "brute force needs a box");
            lo.push(l as i64);
            up.push(u as i64);
        }
        let mut pt = lo.clone();
        let mut best: Option<BigRational> = None;
        let mut feasible = 0usize;
        let maximize = model.sense() == Sense::Maximize;
        loop {
            let vals: Vec<BigRational> = pt.iter().map(|&v| int(v)).collect();
            if model.check_point(&vals).is_ok() {
                feasible += 1;
                let v = model.objective_value_at(&vals);
                let better = match &best {
                    None => true,
                    Some(b) => {
                        if maximize {
                            v > *b
                        } else {
                            v < *b
                        }
                    }
                };
                if better {
                    best = Some(v);
                }
            }
            let mut k = 0;
            loop {
                if k == nc {
                    return (best, feasible);
                }
                pt[k] += 1;
                if pt[k] <= up[k] {
                    break;
                }
                pt[k] = lo[k];
                k += 1;
            }
        }
    }

    /// Solve `model` through the reformulation (with the isolation gate relaxed
    /// by the test seam) and return the caller-frame optimum, asserting the
    /// widened witness is feasible for the ORIGINAL model at exactly that value.
    fn reformulated_optimum(model: &Model) -> Option<BigRational> {
        let (reduced, post) = reformulate_kernel_nonisolated_for_test(model)?;
        let opts = SolveOpts::new().with_time_limit(Duration::from_secs(30));
        match crate::bab::solve_milp(&reduced, &opts) {
            Outcome::Optimal {
                value,
                model_values,
                ..
            } => {
                let full = post.widen(&model_values);
                let recovered = value + post.const_delta();
                assert!(
                    model.check_point(&full).is_ok(),
                    "the widened witness must be feasible for the ORIGINAL model: {full:?}"
                );
                assert_eq!(
                    model.objective_value_at(&full),
                    recovered,
                    "the witness's objective must BE the reported value"
                );
                Some(recovered)
            }
            Outcome::Infeasible { .. } => None,
            other => panic!("reduced model gave {other:?}"),
        }
    }

    /// `fz135`: reformulated answer must EQUAL the brute-force optimum. With the
    /// translation missing this returns `−10` for a true `−9`.
    #[test]
    fn review_fixture_fz135_agrees_with_brute_force() {
        let _env = solve_lock();
        let m = fz135();
        let (brute, feasible) = brute_force_optimum(&m);
        assert!(feasible > 0, "the fixture must be feasible");
        assert_eq!(brute, Some(int(-9)), "the review's recorded true optimum");
        assert_eq!(
            reformulated_optimum(&m),
            brute,
            "fz135: the reformulated optimum must equal the brute-force optimum"
        );
    }

    /// `fz2169`: same, MINIMIZE. With the translation missing this returns `20`
    /// for a true `15`.
    #[test]
    fn review_fixture_fz2169_agrees_with_brute_force() {
        let _env = solve_lock();
        let m = fz2169();
        let (brute, feasible) = brute_force_optimum(&m);
        assert!(feasible > 0, "the fixture must be feasible");
        assert_eq!(brute, Some(int(15)), "the review's recorded true optimum");
        assert_eq!(
            reformulated_optimum(&m),
            brute,
            "fz2169: the reformulated optimum must equal the brute-force optimum"
        );
    }

    /// SplitMix64 — a deterministic generator, so a failing seed in the
    /// differential below is reproducible verbatim.
    struct SplitMix(u64);

    impl SplitMix {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        }

        /// Uniform in `[lo, hi]`.
        fn range(&mut self, lo: i64, hi: i64) -> i64 {
            let span = (hi - lo + 1) as u64;
            lo + (self.next() % span) as i64
        }

        fn nonzero(&mut self, mag: i64) -> i64 {
            let v = self.range(-mag, mag);
            if v == 0 {
                mag
            } else {
                v
            }
        }
    }

    /// A random model of THE SHAPE THAT EXPOSES THE DEFECT: an integral equality
    /// block whose coefficients (~10⁴–10⁵) dwarf the box, plus surviving rows
    /// that touch `C`. The equality right-hand side is generated as `A·pt` for a
    /// `pt` inside the box, so the block always has a solution there and the
    /// instance is rarely trivially infeasible.
    fn random_exposing_model(seed: u64) -> Model {
        let mut r = SplitMix(seed);
        let ncc = r.range(3, 4) as usize;
        let nsurv = r.range(1, 2) as usize;
        let cap = r.range(4, 5);
        let mut m = Model::new();
        let c_cols: Vec<Col> = (0..ncc).map(|_| m.add_int_col(0.0, cap as f64)).collect();
        let s_cols: Vec<Col> = (0..nsurv).map(|_| m.add_int_col(0.0, 2.0)).collect();
        let pt: Vec<i64> = (0..ncc).map(|_| r.range(0, cap)).collect();

        let ne = if ncc == 3 { 1 } else { r.range(1, 2) as usize };
        for _ in 0..ne {
            let coeffs: Vec<i64> = (0..ncc).map(|_| r.nonzero(60_000)).collect();
            let rhs: i64 = coeffs.iter().zip(&pt).map(|(a, p)| a * p).sum();
            let terms: Vec<(Col, f64)> = c_cols
                .iter()
                .zip(&coeffs)
                .map(|(&c, &a)| (c, a as f64))
                .collect();
            m.add_row(rhs as f64, rhs as f64, &terms);
        }
        // Surviving rows, deliberately NON-ISOLATED: each touches at least one
        // member of `C`, which is what carries `x_p` into a row that stays.
        for _ in 0..r.range(1, 2) {
            let mut terms: Vec<(Col, f64)> = Vec::new();
            let mut base = 0i64;
            for (j, &c) in c_cols.iter().enumerate() {
                if r.range(0, 9) < 5 {
                    let a = r.nonzero(9);
                    terms.push((c, a as f64));
                    base += a * pt[j];
                }
            }
            if terms.is_empty() {
                let a = r.nonzero(9);
                terms.push((c_cols[0], a as f64));
                base += a * pt[0];
            }
            for &c in &s_cols {
                if r.range(0, 9) < 8 {
                    let a = r.nonzero(9);
                    terms.push((c, a as f64));
                    base += a;
                }
            }
            let slack = r.range(0, 7);
            if r.range(0, 1) == 0 {
                m.add_row(f64::NEG_INFINITY, (base + slack) as f64, &terms);
            } else {
                m.add_row((base - slack) as f64, f64::INFINITY, &terms);
            }
        }
        let obj: Vec<(Col, f64)> = c_cols
            .iter()
            .chain(&s_cols)
            .map(|&c| (c, r.range(-20, 20) as f64))
            .collect();
        let sense = if r.range(0, 1) == 0 {
            Sense::Minimize
        } else {
            Sense::Maximize
        };
        m.set_objective(&obj, sense);
        m
    }

    /// THE DIFFERENTIAL THAT WOULD HAVE FOUND THIS. Hundreds of random models of
    /// the exposing shape, each brute-forced over its whole box and each solved
    /// through the reformulation; the optimum must MATCH and the reduced feasible
    /// set must be in exact bijection with the original.
    ///
    /// The review needed 2,856 models to see two wrong answers because it was
    /// sampling BOTH shapes; the generator here only builds the exposing one, and
    /// with the translation disabled the very first hundred seeds disagree.
    #[test]
    fn randomised_brute_force_differential_over_the_exposing_shape() {
        let _env = solve_lock();
        let mut fired = 0usize;
        let mut disagreements: Vec<u64> = Vec::new();
        for seed in 0..400u64 {
            let m = random_exposing_model(seed);
            let Some((reduced, post)) = reformulate_kernel_nonisolated_for_test(&m) else {
                continue;
            };
            fired += 1;
            let (brute, feasible) = brute_force_optimum(&m);

            // (1) THE FEASIBLE SET, as an exact BIJECTION. Enumerate the
            // integer points of the `C` box that satisfy the equality block,
            // enumerate `z` over a range far wider than the box can reach, and
            // assert the two sets are EQUAL and the map injective. The `z` range
            // is only usable BECAUSE `x_p` now sits near the box — with the
            // untranslated representative the box lives at `z ~ 10^15` and no
            // finite enumeration would find it.
            let d = post.z.len();
            if d <= 2 {
                let cbox: Vec<(i64, i64)> = post
                    .cols_c
                    .iter()
                    .map(|&j| {
                        let (l, u) = m.col_bounds(Col(j as u32));
                        (l as i64, u as i64)
                    })
                    .collect();
                let mut brute_c: Vec<Vec<i64>> = Vec::new();
                let mut pt: Vec<i64> = cbox.iter().map(|&(l, _)| l).collect();
                loop {
                    if post.e_rows.iter().all(|&ri| {
                        let (coeffs, rlo, _) = m.row(Row(ri as u32));
                        let lhs: f64 = coeffs
                            .iter()
                            .map(|&(c, a)| {
                                a * pt[post
                                    .cols_c
                                    .iter()
                                    .position(|&j| j == c as usize)
                                    .expect("an E row's support is exactly C")]
                                    as f64
                            })
                            .sum();
                        lhs == rlo
                    }) {
                        brute_c.push(pt.clone());
                    }
                    let mut k = 0;
                    loop {
                        if k == cbox.len() {
                            break;
                        }
                        pt[k] += 1;
                        if pt[k] <= cbox[k].1 {
                            break;
                        }
                        pt[k] = cbox[k].0;
                        k += 1;
                    }
                    if k == cbox.len() {
                        break;
                    }
                }

                let mut image: Vec<Vec<i64>> = Vec::new();
                let span = 60i64;
                let mut zv = vec![-span; d];
                loop {
                    let mut reduced_pt = vec![BigRational::zero(); reduced.num_cols()];
                    for (t, &zc) in post.z.iter().enumerate() {
                        reduced_pt[zc.index()] = int(zv[t]);
                    }
                    let full = post.widen(&reduced_pt);
                    let xc: Vec<i64> = post
                        .cols_c
                        .iter()
                        .map(|&j| {
                            assert!(full[j].is_integer(), "x_p + Bz is integral");
                            full[j].to_integer().to_i64().expect("small after S4")
                        })
                        .collect();
                    if xc.iter().zip(&cbox).all(|(&v, &(l, u))| v >= l && v <= u) {
                        image.push(xc);
                    }
                    let mut k = 0;
                    loop {
                        if k == d {
                            break;
                        }
                        zv[k] += 1;
                        if zv[k] <= span {
                            break;
                        }
                        zv[k] = -span;
                        k += 1;
                    }
                    if k == d {
                        break;
                    }
                }
                let mut sorted = image.clone();
                sorted.sort_unstable();
                sorted.dedup();
                assert_eq!(
                    sorted.len(),
                    image.len(),
                    "seed {seed}: two z widened to the same x_C -- not injective"
                );
                brute_c.sort_unstable();
                assert_eq!(
                    sorted, brute_c,
                    "seed {seed}: the reduced feasible set is not the original one"
                );
            }

            // (2) THE OPTIMUM.
            let opts = SolveOpts::new().with_time_limit(Duration::from_secs(30));
            match crate::bab::solve_milp(&reduced, &opts) {
                Outcome::Optimal {
                    value,
                    model_values,
                    ..
                } => {
                    let full = post.widen(&model_values);
                    let recovered = value + post.const_delta();
                    assert!(
                        m.check_point(&full).is_ok(),
                        "seed {seed}: widened witness infeasible for the original model"
                    );
                    if brute.as_ref() != Some(&recovered) {
                        disagreements.push(seed);
                    }
                }
                Outcome::Infeasible { .. } => {
                    if feasible != 0 {
                        disagreements.push(seed);
                    }
                }
                other => panic!("seed {seed}: reduced model gave {other:?}"),
            }
        }
        println!(
            "S4 differential: {fired} models fired, {} wrong",
            disagreements.len()
        );
        assert!(
            fired >= 100,
            "the generator must actually exercise the reformulation; fired={fired}"
        );
        assert!(
            disagreements.is_empty(),
            "reformulated optimum disagrees with brute force on seeds {disagreements:?}"
        );
    }

    /// A random model of THE SHAPE THE SHIPPED GATE ADMITS: an **isolated**
    /// integral equality block whose coefficients (~10⁴–10⁵) dwarf a small box,
    /// plus surviving rows that touch only columns OUTSIDE `C`.
    ///
    /// The generator above builds the NON-ISOLATED shape and can only be solved
    /// through the `#[cfg(test)]` seam. This one is the shape production actually
    /// sees, so its models go through the ordinary public entry — which is the
    /// point: root reductions are no longer gated on `tree_cert_leaves == 0`, so
    /// this call site is reachable on DEFAULT options for the first time and every
    /// model here is one the shipped engine will now really reformulate.
    ///
    /// Half the seeds anchor the equality's right-hand side on a point INSIDE the
    /// box (so the block is satisfiable there and the instance is usually
    /// feasible); the other half anchor it outside. An outside anchor keeps an
    /// integer solution in `ℤ^C` — so `hnf_particular` still succeeds and the gate
    /// still fires — while usually leaving the BOX empty. Both halves matter: the
    /// feasible one checks the optimum, and the infeasible one is the only way the
    /// tree-certificate harvest (`bab::harvest_tree_cert_by_resolve`) is exercised
    /// at all, since `tree_cert` exists on no other `Outcome` variant.
    fn random_isolated_model(seed: u64) -> Model {
        let mut r = SplitMix(seed);
        let ncc = r.range(2, 4) as usize;
        let nsurv = r.range(1, 2) as usize;
        let cap = r.range(3, 5);
        let mut m = Model::new();
        let c_cols: Vec<Col> = (0..ncc).map(|_| m.add_int_col(0.0, cap as f64)).collect();
        let s_cols: Vec<Col> = (0..nsurv).map(|_| m.add_int_col(0.0, 2.0)).collect();
        let inside = r.range(0, 1) == 0;
        let pt: Vec<i64> = (0..ncc)
            .map(|_| {
                if inside {
                    r.range(0, cap)
                } else {
                    r.range(cap + 1, cap + 6)
                }
            })
            .collect();
        let s_pt: Vec<i64> = (0..nsurv).map(|_| r.range(0, 2)).collect();

        // One equality for `ncc <= 3` and up to two for `ncc == 4`, so the kernel
        // always has dimension `d >= 1` and the reduced model is not the empty
        // frame.
        let ne = if ncc <= 3 { 1 } else { r.range(1, 2) as usize };
        for _ in 0..ne {
            let coeffs: Vec<i64> = (0..ncc).map(|_| r.nonzero(60_000)).collect();
            let rhs: i64 = coeffs.iter().zip(&pt).map(|(a, p)| a * p).sum();
            let terms: Vec<(Col, f64)> = c_cols
                .iter()
                .zip(&coeffs)
                .map(|(&c, &a)| (c, a as f64))
                .collect();
            m.add_row(rhs as f64, rhs as f64, &terms);
        }
        // Surviving rows over `s_cols` ONLY. A surviving row touching any member of
        // `C` is exactly what `require_isolated` (`reformulate_kernel_inner`)
        // refuses, and refusing it is NOT what this change touches — the admitted
        // set is identical to before. Keeping the generator inside the gate is
        // therefore deliberate: a campaign over models the engine declines proves
        // nothing about the engine.
        for _ in 0..r.range(1, 2) {
            let mut terms: Vec<(Col, f64)> = Vec::new();
            let mut base = 0i64;
            for (j, &c) in s_cols.iter().enumerate() {
                let a = r.nonzero(9);
                terms.push((c, a as f64));
                base += a * s_pt[j];
            }
            let slack = r.range(0, 7);
            if r.range(0, 1) == 0 {
                m.add_row(f64::NEG_INFINITY, (base + slack) as f64, &terms);
            } else {
                m.add_row((base - slack) as f64, f64::INFINITY, &terms);
            }
        }
        let obj: Vec<(Col, f64)> = c_cols
            .iter()
            .chain(&s_cols)
            .map(|&c| (c, r.range(-20, 20) as f64))
            .collect();
        let sense = if r.range(0, 1) == 0 {
            Sense::Minimize
        } else {
            Sense::Maximize
        };
        m.set_objective(&obj, sense);
        m
    }

    /// What one campaign run found: how many generated models the SHIPPED gate
    /// admitted, how many were instead claimed by the market-split device before
    /// the reformulation could be reached, how many infeasible verdicts came back
    /// carrying a VERIFYING tree certificate, and every seed that disagreed.
    struct IsolatedCampaign {
        generated: usize,
        admitted: usize,
        market_split: usize,
        infeasible: usize,
        verified_certs: usize,
        disagreements: Vec<u64>,
    }

    /// Run the campaign over `seeds`. Every admitted model is solved through the
    /// PUBLIC entry on DEFAULT options and judged against brute force over its
    /// whole box.
    fn isolated_shape_campaign(seeds: std::ops::Range<u64>) -> IsolatedCampaign {
        let mut c = IsolatedCampaign {
            generated: 0,
            admitted: 0,
            market_split: 0,
            infeasible: 0,
            verified_certs: 0,
            disagreements: Vec::new(),
        };
        for seed in seeds {
            let m = random_isolated_model(seed);
            c.generated += 1;
            // `solve_milp_advised_with_prefix` tries the market-split device and
            // the GF(2) parity device before the reformulation, so a model either
            // of those claims is not evidence about this call site. Counted rather
            // than filtered, so the report can say whether it ever happened.
            if detect(&m).is_some() {
                c.market_split += 1;
                continue;
            }
            if reformulate_kernel(&m).is_none() {
                continue;
            }
            c.admitted += 1;
            let (brute, feasible) = brute_force_optimum(&m);
            let opts = SolveOpts::new().with_time_limit(Duration::from_secs(30));
            match crate::bab::solve_milp(&m, &opts) {
                Outcome::Optimal {
                    value,
                    model_values,
                    ..
                } => {
                    let witness_ok = m.check_point(&model_values).is_ok()
                        && m.objective_value_at(&model_values) == value;
                    if !witness_ok || brute.as_ref() != Some(&value) {
                        c.disagreements.push(seed);
                    }
                }
                Outcome::Infeasible { tree_cert, .. } => {
                    c.infeasible += 1;
                    if feasible != 0 {
                        c.disagreements.push(seed);
                    }
                    // THE HARVEST, judged by the real verifier. The reduced tree is
                    // not a statement about this model, so what must come back is
                    // the CALLER-frame tree the re-solve captured — or nothing.
                    if let Some(t) = tree_cert {
                        if t.verify(&m).is_ok() {
                            c.verified_certs += 1;
                        } else {
                            c.disagreements.push(seed);
                        }
                    }
                }
                other => c.disagreements.push(seed_of_unexpected(seed, &other)),
            }
        }
        c
    }

    /// A non-`Optimal`/`Infeasible` verdict on a fully-boxed 3-to-6 column model
    /// is itself a failure; funnel it into the disagreement list with its verdict
    /// printed rather than panicking mid-campaign, so one bad seed does not hide
    /// the other 2,000 results.
    fn seed_of_unexpected(seed: u64, outcome: &Outcome) -> u64 {
        println!("seed {seed}: unexpected verdict {outcome:?}");
        seed
    }

    /// ⚠ **THE CAMPAIGN THAT GUARDS THE NEWLY-REACHABLE LANE.**
    ///
    /// Root reductions used to be gated on `opts.tree_cert_leaves == 0`, a field
    /// that defaults to 256 — so the kernel reformulation was unreachable on
    /// default options and had almost no production exposure. Decoupling the two
    /// makes it reachable for the first time, and the last time this lane's gate
    /// was widened it shipped a SILENT WRONG ANSWER: `OPTIMAL` at a
    /// worse-than-true optimum (fz135 −10 for a true −9, fz2169 20 for 15),
    /// through 433 lib tests and a 40-instance corpus run. What caught it was a
    /// random-model campaign, and nothing else did.
    ///
    /// So the full 2,600-seed campaign runs here, against the shape production
    /// now really admits, through the public entry, on default options. Keeping
    /// the complete campaign active prevents the soundness evidence from
    /// silently becoming an ignored test that normal verification never runs.
    ///
    /// The firing rate is asserted, not assumed. A campaign whose generator never
    /// reaches the reformulation proves nothing, and that failure mode is silent.
    #[test]
    fn randomised_isolated_shape_matches_brute_force() {
        let _env = solve_lock();
        let c = isolated_shape_campaign(0..2_600);
        println!(
            "isolated-shape campaign: {} generated, {} admitted by the shipped gate, \
             {} claimed by market-split, {} infeasible, {} verifying tree certificates, \
             {} disagreements",
            c.generated,
            c.admitted,
            c.market_split,
            c.infeasible,
            c.verified_certs,
            c.disagreements.len()
        );
        assert!(
            c.admitted >= 2_000,
            "the generator must actually reach the reformulation at scale; admitted={}",
            c.admitted
        );
        assert!(
            c.infeasible >= 20,
            "the infeasible half must actually be infeasible, or the harvest is untested; \
             infeasible={}",
            c.infeasible
        );
        // NON-VACUITY OF THE HARVEST. A reduced-frame tree is never lifted for the
        // kernel (there is no `KernelPostsolve::lift_tree_cert`), so every
        // certificate counted here was bought by `bab::harvest_tree_cert_by_resolve`
        // re-solving the caller's own model, and every one was checked by the real
        // whole-tree verifier against that model. Zero here would mean the campaign
        // is silently testing verdicts only.
        assert!(
            c.verified_certs > 0,
            "no infeasible verdict carried a verifying tree certificate — the harvest \
             is not being exercised"
        );
        assert!(
            c.disagreements.is_empty(),
            "the shipped kernel path disagrees with brute force on seeds {:?}",
            c.disagreements
        );
    }

    /// THE OTHER HALF OF THE ADMITTED SET: a random model of the **`ej` family**,
    /// where applicability comes from an INFINITE column side rather than from
    /// coefficients outgrowing the box.
    ///
    /// The two halves are not the same test. `reformulate_kernel_inner`'s
    /// applicability check is a disjunction — `any_infinite_side ||
    /// coefficients_outgrow_the_box` — and the branches build DIFFERENT reduced
    /// models: an infinite side contributes NO bound row, which is what leaves the
    /// new `z` columns free, and free `z` is the property the whole reformulation
    /// rests on. A campaign over boxed models never builds one.
    ///
    /// Every equality coefficient is POSITIVE and every `C` column is `x >= 0`, so
    /// `a·x = b` with `b >= 0` implies `x_j <= b / a_j`: the model is unbounded as
    /// DECLARED (which is what the gate reads) and finite in truth, so a ground
    /// truth exists. The objective is nonnegative under Minimize for the same
    /// reason — it must be bounded below for `Optimal` to be the right verdict.
    fn random_unbounded_model(seed: u64) -> (Model, Vec<Col>, Vec<i64>, i64) {
        let mut r = SplitMix(seed);
        let mut m = Model::new();
        let c_cols: Vec<Col> = (0..3).map(|_| m.add_int_col(0.0, f64::INFINITY)).collect();
        let s_cols: Vec<Col> = (0..2).map(|_| m.add_int_col(0.0, 2.0)).collect();
        let coeffs: Vec<i64> = (0..3).map(|_| r.range(7, 60)).collect();
        let pt: Vec<i64> = (0..3).map(|_| r.range(0, 2)).collect();
        let rhs: i64 = coeffs.iter().zip(&pt).map(|(a, p)| a * p).sum();
        let terms: Vec<(Col, f64)> = c_cols
            .iter()
            .zip(&coeffs)
            .map(|(&c, &a)| (c, a as f64))
            .collect();
        m.add_row(rhs as f64, rhs as f64, &terms);
        // Isolated surviving row, over `s_cols` only.
        let s_pt: Vec<i64> = (0..2).map(|_| r.range(0, 2)).collect();
        let sterms: Vec<(Col, f64)> = s_cols.iter().map(|&c| (c, r.nonzero(9) as f64)).collect();
        let base: i64 = sterms
            .iter()
            .zip(&s_pt)
            .map(|((_, a), p)| *a as i64 * p)
            .sum();
        m.add_row(f64::NEG_INFINITY, (base + r.range(0, 5)) as f64, &sterms);
        // Nonnegative costs on `C` under Minimize: the objective must be bounded
        // below or `Optimal` is not the right verdict and the comparison is void.
        let mut obj: Vec<(Col, f64)> = c_cols.iter().map(|&c| (c, r.range(0, 20) as f64)).collect();
        obj.extend(s_cols.iter().map(|&c| (c, r.range(-20, 20) as f64)));
        m.set_objective(&obj, Sense::Minimize);
        (m, c_cols, coeffs, rhs)
    }

    /// The ground truth for [`random_unbounded_model`]: enumerate the equality's
    /// solutions directly (two free coordinates, the third forced) rather than a
    /// box the model does not declare, and take the best objective over the
    /// surviving rows' own small box.
    fn unbounded_family_optimum(
        m: &Model,
        c_cols: &[Col],
        coeffs: &[i64],
        rhs: i64,
    ) -> Option<BigRational> {
        let mut best: Option<BigRational> = None;
        let n = m.num_cols();
        // The generator lays the three `C` columns down first and the two
        // surviving ones after, so 3 and 4 below are the `s` columns. Pinned
        // rather than assumed.
        assert_eq!(n, 5, "random_unbounded_model builds exactly 3 + 2 columns");
        let mut x0 = 0i64;
        while coeffs[0] * x0 <= rhs {
            let mut x1 = 0i64;
            while coeffs[0] * x0 + coeffs[1] * x1 <= rhs {
                let rem = rhs - coeffs[0] * x0 - coeffs[1] * x1;
                if rem % coeffs[2] == 0 {
                    let x2 = rem / coeffs[2];
                    // The two `s` columns, whole box.
                    for s0 in 0..=2i64 {
                        for s1 in 0..=2i64 {
                            let mut pt = vec![BigRational::zero(); n];
                            pt[c_cols[0].index()] = int(x0);
                            pt[c_cols[1].index()] = int(x1);
                            pt[c_cols[2].index()] = int(x2);
                            pt[3] = int(s0);
                            pt[4] = int(s1);
                            if m.check_point(&pt).is_ok() {
                                let v = m.objective_value_at(&pt);
                                if best.as_ref().is_none_or(|b| v < *b) {
                                    best = Some(v);
                                }
                            }
                        }
                    }
                }
                x1 += 1;
            }
            x0 += 1;
        }
        best
    }

    /// ⚠ **THE SAME CAMPAIGN OVER THE `ej` FAMILY** — declared-unbounded columns,
    /// free `z`, no bound rows. This is the sub-shape with the least production
    /// exposure of anything in the engine, and it is the one the decoupling turns
    /// on by default.
    #[test]
    fn randomised_unbounded_family_matches_enumeration() {
        let _env = solve_lock();
        let mut admitted = 0usize;
        let mut disagreements: Vec<u64> = Vec::new();
        for seed in 0..600u64 {
            let (m, c_cols, coeffs, rhs) = random_unbounded_model(seed);
            if detect(&m).is_some() || reformulate_kernel(&m).is_none() {
                continue;
            }
            admitted += 1;
            let truth = unbounded_family_optimum(&m, &c_cols, &coeffs, rhs);
            let opts = SolveOpts::new().with_time_limit(Duration::from_secs(30));
            match crate::bab::solve_milp(&m, &opts) {
                Outcome::Optimal {
                    value,
                    model_values,
                    ..
                } => {
                    let witness_ok = m.check_point(&model_values).is_ok()
                        && m.objective_value_at(&model_values) == value;
                    if !witness_ok || truth.as_ref() != Some(&value) {
                        disagreements.push(seed);
                    }
                }
                Outcome::Infeasible { .. } => {
                    if truth.is_some() {
                        disagreements.push(seed);
                    }
                }
                other => {
                    println!("seed {seed}: unexpected verdict {other:?}");
                    disagreements.push(seed);
                }
            }
        }
        println!(
            "unbounded-family campaign: {admitted} admitted, {} disagreements",
            disagreements.len()
        );
        assert!(
            admitted >= 400,
            "the generator must reach the reformulation; admitted={admitted}"
        );
        assert!(
            disagreements.is_empty(),
            "the shipped kernel path disagrees with enumeration on seeds {disagreements:?}"
        );
    }

    /// **THE NEGATIVE CONTROL, AND THE POINT OF THE WHOLE SOUNDNESS SECTION.**
    ///
    /// A DOUBLED basis `{2·b₁, b₂, …}` consists entirely of genuine kernel
    /// vectors, so it passes S1(a) — and it spans an INDEX-2 SUBLATTICE, which
    /// would silently delete half the feasible integer points and let the solver
    /// report a value strictly worse than the true optimum while claiming
    /// OPTIMAL. The exact covolume check S1(b) is what refuses it. Disable that
    /// check and this test fails; that has been verified by actually removing it.
    #[test]
    fn a_doubled_basis_spanning_an_index_two_sublattice_is_declined() {
        // ker[2, 3, 5] over ℤ³ — dimension 2.
        let a = vec![vec![BigInt::from(2), BigInt::from(3), BigInt::from(5)]];
        let (u, rank, mm) = col_hnf(&a, 1, 3, deadline()).expect("hnf");
        assert_eq!(rank, 1);
        assert!(hnf_kernel_invariant_holds(&a, &u, &mm, rank, 3, deadline()));
        let k0: Vec<Vec<BigInt>> = (0..2)
            .map(|t| (0..3).map(|i| u[i][rank + t].clone()).collect())
            .collect();

        // The honest reduction is accepted.
        let good = lll(k0.clone(), deadline()).expect("lll");
        assert!(
            kernel_basis_is_same_lattice(&a, &k0, &good, 3, deadline()),
            "an LLL reduction of the kernel basis must be accepted"
        );

        // The doubled basis is in the kernel, and is REJECTED.
        let mut doubled = good.clone();
        for v in &mut doubled[0] {
            *v *= 2;
        }
        for row in &a {
            let dot: BigInt = row.iter().zip(&doubled[0]).map(|(ai, vi)| ai * vi).sum();
            assert!(
                dot.is_zero(),
                "the doubled vector really is a kernel vector"
            );
        }
        assert!(
            !kernel_basis_is_same_lattice(&a, &k0, &doubled, 3, deadline()),
            "a doubled basis spans an index-2 sublattice and MUST be declined"
        );
        // The covolume is what separates them, by a factor of exactly 4 = 2².
        let g_ref = gram_det(&k0, deadline()).expect("gram");
        let g_bad = gram_det(&doubled, deadline()).expect("gram");
        assert_eq!(g_bad, g_ref * BigInt::from(4));
    }

    /// A model with no qualifying equality row is not this device's business.
    /// Three shapes that each fail a different clause: an inequality-only model,
    /// an equality over a CONTINUOUS column, and an equality whose columns are
    /// also touched by another row.
    #[test]
    fn models_without_a_qualifying_equality_are_declined() {
        // (1) inequality only.
        let mut m = Model::new();
        let x = m.add_int_col(0.0, f64::INFINITY);
        let y = m.add_int_col(0.0, f64::INFINITY);
        m.add_row(f64::NEG_INFINITY, 7.0, &[(x, 31013.0), (y, -41014.0)]);
        m.set_objective(&[(x, 1.0)], Sense::Minimize);
        assert!(reformulate_kernel(&m).is_none());

        // (2) the equality's support includes a continuous column.
        let mut m = Model::new();
        let x = m.add_int_col(0.0, f64::INFINITY);
        let s = m.add_col(0.0, f64::INFINITY);
        m.add_row(0.0, 0.0, &[(x, 31013.0), (s, -41014.0)]);
        m.set_objective(&[(x, 1.0)], Sense::Minimize);
        assert!(reformulate_kernel(&m).is_none());

        // (3) a column of C is touched by a row outside E.
        let mut m = Model::new();
        let x = m.add_int_col(0.0, f64::INFINITY);
        let y = m.add_int_col(0.0, f64::INFINITY);
        m.add_row(0.0, 0.0, &[(x, 31013.0), (y, -41014.0)]);
        m.add_row(f64::NEG_INFINITY, 100.0, &[(x, 1.0)]);
        m.set_objective(&[(x, 1.0)], Sense::Minimize);
        assert!(reformulate_kernel(&m).is_none());

        // (4) the box already bounds the equalities: nothing to re-coordinate.
        let mut m = Model::new();
        let x = m.add_int_col(0.0, 40.0);
        let y = m.add_int_col(0.0, 40.0);
        m.add_row(0.0, 0.0, &[(x, 3.0), (y, -5.0)]);
        m.set_objective(&[(x, 1.0)], Sense::Minimize);
        assert!(reformulate_kernel(&m).is_none());
    }

    /// A model whose true coefficients are rounded `f64` proxies is declined
    /// wholesale — the same fail-closed rule `presolve.rs:87` and `detect` apply.
    /// Reasoning over the public `f64` matrix here would be reasoning over a
    /// DIFFERENT model, and the reformulation's whole value is that it is exact.
    #[test]
    fn inexact_coefficient_models_are_declined() {
        use num_traits::ToPrimitive;
        let mut m = ej_model();
        assert!(
            reformulate_kernel(&m).is_some(),
            "control: the exact model does fire"
        );
        // 2^53 + 1 is not an f64; recording it marks the model inexact.
        let truth = BigRational::from(BigInt::from((1u64 << 53) + 1));
        let rounded = truth.to_f64().expect("finite");
        let row = m.row_at(0).expect("one row");
        m.set_row(
            row,
            0.0,
            0.0,
            &[(Col(0), rounded), (Col(1), -41014.0), (Col(2), -51015.0)],
        );
        m.record_inexact_row_coeff(row, 0, truth);
        assert!(m.has_inexact_coeffs());
        assert!(reformulate_kernel(&m).is_none());
    }

    /// The kill switch has to work, and the postsolve's objective constant must
    /// never travel through an `f64`: `const_delta` is exact by construction here
    /// even when the fold is a large integer.
    #[test]
    fn kill_switch_and_exact_objective_constant() {
        let m = ej_model();
        // `ej`'s particular solution is x_p = 0, so its const_delta is 0; the
        // interesting case is a shifted rhs, where the fold is nonzero.
        let (_, post) = reformulate_kernel(&m).expect("fires");
        assert_eq!(*post.const_delta(), BigRational::zero());
        assert!(post.const_delta().is_integer());

        let mut shifted = Model::new();
        let x0 = shifted.add_int_col(1.0, f64::INFINITY);
        let x1 = shifted.add_int_col(0.0, f64::INFINITY);
        let x2 = shifted.add_int_col(0.0, f64::INFINITY);
        shifted.add_row(1.0, 1.0, &[(x0, 31013.0), (x1, -41014.0), (x2, -51015.0)]);
        shifted.set_objective(&[(x0, 1.0)], Sense::Minimize);
        let (_, post) = reformulate_kernel(&shifted).expect("fires");
        // Whatever x_p is, widening z = 0 must reproduce it and satisfy the row.
        let at_zero = post.widen(&[BigRational::zero(), BigRational::zero()]);
        let act = &at_zero[0] * int(31013) - &at_zero[1] * int(41014) - &at_zero[2] * int(51015);
        assert_eq!(act, int(1));
        assert_eq!(*post.const_delta(), at_zero[0]);

        temp_env_var("AY_MILP_NO_KERNEL_REFORM", "1", || {
            assert!(reformulate_kernel(&ej_model()).is_none());
        });
    }

    /// Set an environment variable for the duration of `f`. Tests in this module
    /// that need it are serialized by taking one lock, because the environment is
    /// process-wide and the rest of the suite runs in parallel.
    fn temp_env_var(key: &str, value: &str, f: impl FnOnce()) {
        static LOCK: Mutex<()> = Mutex::new(());
        let _guard = LOCK.lock().unwrap_or_else(|e| e.into_inner());
        // SAFETY: the lock serializes this module's mutations, and no other test
        // in the crate reads this key.
        unsafe { std::env::set_var(key, value) };
        let out = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
        unsafe { std::env::remove_var(key) };
        if let Err(p) = out {
            std::panic::resume_unwind(p);
        }
    }
}

#[cfg(test)]
mod kernel_reform_corpus_scan {
    use super::*;

    /// HOW OFTEN THE GATE FIRES ON REAL MODELS — the measurement that decides
    /// whether [`reformulate_kernel`] may run by default.
    ///
    /// Synthetic gains do not transfer; a structural gate is only as good as the
    /// corpus census behind it. Point `AY_MILP_KERNEL_SCAN_DIR` at a directory of
    /// `.mps` / `.mps.gz` files (MIPLIB 2017 lives in `ay-bench/milp/instances`)
    /// and this reports, per instance, whether the reformulation fires and what
    /// it does to the model's shape. Unset — which is every ordinary test run —
    /// it does nothing at all.
    ///
    /// ```text
    /// AY_MILP_KERNEL_SCAN_DIR=$HOME/ay-bench/milp/instances \
    ///   cargo test --release -p ay-milp --lib kernel_reform_corpus_scan -- --nocapture
    /// ```
    #[test]
    fn kernel_reformulation_corpus_census() {
        let Some(dir) = std::env::var_os("AY_MILP_KERNEL_SCAN_DIR") else {
            return;
        };
        let mut files: Vec<std::path::PathBuf> = std::fs::read_dir(&dir)
            .expect("scan dir")
            .filter_map(|e| e.ok().map(|e| e.path()))
            .filter(|p| {
                let s = p.to_string_lossy();
                s.ends_with(".mps") || s.ends_with(".mps.gz")
            })
            .collect();
        files.sort();
        let (mut fired, mut seen, mut parse_fail) = (0usize, 0usize, 0usize);
        for path in &files {
            let text = if path.extension() == Some(OsStr::new("gz")) {
                let out = std::process::Command::new("gzip")
                    .arg("-dc")
                    .arg(path)
                    .output()
                    .expect("gzip");
                String::from_utf8_lossy(&out.stdout).into_owned()
            } else {
                std::fs::read_to_string(path).expect("read")
            };
            let Ok(p) = crate::mps::read_mps(&text) else {
                parse_fail += 1;
                continue;
            };
            seen += 1;
            let t0 = Instant::now();
            if let Some((reduced, _)) = reformulate_kernel(&p.model) {
                fired += 1;
                println!(
                    "KERNEL_REFORM_FIRES {} {}r/{}c -> {}r/{}c ({:.3}s)",
                    p.name,
                    p.model.num_rows(),
                    p.model.num_cols(),
                    reduced.num_rows(),
                    reduced.num_cols(),
                    t0.elapsed().as_secs_f64(),
                );
            }
        }
        println!(
            "KERNEL_REFORM_CENSUS fired={fired} of {seen} parsed ({parse_fail} unparsed) in {}",
            std::path::Path::new(&dir).display()
        );
    }
}
