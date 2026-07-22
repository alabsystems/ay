// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared NuPBO-class incremental scorer for pseudo-Boolean local search.
//!
//! This module is the reusable scoring substrate underneath the unified
//! local-search primal in [`crate::optimize::sls`]. It operates directly on the
//! REAL [`PbConstraint`] / [`PbObjective`] / `PbTerm` / `PbLit` types (linear
//! rows only) and maintains, *incrementally* and in `O(touched)` per flip:
//!
//! * the exact left-hand side of every hard constraint (so feasibility is
//!   tracked exactly), and the incrementally-maintained set of violated rows;
//! * the exact `i128` objective value of the current assignment;
//! * a NuPBO-style two-stream score per variable — a **hard** score `hscore`
//!   (gradient of weighted hard-violation reduction, degree/coefficient
//!   normalized) and a **soft/objective** score `sscore` (objective-reduction
//!   gradient, normalized by the average objective coefficient and scaled by an
//!   adaptive objective-pressure weight `s_weight`);
//! * a `goodvar` stack: the set of variables whose combined score
//!   `hscore + sscore > 0` (i.e. flipping strictly improves the unified
//!   objective-as-soft cost), maintained with O(1) membership updates so the
//!   search can pick an improving move without rescanning all variables.
//!
//! ## Performance contract (design §3.1 / §4)
//! 1. **i64 fast path with an exact per-instance overflow flag.** All
//!    constraint-side arithmetic (LHS, RHS, per-flip deltas, shortfalls) is
//!    generic over [`ScoreInt`] (`i64` or `i128`). At construction, every row
//!    is checked with exact (checked/saturating `i128`) arithmetic: when
//!    `Σ|coeff| + |rhs|` provably fits `i64` for every row, the `i64` core is
//!    used — halving the memory traffic of the hot per-flip loops and removing
//!    every 128-bit saturating operation from them. Otherwise the exact `i128`
//!    core runs. Both cores compute IDENTICAL values (everything the `i64`
//!    core touches provably fits `i64`, so no saturation point differs), hence
//!    bit-identical trajectories — differentially tested for both widths.
//!    Cross-row aggregates and the objective stay `i128` on both paths.
//! 2. **Bucketed dirty-set best-move selection** ([`MoveSelector::Bucketed`]):
//!    a ~[`NUM_BUCKETS`]-bucket gain-quantized argmax with epoch/stamp/touched
//!    bookkeeping (the [`crate::cp_dense`] idiom) so selection costs
//!    `O(touched)` per flip and per-selection clears are epoch bumps — no
//!    reallocation. The quantized global maximum always lives in the highest
//!    non-empty bucket, so selection quality is at least that of the
//!    Best-from-Multiple-Selections sample over the whole goodvar stack
//!    ([`MoveSelector::Bms`], the historical pick, which stays selectable).
//!    Ships DEFAULT-OFF: the flip-rate microbenchmark did not clear the
//!    at-least-matches-BMS bar (see [`MoveSelector`] for the numbers).
//!
//! ## NuPBO levers implemented here
//! 1. **Objective-as-soft unified cost.** `hscore` and `sscore` are summed into a
//!    single combined score; an improving move may *increase* hard violation if
//!    it reduces the objective enough (and vice versa). The search can therefore
//!    move through mildly-infeasible regions toward a better optimum — it is NOT
//!    restricted to feasibility-preserving flips.
//! 2. **Incremental make/break scoring + goodvar stack + BMS/bucketed pick.** A
//!    flip touches only the constraints the variable occurs in and their member
//!    variables; only those scores are updated. Move selection samples the
//!    goodvar stack (BMS) or reads the top gain bucket (bucketed) — never an
//!    `O(vars)` rescan.
//! 3. **Degree/coefficient-normalized scoring.** Each constraint's contribution to
//!    `hscore` is divided by its average coefficient (`inv_avg_coeff`), and the
//!    objective gradient by the average objective coefficient, so large
//!    coefficients do not swamp the gradient.
//! 4. **Two-stream adaptive weights.** Hard rows carry PAWS-style integer weights
//!    bumped on plateaus; the objective pressure λ (`s_weight`) is **hard-locked
//!    at 0 until the search first reaches feasibility** (a pure feasibility hunt
//!    — design §2.1), then initialized to [`LAMBDA_INIT`] and adapted
//!    *multiplicatively* within `[LAMBDA_MIN, LAMBDA_MAX]`: raised when dwelling
//!    feasible with no objective gain, lowered when the search keeps leaving the
//!    feasible region — an adaptive-lambda ridge-crossing schedule.
//!
//! ## Soundness
//! This module is **advisory only**. It never decides what is reported; it merely
//! steers the search. The maintained `lhs`/`obj_value` are exact (and
//! differentially tested against from-scratch oracles on BOTH integer widths),
//! but even a bug in them could only degrade search quality: every incumbent the
//! search wants to emit is independently re-verified by
//! [`crate::eval::verify_all_constraints`] plus an exact
//! [`crate::solver::eval_objective`] recompute before it is reported. This
//! module NEVER claims OPTIMUM or UNSAT. The `i64` core is additionally
//! fail-closed: its constructor re-checks every row bound and every narrowing,
//! so even a dispatch bug degrades to the exact `i128` core (or a decline),
//! never to wrapped arithmetic.

use crate::optimize::lns::SplitMix64;
use crate::types::{PbConstraint, PbObjective, PbRel};

/// Maximum total constraint occurrences (sum of row sizes) the inverse index will
/// build. Mirrors the SLS occurrence cap so the scorer declines on the very large
/// families rather than blowing up memory.
const MAX_SCORE_OCCURRENCES: usize = 8_000_000;

/// A variable's combined score must exceed this to count as "good" (improving).
/// A tiny positive epsilon avoids treating float round-off as an improvement.
const GOOD_EPS: f64 = 1e-9;

/// PAWS additive bump applied to each violated hard row's integer weight on a
/// plateau.
const H_INC: i128 = 1;

/// Objective-pressure weight λ assigned the moment the hard lock releases — the
/// search's FIRST feasible assignment (design §2.1). A feasible warm start (the
/// polish path) releases the lock at construction, i.e. at step 0, so a
/// warm-started run never degrades to a feasibility-only search. Until that
/// first feasible point, λ is HARD-LOCKED at exactly 0 (pure feasibility hunt).
pub(crate) const LAMBDA_INIT: f64 = 1.0;

/// Multiplicative raise factor applied to λ when the search is DWELLING FEASIBLE
/// with no objective gain (stuck at a feasible local optimum): objective pressure
/// escalates so the search will cross a mildly-infeasible ridge into a cheaper
/// basin. Together with [`LAMBDA_DECAY`] this IS the clamped change rate: one
/// stuck event changes λ by at most ×1.25 (and never past [`LAMBDA_MAX`]).
const LAMBDA_RAISE: f64 = 1.25;

/// Multiplicative decay factor applied to λ when the search KEEPS LEAVING the
/// feasible region (stuck while infeasible): the hard streams regain priority and
/// the search is pulled back across the feasibility ridge. One stuck event
/// changes λ by at most ×0.8 (and never below [`LAMBDA_MIN`]).
const LAMBDA_DECAY: f64 = 0.8;

/// Bounds on the UNLOCKED objective-pressure weight λ so it can neither vanish
/// (losing the ridge-crossing pull) nor explode (drowning the hard streams). The
/// hard-locked value 0 (before the first feasible assignment) is the one
/// deliberate exception below `LAMBDA_MIN`.
const LAMBDA_MIN: f64 = 0.0625;
const LAMBDA_MAX: f64 = 1_048_576.0;

// ---------------------------------------------------------------------------
// ScoreInt: the exact-overflow-flagged scalar of the hot per-flip arithmetic
// ---------------------------------------------------------------------------

/// The integer scalar of the per-row constraint arithmetic (design §3.1: "i64
/// fast path with an exact per-instance i128 overflow flag"). Implemented for
/// `i64` (the fast path) and `i128` (the exact fallback).
///
/// # Exactness contract
/// A row may be tracked in `Self` only when [`ScoreInt::row_fits`] holds for
/// it: `Σ|coeff| + |rhs|` (computed in exact `i128`) is representable. Under
/// that bound every value this scalar ever holds for the row — any reachable
/// LHS (`|lhs| ≤ Σ|coeff|`), any shortfall (`≤ Σ|coeff| + |rhs|`), any
/// single-term delta — is exactly representable and no saturating operation
/// ever actually saturates, so the `i64` and `i128` cores compute IDENTICAL
/// numbers (and therefore identical search trajectories). Cross-row aggregates
/// are always accumulated in `i128` by the callers (widening via
/// [`ScoreInt::to_i128`] is exact and, for 64-bit products, cheap).
pub(crate) trait ScoreInt: Copy + Ord + std::fmt::Debug + 'static {
    const ZERO: Self;
    const ONE: Self;

    /// Exact widening view (infallible) for cross-row `i128` aggregates.
    fn to_i128(self) -> i128;

    /// Checked narrowing used at construction time only. `None` = fail-closed
    /// decline (the caller falls back to the wider core or declines outright);
    /// narrowing NEVER wraps.
    fn from_i128(v: i128) -> Option<Self>;

    /// The per-row exact overflow flag: whether a row with `Σ|coeff| =
    /// coeff_abs_sum` (exact `i128`, saturating accumulation — a saturated sum
    /// simply fails the bound) and right-hand side `rhs` provably keeps every
    /// LHS / shortfall / per-flip delta representable in `Self`. The `i128`
    /// implementation is unconditionally `true`, preserving the historical
    /// saturating semantics of the wide path bit-for-bit.
    fn row_fits(coeff_abs_sum: i128, rhs: i128) -> bool;

    fn saturating_add(self, rhs: Self) -> Self;
    fn saturating_sub(self, rhs: Self) -> Self;
    fn saturating_neg(self) -> Self;

    /// `self / 2` rounding toward zero (the DDFW transfer divisor — kept as a
    /// trait method so the generic tracker needs no `Div` bound).
    fn div2(self) -> Self;

    /// Shortfall (non-negative distance from satisfaction) for a relation.
    /// `Ge`: `max(0, rhs - lhs)`. `Eq`: `|lhs - rhs|`. Saturating, so it can
    /// never panic on pathological coefficients. The `i128` implementation is
    /// the LITERAL [`crate::optimize::sls::shortfall_for`] — the function
    /// carrying the machine-checked `ret >= 0` deductive_checks contract — so the wide
    /// path runs exactly the proven code; the `i64` implementation is the same
    /// formula on `i64` (structurally identical, covered by the differential
    /// fuzz on both widths).
    fn shortfall(rel: PbRel, lhs: Self, rhs: Self) -> Self;

    /// Exact conversion to `f64` for score gradients. Both widths convert the
    /// same numeric value to the same `f64`, keeping trajectories identical.
    fn to_f64(self) -> f64;
}

impl ScoreInt for i64 {
    const ZERO: Self = 0;
    const ONE: Self = 1;

    #[inline]
    fn to_i128(self) -> i128 {
        self as i128
    }

    #[inline]
    fn from_i128(v: i128) -> Option<Self> {
        i64::try_from(v).ok()
    }

    #[inline]
    fn row_fits(coeff_abs_sum: i128, rhs: i128) -> bool {
        // Exact i128 arithmetic: |rhs| of i128::MIN has no i128 abs, so
        // checked_abs -> None -> fail closed (the row goes to the i128 core).
        rhs.checked_abs()
            .and_then(|abs_rhs| coeff_abs_sum.checked_add(abs_rhs))
            .is_some_and(|total| total <= i64::MAX as i128)
    }

    #[inline]
    fn saturating_add(self, rhs: Self) -> Self {
        i64::saturating_add(self, rhs)
    }
    #[inline]
    fn saturating_sub(self, rhs: Self) -> Self {
        i64::saturating_sub(self, rhs)
    }
    #[inline]
    fn saturating_neg(self) -> Self {
        i64::saturating_neg(self)
    }
    #[inline]
    fn div2(self) -> Self {
        self / 2
    }

    #[inline]
    fn shortfall(rel: PbRel, lhs: Self, rhs: Self) -> Self {
        // Same formula as `sls::shortfall_for`, on i64 (see trait docs).
        match rel {
            PbRel::Ge => (rhs.saturating_sub(lhs)).max(0),
            PbRel::Eq => lhs.saturating_sub(rhs).saturating_abs(),
        }
    }

    #[inline]
    fn to_f64(self) -> f64 {
        self as f64
    }
}

impl ScoreInt for i128 {
    const ZERO: Self = 0;
    const ONE: Self = 1;

    #[inline]
    fn to_i128(self) -> i128 {
        self
    }

    #[inline]
    fn from_i128(v: i128) -> Option<Self> {
        Some(v)
    }

    #[inline]
    fn row_fits(_coeff_abs_sum: i128, _rhs: i128) -> bool {
        true // the exact wide path accepts every row (historical semantics)
    }

    #[inline]
    fn saturating_add(self, rhs: Self) -> Self {
        i128::saturating_add(self, rhs)
    }
    #[inline]
    fn saturating_sub(self, rhs: Self) -> Self {
        i128::saturating_sub(self, rhs)
    }
    #[inline]
    fn saturating_neg(self) -> Self {
        i128::saturating_neg(self)
    }
    #[inline]
    fn div2(self) -> Self {
        self / 2
    }

    #[inline]
    fn shortfall(rel: PbRel, lhs: Self, rhs: Self) -> Self {
        // The LITERAL contract-carrying function (see trait docs).
        crate::optimize::sls::shortfall_for(rel, lhs, rhs)
    }

    #[inline]
    fn to_f64(self) -> f64 {
        self as f64
    }
}

/// The per-instance exact overflow flag (design §3.1): whether EVERY row's
/// `Σ|coeff| + |rhs|` provably fits `T`, computed with exact `i128` arithmetic
/// (saturating |coeff| accumulation — a saturated sum fails the `i64` bound and
/// is accepted by the unconditional `i128` bound, both correct). This is the
/// SAME per-row predicate the generic cores re-check at construction, so
/// dispatch and construction can never disagree.
pub(crate) fn rows_fit<T: ScoreInt>(constraints: &[PbConstraint]) -> bool {
    constraints.iter().all(|c| {
        let mut coeff_abs_sum: i128 = 0;
        for term in &c.terms {
            coeff_abs_sum = coeff_abs_sum.saturating_add(term.coeff.saturating_abs());
        }
        T::row_fits(coeff_abs_sum, c.rhs)
    })
}

// ---------------------------------------------------------------------------
// Bucketed dirty-set best-move selector (design §4: O(touched) argmax)
// ---------------------------------------------------------------------------

/// Number of gain buckets for the dirty-set best-move selector (design §4:
/// "best-move argmax O(touched) — ~256-bucket dirty-set via cp_dense
/// epoch/stamp").
const NUM_BUCKETS: usize = 256;

/// Sentinel bucket id: the variable is currently in no bucket (its combined
/// score is not improving).
const NO_BUCKET: u16 = u16::MAX;

/// Maps a positive combined score to its gain bucket at half-exponent (×√2)
/// granularity: bucket `≈ 2·log2(score) + 128`, clamped to `0..NUM_BUCKETS`.
/// Pure bit arithmetic on the IEEE-754 representation (positive f64 bit
/// patterns are monotone in the value), so the mapping is monotone,
/// branch-free, and deterministic across platforms. Scores in `(2⁻⁶⁴, 2⁶⁴)`
/// resolve to distinct half-exponent buckets; anything outside clamps.
#[inline]
fn bucket_of(score: f64) -> u16 {
    debug_assert!(score > 0.0 && score.is_finite());
    let bits = score.to_bits();
    let expo = ((bits >> 52) & 0x7FF) as i64 - 1023; // unbiased binary exponent
    let half = ((bits >> 51) & 1) as i64; // top mantissa bit: upper half-octave
    (expo * 2 + half + 128).clamp(0, (NUM_BUCKETS - 1) as i64) as u16
}

/// The bucketed dirty-set argmax (design §4). Score changes are recorded in a
/// dirty set with the [`crate::cp_dense`] epoch/stamp/touched idiom (O(1)
/// mark, O(touched) flush, clear = epoch bump with NO reallocation); at
/// selection time the pending changes are flushed into ~[`NUM_BUCKETS`]
/// score-quantized buckets (O(1) swap-remove membership, like the violated
/// set) and the pick reads the highest non-empty bucket, which — because the
/// bucket mapping is monotone — always contains the true argmax of the
/// combined score, up to the ×√2 quantization within the bucket.
struct BucketSelector {
    /// Bucket id per variable, or [`NO_BUCKET`] when not an improving move.
    var_bucket: Vec<u16>,
    /// Position of the variable inside its bucket's member list.
    var_pos: Vec<u32>,
    /// Member lists, one per bucket. Never shrunk: swap-remove keeps capacity,
    /// so steady-state operation allocates nothing.
    buckets: Vec<Vec<u32>>,
    /// Upper bound on the highest non-empty bucket; raised on insert, repaired
    /// downward lazily at selection (amortized O(1) + a ≤ NUM_BUCKETS walk).
    max_bucket: usize,
    /// Dirty-set stamps: `dirty_stamp[v] == epoch` iff `v` is queued in
    /// `dirty` (the cp_dense O(1)-membership scheme).
    dirty_stamp: Vec<u32>,
    /// Queued variables whose bucket membership may be stale (the cp_dense
    /// `touched` list): flushing walks exactly these, O(touched).
    dirty: Vec<u32>,
    /// Current dirty-set epoch; bumped on every flush so the clear is O(1)
    /// bookkeeping + O(touched) list truncation — no reallocation, ever.
    epoch: u32,
}

impl BucketSelector {
    fn new(num_vars: usize) -> Self {
        BucketSelector {
            var_bucket: vec![NO_BUCKET; num_vars],
            var_pos: vec![0; num_vars],
            buckets: vec![Vec::new(); NUM_BUCKETS],
            max_bucket: 0,
            dirty_stamp: vec![0; num_vars],
            dirty: Vec::new(),
            epoch: 1,
        }
    }

    /// Queues `v` for a bucket-membership refresh at the next flush. O(1);
    /// idempotent within an epoch (the stamp dedups).
    #[inline]
    fn mark_dirty(&mut self, v: usize) {
        if self.dirty_stamp[v] != self.epoch {
            self.dirty_stamp[v] = self.epoch;
            self.dirty.push(v as u32);
        }
    }

    /// Moves `v` into `new_bucket` ([`NO_BUCKET`] = remove), maintaining the
    /// O(1) swap-remove membership invariants.
    fn place(&mut self, v: usize, new_bucket: u16) {
        let old = self.var_bucket[v];
        if old == new_bucket {
            return;
        }
        if old != NO_BUCKET {
            let list = &mut self.buckets[old as usize];
            let pos = self.var_pos[v] as usize;
            let last = list.len() - 1;
            list.swap(pos, last);
            list.pop();
            if pos < list.len() {
                let moved = list[pos] as usize;
                self.var_pos[moved] = pos as u32;
            }
        }
        self.var_bucket[v] = new_bucket;
        if new_bucket != NO_BUCKET {
            let b = new_bucket as usize;
            self.var_pos[v] = self.buckets[b].len() as u32;
            self.buckets[b].push(v as u32);
            if b > self.max_bucket {
                self.max_bucket = b;
            }
        }
    }

    /// Applies every queued score change (`combined(v)` is the CURRENT
    /// combined score; `> GOOD_EPS` = improving), then clears the dirty set by
    /// an epoch bump (the cp_dense idiom: O(touched), no reallocation, wrap
    /// resets the stamps exactly like [`crate::cp_dense::DenseCp::clear`]).
    fn flush(&mut self, combined: impl Fn(usize) -> f64) {
        for i in 0..self.dirty.len() {
            let v = self.dirty[i] as usize;
            let score = combined(v);
            let nb = if score > GOOD_EPS {
                bucket_of(score)
            } else {
                NO_BUCKET
            };
            self.place(v, nb);
        }
        self.dirty.clear();
        match self.epoch.checked_add(1) {
            Some(next) => self.epoch = next,
            None => {
                self.dirty_stamp.fill(0);
                self.epoch = 1;
            }
        }
    }

    /// Picks from the highest non-empty bucket (which contains the combined-
    /// score argmax, by monotonicity of [`bucket_of`]): a full deterministic
    /// argmax scan when the bucket is small (≤ `cap`), else the best of `cap`
    /// uniform samples FROM THAT BUCKET (a BMS confined to near-maximum
    /// candidates — strictly tighter than BMS over the whole goodvar stack).
    /// Returns `None` only when every bucket is empty. All randomness comes
    /// from the caller's PRNG: deterministic per seed.
    fn select(
        &mut self,
        combined: impl Fn(usize) -> f64,
        rng: &mut SplitMix64,
        cap: usize,
    ) -> Option<usize> {
        while self.max_bucket > 0 && self.buckets[self.max_bucket].is_empty() {
            self.max_bucket -= 1;
        }
        let list = &self.buckets[self.max_bucket];
        if list.is_empty() {
            return None;
        }
        let cap = cap.max(1);
        if list.len() <= cap {
            let mut best = list[0] as usize;
            for &u in &list[1..] {
                let u = u as usize;
                if combined(u) > combined(best) {
                    best = u;
                }
            }
            Some(best)
        } else {
            let mut best = list[rng.below(list.len())] as usize;
            for _ in 1..cap {
                let cand = list[rng.below(list.len())] as usize;
                if combined(cand) > combined(best) {
                    best = cand;
                }
            }
            Some(best)
        }
    }
}

/// Which best-move selector [`Scorer::pick_var`] uses for the greedy goodvar
/// pick (design §3.1). Both are deterministic per seed; both consult the same
/// incrementally-maintained scores; neither touches soundness (the scorer is
/// advisory, every incumbent is independently re-verified).
///
/// # Measured default (honest-measurement rule)
/// The default is decided by the in-file microbenchmark
/// (`bench_bucketed_vs_bms_flip_rate`, 10k/100k-var mixed Ge/Eq synthetic
/// instances with negated literals, fixed 400k-flip budgets, release build):
/// the bucketed selector becomes the default ONLY if it at least matches the
/// BMS flip rate on BOTH sizes. Measured 2026-07-11 (busy host, best of 2,
/// i64 core): 10k vars — BMS 1.69M flips/s vs bucketed 1.53M (0.90×);
/// 100k vars — BMS 1.18M vs bucketed 1.12M (0.95×). The bucketed selector did
/// NOT meet the flip-rate bar, so [`MoveSelector::Bms`] stays the DEFAULT and
/// the bucketed argmax ships default-off as an A/B lever. (For the record,
/// its per-flip quality was BETTER on both sizes — end-of-budget objective
/// 13524 vs 15149 and 159719 vs 162010 — so a quality-per-second A/B on the
/// real corpus may still earn it the default later; raw flip throughput is
/// what the timed-budget rule rewards, and it lost that.)
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum MoveSelector {
    /// Historical NuPBO-style BMS sample over the whole goodvar stack — the
    /// measured flip-rate default (see the enum docs).
    #[default]
    Bms,
    /// Bucketed dirty-set argmax (design §4) — A/B lever, default-off per the
    /// flip-rate measurement recorded above. Corpus A/B (2026-07-11, PB24
    /// 107-family slice, 15s): +13/=83/−11 vs BMS (net +2, high variance, one
    /// UNKNOWN→SAT) — not a convincing quality-per-second win; BMS keeps the
    /// default. Constructed only by the A/B
    /// tests/benches until it earns the default, so dead-code in the shipping
    /// binary is expected and deliberate.
    #[allow(dead_code)]
    Bucketed,
}

// ---------------------------------------------------------------------------
// The generic scorer core
// ---------------------------------------------------------------------------

/// One occurrence of a variable inside a constraint, with the exact LHS delta the
/// constraint sees when the variable flips false -> true.
#[derive(Clone, Copy)]
struct Occ<T> {
    constraint: u32,
    /// LHS change when the variable goes false -> true. Positive literal with
    /// coefficient `c`: `+c`; negated literal: `-c`.
    delta_f2t: T,
}

/// The shared incremental scorer core over a linear PB instance, generic over
/// the constraint-arithmetic scalar `T` (see [`ScoreInt`]). Use [`Scorer`] —
/// the width-dispatching wrapper — from outside this module.
struct ScorerCore<T: ScoreInt> {
    // ---- exact per-constraint state (differentially tested) ----
    lhs: Vec<T>,
    rhs: Vec<T>,
    rel: Vec<PbRel>,
    /// PAWS integer penalty weight per row (>= 1). Kept `i128` (cold: read
    /// only through the cached `norm_weight` on the hot path).
    unit_weight: Vec<i128>,
    /// `1 / round(avg |coeff|)` per row, for degree/coefficient normalization.
    inv_avg_coeff: Vec<f64>,
    /// Cached `unit_weight[c] as f64 * inv_avg_coeff[c]` — the per-row factor
    /// of every `contrib` call. Refreshed whenever `unit_weight` changes so the
    /// hot loop performs no int→f64 conversion (bit-identical value to the
    /// historical inline computation).
    norm_weight: Vec<f64>,
    /// For each constraint, the member variables and their f->t LHS deltas.
    cvars: Vec<Vec<(u32, T)>>,

    // ---- per-variable indices ----
    /// For each variable, the constraints it occurs in (and the f->t LHS delta).
    var_occ: Vec<Vec<Occ<T>>>,
    /// Per-variable objective delta (objective change when the var flips f->t).
    /// Objective arithmetic stays exact `i128` on both widths (O(1) per flip —
    /// not part of the hot constraint scan).
    obj_delta: Vec<i128>,
    /// The variables that appear in the objective (for objective-pressure updates).
    obj_vars: Vec<u32>,
    /// `1 / round(avg |objective coeff|)` for objective gradient normalization.
    inv_avg_obj_coeff: f64,

    // ---- mutable search state ----
    assign: Vec<bool>,
    /// Exact current objective value of `assign`.
    obj_value: i128,

    /// Violated-row set, with O(1) swap-remove membership.
    violated_list: Vec<usize>,
    /// Position of row `c` in `violated_list`, or `usize::MAX` if not violated.
    violated_pos: Vec<usize>,

    // ---- scores ----
    hscore: Vec<f64>,
    sscore: Vec<f64>,
    /// Adaptive objective-pressure weight λ (lever 4 / adaptive-lambda). Exactly
    /// 0 while `lambda_unlocked` is false; in `[LAMBDA_MIN, LAMBDA_MAX]` after.
    s_weight: f64,
    /// Whether the search has EVER reached feasibility. False = λ is hard-locked
    /// at 0 (design §2.1); set once (never cleared) by `unlock_lambda`.
    lambda_unlocked: bool,

    /// goodvar stack: variables with `hscore + sscore > GOOD_EPS`.
    goodvar_stack: Vec<u32>,
    /// Position of a variable in `goodvar_stack`, or `-1` if absent.
    goodvar_pos: Vec<isize>,

    /// `Some` iff [`MoveSelector::Bucketed`] — the default path pays one
    /// is-Some branch per touched var; the BMS path pays the same branch on a
    /// `None`.
    selector: Option<BucketSelector>,
}

impl<T: ScoreInt> ScorerCore<T> {
    /// Builds a scorer core for a linear instance under `assignment`. Returns
    /// `None` if the instance has a non-linear (product) term, references an
    /// out-of-range variable, exceeds the occurrence cap, a coefficient
    /// computation overflows `i128`, or — fail-closed, `i64` core only — any
    /// row fails the exact [`ScoreInt::row_fits`] bound or any narrowing
    /// fails.
    fn new(
        constraints: &[PbConstraint],
        objective: &PbObjective,
        num_vars: usize,
        assignment: &[bool],
        selector: MoveSelector,
    ) -> Option<ScorerCore<T>> {
        if assignment.len() != num_vars {
            return None;
        }

        let mut var_occ: Vec<Vec<Occ<T>>> = Vec::new();
        var_occ.resize_with(num_vars, Vec::new);
        let n = constraints.len();
        let mut lhs = Vec::with_capacity(n);
        let mut rhs = Vec::with_capacity(n);
        let mut rel = Vec::with_capacity(n);
        let mut inv_avg_coeff = Vec::with_capacity(n);
        let mut cvars: Vec<Vec<(u32, T)>> = Vec::with_capacity(n);
        let mut total_occ = 0usize;

        for (ci, constraint) in constraints.iter().enumerate() {
            let cidx = u32::try_from(ci).ok()?;
            let mut row_lhs: i128 = 0;
            let mut coeff_sum: i128 = 0;
            let mut members: Vec<(u32, T)> = Vec::with_capacity(constraint.terms.len());
            for term in &constraint.terms {
                let [lit] = term.lits.as_slice() else {
                    return None; // non-linear: decline
                };
                let var_index = (lit.var as usize).checked_sub(1)?;
                if var_index >= num_vars {
                    return None;
                }
                let value = assignment.get(var_index).copied().unwrap_or(false);
                let literal_true = if lit.negated { !value } else { value };
                if literal_true {
                    row_lhs = row_lhs.checked_add(term.coeff)?;
                }
                let delta_f2t = if lit.negated {
                    term.coeff.checked_neg()?
                } else {
                    term.coeff
                };
                coeff_sum = coeff_sum.saturating_add(term.coeff.saturating_abs());
                total_occ = total_occ.checked_add(1)?;
                if total_occ > MAX_SCORE_OCCURRENCES {
                    return None;
                }
                let var_u32 = u32::try_from(var_index).ok()?;
                // Fail-closed narrowing: a delta the scalar cannot represent
                // declines this core (the dispatcher falls back to i128).
                let delta_t = T::from_i128(delta_f2t)?;
                members.push((var_u32, delta_t));
                var_occ[var_index].push(Occ {
                    constraint: cidx,
                    delta_f2t: delta_t,
                });
            }
            // The per-instance exact overflow flag, re-checked per row at the
            // core itself (same predicate as the `rows_fit` dispatch, so a
            // dispatch bug can only decline, never wrap).
            if !T::row_fits(coeff_sum, constraint.rhs) {
                return None;
            }
            let len = constraint.terms.len().max(1) as i128;
            let avg = ((coeff_sum + len - 1) / len).max(1); // round-up avg, >= 1
            inv_avg_coeff.push(1.0 / avg as f64);
            lhs.push(T::from_i128(row_lhs)?);
            rhs.push(T::from_i128(constraint.rhs)?);
            rel.push(constraint.rel);
            cvars.push(members);
        }

        // Objective deltas (single-literal terms only) and objective value.
        // Objective arithmetic is exact i128 on BOTH widths.
        let mut obj_delta = vec![0i128; num_vars];
        let mut obj_vars_set = vec![false; num_vars];
        let mut obj_coeff_sum: i128 = 0;
        let mut obj_term_count: i128 = 0;
        let mut obj_value: i128 = 0;
        for term in &objective.terms {
            let [lit] = term.lits.as_slice() else {
                return None;
            };
            let var_index = (lit.var as usize).checked_sub(1)?;
            if var_index >= num_vars {
                return None;
            }
            let contribution = if lit.negated {
                term.coeff.checked_neg()?
            } else {
                term.coeff
            };
            obj_delta[var_index] = obj_delta[var_index].checked_add(contribution)?;
            obj_vars_set[var_index] = true;
            obj_coeff_sum = obj_coeff_sum.saturating_add(term.coeff.saturating_abs());
            obj_term_count += 1;
            let value = assignment.get(var_index).copied().unwrap_or(false);
            let literal_true = if lit.negated { !value } else { value };
            if literal_true {
                obj_value = obj_value.checked_add(term.coeff)?;
            }
        }
        let obj_vars: Vec<u32> = (0..num_vars)
            .filter(|&v| obj_vars_set[v])
            .map(|v| v as u32)
            .collect();
        let avg_obj = if obj_term_count == 0 {
            1
        } else {
            ((obj_coeff_sum + obj_term_count - 1) / obj_term_count).max(1)
        };

        let unit_weight = vec![1i128; n];
        let norm_weight: Vec<f64> = unit_weight
            .iter()
            .zip(&inv_avg_coeff)
            .map(|(&w, &inv)| w as f64 * inv)
            .collect();
        let mut scorer = ScorerCore {
            lhs,
            rhs,
            rel,
            unit_weight,
            inv_avg_coeff,
            norm_weight,
            cvars,
            var_occ,
            obj_delta,
            obj_vars,
            inv_avg_obj_coeff: 1.0 / avg_obj as f64,
            assign: assignment.to_vec(),
            obj_value,
            violated_list: Vec::new(),
            violated_pos: vec![usize::MAX; n],
            hscore: vec![0.0; num_vars],
            sscore: vec![0.0; num_vars],
            // λ starts HARD-LOCKED at 0 (design §2.1): pure feasibility hunt
            // until the first feasible assignment. A feasible seed (the polish
            // warm-start path) releases the lock immediately below.
            s_weight: 0.0,
            lambda_unlocked: false,
            goodvar_stack: Vec::new(),
            goodvar_pos: vec![-1; num_vars],
            selector: match selector {
                MoveSelector::Bms => None,
                MoveSelector::Bucketed => Some(BucketSelector::new(num_vars)),
            },
        };
        scorer.rebuild_violated();
        if scorer.violated_list.is_empty() {
            // Feasible from step 0 (e.g. warm-started from an existing feasible
            // incumbent): release the λ lock right away so the run does objective
            // descent from the start instead of degrading to a feasibility-only
            // search. `recompute_scores` below picks up the unlocked λ.
            scorer.lambda_unlocked = true;
            scorer.s_weight = LAMBDA_INIT;
        }
        scorer.recompute_scores();
        Some(scorer)
    }

    /// Whether the current assignment satisfies every hard constraint.
    fn is_feasible(&self) -> bool {
        self.violated_list.is_empty()
    }

    /// The exact objective value of the current assignment (test-only
    /// observability; production re-values incumbents independently).
    #[cfg(test)]
    fn obj_value(&self) -> i128 {
        self.obj_value
    }

    /// The current assignment.
    fn assignment(&self) -> &[bool] {
        &self.assign
    }

    /// Releases the λ hard-lock — called exactly once, the first time the search
    /// reaches feasibility (at construction for a feasible seed, else from
    /// `flip`). Sets λ to [`LAMBDA_INIT`] and refreshes every objective
    /// variable's `sscore`/goodvar membership, which were all 0 under the lock.
    fn unlock_lambda(&mut self) {
        debug_assert!(!self.lambda_unlocked);
        self.lambda_unlocked = true;
        self.s_weight = LAMBDA_INIT;
        let obj_vars = std::mem::take(&mut self.obj_vars);
        for &v in &obj_vars {
            let v = v as usize;
            self.sscore[v] = self.s_weight * self.obj_gain_norm(v);
            self.refresh_goodvar(v);
        }
        self.obj_vars = obj_vars;
    }

    /// Combined NuPBO score of flipping `v` (higher is a better move).
    #[inline]
    fn combined(&self, v: usize) -> f64 {
        self.hscore[v] + self.sscore[v]
    }

    /// The objective-reduction gradient of variable `v` under the CURRENT
    /// assignment, normalized by the average objective coefficient. Positive when
    /// flipping `v` lowers the objective.
    #[inline]
    fn obj_gain_norm(&self, v: usize) -> f64 {
        // If v is currently true, flipping to false reduces the objective by
        // obj_delta[v]; if currently false, flipping to true reduces it by
        // -obj_delta[v].
        let gain = if self.assign[v] {
            self.obj_delta[v]
        } else {
            self.obj_delta[v].saturating_neg()
        };
        gain as f64 * self.inv_avg_obj_coeff
    }

    /// The contribution of constraint `c` to `hscore[u]`: the reduction in `c`'s
    /// degree-normalized weighted shortfall if `u` were flipped from its CURRENT
    /// value. Positive when flipping `u` helps satisfy `c`. All integer work is
    /// in `T` (the i64 fast path's hot kernel); `norm_weight` caches the
    /// weight×normalization factor so no int→f64 conversion happens here.
    #[inline]
    fn contrib(&self, c: usize, u: usize, du: T) -> f64 {
        let signed = if self.assign[u] {
            du.saturating_neg()
        } else {
            du
        };
        let cur = T::shortfall(self.rel[c], self.lhs[c], self.rhs[c]);
        let nxt = T::shortfall(self.rel[c], self.lhs[c].saturating_add(signed), self.rhs[c]);
        self.norm_weight[c] * cur.saturating_sub(nxt).to_f64()
    }

    /// Rebuilds the violated-row set from scratch from the current `lhs`.
    fn rebuild_violated(&mut self) {
        self.violated_list.clear();
        for p in self.violated_pos.iter_mut() {
            *p = usize::MAX;
        }
        for c in 0..self.lhs.len() {
            if T::shortfall(self.rel[c], self.lhs[c], self.rhs[c]) > T::ZERO {
                self.violated_pos[c] = self.violated_list.len();
                self.violated_list.push(c);
            }
        }
    }

    fn mark_violated(&mut self, c: usize) {
        if self.violated_pos[c] == usize::MAX {
            self.violated_pos[c] = self.violated_list.len();
            self.violated_list.push(c);
        }
    }

    fn mark_satisfied(&mut self, c: usize) {
        let pos = self.violated_pos[c];
        if pos == usize::MAX {
            return;
        }
        let last = self.violated_list.len() - 1;
        let moved = self.violated_list[last];
        self.violated_list.swap(pos, last);
        self.violated_list.pop();
        self.violated_pos[moved] = pos;
        self.violated_pos[c] = usize::MAX;
    }

    /// Recomputes every variable's `hscore`/`sscore` and rebuilds the goodvar
    /// stack from scratch under the current assignment/weights. Used at
    /// construction and re-sync; the per-flip path maintains these incrementally.
    fn recompute_scores(&mut self) {
        for v in 0..self.hscore.len() {
            self.hscore[v] = 0.0;
        }
        for c in 0..self.cvars.len() {
            let m = self.cvars[c].len();
            for k in 0..m {
                let (u, du) = self.cvars[c][k];
                let u = u as usize;
                self.hscore[u] += self.contrib(c, u, du);
            }
        }
        for v in 0..self.sscore.len() {
            self.sscore[v] = self.s_weight * self.obj_gain_norm(v);
        }
        self.goodvar_stack.clear();
        for p in self.goodvar_pos.iter_mut() {
            *p = -1;
        }
        for v in 0..self.hscore.len() {
            if self.hscore[v] + self.sscore[v] > GOOD_EPS {
                self.goodvar_pos[v] = self.goodvar_stack.len() as isize;
                self.goodvar_stack.push(v as u32);
            }
        }
        // Full re-sync of the bucketed selector: mark everything dirty; the
        // next selection's flush rebuilds membership in one O(vars) pass.
        if let Some(sel) = self.selector.as_mut() {
            for v in 0..self.hscore.len() {
                sel.mark_dirty(v);
            }
        }
    }

    /// Updates `v`'s membership in the goodvar stack to match its current score,
    /// and queues `v` in the bucketed selector's dirty set (O(1); the selector
    /// re-buckets it at the next selection flush).
    fn refresh_goodvar(&mut self, v: usize) {
        if let Some(sel) = self.selector.as_mut() {
            sel.mark_dirty(v);
        }
        let good = self.hscore[v] + self.sscore[v] > GOOD_EPS;
        let pos = self.goodvar_pos[v];
        if good && pos < 0 {
            self.goodvar_pos[v] = self.goodvar_stack.len() as isize;
            self.goodvar_stack.push(v as u32);
        } else if !good && pos >= 0 {
            let pos = pos as usize;
            let last_idx = self.goodvar_stack.len() - 1;
            let moved = self.goodvar_stack[last_idx] as usize;
            self.goodvar_stack.swap(pos, last_idx);
            self.goodvar_stack.pop();
            self.goodvar_pos[moved] = pos as isize;
            self.goodvar_pos[v] = -1;
        }
    }

    /// Applies a flip of variable `v`, maintaining `lhs`, the violated set,
    /// `obj_value`, all touched `hscore`/`sscore`, and goodvar membership — all in
    /// `O(touched)` where touched = the rows `v` occurs in and their members.
    fn flip(&mut self, v: usize) {
        let old_val = self.assign[v];

        // Phase A: remove the OLD hard contributions of every neighbour variable
        // (their scores depend on the current lhs of the rows v touches).
        let occ_len = self.var_occ[v].len();
        for i in 0..occ_len {
            let c = self.var_occ[v][i].constraint as usize;
            let m = self.cvars[c].len();
            for k in 0..m {
                let (u, du) = self.cvars[c][k];
                let u = u as usize;
                self.hscore[u] -= self.contrib(c, u, du);
            }
        }

        // Phase B: apply the flip to lhs / violated-set / obj_value.
        let obj_change = if old_val {
            self.obj_delta[v].saturating_neg()
        } else {
            self.obj_delta[v]
        };
        self.obj_value = self.obj_value.saturating_add(obj_change);

        for i in 0..occ_len {
            let occ = self.var_occ[v][i];
            let c = occ.constraint as usize;
            // lhs change: old true -> now false => -delta_f2t; old false -> now true => +delta_f2t.
            let signed = if old_val {
                occ.delta_f2t.saturating_neg()
            } else {
                occ.delta_f2t
            };
            let before = T::shortfall(self.rel[c], self.lhs[c], self.rhs[c]);
            self.lhs[c] = self.lhs[c].saturating_add(signed);
            let after = T::shortfall(self.rel[c], self.lhs[c], self.rhs[c]);
            if before == T::ZERO && after > T::ZERO {
                self.mark_violated(c);
            } else if before > T::ZERO && after == T::ZERO {
                self.mark_satisfied(c);
            }
        }
        self.assign[v] = !old_val;

        // Phase C: add the NEW hard contributions under the updated lhs/assign.
        for i in 0..occ_len {
            let c = self.var_occ[v][i].constraint as usize;
            let m = self.cvars[c].len();
            for k in 0..m {
                let (u, du) = self.cvars[c][k];
                let u = u as usize;
                self.hscore[u] += self.contrib(c, u, du);
            }
        }

        // Phase D: v's own objective gradient flips sign with its value.
        self.sscore[v] = self.s_weight * self.obj_gain_norm(v);

        // Phase E: refresh goodvar membership for v and every touched neighbour.
        self.refresh_goodvar(v);
        for i in 0..occ_len {
            let c = self.var_occ[v][i].constraint as usize;
            let m = self.cvars[c].len();
            for k in 0..m {
                let u = self.cvars[c][k].0 as usize;
                self.refresh_goodvar(u);
            }
        }

        // Phase F: λ hard-lock release (design §2.1) — the FIRST time the search
        // reaches feasibility, objective pressure switches on at LAMBDA_INIT.
        // Checked after the violated-set update so the flip that satisfies the
        // last violated row unlocks immediately. Once unlocked, never re-locked.
        if !self.lambda_unlocked && self.violated_list.is_empty() {
            self.unlock_lambda();
        }
    }

    /// PAWS + objective-pressure weight update, invoked when the search is stuck
    /// (no improving move). Bumps every violated hard row's weight (updating the
    /// affected `hscore`s) and either escalates objective pressure (when feasible)
    /// or decays it (when infeasible), then refreshes goodvar membership.
    fn bump_weights(&mut self) {
        let feasible = self.violated_list.is_empty();

        // Hard PAWS bump on violated rows. Updating the weight changes the
        // normalized contribution of the row to every member's hscore, so we
        // remove-old / bump / add-new for each violated row.
        let violated: Vec<usize> = self.violated_list.clone();
        for &c in &violated {
            let m = self.cvars[c].len();
            for k in 0..m {
                let (u, du) = self.cvars[c][k];
                self.hscore[u as usize] -= self.contrib(c, u as usize, du);
            }
            self.unit_weight[c] = self.unit_weight[c].saturating_add(H_INC);
            self.norm_weight[c] = self.unit_weight[c] as f64 * self.inv_avg_coeff[c];
            for k in 0..m {
                let (u, du) = self.cvars[c][k];
                self.hscore[u as usize] += self.contrib(c, u as usize, du);
            }
        }
        for &c in &violated {
            let m = self.cvars[c].len();
            for k in 0..m {
                let u = self.cvars[c][k].0 as usize;
                self.refresh_goodvar(u);
            }
        }

        // Objective-pressure (adaptive-λ) update — design §2.1. HARD-LOCKED at
        // exactly 0 until the first feasible assignment (the lock is released
        // only in `new`/`flip`, never here: `feasible` implies already unlocked,
        // so a locked scorer is infeasible and λ must stay 0). Once unlocked, λ
        // adapts MULTIPLICATIVELY within [LAMBDA_MIN, LAMBDA_MAX]: raised when
        // dwelling feasible with no objective gain, lowered when the search
        // keeps leaving the feasible region. The factors ARE the clamped
        // per-update change rate (at most ×LAMBDA_RAISE up / ×LAMBDA_DECAY down).
        if !self.lambda_unlocked {
            return;
        }
        let new_s = if feasible {
            (self.s_weight * LAMBDA_RAISE).min(LAMBDA_MAX)
        } else {
            (self.s_weight * LAMBDA_DECAY).max(LAMBDA_MIN)
        };
        if (new_s - self.s_weight).abs() > f64::EPSILON {
            self.s_weight = new_s;
            // sscore depends linearly on s_weight; update only objective vars.
            let obj_vars = std::mem::take(&mut self.obj_vars);
            for &v in &obj_vars {
                let v = v as usize;
                self.sscore[v] = self.s_weight * self.obj_gain_norm(v);
                self.refresh_goodvar(v);
            }
            self.obj_vars = obj_vars;
        }
    }

    /// Picks the next variable to flip, NuPBO-style:
    /// * if the goodvar stack is non-empty, return a goodvar — with a small
    ///   probability a uniform random one (diversification), otherwise the
    ///   greedy pick of the configured [`MoveSelector`] (top-gain-bucket
    ///   argmax, or a bounded Best-from-Multiple-Selections sample);
    /// * otherwise bump weights (PAWS + objective pressure) and pick from a random
    ///   violated row (if infeasible) or a sampled objective variable (if feasible
    ///   but at a local optimum — this is the move that may cross the ridge).
    ///
    /// `rd_prob_permille` is the random-goodvar probability (in 1/1000); `bms` is
    /// the BMS sample size (also the top-bucket scan/sample cap). Returns `None`
    /// only if there is genuinely nothing to flip (no constraints and no
    /// objective variables).
    fn pick_var(
        &mut self,
        rng: &mut SplitMix64,
        rd_prob_permille: u64,
        bms: usize,
    ) -> Option<usize> {
        if let Some(v) = self.pick_from_goodvar(rng, rd_prob_permille, bms) {
            return Some(v);
        }
        // Stuck: escalate weights, then re-try the goodvar stack (the bump may have
        // created improving moves), else fall back to a focused random pick.
        self.bump_weights();
        if let Some(v) = self.pick_from_goodvar(rng, rd_prob_permille, bms) {
            return Some(v);
        }
        if !self.violated_list.is_empty() {
            let c = self.violated_list[rng.below(self.violated_list.len())];
            return self.best_in_constraint(c, rng, bms);
        }
        // Feasible local optimum: diversify by sampling an objective variable.
        if self.obj_vars.is_empty() {
            return None;
        }
        let k = bms.max(1).min(self.obj_vars.len());
        let mut best = self.obj_vars[rng.below(self.obj_vars.len())] as usize;
        for _ in 1..k {
            let cand = self.obj_vars[rng.below(self.obj_vars.len())] as usize;
            if self.combined(cand) > self.combined(best) {
                best = cand;
            }
        }
        Some(best)
    }

    fn pick_from_goodvar(
        &mut self,
        rng: &mut SplitMix64,
        rd_prob_permille: u64,
        bms: usize,
    ) -> Option<usize> {
        let len = self.goodvar_stack.len();
        if len == 0 {
            return None;
        }
        if (rng.below(1000) as u64) < rd_prob_permille {
            return Some(self.goodvar_stack[rng.below(len)] as usize);
        }
        // Bucketed greedy pick (design §4): flush the dirty set (O(touched)),
        // then take from the top gain bucket. Defensive: falls through to BMS
        // if the bucket state were ever empty while goodvars exist (sync bug —
        // cannot happen, pinned by the fuzz), so selection can never stall.
        if self.selector.is_some() {
            let ScorerCore {
                selector,
                hscore,
                sscore,
                ..
            } = self;
            if let Some(sel) = selector.as_mut() {
                sel.flush(|v| hscore[v] + sscore[v]);
                if let Some(v) = sel.select(|v| hscore[v] + sscore[v], rng, bms) {
                    return Some(v);
                }
            }
        }
        let k = bms.max(1).min(len);
        let mut best = self.goodvar_stack[rng.below(len)] as usize;
        for _ in 1..k {
            let cand = self.goodvar_stack[rng.below(len)] as usize;
            if self.combined(cand) > self.combined(best) {
                best = cand;
            }
        }
        Some(best)
    }

    fn best_in_constraint(&self, c: usize, rng: &mut SplitMix64, bms: usize) -> Option<usize> {
        let members = &self.cvars[c];
        if members.is_empty() {
            return None;
        }
        // BMS within the row when it is large; full scan when small.
        if members.len() <= bms.max(1) {
            let mut best = members[0].0 as usize;
            for &(u, _) in &members[1..] {
                let u = u as usize;
                if self.combined(u) > self.combined(best) {
                    best = u;
                }
            }
            Some(best)
        } else {
            let k = bms.max(1);
            let mut best = members[rng.below(members.len())].0 as usize;
            for _ in 1..k {
                let cand = members[rng.below(members.len())].0 as usize;
                if self.combined(cand) > self.combined(best) {
                    best = cand;
                }
            }
            Some(best)
        }
    }

    // ---- test-only oracles for differential testing ----

    /// Recomputes `hscore`/`sscore` from scratch (independent of the incremental
    /// maintenance) for differential testing.
    #[cfg(test)]
    fn fresh_scores(&self) -> (Vec<f64>, Vec<f64>) {
        let mut h = vec![0.0; self.hscore.len()];
        for c in 0..self.cvars.len() {
            for &(u, du) in &self.cvars[c] {
                h[u as usize] += self.contrib(c, u as usize, du);
            }
        }
        let mut s = vec![0.0; self.sscore.len()];
        for v in 0..s.len() {
            s[v] = self.s_weight * self.obj_gain_norm(v);
        }
        (h, s)
    }

    /// Flushes the bucketed selector and asserts its state exactly mirrors the
    /// goodvar predicate: every improving variable sits in `bucket_of(score)`,
    /// nothing else is in any bucket, and positions are consistent. Test-only.
    #[cfg(test)]
    fn assert_selector_in_sync(&mut self) {
        let ScorerCore {
            selector,
            hscore,
            sscore,
            ..
        } = self;
        let Some(sel) = selector.as_mut() else {
            return;
        };
        sel.flush(|v| hscore[v] + sscore[v]);
        for v in 0..hscore.len() {
            let score = hscore[v] + sscore[v];
            let want = if score > GOOD_EPS {
                bucket_of(score)
            } else {
                NO_BUCKET
            };
            assert_eq!(sel.var_bucket[v], want, "bucket drift for var {v}");
            if want != NO_BUCKET {
                let list = &sel.buckets[want as usize];
                assert_eq!(
                    list[sel.var_pos[v] as usize] as usize, v,
                    "bucket position drift for var {v}"
                );
            }
        }
        let total: usize = sel.buckets.iter().map(Vec::len).sum();
        let good = (0..hscore.len())
            .filter(|&v| hscore[v] + sscore[v] > GOOD_EPS)
            .count();
        assert_eq!(total, good, "bucket population != goodvar count");
    }
}

// ---------------------------------------------------------------------------
// Width-dispatching wrapper (the public face of the scorer)
// ---------------------------------------------------------------------------

enum ScorerRepr {
    /// The i64 fast path: every row passed the exact `Σ|coeff| + |rhs| ≤
    /// i64::MAX` bound, so all constraint arithmetic runs (exactly) in i64.
    I64(ScorerCore<i64>),
    /// The exact i128 fallback (large-coefficient instances).
    I128(ScorerCore<i128>),
}

macro_rules! with_core {
    ($self:expr, $core:ident => $body:expr) => {
        match &$self.repr {
            ScorerRepr::I64($core) => $body,
            ScorerRepr::I128($core) => $body,
        }
    };
}
macro_rules! with_core_mut {
    ($self:expr, $core:ident => $body:expr) => {
        match &mut $self.repr {
            ScorerRepr::I64($core) => $body,
            ScorerRepr::I128($core) => $body,
        }
    };
}

/// The shared incremental scorer over a linear PB instance. Dispatches at
/// construction between the `i64` fast core and the exact `i128` core via the
/// per-instance overflow flag (see [`ScoreInt`] / [`rows_fit`]); both cores
/// compute identical values, so the choice affects only speed. See the module
/// docs for the full contract.
pub(crate) struct Scorer {
    repr: ScorerRepr,
}

impl Scorer {
    /// Builds a scorer for a linear instance under `assignment` with the
    /// DEFAULT move selector (see [`MoveSelector`]). Returns `None` if the
    /// instance has a non-linear (product) term, references an out-of-range
    /// variable, exceeds the occurrence cap, or a coefficient computation
    /// overflows `i128`.
    pub(crate) fn new(
        constraints: &[PbConstraint],
        objective: &PbObjective,
        num_vars: usize,
        assignment: &[bool],
    ) -> Option<Scorer> {
        Self::with_selector(
            constraints,
            objective,
            num_vars,
            assignment,
            MoveSelector::default(),
        )
    }

    /// As [`Scorer::new`], with an explicit [`MoveSelector`] (the A/B lever;
    /// `MoveSelector::default()` reproduces `new` exactly).
    pub(crate) fn with_selector(
        constraints: &[PbConstraint],
        objective: &PbObjective,
        num_vars: usize,
        assignment: &[bool],
        selector: MoveSelector,
    ) -> Option<Scorer> {
        // i64 fast path only when every row provably fits (the exact
        // per-instance overflow flag); the core re-checks per row, so even a
        // flag bug degrades to the exact i128 core — fail-closed, never wraps.
        if rows_fit::<i64>(constraints) {
            if let Some(core) =
                ScorerCore::<i64>::new(constraints, objective, num_vars, assignment, selector)
            {
                return Some(Scorer {
                    repr: ScorerRepr::I64(core),
                });
            }
        }
        ScorerCore::<i128>::new(constraints, objective, num_vars, assignment, selector).map(
            |core| Scorer {
                repr: ScorerRepr::I128(core),
            },
        )
    }

    /// Whether the current assignment satisfies every hard constraint.
    pub(crate) fn is_feasible(&self) -> bool {
        with_core!(self, c => c.is_feasible())
    }

    /// The exact objective value of the current assignment (test-only
    /// observability; production re-values incumbents independently).
    #[cfg(test)]
    pub(crate) fn obj_value(&self) -> i128 {
        with_core!(self, c => c.obj_value())
    }

    /// The current assignment.
    pub(crate) fn assignment(&self) -> &[bool] {
        with_core!(self, c => c.assignment())
    }

    /// The current objective-pressure weight λ (test-only observability for the
    /// hard-lock / multiplicative-schedule invariants).
    #[cfg(test)]
    pub(crate) fn lambda(&self) -> f64 {
        with_core!(self, c => c.s_weight)
    }

    /// Whether the i64 fast core was selected (test-only observability for the
    /// overflow-flag dispatch).
    #[cfg(test)]
    pub(crate) fn uses_i64(&self) -> bool {
        matches!(self.repr, ScorerRepr::I64(_))
    }

    /// Applies a flip of variable `v` — see `ScorerCore::flip`.
    pub(crate) fn flip(&mut self, v: usize) {
        with_core_mut!(self, c => c.flip(v))
    }

    /// Picks the next variable to flip — see `ScorerCore::pick_var`.
    pub(crate) fn pick_var(
        &mut self,
        rng: &mut SplitMix64,
        rd_prob_permille: u64,
        bms: usize,
    ) -> Option<usize> {
        with_core_mut!(self, c => c.pick_var(rng, rd_prob_permille, bms))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver::eval_objective;
    use crate::types::{PbInstance, PbLit, PbTerm};

    fn lit(var: u32) -> PbLit {
        PbLit {
            var,
            negated: false,
        }
    }
    fn neg(var: u32) -> PbLit {
        PbLit { var, negated: true }
    }
    fn term(coeff: i128, l: PbLit) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![l],
        }
    }
    fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs,
        }
    }
    fn eq(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Eq,
            rhs,
        }
    }

    /// Exact weighted (integer) violation oracle = Σ unit_weight·shortfall.
    fn fresh_weighted_violation<T: ScoreInt>(s: &ScorerCore<T>) -> i128 {
        let mut total: i128 = 0;
        for c in 0..s.lhs.len() {
            let short = T::shortfall(s.rel[c], s.lhs[c], s.rhs[c]);
            total = total.saturating_add(s.unit_weight[c].saturating_mul(short.to_i128()));
        }
        total
    }

    /// Exact LHS of a single linear row under `assign`, computed directly from the
    /// ORIGINAL constraint (independent of the scorer's incremental tracker).
    fn oracle_lhs(constraint: &PbConstraint, assign: &[bool]) -> i128 {
        let mut v: i128 = 0;
        for t in &constraint.terms {
            let l = t.lits[0];
            let var_true = assign[(l.var - 1) as usize];
            let lit_true = if l.negated { !var_true } else { var_true };
            if lit_true {
                v = v.saturating_add(t.coeff);
            }
        }
        v
    }

    fn close(a: f64, b: f64) -> bool {
        (a - b).abs() <= 1e-6 * (1.0 + a.abs() + b.abs())
    }

    /// A mixed instance exercising Ge rows, an Eq (split) row, negated literals,
    /// and a weighted objective.
    fn mixed_instance() -> (PbInstance, PbObjective) {
        let constraints = vec![
            // 2 x1 + 3 ~x2 + 1 x3 >= 3
            ge(vec![term(2, lit(1)), term(3, neg(2)), term(1, lit(3))], 3),
            // x1 + 2 ~x2 + x3 + 3 ~x4 = 3   (a market-split style equality /
            // split row WITH negated literals: the Eq-row × negated-literal
            // slack-sign interaction of design §2.6)
            eq(
                vec![
                    term(1, lit(1)),
                    term(2, neg(2)),
                    term(1, lit(3)),
                    term(3, neg(4)),
                ],
                3,
            ),
            // 4 ~x3 + 2 x4 >= 2
            ge(vec![term(4, neg(3)), term(2, lit(4))], 2),
        ];
        let objective = PbObjective {
            terms: vec![
                term(5, lit(1)),
                term(3, neg(2)),
                term(7, lit(3)),
                term(2, lit(4)),
            ],
        };
        let instance = PbInstance {
            num_vars: 4,
            num_constraints: constraints.len() as u32,
            constraints,
            objective: Some(objective.clone()),
        };
        (instance, objective)
    }

    fn core<T: ScoreInt>(
        constraints: &[PbConstraint],
        objective: &PbObjective,
        num_vars: usize,
        assignment: &[bool],
        selector: MoveSelector,
    ) -> ScorerCore<T> {
        ScorerCore::<T>::new(constraints, objective, num_vars, assignment, selector).unwrap()
    }

    // ---- differential oracles, run on BOTH integer widths (design §3.1:
    // "the differential-oracle fuzz tests must cover BOTH paths") ----

    fn scorer_obj_value_matches_oracle_after_flips_impl<T: ScoreInt>(sel: MoveSelector) {
        let (instance, objective) = mixed_instance();
        let mut rng = SplitMix64::new(0xDEAD_BEEF_1234_5678);
        let init = vec![false, false, false, false];
        let mut s = core::<T>(&instance.constraints, &objective, 4, &init, sel);
        assert_eq!(s.obj_value(), eval_objective(&objective, s.assignment()));
        for _ in 0..500 {
            let v = rng.below(4);
            s.flip(v);
            // Exact objective: incremental == from-scratch oracle.
            assert_eq!(
                s.obj_value(),
                eval_objective(&objective, s.assignment()),
                "obj_value drifted from oracle"
            );
        }
    }

    #[test]
    fn scorer_obj_value_matches_oracle_after_flips_i64() {
        scorer_obj_value_matches_oracle_after_flips_impl::<i64>(MoveSelector::Bms);
    }
    #[test]
    fn scorer_obj_value_matches_oracle_after_flips_i128() {
        scorer_obj_value_matches_oracle_after_flips_impl::<i128>(MoveSelector::Bms);
    }

    fn scorer_lhs_and_violation_match_oracle_after_flips_impl<T: ScoreInt>() {
        let (instance, objective) = mixed_instance();
        let mut rng = SplitMix64::new(0x0123_4567_89AB_CDEF);
        let init = vec![true, false, true, false];
        let mut s = core::<T>(
            &instance.constraints,
            &objective,
            4,
            &init,
            MoveSelector::Bms,
        );
        for _ in 0..500 {
            let v = rng.below(4);
            s.flip(v);
            // Exact per-row lhs: incremental == oracle over original constraints.
            let oracle: Vec<i128> = instance
                .constraints
                .iter()
                .map(|c| oracle_lhs(c, s.assignment()))
                .collect();
            let got_lhs: Vec<i128> = s.lhs.iter().map(|&x| x.to_i128()).collect();
            assert_eq!(got_lhs, oracle, "lhs drifted");
            // Violated set matches the exact shortfall oracle.
            let oracle_violated: Vec<usize> = (0..s.lhs.len())
                .filter(|&c| T::shortfall(s.rel[c], s.lhs[c], s.rhs[c]) > T::ZERO)
                .collect();
            let mut got = s.violated_list.clone();
            got.sort_unstable();
            let mut want = oracle_violated.clone();
            want.sort_unstable();
            assert_eq!(got, want, "violated set drifted");
            // feasibility flag consistent.
            assert_eq!(s.is_feasible(), oracle_violated.is_empty());
            let _ = fresh_weighted_violation(&s);
        }
    }

    #[test]
    fn scorer_lhs_and_violation_match_oracle_after_flips_i64() {
        scorer_lhs_and_violation_match_oracle_after_flips_impl::<i64>();
    }
    #[test]
    fn scorer_lhs_and_violation_match_oracle_after_flips_i128() {
        scorer_lhs_and_violation_match_oracle_after_flips_impl::<i128>();
    }

    fn scorer_scores_match_oracle_after_flips_and_bumps_impl<T: ScoreInt>() {
        // The hard part: incrementally-maintained hscore/sscore must equal a
        // from-scratch recompute after flips AND weight bumps (which change the
        // normalized hard weights and objective pressure).
        let (instance, objective) = mixed_instance();
        let mut rng = SplitMix64::new(0xFEED_FACE_C0DE_0001);
        let init = vec![false, true, false, true];
        let mut s = core::<T>(
            &instance.constraints,
            &objective,
            4,
            &init,
            MoveSelector::Bms,
        );
        for step in 0..800 {
            if step % 7 == 0 {
                s.bump_weights();
            } else {
                let v = rng.below(4);
                s.flip(v);
            }
            let (fh, fs) = s.fresh_scores();
            for v in 0..4 {
                assert!(
                    close(s.hscore[v], fh[v]),
                    "hscore[{v}] drift: inc={} fresh={} (step {step})",
                    s.hscore[v],
                    fh[v]
                );
                assert!(
                    close(s.sscore[v], fs[v]),
                    "sscore[{v}] drift: inc={} fresh={} (step {step})",
                    s.sscore[v],
                    fs[v]
                );
            }
            // goodvar stack must exactly equal {v : hscore+sscore > eps}.
            let mut want: Vec<u32> = (0..4)
                .filter(|&v| s.hscore[v] + s.sscore[v] > GOOD_EPS)
                .map(|v| v as u32)
                .collect();
            want.sort_unstable();
            let mut got = s.goodvar_stack.clone();
            got.sort_unstable();
            assert_eq!(got, want, "goodvar stack drift at step {step}");
        }
    }

    #[test]
    fn scorer_scores_match_oracle_after_flips_and_bumps_i64() {
        scorer_scores_match_oracle_after_flips_and_bumps_impl::<i64>();
    }
    #[test]
    fn scorer_scores_match_oracle_after_flips_and_bumps_i128() {
        scorer_scores_match_oracle_after_flips_and_bumps_impl::<i128>();
    }

    #[test]
    fn scorer_flip_delta_matches_obj_recompute() {
        // The objective change reported by a flip equals the difference of the
        // exact objective oracle, over negated-literal objective terms.
        let (instance, objective) = mixed_instance();
        let mut rng = SplitMix64::new(0xABCD_1234_5678_9999);
        let init = vec![true, true, false, false];
        let mut s = Scorer::new(&instance.constraints, &objective, 4, &init).unwrap();
        for _ in 0..300 {
            let v = rng.below(4);
            let before = eval_objective(&objective, s.assignment());
            s.flip(v);
            let after = eval_objective(&objective, s.assignment());
            assert_eq!(s.obj_value(), after);
            // The maintained delta equals the oracle delta.
            assert_eq!(after - before, s.obj_value() - before);
        }
    }

    // ---- i64 fast path: dispatch, fail-closed narrowing, path equality ----

    #[test]
    fn overflow_flag_dispatches_i64_and_i128_at_the_exact_boundary() {
        let objective = PbObjective {
            terms: vec![term(1, lit(1)), term(1, lit(2))],
        };
        // Σ|coeff| + |rhs| == i64::MAX exactly: fits the i64 core.
        let c_fit = ge(
            vec![term((i64::MAX - 10) as i128, lit(1)), term(3, lit(2))],
            7,
        );
        assert!(rows_fit::<i64>(std::slice::from_ref(&c_fit)));
        let s = Scorer::new(&[c_fit], &objective, 2, &[false, false]).unwrap();
        assert!(s.uses_i64(), "boundary row must take the i64 fast path");

        // Σ|coeff| + |rhs| == i64::MAX + 1: must fall back to the i128 core.
        let c_over = ge(
            vec![term((i64::MAX - 10) as i128, lit(1)), term(3, lit(2))],
            8,
        );
        assert!(!rows_fit::<i64>(std::slice::from_ref(&c_over)));
        let s = Scorer::new(&[c_over], &objective, 2, &[false, false]).unwrap();
        assert!(!s.uses_i64(), "over-boundary row must take the i128 path");

        // A single huge coefficient (> i64::MAX) must also fall back, and the
        // i64 core itself must fail closed (None) on it — the narrowing check.
        let huge = 1i128 << 70;
        let c_huge = ge(vec![term(huge, lit(1))], 1);
        assert!(!rows_fit::<i64>(std::slice::from_ref(&c_huge)));
        assert!(ScorerCore::<i64>::new(
            std::slice::from_ref(&c_huge),
            &objective,
            2,
            &[false, false],
            MoveSelector::Bms
        )
        .is_none());
        let s = Scorer::new(&[c_huge], &objective, 2, &[false, false]).unwrap();
        assert!(!s.uses_i64());
        // rhs of i128::MIN (no i128 abs) must fail the i64 bound, not panic.
        let c_min = ge(vec![term(1, lit(1))], i128::MIN);
        assert!(!rows_fit::<i64>(std::slice::from_ref(&c_min)));
    }

    #[test]
    fn i64_and_i128_cores_produce_bit_identical_trajectories() {
        // Same instance, same seed, both widths driven through the FULL
        // pick_var/flip/bump loop (both selectors): every picked variable, λ
        // bit pattern, objective, feasibility flag, lhs vector, and score
        // vector must be IDENTICAL — the i64 fast path is a pure speed
        // change, never a trajectory change.
        for sel in [MoveSelector::Bms, MoveSelector::Bucketed] {
            let (instance, objective) = mixed_instance();
            let init = vec![false; 4];
            let mut a = core::<i64>(&instance.constraints, &objective, 4, &init, sel);
            let mut b = core::<i128>(&instance.constraints, &objective, 4, &init, sel);
            let mut rng_a = SplitMix64::new(0x1DE2_71CA_2026_F00D);
            let mut rng_b = SplitMix64::new(0x1DE2_71CA_2026_F00D);
            for step in 0..3_000 {
                let va = a.pick_var(&mut rng_a, 50, 10);
                let vb = b.pick_var(&mut rng_b, 50, 10);
                assert_eq!(va, vb, "pick divergence at step {step} ({sel:?})");
                let Some(v) = va else { break };
                a.flip(v);
                b.flip(v);
                assert_eq!(a.obj_value(), b.obj_value(), "obj divergence ({sel:?})");
                assert_eq!(
                    a.s_weight.to_bits(),
                    b.s_weight.to_bits(),
                    "λ divergence ({sel:?})"
                );
                assert_eq!(a.is_feasible(), b.is_feasible());
                let la: Vec<i128> = a.lhs.iter().map(|&x| x.to_i128()).collect();
                let lb: Vec<i128> = b.lhs.iter().map(|&x| x.to_i128()).collect();
                assert_eq!(la, lb, "lhs divergence at step {step} ({sel:?})");
                for u in 0..4 {
                    assert_eq!(
                        a.hscore[u].to_bits(),
                        b.hscore[u].to_bits(),
                        "hscore divergence ({sel:?})"
                    );
                }
            }
        }
    }

    // ---- adaptive-λ hard-lock / multiplicative-schedule tests (design §2.1) ----

    #[test]
    fn lambda_locked_at_zero_until_first_feasible_step() {
        // From an INFEASIBLE start, λ must be EXACTLY 0 at every step (flips and
        // weight bumps included) until the first feasible assignment, then jump
        // to LAMBDA_INIT and never re-lock.
        let (instance, objective) = mixed_instance();
        let init = vec![false; 4]; // violates the Eq row (lhs 5 != 3)
        let mut s = Scorer::new(&instance.constraints, &objective, 4, &init).unwrap();
        assert!(!s.is_feasible(), "test needs an infeasible start");
        assert_eq!(s.lambda(), 0.0, "λ must start hard-locked at exactly 0");

        // Weight bumps while locked must NOT move λ off 0.
        for _ in 0..5 {
            with_core_mut!(s, c => c.bump_weights());
            assert_eq!(s.lambda(), 0.0, "λ moved off 0 while hard-locked");
        }

        let mut rng = SplitMix64::new(0x1A3B_5C7D_9E0F_2468);
        let mut reached_feasible = false;
        for _ in 0..10_000 {
            let Some(v) = s.pick_var(&mut rng, 50, 10) else {
                break;
            };
            s.flip(v);
            if s.is_feasible() {
                reached_feasible = true;
                break;
            }
            assert_eq!(s.lambda(), 0.0, "λ unlocked before the first feasible step");
        }
        assert!(reached_feasible, "search never reached feasibility");
        assert_eq!(
            s.lambda(),
            LAMBDA_INIT,
            "λ must initialize to LAMBDA_INIT on first feasibility"
        );

        // Leaving the feasible region afterwards must never re-lock λ to 0.
        for v in 0..4 {
            s.flip(v);
            assert!(s.lambda() > 0.0, "λ re-locked after first feasibility");
        }
    }

    #[test]
    fn lambda_unlocks_immediately_on_feasible_seed() {
        // The polish warm-start semantics: a scorer seeded with an ALREADY
        // FEASIBLE assignment (feasible from step 0) must release the hard lock
        // at construction with λ = LAMBDA_INIT — the warm-started run does
        // objective descent immediately, not a feasibility-only search.
        let (instance, objective) = mixed_instance();
        let warm = vec![true, false, false, true]; // feasible for all three rows
        let s = Scorer::new(&instance.constraints, &objective, 4, &warm).unwrap();
        assert!(s.is_feasible(), "test seed must be feasible");
        assert_eq!(
            s.lambda(),
            LAMBDA_INIT,
            "feasible seed must unlock λ at construction"
        );
    }

    #[test]
    fn lambda_bounded_and_change_rate_clamped() {
        // Once unlocked, λ adapts multiplicatively: each stuck update changes it
        // by at most ×LAMBDA_RAISE (dwelling feasible) / ×LAMBDA_DECAY (leaving
        // feasibility), and it never exits [LAMBDA_MIN, LAMBDA_MAX].
        let (instance, objective) = mixed_instance();
        let warm = vec![true, false, false, true]; // feasible seed -> unlocked
        let mut s = Scorer::new(&instance.constraints, &objective, 4, &warm).unwrap();
        assert!(s.is_feasible());

        // Dwelling feasible: monotone multiplicative raise, clamped at LAMBDA_MAX.
        for _ in 0..200 {
            let old = s.lambda();
            with_core_mut!(s, c => c.bump_weights());
            let new = s.lambda();
            assert!(new >= old, "feasible dwell must not lower λ");
            assert!(
                new <= old * LAMBDA_RAISE * (1.0 + 1e-12),
                "raise rate exceeded the ×{LAMBDA_RAISE} clamp: {old} -> {new}"
            );
            assert!(new <= LAMBDA_MAX, "λ exceeded LAMBDA_MAX");
        }
        assert_eq!(
            s.lambda(),
            LAMBDA_MAX,
            "λ must saturate exactly at LAMBDA_MAX"
        );

        // Leave the feasible region (flip x4 breaks the Eq row), then keep
        // bumping: monotone multiplicative decay, clamped at LAMBDA_MIN.
        s.flip(3);
        assert!(!s.is_feasible(), "flip was supposed to break feasibility");
        for _ in 0..600 {
            let old = s.lambda();
            with_core_mut!(s, c => c.bump_weights());
            let new = s.lambda();
            assert!(new <= old, "infeasible dwell must not raise λ");
            assert!(
                new >= old * LAMBDA_DECAY * (1.0 - 1e-12),
                "decay rate exceeded the ×{LAMBDA_DECAY} clamp: {old} -> {new}"
            );
            assert!(new >= LAMBDA_MIN, "λ fell below LAMBDA_MIN");
        }
        assert_eq!(
            s.lambda(),
            LAMBDA_MIN,
            "λ must saturate exactly at LAMBDA_MIN"
        );
    }

    #[test]
    fn lambda_trajectory_deterministic_per_seed() {
        // Same PRNG seed => bit-identical (picked var, λ, objective, feasibility)
        // trajectory. λ compared via to_bits: exact, not approximate. Run for
        // BOTH selectors (the bucketed pick must be exactly as deterministic).
        for sel in [MoveSelector::Bms, MoveSelector::Bucketed] {
            let run = || -> Vec<(usize, u64, i128, bool)> {
                let (instance, objective) = mixed_instance();
                let init = vec![false; 4];
                let mut s = Scorer::with_selector(&instance.constraints, &objective, 4, &init, sel)
                    .unwrap();
                let mut rng = SplitMix64::new(0xD00D_FEED_0123_4567);
                let mut trajectory = Vec::new();
                for _ in 0..2_000 {
                    let Some(v) = s.pick_var(&mut rng, 50, 10) else {
                        break;
                    };
                    s.flip(v);
                    trajectory.push((v, s.lambda().to_bits(), s.obj_value(), s.is_feasible()));
                }
                trajectory
            };
            let a = run();
            let b = run();
            assert!(!a.is_empty());
            assert_eq!(
                a, b,
                "λ/search trajectory not deterministic per seed ({sel:?})"
            );
        }
    }

    /// M0 differential-fuzz gate (design §2.6): incremental lhs / violated set /
    /// objective / scores must equal from-scratch oracles over arbitrary
    /// flip+bump sequences on RANDOM instances whose Eq rows (and Ge rows) draw
    /// random NEGATED literals — the Eq-row × negated-literal slack-sign
    /// interaction the fixed `mixed_instance` fixture alone underexercises.
    /// Runs on BOTH integer widths and BOTH selectors; under the bucketed
    /// selector the bucket state is additionally checked against the goodvar
    /// predicate after every step.
    fn scorer_differential_fuzz_impl<T: ScoreInt>(sel: MoveSelector, seed: u64) {
        let mut rng = SplitMix64::new(seed);
        for round in 0..25 {
            let n = 3 + rng.below(6); // 3..=8 vars
            let rows = 2 + rng.below(4); // 2..=5 rows
            let mut constraints = Vec::new();
            for r in 0..rows {
                let k = 2 + rng.below(n - 1); // 2..=n terms
                let mut terms = Vec::new();
                let mut used = vec![false; n];
                let mut any_neg = false;
                while terms.len() < k {
                    let v = rng.below(n);
                    if used[v] {
                        continue;
                    }
                    used[v] = true;
                    let negated = rng.below(2) == 1;
                    any_neg |= negated;
                    let l = if negated {
                        neg(v as u32 + 1)
                    } else {
                        lit(v as u32 + 1)
                    };
                    terms.push(term(1 + rng.below(6) as i128, l));
                }
                if !any_neg {
                    // Guarantee EVERY row exercises the negated slack-delta sign.
                    terms[0].lits[0].negated = true;
                }
                let rhs = rng.below(3 * k) as i128 - k as i128;
                // Alternate Eq / Ge so both row kinds see negated literals.
                constraints.push(if r % 2 == 0 {
                    eq(terms, rhs)
                } else {
                    ge(terms, rhs)
                });
            }
            let objective = PbObjective {
                terms: (0..n)
                    .map(|v| {
                        let l = if rng.below(2) == 1 {
                            neg(v as u32 + 1)
                        } else {
                            lit(v as u32 + 1)
                        };
                        term(1 + rng.below(9) as i128, l)
                    })
                    .collect(),
            };
            let init: Vec<bool> = (0..n).map(|_| rng.below(2) == 1).collect();
            let mut s = core::<T>(&constraints, &objective, n, &init, sel);
            let flips = 300 + rng.below(501); // 300..=800 steps
            for step in 0..flips {
                if step % 9 == 0 {
                    s.bump_weights();
                } else if step % 5 == 0 {
                    // Drive the REAL selection path too (both selectors), so
                    // the bucketed pick sees organic dirty-set churn.
                    if let Some(v) = s.pick_var(&mut rng, 50, 10) {
                        s.flip(v);
                    }
                } else {
                    s.flip(rng.below(n));
                }
                // Exact per-row lhs: incremental == oracle over ORIGINAL rows.
                let oracle: Vec<i128> = constraints
                    .iter()
                    .map(|c| oracle_lhs(c, s.assignment()))
                    .collect();
                let got_lhs: Vec<i128> = s.lhs.iter().map(|&x| x.to_i128()).collect();
                assert_eq!(got_lhs, oracle, "lhs drift (round {round}, step {step})");
                // Violated set matches the exact shortfall oracle.
                let mut want: Vec<usize> = (0..s.lhs.len())
                    .filter(|&c| T::shortfall(s.rel[c], s.lhs[c], s.rhs[c]) > T::ZERO)
                    .collect();
                let mut got = s.violated_list.clone();
                got.sort_unstable();
                want.sort_unstable();
                assert_eq!(got, want, "violated-set drift (round {round}, step {step})");
                // Exact objective: incremental == from-scratch oracle.
                assert_eq!(s.obj_value(), eval_objective(&objective, s.assignment()));
                // Incremental scores == fresh recompute (negated-sign gradient).
                let (fh, fs) = s.fresh_scores();
                for v in 0..n {
                    assert!(
                        close(s.hscore[v], fh[v]),
                        "hscore[{v}] drift (round {round}, step {step}): inc={} fresh={}",
                        s.hscore[v],
                        fh[v]
                    );
                    assert!(
                        close(s.sscore[v], fs[v]),
                        "sscore[{v}] drift (round {round}, step {step}): inc={} fresh={}",
                        s.sscore[v],
                        fs[v]
                    );
                }
                // Bucketed selector: bucket state must exactly mirror the
                // goodvar predicate after a flush (no-op under BMS).
                s.assert_selector_in_sync();
            }
        }
    }

    #[test]
    fn scorer_differential_fuzz_eq_rows_with_random_negated_literals_i64() {
        scorer_differential_fuzz_impl::<i64>(MoveSelector::Bms, 0xE00D_0D5E_ED00_0001);
    }
    #[test]
    fn scorer_differential_fuzz_eq_rows_with_random_negated_literals_i128() {
        scorer_differential_fuzz_impl::<i128>(MoveSelector::Bms, 0xE00D_0D5E_ED00_0001);
    }
    #[test]
    fn scorer_differential_fuzz_bucketed_selector_i64() {
        scorer_differential_fuzz_impl::<i64>(MoveSelector::Bucketed, 0xB0C4_E75E_1EC7_0001);
    }
    #[test]
    fn scorer_differential_fuzz_bucketed_selector_i128() {
        scorer_differential_fuzz_impl::<i128>(MoveSelector::Bucketed, 0xB0C4_E75E_1EC7_0001);
    }

    // ---- bucketed dirty-set selector unit pins ----

    #[test]
    fn bucket_of_is_monotone_and_clamped() {
        // Monotone: a strictly larger score never lands in a strictly lower
        // bucket (so the argmax is ALWAYS in the highest non-empty bucket).
        let scores = [
            1e-12,
            1e-9,
            3e-9,
            1e-6,
            0.01,
            0.5,
            0.9,
            1.0,
            1.4,
            1.5,
            2.0,
            3.0,
            7.9,
            8.0,
            1e3,
            1e9,
            1e18,
            1e30,
            f64::MAX,
        ];
        for w in scores.windows(2) {
            assert!(
                bucket_of(w[0]) <= bucket_of(w[1]),
                "bucket_of not monotone: {} -> {}, {} -> {}",
                w[0],
                bucket_of(w[0]),
                w[1],
                bucket_of(w[1])
            );
        }
        for &s in &scores {
            assert!((bucket_of(s) as usize) < NUM_BUCKETS);
        }
        // Half-exponent granularity: 1.0 and 1.5 differ, 2.0 is higher still.
        assert!(bucket_of(1.0) < bucket_of(1.5));
        assert!(bucket_of(1.5) < bucket_of(2.0));
        // Extremes clamp instead of wrapping.
        assert_eq!(bucket_of(f64::MAX) as usize, NUM_BUCKETS - 1);
        assert_eq!(bucket_of(f64::MIN_POSITIVE), 0);
    }

    #[test]
    fn bucket_selector_membership_and_epoch_clears() {
        let mut sel = BucketSelector::new(4);
        let scores = [2.0f64, 0.0, 8.0, 8.1];
        let combined = |v: usize| scores[v];
        for v in 0..4 {
            sel.mark_dirty(v);
            sel.mark_dirty(v); // idempotent within an epoch (stamp dedups)
        }
        assert_eq!(sel.dirty.len(), 4);
        let epoch_before = sel.epoch;
        sel.flush(combined);
        // Clear = epoch bump (cp_dense idiom): dirty list emptied, epoch moved,
        // stamps intact (no reallocation, no O(n) stamp reset).
        assert!(sel.dirty.is_empty());
        assert_eq!(sel.epoch, epoch_before + 1);
        // Membership: v1 (score 0) is nowhere; v0/v2/v3 in their buckets.
        assert_eq!(sel.var_bucket[1], NO_BUCKET);
        assert_eq!(sel.var_bucket[0], bucket_of(2.0));
        assert_eq!(sel.var_bucket[2], bucket_of(8.0));
        assert_eq!(sel.var_bucket[3], bucket_of(8.1));
        assert_eq!(
            sel.var_bucket[2], sel.var_bucket[3],
            "8.0 and 8.1 share a half-octave"
        );

        // The top bucket holds the argmax; the full-scan pick returns it.
        let mut rng = SplitMix64::new(7);
        assert_eq!(sel.select(combined, &mut rng, 50), Some(3));

        // Score decay moves v3 out of the top bucket; v2 becomes the pick.
        let scores2 = [2.0f64, 0.0, 8.0, 0.5];
        sel.mark_dirty(3);
        sel.flush(|v| scores2[v]);
        assert_eq!(sel.select(|v| scores2[v], &mut rng, 50), Some(2));

        // Empty everything -> select None.
        for v in 0..4 {
            sel.mark_dirty(v);
        }
        sel.flush(|_| 0.0);
        assert_eq!(sel.select(|_| 0.0, &mut rng, 50), None);
        assert!(sel.buckets.iter().all(Vec::is_empty));
    }

    #[test]
    fn bucketed_pick_selects_from_top_gain_bucket() {
        // A star of unit Ge rows: flipping the center satisfies everything at
        // once, so its hscore dominates every leaf's. The bucketed greedy pick
        // must find the center (the argmax lives in the top bucket) — no
        // sampling luck involved (rd_prob = 0 disables diversification).
        let n = 40usize;
        let constraints: Vec<PbConstraint> = (2..=n as u32)
            .map(|leaf| ge(vec![term(1, lit(1)), term(1, lit(leaf))], 1))
            .collect();
        let objective = PbObjective {
            terms: (1..=n as u32).map(|v| term(1, lit(v))).collect(),
        };
        let init = vec![false; n];
        let mut s = core::<i64>(&constraints, &objective, n, &init, MoveSelector::Bucketed);
        let mut rng = SplitMix64::new(42);
        let picked = s.pick_var(&mut rng, 0, 8).expect("goodvars exist");
        assert_eq!(picked, 0, "bucketed pick must select the dominating center");
    }

    #[test]
    fn bucketed_selector_escapes_market_split_ridge() {
        // Selection-quality gate (mirrors the sls-level ridge test): from the
        // WORST feasible warm start of a pick-exactly-k equality, the bucketed
        // selector must cross the ridge and reach the optimum, like BMS does.
        let n = 8u32;
        let k = 3i128;
        let constraint = eq((1..=n).map(|v| term(1, lit(v))).collect(), k);
        let objective = PbObjective {
            terms: (1..=n).map(|v| term(v as i128, lit(v))).collect(),
        };
        let mut warm = vec![false; n as usize];
        warm[5] = true;
        warm[6] = true;
        warm[7] = true; // objective 6+7+8 = 21; optimum 1+2+3 = 6
        for sel in [MoveSelector::Bms, MoveSelector::Bucketed] {
            let mut s = Scorer::with_selector(
                std::slice::from_ref(&constraint),
                &objective,
                n as usize,
                &warm,
                sel,
            )
            .unwrap();
            let mut rng = SplitMix64::new(0x21D6_E000_2026_ABCD);
            let mut best = i128::MAX;
            for _ in 0..20_000 {
                let Some(v) = s.pick_var(&mut rng, 10, 50) else {
                    break;
                };
                s.flip(v);
                if s.is_feasible() {
                    best = best.min(s.obj_value());
                }
            }
            assert_eq!(best, 6, "{sel:?} must reach the ridge optimum");
        }
    }

    #[test]
    fn scorer_declines_nonlinear() {
        let constraints = vec![PbConstraint {
            terms: vec![PbTerm {
                coeff: 1,
                lits: vec![lit(1), lit(2)],
            }],
            rel: PbRel::Ge,
            rhs: 1,
        }];
        let objective = PbObjective {
            terms: vec![term(1, lit(1))],
        };
        assert!(Scorer::new(&constraints, &objective, 2, &[false, false]).is_none());
    }

    #[test]
    fn scorer_handles_empty_objective_and_no_constraints() {
        let objective = PbObjective { terms: vec![] };
        let mut s = Scorer::new(&[], &objective, 3, &[false, false, false]).unwrap();
        assert!(s.is_feasible());
        assert_eq!(s.obj_value(), 0);
        // pick_var returns None (nothing to optimize / satisfy).
        let mut rng = SplitMix64::new(1);
        assert_eq!(s.pick_var(&mut rng, 50, 10), None);
    }

    // ---- microbenchmarks (design §4 performance contract) ----
    //
    // Ignored by default: run explicitly, release build, e.g.
    //   cargo test -p ay-pb --release -j 4 --lib -- --ignored bench_ --nocapture
    // Deterministic instances and flip budgets; wall clock printed. These
    // justify (a) the MoveSelector default and (b) the i64 fast path.

    /// Deterministic synthetic instance: mixed Ge/Eq rows (every 3rd Eq),
    /// ~half negated literals, small coefficients (i64-fitting), objective
    /// over all variables.
    fn synth_mixed(
        num_vars: usize,
        rows: usize,
        row_len: usize,
        seed: u64,
        coeff_base: i128,
    ) -> (Vec<PbConstraint>, PbObjective) {
        let mut rng = SplitMix64::new(seed);
        let mut constraints = Vec::with_capacity(rows);
        for r in 0..rows {
            let mut terms = Vec::with_capacity(row_len);
            let mut sum: i128 = 0;
            for _ in 0..row_len {
                let v = rng.below(num_vars) as u32 + 1;
                let negated = rng.below(2) == 1;
                let c = coeff_base + rng.below(16) as i128;
                sum += c;
                terms.push(term(c, if negated { neg(v) } else { lit(v) }));
            }
            if r % 3 == 0 {
                constraints.push(eq(terms, sum / 2));
            } else {
                constraints.push(ge(terms, sum / 4));
            }
        }
        let objective = PbObjective {
            terms: (1..=num_vars as u32)
                .map(|v| term(1 + (v as i128 % 8), lit(v)))
                .collect(),
        };
        (constraints, objective)
    }

    fn run_flip_loop<T: ScoreInt>(
        constraints: &[PbConstraint],
        objective: &PbObjective,
        num_vars: usize,
        sel: MoveSelector,
        flips: u64,
    ) -> (f64, i128) {
        let init = vec![false; num_vars];
        let mut s = core::<T>(constraints, objective, num_vars, &init, sel);
        let mut rng = SplitMix64::new(0xBE2C_4001_2026_0711);
        let t0 = std::time::Instant::now();
        for _ in 0..flips {
            let Some(v) = s.pick_var(&mut rng, 10, 50) else {
                break;
            };
            s.flip(v);
        }
        (t0.elapsed().as_secs_f64(), s.obj_value())
    }

    #[test]
    #[ignore = "microbench: run explicitly with --ignored --nocapture (release)"]
    fn bench_bucketed_vs_bms_flip_rate() {
        println!("\n=== scorer selector flip-rate: BMS vs bucketed (i64 core) ===");
        println!(
            "{:>8} {:>9} {:>10} {:>10} {:>12} {:>12}",
            "vars", "rows", "selector", "flips", "secs", "flips/sec"
        );
        for &(num_vars, rows, flips) in &[
            (10_000usize, 20_000usize, 400_000u64),
            (100_000, 200_000, 400_000),
        ] {
            let (constraints, objective) = synth_mixed(num_vars, rows, 5, 0x5EED_0001, 1);
            for sel in [MoveSelector::Bms, MoveSelector::Bucketed] {
                let (secs, obj) =
                    run_flip_loop::<i64>(&constraints, &objective, num_vars, sel, flips);
                println!(
                    "{:>8} {:>9} {:>10} {:>10} {:>12.3} {:>12.0}   (obj {obj})",
                    num_vars,
                    rows,
                    format!("{sel:?}"),
                    flips,
                    secs,
                    flips as f64 / secs
                );
            }
        }
    }

    #[test]
    #[ignore = "microbench: run explicitly with --ignored --nocapture (release)"]
    fn bench_scorer_i64_vs_i128_flip_rate() {
        println!("\n=== scorer core flip-rate: i64 fast path vs i128 (default selector) ===");
        println!(
            "{:>8} {:>9} {:>6} {:>10} {:>12} {:>12}",
            "vars", "rows", "width", "flips", "secs", "flips/sec"
        );
        for &(num_vars, rows, flips) in &[
            (10_000usize, 20_000usize, 400_000u64),
            (100_000, 200_000, 400_000),
        ] {
            let (constraints, objective) = synth_mixed(num_vars, rows, 5, 0x5EED_0002, 1);
            let sel = MoveSelector::default();
            let (s64, o64) = run_flip_loop::<i64>(&constraints, &objective, num_vars, sel, flips);
            let (s128, o128) =
                run_flip_loop::<i128>(&constraints, &objective, num_vars, sel, flips);
            assert_eq!(o64, o128, "widths must agree on the trajectory");
            println!(
                "{:>8} {:>9} {:>6} {:>10} {:>12.3} {:>12.0}",
                num_vars,
                rows,
                "i64",
                flips,
                s64,
                flips as f64 / s64
            );
            println!(
                "{:>8} {:>9} {:>6} {:>10} {:>12.3} {:>12.0}   (speedup {:.2}x)",
                num_vars,
                rows,
                "i128",
                flips,
                s128,
                flips as f64 / s128,
                s128 / s64
            );
        }
    }
}
