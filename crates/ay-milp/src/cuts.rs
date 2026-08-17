// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Knapsack cover cuts.
//!
//! Branch-and-bound closes the 40-binary instances but pays thousands of nodes
//! for them, and node count is what cuts attack. For a row of binaries
//! `Σ a_j x_j <= b`, a *cover* is a subset `C` whose coefficients already
//! overshoot the right-hand side:
//!
//! ```text
//!   Σ_{j∈C} a_j  >  b        =>        Σ_{j∈C} x_j  <=  |C| − 1
//! ```
//!
//! — not every member of a cover can be on at once. The LP relaxation cannot see
//! this (it just sets each `x_j` to a fraction), which is precisely why the
//! relaxation is weak on knapsacks and why the tree is large.
//!
//! ## Validity is checked, not assumed
//!
//! A cut is the one thing in a MILP solver that can silently delete the optimum:
//! an invalid inequality removes integer points, and the search then proves an
//! optimum that was never there. So the cover condition `Σ_{j∈C} a_j > b` is
//! re-tested in EXACT rationals before the cut is admitted, and the greedy
//! separation below — which works in `f64` because it is only choosing WHICH
//! subset to propose — is never trusted on its own. A float that proposes a
//! non-cover produces a cut that fails the exact test and is dropped.
//!
//! Rows with negative coefficients are handled by complementing those columns
//! (`x_j -> 1 − x_j`), which turns the row into a genuine knapsack; the cut is
//! then translated back. Rows touching a continuous column are skipped: this is a
//! 0/1 argument and does not survive one.

use num_rational::BigRational;
use num_traits::Zero;

use crate::model::{exact, Col, ColKind, Model, Row};

/// A cut must be violated by at least this much to be worth its row.
///
/// # It is PRINCIPLED, and the principle is SUBSUMPTION, not numerics (measured 2026-08-01)
///
/// the development design notes lists this constant as half of
/// its sixth and last root-closure cause: "valid cuts generated and then killed entirely by
/// post-filters — the absolute nnz cap and the efficacy floor", on 6 of 65 zero-cut instances.
/// That attribution was made by reading the code. Counting it says something different.
///
/// The number itself is not defensible on its own terms: `violation` is scale-DEPENDENT, so
/// multiplying a cut through by ten multiplies its violation by ten while the inequality says
/// exactly the same thing, and `1e-4` therefore tests the cut's UNITS as much as its strength.
/// What rescues it is that nothing downstream ranks on raw violation either. The root pool ranks
/// on scale-free [`cut_depth`] and applies its own floor there (`bab::default_root_cut_eff_floor`,
/// `1e-3` or `6e-3` by shape), which for any cut with `‖a‖ >= 0.1` is the STRICTER of the two.
///
/// So the question is not how many cuts `1e-4` refuses but how many of them the pool's own floor
/// would have kept, and `sepstat::GATE_CUT_MIN_VIOLATION` counts exactly that. Over **101
/// instances** (66 spanning all three corpus tiers plus the 35-instance named/slow-prover set,
/// serial, `AY_ROOT_CLOSURE=1`, 10 s):
///
/// ```text
///   fires on                                     17 / 101 instances
///   violated cuts refused                       163
///   of which would clear the pool's DEPTH floor    3   (all on glass4)
/// ```
///
/// 160 of 163 were shallow in the only currency the pool spends. The count is not merely
/// suggestive, it BOUNDS the loss: a cut has to clear the depth floor to enter the pool at all,
/// so at most THREE cuts corpus-wide could have reached it had this filter never existed — and
/// those three are glass4's, which buy nothing (its root bound is 800002400 with them and
/// without). The arm agrees: `AY_MILP_MIN_VIOLATION=1e-12` over the 25 instances where either
/// post-filter fires moves mean root closure by **−0.01pp — zero instances better, one worse**
/// (aflow30a 12.76% → 12.56%, an extra shallow row displacing a better one), with the
/// fractional-integer-column count at the root identical on all 25.
///
/// ⚠ MEASUREMENT HYGIENE, learned the hard way in this pass: the root cut loop is
/// DEADLINE-bound (`AY_MILP_CUT_SHARE`), so `cuts` and `gain` are NOT deterministic under CPU
/// contention — three consecutive runs of the same binary on qnet1 returned 32, 28 and 21 adopted
/// cuts. A second worktree was solving on the same box. Every verdict claim in this comment and
/// in [`crate::bab::MAX_CUT_NNZ`]'s was therefore re-taken with three repetitions per arm, which
/// is how two phantom verdict "gains" (qiu, danoint) were caught and discarded. The COUNTS above
/// are robust in a way the closure deltas are not, because they are bounded by the depth floor
/// rather than by how many rounds the deadline allowed.
///
/// **Verdict: this filter forgoes nothing on real models. Left exactly as it is.** The arm stays
/// (`AY_MILP_MIN_VIOLATION`, see [`min_violation`]) so the negative result is re-derivable.
const MIN_VIOLATION: f64 = 1e-4;

/// [`MIN_VIOLATION`] as the cut-ADMISSION filters apply it, overridable for measurement with
/// `AY_MILP_MIN_VIOLATION=<f>`.
///
/// # Scope, and why it is deliberately narrow
///
/// `MIN_VIOLATION` appears at two kinds of site and only one of them is a policy. The ADMISSION
/// sites ask "is this finished cut violated enough to be worth its row" and are the ones this
/// function governs — [`clears_min_violation`], [`Cut::clean`]'s survival test, the single-row
/// flow-cover arg-max floor, the exact-cover emit test, and the whole-row screen in
/// `best_over_deltas` (whose ONLY claim is that no delta on the row can reach the admission
/// floor, so it must move with it or the arm measures a screen, not a policy).
///
/// The other sites reuse the same number as a small SLACK tolerance in a family's own geometry —
/// `slack >= 1 - MIN_VIOLATION` in the cover greedy, `weight <= 1 + MIN_VIOLATION` in the lifting
/// pass, the odd-hole `1 - MIN_VIOLATION` test, [`Cut::snap`]'s "does it still cut on this grid"
/// retry. Those are not admission decisions and are left on the constant on purpose: an arm that
/// moved them would measure four changes at once and attribute the result to one.
fn min_violation() -> f64 {
    // B25: the measurement-arm env is retired; the floor's NEGATIVE result
    // (refusing 163 cuts moved zero instances) stays re-checkable by editing
    // the constant.
    MIN_VIOLATION
}

/// The most permissive scale-free DEPTH floor the root pool ever applies
/// (`bab::default_root_cut_eff_floor`; the shape-gated arm is six times this). Used only by the
/// census below, to answer whether a cut [`MIN_VIOLATION`] refuses could have survived the filter
/// that actually governs the pool. Kept as a literal rather than a cross-module import because it
/// is a MEASUREMENT reference point, not a policy: if the pool's floor moves, this census
/// over-counts, which is the safe direction for a "what did we forgo" number.
const POOL_DEPTH_FLOOR_MIN: f64 = 1e-3;

/// Charge a fully derived, genuinely violated cut that the raw-violation floor refused.
///
/// # Why the cost is not the violation
///
/// [`MIN_VIOLATION`] is applied to `violation`, which is scale-DEPENDENT: multiply a cut through
/// by ten and its violation multiplies by ten while the inequality says exactly the same thing.
/// Nothing downstream ranks on that number — the root pool ranks on [`cut_depth`] and applies its
/// own floor there. So "how many cuts did 1e-4 refuse" is a fire rate and orders nothing (the
/// lesson of `1c1ce672c`, four families at fire rate zero and four different verdicts); the
/// decision statistic is how many of the refused cuts would ALSO have cleared the DEPTH floor,
/// i.e. how many were real capability rather than scale.
///
/// One f64 dot product plus one norm, on a cut that has already been built exactly — strictly
/// dominated by the derivation that produced it, and only on the refusal branch.
#[inline]
fn charge_min_violation(cut: &Cut, v: f64) {
    if v <= 0.0 {
        return; // a satisfied cut cost nothing: there was no capability to forgo
    }
    let norm = cut
        .coeffs
        .iter()
        .map(|&(_, a)| a * a)
        .sum::<f64>()
        .sqrt()
        .max(1e-12);
    crate::sepstat::gate_charge(
        crate::sepstat::GATE_CUT_MIN_VIOLATION,
        u64::from(v / norm >= POOL_DEPTH_FLOOR_MIN),
    );
}

/// `violation(cut, x) > MIN_VIOLATION`, with the refusal charged to the census.
///
/// Behaviourally identical to the bare comparison it replaces — same operands, same operator,
/// same order — so every measurement taken through the old spelling keeps its meaning.
#[inline]
fn clears_min_violation(cut: &Cut, x: &[f64]) -> bool {
    let v = violation(cut, x);
    if v > min_violation() {
        return true;
    }
    charge_min_violation(cut, v);
    false
}

/// The dyadic grids a cut's coefficients are rounded onto, COARSEST FIRST -- see `Cut::snap`.
/// Coarse is what keeps the exact basis cheap, so the first grid the cut can afford wins.
const SNAP_GRIDS: [i32; 5] = [6, 10, 14, 20, 26];

/// The largest basis GMI will factor EXACTLY.
///
/// # This was a MEMORY budget wearing a time budget's docstring, and it cost 63% of the corpus
///
/// It read 600 from 2026-07-14 (`b68d10a18`) to 2026-08-01, and that number was never measured.
/// `b68d10a18` diagnosed GMI as having wrongly inherited `certify::MAX_EXACT_BASIS_ROWS` -- "two
/// jobs, two costs, two caps" -- then created this function and left the inherited literal
/// unchanged. The cost that motivated a cap was fixed by a DIFFERENT bug in the same commit
/// (`Cut::snap`, which flattened separation to mod010 0.88 / 0.84 / 0.95s), so the cap was never
/// remeasured against the code that shipped.
///
/// The docstring it carried called this a TIME budget -- "its LU is dense and cubic and runs once
/// per cut ROUND". At 600 it denied EXACT-BASIS GMI, the primary cut family, to **238 of 379 MIPLIB
/// instances (63%)**, on a front where root closure is the single largest measured gap to Gurobi
/// (7.02% against 54.69%). A full cost-curve study over 173 uncapped calls says the time reading
/// was WRONG on every count:
///
/// * **No cheap quantity predicts the time.** Spearman rho against LU-factor seconds: `m` +0.82,
///   `m·n` +0.69, nonbasic count +0.52, `nnz` +0.45 -- every proposed replacement is WORSE than `m`,
///   and `m` is useless for MAGNITUDE. Within `m ∈ [900,1400]` factor time spans 0.0007s to 0.2897s
///   (414x); the most expensive factorisation in the whole sweep was at **m=996 (1.0437s)**, and
///   m=2313 factored in 0.0232s (m=4554 costs 0.044s). Measured over 27 bases the same ordering
///   fails again: inside `m ∈ [930,1130]` the LU spans 0.0017s to 1.044s, 614x at fixed `m`.
///   `ExactLu::factor_with_deadline` skips exact zeros, so its cost tracks fill-in and bit growth,
///   and no function of `m` orders those.
/// * **Every expensive factorisation sat BELOW any middling cap**, so the cap never protected
///   against one.
/// * **The deadline already governs the time, and was measured doing it**: 28 of the 173 uncapped
///   calls aborted inside `ExactLu::factor_with_deadline`, worst overrun anywhere 1.0437s.
/// * **The exemplars were stale**: air05 (426 rows) now factors in 0.0033s and its whole GMI share
///   is ~0.57s, not the 11.2s the note quoted.
///
/// What `m` really governed was one line: `vec![vec![Rational::zero(); m]; m]`, O(m²) and
/// unconditional, built from a SPARSE basis and allocated BEFORE the deadline was consulted -- at
/// 36 B/entry that is 4.26 GB at m=10765 and 9.51 GB at m=16381, and THAT is the cost the cap was
/// really bounding. Measured peak RSS against the sparse assembly that replaced it
/// (`--dense-gmi-lu` restores the old one), 3 repetitions each: 50 MB vs 19 MB at m=1048,
/// 186 MB vs 17 MB at m=2527, 1861 MB vs 57 MB at m=6558, and **3329 MB vs 78 MB at m=10765** --
/// 43x, with the dense arm tracking m² (66x the bytes for 10.3x the rows) and the sparse arm
/// essentially flat. On the corpus's largest model (169,576 rows) the dense assembly is ~1 PB.
/// See [`SparseExactLu`] for the full table and the per-repetition spread.
///
/// # The intermediate step: 600 -> 2000, and why its limits no longer bind
///
/// Before the sparse assembly existed the cap was raised to 2000 == 144 MB worst case, the memory
/// budget expressed in the units the dense code had. GATED, 15s solves, arms interleaved
/// back-to-back in one serial worker, checked against MIPLIB references and cross-checked against
/// `~/ay-bench/milp/Highs.log`:
///   * ALL 73 corpus instances whose row count lies in (600, 2000] -- the complete population where
///     that cap binds differently from 600: verdicts GAINED 1, LOST 0, soundness alarms 0.
///   * 26 tightest-gap in-band instances re-run at 60s: GAINED 1, LOST 0, alarms 0.
///   * 62 controls (both arms gated identically): 0 verdicts gained, 0 lost.
/// The gain was `haprp` (m=1048), and it is the SAME gain the 12000 A/B re-measures below. That
/// study's honest limit was that its verdict evidence justified only `>= 1048`, and that the
/// bands above bought zero verdicts at 15s and 60s; do not read the bound/incumbent deltas as
/// support, because 62 control pairs running IDENTICAL code differed on 15 of them (24%),
/// including one status change and a dual bound moving -109,730 -> -1,300,747. The one
/// reproducible COST recorded there is primal: `neos2` (m=1103) incumbent 488.77 -> 1043.47, 3/3
/// deterministic, against a 454.86 reference. Root closure is not the scoreboard and does not
/// track the win -- haprp's own root gain FELL (7042 -> 5659 in an earlier sweep) while its verdict
/// rose; over 40 in-band instances closure went up on 16, down on 5, flat on 19.
///
/// # What the number is now
///
/// A BACKSTOP, and no longer the memory guard: [`SparseExactLu`]'s fill budget bounds the
/// factorization's bytes DIRECTLY (it counts entries, the thing it is protecting, rather than
/// proxying them by a row count), and the deadline bounds its time. What is left scaling with `m` is
/// the per-cut `e`/`u` dense rational vectors and the separator's O(m) bookkeeping -- linear, and
/// small next to the O(nnz) work per cut. So the cap exists to stop a basis so large that the
/// SEPARATOR's own linear costs stop being noise, not to stop the factorization. This is the
/// durable fix the 2000-era note asked for ("gate on `36 * m * m <= budget` and let the deadline own
/// the time"), except that counting entries beats any `m`-shaped proxy for them.
///
/// KILL SWITCH: `the gmi-max-rows knob` (registered in `knobs.rs`, bucket `Tuning`) sets this at
/// runtime; `the gmi-max-rows knob=600` restores the pre-2026-08-01 behaviour exactly, and
/// `--dense-gmi-lu` restores the dense assembly independently.
fn gmi_max_basis_rows() -> usize {
    crate::tune::count_opt(crate::tune::Knob::GmiMaxRows).unwrap_or(DEFAULT_GMI_MAX_BASIS_ROWS)
}

/// See [`gmi_max_basis_rows`]. VALUE SET BY A/B, not by the memory argument: the memory argument
/// only says the cap CAN rise, and this campaign has twice measured that more cuts is not better
/// (seven verdicts lost to a bigger cut budget, five to a PERFECT root bound that made trees 1.72x
/// bigger). 12000 is what the corpus A/B admitted, and it is where the evidence stops -- nothing
/// above it has been measured, so nothing above it is claimed.
///
/// # The A/B, both sides of it
///
/// 70 instances (40 gurobi / 20 mid / 10 large, all with `rows > 600`), 15s, SERIAL, three arms one
/// binary apart: A0 = 600 + the old dense `Bᵀ` (`--dense-gmi-lu`), A1 = 600 + sparse,
/// A2 = 12000 + sparse. Every headline below was RE-TAKEN at 3 repetitions; the gate pass itself is
/// a screen, not the evidence, because it is one observation per cell.
///
/// * **A0 -> A2: +1 verdict, -0, 0 soundness alarms.** The gain is `haprp` (m=1048), FEASIBLE ->
///   OPTIMAL at 3673280.681685. It is not a budget squeak: at 60s and 3 repeats it proves 3/3 at
///   **exactly 31,609 nodes every time** (12.9s / 16.2s / 18.0s of a heavily loaded box -- wall
///   moves, nodes-to-proof does not), while cap 600 fails to prove 6/6 at 60s having reached
///   94,842 to 116,724 nodes. The cap is buying a SMALLER TREE, not more clock. The value is NOT
///   the manifest's (3673280.6808, off by 2.4e-10); it agrees with HiGHS's proved optimum
///   3673280.68169 to 12 significant figures, so the manifest is the outlier -- cross-checked
///   against `~/ay-bench/milp/Highs.log`, per the standing rule that the manifest is not ground
///   truth.
/// * **A0 -> A1 is the representation change alone and moves NOTHING that reproduces.** The one
///   verdict it appeared to lose (`app1-1`) separates ZERO GMI cuts in every arm, and 9 repeats
///   produced 9 non-proofs with node counts from 21 to 60 at the same budget: a wall-clock-budget
///   instance on a loaded box, not a regression. The load-invariant statistic says the same thing
///   the other way: on the two instances that PROVE, nodes-to-proof is EQUAL to the node --
///   `rout` 15,328 = 15,328 and `misc07` 7,491 = 7,491 -- which is what "same cuts" looks like from
///   the search's side.
///
/// # What it costs, named -- and ONLY what survived repetition
///
/// The root cut loop is DEADLINE-bound, so a single 15s observation is not a result: six of the
/// gate's per-instance movements were re-run at 3 repetitions per arm and **two of the four
/// primal ones evaporated** (`fiball`'s gained incumbent and `p200x1188c`'s lost optimum were both
/// the box, not the cap). What is left, at 3/3:
///
/// * `beasleyC2` (m=1750) gets a REPRODUCIBLY WORSE incumbent: 308/308/308 at 12000 against
///   256/256/256 at 600 (optimum 144), on MORE nodes (5385-5543 against 3955-4059).
/// * `n5-3` (m=1062) gets a WEAKER dual bound (4573-4589 against 4664-4708) on 10x fewer nodes
///   (205-227 against 623-1039).
/// * `qiu` (m=1192) explores 528-734 nodes at 12000 against 1221-6171 at 600, a 3x loss of
///   throughput. Its incumbent lands at the worst end of a spread cap 600 ALREADY had (-110.84,
///   where 600 ranged -110.84 to the optimum -132.873 across repeats), so the node loss is the
///   finding and the incumbent is not.
///
/// What it buys, at 3/3: `nsa` (m=1297) REACHES its optimum -- 120/120/120 at 12000 against
/// 123/123/123 at 600 -- and `haprp` proves. The one-shot movements on `graphdraw-domain`,
/// `supportcase26`, `g200x740`, `bg512142`, `n3div36`, `mtest4ma`, `tr12-30`, `nu25-pr12`,
/// `neos-3610173-itata` and `neos-1430701` are recorded in the gate JSON and are deliberately NOT
/// claimed here, because the two of that class that were tested did not reproduce.
///
/// The shape of the trade is consistent: the cap raise buys BOUND QUALITY PER NODE and pays for it
/// in NODE THROUGHPUT, since every adopted row is charged at every node below it. It wins where the
/// tree is bound-limited (haprp: 31,609 nodes to proof against >116,724 without) and loses where
/// the tree is throughput-limited (qiu, n5-3).
///
/// `noswot`, `misc07`, `fiball` and `app1-1` are unaffected either way -- they separate the SAME
/// cuts (8, 12, 0 and 0) at both caps, because their bases never reach 600 in the first place.
const DEFAULT_GMI_MAX_BASIS_ROWS: usize = 12000;

/// Kill switch for the fused multiply-add / clone-elided form of the exact GMI
/// back-solve dot products (`separate_gmi_budget`). The fused path computes the
/// SAME exact rational values (`Rational` canonicalises to a unique reduced
/// form) with fewer GCD reductions and no throwaway heap clones; set
/// `--no-cut-fma` to fall back to the literal `acc += a.clone() * b`
/// form for an A/B byte-identity check. Default: fused (enabled).
#[inline]
fn cut_fma_enabled() -> bool {
    crate::tune::caller_flag(crate::tune::Knob::NoCutFma).map_or(true, |no| !no)
}

/// How many c-MIR scalings to try per row. See the note at its use: the delta IS the cut.
const MAX_DELTAS: usize = 12;

/// The largest coefficient (or right-hand side) a cut may carry. See the fractionality guard in
/// `mir_round`: past this the cut is a wrecked basis, not an inequality.
const MAX_CUT_COEFF: f64 = 1e7;

/// The widest spread of coefficient magnitudes a cut may have.
const MAX_CUT_DYNAMISM: f64 = 1e8;

/// The fraction of a cut's violation that may be spent on sparsifying it. See [`Cut::clean`].
pub(crate) const CLEAN_BUDGET: f64 = 0.1;

/// One separated cut: `lb <= coeffs·x <= ub`.
#[derive(Clone)]
pub(crate) struct Cut {
    pub coeffs: Vec<(Col, f64)>,
    pub lb: f64,
    pub ub: f64,
}

impl Cut {
    /// SPARSIFY: drop the coefficients that are noise, and pay for them in the right-hand side.
    ///
    /// A GMI row comes out of the tableau with whatever the tableau had in it, and on a real model
    /// that is dense and ragged -- on rout, 294 to 438 non-zeros out of 556 columns, with magnitudes
    /// running from 3e-5 up to 2. Most of those terms carry no information; what they carry is
    /// FILL-IN, and the relaxation has to be re-solved with them at every round of the cut loop and
    /// at every node after it. Measured: with the raw rows, a rout cut round takes five seconds on
    /// an LP that solves in one hundredth of one without them.
    ///
    /// Dropping a term cannot invalidate the cut PROVIDED the right-hand side is relaxed by the most
    /// that term could ever have contributed over the column's box:
    ///
    /// ```text
    ///   Σ_kept a_j x_j  =  Σ_all a_j x_j − Σ_dropped a_j x_j
    ///                  <=  ub            − Σ_dropped min over the box of a_j·x_j
    /// ```
    ///
    /// so the weakened cut is IMPLIED by the original and every integer point still satisfies it. A
    /// column with an unbounded side cannot be paid for, so its term stays.
    ///
    /// (This was written once before and reverted as "neutral" -- correctly, because there was no
    /// cut LOOP for it to matter to. With one, it is what makes the loop affordable.)
    /// BOUND THE DENOMINATORS, or the exact rim pays for the float lane's noise.
    ///
    /// A cut coefficient is an `f64`, and the exact rim reads it with `BigRational::from_float` --
    /// EXACTLY. So a perfectly ordinary GMI coefficient like `0.4166666666666667` does not enter
    /// the exact basis as `5/12`; it enters as a 55-bit numerator over `2^52`. The model's own rows
    /// are small integers (the MPS reader scales them so), and exact Gaussian elimination has
    /// ENTRY GROWTH: the bit-length of the LU's internal entries accumulates along the pivot chain.
    /// Feed it a handful of 55-bit rows and the entries reach thousands of bits.
    ///
    /// That is what made the cut loop unaffordable, and it is worth being precise about the shape,
    /// because it looked for a long time like a complexity problem and it is not one. On mod010 --
    /// 146 rows, so the basis barely moves -- separation went 0.87s, 11.04s, 29.36s over three
    /// rounds. Round one factors original rows only, and it is cheap. Round two puts THIRTEEN cut
    /// rows into the same 146-row basis and costs twelve times as much. The matrix did not grow.
    /// The NUMBERS did.
    ///
    /// So round every coefficient onto a dyadic grid, which caps its denominator at `2^b`, and pay
    /// for the change out of the cut's own violation, exactly as `clean` pays for a dropped term:
    /// moving `a_j` to `ã_j` shifts the row's activity by `δ_j · x_j`, which over the column's box
    /// is at least `min(δ_j·lo, δ_j·up)`, so a `≥` cut whose right-hand side is lowered by the sum
    /// of those minima is IMPLIED by the original -- every point the original admits, this admits.
    /// Validity does not depend on the grid, only on paying for it, so the grid is free to be
    /// coarse; `mir_cuts_never_remove_an_integer_point` covers the payment.
    ///
    /// The grid is chosen per cut: coarsest first, and the first one that still leaves the cut
    /// cutting wins. A column with an unbounded side cannot be paid for, so its coefficient is left
    /// exact -- one such term costs one wide row, not the whole basis.
    pub(crate) fn snap(&mut self, model: &Model, x: &[f64], budget: f64) -> bool {
        let viol = violation(self, x);
        if viol <= 0.0 {
            return false;
        }
        let allowance = budget * viol;

        for &bits in &SNAP_GRIDS {
            let grid = (2.0f64).powi(bits);
            let mut snapped: Vec<(Col, f64)> = Vec::with_capacity(self.coeffs.len());
            let (mut pay_lb, mut pay_ub) = (0.0f64, 0.0f64);
            let mut cost = 0.0f64;

            for &(c, a) in &self.coeffs {
                let (lo, up) = model.col_bounds(c);
                if !lo.is_finite() || !up.is_finite() {
                    snapped.push((c, a)); // cannot be paid for: leave it exact
                    continue;
                }
                // `a * grid` is exact (a power of two), so `round` and the divide are too: the
                // snapped value is a true multiple of `2^-bits` and its denominator really is bounded.
                let scaled = a * grid;
                if !scaled.is_finite() || scaled.abs() >= 9.0e15 {
                    snapped.push((c, a)); // too big to snap without losing the grid: leave it
                    continue;
                }
                let sa = scaled.round() / grid;
                let d = sa - a;
                if d != 0.0 {
                    let (p, q) = (d * lo, d * up);
                    pay_lb += p.min(q); // the least the change can add to the activity
                    pay_ub += p.max(q); // the most it can
                    cost += (d * lo).abs().max((d * up).abs());
                }
                if sa != 0.0 {
                    snapped.push((c, sa));
                }
            }

            if snapped.is_empty() || cost > allowance {
                continue; // too coarse to afford; try a finer grid
            }

            let mut trial = Cut {
                coeffs: snapped,
                lb: self.lb,
                ub: self.ub,
            };
            // Pay for it, and give the payment a hair of slack so that no rounding in the SUM above
            // can leave the right-hand side a bit stronger than the box argument justifies.
            if trial.lb.is_finite() {
                trial.lb += pay_lb - 1e-12 * (1.0 + trial.lb.abs());
            }
            if trial.ub.is_finite() {
                trial.ub += pay_ub + 1e-12 * (1.0 + trial.ub.abs());
            }
            if violation(&trial, x) <= MIN_VIOLATION {
                continue; // it no longer cuts on this grid; try a finer one
            }
            *self = trial;
            return true;
        }
        true // no grid was affordable: keep it exact, and pay for it in the basis
    }

    pub(crate) fn clean(&mut self, model: &Model, x: &[f64], budget: f64) -> bool {
        // SPARSIFY AGAINST A DAMAGE BUDGET, NOT A COEFFICIENT THRESHOLD.
        //
        // The old rule dropped a term when its coefficient fell below 1e-4 of the largest, which on
        // a GMI or MIR row drops essentially nothing: they come out of the tableau at 300-400
        // non-zeros with magnitudes spread over four orders, and almost every one clears that bar.
        // So the cuts stayed dense, and dense is what the LP cannot carry -- four hundred of these
        // rows and the float simplex returns a bound of ZERO.
        //
        // What matters is not how small a coefficient is but how much DROPPING it can cost. A term
        // can contribute at most `|a_j| · max|x_j|` over the column's box, and the right-hand side
        // must be relaxed by that much to keep the cut implied by the original. So spend that as a
        // BUDGET, taken as a fraction of the violation the cut currently has: drop the cheapest
        // terms first, and stop before the relaxation eats the cut. What survives is guaranteed
        // still violated -- by at least `1 − budget` of what it was.
        //
        // Returns whether the cut still cuts.
        let act: f64 = self
            .coeffs
            .iter()
            .map(|&(c, a)| a * x.get(c.index()).copied().unwrap_or(0.0))
            .sum();
        let viol = if self.ub.is_finite() {
            act - self.ub
        } else {
            self.lb - act
        };
        if viol <= 0.0 {
            return false;
        }
        let mut allowance = budget * viol;

        // Cheapest-to-drop first: the most a term could ever have been worth.
        let mut order: Vec<usize> = (0..self.coeffs.len()).collect();
        let worth = |i: usize, coeffs: &Vec<(Col, f64)>| -> f64 {
            let (c, a) = coeffs[i];
            let (lo, up) = model.col_bounds(c);
            if !lo.is_finite() || !up.is_finite() {
                return f64::INFINITY; // cannot be paid for: never drop it
            }
            ((a * lo).abs()).max((a * up).abs())
        };
        order.sort_by(|&i, &j| {
            worth(i, &self.coeffs)
                .partial_cmp(&worth(j, &self.coeffs))
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        let mut drop = vec![false; self.coeffs.len()];
        let (mut pay_ub, mut pay_lb) = (0.0f64, 0.0f64);
        for &i in &order {
            let w = worth(i, &self.coeffs);
            if !w.is_finite() || w > allowance {
                break; // the rest cost at least as much; nothing more is affordable
            }
            let (c, a) = self.coeffs[i];
            let (lo, up) = model.col_bounds(c);
            drop[i] = true;
            allowance -= w;
            pay_ub += (a * lo).min(a * up); // the least it could have contributed
            pay_lb += (a * lo).max(a * up); // the most it could have contributed
        }
        if !drop.iter().any(|&d| d) {
            return true;
        }
        let mut kept = Vec::with_capacity(self.coeffs.len());
        for (i, &t) in self.coeffs.iter().enumerate() {
            if !drop[i] {
                kept.push(t);
            }
        }
        if kept.is_empty() {
            return false;
        }
        self.coeffs = kept;
        if self.ub.is_finite() {
            self.ub -= pay_ub;
        }
        if self.lb.is_finite() {
            self.lb -= pay_lb;
        }
        // It must still cut, or it is only fill-in.
        let act: f64 = self
            .coeffs
            .iter()
            .map(|&(c, a)| a * x.get(c.index()).copied().unwrap_or(0.0))
            .sum();
        let v = if self.ub.is_finite() {
            act - self.ub
        } else {
            self.lb - act
        };
        if v <= min_violation() {
            // Charged like every other refusal, but note what `clean` can and cannot cost: it
            // spends at most `budget` (0.1) of the violation the cut arrived with, so a row that
            // falls through here arrived at 1.11e-4 or less and was ALREADY within a hair of the
            // floor. The sparsifier does not turn a deep cut into a shallow one.
            charge_min_violation(self, v);
            return false;
        }
        true
    }
}

/// Separate cover cuts for `model` violated by the LP point `x`.
///
/// `x` is the float relaxation point — advice, used only to pick which covers to
/// look for. Every cut returned has had its cover condition proven exactly.
pub(crate) fn separate(model: &Model, x: &[f64]) -> Vec<Cut> {
    let mut cuts = Vec::new();
    for r in 0..model.num_rows() {
        let row = Row(r as u32);
        let (coeffs, lb, ub) = model.row(row);
        if coeffs.is_empty() {
            continue;
        }
        // BOTH orientations of the row are knapsack views. The `<=` side is the
        // classic one; the `>=` side (`Σ a·x >= lb  ⟺  Σ(−a)·x <= −lb`) feeds the
        // SAME complement machinery below and was previously SKIPPED outright —
        // measured on the weighted-domination family (`Σ_{v∈N[u]} x_v >= 1`, 470
        // covering rows): the separator generated ZERO cuts and the dual crawled;
        // covering rows are exactly where cover cuts live. An Eq row is two views.
        if ub.is_finite() {
            separate_cover_view(model, x, coeffs, ub, &mut cuts);
        }
        if lb.is_finite() {
            let neg: Vec<(u32, f64)> = coeffs.iter().map(|&(c, a)| (c, -a)).collect();
            separate_cover_view(model, x, &neg, -lb, &mut cuts);
        }
    }
    if crate::tune::caller_flag(crate::tune::Knob::ModK) == Some(true) {
        cuts.extend(separate_covering_modk(model, x));
    }
    cuts
}

/// PROTOTYPE mod-k Chvátal-Gomory covering-aggregation cut. See design note at
/// the module tail. Sound: aggregate ≥-covering rows, relax continuous columns
/// to their upper bound, then mod-k round the pure-integer residual.
fn separate_covering_modk(model: &Model, x: &[f64]) -> Vec<Cut> {
    // The separator classifies coefficients and right-hand sides as integers,
    // then performs CG rounding, entirely through the f64 matrix. When the
    // model carries exact-rational overrides those values are only proxies and
    // may sit on the other side of an integer boundary. Decline until the
    // derivation consumes the exact side store directly.
    if model.has_inexact_coeffs() {
        return Vec::new();
    }
    let nr = model.num_rows();
    struct CRow {
        cols: Vec<u32>,
        a: Vec<i64>,
        b: i64,
        act: f64,
    }
    let mut rows: Vec<CRow> = Vec::new();
    for r in 0..nr {
        let row = model.row_at(r).unwrap();
        let (coeffs, lb, _ub) = model.row(row);
        if coeffs.is_empty() || !lb.is_finite() {
            continue;
        }
        let mut ok = (lb - lb.round()).abs() < 1e-6;
        let mut cols = Vec::with_capacity(coeffs.len());
        let mut av = Vec::with_capacity(coeffs.len());
        let mut act = 0.0f64;
        for &(c, a) in coeffs {
            if a <= 0.0 || (a - a.round()).abs() > 1e-6 {
                ok = false;
                break;
            }
            cols.push(c);
            av.push(a.round() as i64);
            act += a * x.get(c as usize).copied().unwrap_or(0.0);
        }
        if !ok {
            continue;
        }
        rows.push(CRow {
            cols,
            a: av,
            b: lb.round() as i64,
            act,
        });
    }
    if rows.len() < 2 {
        return Vec::new();
    }
    let n = model.num_cols();
    let is_int = |c: u32| !matches!(model.col_kind(Col(c)), ColKind::Continuous);
    let ub_of = |c: u32| model.col_bounds(Col(c)).1;

    let build = |acc: &[i64], bsum: i64, k: i64| -> Option<Cut> {
        if k < 2 {
            return None;
        }
        let mut bprime = bsum as f64;
        for (j, &aj) in acc.iter().enumerate() {
            if aj == 0 {
                continue;
            }
            if is_int(j as u32) {
                // The mod-k CG rounding below replaces `a_j/k` by its CEILING.
                // That implication needs x_j >= 0: multiplying a larger
                // coefficient by a negative integer reverses the comparison.
                // A shifted derivation could retain such columns, but until it
                // also carries the shift into the RHS, decline the whole cut.
                if model.col_bounds(Col(j as u32)).0 < 0.0 {
                    return None;
                }
            } else {
                let u = ub_of(j as u32);
                if !u.is_finite() {
                    return None;
                }
                bprime -= aj as f64 * u;
            }
        }
        let rhs = (bprime / k as f64 - 1e-9).ceil();
        if rhs < 1.0 {
            return None;
        }
        let mut out: Vec<(Col, f64)> = Vec::new();
        for (j, &aj) in acc.iter().enumerate() {
            if aj == 0 || !is_int(j as u32) {
                continue;
            }
            let coef = ((aj as f64) / (k as f64)).ceil();
            if coef != 0.0 {
                out.push((Col(j as u32), coef));
            }
        }
        if out.is_empty() {
            return None;
        }
        Some(Cut {
            coeffs: out,
            lb: rhs,
            ub: f64::INFINITY,
        })
    };

    let mut order: Vec<usize> = (0..rows.len()).collect();
    order.sort_by(|&i, &j| {
        (rows[i].act - rows[i].b as f64)
            .partial_cmp(&(rows[j].act - rows[j].b as f64))
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    // B11: compiled constant (the the mod-k knob_SEEDS override nothing set is
    // retired).
    const MODK_SEED_CAP: usize = 40;
    let cap = MODK_SEED_CAP.min(rows.len());
    let seeds = &order[..cap];

    let mut cuts: Vec<Cut> = Vec::new();
    let mut acc = vec![0i64; n];
    let add_row = |acc: &mut [i64], r: &CRow, sign: i64| {
        for (idx, &c) in r.cols.iter().enumerate() {
            acc[c as usize] += sign * r.a[idx];
        }
    };
    let ks: [i64; 5] = [2, 3, 4, 5, 6];
    for a in 0..seeds.len() {
        for b in (a + 1)..seeds.len() {
            let (ri, rj) = (seeds[a], seeds[b]);
            add_row(&mut acc, &rows[ri], 1);
            add_row(&mut acc, &rows[rj], 1);
            let bsum = rows[ri].b + rows[rj].b;
            for &k in &ks {
                if let Some(c) = build(&acc, bsum, k) {
                    if clears_min_violation(&c, x) {
                        cuts.push(c);
                    }
                }
            }
            add_row(&mut acc, &rows[ri], -1);
            add_row(&mut acc, &rows[rj], -1);
        }
    }
    // B11: compiled constant (the the mod-k knob_TRI override nothing set is
    // retired).
    const MODK_TRI_CAP: usize = 20;
    let tri_cap = MODK_TRI_CAP.min(seeds.len());
    for a in 0..tri_cap {
        for b in (a + 1)..tri_cap {
            for cc in (b + 1)..tri_cap {
                let (ri, rj, rk) = (seeds[a], seeds[b], seeds[cc]);
                add_row(&mut acc, &rows[ri], 1);
                add_row(&mut acc, &rows[rj], 1);
                add_row(&mut acc, &rows[rk], 1);
                let bsum = rows[ri].b + rows[rj].b + rows[rk].b;
                for &k in &ks {
                    if let Some(c) = build(&acc, bsum, k) {
                        if clears_min_violation(&c, x) {
                            cuts.push(c);
                        }
                    }
                }
                add_row(&mut acc, &rows[ri], -1);
                add_row(&mut acc, &rows[rj], -1);
                add_row(&mut acc, &rows[rk], -1);
            }
        }
    }
    cuts.sort_by(|a, b| {
        efficacy(b, x)
            .partial_cmp(&efficacy(a, x))
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    cuts.truncate(60usize);
    cuts
}

#[cfg(test)]
mod modk_tests {
    use super::*;
    use crate::model::Sense;

    #[test]
    fn covering_modk_cuts_never_remove_an_integer_point() {
        let mut seed = 0x9e37_79b9_u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };
        const NBIN: usize = 6;
        const NCON: usize = 2;
        let n = NBIN + NCON;
        let mut fired = 0usize;
        for _case in 0..400 {
            let mut m = Model::new();
            let bins: Vec<Col> = (0..NBIN).map(|_| m.add_binary_col()).collect();
            let cons: Vec<Col> = (0..NCON).map(|_| m.add_col(0.0, 1.0)).collect();
            let all: Vec<Col> = bins.iter().chain(cons.iter()).copied().collect();
            let mut rows: Vec<(Vec<usize>, i64)> = Vec::new();
            for _r in 0..4 {
                let mut mem: Vec<usize> = Vec::new();
                for j in 0..n {
                    if rnd() % 100 < 60 {
                        mem.push(j);
                    }
                }
                if mem.len() < 2 {
                    continue;
                }
                let b = 1 + rnd() % (mem.len() as i64);
                let terms: Vec<(Col, f64)> = mem.iter().map(|&j| (all[j], 1.0)).collect();
                m.add_row(b as f64, f64::INFINITY, &terms);
                rows.push((mem, b));
            }
            if rows.len() < 2 {
                continue;
            }
            m.set_objective(&[(bins[0], 1.0)], Sense::Minimize);
            let xv: Vec<f64> = (0..n).map(|_| (rnd() % 101) as f64 / 100.0).collect();
            let cuts = separate_covering_modk(&m, &xv);
            fired += cuts.len();
            let grid = [0.0f64, 0.25, 0.5, 0.75, 1.0];
            for code in 0..(1u32 << NBIN) {
                let bvals: Vec<f64> = (0..NBIN).map(|t| f64::from((code >> t) & 1)).collect();
                let mut idxs = [0usize; NCON];
                loop {
                    let mut p = vec![0.0f64; n];
                    p[..NBIN].copy_from_slice(&bvals[..NBIN]);
                    for j in 0..NCON {
                        p[NBIN + j] = grid[idxs[j]];
                    }
                    let feasible = rows.iter().all(|(mem, b)| {
                        let act: f64 = mem.iter().map(|&j| p[j]).sum();
                        act >= *b as f64 - 1e-9
                    });
                    if feasible {
                        for c in &cuts {
                            let act: f64 = c.coeffs.iter().map(|&(j, a)| a * p[j.index()]).sum();
                            assert!(
                                act >= c.lb - 1e-7,
                                "mod-k cut deleted a feasible point: {act} < {}",
                                c.lb
                            );
                        }
                    }
                    let mut carry = 1;
                    for d in 0..NCON {
                        idxs[d] += carry;
                        if idxs[d] >= grid.len() {
                            idxs[d] = 0;
                        } else {
                            carry = 0;
                            break;
                        }
                    }
                    if carry == 1 {
                        break;
                    }
                }
            }
        }
        assert!(fired > 0, "the mod-k sweep never produced a cut");
    }

    /// Ceil-rounding `(x + 2y >= 1) / k` without first shifting a
    /// negative-lower-bound integer is invalid: aggregating the row twice and
    /// taking k=4 yields `x + y >= 1`, which deletes the feasible integer point
    /// `x=-1, y=1`. The nonnegative control proves separation is live; the
    /// negative-box model must fail closed.
    #[test]
    fn covering_modk_declines_negative_integer_lower_bounds() {
        let build = |x_lb: f64| {
            let mut m = Model::new();
            let x = m.add_int_col(x_lb, 1.0);
            let y = m.add_binary_col();
            for _ in 0..2 {
                m.add_row(1.0, f64::INFINITY, &[(x, 1.0), (y, 2.0)]);
            }
            m.set_objective(&[(x, 1.0)], Sense::Minimize);
            m
        };

        let nonnegative = build(0.0);
        assert!(
            !separate_covering_modk(&nonnegative, &[0.0, 0.0]).is_empty(),
            "the nonnegative control must exercise mod-k rounding"
        );

        let negative = build(-1.0);
        let feasible = [-1.0, 1.0];
        for r in 0..negative.num_rows() {
            let (coeffs, lb, _) = negative.row(Row(r as u32));
            let act: f64 = coeffs.iter().map(|&(c, a)| a * feasible[c as usize]).sum();
            assert!(act >= lb, "the exposing point must be model-feasible");
        }
        assert!(
            separate_covering_modk(&negative, &feasible).is_empty(),
            "mod-k must decline until negative integer columns are shifted soundly"
        );
    }

    /// The mod-k integer tests and rounding must never inspect an f64 proxy
    /// when the model carries a different exact row. Keep the guard
    /// non-vacuous by proving that the same proxy matrix separates before the
    /// exact lower-bound overrides are installed.
    #[test]
    fn covering_modk_fails_closed_on_exact_side_store_models() {
        let mut m = Model::new();
        let x = m.add_int_col(0.0, 1.0);
        let y = m.add_binary_col();
        let mut rows = Vec::new();
        for _ in 0..2 {
            rows.push(m.add_row(1.0, f64::INFINITY, &[(x, 1.0), (y, 2.0)]));
        }
        m.set_objective(&[(x, 1.0)], Sense::Minimize);
        let point = [0.0, 0.0];
        assert!(
            !separate_covering_modk(&m, &point).is_empty(),
            "the exact proxy-matrix control must exercise mod-k separation"
        );

        // 1 - 2^-54 rounds to the stored f64 proxy 1.0. The separator must not
        // classify or round that proxy as though it were the true rational RHS.
        let eps = BigRational::new(1_i64.into(), 18_014_398_509_481_984_i64.into());
        let true_lb = BigRational::from_integer(1_i64.into()) - eps;
        for row in rows {
            m.record_inexact_row_bound(row, true, true_lb.clone());
        }
        assert!(m.has_inexact_coeffs());
        assert!(
            separate_covering_modk(&m, &point).is_empty(),
            "mod-k must fail closed instead of rounding f64 proxy rows"
        );
    }
}

/// Whether `separate_cover_view` reduces its greedy cover to a MINIMAL cover
/// before lifting. DEFAULT-OFF: the reduction is sound and produces a stronger
/// (facet-candidate) cut, but measured across the home corpus it moved no node
/// count down and regressed gen/qiu — a deeper cut is not a better branch on
/// these instances. the cover-minimal knob opts in; the default is
/// byte-identical to the pre-reduction separator.
fn cover_minimal_enabled() -> bool {
    crate::tune::caller_flag(crate::tune::Knob::CoverMinimal) == Some(true)
}

/// Reduce `cover` (indices into `items`, whose `.1` is the exact-representable
/// knapsack weight `a'_j`) to a MINIMAL cover against capacity `exact_rhs`, in
/// exact arithmetic. Drops the LEAST-violating members first — largest `1 − v_j`,
/// `items[i].3` being `v_j` — so the deepest, most-fractional core survives, and
/// only while the remainder is STILL a cover (`Σ_{C'} a' > b'`); never below two
/// members. Returns the kept item indices (a subset of `cover`, order preserved).
///
/// SOUNDNESS: every returned set `C'` satisfies `Σ_{C'} a' > b'` by construction —
/// the subtraction guard is checked in `BigRational` before each drop — so the
/// cover inequality `Σ_{C'} y_j ≤ |C'| − 1` it feeds is valid, exactly as the
/// full cover's was. Pure and deterministic; guarded directly by
/// `minimal_cover_stays_a_cover_and_keeps_every_point`.
fn minimal_cover(
    cover: &[usize],
    items: &[(u32, f64, bool, f64)],
    exact_rhs: &BigRational,
) -> Vec<usize> {
    // Exact weight of every member; bail to the input unchanged if any is not
    // exactly representable (the caller has already proven the whole set a cover).
    let mut w: Vec<BigRational> = Vec::with_capacity(cover.len());
    for &i in cover {
        match exact(items[i].1) {
            Some(a) => w.push(a),
            None => return cover.to_vec(),
        }
    }
    let mut running: BigRational = w.iter().fold(BigRational::zero(), |acc, a| acc + a);
    // Least-violating first: those members buy the least violation, so dropping
    // them keeps the deepest cut.
    let mut drop_order: Vec<usize> = (0..cover.len()).collect();
    drop_order.sort_by(|&p, &q| {
        (1.0 - items[cover[q]].3)
            .partial_cmp(&(1.0 - items[cover[p]].3))
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    let mut keep = vec![true; cover.len()];
    let mut kept = cover.len();
    for pos in drop_order {
        if kept <= 2 {
            break; // never fall below a 2-item cover
        }
        let reduced = &running - &w[pos];
        if reduced > *exact_rhs {
            running = reduced;
            keep[pos] = false;
            kept -= 1;
        }
    }
    cover
        .iter()
        .zip(&keep)
        .filter_map(|(&i, &k)| k.then_some(i))
        .collect()
}

/// Cover + sequential-lifting separation for ONE knapsack view `Σ a·x <= ub`
/// (the body previously inlined in `separate`; negative coefficients are
/// complemented into a true knapsack below, exactly as before).
fn separate_cover_view(
    model: &Model,
    x: &[f64],
    coeffs: &[(u32, f64)],
    ub: f64,
    cuts: &mut Vec<Cut>,
) {
    // A 0/1 argument needs 0/1 columns.
    //
    // NEGATIVE RESULT -- admitting MIXED rows is SOUND, was implemented, and buys rout NOTHING.
    // Root bound 982.486176 with it and 982.486176 without, to six decimals; not one cut.
    //
    // ⚠ AND MY FIRST WRITE-UP OF *WHY* WAS WRONG, which is worth more than the result. I claimed
    // it could not work because "the passenger IS the capacity" -- a row `Σ d·y − Q·z ≤ 0` where
    // paying for the general integer `z` over its range adds `Q·u_z` back and the knapsack goes
    // vacuous. I never opened the file. rout's capacity rows are
    //
    //     Σ(60 binaries) d_j·y_j  +  4.99·x302 + 5.71·x307 + 4.28·x312  ≤  12.5
    //
    // -- the passengers have POSITIVE coefficients and sit in `[0, 2]`, so `min(a·0, a·2) = 0`
    // and paying for them costs exactly NOTHING. The relaxed knapsack keeps its full capacity of
    // 12.5 and is perfectly tight. The reasoning in the old comment was fiction.
    //
    // The REAL reason is that the relaxation is SLACK AT THE LP POINT. Dropping the three
    // integers hands their share of the 12.5 back to the binaries, and the LP's binaries then sit
    // comfortably inside it -- so a cover exists but nothing violates one, and a valid cut nobody
    // violates is not a cut. To bite, the family would have to keep the general integers IN the
    // knapsack (a mixed-integer cover / lifted knapsack over `[0,2]` variables), not pay them off.
    //
    // The conclusion survives; the argument for it did not. Do not re-derive the old one.
    //
    // ┌─ WHAT ROUT ACTUALLY WANTS: A LIFTED COVER WITH THE INTEGERS LIFTED *IN* ────────────────┐
    // │                                                                                          │
    // │ The knapsack is  Σ_{j∈B} a_j·y_j + Σ_{k∈G} a_k·x_k ≤ b,  y binary, x_k ∈ [0, u_k],      │
    // │ every a > 0 (rout: |B| = 60, |G| = 3, u_k = 2, b = 12.5).                                │
    // │                                                                                          │
    // │ 1. RESTRICT to the face x_G = 0. On that face it is a pure binary knapsack with          │
    // │    capacity b, and the existing greedy separation + `SEQUENTIAL LIFTING` already produce │
    // │    a violated lifted cover  Σ_{j∈C} α_j·y_j ≤ |C| − 1  there.                            │
    // │    ⚠ A cut valid on a FACE is NOT valid for the model. It must be lifted before it is    │
    // │      believed -- this is the step that makes the difference, and skipping it deletes     │
    // │      integer points.                                                                     │
    // │                                                                                          │
    // │ 2. LIFT each general integer back in. Seek the largest γ_k with                          │
    // │                                                                                          │
    // │       Σ_{j∈C} α_j·y_j + γ_k·x_k ≤ |C| − 1   valid for every x_k ∈ {0..u_k}               │
    // │                                                                                          │
    // │    i.e.   γ_k = min_{t = 1..u_k}  ( (|C| − 1) − Φ(b − a_k·t) ) / t,                      │
    // │                                                                                          │
    // │    where Φ(c) = max{ Σ_{j∈C} α_j·y_j : Σ_{j∈C} a_j·y_j ≤ c, y binary } is the lifting   │
    // │    knapsack -- computed exactly by the same greedy the cover separation already runs.    │
    // │    Lift the integers one at a time, folding each into the residual capacity (sequential  │
    // │    lifting: the coefficients depend on the order, and any order is valid).               │
    // │                                                                                          │
    // │ WHY THIS AND NOT WHAT IS ALREADY HERE. Paying the integers off (above) is valid and      │
    // │ SLACK -- the LP's binaries sit comfortably inside the capacity it hands back, so no cover │
    // │ is violated. MIR sees these rows and reaches only 982.49. Lifting keeps the integers      │
    // │ CHARGED, so the cut still binds at the LP point, which is the whole difference between a  │
    // │ valid cut and a useful one.                                                               │
    // │                                                                                          │
    // │ GUARD IT LIKE THE OTHERS. `flow_cover_cuts_never_remove_an_integer_point` is the model:   │
    // │ brute-force every point of a small mixed knapsack (binaries + a couple of [0,2] columns), │
    // │ assert `fired > 0` so the guard cannot be vacuous, and check it FAILS with the lifting    │
    // │ coefficient deliberately over-strengthened by one.                                        │
    // └──────────────────────────────────────────────────────────────────────────────────────────┘
    if coeffs
        .iter()
        .any(|&(c, _)| !matches!(model.col_kind(Col(c)), ColKind::Binary))
    {
        return;
    }

    // Complement the negative coefficients so the row is a true knapsack:
    // for a_j < 0 substitute x_j = 1 − y_j, which flips the sign of a_j and
    // moves `a_j` to the right-hand side.
    //
    //   item = (col, |a_j|, complemented?, value of the 0/1 var in this frame)
    let mut items: Vec<(u32, f64, bool, f64)> = Vec::with_capacity(coeffs.len());
    let mut rhs = ub;
    for &(c, a) in coeffs {
        if a == 0.0 {
            continue;
        }
        let v = x[c as usize].clamp(0.0, 1.0);
        if a > 0.0 {
            items.push((c, a, false, v));
        } else {
            rhs -= a; // b' = b − a_j  (a_j < 0, so this raises the capacity)
            items.push((c, -a, true, 1.0 - v));
        }
    }
    if items.is_empty() || rhs < 0.0 {
        return;
    }

    // Greedy separation: a cover is violated exactly when Σ_{C}(1 − v_j) < 1,
    // so take items in increasing order of (1 − v_j) — the ones the LP has
    // most turned ON — until the capacity is exceeded. That is the cheapest
    // cover to violate, if any is.
    let mut order: Vec<usize> = (0..items.len()).collect();
    order.sort_by(|&i, &j| {
        (1.0 - items[i].3)
            .partial_cmp(&(1.0 - items[j].3))
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    let mut cover: Vec<usize> = Vec::new();
    let mut weight = 0.0f64;
    let mut slack = 0.0f64; // Σ (1 − v_j) over the cover
    for &i in &order {
        if weight > rhs {
            break;
        }
        cover.push(i);
        weight += items[i].1;
        slack += 1.0 - items[i].3;
    }
    if weight <= rhs || cover.is_empty() {
        return; // no cover at all
    }
    if slack >= 1.0 - MIN_VIOLATION {
        return; // a cover, but the LP point does not violate it
    }

    // EXACT check: is this really a cover? The greedy above ran in f64 and is
    // only a proposal. `Σ_{j∈C} a'_j > b'` must hold in exact rationals, or
    // the cut is not valid and must not be admitted.
    let mut exact_weight = BigRational::zero();
    let mut ok = true;
    for &i in &cover {
        match exact(items[i].1) {
            Some(a) => exact_weight += a,
            None => {
                ok = false;
                break;
            }
        }
    }
    let Some(exact_rhs) = exact(rhs) else {
        return;
    };
    if !ok || exact_weight <= exact_rhs {
        return; // not a cover under exact arithmetic: drop it
    }

    // MINIMAL-COVER REDUCTION — sound, textbook-stronger, and DEFAULT-OFF because
    // it does not pay on this corpus (see `cover_minimal_enabled`). The greedy
    // above adds items in increasing (1−v) order and stops the instant the running
    // weight tips over `b'`, but a lighter, more-fractional member added earlier
    // can be REDUNDANT: the rest of the cover already exceeds `b'` without it. A
    // non-minimal cover is dominated — its base inequality `Σ_C y ≤ |C|−1` is less
    // violated (violation is `1 − Σ_C(1−v)`, every extra member only adds to that
    // sum) and its sequential lifting is weaker (a bigger `|C|` is a looser bound
    // for every `alpha`). `minimal_cover` drops redundant members while the
    // remainder stays a cover in EXACT arithmetic. Removing member `i` lowers
    // `Σ(1−v)` by `1−v_i ≥ 0`, so the reduced cover is at-least-as-violated, and
    // `Σ_{C'} a > b'` is re-checked exactly at every drop, so it stays a genuine
    // cover. SOUND either way: it only shrinks the set a valid cut is written over.
    //
    // MEASURED default-off. Enabling it is byte-changing but NOT a win: on the home
    // corpus it left every proof intact (all 268 tests, gt2 21166, misc07 2810,
    // pk1 11 @ 357,325 nodes byte-identical, mas76 40005.054142) yet moved no node
    // count down and REGRESSED gen (11 → 43 nodes) and qiu — a deeper cut is not a
    // better branch. This is the cover family's exhaustion, remeasured with a fresh
    // independent lever; the strengthening is kept, tested, and gated for the
    // instance class where a facet-minimal cover would earn its perturbation.
    if cover_minimal_enabled() && cover.len() > 2 {
        let reduced = minimal_cover(&cover, &items, &exact_rhs);
        if reduced.len() < cover.len() {
            // `weight`/`slack` and `exact_weight` are not read past this point
            // (their guards ran above); `cover` is what the lifting reads.
            cover = reduced;
        }
    }

    // SEQUENTIAL LIFTING, when the data is small integers (this family's
    // dense rows are): a plain cover talks only about its own members, and
    // on a dense row that leaves most of the columns unconstrained — the
    // classic reason plain covers barely dent a dense-knapsack tree. Lift
    // every non-cover item j with the exact coefficient
    //
    // MEASURED on the dense random 70x52/80x60 bench: NEUTRAL at the
    // default 2x4 budget, and more rounds of lifted covers still lose
    // (14.8s -> 18.5s -> 24s at 4x8/8x16) — random dense knapsacks resist
    // the family, exactly as the pre-lifting sweep found. Kept: the
    // lifting is exact, free at the default budget, and cover-family
    // strength is structural on the MIPLIB-style instances the pool
    // targets.
    //     alpha_j = (|C|-1) - max{ Σ coef_i y_i : Σ a_i y_i <= b' - a_j }
    // computed by an integer knapsack DP over the already-lifted set. The
    // DP is the validity proof (standard sequential-lifting argument), and
    // it runs in exact i64 arithmetic — nothing to re-verify downstream.
    // Gated: every weight and the capacity must be true small integers.
    let base_bound = (cover.len() as i64) - 1;
    let mut lifted: Vec<(usize, i64)> = Vec::new(); // (item idx, alpha)
    let int_ok = items
        .iter()
        .all(|&(_, a, _, _)| a.fract() == 0.0 && a < 1e6)
        && rhs.fract() == 0.0
        && rhs < 4096.0
        && items.len() <= 256;
    if int_ok && base_bound > 0 {
        let cap_base = rhs as i64;
        let aa: Vec<i64> = items.iter().map(|&(_, a, _, _)| a as i64).collect();
        // Weighted items available to the DP: the cover (coef 1 each) plus
        // everything lifted so far (coef alpha).
        let in_cover = {
            let mut v = vec![false; items.len()];
            for &i in &cover {
                v[i] = true;
            }
            v
        };
        let mut dp_items: Vec<(i64, i64)> = cover.iter().map(|&i| (aa[i], 1i64)).collect();
        // dp[c] = best coef sum within capacity c, over dp_items.
        let knap = |dp_items: &[(i64, i64)], cap: usize| -> Vec<i64> {
            let mut dp = vec![0i64; cap + 1];
            for &(w, v) in dp_items {
                if w as usize > cap {
                    continue;
                }
                for c in (w as usize..=cap).rev() {
                    let cand = dp[c - w as usize] + v;
                    if cand > dp[c] {
                        dp[c] = cand;
                    }
                }
            }
            dp
        };
        let mut dp = knap(&dp_items, cap_base.max(0) as usize);
        // Lift candidates in descending weight: heavier items admit larger
        // coefficients, and the sequence order determines (all-valid)
        // strength.
        let mut order: Vec<usize> = (0..items.len()).filter(|&i| !in_cover[i]).collect();
        order.sort_by_key(|&i| std::cmp::Reverse(aa[i]));
        for i in order {
            let alpha = if aa[i] > cap_base {
                // y_i = 1 alone violates the row: any coefficient up to the
                // bound is valid; take the strongest.
                base_bound
            } else {
                let z = dp[(cap_base - aa[i]) as usize];
                base_bound - z
            };
            if alpha > 0 {
                lifted.push((i, alpha));
                dp_items.push((aa[i], alpha));
                dp = knap(&dp_items, cap_base.max(0) as usize);
            }
        }
    }

    // Translate back out of the complemented frame:
    //   Σ coef_j y_j <= |C| − 1, with y_j = x_j (plain) or 1 − x_j
    //   (complemented; a complemented term contributes −coef to the LHS
    //   and −coef to the bound).
    let mut out: Vec<(Col, f64)> = Vec::with_capacity(cover.len() + lifted.len());
    let mut comp_coef = 0i64;
    for &i in &cover {
        let (c, _, complemented, _) = items[i];
        if complemented {
            comp_coef += 1;
            out.push((Col(c), -1.0));
        } else {
            out.push((Col(c), 1.0));
        }
    }
    for &(i, alpha) in &lifted {
        let (c, _, complemented, _) = items[i];
        #[allow(clippy::cast_precision_loss)]
        let af = alpha as f64;
        if complemented {
            comp_coef += alpha;
            out.push((Col(c), -af));
        } else {
            out.push((Col(c), af));
        }
    }
    let bound = base_bound - comp_coef;
    cuts.push(Cut {
        coeffs: out,
        lb: f64::NEG_INFINITY,
        #[allow(clippy::cast_precision_loss)]
        ub: bound as f64,
    });
}

#[cfg(test)]
mod cover_view_tests {
    use super::*;
    use crate::model::Sense;
    use ay_test_support::env::{lock_env, ScopedEnvVar};

    #[test]
    fn enabled_minimal_cover_reaches_separator_and_keeps_every_integer_point() {
        let _env_lock = lock_env();
        let mut model = Model::new();
        let cols: Vec<Col> = (0..3).map(|_| model.add_binary_col()).collect();
        let coeffs = [(cols[0].0, 4.0), (cols[1].0, 6.0), (cols[2].0, 6.0)];
        model.add_row(
            f64::NEG_INFINITY,
            10.0,
            &[(cols[0], 4.0), (cols[1], 6.0), (cols[2], 6.0)],
        );
        let lp_point = [0.99, 0.98, 0.97];

        let mut unreduced = Vec::new();
        {
            separate_cover_view(&model, &lp_point, &coeffs, 10.0, &mut unreduced);
        }
        let mut reduced = Vec::new();
        {
            let _enabled = crate::tune::activate_caller(crate::tune::Profile::EMPTY.with(
                crate::tune::Knob::CoverMinimal,
                crate::tune::Setting::Flag(true),
            ));
            separate_cover_view(&model, &lp_point, &coeffs, 10.0, &mut reduced);
        }

        assert_eq!(unreduced.len(), 1, "the control must emit its full cover");
        assert_eq!(unreduced[0].coeffs.len(), 3);
        assert_eq!(unreduced[0].ub, 2.0);
        assert_eq!(reduced.len(), 1, "the enabled path must still emit a cut");
        assert_eq!(
            reduced[0].coeffs,
            vec![(cols[1], 1.0), (cols[2], 1.0)],
            "the redundant weight-4 member must be removed before lifting"
        );
        assert_eq!(reduced[0].ub, 1.0);

        for mask in 0u8..8 {
            let point: Vec<f64> = (0..3).map(|bit| f64::from((mask >> bit) & 1)).collect();
            let model_activity = 4.0 * point[0] + 6.0 * point[1] + 6.0 * point[2];
            if model_activity <= 10.0 {
                let cut_activity: f64 = reduced[0]
                    .coeffs
                    .iter()
                    .map(|&(col, a)| a * point[col.index()])
                    .sum();
                assert!(
                    cut_activity <= reduced[0].ub,
                    "minimal cover deleted feasible point {mask:03b}"
                );
            }
        }
    }

    /// COVER CUTS MUST FIRE ON `>=` ROWS — AND MUST NOT DELETE AN INTEGER POINT.
    ///
    /// `separate` used to process only the `<=` side of each row; on weighted
    /// covering rows (`Σ w_j·x_j >= W`, the weighted-domination shape) it
    /// generated ZERO cuts, silently — the whole cover machinery never ran and
    /// the dual crawled. The `>=` side is the same knapsack after negation
    /// (`Σ(−w)·x <= −W`), and its covers are exactly the minimal blocking sets:
    /// on `8a +12b +8c +4d +15e >= 15`, dropping {a, b, e} leaves 12 < 15, so
    /// `a + b + e >= 1` is a valid cut STRICTLY stronger than the LP row.
    ///
    /// The liveness half pins that exact shape (a real domset mw19_14 row) with
    /// the LP point pushed high enough that a blocking set is violated:
    /// `fired > 0` FAILS on the old ub-only code. The soundness half brute-forces
    /// every 0/1 point of random weighted covering models against every emitted
    /// cut — including the lifted coefficients, whose DP runs in the negated
    /// frame and is the part most likely to be wrong.
    #[test]
    fn cover_cuts_fire_on_ge_covering_rows_and_keep_every_integer_point() {
        // Liveness: the domset row shape that previously produced zero cuts.
        {
            let mut m = Model::new();
            let cols: Vec<Col> = (0..5).map(|_| m.add_binary_col()).collect();
            let w = [8.0, 12.0, 8.0, 4.0, 15.0];
            let terms: Vec<(Col, f64)> = cols.iter().copied().zip(w).collect();
            m.add_row(15.0, f64::INFINITY, &terms);
            m.set_objective(&[(cols[0], 1.0)], Sense::Minimize);
            // LP-FEASIBLE (activity 8+4+3 = 15) yet the blocking set {a,b,e}
            // has x_a+x_b+x_e = 0.2 < 1: a `>=` cover cut is violated exactly
            // where the x's are near ZERO — the complemented frame flips the
            // usual near-one intuition.
            let x = [0.0, 0.0, 1.0, 1.0, 0.2];
            let cuts = separate(&m, &x);
            assert!(
                !cuts.is_empty(),
                "the >= view produced no cuts on the weighted covering row"
            );
            for code in 0..32u32 {
                let p: Vec<f64> = (0..5).map(|t| f64::from((code >> t) & 1)).collect();
                let act: f64 = p.iter().zip(w).map(|(v, wj)| v * wj).sum();
                if act < 15.0 {
                    continue; // the model itself excludes this point
                }
                for c in &cuts {
                    let cact: f64 = c.coeffs.iter().map(|&(j, a)| a * p[j.index()]).sum();
                    assert!(
                        cact <= c.ub + 1e-7,
                        "cut deleted feasible point {code:05b}: {cact} > {}",
                        c.ub
                    );
                }
            }
        }

        // ...and the `<=` side must still fire exactly as before the split.
        {
            let mut m = Model::new();
            let cols: Vec<Col> = (0..4).map(|_| m.add_binary_col()).collect();
            let w = [6.0, 5.0, 4.0, 3.0];
            let terms: Vec<(Col, f64)> = cols.iter().copied().zip(w).collect();
            m.add_row(f64::NEG_INFINITY, 10.0, &terms);
            m.set_objective(&[(cols[0], 1.0)], Sense::Minimize);
            let cuts = separate(&m, &[0.9; 4]);
            assert!(!cuts.is_empty(), "the <= side regressed to zero cuts");
        }

        // Soundness sweep: random weighted `>=` covering models, every 0/1
        // point, every cut.
        let mut seed = 0x2c1b_5eed_u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };
        const N: usize = 8;
        let mut fired = 0usize;
        for _case in 0..300 {
            let mut m = Model::new();
            let cols: Vec<Col> = (0..N).map(|_| m.add_binary_col()).collect();
            let mut rows: Vec<(Vec<f64>, f64)> = Vec::new(); // dense weights, rhs
            for _r in 0..3 {
                let mut w = vec![0.0f64; N];
                let mut terms: Vec<(Col, f64)> = Vec::new();
                let mut wmax = 0.0f64;
                let mut wsum = 0.0f64;
                for j in 0..N {
                    if rnd() % 100 < 60 {
                        let a = (1 + rnd() % 30) as f64;
                        w[j] = a;
                        terms.push((cols[j], a));
                        wmax = wmax.max(a);
                        wsum += a;
                    }
                }
                if terms.len() < 2 {
                    continue;
                }
                // Domset shape (rhs = heaviest weight) half the time; an
                // arbitrary achievable rhs the other half.
                let rhs = if rnd() % 2 == 0 {
                    wmax
                } else {
                    (1 + rnd() % (wsum as i64 - 1).max(1)) as f64
                };
                m.add_row(rhs, f64::INFINITY, &terms);
                rows.push((w, rhs));
            }
            if rows.is_empty() {
                continue;
            }
            m.set_objective(&[(cols[0], 1.0)], Sense::Minimize);
            // A point with most variables near OFF is where blocking-set
            // covers get violated (near-one in the complemented frame).
            let x: Vec<f64> = (0..N).map(|_| (rnd() % 51) as f64 / 100.0).collect();
            let cuts = separate(&m, &x);
            fired += cuts.len();
            for code in 0..(1u32 << N) {
                let p: Vec<f64> = (0..N).map(|t| f64::from((code >> t) & 1)).collect();
                let feasible = rows
                    .iter()
                    .all(|(w, rhs)| p.iter().zip(w).map(|(v, wj)| v * wj).sum::<f64>() >= *rhs);
                if !feasible {
                    continue;
                }
                for c in &cuts {
                    let cact: f64 = c.coeffs.iter().map(|&(j, a)| a * p[j.index()]).sum();
                    assert!(
                        cact <= c.ub + 1e-7,
                        "cut deleted feasible point {code:08b}: {cact} > {}",
                        c.ub
                    );
                }
            }
        }
        assert!(
            fired > 0,
            "the sweep never produced a cut — the guard is not guarding anything"
        );
    }

    /// `minimal_cover` must return a set that is STILL a cover (`Σ a' > b'`), must
    /// never grow it, must stop at two members, and — the property that makes it
    /// sound — the cover inequality it feeds must keep every integer-feasible
    /// point. Random small knapsacks, a deliberately NON-minimal greedy cover fed
    /// in, then the reduced cover's inequality checked against every 0/1 point of
    /// the knapsack. Also asserts the reduction actually fires (a shrink happens),
    /// so the guard cannot pass vacuously.
    #[test]
    fn minimal_cover_stays_a_cover_and_keeps_every_point() {
        let mut seed = 0x51ed_c0de_u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };
        const N: usize = 10;
        let mut shrinks = 0usize;
        for _ in 0..2000 {
            // A knapsack `Σ a_j y_j <= b`, small integer weights.
            let a: Vec<f64> = (0..N).map(|_| (1 + rnd() % 12) as f64).collect();
            let total: f64 = a.iter().sum();
            if total < 4.0 {
                continue;
            }
            let b = (2 + rnd() % (total as i64 - 2).max(1)) as f64;
            // `items` in the frame `separate_cover_view` builds: (col, |a|, comp?, v).
            let v: Vec<f64> = (0..N).map(|_| (rnd() % 101) as f64 / 100.0).collect();
            let items: Vec<(u32, f64, bool, f64)> =
                (0..N).map(|j| (j as u32, a[j], false, v[j])).collect();
            // A greedy cover over ALL items (guaranteed a cover: it is the whole
            // set whenever total > b), intentionally not minimized.
            let mut order: Vec<usize> = (0..N).collect();
            order.sort_by(|&p, &q| {
                (1.0 - v[p])
                    .partial_cmp(&(1.0 - v[q]))
                    .unwrap_or(std::cmp::Ordering::Equal)
            });
            let mut cover = Vec::new();
            let mut w = 0.0;
            for &i in &order {
                if w > b {
                    break;
                }
                cover.push(i);
                w += a[i];
            }
            if w <= b || cover.len() < 3 {
                continue; // not a (reducible) cover
            }
            let exact_rhs = exact(b).unwrap();
            let reduced = minimal_cover(&cover, &items, &exact_rhs);
            // Never grows, never drops below two, stays a genuine cover.
            assert!(reduced.len() <= cover.len());
            assert!(reduced.len() >= 2);
            if reduced.len() < cover.len() {
                shrinks += 1;
            }
            let cw: f64 = reduced.iter().map(|&i| a[i]).sum();
            assert!(cw > b + 1e-9, "reduced set is not a cover: {cw} <= {b}");
            // The cover inequality `Σ_{C'} y <= |C'| - 1` deletes no feasible point.
            let rhs = (reduced.len() - 1) as f64;
            for code in 0..(1u32 << N) {
                let p: Vec<f64> = (0..N).map(|t| f64::from((code >> t) & 1)).collect();
                let load: f64 = (0..N).map(|j| a[j] * p[j]).sum();
                if load > b + 1e-9 {
                    continue; // infeasible for the knapsack
                }
                let act: f64 = reduced.iter().map(|&i| p[i]).sum();
                assert!(
                    act <= rhs + 1e-9,
                    "minimal cover deleted feasible point {code:010b}: {act} > {rhs}"
                );
            }
        }
        assert!(
            shrinks > 0,
            "minimal_cover never shrank a cover — guard is vacuous"
        );
    }
}

// ---------------------------------------------------------------------------
// Gomory mixed-integer cuts
// ---------------------------------------------------------------------------

use num_traits::{One, Signed, ToPrimitive};

use crate::certify::{ExactLu, SparseExactLu};
use crate::simplex::{Candidate, FloatLp, NbBound};

/// The GMI basis factorization, in whichever representation this run asked for.
///
/// The sparse path is the default and the only one the row cap is now sized
/// against; the dense one is reachable only through `--dense-gmi-lu` and
/// exists so the representation change stays FALSIFIABLE — same instance, same
/// seed, one env var apart, and the cuts have to come out byte-identical.
enum BasisLu {
    Sparse(SparseExactLu),
    Dense(ExactLu),
}

impl BasisLu {
    fn solve(&self, b: &[ay_lra::rational::Rational]) -> Vec<ay_lra::rational::Rational> {
        match self {
            Self::Sparse(f) => f.solve(b),
            Self::Dense(f) => f.solve(b),
        }
    }
}

/// Kill switch for the sparse GMI basis factorization: set `--dense-gmi-lu`
/// to rebuild the `m × m` dense `Bᵀ` and factor it the way this separator did
/// before [`SparseExactLu`] existed. Kept because the claim being made is
/// "identical cuts, less memory", and half of that claim is only checkable if the
/// old path can still be run. It is also how the QUADRATIC peak-RSS curve was
/// measured (see [`gmi_max_basis_rows`] for the table) — the measurement that
/// showed the 600-row cap was a memory budget wearing a time budget's docstring.
#[inline]
fn dense_gmi_lu() -> bool {
    crate::tune::caller_flag(crate::tune::Knob::DenseGmiLu) == Some(true)
}

/// GMI rounds are the expensive ones (an exact `Bᵀ` solve per cut row), so they
/// happen once, at the root, where the whole tree pays for them.
///
/// TUNED, AND THE TUNING IS LOAD-BEARING. Cuts tighten the bound and bloat the LP,
/// and the LP is paid at every node: at 8 rounds x 12 the root separates ~96 cuts and
/// 60x45 goes from 5.5s to 18.5s. Two rounds of four is where 60 and 70 binaries become
/// solvable at all while the smaller instances give up almost nothing.
///
/// PRESOLVE (coefficient tightening) WAS TRIED AND FINDS NOTHING HERE. For a binary row
/// `Σ a_j x_j <= b` with `M = Σ a_j`, if `M − a_k < b` the row is redundant whenever
/// `x_k = 0`, and it can be rewritten `a_k := M − b`, `b := M − a_k` — same 0/1 solutions,
/// strictly smaller LP relaxation, and NO new row, so no per-node tax. It is the one
/// bound-strengthening lever that dodges the cut-bloat trap entirely, which is why it
/// looked like the answer.
///
/// It never fires on this instance class. The rows are dense with mixed signs, so
/// complementing the negatives inflates the capacity enormously (`b' ≈ 85` against
/// `M ≈ 150` on a 60-column row) and `M − a_k < b` is never close to true. Coefficient
/// tightening bites on rows that are nearly-tight knapsacks; these are nothing like that.
/// It may still help nearly tight Big-M rows, but it is not useful for this
/// dense mixed-sign instance class.
///
/// RE-TUNED after strong branching landed, in case the optimum had moved. It has not:
/// 4 rounds x 8 makes 70 binaries 15.6s -> 116s, and 6 x 10 makes it 84s. The LP is paid
/// at every node and a better-branched tree visits its nodes no more cheaply, so cut
/// bloat is if anything MORE expensive now, not less.
///
/// A "keep only the BINDING cuts" filter was tried — generate freely, then drop every
/// cut the final root LP is not sitting on, on the theory that a slack cut is pure
/// per-node tax. It is much WORSE (60x45: 43,847 nodes -> 73,061; 5.5s -> 18.5s). A cut
/// that ends up slack is not inert: it shaped the relaxation that made the others
/// binding, and removing it weakens the bound the whole tree is pruned against. Cut
/// strength is not a property of individual cuts.
/// GMI IS NOT ENOUGH, AND IT IS NOT BECAUSE THE CUTS ARE BAD. Measured, so the next attempt starts
/// from the data.
///
/// The three MIPLIB instances ay cannot prove (air05, qnet1, rout) all fail the same way: the tree
/// reaches ZERO leaves because the root bound is nowhere near the optimum.
///
/// ```text
///                root LP      optimum     gap
///   rout         981.86       1077.56     9%
///   qnet1      14274.10      16029.69    11%
/// ```
///
/// And the cuts do NOTHING about it. On rout the root bound is 981.864286 WITH the cuts and
/// 981.864286 WITHOUT them -- to six decimals, identical. That is not because the cuts are invalid
/// or unviolated: every one of them was checked, and they cut the relaxation's own vertex off by
/// between 0.04 and 0.57. They are correct cuts. The LP is simply DEGENERATE -- it has a wealth of
/// alternative optima at the same objective, so removing one vertex just moves it to the next, and
/// the bound does not budge. Sweeping the effort (2/4 shipped, 6/16, 12/40 rounds/cuts) changes
/// nothing, for the same reason.
///
/// (Density is not the culprit either: mod010's cuts run to 2,579 non-zeros and they are the ones
/// that WORK -- lifting its root bound from 6532.08 to 6546.92 against an optimum of 6548, which is
/// exactly why mod010 is a proof and rout is not.)
///
/// What is missing is not more GMI. It is other FAMILIES -- MIR on the original rows with bound
/// substitution and aggregation, flow-cover for the fixed-charge structure rout and qnet1 actually
/// have, clique/odd-hole for air05's set-partitioning rows. This engine carries two families
/// against the dozen a competitive solver carries, and the two it has are the two that cannot see
/// the structure these instances are made of.
///
/// **2026-07-25, ten rounds, and why the two above is not the refutation it looks like.** The
/// note above measured rounds against a per-round budget of FOUR cuts, and the sweep it cites
/// ("6/16, 12/40 rounds/cuts changes nothing") was run on rout — a degenerate LP where no cut
/// of any family moves the bound, which is the one instance whose answer does not generalise.
/// Measured on the 130 MIPLIB instances with a published optimum (W0):
///
/// ```text
///   root budget 40, rounds 2      +6.00pp mean root closure   (worst instance −3.10pp)
///   root budget  4, rounds 10     +3.83pp                     (worst −19.06pp: b-ball)
///   root budget 40, rounds 10     +9.83pp                     (worst −0.48pp)
/// ```
///
/// The two levers COMPOUND, and — the load-bearing detail — the b-ball regression that ten
/// rounds cause on their own DISAPPEARS once the budget is 40. Ten shallow rounds re-derive
/// near-copies of the same few rows; ten rounds each allowed forty rows reach different
/// structure. Rounds were never the problem on their own, and neither was the budget; the
/// pair of them at four-by-two was.
///
/// **AND THE BOTTOM LINE REFUSED IT.** Root closure is a LEADING indicator, and it did not
/// transfer. Gated on full 15s solves over 154 instances, twice, `40 × 10` gives:
///
/// ```text
///   proved            38 -> 37
///   verdicts           1 gained, 7 LOST  (qnet1 OPTIMAL->FEASIBLE; four FEASIBLE->UNKNOWN)
///   wall               1 faster, 10 slower  (p0201 +899%, gt2 +881%, f2gap40400 +450%)
///   soundness alarms   0 in every arm
/// ```
///
/// Every row the root adopts is a row in every LP of every node, and ay's node LP cannot
/// carry a Gurobi-sized pool: the bound arrives and the throughput that would have used it
/// does not. The bound-driven final retention below recovers part of the wall (gt2 +881%
/// rather than +5932%, ten slower rather than twelve) and does not recover the verdicts.
///
/// So the defaults STAY at two-by-four, and the finding is the deliverable: **the root cut
/// gap is downstream of the LP-throughput gap.** More cut quality is not affordable until
/// W5 makes a node LP cheap enough to carry it, which reorders the plan — W5 is the
/// prerequisite for W1/W2, not a parallel stream. `--root-cuts-per-round
/// --gmi-rounds` reproduces the +9.25pp closure arm on demand.
pub(crate) const MAX_GMI_ROUNDS: usize = 2;

/// Cut effort, overridable for measurement. The shipped values were tuned on the dense binary
/// generator, where more cuts are decisively worse; a real model may want quite different ones,
/// and that is a question to settle with the corpus rather than a guess.
pub(crate) fn gmi_rounds() -> usize {
    std::env::var("--gmi-rounds")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(MAX_GMI_ROUNDS)
}

/// The ONE read of `--cuts-per-round`. Every budget below funnels through here so the
/// override keeps a single meaning and the ledger keeps a single read site — and, importantly,
/// so that an EXPLICIT `--cuts-per-round=4` still forces four. The shape default below
/// also happens to be four on wide models; collapsing the two would silently convert every
/// baseline arm ever measured through this knob into a shape-gated arm.
fn cuts_per_round_env() -> Option<usize> {
    // B37: caller-layer force (`--cuts-per-round`); unset keeps the
    // shape-gated default below.
    crate::tune::count_opt(crate::tune::Knob::CutsPerRound)
}

pub(crate) fn cuts_per_round() -> usize {
    cuts_per_round_env().unwrap_or(MAX_CUTS_PER_ROUND)
}

/// A model is WIDE when `cols >= 4 * rows`.
///
/// This is not a fitted threshold: [`default_root_cut_eff_floor`] already uses the identical
/// predicate to demand a 6× stricter cut-efficacy bar, on the independent grounds that
/// knapsack-shaped models want fewer, better cuts. The per-round budget turns out to be the
/// same phenomenon measured from the other end.
pub(crate) fn is_wide_shape(num_rows: usize, num_cols: usize) -> bool {
    num_rows > 0 && num_cols / num_rows >= 4
}

/// Per-round cut budget on NARROW models. See [`cuts_per_round_for_shape`].
pub(crate) const NARROW_CUTS_PER_ROUND: usize = 8;

/// Per-round cut budget on WIDE models — ONE, not the historical flat four.
///
/// The first cut of this gate kept wide models at `MAX_CUTS_PER_ROUND` on the reasoning that the
/// wider budget merely failed to help there. That was too timid: a budget sweep on load-invariant
/// node counts showed the flat four is DOMINATED in the wide regime, strictly, by every smaller
/// value. Wide models do not want the extra cuts declined — they want fewer than they were
/// already getting.
///
/// ```text
///   node counts, unseeded (answers byte-identical at every budget -- verified)
///     budget           4         2         1         0
///     mas76      1249781    821481    808359    808367
///     gt2          56670     48955      5094      1178
///     khb05250/air03/mod010/markshare1/markshare2: bit-identical at all four
///
///   WALL, unseeded, measured SERIALLY on an idle machine (the deliverable):
///     wide subset   cpr=4  37.187 s  ->  cpr=1  26.596 s   (-10.59 s, -28.5%)
///       mas76       24.832 -> 16.099 s   (-8.73 s)
///       khb05250, air03, mod010 all faster at IDENTICAL node counts -- the removed
///       cost is pure per-node cut overhead, with no search effect either way.
///
///   SEEDED mas76 (incumbent luck held fixed -- so this is search quality, not timing):
///     cpr=4  21.061 s / 975265 nodes   ->   cpr=1  16.494 s / 810077 nodes
/// ```
///
/// `cpr=0` ties this (26.564 s vs 26.596 s) and is NOT chosen: one keeps a minimal cut stream
/// alive instead of disabling separation outright on every wide model, which is the smaller
/// behavioural change for wide instances outside this corpus. The corpus cannot tell them apart.
///
/// gt2's 48x is deliberately discounted — gt2's node count is set by incumbent discovery and six
/// separate gt2 headlines evaporated under the seeded control in one session. Excluding it
/// entirely the gain is still -8.94 s, carried by mas76, which is not a lottery instance (800k+
/// nodes) and whose gain survives seeding.
pub(crate) const WIDE_CUTS_PER_ROUND: usize = 1;

/// Shape-gated per-round cut budget.
///
/// # The measurement (2026-08-05, full corpus, BOTH arms seeded)
///
/// `--cuts-per-round=8` was measured on 16 corpus instances with both arms seeded from
/// the same witness, so incumbent-discovery luck is held fixed and only the budget varies (the
/// unseeded version of this table is worthless — it reversed sign on qnet1; see
/// the development design notes). Sorted by shape:
///
/// ```text
///   NARROW (cols/rows < 4)                 WIDE (cols/rows >= 4)
///     qnet1    3.06   -2.053 s               mas76     12.58   +1.994 s
///     qiu      0.70   -1.009 s               khb05250  13.37   +0.546 s
///     misc07   1.23   -0.665 s               air03     86.75   +0.100 s
///     p0201    1.51   -0.068 s               mod010    18.18   +0.012 s
///     dcmulti  1.89   -0.048 s               markshare1 10.33  -0.002 s
///     blend2   1.29   -0.037 s               markshare2 10.57  -0.005 s
///     flugpl   1.00    0.000 s
///     rout     1.91    0.000 s
///     gen      1.12   +0.003 s
///     pk1      1.91   +0.131 s
///     SUM            -3.746 s               SUM               +2.645 s
/// ```
///
/// The sign separates on shape with a 4× margin (narrow tops out at 3.06, wide starts at
/// 10.33) and only two negligible exceptions, both narrow. Applied globally the knob is a
/// WASH (−1.10 s net, one big win cancelling one big loss) and not shippable; gated to narrow
/// models it keeps −3.75 s and declines +2.65 s.
///
/// # Why the wide models lose
///
/// Not a bound/tree trade-off — on the losers the node count does not move AT ALL (mas76
/// 975265 → 982027, khb05250 15 → 17) while wall rises. The extra cuts buy zero search and
/// are pure overhead, exactly as [`MAX_GMI_ROUNDS`]'s note predicts: *every row the root adopts
/// is a row in every LP of every node*. On a wide model there are many more columns per row for
/// a cut to be dense over, and correspondingly fewer rows to tighten.
///
/// `--cuts-per-round` overrides this entirely (both directions);
/// `AY_MILP_NO_SHAPE_CPR=1` disables the gate and restores the flat four.
pub(crate) fn cuts_per_round_for_shape(num_rows: usize, num_cols: usize) -> usize {
    cuts_per_round_env().unwrap_or_else(|| shape_cuts_per_round(num_rows, num_cols))
}

fn shape_cuts_per_round(num_rows: usize, num_cols: usize) -> usize {
    // B22 retired the flat-four switch; --cuts-per-round still forces a value.
    if is_wide_shape(num_rows, num_cols) {
        WIDE_CUTS_PER_ROUND
    } else {
        NARROW_CUTS_PER_ROUND
    }
}

/// The ROOT loop's per-round cut budget, which is a different economy from a node's.
///
/// `MAX_CUTS_PER_ROUND`'s four is charged at every NODE as well, where a wider batch is a
/// direct tax on the throughput that proves the tree. At the root the same four rows are
/// paid for once and are the only thing standing between the relaxation and the bound the
/// whole tree prunes against — and MEASURED (W0, 130 MIPLIB instances with a published
/// optimum, the development design notes), four is far too few:
/// the adopted cut counts cluster on 4/8/12 while the mean root closure sits at 7.0%
/// against Gurobi's 54.7%.
///
/// Raising the ROOT budget alone to 40 moves mean root closure by +6.0pp (+779pp summed
/// over 130 instances) with three regressions, the worst −3.1pp; with ten rounds it is
/// +9.25pp and mean closure goes 7.02% → 16.27%.
///
/// **The default is nonetheless still four**, because the full-solve gate refused it — see
/// [`MAX_GMI_ROUNDS`] for the numbers. The value of this function is that the root budget is
/// now SEPARABLE from the node budget at all, so the next attempt does not have to buy the
/// node regression along with the root gain.
///
/// `--root-cuts-per-round` overrides; the historical `--cuts-per-round` still
/// overrides both, so every measurement taken through the old knob keeps its meaning.
pub(crate) fn root_cuts_per_round() -> usize {
    root_cuts_per_round_env().unwrap_or(ROOT_CUTS_PER_ROUND)
}

fn root_cuts_per_round_env() -> Option<usize> {
    std::env::var("--root-cuts-per-round")
        .ok()
        .and_then(|v| v.parse().ok())
        .or_else(cuts_per_round_env)
}

/// The root loop's per-round budget under the same shape gate as
/// [`cuts_per_round_for_shape`] — the measured arm raised BOTH budgets together (the historical
/// `--cuts-per-round` overrides node and root alike), so the gate has to move both to
/// reproduce it.
pub(crate) fn root_cuts_per_round_for_shape(num_rows: usize, num_cols: usize) -> usize {
    root_cuts_per_round_env().unwrap_or_else(|| shape_cuts_per_round(num_rows, num_cols))
}

/// The cap on the root loop's CLIQUE-ONLY extension rounds (see `add_root_cuts`): the loop ends
/// itself the round cliques stop separating or the bound stalls, so this is a backstop, not a
/// budget. Distinct from `gmi_rounds` on purpose -- that constant was tuned against an exact
/// `Bᵀ` factorization per round, and cliques cost milliseconds where GMI costs seconds.
const MAX_CLIQUE_ROUNDS: usize = 30;

pub(crate) fn clique_rounds() -> usize {
    MAX_CLIQUE_ROUNDS
}

/// The cap on the root loop's COVER extension rounds (see `add_root_cuts`): the
/// knapsack-cover analogue of the clique cap, the same shape of backstop — the
/// extension ends itself the round the family stops producing or the bound
/// stops moving materially. Weighted covering models (domset mw19: every row
/// `Σ w·x >= W`) are where it pays: separation is a greedy sweep (0.00s
/// measured where exact GMI burned 60s+ for nothing), each adopted round both
/// lifts the bound and exposes the next vertex's blocking sets (139.885 ->
/// 143.842 in the single round the base budget affords, with 70 fresh covers
/// separated at the new vertex and nowhere to go), and the family needs
/// ROUNDS, exactly like cliques on air03.
const MAX_COVER_EXT_ROUNDS: usize = 30;
pub(crate) fn cover_ext_rounds() -> usize {
    MAX_COVER_EXT_ROUNDS
}

/// The cap on the root loop's MIR-class extension rounds (see `add_root_cuts`): like the clique
/// cap, a backstop, not a budget -- the extension ends itself the round the family stops producing
/// or the bound stops moving materially (`MIR_STALL_ROUNDS`), and the loop's deadline bounds it in
/// wall clock regardless. Distinct from `gmi_rounds` for the same reason the clique cap is: that
/// constant was tuned against an exact `Bᵀ` factorization per round, and a MIR round reads the
/// model's own rows in one sweep. `0` disables the extension outright.
///
/// SHIPPED OFF (0), MACHINERY STAGED. The economy does exactly what it claims — qnet1's root
/// walks 14,438 -> 15,434 deterministically (66% of the root gap, from 13%) at 0.02s a round,
/// and the tree shrinks ~5x — and then STRONG BRANCHING confiscates the win: its per-probe cost
/// grows ~20x on the cut-laden degenerate relaxation and the share-based budget spends it
/// (interleaved pairs: 17.5s base vs 29.9s with the extension; EXT off on the same binary
/// reproduces base). Until SB probe pricing on cut-heavy LPs is fixed, the extension buys
/// bound, not wall. `AY_MILP_MIR_EXT_ROUNDS=40` re-enables for that work.
///
/// 2026-07-15 — SB PROBE PRICING FIXED, AND IT WAS NOT ENOUGH. The limited-iteration probe
/// (`PROBE_DUAL_ITERS`, bab.rs: 25 dual pivots per probe, early-stopped duals certify the
/// bound) cut the extension run's strong branching from 10.2s to 1.9s of wall — probe pairs
/// 294 iters/10.4ms -> ~36-41/~0.6ms — and the interleaved pair moved 30.0s -> 23.5-23.8s
/// against 17.2-17.5s default. The confiscation MOVED rather than died: under 25-pivot advice
/// the degenerate cut-laden LP seeds pseudocosts with near-zero gains (the dual spends its
/// first pivots eating through the optimal face, so the bound has not moved when the cap
/// stops it), one incumbent-phase tree grows 89 -> 4,591 nodes at ~1.9ms/node, and root cuts
/// themselves cost 3.8s of the 23.5s. Sweeping the cap toward optimality-priced probes only
/// climbs back toward the old wall (50 -> 25.1s, 200 -> 27.1s): on this relaxation there is
/// no probe budget at which the cuts pay in wall. What is left is not probe pricing — it is
/// that CHEAP probes carry no ranking signal on a degenerate LP (degeneracy-aware seeding, or
/// cheaper node LPs on cut rows, are the next levers). The extension still buys bound, not
/// wall; `AY_MILP_MIR_EXT_ROUNDS=40` re-enables for that work.
///
/// 2026-07-16 — RE-MEASURED AFTER THE DUAL OBJECTIVE CUTOFF SHIPPED, STILL NET-NEGATIVE. The
/// cutoff cut the extension run's absolute wall almost in half (23.5s -> 14.2s) — but the
/// ext-OFF baseline fell FURTHER (17.2s -> 6.3s), so the gap widened, not closed. Interleaved
/// against a baseline binary, qnet1 @60s: ext OFF 6.28-6.34s, ext ON (=40) 14.17-14.24s (2.25x
/// SLOWER, reproducible x3). The mechanism is intact and confirms the diagnosis — the extended
/// loop still closes the root from 13.9% (14518.7 at round 1) to 67.2% (15454.5 at round 24) of
/// the 14274.1 -> 16030 gap — the extra bound just does not pay for the cut-laden degenerate
/// node LPs it buys. The blocker is unchanged (degeneracy-aware seeding / cheaper node LPs on cut
/// rows), so the default stays 0.
const MAX_MIR_EXT_ROUNDS: usize = 0;

pub(crate) fn mir_ext_rounds() -> usize {
    // B25: env retired; the shipped extension-round count is the constant.
    MAX_MIR_EXT_ROUNDS
}

/// The MIR extension rounds a MIXED-INTEGER-KNAPSACK / MIXING model earns even though the
/// global default (`MAX_MIR_EXT_ROUNDS`) ships at 0. The default is 0 because on qnet1 —
/// a degenerate equality-flow relaxation — the extended rounds buy bound the strong-branch
/// pricing then confiscates in WALL (see the note above `MAX_MIR_EXT_ROUNDS`). That
/// confiscation is specific to that structure; it does NOT occur on the mik/mixing shape,
/// where the family closes the dual gap that single-row MIR saturates weak on at the root
/// (measured on mik-250-20-75-4: rigorous dual −54936 → −53702 over 60s). Gated by
/// [`is_mixed_integer_knapsack`], which every home-corpus instance fails, so the extension
/// stays off — and the 16 stay bit-identical — everywhere it does not pay.
const MIK_MIR_EXT_ROUNDS: usize = 50;

/// The MIR extension round cap for a mixed-integer-knapsack model (see `MIK_MIR_EXT_ROUNDS`),
/// overridable by `AY_MILP_MIK_MIR_EXT_ROUNDS` for measurement. A backstop, not a budget —
/// the extension self-terminates the round the family stops moving the bound materially.
pub(crate) fn mik_mir_ext_rounds() -> usize {
    MIK_MIR_EXT_ROUNDS
}

/// A MIXED-INTEGER KNAPSACK / MIXING model: every constraint an upper-bounded knapsack
/// (`Σ a·x ≤ b`, no equality or `≥` row), at least one continuous "capacity" column and
/// at least one integral (general-integer OR binary) column, and — the mixing signature —
/// a continuous column SHARED across many rows. mik-* is the archetype: mik-250-20-75-4 has
/// 20 continuous columns each shared across ~76 of 195 knapsack rows, and 250 integer columns
/// that all carry an upper bound of 1 (so they load as `Binary`). This is the structure where
/// the MIR extension pays.
///
/// The gate is a DUAL-BOUND / speed lever ONLY: it turns on more rounds of the already
/// verdict-safe MIR / strong-CG / aggregated-MIR families (every cut exact or `Cut::snap`
/// box-damaged — it can never remove an integer point). It cannot change any verdict.
///
/// It is deliberately narrow, and the ALL-`≤` test is the real discriminator: EVERY home-corpus
/// instance that has a continuous column (qnet1, rout, blend2, dcmulti, gen, mas74, mas76) carries
/// an equality or `≥` row and so fails it; the only all-`≤` home instance, p0201, has ZERO
/// continuous columns (`has_cont` false). The 3 prior wins (b-ball, enlight*) and the 6 ext
/// OPTIMALs all carry `E`/`G` rows too. So the corpus stays bit-identical — the gate fires ONLY on
/// the mik/mixing shape.
pub(crate) fn is_mixed_integer_knapsack(model: &Model) -> bool {
    // The f64 matrix is advice only when an exact-rational side store is present.
    // This structural gate would otherwise classify the proxy model and arm cut
    // families whose derivations may not describe the caller's true rows.
    if model.has_inexact_coeffs() {
        return false;
    }
    let ncols = model.num_cols();
    let nrows = model.num_rows();
    if nrows == 0 {
        return false;
    }
    let mut has_cont = false;
    let mut has_int = false;
    for j in 0..ncols {
        match model.col_kind(Col(j as u32)) {
            ColKind::Continuous => has_cont = true,
            // GENERAL-INTEGER *OR* BINARY. The real mik-* archetype (mik-250-20-75-4) is a
            // MIXED 0/1 KNAPSACK: its 250 integer columns all carry an upper bound of 1, so the
            // model loads them as `Binary`, not `Integer`. The old `has_gen_int` requirement
            // therefore NEVER fired on the instance this gate was written for — the extension was
            // dead on real mik. What the rounding needs is any INTEGRAL column, binary or general;
            // the mixing/knapsack strength does not depend on the integers having range > 1.
            //
            // SAFETY (the gate stays narrow because the ALL-`≤` test below is the real
            // discriminator): among the 16 home instances only p0201 is all-`≤`, and p0201 has
            // ZERO continuous columns (`has_cont` false), so it still fails here; every other home
            // instance carries an equality or `≥` row. The 3 prior wins (b-ball, enlight*) and the
            // 6 ext OPTIMALs all carry `E`/`G` rows too. So this widening is bit-identical on the
            // whole corpus — it changes ONLY the mik/mixing shape, which is its entire purpose.
            ColKind::Integer | ColKind::Binary => has_int = true,
        }
    }
    if !has_cont || !has_int {
        return false;
    }
    // Every constraint must be a pure `≤` knapsack: lb = −∞, ub finite. An equality
    // (lb == ub) or a `≥` row (ub = +∞) fails here, which excludes every home instance
    // that has a continuous column.
    let mut cont_rowcount = vec![0u32; ncols];
    for r in 0..nrows {
        let (coeffs, lb, ub) = model.row(Row(r as u32));
        if lb.is_finite() || !ub.is_finite() {
            return false;
        }
        for &(c, a) in coeffs {
            if a != 0.0 && matches!(model.col_kind(Col(c)), ColKind::Continuous) {
                cont_rowcount[c as usize] += 1;
            }
        }
    }
    // The mixing signature: a continuous column shared across many rows.
    cont_rowcount.iter().any(|&n| n >= 10)
}

#[cfg(test)]
mod mik_gate_tests {
    use super::*;

    /// The mixed-integer-knapsack gate must FIRE on the mik/mixing shape and must NOT fire on
    /// any shape a home instance has -- it arms extra MIR rounds, so a false positive would
    /// change one of the 16's proven values (the whole gate exists to keep them bit-identical).
    #[test]
    fn mik_gate_selects_mixing_and_rejects_home_shapes() {
        // mik shape: all `<=` rows, a continuous capacity column shared across many rows,
        // general-integer columns for the rounding.
        {
            let mut m = Model::new();
            let s = m.add_col(0.0, 100.0); // continuous capacity
            let ys: Vec<Col> = (0..12).map(|_| m.add_int_col(0.0, 5.0)).collect();
            for _ in 0..12 {
                let mut terms = vec![(s, -1.0)];
                for &y in &ys {
                    terms.push((y, 3.0));
                }
                m.add_row(f64::NEG_INFINITY, 20.0, &terms); // <= knapsack, shares `s`
            }
            assert!(is_mixed_integer_knapsack(&m), "mik/mixing shape must fire");
        }
        // Equality-flow shape (qnet1/rout/dcmulti/gen/blend2 all carry equality rows): reject.
        {
            let mut m = Model::new();
            let s = m.add_col(0.0, 100.0);
            let ys: Vec<Col> = (0..12).map(|_| m.add_int_col(0.0, 5.0)).collect();
            for _ in 0..12 {
                let mut terms = vec![(s, -1.0)];
                for &y in &ys {
                    terms.push((y, 3.0));
                }
                m.add_row(5.0, 5.0, &terms); // EQUALITY row
            }
            assert!(
                !is_mixed_integer_knapsack(&m),
                "an equality-row model must be rejected"
            );
        }
        // `>=` row present (mas74/mas76 shape): reject.
        {
            let mut m = Model::new();
            let s = m.add_col(0.0, 100.0);
            let ys: Vec<Col> = (0..12).map(|_| m.add_int_col(0.0, 5.0)).collect();
            for _ in 0..12 {
                let mut terms = vec![(s, -1.0)];
                for &y in &ys {
                    terms.push((y, 3.0));
                }
                m.add_row(5.0, f64::INFINITY, &terms); // >= row
            }
            assert!(
                !is_mixed_integer_knapsack(&m),
                "a >= row model must be rejected"
            );
        }
        // PURE BINARY + shared continuous, all `<=`: this IS the real mik-250-20-75-4 shape
        // (250 integer columns, every one bounded to [0,1] so it loads as binary). It must FIRE —
        // the old `has_gen_int` requirement wrongly rejected it and left the extension dead on the
        // one instance the gate exists to arm.
        {
            let mut m = Model::new();
            let s = m.add_col(0.0, 100.0);
            let ys: Vec<Col> = (0..12).map(|_| m.add_binary_col()).collect();
            for _ in 0..12 {
                let mut terms = vec![(s, -1.0)];
                for &y in &ys {
                    terms.push((y, 3.0));
                }
                m.add_row(f64::NEG_INFINITY, 20.0, &terms);
            }
            assert!(
                is_mixed_integer_knapsack(&m),
                "pure-binary mixed knapsack (the real mik shape) must fire"
            );
        }
        // Continuous column NOT shared across rows (no mixing signature): reject.
        {
            let mut m = Model::new();
            let ys: Vec<Col> = (0..12).map(|_| m.add_int_col(0.0, 5.0)).collect();
            for _ in 0..12 {
                let s = m.add_col(0.0, 100.0); // a private continuous per row
                m.add_row(
                    f64::NEG_INFINITY,
                    20.0,
                    &[(s, -1.0), (ys[0], 3.0), (ys[1], 3.0)],
                );
            }
            assert!(
                !is_mixed_integer_knapsack(&m),
                "unshared continuous columns: no mixing signature, reject"
            );
        }
    }
}

/// How many MIR-class rows one EXTENSION round may adopt -- its own budget, like the aggregated
/// flow covers' `MAX_FLOW_AGG_CUTS`, because `cuts_per_round()`'s four was tuned against the
/// expensive separators and an extension round's whole cost is one cheap LP re-solve. Measured on
/// qnet1 (see `add_root_cuts`): the value trades bound per round against selection noise, and the
/// bound-paid stall test is what keeps a bad batch from compounding.
const MAX_MIR_EXT_CUTS: usize = 4;

pub(crate) fn mir_ext_cuts_per_round() -> usize {
    MAX_MIR_EXT_CUTS
}

/// Whether the MIR / strong-CG row preparation searches the KNAPSACK-FORM complementation beside
/// the historical nearest-bound one — see [`BoundPolicy`] for the derivation and the qnet1 row it
/// exists for. `--no-mir-knap` is the kill switch; `--mir-knap` forces it on for A/B
/// against a build whose default has moved.
pub(crate) fn mir_knap_on() -> bool {
    if let Some(on) = KNAP_FORCE.with(std::cell::Cell::get) {
        return on;
    }
    // B29: typed carrier (a forced-on caller value beats a moved default).
    crate::tune::caller_flag(crate::tune::Knob::NoMirKnap).map_or(MIR_KNAP_DEFAULT, |no| !no)
}

thread_local! {
    /// In-process override of the complementation search, for the same reason `SCREEN_FORCE`
    /// exists: the env gate is cached once per process, and the property that matters about a cut
    /// family — that it never removes a feasible integer point — can only be brute-forced by
    /// running the path. See `knap_scope`.
    static KNAP_FORCE: std::cell::Cell<Option<bool>> = const { std::cell::Cell::new(None) };
}

/// Run `f` with the knapsack-form complementation search forced on or off.
#[cfg(test)]
fn knap_scope<T>(on: bool, f: impl FnOnce() -> T) -> T {
    struct Restore(Option<bool>);
    impl Drop for Restore {
        fn drop(&mut self) {
            KNAP_FORCE.with(|c| c.set(self.0));
        }
    }
    let _r = Restore(KNAP_FORCE.with(std::cell::Cell::get));
    KNAP_FORCE.with(|c| c.set(Some(on)));
    f()
}

/// The shipped default for the knapsack-form complementation search (see [`mir_knap_on`]).
const MIR_KNAP_DEFAULT: bool = false;

/// Per-row trace of the complementation search (`the knap-dbg knob`): what each policy's cut
/// was worth at the separation point. Diagnostic only.
fn knap_dbg() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| crate::tune::caller_flag(crate::tune::Knob::KnapDbg) == Some(true))
}

/// Admit [`separate_mir_agg`] into EVERY root round the MIR-class families separate in, rather
/// than only into a stage-two extension round the plain family's dry-up buys.
///
/// This exists because the stage-two gate is unreachable on the instance the family was written
/// for: `add_root_cuts` enters stage two only when `fresh.is_empty()`, and on qnet1 plain MIR
/// separates four cuts in every one of its 21 extended rounds, so the aggregation walk had
/// literally never executed there (traced: zero `mir_agg` lines under
/// `AY_MILP_MIR_EXT_ROUNDS=40`).
///
/// DEFAULT-OFF, and the reason is measured, not cautionary — see the campaign note on
/// `separate_mir_agg`. Off, every call site is skipped before any model scan, so the corpus is
/// bit-identical.
pub(crate) fn mir_agg_root() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| crate::tune::caller_flag(crate::tune::Knob::MirAggRoot) == Some(true))
}

/// Don't cut on a value that is essentially integral already.
const FRAC_TOL: f64 = 1e-6;
/// Cap the cuts per round so the LP does not bloat faster than it tightens. This is the
/// NODE budget; the root has its own — see [`root_cuts_per_round`].
const MAX_CUTS_PER_ROUND: usize = 4;

/// The root loop's per-round cut budget. Equal to the node budget by default — the raised
/// value that improves root closure did not survive the full-solve gate. See
/// [`root_cuts_per_round`] and [`MAX_GMI_ROUNDS`].
const ROOT_CUTS_PER_ROUND: usize = MAX_CUTS_PER_ROUND;

/// Separate Gomory mixed-integer cuts from the basis `cand`.
///
/// The cut is derived from the tableau row of a basic INTEGER variable sitting at
/// a fractional value. Writing the row against the non-basic variables shifted to
/// their bounds (`t_j >= 0`),
///
/// ```text
///   z_B[i] + Σ_j ᾱ_ij t_j = x̄_i,     f0 = frac(x̄_i) ∈ (0,1)
/// ```
///
/// the GMI inequality `Σ_j coef_j · t_j >= f0` holds for every mixed-integer point,
/// with `coef` taking the integer form on integer `t_j` and the continuous form
/// otherwise. This is the cut family that actually closes the gap on these
/// instances — cover cuts separate almost nothing on mixed-sign rows, and the
/// search is bound-limited, not incumbent-limited.
///
/// ## Exactness, and why the last step matters
///
/// EVERYTHING here is exact rational: the row of `B⁻¹` comes from an exact `Bᵀ u =
/// e_i` solve, and `ᾱ`, `x̄_i`, `f0` and every coefficient follow exactly. A cut is
/// the one artifact in a MILP solver that can silently delete the optimum, so none
/// of it is left to a float.
///
/// But [`Model`] rows are `f64`, and rounding an exact coefficient to `f64` can
/// TIGHTEN the cut — which would cut off integer points and lose the optimum. So
/// the right-hand side is relaxed by exactly the damage the rounding can do:
/// `Σ_k |ĉ_k − c_k| · max|x_k|` over the box. The stored `f64` cut is then implied
/// by the exact one, and is valid for every integer point of the model.
/// `base_rows`/`base_cols` are the shape of the model BEFORE any cut rows were adopted.
///
/// They cannot be read off `model`: the root loop passes its accumulating `work` model here, so
/// `model.num_rows()` grows every round as cuts are adopted. Deriving the gate from that would
/// make the budget depend on how far the loop had already got — a model wide enough to decline
/// the wider budget could talk itself into it after enough rounds. The shape is a property of
/// the MODEL, not of the loop's progress through it.
///
/// (This was found while chasing an 8-node drift on mas76 and is NOT its cause — that turned out
/// to be sub-MIPs, which are separate models and are classified on their own shape. The latent
/// defect here is real anyway.)
pub(crate) fn separate_gmi(
    model: &Model,
    lp: &FloatLp,
    cand: &Candidate,
    deadline: Option<std::time::Instant>,
    base_rows: usize,
    base_cols: usize,
) -> Vec<Cut> {
    // Only the ROOT loop calls this entry point; every node site calls
    // `separate_gmi_budget` with its own budget, so the root budget stays root-scoped.
    separate_gmi_budget(
        model,
        lp,
        cand,
        deadline,
        root_cuts_per_round_for_shape(base_rows, base_cols),
    )
}

/// [`separate_gmi`] with an explicit per-call cut budget. The root loop keeps its tuned
/// `cuts_per_round()`; the node-level plateau rounds (bab.rs) ask for more rows per visit,
/// because a node vertex offers many fractional basics and only the ones still violated
/// AFTER the root-frame bound shift survive — the caller filters, so the budget here is
/// a derivation cap, not a selection.
pub(crate) fn separate_gmi_budget(
    model: &Model,
    lp: &FloatLp,
    cand: &Candidate,
    deadline: Option<std::time::Instant>,
    budget: usize,
) -> Vec<Cut> {
    let (n, m) = (lp.n, lp.m);
    // LET THE BUDGET GOVERN, not a row count.
    //
    // The obvious guard here is a cap on `m`, and it is the wrong one, because rows do not predict
    // the cost: qnet1's 503-row basis separates in 1.7s and air05's 426-row basis takes 11.2s. Nor
    // is the factorisation the expense -- air05 factors in 0.33s of those 11.2s. The cost is in the
    // BACK-SOLVE: `u`, a row of `B⁻¹`, carries rationals hundreds of bits wide, and every one of the
    // 7,000 nonbasic columns is dotted against it. What that cost tracks is the basis's fill-in and
    // its bit growth, and no cheap function of `m` sees either.
    //
    // So the separator holds a deadline and stops at a cut boundary when it runs out, and a hard cap
    // stays only as a backstop against a basis so large that even one cut overruns.
    //
    // That reasoning was right and the CAP DID NOT FOLLOW IT: at 600 it was refusing 63% of the
    // corpus on a quantity the note itself says predicts nothing, because the real thing the number
    // held back was an O(m²) allocation two screens down. That allocation is gone (see the `bt`
    // assembly below and [`SparseExactLu`]), and `gmi_max_basis_rows` now documents what the number
    // is a backstop FOR.
    if m == 0 || m > gmi_max_basis_rows() {
        return Vec::new();
    }
    let mut is_basic = vec![false; lp.cols];
    for &j in &cand.basis {
        if j >= lp.cols || is_basic[j] {
            return Vec::new();
        }
        is_basic[j] = true;
    }
    // A free non-basic has no bound to shift to, so `t_j >= 0` is meaningless and the
    // derivation does not hold FOR A ROW THAT USES IT. This used to bail on the whole
    // model at the first free column, which is far more than the derivation requires and
    // was measured to be expensive: a free non-basic appears in a tableau row only where
    // its ᾱ_ij is nonzero, and a row where it is zero never mentions it. On the
    // 133-instance Gurobi-comparable tier the model-wide bail was a large part of why the
    // root cut loop separated NOTHING on half the corpus (control30-3-2-3: 512 rows, a
    // 2.1e7 integrality gap, and GMI — the only family its structure admits — returned dry).
    //
    // The check now lives per row, at the one place the derivation actually needs it (see
    // `free_nb` below): the row is abandoned if a free non-basic has a NONZERO coefficient
    // in it, and kept otherwise. Strictly fewer rows are refused and no row is accepted
    // that the old code would have derived differently — the cuts are the same cuts.
    let nonbasic: Vec<usize> = (0..lp.cols).filter(|&j| !is_basic[j]).collect();
    let free_nb: Vec<bool> = (0..lp.cols)
        .map(|j| matches!(cand.at[j], NbBound::Zero))
        .collect();
    let any_free = free_nb.iter().any(|&f| f);

    let is_int = |j: usize| -> bool {
        j < n && !matches!(model.col_kind(Col(j as u32)), ColKind::Continuous)
    };

    // No fractional integer basic ⟹ no candidate rows ⟹ every line of exact
    // setup below (column conversion, Bᵀ assembly, the LU factorization) is
    // wasted. Free to check, and it is the whole bill on an integral vertex.
    if !cand.basis.iter().any(|&bvar| {
        if !is_int(bvar) {
            return false;
        }
        let v = cand.values[bvar];
        let f = v - v.floor();
        (FRAC_TOL..=1.0 - FRAC_TOL).contains(&f)
    }) {
        return Vec::new();
    }

    // Exact columns of the STRUCTURAL matrix, converted ONCE. `m_column`
    // allocated a fresh `Vec<BigRational>` — one f64→BigRational conversion per
    // entry — every time it was asked, and the loops below used to ask for the
    // same column once per cut (and the logical-dissolve asked for ALL of them
    // per logical coefficient). The arithmetic runs on [`Rational`] (inline
    // i64/i64, exact big fallback): same numbers, same cuts, a fraction of the
    // allocations. Logical columns stay implicit (a single −1 at row `j − n`).
    use ay_lra::rational::Rational;
    let ecol: Vec<Vec<(u32, Rational)>> = (0..n)
        .map(|j| {
            lp.column(j)
                .map(|(r, a)| {
                    (
                        r as u32,
                        Rational::from_big(exact(a).expect("finite coefficient")),
                    )
                })
                .collect()
        })
        .collect();
    // The same data row-major: what the logical-dissolve needs (it used to scan
    // every structural column per logical, O(n·nnz) a coefficient).
    let mut rows_of: Vec<Vec<(u32, Rational)>> = vec![Vec::new(); m];
    for (j, col) in ecol.iter().enumerate() {
        for (r, a) in col {
            rows_of[*r as usize].push((j as u32, a.clone()));
        }
    }

    let nb_value = |j: usize| -> Option<Rational> {
        match cand.at[j] {
            NbBound::Lower => exact(lp.lower[j]).map(Rational::from_big),
            NbBound::Upper => exact(lp.upper[j]).map(Rational::from_big),
            NbBound::Zero => Some(Rational::zero()),
        }
    };

    // A basis has one column per row slot. The dense assembly below used to index
    // `bt[k]` straight from this iteration, which PANICS on a longer basis; the
    // sparse one would silently factor a non-square matrix instead. Neither is an
    // answer, so a malformed candidate is refused here.
    if cand.basis.len() != m {
        return Vec::new();
    }

    // Bᵀ, factored ONCE; each cut row is a back-solve, not another elimination.
    //
    // SPARSE, AND THAT IS A MEMORY DECISION, NOT A SPEED ONE. This used to be
    // `vec![vec![Rational::zero(); m]; m]` — m² rationals, unconditional, built
    // out of a basis that is sparse (one structural column's non-zeros, or a
    // single −1 for a logical) and allocated BEFORE the deadline was consulted, so
    // an already-expired deadline still paid for it in full. Measured peak RSS (3
    // repetitions per point) grew QUADRATICALLY with it: 50 MB at m=1048 up to
    // 3329 MB at m=10765 — 66x the bytes for 10.3x the rows — against 19 MB and
    // 78 MB on this assembly. Extrapolated to the corpus's largest model (169,576
    // rows) the dense array alone is ~1 PB. That allocation, not the factor time,
    // is what the
    // 600-row cap above was actually holding back — see [`SparseExactLu`] for the
    // cost-curve study that refuted the time reading, and `gmi_max_basis_rows` for
    // what the cap became once the quadratic term was gone.
    let mut bt: Vec<Vec<(u32, Rational)>> = Vec::with_capacity(m);
    for &j in &cand.basis {
        if j < n {
            bt.push(ecol[j].clone());
        } else {
            bt.push(vec![((j - n) as u32, -Rational::new(1, 1))]);
        }
    }
    // The deadline goes INTO the factorization: rational elimination's cost is
    // bit growth, which nothing up front can price (air05's 426-row basis
    // factors in 0.33s; domset mw19's 468-row covering basis was measured at
    // 72s — four times the whole cut share — while the per-cut checks below
    // waited politely for a loop that had not started).
    let lu = if dense_gmi_lu() {
        let mut dense = vec![vec![Rational::zero(); m]; m];
        for (k, row) in bt.iter().enumerate() {
            for (r, a) in row {
                dense[k][*r as usize] = a.clone();
            }
        }
        let Some(f) = ExactLu::factor_with_deadline(dense, deadline) else {
            return Vec::new();
        };
        BasisLu::Dense(f)
    } else {
        let bt_nnz: usize = bt.iter().map(Vec::len).sum();
        let Some(f) = SparseExactLu::factor_with_deadline(bt, deadline) else {
            return Vec::new();
        };
        if crate::debug_flags::milp_debug_flags().trace {
            eprintln!(
                "--trace   gmi lu: m={m} basis_nnz={bt_nnz} factor_nnz={} fill={:.2}x dense_would_be={}",
                f.factor_nnz(),
                f.factor_nnz() as f64 / bt_nnz.max(1) as f64,
                m * m,
            );
        }
        BasisLu::Sparse(f)
    };

    let one = Rational::new(1, 1);
    let mut cuts = Vec::new();
    // Read the fused-arithmetic kill switch ONCE for the whole separation call —
    // a loop-invariant branch the predictor pins, never a per-term env read.
    let use_fma = cut_fma_enabled();

    for (i, &bvar) in cand.basis.iter().enumerate() {
        if cuts.len() >= budget {
            break;
        }
        // Each cut is a back-solve against a wide rational basis, and on a model like air05 one of
        // them is a second of wall clock. Stop at a cut boundary rather than overrun the round.
        if deadline.is_some_and(|d| std::time::Instant::now() >= d) {
            break;
        }
        if !is_int(bvar) {
            continue; // only an integer variable can be fractional-in-a-way-that-cuts
        }
        let v = cand.values[bvar];
        let frac = v - v.floor();
        if !(FRAC_TOL..=1.0 - FRAC_TOL).contains(&frac) {
            continue; // already integral enough to cut nothing
        }

        // Row i of B⁻¹: solve Bᵀ u = e_i against the shared factorization.
        let mut e = vec![Rational::zero(); m];
        e[i] = Rational::new(1, 1);
        let ur = lu.solve(&e);

        // ᾱ_ij (shifted to the bound each non-basic rests on) and x̄_i.
        let mut alpha: Vec<(usize, Rational)> = Vec::with_capacity(nonbasic.len());
        let mut xbar = Rational::zero();
        let mut ok = true;
        for &j in &nonbasic {
            let mut raw = Rational::zero();
            if j < n {
                for (r, a) in &ecol[j] {
                    let uv = &ur[*r as usize];
                    if !uv.is_zero() {
                        // Fused `raw += a*uv`: one GCD reduction on the Small path and no
                        // throwaway heap clone on the Big path, same canonical value as
                        // the literal `raw += a.clone() * uv` (`Rational` reduces to a
                        // unique form). This is the hottest exact-rational site in the
                        // separator (the B⁻¹-row back-solve dotted against every column).
                        if use_fma {
                            raw.mul_add_assign(a, uv);
                        } else {
                            raw += a.clone() * uv;
                        }
                    }
                }
            } else {
                raw = -&ur[j - n];
            }
            // THE FREE-NON-BASIC TEST, at the one place it is needed. `t_j = x_j − l_j`
            // does not exist for a free column, so a row whose ᾱ_ij is nonzero there
            // cannot be shifted into the `t >= 0` frame the GMI derivation rests on and
            // is abandoned. A zero coefficient means the row does not mention the column
            // at all, and refusing that row would refuse a cut for a variable it is
            // independent of.
            if any_free && free_nb[j] && !raw.is_zero() {
                ok = false;
                break;
            }
            let Some(val) = nb_value(j) else {
                ok = false;
                break;
            };
            // `&raw * &val` runs the identical `Mul for &Rational` the clone form did,
            // minus the deep clone of `raw` (needed intact below for `shifted`).
            xbar -= if use_fma {
                &raw * &val
            } else {
                raw.clone() * &val
            };
            // t_j = z_j − lo_j at a lower bound (coefficient unchanged); at an upper
            // bound t_j = up_j − z_j, which flips it.
            let shifted = if matches!(cand.at[j], NbBound::Upper) {
                -raw
            } else {
                raw
            };
            if !shifted.is_zero() {
                alpha.push((j, shifted));
            }
        }
        if !ok {
            continue;
        }
        let f0 = &xbar - &Rational::from_integer(xbar.floor());
        if f0.is_zero() || f0 >= one {
            continue;
        }
        let one_minus_f0 = &one - &f0;

        // The GMI coefficients.
        let mut coef: Vec<(usize, Rational)> = Vec::with_capacity(alpha.len());
        for (j, a) in &alpha {
            let c = if is_int(*j) {
                let fj = a - &Rational::from_integer(a.floor());
                if fj <= f0 {
                    fj
                } else {
                    f0.clone() * (&one - &fj) / one_minus_f0.clone()
                }
            } else if a.is_positive() {
                a.clone()
            } else {
                f0.clone() * (-a) / one_minus_f0.clone()
            };
            if !c.is_zero() {
                coef.push((*j, c));
            }
        }
        if coef.is_empty() {
            continue;
        }

        // Back into the structural variables. A logical `s_r` is `Σ_k a_rk x_k`, so
        // it dissolves into the row it came from.
        let mut cx = vec![Rational::zero(); n];
        let mut konst = Rational::zero(); // the cut is Σ cx·x + konst >= f0
        for (j, c) in &coef {
            let at_upper = matches!(cand.at[*j], NbBound::Upper);
            let Some(bound) = nb_value(*j) else {
                ok = false;
                break;
            };
            // t_j = (z_j − bound) at lower, (bound − z_j) at upper.
            // c · sign · z_j  +  c · (−sign · bound)
            let sc = if at_upper { -c } else { c.clone() };
            // `&sc * &bound` is the same `Mul for &Rational`, minus the clone of `sc`
            // (still needed below). `cx[k] += &sc * a` likewise elides the per-term
            // clone in the logical-dissolve inner loop.
            if use_fma {
                konst -= &sc * &bound;
                if *j < n {
                    cx[*j] += sc;
                } else {
                    let r = *j - n;
                    for (k, a) in &rows_of[r] {
                        cx[*k as usize].mul_add_assign(&sc, a);
                    }
                }
            } else {
                konst -= sc.clone() * &bound;
                if *j < n {
                    cx[*j] += sc;
                } else {
                    let r = *j - n;
                    for (k, a) in &rows_of[r] {
                        cx[*k as usize] += sc.clone() * a;
                    }
                }
            }
        }
        if !ok {
            continue;
        }

        // Exact right-hand side: Σ cx·x >= f0 − konst.
        let cx: Vec<BigRational> = cx.into_iter().map(|c| c.to_big()).collect();
        let rhs = (&f0 - &konst).to_big();

        // Down to f64, paying for the rounding. Each coefficient moves by at most
        // |ĉ − c|, and `x_k` is bounded by the box, so relaxing the RHS by
        // Σ |ĉ_k − c_k| · max|x_k| makes the f64 cut IMPLIED by the exact one.
        // On a column the box cannot pay for, `coef_to_f64` rounds the coefficient
        // in the direction the column's SIGN makes free instead, and refuses only a
        // genuinely free one. This is a `>=` store (`ub` is `+inf` at the push below).
        let mut f_coeffs: Vec<(Col, f64)> = Vec::new();
        let mut damage = BigRational::zero();
        for (k, c) in cx.iter().enumerate() {
            if c.is_zero() {
                continue;
            }
            let col = Col(k as u32);
            let Some((cf, cost)) = coef_to_f64(model, col, c, CutSide::Ge) else {
                ok = false;
                break;
            };
            damage += cost;
            f_coeffs.push((col, cf));
        }
        if !ok {
            // FORGONE COST (see `sepstat::discarded`). The exact cut is already
            // built: `cx`/`rhs` are complete, and this refusal throws them away.
            // The gate's implicit claim is that what it discards is worthless, and
            // that claim is checkable for free HERE, because evaluating the exact
            // cut at the point it was separating costs one pass over a vector this
            // loop just finished walking.
            //
            // Fire rate cannot answer it -- a refusal that discards a SATISFIED cut
            // costs nothing, and one that discards a VIOLATED cut is capability the
            // model had and did not get. Only the second number is a finding, and
            // the two are indistinguishable in a count of refusals.
            let mut lhs = BigRational::zero();
            for (k, c) in cx.iter().enumerate() {
                if c.is_zero() {
                    continue;
                }
                // `cand.values` is f64 ADVICE, which is the right precision for a
                // census: this decides nothing, and a bound is never admitted from
                // it. `exact` fails only on a non-finite value, where "was it
                // violated" has no answer and abstaining is correct.
                let Some(xk) = cand.values.get(k).copied().and_then(exact) else {
                    lhs = rhs.clone();
                    break;
                };
                lhs += c * xk;
            }
            crate::sepstat::discarded(lhs < rhs);
        }
        if !ok || f_coeffs.is_empty() {
            continue;
        }
        let safe_rhs = &rhs - &damage;
        let Some(mut lb) = safe_rhs.to_f64() else {
            continue;
        };
        if !lb.is_finite() {
            continue;
        }
        // Round the stored bound DOWN, so `f64` conversion cannot tighten it either.
        lb -= lb.abs().mul_add(f64::EPSILON, f64::MIN_POSITIVE);

        // The identity digest, at the last point the cut is still exactly what this
        // separator decided (see `sepstat::gmi_cut`). This is the evidence the
        // sparse factorization's "same cuts" claim rests on.
        crate::sepstat::gmi_cut(lb, f_coeffs.iter().map(|(c, v)| (c.0, *v)));

        cuts.push(Cut {
            coeffs: f_coeffs,
            ub: f64::INFINITY,
            lb,
        });
    }
    cuts
}

// ---------------------------------------------------------------------------------------------
// MIXED-INTEGER ROUNDING (MIR) CUTS, from the ORIGINAL rows.
// ---------------------------------------------------------------------------------------------

/// Separate MIR cuts from the model's own rows.
///
/// # Why this family, and why the two already here cannot do its job
///
/// The three MIPLIB instances this engine cannot prove (air05, qnet1, rout) all fail identically:
/// the tree reaches ZERO leaves, because the root bound is nowhere near the optimum -- rout 981.86
/// against 1077.56, qnet1 14274 against 16030. And the cuts it already has do NOTHING about that.
/// Measured: rout's root bound is 981.864286 with cuts and 981.864286 without, identical to six
/// decimals -- and NOT because those cuts are invalid or unviolated (each was checked; they cut the
/// relaxation's own vertex off by 0.04 to 0.57). The LP is simply DEGENERATE, so removing one
/// optimal vertex just moves it to the next.
///
/// GMI is read off the TABLEAU, so a degenerate tableau gives it nothing to say. MIR is read off
/// the MODEL, and says something a tableau cannot: given
///
/// ```text
///   Σ_{j integer} a_j y_j  +  Σ_{j continuous} a_j s_j  <=  b ,      y, s >= 0
/// ```
///
/// and writing `f = b − ⌊b⌋` and `f_j = a_j − ⌊a_j⌋`, the inequality
///
/// ```text
///   Σ_j ( ⌊a_j⌋ + max(0, (f_j − f) / (1 − f)) ) · y_j  +  Σ_{a_j < 0} a_j/(1 − f) · s_j  <=  ⌊b⌋
/// ```
///
/// is valid for every integer point of the row. It is the rounding argument the LP cannot make for
/// itself, applied to the ROW rather than to a basis -- so degeneracy has no purchase on it.
///
/// # How it is made safe
///
/// A cut is the one thing in a MILP solver that can silently delete the optimum. So:
///   * every coefficient is derived in EXACT rationals, never in `f64`;
///   * a row is only used when the columns it touches are BOUNDED on the side the substitution
///     needs -- an unbounded column cannot be shifted to `>= 0` and the derivation does not hold
///     without that;
///   * the `f64` cut that finally reaches the model has its right-hand side RELAXED by exactly the
///     damage the rounding to `f64` can do (`Σ |ĉ_j − c_j| · max|x_j|` over the box), so the stored
///     cut is IMPLIED by the exact one and cannot cut off an integer point the exact one admits.
pub(crate) fn separate_mir(model: &Model, x: &[f64], n_rows: usize, budget: usize) -> Vec<Cut> {
    let t = crate::sepstat::on().then(std::time::Instant::now);
    let out = separate_mir_family(model, x, n_rows, budget, mir_from_row);
    crate::sepstat::add(&crate::sepstat::MIR_CUTS, out.len() as u64);
    if let Some(t) = t {
        crate::sepstat::add(&crate::sepstat::SEP_NS, t.elapsed().as_nanos() as u64);
    }
    out
}

/// Separate STRENGTHENED CHVÁTAL-GOMORY cuts — the same family, same rows, same VUB substitution as
/// `separate_mir`, rounded by the tighter Letchford–Lodi step function (`strongcg_round`) instead of
/// MIR. Strong CG and MIR do not dominate each other, so this runs BESIDE `separate_mir` and the
/// pool keeps whichever cut is deeper per row; Gurobi's qnet1 root log carries both.
///
/// SELF-GATING is inherited unchanged: `separate_mir_family` returns nothing on an all-BINARY
/// model (see `mir_family_inert`), so the dense-binary ladder — where GMI already saturates —
/// separates zero strong CG cuts and its search is bit-identical. It now also runs on an
/// all-integral model with GENERAL integer columns, and there it is NOT the load-bearing half:
/// haprp proves in 27.0s / 88,481 nodes with `--no-strongcg` against 63.2s / 357,624
/// with it on. See `mir_family_inert` for the full verdict. `--no-strongcg` is the kill
/// switch.
pub(crate) fn separate_strongcg(
    model: &Model,
    x: &[f64],
    n_rows: usize,
    budget: usize,
) -> Vec<Cut> {
    if crate::tune::caller_flag(crate::tune::Knob::NoStrongcg) == Some(true) {
        return Vec::new();
    }
    let t = crate::sepstat::on().then(std::time::Instant::now);
    let out = separate_mir_family(model, x, n_rows, budget, strongcg_from_row);
    crate::sepstat::add(&crate::sepstat::SCG_CUTS, out.len() as u64);
    if let Some(t) = t {
        crate::sepstat::add(&crate::sepstat::SEP_NS, t.elapsed().as_nanos() as u64);
    }
    out
}

/// The row-selection + substitution core SHARED by `separate_mir` and `separate_strongcg`. `row_fn`
/// is the per-row derivation (`mir_from_row` or `strongcg_from_row`); everything else — the
/// self-gate, the fractional-column scan, the one-shot VUB scan, the both-orientations row loop, and
/// the efficacy ranking — is common to both families.
/// The variable-upper-bound map, precomputed for a caller that separates MANY times against the
/// SAME model — the node-level cut engine (`bab.rs`). The scan is a full model pass; inside a tree
/// it would otherwise run per separation round against rows that never change.
pub(crate) type Vubs = std::collections::HashMap<usize, (BigRational, usize)>;

thread_local! {
    /// The delta budget `best_over_deltas` honors — `MAX_DELTAS` except inside
    /// [`node_delta_scope`]. Thread-local because the row derivations are `fn` pointers
    /// (their signature cannot grow a parameter without touching every family) and the
    /// engine is single-threaded per solve.
    static DELTA_CAP: std::cell::Cell<usize> = const { std::cell::Cell::new(MAX_DELTAS) };
}

/// Run `f` with the node-level delta budget in force (see the note in `best_over_deltas`).
pub(crate) fn node_delta_scope<T>(f: impl FnOnce() -> T) -> T {
    struct Restore(usize);
    impl Drop for Restore {
        fn drop(&mut self) {
            DELTA_CAP.with(|c| c.set(self.0));
        }
    }
    let _r = Restore(DELTA_CAP.with(std::cell::Cell::get));
    DELTA_CAP.with(|c| c.set(NODE_DELTA_CAP));
    f()
}

/// Node rounds keep δ = 1 plus the three leading integral-coefficient magnitudes (and their
/// halvings, `cap / 2` of them) — measured on rout to carry the violated node cuts at a quarter
/// of the full list's exact-rational bill.
const NODE_DELTA_CAP: usize = 4;
pub(crate) fn node_vubs(model: &Model) -> Vubs {
    if crate::tune::on(crate::tune::Knob::NoVub) {
        Vubs::new()
    } else {
        variable_upper_bounds(model)
    }
}

/// `separate_mir` against a precomputed VUB map (see [`node_vubs`]) — same family, same ranking;
/// only the per-call model scan is factored out, and the caller may RESTRICT the derivation to
/// given `(row, negate)` orientations. The node-level engine passes the rows TIGHT at the node's
/// vertex (nonbasic slack, on the tight side): the exact-rational delta search is the entire cost
/// of a separation round, and a MIR cut derived from a row that is slack at the point is almost
/// never violated there — the restriction spends the rationals only where a cut can bite.
pub(crate) fn separate_mir_cached(
    model: &Model,
    x: &[f64],
    orients: Option<&[(u32, bool)]>,
    budget: usize,
    vubs: &Vubs,
) -> Vec<Cut> {
    separate_mir_family_with(
        model,
        x,
        model.num_rows(),
        budget,
        mir_from_row,
        vubs,
        orients,
    )
}

/// THE MIR-CLASS SELF-GATE — the models on which `separate_mir` / `separate_strongcg` /
/// `separate_mir_agg` provably have nothing to say, and so decline to be paid for.
///
/// The gate used to read ALL-INTEGRAL: "no continuous column, nothing for the bound substitution
/// to reason about". Half of that is right and half of it was a MEASURED LOSS. What the family
/// adds over GMI on a CONTINUOUS column is bound substitution and the `x <= u·y` VUB rewrite —
/// none of which a 0/1 column offers, since a binary is already at a bound on both sides and the
/// MIR step function collapses to something GMI has already found. That half is kept: the
/// journal's own measurement is that opening the family on the 70-binary benchmark cost
/// 9.8s -> 11.8s for no cuts at all, so a 0/1 model still declines to pay for the scan.
///
/// A GENERAL INTEGER column is a different object, and the old predicate swept it into the same
/// bin. `x_j ∈ {0..u}` with a non-unit coefficient is exactly what MIR's `⌊a/δ⌋ + (f_j−f)⁺/(1−f)`
/// step function was built for. Measured on `haprp` (1048 rows, 1828 general integers, ZERO
/// binaries), the difference is the instance:
///
/// ```text
///   root closure   0 cuts, gain 0   ->  24 cuts, gain 7042.4578 of a 7317.47 gap (96.2%)
///   300s solve     BOUND 3666028.211734 @ 640,876 nodes, NO INCUMBENT AT ALL
///                  ->  OPTIMAL 3673280.681685 in 63.2s @ 357,624 nodes
/// ```
///
/// (HiGHS reports 3673280.68169 on the same file; the manifest's 3673280.6808 is the less
/// precise number — do NOT read ay/HiGHS agreement here as a reference violation.)
/// `neos-3083819-nubu` is the second signal: root closure 0% -> 54.3%, and at 300s its
/// primal-dual gap closes 68,185 -> 12,344.
///
/// ⚠ MIR, NOT STRONG CG, IS WHAT CARRIES haprp — measured, against the opposite expectation.
/// `--no-strongcg` proves haprp in 27.0s at 88,481 nodes against 63.2s at 357,624 with
/// strong CG on, so on this instance the strengthened rounding is a 2.3x COST that the MIR cuts
/// pay for anyway. It is left on because it is corpus-wide neutral-to-positive here (it is part
/// of every "BETTER" row of the sweep below and costs no verdict), but nothing in this change
/// rests on it, and `--no-strongcg` is the arm if the tree-size cost is chased later.
///
/// So the predicate is BINARY, not integral. Of 379 corpus instances 128 are all-integral and
/// trip this gate; by THIS reader's own classification 63 of those are pure 0/1 and keep their
/// historical path bit-for-bit, and 65 carry at least one general integer column and are what
/// the family can now see. (The bench manifest's `bins` column is HiGHS's and says 66/62: it
/// counts `eil33-2`, `eilA101-2` and `qap10` as binary where `mps.rs` reads their integer
/// columns as general integers. All three separate ZERO cuts either way, so the discrepancy
/// costs nothing — but the ledger of what changed is the READER's, not the manifest's.)
///
/// Measured root closure over the admitted set, serial, one binary per arm: 16 BETTER / 0 WORSE
/// / 30 same on the 46 non-large members, and on the 16 large members every difference is on an
/// instance separating ZERO cuts in BOTH arms (the diag's "gain" there is two differently
/// budgeted LP solves, and the CONTROL alone spans 47.14-51.18 on comp07-2idx across three
/// runs). On 35 pure-binary members the cut COUNT is identical on all 35 and the gain identical
/// to the digit wherever any cut exists; a 20-instance pure-binary SOLVE A/B at 30s matches
/// every verdict and every value, with node counts identical on all five it proves.
///
/// WHAT IT COSTS, honestly. Over the admitted set at a 30s budget: 0 verdicts gained, 0 lost,
/// 0 soundness violations, and the node geomean over the four instances both arms prove is
/// 1.61 — the vertex/fractionality trade this crate has measured before (`gt2` closes 8.7% ->
/// 89.6% of its root gap and its tree goes 272 -> 514 nodes; `decomp2` still proves -160 but at
/// 702 -> 2,477 nodes). Two instances are worse in a way the cuts cause and time does not fix:
/// `neos-3024952-loue`'s incumbent at 60s is 32,889 -> 35,291 against an optimum of 26,756
/// (its dual bound is better, 22,882 -> 22,925), and `neos-4738912-atrato`'s 60s dual bound is
/// 207.6M -> 169.6M against an optimum of 283.6M. They are the price of haprp.
///
/// `AY_MILP_NO_MIR_GENINT` restores the all-integral predicate byte-identically — the A/B arm the
/// numbers above were taken against, and the escape hatch if a general-integer model ever pays
/// for separation it does not get back.
fn mir_family_inert(model: &Model) -> bool {
    if mir_genint_off() {
        return (0..model.num_cols()).all(|j| model.col_kind(Col(j as u32)).is_integral());
    }
    (0..model.num_cols()).all(|j| model.col_kind(Col(j as u32)) == ColKind::Binary)
}

/// Kill switch for [`mir_family_inert`]'s narrowing — restores the historical all-integral gate.
fn mir_genint_off() -> bool {
    // B11: caller-layer switch (`with_mir_genint(false)`); the never-set
    // AY_MILP_NO_MIR_GENINT env read is gone. Per-separation-round call, so
    // the thread-local lookup replaces the process-global cache that would
    // otherwise pin the first solve's setting.
    crate::tune::on(crate::tune::Knob::NoMirGenint)
}

/// Is this a model the NARROWED gate newly admits — all-integral, with at least one general
/// integer column? The root cut loop uses this to charge the MIR class a wall budget on exactly
/// this set and on no other: these are the models where the class is NEW, so there is no
/// historical separation wall to preserve, and (measured) they are where it is expensive.
///
/// With `AY_MILP_NO_MIR_GENINT` set this is `false` everywhere, because `mir_family_inert` is
/// then true on every all-integral model — so the kill switch restores the historical path
/// including the absence of any budget.
pub(crate) fn mir_class_newly_admitted(model: &Model) -> bool {
    model.num_cols() > 0
        && (0..model.num_cols()).all(|j| model.col_kind(Col(j as u32)).is_integral())
        && !mir_family_inert(model)
}

thread_local! {
    /// The wall-clock deadline the MIR-class row loops stop at, or `None` for the historical
    /// unbounded behaviour. Thread-local for exactly the reason [`DELTA_CAP`] is: the row
    /// derivations are `fn` pointers whose signature cannot grow a parameter without touching
    /// every family, and the engine is single-threaded per solve.
    static SEP_WALL: std::cell::Cell<Option<std::time::Instant>> =
        const { std::cell::Cell::new(None) };
}

/// Run `f` with a wall budget on the MIR-class row loops (`None` = unbounded, the historical
/// behaviour and what every caller outside the root loop passes).
///
/// WHY THE CLASS NEEDS ONE AT ALL. Narrowing the self-gate (see [`mir_family_inert`]) makes MIR
/// and strong CG separate on all-integral models with general integer columns — and on a wide
/// one that is not free. Measured on `30n20b8` (576 rows, 18,380 columns) at the default 15%
/// root-cut share of a 60s budget, a round's MIR + strong CG costs 3.3s where the whole round
/// used to cost 0.07s. That wall is not the problem by itself; what it does is push the round
/// past `d − 1.5·round_lp_secs`, which is the clamp `separate_gmi`'s own deadline is computed
/// from — so GMI, which runs LAST among the round's expensive steps, got a deadline ALREADY IN
/// THE PAST and returned zero cuts without factorising anything. The instance's whole root
/// closure is GMI's: 149.4226 of gain became 148.4849 (its second and third cuts lost), and the
/// MIR-class rows that displaced them sparsified away to nothing. Confirmed by handing the loop
/// the whole budget (`AY_MILP_CUT_SHARE=1.0`): GMI reappears and the gain is 149.4226 to the
/// digit, identical to the pre-narrowing arm. The regression was WALL, not cut quality.
///
/// THE BUDGET. The class stops at
/// `max( min(now + (d−now)/2, d − 1.5·round_lp_secs), now + round_lp_secs )`, one absolute
/// instant computed BEFORE MIR runs and shared by MIR and strong CG (a fresh half-tail per
/// family would let the second one spend the reservation the first one left). The two inner
/// clamps are `separate_gmi`'s, for the same reason: one family may not spend the wall the
/// round's adopting re-solve needs. The outer floor is what keeps the budget from suppressing
/// the family on a model whose root LP is slower than the whole share (`rococoB10-011000`
/// solves its root LP in 21.5s against a 9s share) — the class may always have as long as the
/// LP it is trying to improve. On 30n20b8 that restores GMI's slot and the 149.4226 gain; on
/// `haprp`, where the round LP is 0.1s and the class needs 0.4s of a 4.5s budget, it never
/// binds.
pub(crate) fn sep_wall_scope<T>(d: Option<std::time::Instant>, f: impl FnOnce() -> T) -> T {
    struct Restore(Option<std::time::Instant>);
    impl Drop for Restore {
        fn drop(&mut self) {
            SEP_WALL.with(|c| c.set(self.0));
        }
    }
    let _r = Restore(SEP_WALL.with(std::cell::Cell::get));
    SEP_WALL.with(|c| c.set(d));
    f()
}

/// Has the MIR-class wall budget run out? `false` when no budget is in force, and the clock is
/// not read at all in that case — this is called once per candidate row.
fn sep_wall_expired() -> bool {
    SEP_WALL
        .with(std::cell::Cell::get)
        .is_some_and(|d| std::time::Instant::now() >= d)
}

fn separate_mir_family(
    model: &Model,
    x: &[f64],
    n_rows: usize,
    budget: usize,
    row_fn: fn(
        &Model,
        &[f64],
        &[(usize, BigRational)],
        &BigRational,
        &std::collections::HashMap<usize, (BigRational, usize)>,
    ) -> Option<Cut>,
) -> Vec<Cut> {
    // The self-gate is re-checked here BEFORE the VUB scan, so a gated model pays
    // neither (see the note inside `_with`).
    if mir_family_inert(model) {
        return Vec::new();
    }
    separate_mir_family_with(model, x, n_rows, budget, row_fn, &node_vubs(model), None)
}

fn separate_mir_family_with(
    model: &Model,
    x: &[f64],
    n_rows: usize,
    budget: usize,
    row_fn: fn(
        &Model,
        &[f64],
        &[(usize, BigRational)],
        &BigRational,
        &std::collections::HashMap<usize, (BigRational, usize)>,
    ) -> Option<Cut>,
    vubs: &Vubs,
    orients: Option<&[(u32, bool)]>,
) -> Vec<Cut> {
    // NOT ON AN ALL-BINARY MODEL -- see `mir_family_inert` for what this gate does and does not
    // exclude. (It used to exclude every all-INTEGRAL model, which cost haprp its proof.)
    if mir_family_inert(model) {
        return Vec::new();
    }

    // EVERY ROW IS A CANDIDATE, AND THE BEST ONES WIN.
    //
    // This used to stop at the first four cuts it could make, in ROW ORDER -- and worse, at the
    // hard constant four rather than the round's actual budget, so every sweep run at twenty-five
    // or sixty cuts a round was silently still getting four, chosen by nothing. Separate from all of
    // them, rank by EFFICACY (the Euclidean depth of the cut, which is scale-free -- a raw violation
    // just prefers cuts whose coefficients happen to be large), and hand the round its budget.
    // WHICH INTEGER COLUMNS ARE FRACTIONAL. A row that mentions none of them has nothing for the
    // rounding to bite on, and there is no point deriving a cut from it at all.
    let frac: Vec<bool> = (0..model.num_cols())
        .map(|j| {
            if !model.col_kind(Col(j as u32)).is_integral() {
                return false;
            }
            let v = x.get(j).copied().unwrap_or(0.0);
            let f = v - v.floor();
            (FRAC_TOL..=1.0 - FRAC_TOL).contains(&f)
        })
        .collect();

    // THE VARIABLE UPPER BOUNDS come from the CALLER (`node_vubs`), scanned once per call site —
    // once per root round, once per TREE for the node-level engine. Rebuilding them inside every
    // row's derivation once made a round quadratic in the rows (qnet1: 1.75s -> 9.93s -> 26.35s
    // over three rounds); rebuilding per round was in turn the node engine's separation bill.

    let mut cand: Vec<Cut> = Vec::new();
    // SEPARATE FROM THE MODEL'S OWN ROWS, NEVER FROM THE CUTS.
    //
    // The working model grows a row per cut, and separating from all of them makes the cost of a
    // round grow with the pool: on qnet1 separation went 1.75s -> 9.93s -> 26.35s over three rounds,
    // which is what makes a cut loop unaffordable however cheap each cut is. A cut derived from a
    // cut is also the weakest thing the family produces. So the model's rows, and only those.
    // Both orientations of every candidate row — or exactly the orientations the caller named
    // (a `>=` row is a `<=` row negated).
    let all_orients: Vec<(u32, bool)>;
    let orients: &[(u32, bool)] = match orients {
        Some(o) => o,
        None => {
            all_orients = (0..n_rows.min(model.num_rows()) as u32)
                .flat_map(|r| [(r, false), (r, true)])
                .collect();
            &all_orients
        }
    };
    for &(r, negate) in orients {
        // STOP AT A ROW BOUNDARY when the class's wall budget runs out (see `sep_wall_scope`;
        // no budget in force means no clock read). The candidates already derived still rank
        // and ship — a truncated search returns fewer cuts, never a wrong one.
        if sep_wall_expired() {
            break;
        }
        if r as usize >= model.num_rows() {
            continue;
        }
        let (coeffs, lb, ub) = model.row(Row(r));
        if !coeffs.iter().any(|&(c, _)| frac[c as usize]) {
            continue; // nothing fractional in it: the rounding has nothing to bite on
        }
        {
            let rhs = if negate { lb } else { ub };
            if !rhs.is_finite() {
                continue;
            }
            let sign = if negate { -1.0 } else { 1.0 };
            crate::sepstat::bump(&crate::sepstat::TERMS_BUILT);
            let terms: Vec<(usize, BigRational)> = coeffs
                .iter()
                .filter_map(|&(c, a)| exact(sign * a).map(|v| (c as usize, v)))
                .filter(|(_, v)| !v.is_zero())
                .collect();
            let Some(rhs) = exact(sign * rhs) else {
                continue;
            };
            if let Some(cut) = row_fn(model, x, &terms, &rhs, vubs) {
                cand.push(cut);
            }
        }
    }
    cand.sort_by(|a, b| {
        efficacy(b, x)
            .partial_cmp(&efficacy(a, x))
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    cand.truncate(budget);
    cand
}

/// How many continuous columns one aggregate may cancel (a MIR cut is emitted after EACH step, so
/// the search keeps every intermediate), how wide a cancelling equality may be, how wide the
/// aggregate may grow, and how many aggregates one call may build. The caps are cost control, not
/// tuning: each eval is one exact-rational aggregation plus one `mir_from_row` delta search.
const MIR_AGG_STEPS: usize = 3;
const MIR_AGG_PARTNER_NNZ: usize = 64;
/// NOT A CUT FILTER, and the cause-6 diagnosis lists it as one. The aggregate is MIR'd after
/// EVERY step, so by the time this fires every cut the chain has produced is already banked in
/// `cand`; what it refuses is the remaining aggregation STEPS, never a built inequality. It also
/// **never fires** over 101 instances (`sepstat::GATE_MIR_AGG_NNZ`, measured 2026-08-01) — no
/// aggregate on the corpus grows past 250 terms inside its three-step budget.
const MIR_AGG_MAX_NNZ: usize = 250;
const MIR_AGG_MAX_EVALS: usize = 1024;

/// MIR ON EQUALITY-AGGREGATED ROWS -- the continuous-cancelling half of c-MIR, separated ONLY in
/// the extension rounds the MIR economy is paying for (see `add_root_cuts`).
///
/// A single-row MIR cut is weakened by every continuous column sitting strictly BETWEEN its
/// bounds: bound substitution shifts the column to its nearer bound and the cut pays
/// `|a_j| · distance` of slack for the privilege -- and a column with no finite bound on the
/// needed side kills the derivation outright (`mir_from_row` returns `None` for the whole row).
/// Aggregation is the classical fix (Marchand-Wolsey): add an exactly-scaled EQUALITY row to
/// CANCEL the offending column, then round the aggregate. An equality may be added with ANY
/// multiplier, so validity is inherited from the two model rows -- and qnet1 is 332 conservation
/// equalities threaded through exactly the continuous flow columns that weaken its capacity rows'
/// MIR cuts; this family is how Gurobi closes 93% of that root gap with 23 cuts.
///
/// The journal above records row aggregation tried once and measured HARMFUL (qnet1's root fell
/// 14,499 -> 14,274), under VIOLATION-ranked selection in two fixed rounds, where the big
/// aggregated rows won the ranking and then said less. This family answers that lesson
/// structurally instead of re-litigating it: it never runs in a base round, and the extension
/// rounds it does run in must each move the root bound MATERIALLY or the extension -- and the
/// family with it -- is cut off. An aggregate that says less cannot buy itself a second round.
///
/// # `the mir-agg-root knob` — the measurement arm for the qnet1 lead
///
/// Stage two is reached only when the PLAIN family dries up mid-round (see the `fresh.is_empty()`
/// gate in `add_root_cuts`). On qnet1 the plain family never dries up, so this separator has
/// never actually run there: `AY_MILP_MIR_EXT_ROUNDS=40` climbs to 15,465 over 21 rounds with
/// ZERO `mir_agg` evals (traced). `the mir-agg-root knob` admits it into every root round the
/// MIR-class families separate in, so the family can be measured against the root bound directly.
/// DEFAULT-OFF: see [`mir_agg_root`] for the measured verdict.
pub(crate) fn separate_mir_agg(model: &Model, x: &[f64], n_rows: usize, budget: usize) -> Vec<Cut> {
    if budget == 0 {
        return Vec::new();
    }
    // The same self-gate as `separate_mir` (`mir_family_inert`): on an all-binary model there is
    // no continuous column to cancel and nothing for the rounding to bite on.
    if mir_family_inert(model) {
        return Vec::new();
    }
    let n_rows = n_rows.min(model.num_rows());
    let vubs = if crate::tune::on(crate::tune::Knob::NoVub) {
        std::collections::HashMap::new()
    } else {
        variable_upper_bounds(model)
    };

    // Which integer columns are fractional at `x` -- a row that mentions none has nothing for the
    // rounding to bite on, aggregated or not.
    let frac: Vec<bool> = (0..model.num_cols())
        .map(|j| {
            if !model.col_kind(Col(j as u32)).is_integral() {
                return false;
            }
            let v = x.get(j).copied().unwrap_or(0.0);
            let f = v - v.floor();
            (FRAC_TOL..=1.0 - FRAC_TOL).contains(&f)
        })
        .collect();

    // The candidate PARTNER rows, indexed by column. An EQUALITY may be added with any
    // multiplier; a one-sided row only with a multiplier that keeps its oriented `<=` sense
    // (checked at use). Equalities first -- they relax nothing -- then sparsest: the cancelling
    // row's OTHER columns are fill the aggregate must carry. Deterministic (vectors in row
    // order, then an explicit sort), never a hash iteration.
    let mut partners_by_col: Vec<Vec<u32>> = vec![Vec::new(); model.num_cols()];
    let mut any_partner = false;
    let is_eq = |r: u32| -> bool {
        let (_, lb, ub) = model.row(Row(r));
        lb.is_finite() && lb == ub
    };
    for r in 0..n_rows {
        let (coeffs, lb, ub) = model.row(Row(r as u32));
        if coeffs.len() < 2 || coeffs.len() > MIR_AGG_PARTNER_NNZ {
            continue;
        }
        if !lb.is_finite() && !ub.is_finite() {
            continue;
        }
        any_partner = true;
        for &(c, a) in coeffs {
            if a != 0.0 {
                partners_by_col[c as usize].push(r as u32);
            }
        }
    }
    if !any_partner {
        return Vec::new(); // nothing to aggregate with
    }
    for v in partners_by_col.iter_mut() {
        v.sort_by_key(|&r| (!is_eq(r), model.row(Row(r)).0.len(), r));
    }

    let mut cand: Vec<Cut> = Vec::new();
    let mut seen: std::collections::HashSet<Vec<(u32, u64)>> = std::collections::HashSet::new();
    let mut evals = 0usize;
    'rows: for r in 0..n_rows {
        // The same row-boundary stop the single-row family takes (`sep_wall_scope`): the
        // aggregate walk is the most expensive thing in the class, at one exact-rational
        // aggregation plus a full delta search per eval.
        if sep_wall_expired() {
            break 'rows;
        }
        let (coeffs, lb, ub) = model.row(Row(r as u32));
        if !coeffs.iter().any(|&(c, _)| frac[c as usize]) {
            continue;
        }
        for negate in [false, true] {
            if evals >= MIR_AGG_MAX_EVALS {
                break 'rows;
            }
            let rhs = if negate { lb } else { ub };
            if !rhs.is_finite() {
                continue;
            }
            let sign = if negate { -1.0 } else { 1.0 };
            // The oriented base row, exact.
            let mut terms: std::collections::BTreeMap<usize, BigRational> =
                std::collections::BTreeMap::new();
            let mut ok = true;
            for &(c, a) in coeffs {
                let Some(v) = exact(sign * a) else {
                    ok = false;
                    break;
                };
                if !v.is_zero() {
                    *terms.entry(c as usize).or_insert_with(BigRational::zero) += v;
                }
            }
            if !ok {
                continue;
            }
            let Some(mut b) = exact(sign * rhs) else {
                continue;
            };
            let mut used: Vec<u32> = vec![r as u32];
            for _step in 0..MIR_AGG_STEPS {
                // THE CANCELLATION TARGET: the continuous column whose bound substitution costs
                // the rounding most -- `|a_j| · (distance to its nearer bound)` -- with a column
                // that has NO finite bound ranked above everything (until it is cancelled the row
                // yields no MIR cut at all). Columns the VUB substitution already handles are not
                // targets: substituting to the switch is the family's strength, not a weakness.
                // WHAT MAY BE CANCELLED. The classical c-MIR target is the interior continuous
                // column (its bound substitution is what weakens the rounding), and the first
                // version of this walk took ONLY those -- and separated NOTHING on qnet1, zero
                // evals, because qnet1's continuous columns are 124 dangling objective
                // definitions (`x = Σ c·y`, one row each) and its whole core is pure-integer.
                // The reach this family was built for is there all the same: a capacity row with
                // `b = 0` yields no MIR cut at any delta (`b/δ` is never fractional), and
                // cancelling one of its INTEGRAL-valued binaries through an SOS equality
                // (`Σ y = 1`) is what turns it into a `b ≠ 0` row the rounding can bite. So:
                // any column is a target EXCEPT an integer sitting at a FRACTIONAL value --
                // those are the surface the cut is made of. Ranking: a continuous column with no
                // finite bound first (the row yields nothing until it goes), then interior
                // columns by the slack their substitution would cost, then bound-sitting ones.
                let mut target: Option<(f64, usize)> = None;
                for (&j, a) in &terms {
                    let col = Col(j as u32);
                    let af = to_f64(a).abs();
                    if af == 0.0 {
                        continue;
                    }
                    let xj = x.get(j).copied().unwrap_or(0.0);
                    let integral = model.col_kind(col).is_integral();
                    if integral {
                        let f = xj - xj.floor();
                        if (FRAC_TOL..=1.0 - FRAC_TOL).contains(&f) {
                            continue; // fractional integer: that is what the rounding cuts on
                        }
                    }
                    let (lo, up) = model.col_bounds(col);
                    let d_lo = if lo.is_finite() {
                        xj - lo
                    } else {
                        f64::INFINITY
                    };
                    let d_up = if up.is_finite() {
                        up - xj
                    } else {
                        f64::INFINITY
                    };
                    let gap = d_lo.min(d_up);
                    let score = if !gap.is_finite() {
                        if integral {
                            continue; // an unbounded integral column: leave it to the rounding
                        }
                        f64::MAX // unbounded continuous: MIR is impossible until this goes
                    } else if gap > 1e-9 {
                        af * gap
                    } else {
                        af * 1e-6 // at a bound: eligible, but every interior column outranks it
                    };
                    if target.as_ref().is_none_or(|&(s, _)| score > s) {
                        target = Some((score, j));
                    }
                }
                let Some((_, j)) = target else {
                    break; // nothing left worth cancelling
                };
                let Some(a_j) = terms.get(&j).cloned() else {
                    break;
                };
                // The best partner not already in the aggregate that can LEGALLY cancel it: an
                // equality with any multiplier, or a one-sided row in whichever orientation
                // makes the cancelling multiplier positive (adding `λ · (oriented row <= rhs)`
                // with `λ > 0` keeps the aggregate a valid `<=` row).
                // (λ, oriented rhs, orientation sign, row)
                let mut chosen: Option<(BigRational, BigRational, BigRational, u32)> = None;
                for &p in partners_by_col[j].iter().filter(|p| !used.contains(p)) {
                    let (pc, plb, pub_) = model.row(Row(p));
                    let Some(e_j) = pc
                        .iter()
                        .find(|&&(c, _)| c as usize == j)
                        .and_then(|&(_, a)| exact(a))
                    else {
                        continue;
                    };
                    if e_j.is_zero() {
                        continue;
                    }
                    let eq = plb.is_finite() && plb == pub_;
                    // Try the `<= ub` orientation (sign +1), then `-row <= -lb` (sign -1).
                    for (sgn_f, rhs_p) in [(1.0f64, pub_), (-1.0, plb)] {
                        if !rhs_p.is_finite() {
                            continue;
                        }
                        // A one-sided partner donates its SLACK to the aggregate verbatim, and a
                        // slack aggregate's MIR cut is almost never violated at `x` -- the same
                        // lesson `AGG_SLACK_SKIP` records for the flow-cover aggregates. An
                        // equality has no slack to donate.
                        if !eq {
                            let act: f64 = pc
                                .iter()
                                .map(|&(c, a)| {
                                    sgn_f * a * x.get(c as usize).copied().unwrap_or(0.0)
                                })
                                .sum();
                            if sgn_f * rhs_p - act > 0.1 * (1.0 + rhs_p.abs()) {
                                continue;
                            }
                        }
                        let sgn = if sgn_f > 0.0 {
                            BigRational::one()
                        } else {
                            -BigRational::one()
                        };
                        let lambda = -&a_j / (&e_j * &sgn);
                        if !eq && lambda <= BigRational::zero() {
                            continue; // this orientation would flip the partner's sense
                        }
                        let Some(rb) = exact(sgn_f * rhs_p) else {
                            continue;
                        };
                        chosen = Some((lambda, rb, sgn, p));
                        break;
                    }
                    if chosen.is_some() {
                        break;
                    }
                }
                let Some((lambda, rb, sgn, prow)) = chosen else {
                    break;
                };
                let (pc, _, _) = model.row(Row(prow));
                let mut ok = true;
                for &(c, a) in pc {
                    let Some(v) = exact(a) else {
                        ok = false;
                        break;
                    };
                    if !v.is_zero() {
                        *terms.entry(c as usize).or_insert_with(BigRational::zero) +=
                            &lambda * &sgn * v;
                    }
                }
                if !ok {
                    break;
                }
                b += &lambda * rb;
                terms.retain(|_, v| !v.is_zero());
                used.push(prow);
                if terms.len() > MIR_AGG_MAX_NNZ {
                    // FORGONE COST, and note what this gate is NOT. It refuses no built cut: the
                    // aggregate is MIR'd after every step (below), so every cut this chain has
                    // produced so far is already in `cand`. What it forgoes is the REMAINING
                    // aggregation steps, and that is the unit charged. Listed among the
                    // "absolute nnz caps" of the cause-6 diagnosis, which is a misreading of the
                    // site worth recording rather than repeating.
                    crate::sepstat::gate_charge(
                        crate::sepstat::GATE_MIR_AGG_NNZ,
                        (MIR_AGG_STEPS.saturating_sub(used.len())) as u64,
                    );
                    break; // the aggregate is turning into a monster; stop feeding it
                }
                // MIR the aggregate after EVERY step: the one-step cut is often the strong one,
                // and the ranking below keeps whichever survives.
                evals += 1;
                let tv: Vec<(usize, BigRational)> =
                    terms.iter().map(|(&j, v)| (j, v.clone())).collect();
                if let Some(cut) = mir_from_row(model, x, &tv, &b, &vubs) {
                    let mut sig: Vec<(u32, u64)> = cut
                        .coeffs
                        .iter()
                        .map(|&(c, a)| (c.0, a.to_bits()))
                        .collect();
                    sig.sort_unstable();
                    sig.push((u32::MAX, cut.ub.to_bits()));
                    if seen.insert(sig) {
                        cand.push(cut);
                    }
                }
                if evals >= MIR_AGG_MAX_EVALS {
                    break;
                }
            }
        }
    }
    cand.sort_by(|a, b| {
        efficacy(b, x)
            .partial_cmp(&efficacy(a, x))
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    if crate::debug_flags::milp_debug_flags().trace {
        eprintln!(
            "--trace   mir_agg: {} candidates from {evals} evals, best efficacy {:.4}, kept {}",
            cand.len(),
            cand.first().map(|c| efficacy(c, x)).unwrap_or(0.0),
            cand.len().min(budget)
        );
    }
    cand.truncate(budget);
    cand
}

mod mir_chain;
pub(crate) use mir_chain::separate_mir_chain_agg;

// ---------------------------------------------------------------------------------------------
// GÜNLÜK–POCHET MIXING CUTS, from the shared lower-bounding continuous of a mixing set.
// ---------------------------------------------------------------------------------------------

/// One usable mixing row `Σ_j a_ij x_j − Σ_{k∈K_i} s_k <= b_i`, split into its structural (integer)
/// terms and the continuous columns that lower-bound it (members of `S`).
struct MixRow {
    /// Right-hand side `b_i`, exact.
    b: BigRational,
    /// `(col, a_ij)` for the structural (non-continuous) columns, exact.
    int_terms: Vec<(usize, BigRational)>,
    /// The continuous columns present with coefficient in `[−1, 0]` — the `s_k` that `S` covers.
    cont_cols: Vec<usize>,
}

/// GÜNLÜK–POCHET MIXING INEQUALITIES on the shared lower-bounding continuous of a mixed-integer
/// knapsack ("mixing") set — the ONE family that structurally reaches past the rank-1 single-row
/// MIR closure that `separate_mir`/`separate_strongcg` saturate on mik-* instances.
///
/// # The set, and why single-row MIR cannot close it
///
/// The mik/mixing rows are `Σ_j a_ij x_j − Σ_{k∈K_i} s_k <= b_i`, `a,b` integer, `x >= 0` integer,
/// `s_k >= 0` continuous. Let `S := Σ_{k∈C} s_k` over the shared continuous columns. Each row gives
/// `Σ_{k∈K_i} s_k >= Σ_j a_ij x_j − b_i =: ρ_i(x)`, and since the other `s_k >= 0`,
///
/// ```text
///   S  >=  Σ_{k∈K_i} s_k  >=  ρ_i(x)      for EVERY row i,   and   S >= 0,
/// ```
///
/// so the feasible set projects onto the MIXING SET `M = {(S,x): S >= ρ_i(x) ∀i, S >= 0}`, with
/// `ρ_i` integer-valued on integer `x`. Single-row MIR rounds each `S >= ρ_i(x)` in ISOLATION; the
/// mik dual gap is exactly the facets that COUPLE many rows through the shared `S`, which no single
/// δ and no number of rounds of the single-row family can express (measured: the mik dual saturates
/// well short of the optimum). Row AGGREGATION cannot form them either — cancelling a shared `−1`
/// continuous between two `<=` rows needs a NEGATIVE multiplier, which flips the `<=` sense.
///
/// # The cut (Günlük–Pochet type-I), derived so it is SOUND by construction
///
/// Scale a chosen row set by `δ > 0`: `β_i = b_i/δ`, and since `x_j >= 0`,
/// `Σ_j (a_ij/δ) x_j >= Σ_j ⌊a_ij/δ⌋ x_j =: G_i(x)` (an integer). So `S/δ >= G_i(x) − β_i`, i.e.
/// with `z_i := G_i(x) − ⌊β_i⌋ ∈ Z` and `μ_i := β_i − ⌊β_i⌋ ∈ (0,1)`,
///
/// ```text
///   t := S/δ >= 0,      t >= z_i − μ_i     for each row i.
/// ```
///
/// Order a subset `T = {t_1..t_r}` by INCREASING `μ` (`0 < μ_{t_1} <= … <= μ_{t_r} < 1`,
/// `μ_{t_{r+1}} := 1`). After mapping `t >= z_i - μ_i` to the canonical
/// Günlük–Pochet form, the type-I mixing inequality is
///
/// ```text
///   t  >=  Σ_{l=1}^r (μ_{t_{l+1}} − μ_{t_l}) · z_{t_l}
/// ```
///
/// is valid for `M` (Günlük–Pochet 2001) — the telescoping weights `μ_{t_{l+1}} − μ_{t_l}` are `>= 0`
/// exactly because `μ` is sorted INCREASING, which is the load-bearing invariant a weak
/// implementation gets wrong. Multiplying by `δ` and substituting `G_i, z_i` back gives the stored
/// cut
///
/// ```text
///   Σ_{k∈S} s_k  −  δ Σ_l (μ_{l+1} − μ_l) Σ_j ⌊a_{t_l,j}/δ⌋ x_j  >=  − δ Σ_l (μ_{l+1} − μ_l) ⌊β_{t_l}⌋,
/// ```
///
/// a `>=` cut valid for `M ⊇` the projection of the MILP feasible set, so it removes only
/// FRACTIONAL points. Every coefficient is exact `BigRational`; the `f64` cut has its right-hand
/// side RELAXED DOWN by the rounding damage (`Σ |ĉ_j − c_j| · max|x_j|`) so it is IMPLIED by the
/// exact one. `mixing_cuts_never_remove_an_integer_point` brute-forces the guarantee.
///
/// The production call site gates on `is_mixed_integer_knapsack` — the same gate the extended MIR
/// rounds are armed by, which excludes every one of the 16 home instances — and this function
/// independently checks the working rows' local signature. Exact-side-store models fail closed.
pub(crate) fn separate_mixing(model: &Model, x: &[f64], n_rows: usize, budget: usize) -> Vec<Cut> {
    if budget == 0 || false || model.has_inexact_coeffs() {
        return Vec::new();
    }
    // NOTE ON THE GATE. The corpus-identity guarantee comes from the CALL SITE, which only invokes
    // this on `is_mixed_integer_knapsack(model)` — the ORIGINAL model. We cannot re-check that here
    // because the caller passes the WORKING model (`work`), which by the extension rounds has
    // accumulated `>=` cut rows and would fail the "every constraint is `<=`" test. So the internal
    // guard is the MIXING SIGNATURE detected directly on the `<=` rows below (a continuous column
    // shared across many of them), which tolerates the added cut rows.
    let n_rows = n_rows.min(model.num_rows());
    let ncols = model.num_cols();
    let is_cont = |j: usize| matches!(model.col_kind(Col(j as u32)), ColKind::Continuous);
    // C: continuous columns with lower bound >= 0 (all the derivation needs of `s_k` is `s_k >= 0`).
    let cont_ok: Vec<bool> = (0..ncols)
        .map(|j| is_cont(j) && model.col_bounds(Col(j as u32)).0 >= 0.0)
        .collect();

    let mut rows: Vec<MixRow> = Vec::new();
    for r in 0..n_rows {
        let (coeffs, lb, ub) = model.row(Row(r as u32));
        if lb.is_finite() || !ub.is_finite() {
            continue; // must be a pure `<=` knapsack row
        }
        let mut ok = true;
        let mut cont_cols: Vec<usize> = Vec::new();
        let mut int_terms: Vec<(usize, BigRational)> = Vec::new();
        for &(c, a) in coeffs {
            if a == 0.0 {
                continue;
            }
            let cj = c as usize;
            if is_cont(cj) {
                // A continuous member of `S`: must be in C and LOWER-BOUND the row (coeff ∈ [−1,0]),
                // so `S >= Σ_{k∈row} (−a_ik) s_k >= ρ_i(x)` holds.
                if !cont_ok[cj] || !(-1.0..=0.0).contains(&a) {
                    ok = false;
                    break;
                }
                cont_cols.push(cj);
            } else {
                // A structural column: the `Σ(a/δ)x >= Σ⌊a/δ⌋x` relaxation needs `x_j >= 0`.
                if model.col_bounds(Col(c)).0 < 0.0 {
                    ok = false;
                    break;
                }
                let Some(av) = exact(a) else {
                    ok = false;
                    break;
                };
                int_terms.push((cj, av));
            }
        }
        if !ok || cont_cols.is_empty() || int_terms.is_empty() {
            continue;
        }
        let Some(b) = exact(ub) else {
            continue;
        };
        rows.push(MixRow {
            b,
            int_terms,
            cont_cols,
        });
    }
    if crate::debug_flags::milp_debug_flags().trace {
        eprintln!(
            "--trace   mixing ENTER: {} usable rows of {} (ncols {})",
            rows.len(),
            n_rows,
            ncols
        );
    }
    if rows.len() < 2 {
        return Vec::new(); // a mixing cut needs a multi-row set to beat single-row MIR
    }
    // The MIXING SIGNATURE, checked on the `<=` rows we kept (so it survives the added cut rows in
    // `work`): a continuous column shared across many rows — the same discriminator
    // `is_mixed_integer_knapsack` uses, which excludes every home instance.
    {
        let mut cont_rowcount: std::collections::HashMap<usize, u32> =
            std::collections::HashMap::new();
        for row in &rows {
            for &k in &row.cont_cols {
                *cont_rowcount.entry(k).or_insert(0) += 1;
            }
        }
        if !cont_rowcount.values().any(|&n| n >= 10) {
            return Vec::new();
        }
    }

    // The divisor scan, the same shape as `best_over_deltas`: δ = 1 does nothing here (`b_i` integer
    // ⇒ `β_i` integer ⇒ `μ_i = 0`), so the useful scalings are the structural coefficient
    // magnitudes (and their doublings), which is where `b_i/δ` lands fractional and the floors
    // couple across rows.
    let deltas = mixing_deltas(&rows);
    let mut cand: Vec<Cut> = Vec::new();
    for delta in &deltas {
        if let Some(cut) = mixing_from_rows(model, x, &rows, delta) {
            cand.push(cut);
        }
    }
    cand.sort_by(|a, b| {
        efficacy(b, x)
            .partial_cmp(&efficacy(a, x))
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    if crate::debug_flags::milp_debug_flags().trace {
        eprintln!(
            "--trace   mixing: {} rows, {} deltas, {} candidates, best efficacy {:.4}, kept {}",
            rows.len(),
            deltas.len(),
            cand.len(),
            cand.first().map(|c| efficacy(c, x)).unwrap_or(0.0),
            cand.len().min(budget)
        );
    }
    cand.truncate(budget);
    cand
}

/// The divisor list for the mixing scan: distinct structural coefficient magnitudes across the
/// mixing rows plus their doublings, capped. `best_over_deltas` keys the single-row family on the
/// SAME magnitudes; the mixing cut reuses them to couple rows the single-row family rounds alone.
fn mixing_deltas(rows: &[MixRow]) -> Vec<BigRational> {
    const MIX_MAX_DELTAS: usize = 64;
    let cap = MIX_MAX_DELTAS.max(1);
    let mut mags: Vec<BigRational> = Vec::new();
    for row in rows {
        for (_, a) in &row.int_terms {
            let m = a.abs();
            if !m.is_zero() {
                mags.push(m);
            }
        }
    }
    mags.sort();
    mags.dedup();
    // Keep an even spread of the distinct magnitudes when there are more than the cap allows, so a
    // single dense band of coefficients cannot crowd out the rest of the range.
    let mut out: Vec<BigRational> = if mags.len() <= cap {
        mags
    } else {
        let step = mags.len() as f64 / cap as f64;
        (0..cap)
            .map(|k| mags[((k as f64) * step) as usize].clone())
            .collect()
    };
    // ...and the doublings of the smallest few, the other half of the c-MIR family (`best_over_deltas`
    // does the same): dividing by `2δ` lands the right-hand side on a different fraction.
    let two = BigRational::from_integer(2.into());
    let base = out.len().min(8);
    for k in 0..base {
        let d = &out[k] * &two;
        if !out.contains(&d) {
            out.push(d);
        }
    }
    out
}

/// Build the single deepest Günlük–Pochet type-I mixing cut for one divisor `δ`, selecting the
/// violated ordered row subset by a dynamic program over the μ-sorted candidates. Returns `None`
/// when no violated multi-row cut exists for this `δ`.
fn mixing_from_rows(model: &Model, x: &[f64], rows: &[MixRow], delta: &BigRational) -> Option<Cut> {
    if delta.is_zero() || delta.is_negative() {
        return None;
    }

    // Per-row mixing data at this δ. `mu = frac(b_i/δ) ∈ (0,1)`; `floors[j] = ⌊a_ij/δ⌋`;
    // `z_f = Σ ⌊a/δ⌋ x_j − ⌊β_i⌋` is the value of the integer variable `z_i` at the LP point.
    struct Cand<'a> {
        mu: BigRational,
        mu_f: f64,
        z_f: f64,
        floor_beta: BigRational,
        floors: Vec<(usize, BigRational)>,
        cont_cols: &'a [usize],
    }
    let mut cs: Vec<Cand<'_>> = Vec::new();
    for row in rows {
        let beta = &row.b / delta;
        let fb = beta.floor();
        let mu = &beta - &fb;
        if mu.is_zero() {
            continue; // integer β: no fractionality, nothing for this row to contribute
        }
        let mut floors: Vec<(usize, BigRational)> = Vec::with_capacity(row.int_terms.len());
        let mut z_f = -to_f64(&fb);
        for (j, a) in &row.int_terms {
            let fa = (a / delta).floor();
            if !fa.is_zero() {
                z_f += to_f64(&fa) * x.get(*j).copied().unwrap_or(0.0);
                floors.push((*j, fa));
            }
        }
        cs.push(Cand {
            mu_f: to_f64(&mu),
            mu,
            z_f,
            floor_beta: fb,
            floors,
            cont_cols: &row.cont_cols,
        });
    }
    if cs.len() < 2 {
        return None;
    }
    // Sort by μ INCREASING — the Günlük–Pochet ordering. Mapping our `t >= z_i − μ_i` onto the
    // canonical mixing set `s + Z_i >= B_i` (with `Z_i = −z_i`, `B_i = −μ_i`) gives fractionalities
    // `f_i = 1 − μ_i`, and GP sorts by DECREASING `f`, i.e. INCREASING `μ`. Ties by z broken
    // deterministically so the cut is reproducible.
    cs.sort_by(|a, b| {
        a.mu.cmp(&b.mu).then(
            b.z_f
                .partial_cmp(&a.z_f)
                .unwrap_or(std::cmp::Ordering::Equal),
        )
    });

    // Pick the ordered subset maximizing the cut's LHS value `V = Σ_l (μ_{p_{l+1}} − μ_{p_l}) z_{p_l}`
    // with the sentinel `μ_{p_{r+1}} := 1` (so the LARGEST-μ row carries weight `1 − μ_{p_r}` and
    // the earlier ones `μ_{p_{l+1}} − μ_{p_l} >= 0`). Adding row `i` after `j` (`μ_j <= μ_i`) changes
    // the running value by exactly `(1 − μ_i)(z_i − z_j)` — a clean DP over the μ-sorted list where
    // `dp[i]` is the best `V` for a chain ENDING at i (its z carrying the sentinel weight `1 − μ_i`).
    let rmax = 8.max(2);
    let n = cs.len();
    let mut dp = vec![f64::NEG_INFINITY; n];
    let mut pred = vec![usize::MAX; n];
    let mut sz = vec![1usize; n];
    let mut best: (f64, usize) = (f64::NEG_INFINITY, usize::MAX);
    for i in 0..n {
        let g_i = 1.0 - cs[i].mu_f; // the sentinel weight `1 − μ_i` of i as the chain's last row
        dp[i] = g_i * cs[i].z_f; // i chosen alone
        pred[i] = usize::MAX;
        sz[i] = 1;
        for j in 0..i {
            if sz[j] >= rmax {
                continue;
            }
            let v = dp[j] + g_i * (cs[i].z_f - cs[j].z_f);
            if v > dp[i] {
                dp[i] = v;
                pred[i] = j;
                sz[i] = sz[j] + 1;
            }
        }
        // Only multi-row chains are new strength; a singleton mixing cut is dominated by MIR.
        if sz[i] >= 2 && dp[i] > best.0 {
            best = (dp[i], i);
        }
    }
    if best.1 == usize::MAX {
        return None;
    }

    // Reconstruct the chain in increasing-μ order `p_1..p_r`.
    let mut chain: Vec<usize> = Vec::new();
    let mut i = best.1;
    while i != usize::MAX {
        chain.push(i);
        i = pred[i];
    }
    chain.reverse();

    // Assemble the exact cut  Σ_{k∈S} s_k − δ Σ_l w_l Σ_j ⌊a/δ⌋ x_j  >=  − δ Σ_l w_l ⌊β_l⌋,
    // with w_l = μ_{[l+1]} − μ_{[l]} (μ_{[r+1]} = 1).
    let mut sset: std::collections::BTreeSet<usize> = std::collections::BTreeSet::new();
    let mut xc: std::collections::BTreeMap<usize, BigRational> = std::collections::BTreeMap::new();
    let mut rhs = BigRational::zero();
    for (l, &ci) in chain.iter().enumerate() {
        for &k in cs[ci].cont_cols {
            sset.insert(k);
        }
        let mu_next = if l + 1 < chain.len() {
            cs[chain[l + 1]].mu.clone()
        } else {
            BigRational::one() // sentinel μ_{p_{r+1}} := 1
        };
        let w = &mu_next - &cs[ci].mu; // >= 0 by the increasing-μ order (last row: 1 − μ)
        if w.is_zero() {
            continue;
        }
        let wd = delta * &w; // δ · w_l
        for (j, fa) in &cs[ci].floors {
            *xc.entry(*j).or_insert_with(BigRational::zero) -= &wd * fa;
        }
        rhs -= &wd * &cs[ci].floor_beta;
    }
    if sset.is_empty() {
        return None;
    }

    // Down to f64, paying the rounding damage into the right-hand side so the stored cut is IMPLIED
    // by the exact one. The `s_k` coefficients are exactly `1.0` (representable), so only the
    // structural terms can damage.
    let mut out: Vec<(Col, f64)> = Vec::with_capacity(sset.len() + xc.len());
    for &k in &sset {
        out.push((Col(k as u32), 1.0));
    }
    let mut damage = BigRational::zero();
    for (j, c) in &xc {
        if c.is_zero() {
            continue;
        }
        let col = Col(*j as u32);
        // A `>=` store, so an unbounded-but-signed column rounds outward for free; see
        // `coef_to_f64`.
        let (cf, cost) = coef_to_f64(model, col, c, CutSide::Ge)?;
        damage += cost;
        if cf != 0.0 {
            out.push((col, cf));
        }
    }
    // A `>=` cut: relax the right-hand side DOWNWARD by the damage, then nudge it down once more so
    // the f64 conversion cannot tighten it (same convention as the GMI `>=` store).
    let relaxed = &rhs - &damage;
    let mut lb = to_f64(&relaxed);
    if !lb.is_finite() {
        return None;
    }
    lb -= lb.abs().mul_add(f64::EPSILON, f64::MIN_POSITIVE);

    // Refuse absurd numbers exactly as `mir_round` does — a row the LP cannot be conditioned around
    // is a wrecked basis, not a cut.
    let hi = out.iter().map(|&(_, a)| a.abs()).fold(0.0f64, f64::max);
    let lo = out
        .iter()
        .map(|&(_, a)| a.abs())
        .filter(|&a| a > 0.0)
        .fold(f64::INFINITY, f64::min);
    if hi > MAX_CUT_COEFF || lb.abs() > MAX_CUT_COEFF || hi / lo > MAX_CUT_DYNAMISM {
        return None;
    }

    let cut = Cut {
        coeffs: out,
        lb,
        ub: f64::INFINITY,
    };
    clears_min_violation(&cut, x).then_some(cut)
}

/// A REAL CUT LOOP WAS RUN, AND IT SETTLES THE QUESTION. Two facts, both measured on rout.
///
/// The suspicion was that this engine's two-round, four-cut budget is simply too small: on a
/// DEGENERATE relaxation the bound cannot move until the whole optimal FACE is cut off, which takes
/// many rounds, each separating from the next vertex the LP retreats to. So the loop was run
/// properly -- the "must earn its row" gate lifted (it is precisely what stops cuts accumulating
/// across rounds), twenty cuts a round, thirty rounds, most of the clock.
///
/// 1. THE BOUND MOVES, AND BY NOTHING. rout: 981.864286 -> 981.890126 after a round of twenty GMI
///    cuts. That is 0.026 against a gap of 95.7 -- three hundredths of one percent. Thirty such
///    rounds would not cover one percent of it. GMI cannot close this instance at ANY budget, and
///    that is a fact about the FAMILY, not about the budget it is given.
///
/// 2. AND THE LOOP CANNOT RUN ANYWAY, because the cuts make the LP too EXPENSIVE to keep solving.
///    It dies in round two. Not because the relaxation becomes unsolvable -- neither the iteration
///    cap nor the drift loop fires -- but because it becomes SLOW: forty GMI cuts at ~350 non-zeros
///    apiece add 14,000 non-zeros to a matrix that had about 2,000. The LP is eight times denser,
///    the solve runs past the budget, and every cut is thrown away. Dense cuts are the tax a cut
///    loop pays, and this engine cannot afford it.
///
/// So the order of the remaining work is settled, and it is NOT another cut family:
///   (a) the LP has to stay cheap as rows are added -- a sparse factorisation, and cuts sparsified
///       on the way in (dropping the near-noise coefficients and paying for them in the right-hand
///       side, which `Cut::clean` does but which was reverted as neutral WITHOUT a cut loop to make
///       it matter);
///   (b) then a cut POOL with bound-driven selection, because violation and efficacy both fail to
///       predict the bound (see below);
///   (c) then, and only then, stronger families.
/// Doing (c) first -- which was tried here twice -- cannot pay.
///
/// ROW AGGREGATION WAS BUILT AND IT DOES NOT HELP. Recorded so it is not built twice.
///
/// Aggregation is supposed to be the half that gives MIR its reach: a MIR cut is weakened by every
/// continuous column sitting strictly BETWEEN its bounds (the relaxation pays for the rounding with
/// it), so you aggregate a second `<=` row with a positive multiplier to CANCEL that column and
/// remove the escape. A non-negative combination of `<=` rows is a `<=` row, so validity is free.
/// It was implemented that way -- up to four aggregation steps, all in exact rationals, and the
/// brute-force validity guard passes on it.
///
/// It buys NOTHING, and it costs:
///   * rout's root bound is 981.864286 with it and 981.864286 without -- and 981.864286 with GMI,
///     with single-row MIR, with 4 cuts and with 150. NOTHING this engine can separate moves it.
///   * qnet1 goes BACKWARDS: single-row MIR lifts it to 14499.61, and with aggregation it falls back
///     to 14274.10, because the aggregated cuts win the selection and then say less.
///
/// That last point is the real lesson, and it is about SELECTION, not about MIR. Ranking cuts by
/// their VIOLATION prefers the ones that are merely big -- scale a cut's coefficients by ten and its
/// violation multiplies by ten while the inequality says the same thing -- and aggregation makes
/// cuts big. Ranking by EFFICACY instead (violation over the coefficient norm, the actual Euclidean
/// depth of the cut) was also tried, and it does not correlate with the bound either.
///
/// The unsolved problem here is not "which family": it is WHICH CUTS TO KEEP. The only measure that
/// is ground truth is to add a cut, re-solve, and look at the bound -- and that is what a real cut
/// pool with a proper selection loop does. That, not another family, is the next piece of work.
///
/// A variable of the substituted row: either a model column, or the SLACK of a variable upper
/// bound (`s_j = u_j·y_j − x_j`, which is what puts the binary into the row).
#[derive(Clone)]
enum Var {
    Col(usize),
    VubSlack { x: usize, y: usize, u: BigRational },
}

/// One variable of a row, rewritten as a non-negative displacement from its nearer bound.
#[derive(Clone)]
struct Sub {
    var: Var,
    /// Coefficient of the displacement `t >= 0`.
    a: BigRational,
    /// `t = v − lo` (false) or `t = up − v` (true).
    complemented: bool,
    bound: BigRational,
    integral: bool,
}

/// WHICH BOUND EACH COLUMN IS SUBSTITUTED AT — the half of c-MIR ay was not searching.
///
/// c-MIR has two free choices: the divisor `delta`, and the COMPLEMENTATION — for each column,
/// whether it is shifted to its lower bound (`t = x − l`) or its upper one (`t = u − x`). Both
/// are exact rewritings, so both are valid; they produce DIFFERENT cuts. `best_over_deltas`
/// searches the first. Until now the second was not a search at all but a fixed rule
/// ([`BoundPolicy::Near`]).
///
/// # The row that rule cannot cut
///
/// qnet1's capacity rows are `Σ_j w_j·y_j − 56·b_k − 1344·g_k <= 0` — `y` binary, `b_k ∈ [0,11]`
/// and `g_k ∈ [0,4]` general integers, every `w_j` a multiple of 56, RIGHT-HAND SIDE ZERO. MIR
/// only bites where `b/δ` lands FRACTIONAL, and a zero right-hand side is fractional for no `δ`
/// whatsoever: the whole family says nothing about the 124 rows that carry qnet1's objective.
/// The nearest-bound rule cannot fix that, because `b_k` and `g_k` sit near their LOWER bounds at
/// the root vertex and so are substituted at zero, which moves nothing into the right-hand side.
///
/// Complementing them at their upper bounds instead — `b' = 11 − b_k >= 0`, `g' = 4 − g_k >= 0` —
/// gives `Σ_j w_j·y_j + 56·b' + 1344·g' <= 5992`, and now `δ = 1344` lands `b/δ = 4.458…`. The MIR
/// cut of that row is `Σ_j c_j·y_j <= g_k` with `c_j = ⌊w_j/1344⌋ + (frac − 11/24)⁺·24/13` —
/// "switching on the big arcs forces a large capacity module" — which is precisely the statement
/// the LP relaxation is missing and which no `δ` on the uncomplemented row can express.
#[derive(Clone, Copy, PartialEq, Eq)]
enum BoundPolicy {
    /// Each column to the bound it is NEAREST at the separation point. The classical H1
    /// heuristic, and the historical behaviour: it keeps the displacements `t_i` small, which is
    /// what makes the rounding's damage term small.
    Near,
    /// Each column to whichever bound makes its coefficient POSITIVE — the canonical
    /// mixed-integer-knapsack form `Σ |a_j|·t_j <= b`, `t >= 0`. A column with a negative
    /// coefficient is complemented at its upper bound (which moves `|a_j|·u_j` INTO the
    /// right-hand side); one with a positive coefficient stays at its lower bound. Where a
    /// column has no finite bound on the side the policy wants, it falls back to the only finite
    /// one, exactly as `Near` does.
    Knapsack,
}

/// One row, `Σ a_j x_j <= b`, put through bound substitution and the MIR rounding.
///
/// Both complementations are derived (see [`BoundPolicy`]) and the DEEPER cut is kept. The second
/// derivation is skipped whenever the two policies would substitute every column identically —
/// which is every row whose oriented coefficients are already all positive, so a pure covering or
/// packing model pays nothing for it.
fn mir_from_row(
    model: &Model,
    x: &[f64],
    terms: &[(usize, BigRational)],
    rhs: &BigRational,
    vubs: &std::collections::HashMap<usize, (BigRational, usize)>,
) -> Option<Cut> {
    crate::sepstat::bump(&crate::sepstat::MIR_ROWS);
    best_over_policies(model, x, terms, rhs, vubs, Rounding::Mir)
}

/// Derive the row under every admissible complementation and keep the deepest cut. Shared by
/// `mir_from_row` and `strongcg_from_row` — the complementation search is a property of the ROW
/// PREPARATION, so both roundings get it.
fn best_over_policies(
    model: &Model,
    x: &[f64],
    terms: &[(usize, BigRational)],
    rhs: &BigRational,
    vubs: &std::collections::HashMap<usize, (BigRational, usize)>,
    kind: Rounding,
) -> Option<Cut> {
    let (subs, b, differs) = mir_build_subs(model, x, terms, rhs, vubs, BoundPolicy::Near)?;
    let near = best_over_deltas(model, x, &subs, &b, kind);
    if !differs || !mir_knap_on() {
        return near;
    }
    let knap = mir_build_subs(model, x, terms, rhs, vubs, BoundPolicy::Knapsack)
        .and_then(|(s, b2, _)| best_over_deltas(model, x, &s, &b2, kind));
    if knap_dbg() {
        eprintln!(
            "--trace   knap: nnz={} near={:?} knap={:?}",
            terms.len(),
            near.as_ref().map(|c| efficacy(c, x)),
            knap.as_ref().map(|c| efficacy(c, x)),
        );
    }
    match (near, knap) {
        (Some(a), Some(c)) => {
            // Deeper wins; a tie keeps the HISTORICAL derivation, so the family says the same
            // thing twice and the knapsack form can only ever add depth.
            Some(if efficacy(&c, x) > efficacy(&a, x) {
                c
            } else {
                a
            })
        }
        (a, None) => a,
        (None, c) => c,
    }
}

/// The STRENGTHENED CHVÁTAL-GOMORY sibling of `mir_from_row`: identical row preparation (the same
/// bound substitution and VARIABLE-upper-bound substitution, so the same structural binary enters
/// the row), but rounded by `strongcg_round` instead of `mir_round`. See `strongcg_round` for the
/// strengthened coefficient function and why it is pure-integer.
fn strongcg_from_row(
    model: &Model,
    x: &[f64],
    terms: &[(usize, BigRational)],
    rhs: &BigRational,
    vubs: &std::collections::HashMap<usize, (BigRational, usize)>,
) -> Option<Cut> {
    crate::sepstat::bump(&crate::sepstat::SCG_ROWS);
    best_over_policies(model, x, terms, rhs, vubs, Rounding::StrongCg)
}

/// Apply exact variable-upper-bound rewrites first and accumulate the remaining columns in stable
/// order. The `BTreeMap` ordering is load-bearing because the bounded delta search takes the first
/// integral coefficients it sees.
fn mir_collect_vub_subs(
    model: &Model,
    x: &[f64],
    terms: &[(usize, BigRational)],
    vubs: &std::collections::HashMap<usize, (BigRational, usize)>,
) -> (Vec<Sub>, std::collections::BTreeMap<usize, BigRational>) {
    let mut subs: Vec<Sub> = Vec::with_capacity(terms.len());
    let mut ycoef = std::collections::BTreeMap::new();
    let mut plain = Vec::new();
    for (j, a) in terms {
        if let Some((u, ybin)) = vubs.get(j) {
            let yv = x.get(*ybin).copied().unwrap_or(0.0);
            let uv = to_f64(u);
            let xs = x.get(*j).copied().unwrap_or(0.0);
            let (lo, _) = model.col_bounds(Col(*j as u32));
            if yv > 1e-7 && (uv * yv - xs).abs() + 1e-9 < (xs - lo).abs() {
                // a·x = a·u·y − a·s
                *ycoef.entry(*ybin).or_insert_with(BigRational::zero) += a * u;
                subs.push(Sub {
                    var: Var::VubSlack {
                        x: *j,
                        y: *ybin,
                        u: u.clone(),
                    },
                    a: -a.clone(),
                    complemented: false,
                    bound: BigRational::zero(), // s >= 0
                    integral: false,
                });
                continue;
            }
        }
        plain.push((*j, a.clone()));
    }
    for (j, a) in plain {
        *ycoef.entry(j).or_insert_with(BigRational::zero) += a;
    }
    (subs, ycoef)
}

/// Substitute the stably accumulated columns at the requested finite bound.
///
/// The displacement is integral only when the column AND chosen bound are integral. This is
/// load-bearing: treating `x - 1.5` as integral once emitted a cut that deleted feasible point
/// `(2,0,0,4)`. Presolve normally rounds such bounds, but in-process callers need the same guard.
fn mir_substitute_columns(
    model: &Model,
    x: &[f64],
    ycoef: std::collections::BTreeMap<usize, BigRational>,
    policy: BoundPolicy,
    subs: &mut Vec<Sub>,
    b: &mut BigRational,
) -> Option<bool> {
    let mut differs = false;
    for (j, a) in ycoef {
        if a.is_zero() {
            continue;
        }
        let col = Col(j as u32);
        let (lo, up) = model.col_bounds(col);
        let xs = x.get(j).copied()?;
        let d_lo = if lo.is_finite() {
            xs - lo
        } else {
            f64::INFINITY
        };
        let d_up = if up.is_finite() {
            up - xs
        } else {
            f64::INFINITY
        };
        let near = d_up < d_lo;
        // KNAPSACK FORM: complement exactly the negative coefficients, so the substituted row
        // reads `Σ |a_j|·t_j <= b` with every `t_j >= 0` — and `|a_j|·u_j` of every complemented
        // column has moved INTO `b`, which is what gives the rounding a fractional right-hand
        // side to bite on. Where the side the policy wants has no finite bound, fall through to
        // the other one; `Near` does the same, and both policies therefore succeed and fail on
        // exactly the same rows.
        let knap = if a.is_negative() {
            up.is_finite()
        } else {
            !lo.is_finite()
        };
        // Reported for BOTH policies, so a `Near` caller learns whether the knapsack derivation
        // would say anything new before paying for it.
        differs |= knap != near;
        let compl = match policy {
            BoundPolicy::Near => near,
            BoundPolicy::Knapsack => knap,
        };
        let bnd_f = if compl { up } else { lo };
        if !bnd_f.is_finite() {
            return None; // cannot be shifted to zero: this row yields no MIR cut
        }
        let bnd = exact(bnd_f)?;
        *b -= &a * &bnd;
        let bound_is_integral = bnd.is_integer();
        subs.push(Sub {
            var: Var::Col(j),
            a: if compl { -a } else { a },
            complemented: compl,
            bound: bnd,
            integral: model.col_kind(col).is_integral() && bound_is_integral,
        });
    }
    Some(differs)
}

/// Put a row `Σ a_j x_j <= b` through bound substitution, returning the non-negative displacements
/// `subs`, the shifted right-hand side `b`, and whether the chosen [`BoundPolicy`] substituted any
/// column DIFFERENTLY from `BoundPolicy::Near` (so the caller can skip a second, identical
/// derivation). SHARED by `mir_from_row` and `strongcg_from_row`: the substitution — including the
/// VUB substitution that drags the switch binary in — is the same for both families; only the
/// rounding of the resulting row differs.
fn mir_build_subs(
    model: &Model,
    x: &[f64],
    terms: &[(usize, BigRational)],
    rhs: &BigRational,
    vubs: &std::collections::HashMap<usize, (BigRational, usize)>,
    policy: BoundPolicy,
) -> Option<(Vec<Sub>, BigRational, bool)> {
    crate::sepstat::bump(&crate::sepstat::SUBS_BUILT);
    let (mut subs, ycoef) = mir_collect_vub_subs(model, x, terms, vubs);
    let mut b = rhs.clone();
    let differs = mir_substitute_columns(model, x, ycoef, policy, &mut subs, &mut b)?;
    if subs.is_empty() {
        crate::sepstat::bump(&crate::sepstat::SUBS_NONE);
        return None;
    }
    Some((subs, b, differs))
}

/// Which rounding a `best_over_deltas` sweep is running — the screen has to model the SAME
/// coefficient function the kernel will use, so the two must not drift apart.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Rounding {
    Mir,
    StrongCg,
}

/// What the `f64` screen can say about one `delta`.
enum Verdict {
    /// The kernel provably returns `None` for this delta (its own fractionality guard fails,
    /// evaluated EXACTLY -- this is not an approximation).
    NoCut,
    /// A rigorous upper bound on the violation at `x` of the cut the kernel would return.
    Ub(f64),
    /// The floating-point screen is not trustworthy here; the kernel must run.
    Unknown,
}

/// PRECOMPUTED ROW GEOMETRY FOR THE VIOLATION SCREEN.
///
/// # Why a screen exists at all
///
/// Measured on mas74's root round (`--sepstat AY_ROOT_CLOSURE=1`): 26 rows, 872 exact
/// rounding passes, **zero** cuts. 410 of the MIR passes ran the full `BigRational` derivation and
/// produced a cut that was not violated at `x`; 418 of the strong-CG passes ran the full derivation
/// and were then thrown away by the coefficient-sanity filter at the very end. The delta sweep
/// multiplies this by ~17. None of that work can be removed by choosing cuts better -- it is spent
/// before there is a cut to choose.
///
/// # The identity the screen rests on
///
/// Both kernels map their displacement-space inequality `Σ c_i t_i <= ⌊b/δ⌋` back onto the model's
/// columns by adding `c·bound` into the right-hand side for every substituted column (and, for a
/// VUB slack `s = u·y − x`, by splitting `c` across the two columns). Re-expanding that mapping at
/// the separation point gives, term by term,
///
/// ```text
///   Σ_j C_j x_j − RHS   =   Σ_i c_i · t_i(x)   −   ⌊b/δ⌋
/// ```
///
/// exactly -- it is the same inequality written in two coordinate systems. So the violation of the
/// finished cut can be evaluated from the DISPLACEMENTS, which are known before any coefficient is
/// derived.
///
/// # Why bounding it in `f64` is sound
///
/// The stored `f64` cut is IMPLIED by the exact one: each kernel adds `damage = Σ|cf_j − C_j| ·
/// max(|l_j|,|u_j|)` into the right-hand side and rounds that outward, and `|x_j| <=
/// max(|l_j|,|u_j|)` holds for any point inside the box. Hence
/// `violation(stored) <= violation(exact)` -- proved in the two `damage` blocks below. So an upper
/// bound on the exact violation is an upper bound on the one `best_over_deltas` will test.
///
/// The bound itself is not a heuristic tolerance:
///
/// * `⌊b/δ⌋` and the fractionality `f` are computed in EXACT rationals (an `O(1)` bignum step, not
///   the `O(nnz)` pass the screen is removing), so the term that carries integer-sized error
///   carries none.
/// * both coefficient functions are NON-DECREASING in `a` (MIR's is continuous; strong CG's jumps
///   UPWARD by `1/(k+1)` at each integer), so evaluating at `a ± da` in the direction that makes
///   `c_i·t_i` largest is a true upper bound on that term rather than a linearisation.
/// * the remaining `f64` slop -- the `to_f64` of `a`, the displacement subtraction, the summation
///   -- is bounded explicitly in `eps` below.
///
/// When any of that cannot be established (a right-hand side too large for `f64` to resolve its
/// fractional part, a non-finite value), the screen answers `Unknown` and the kernel runs.
struct ScreenRow {
    /// `t_i(x)`, the displacement of sub `i` at the separation point.
    tv: Vec<f64>,
    /// The sub's coefficient on the UNDIVIDED row, in `f64`.
    av: Vec<f64>,
    /// A magnitude scale for sub `i` that dominates `|t_i|` and every quantity its `f64`
    /// evaluation rounded -- used only to size the error term.
    sc: Vec<f64>,
    /// Strong CG projects the continuous displacements into the right-hand side before it rounds.
    /// That penalty does not depend on `delta`, so it is computed ONCE here, exactly.
    b_eff: BigRational,
    /// How far outside its own column box the separation point sits, at worst. Zero for every LP
    /// vertex; nonzero only for a synthetic or drifted point, and then it is priced into `eps`.
    box_excess: f64,
}

impl ScreenRow {
    fn build(
        model: &Model,
        x: &[f64],
        subs: &[Sub],
        b: &BigRational,
        kind: Rounding,
    ) -> Option<Self> {
        if screen_off() {
            return None;
        }
        let mut tv = Vec::with_capacity(subs.len());
        let mut av = Vec::with_capacity(subs.len());
        let mut sc = Vec::with_capacity(subs.len());
        let mut b_eff = b.clone();
        let mut box_excess = 0.0f64;
        let mut out_of_box = |m: &Model, j: usize| {
            let (lo, up) = m.col_bounds(Col(j as u32));
            let xv = x.get(j).copied().unwrap_or(0.0);
            let d = (lo - xv).max(xv - up).max(0.0);
            if d.is_finite() {
                box_excess = box_excess.max(d);
            }
        };
        for s in subs {
            let (t, scale) = match &s.var {
                Var::Col(j) => {
                    let xv = *x.get(*j)?;
                    let bnd = to_f64(&s.bound);
                    let t = if s.complemented { bnd - xv } else { xv - bnd };
                    out_of_box(model, *j);
                    (t, xv.abs() + bnd.abs())
                }
                Var::VubSlack { x: xj, y, u } => {
                    let xv = *x.get(*xj)?;
                    let yv = *x.get(*y)?;
                    let uf = to_f64(u);
                    out_of_box(model, *xj);
                    out_of_box(model, *y);
                    (uf * yv - xv, (uf * yv).abs() + xv.abs())
                }
            };
            let a = to_f64(&s.a);
            if !t.is_finite() || !a.is_finite() || !scale.is_finite() {
                return None;
            }
            // Strong CG's continuous projection, in exact arithmetic and delta-independent --
            // `strongcg_round` derives the identical `b_pen` for every delta it is handed.
            if kind == Rounding::StrongCg && !s.integral && s.a < BigRational::zero() {
                let r = strongcg_range(model, &s.var)?;
                b_eff += (-&s.a) * &r;
            }
            tv.push(t);
            av.push(a);
            sc.push(scale);
        }
        if !box_excess.is_finite() {
            return None;
        }
        Some(Self {
            tv,
            av,
            sc,
            b_eff,
            box_excess,
        })
    }

    fn screen_delta(&self, subs: &[Sub], delta: &BigRational, kind: Rounding) -> Verdict {
        // EXACT: the right-hand side's integer part and its fractionality. These are the two
        // quantities a floating-point slip would corrupt by a whole unit, and they cost `O(1)`.
        let bd = &self.b_eff / delta;
        let fl_r = bd.floor();
        let fb_r = &bd - &fl_r;
        if fb_r.is_zero() {
            return Verdict::NoCut;
        }
        let fmin = BigRational::new(1.into(), 100.into());
        if fb_r < fmin || fb_r > BigRational::one() - &fmin {
            return Verdict::NoCut; // both kernels refuse this row at exactly this test
        }
        let fl = to_f64(&fl_r);
        let fb = to_f64(&fb_r);
        let delta_f = to_f64(delta);
        if !fl.is_finite() || !fb.is_finite() || !delta_f.is_finite() || delta_f == 0.0 {
            return Verdict::Unknown;
        }
        // `⌊b/δ⌋` must be exactly representable, or the violation's integer part is already noise.
        if fl.abs() >= 9.0e15 {
            return Verdict::Unknown;
        }
        let inv = 1.0 / (1.0 - fb);
        // Strong CG's sub-interval count, `k = ⌈1/f⌉ − 1`, taken from the EXACT `f`.
        let k = match kind {
            Rounding::Mir => 0.0,
            Rounding::StrongCg => {
                let k_rat = (BigRational::one() / &fb_r).ceil() - BigRational::one();
                if k_rat < BigRational::one() {
                    return Verdict::NoCut;
                }
                let k = to_f64(&k_rat);
                if !k.is_finite() || !(1.0..=1.0e6).contains(&k) {
                    return Verdict::Unknown;
                }
                k
            }
        };

        let mut sum = 0.0f64;
        let mut mag_c = 0.0f64;
        let mut mag_a = 0.0f64;
        let mut sum_c = 0.0f64;
        let mut nz = 0usize;
        for (i, s) in subs.iter().enumerate() {
            let t = self.tv[i];
            let a = self.av[i] / delta_f;
            if !a.is_finite() {
                return Verdict::Unknown;
            }
            // Both coefficient rules are NON-DECREASING in `a`, so pushing `a` in the direction
            // that grows `c·t` bounds the term from above whatever the `to_f64` of `a` did.
            // `a` came through two `to_f64`s and a division, so ~1.5 ulp; 64 is a wide margin
            // that costs nothing (it moves the final bound by ~1e-9, and the floor it is tested
            // against, `MIN_VIOLATION`, is 1e-4).
            let da = a.abs() * 64.0 * f64::EPSILON + f64::MIN_POSITIVE;
            let want_max = t >= 0.0;
            let ah = if want_max { a + da } else { a - da };
            let c = screen_coeff(kind, ah, fb, inv, k, s.integral, want_max);
            if !c.is_finite() {
                return Verdict::Unknown;
            }
            sum += c * t;
            mag_c += c.abs() * self.sc[i];
            mag_a += a.abs() * self.sc[i];
            sum_c += c.abs();
            nz += 1;
        }
        if !sum.is_finite() {
            return Verdict::Unknown;
        }
        // The residual `f64` slop, term by term: the rounded `a` entering the coefficient formula
        // (sensitivity `1/(1−f)`); the displacement subtractions and the running sum over `nz`
        // terms; and `f`'s own last bit, which reaches the coefficient through `1/(1−f)` twice.
        // On mas74 this lands around 1e-9 -- five orders below the `MIN_VIOLATION` floor it gates,
        // which is why the screen loses no power to being conservative.
        //
        // The last term is the only place the point's position matters. The kernels pay their
        // `f64` coefficient rounding into the right-hand side as `Σ|cf_j − C_j|·max(|l_j|,|u_j|)`,
        // which dominates the same rounding's effect on the left-hand side ONLY for a point inside
        // the box. `box_excess` measures how far outside the point actually is and prices the
        // shortfall, so the bound stands for any point rather than resting on a caller's promise.
        let eps = f64::EPSILON
            * (64.0 * inv * mag_a
                + (nz as f64 + 64.0) * (mag_c + fl.abs())
                + 8.0 * nz as f64 * inv * inv
                + 4.0 * self.box_excess * sum_c)
            + 1.0e-12;
        Verdict::Ub(sum - fl + eps)
    }
}

impl ScreenRow {
    /// Diagnostic for `AY_MILP_SEP_SCREEN_EXPLAIN`: dump the screen's view of a row beside the cut
    /// the kernel actually built, so a disagreement can be attributed to a term rather than guessed.
    #[cold]
    fn explain(&self, subs: &[Sub], delta: &BigRational, kind: Rounding, cut: &Cut, x: &[f64]) {
        let bd = &self.b_eff / delta;
        let fl_r = bd.floor();
        let fb_r = &bd - &fl_r;
        let fl = to_f64(&fl_r);
        let fb = to_f64(&fb_r);
        let inv = 1.0 / (1.0 - fb);
        let df = to_f64(delta);
        let k = match kind {
            Rounding::Mir => 0.0,
            Rounding::StrongCg => {
                to_f64(&((BigRational::one() / &fb_r).ceil() - BigRational::one()))
            }
        };
        eprintln!(
            "  EXPLAIN delta={df} fl={fl} fb={fb} k={k} nsubs={}",
            subs.len()
        );
        let mut sum = 0.0;
        for (i, s) in subs.iter().enumerate() {
            let a = self.av[i] / df;
            let t = self.tv[i];
            let c = screen_coeff(kind, a, fb, inv, k, s.integral, t >= 0.0);
            sum += c * t;
            let vs = match &s.var {
                Var::Col(j) => format!("col{j}"),
                Var::VubSlack { x, y, .. } => format!("vub(x{x},y{y})"),
            };
            eprintln!("    {vs} int={} a={a} t={t} c={c}", s.integral);
        }
        eprintln!("  screen sum={sum} -> viol={}", sum - fl);
        eprintln!("  cut ub={} coeffs={:?}", cut.ub, cut.coeffs);
        let act: f64 = cut
            .coeffs
            .iter()
            .map(|&(c, a)| a * x.get(c.index()).copied().unwrap_or(0.0))
            .sum();
        eprintln!("  cut act={act} viol={}", act - cut.ub);
    }
}

/// The rounded coefficient both kernels put on displacement `i`, evaluated in `f64`. Mirrors
/// `mir_round` / `strongcg_round` term for term; the exact versions remain the only ones that ever
/// build a cut.
///
/// `want_max` says which way to resolve strong CG's `⌈·⌉`, which is a STEP: the caller is bounding
/// `c·t` from above, so it wants the largest admissible `c` when `t >= 0` and the smallest when
/// `t < 0`. Rounding that step the same way regardless was a real defect -- it made the "upper
/// bound" a lower bound on every term with a negative displacement, and a negative displacement is
/// exactly what a separation point sitting outside a column's box produces.
#[inline]
fn screen_coeff(
    kind: Rounding,
    a: f64,
    fb: f64,
    inv: f64,
    k: f64,
    integral: bool,
    want_max: bool,
) -> f64 {
    if !integral {
        return match kind {
            // Strong CG projected every continuous displacement into `b_eff` already.
            Rounding::StrongCg => 0.0,
            Rounding::Mir => {
                if a < 0.0 {
                    a * inv
                } else {
                    0.0
                }
            }
        };
    }
    let fl = a.floor();
    let fj = a - fl;
    match kind {
        Rounding::Mir => {
            if fj > fb {
                fl + (fj - fb) * inv
            } else {
                fl
            }
        }
        Rounding::StrongCg => {
            if fj <= fb {
                fl
            } else {
                // `p = ⌈k·(f(a) − f)/(1 − f)⌉` clamped to `{1,…,k}`. `ceil` is a step: when its
                // argument lands within a hair of an integer `m`, the exact `p` is `m` or `m+1`
                // and the `f64` evaluation cannot tell which. Take whichever of the two the
                // caller's direction needs.
                let ku = k * (fj - fb) * inv;
                let fr = ku - ku.floor();
                let p = if !(1.0e-9..=1.0 - 1.0e-9).contains(&fr) {
                    let m = ku.round();
                    if want_max {
                        m + 1.0
                    } else {
                        m
                    }
                } else {
                    ku.ceil()
                };
                fl + p.clamp(1.0, k) / (k + 1.0)
            }
        }
    }
}

thread_local! {
    /// In-process override of the screen gate. The env kill switch is read once and cached, which
    /// is right for a solve but makes it impossible to run BOTH paths in one process — and the
    /// property that matters about this screen ("the two paths return the same cuts") can only be
    /// tested by running both. See `screen_scope`.
    static SCREEN_FORCE: std::cell::Cell<Option<bool>> = const { std::cell::Cell::new(None) };
}

/// Run `f` with the violation screen forced on or off.
#[cfg(test)]
fn screen_scope<T>(on: bool, f: impl FnOnce() -> T) -> T {
    struct Restore(Option<bool>);
    impl Drop for Restore {
        fn drop(&mut self) {
            SCREEN_FORCE.with(|c| c.set(self.0));
        }
    }
    let _r = Restore(SCREEN_FORCE.with(std::cell::Cell::get));
    SCREEN_FORCE.with(|c| c.set(Some(on)));
    f()
}

/// Kill switch for the violation screen — for A/B measurement and as an escape hatch.
fn screen_off() -> bool {
    if let Some(on) = SCREEN_FORCE.with(std::cell::Cell::get) {
        return !on;
    }
    // B11: caller-layer switch (`with_sep_screen(false)`); the never-set
    // AY_MILP_NO_SEP_SCREEN env read is gone.
    crate::tune::on(crate::tune::Knob::NoSepScreen)
}

/// Audit mode: derive every delta exactly and check the screen's claim against it.
fn screen_audit() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| crate::debug_flags::milp_debug_flags().sep_screen_audit)
}

type MirRoundFn = fn(&Model, &[Sub], &BigRational, &BigRational) -> Option<Cut>;

/// Deterministic c-MIR scaling list: one, leading integral magnitudes, then their doublings.
fn mir_delta_candidates(subs: &[Sub]) -> Vec<BigRational> {
    let cap = DELTA_CAP.with(std::cell::Cell::get);
    let mut deltas = vec![BigRational::one()];
    for sub in subs.iter().filter(|sub| sub.integral) {
        let magnitude = sub.a.abs();
        if !magnitude.is_zero() && !deltas.contains(&magnitude) && deltas.len() < cap {
            deltas.push(magnitude);
        }
    }
    let two = BigRational::from_integer(2.into());
    for index in 0..deltas.len().min(cap / 2) {
        let doubled = &deltas[index] * &two;
        if !deltas.contains(&doubled) {
            deltas.push(doubled);
        }
    }
    crate::sepstat::bump(&crate::sepstat::DELTA_LISTS);
    crate::sepstat::add(&crate::sepstat::DELTA_ENTRIES, deltas.len() as u64);
    deltas
}

/// Price every delta through the sound floating screen, including the optional exact audit.
/// `None` means Rule A proved the whole row unable to clear the admission floor.
fn screen_mir_deltas(
    model: &Model,
    x: &[f64],
    subs: &[Sub],
    b: &BigRational,
    kind: Rounding,
    round_fn: MirRoundFn,
    deltas: &[BigRational],
) -> Option<Vec<Verdict>> {
    let screen = ScreenRow::build(model, x, subs, b, kind);
    if screen.is_none() && !screen_off() {
        crate::sepstat::bump(&crate::sepstat::SCREEN_BUILD_FAIL);
    }
    let Some(screen) = screen.as_ref() else {
        return Some(Vec::new());
    };
    let mut bounds = Vec::with_capacity(deltas.len());
    let mut row_max = f64::NEG_INFINITY;
    let mut all_known = true;
    for delta in deltas {
        let verdict = if delta.is_zero() {
            Verdict::NoCut
        } else {
            screen.screen_delta(subs, delta, kind)
        };
        match verdict {
            Verdict::Ub(upper) => row_max = row_max.max(upper),
            Verdict::NoCut => {}
            Verdict::Unknown => {
                all_known = false;
                crate::sepstat::bump(&crate::sepstat::SCREEN_UNKNOWN);
            }
        }
        bounds.push(verdict);
    }
    crate::sepstat::add(&crate::sepstat::SCREEN_TRIED, deltas.len() as u64);
    if screen_audit() {
        for (index, delta) in deltas.iter().enumerate().filter(|(_, d)| !d.is_zero()) {
            let got = round_fn(model, subs, b, delta);
            let violation = got
                .as_ref()
                .map_or(f64::NEG_INFINITY, |cut| violation(cut, x));
            match bounds[index] {
                Verdict::NoCut if got.is_some() => {
                    crate::sepstat::bump(&crate::sepstat::AUDIT_FAIL);
                    eprintln!(
                        "AY_SEPSTAT AUDIT-FAIL NoCut but kernel derived a cut (v={violation})"
                    );
                }
                Verdict::Ub(upper) if violation > upper => {
                    crate::sepstat::bump(&crate::sepstat::AUDIT_FAIL);
                    eprintln!(
                        "AY_SEPSTAT AUDIT-FAIL violation {violation} exceeds screen bound {upper}"
                    );
                    if false {
                        if let Some(cut) = got.as_ref() {
                            screen.explain(subs, delta, kind, cut, x);
                        }
                    }
                }
                _ => crate::sepstat::bump(&crate::sepstat::AUDIT_OK),
            }
        }
    }
    if all_known && row_max <= min_violation() {
        crate::sepstat::add(&crate::sepstat::SCREEN_SKIP, deltas.len() as u64);
        crate::sepstat::bump(&crate::sepstat::SCREEN_ROW_KILL);
        None
    } else {
        Some(bounds)
    }
}

/// Run the exact kernels not eliminated by Rule B and retain the highest-efficacy candidate.
fn derive_best_delta(
    model: &Model,
    x: &[f64],
    subs: &[Sub],
    b: &BigRational,
    kind: Rounding,
    round_fn: MirRoundFn,
    deltas: &[BigRational],
    bounds: &[Verdict],
) -> Option<Cut> {
    let mut best: Option<(f64, Cut)> = None;
    for (index, delta) in deltas.iter().enumerate() {
        if delta.is_zero() {
            continue;
        }
        if bounds.get(index).is_some_and(|verdict| match verdict {
            Verdict::Ub(upper) => *upper <= 0.0,
            Verdict::NoCut => true,
            Verdict::Unknown => false,
        }) {
            crate::sepstat::bump(&crate::sepstat::SCREEN_SKIP);
            continue;
        }
        let Some(cut) = round_fn(model, subs, b, delta) else {
            continue;
        };
        if crate::attrib::on() {
            let counter = match kind {
                Rounding::Mir => &crate::attrib::MIR_ROUND_SOME,
                Rounding::StrongCg => &crate::attrib::STRONGCG_ROUND_SOME,
            };
            counter.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
        let value = efficacy(&cut, x);
        crate::sepstat::bump(if value > 0.0 {
            &crate::sepstat::CAND_POS
        } else {
            &crate::sepstat::CAND_NONPOS
        });
        if value > 0.0 && best.as_ref().is_none_or(|(old, _)| value > *old) {
            best = Some((value, cut));
        }
    }
    let (_, cut) = best?;
    let out = clears_min_violation(&cut, x).then_some(cut);
    if out.is_some() {
        crate::sepstat::bump(&crate::sepstat::ROW_RET);
    }
    out
}

/// Search the c-MIR scalings and keep the deepest cut `round_fn` yields. SHARED by `mir_from_row`
/// and `strongcg_from_row`: the `delta` family and the efficacy-ranked selection are identical; the
/// only thing that varies is whether each `delta` is rounded by MIR or by strong CG.
///
/// A few scalings: dividing through by an integer coefficient's magnitude is what makes the
/// rounding bite on a row whose numbers are not near one.
/// THE SCALING IS THE CUT. c-MIR divides the row through by a `delta` before rounding, and WHICH
/// delta decides everything: the rounding only bites where the right-hand side lands fractional
/// and the coefficients straddle it. Three candidates is not a search. HiGHS lifts qnet1's root
/// bound from 14274.10 -- the same LP ay starts from -- to 16021.07 with 880 root cuts, closing
/// 99.5% of the gap before it branches at all; ay's whole remaining deficit is cut STRENGTH, and
/// the delta is the cheapest place to look for it.
fn best_over_deltas(
    model: &Model,
    x: &[f64],
    subs: &[Sub],
    b: &BigRational,
    kind: Rounding,
) -> Option<Cut> {
    let round_fn = match kind {
        Rounding::Mir => mir_round,
        Rounding::StrongCg => strongcg_round,
    };
    let deltas = mir_delta_candidates(subs);
    let bounds = screen_mir_deltas(model, x, subs, b, kind, round_fn, &deltas)?;
    derive_best_delta(model, x, subs, b, kind, round_fn, &deltas, &bounds)
}

/// How deeply the cut bites at `x` -- its Euclidean distance from the point, which is scale-free.
pub(crate) fn cut_depth(cut: &Cut, x: &[f64]) -> f64 {
    efficacy(cut, x)
}

/// How far `x` breaks the cut.
pub(crate) fn violation(cut: &Cut, x: &[f64]) -> f64 {
    let act: f64 = cut
        .coeffs
        .iter()
        .map(|&(c, a)| a * x.get(c.index()).copied().unwrap_or(0.0))
        .sum();
    // BOTH SIDES. This read `act - cut.ub`, which is right for a `<=` cut and silently catastrophic
    // for a `>=` one: its `ub` is `+inf`, so the violation came back `-inf` and the cut looked
    // satisfied. `clean` always did this correctly; `snap` reused this helper and threw away every
    // `>=` cut it was given -- on mas74 that was ALL of them, and the cut loop exited at round zero
    // with an empty pool.
    if cut.ub.is_finite() {
        act - cut.ub
    } else {
        cut.lb - act
    }
}

/// EFFICACY: the Euclidean depth of the cut, which is scale-free. Ranking by raw violation prefers
/// cuts that are merely BIG -- multiply a cut through by ten and its violation multiplies by ten
/// while the inequality says exactly the same thing.
fn efficacy(cut: &Cut, x: &[f64]) -> f64 {
    let norm = cut
        .coeffs
        .iter()
        .map(|&(_, a)| a * a)
        .sum::<f64>()
        .sqrt()
        .max(1e-12);
    violation(cut, x) / norm
}

/// W1 CUT SELECTION — efficacy ranking plus an orthogonality filter.
///
/// The measured diagnosis in the development design notes was that
/// ay separates the same cut FAMILIES as the commercial solvers and still reaches a weaker
/// root bound, because it *keeps* differently: everything above an absolute efficacy floor
/// went into the pool, in separation order, however redundant.
///
/// Two rows that are nearly parallel say nearly the same thing. The second one moves the
/// bound by almost nothing and yet is carried by every LP of the loop and of every node
/// under it — that is the "dense redundant cut" failure the plan attributes to the
/// asymmetric lift-and-project family. Selecting in efficacy order and rejecting a
/// candidate that is near-parallel to something already selected spends the round's budget
/// on rows that cut in *different directions*.
///
/// ```text
///   accept c  iff  |⟨c, s⟩| / (‖c‖·‖s‖)  <=  max_parallel   for every already-selected s
/// ```
///
/// SOUNDNESS. This function only ever DROPS cuts, and every cut it is given is already
/// valid for the integer hull. Dropping a valid cut changes which relaxation the search
/// carries — never which points are feasible — so no verdict and no objective can move.
/// That is why the plan rates W1 highest-leverage *and* lowest-risk.
///
/// `x` is the point the cuts were separated from, so `efficacy` is their depth against the
/// vertex they were built to cut off. Returns the kept cuts in rank order, and (as a
/// parallel vector) the caller's per-cut tag permuted the same way — the MIR-family
/// accounting in the root loop depends on tag and cut staying in step.
///
/// # W2: the fractionality-penalised rank (`frac_penalty`, DEFAULT OFF, measured LOSING)
///
/// The W2 campaign asked whether the rank should charge a cut for the fractionality it
/// INTRODUCES as well as credit it for the depth it buys —
/// the development design notes. The causal leg is real but small
/// (controlling for bound, fractional share is significant at p = 0.028 and sign-stable
/// across all 21 leave-one-instance-out fits, but adds only +0.10 to a within-instance
/// R² of 0.336). This parameter is the mechanism, kept because the negative result is only
/// re-checkable while its arm exists:
///
/// ```text
///   rank key  =  depth(c)  /  (1 + frac_penalty · added(c))
///   added(c)  =  |{ j ∈ supp(c) : j is an INTEGER column and x_j is currently INTEGRAL }|
/// ```
///
/// `added` is the only admission-time proxy for induced fractionality that is actually
/// available: a cut can only make an integer column newly fractional if it touches it, and a
/// column already fractional at `x` is already being paid for. It is sharper than the cut
/// DENSITY the campaign correlated (density counts continuous columns and already-fractional
/// ones too), and it is exact, deterministic and free — no LP re-solve.
///
/// `frac_penalty = 0` makes the key `depth / 1.0`, which is bit-identical to the depth key
/// (dividing an `f64` by exactly `1.0` is exact), so the default path is byte-for-byte the
/// pre-W2 ranking. That is the A/B control and `frac_penalty_zero_is_the_depth_rank` pins it.
///
/// MEASURED ON 32 INSTANCES, AND IT DOES NOT WIN. At a fixed `TOPK=4` budget the penalised
/// rank moves the tree on 8 instances — 3 better, 5 worse — for a geomean of 0.987x nodes
/// against its own depth-ranked control (`lambda = 4`: 0.962x, still 3/5). But the budget it
/// needs in order to bite is ITSELF a 1.287x loss against the shipped default, so the rule
/// nets out **1.270x WORSE than shipping nothing**: it gives back 1.3% of nodes inside a lane
/// that costs 28.7%. No verdict moved in either direction on any arm. It is structurally wrong on models
/// where fractionality is how the bound arrives — fiber goes 43,594 -> 83,161 nodes. Default
/// stays `0.0`; the arm stays so the negative result is re-checkable.
pub(crate) fn select_cuts<T: Copy>(
    cuts: Vec<Cut>,
    tags: Vec<T>,
    x: &[f64],
    max_keep: usize,
    max_parallel: f64,
    ncols: usize,
    frac_penalty: f64,
    newly_fractionable: &[bool],
) -> (Vec<Cut>, Vec<T>) {
    debug_assert_eq!(cuts.len(), tags.len());
    if cuts.is_empty() || (max_keep >= cuts.len() && max_parallel >= 1.0) {
        return (cuts, tags);
    }
    // Rank by depth (penalised, if W2 is on), deepest first. `sort_by` with a total-order
    // fallback keeps this deterministic on ties and on any NaN a degenerate row could
    // produce — the engine's determinism guarantee is not negotiable for a ranking
    // heuristic.
    let mut order: Vec<usize> = (0..cuts.len()).collect();
    let key: Vec<f64> = cuts
        .iter()
        .map(|c| {
            let d = efficacy(c, x);
            if frac_penalty <= 0.0 {
                return d;
            }
            // Count the integer columns this row touches that are INTEGRAL right now —
            // the ones it could newly fractionalise. `get` because a cut may name a
            // column the caller's mask does not cover (a slack introduced by the
            // aggregator); an unknown column is charged nothing rather than panicking
            // inside a ranking heuristic.
            let added = c
                .coeffs
                .iter()
                .filter(|&&(j, a)| {
                    a != 0.0 && newly_fractionable.get(j.index()).copied().unwrap_or(false)
                })
                .count();
            d / (1.0 + frac_penalty * added as f64)
        })
        .collect();
    let norm: Vec<f64> = cuts
        .iter()
        .map(|c| {
            c.coeffs
                .iter()
                .map(|&(_, a)| a * a)
                .sum::<f64>()
                .sqrt()
                .max(1e-12)
        })
        .collect();
    order.sort_by(|&a, &b| {
        key[b]
            .partial_cmp(&key[a])
            .unwrap_or(std::cmp::Ordering::Equal)
            .then(a.cmp(&b))
    });

    // Dense scratch for the dot products: the cuts are sparse but the pairwise dot of two
    // sparse rows is otherwise quadratic in their lengths. Scattering the selected row once
    // and gathering each candidate against it makes each test linear in the CANDIDATE's
    // nonzeros, which is what the cap on cut nnz already bounds.
    let mut scratch = vec![0.0f64; ncols];
    let mut kept_idx: Vec<usize> = Vec::with_capacity(max_keep.min(cuts.len()));
    for &i in &order {
        if kept_idx.len() >= max_keep {
            break;
        }
        let mut parallel = false;
        for &k in &kept_idx {
            for &(c, a) in &cuts[k].coeffs {
                scratch[c.index()] = a;
            }
            let dot: f64 = cuts[i]
                .coeffs
                .iter()
                .map(|&(c, a)| a * scratch[c.index()])
                .sum();
            for &(c, _) in &cuts[k].coeffs {
                scratch[c.index()] = 0.0;
            }
            if (dot / (norm[i] * norm[k])).abs() > max_parallel {
                parallel = true;
                break;
            }
        }
        if !parallel {
            kept_idx.push(i);
        }
    }

    // Emit in the SELECTED order (deepest first), not the original separation order: the
    // pool's own `MAX_POOL` truncation and the LP's row order then both see the strong rows
    // first, and a round that overflows drops the shallow end.
    let mut cuts: Vec<Option<Cut>> = cuts.into_iter().map(Some).collect();
    let mut out_cuts = Vec::with_capacity(kept_idx.len());
    let mut out_tags = Vec::with_capacity(kept_idx.len());
    for &i in &kept_idx {
        out_cuts.push(cuts[i].take().expect("each index selected once"));
        out_tags.push(tags[i]);
    }
    (out_cuts, out_tags)
}

/// The MIR rounding itself, on the substituted row divided by `delta`, mapped back to `x`.
///
/// ```text
///   Σ_j ( ⌊a_j⌋ + max(0, (f_j − f)/(1 − f)) ) · t_j   +   Σ_{a_j < 0} a_j/(1 − f) · t_j   <=   ⌊b⌋
///        integer j                                          continuous j
/// ```
///
/// with `f = b − ⌊b⌋` and `f_j = a_j − ⌊a_j⌋`, all in exact rationals. `f = 0` means the
/// right-hand side was already integral and there is nothing to round.
fn mir_round(model: &Model, subs: &[Sub], b: &BigRational, delta: &BigRational) -> Option<Cut> {
    // ATTRIBUTION (measurement only, gated): the exact-rational rounding kernel
    // the macOS `sample` profile named. Counts calls and how many yield a cut.
    let _attrib = crate::attrib::on()
        .then(|| crate::attrib::MIR_ROUND_CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed));
    if !crate::sepstat::on() {
        return mir_round_inner(model, subs, b, delta);
    }
    crate::sepstat::bump(&crate::sepstat::MIR_PASS);
    let r = mir_round_inner(model, subs, b, delta);
    if r.is_some() {
        crate::sepstat::bump(&crate::sepstat::MIR_SOME);
    }
    r
}

fn mir_round_inner(
    model: &Model,
    subs: &[Sub],
    b: &BigRational,
    delta: &BigRational,
) -> Option<Cut> {
    let one = BigRational::one();
    let bd = b / delta;
    let fb = &bd - bd.floor();
    if fb.is_zero() {
        crate::sepstat::bump(&crate::sepstat::MIR_EARLY);
        return None; // nothing to round
    }

    // REFUSE A ROW WHOSE FRACTIONALITY IS TOO NEAR 0 OR 1.
    //
    // The rounding divides by `1 − f`. Let `f` sit at `1 − 1e-13` and that factor is 1e13, and the
    // cut comes out with coefficients of 1e13 and a right-hand side of 1e15. It is a VALID
    // inequality and it is a catastrophe: on qnet1 those cuts took the model's coefficient scale to
    // 3.1e13 and its right-hand-side scale to 9.6e15, which wrecks the conditioning of every basis
    // that touches them and made the exact replay of every leaf fail (11 of 11).
    //
    // A cut this steep says almost nothing anyway -- it is a hair away from the trivial rounding it
    // came from. Every real solver refuses it; this one now does too.
    let fmin = BigRational::new(1.into(), 100.into()); // 0.01
    if fb < fmin || fb > &one - &fmin {
        crate::sepstat::bump(&crate::sepstat::MIR_EARLY);
        return None;
    }
    let inv = &one / (&one - &fb);

    // Coefficients on the DISPLACEMENTS.
    let mut ct: Vec<(&Sub, BigRational)> = Vec::with_capacity(subs.len());
    for s in subs {
        let a = &s.a / delta;
        let c = if s.integral {
            let fl = a.floor();
            let fj = &a - &fl;
            if fj > fb {
                fl + (&fj - &fb) * &inv
            } else {
                fl
            }
        } else if a < BigRational::zero() {
            &a * &inv
        } else {
            BigRational::zero()
        };
        if !c.is_zero() {
            ct.push((s, c));
        }
    }
    if ct.is_empty() {
        return None;
    }
    let mut rhs = bd.floor();

    // Map back to the model's own columns.
    //
    //   a COLUMN:      t = x − bound   =>   +c·x,  rhs += c·bound
    //                  t = bound − x   =>   −c·x,  rhs −= c·bound
    //   a VUB SLACK:   t = s = u·y − x =>   −c·x  AND  +c·u·y,  rhs unchanged
    //
    // That binary term is the whole point of the substitution, and dropping it would produce an
    // inequality that is not implied by anything -- an invalid cut, which deletes integer points.
    // BTreeMap for the same determinism reason as `ycoef` in `mir_from_row`: this map is iterated
    // to lay out the stored cut's coefficients, and a hash-ordered row perturbs every float sum
    // the LP takes over it -- a different cut per process from the same derivation.
    let mut xc: std::collections::BTreeMap<usize, BigRational> = std::collections::BTreeMap::new();
    for (s, c) in ct {
        match &s.var {
            Var::Col(j) => {
                if s.complemented {
                    rhs -= &c * &s.bound;
                    *xc.entry(*j).or_insert_with(BigRational::zero) -= c;
                } else {
                    rhs += &c * &s.bound;
                    *xc.entry(*j).or_insert_with(BigRational::zero) += c;
                }
            }
            Var::VubSlack { x, y, u } => {
                *xc.entry(*x).or_insert_with(BigRational::zero) -= &c;
                *xc.entry(*y).or_insert_with(BigRational::zero) += &c * u;
            }
        }
    }

    // To f64, paying for the rounding in the right-hand side so the stored cut is IMPLIED by the
    // exact one. A `<=` store, so the directed fallback in `coef_to_f64` rounds a non-negative
    // column's coefficient DOWN -- the opposite of the GMI `>=` store, and the reason the side is
    // passed in rather than guessed.
    let mut damage = BigRational::zero();
    let mut out: Vec<(Col, f64)> = Vec::with_capacity(xc.len());
    for (j, c) in xc {
        if c.is_zero() {
            continue;
        }
        let col = Col(j as u32);
        let (cf, cost) = coef_to_f64(model, col, &c, CutSide::Le)?;
        damage += cost;
        if cf != 0.0 {
            out.push((col, cf));
        }
    }
    if out.is_empty() {
        crate::sepstat::bump(&crate::sepstat::LATE_EMPTY);
        return None;
    }
    let relaxed = &rhs + &damage;
    let ub0 = to_f64(&relaxed);
    if !ub0.is_finite() {
        crate::sepstat::bump(&crate::sepstat::LATE_NONFINITE);
        return None;
    }
    let ub = if exact(ub0)? < relaxed {
        next_up(ub0)
    } else {
        ub0
    };

    // ...and refuse the finished cut if its numbers are absurd regardless. A row the LP cannot be
    // conditioned around is not a cut, it is a wrecked basis.
    let hi = out.iter().map(|&(_, a)| a.abs()).fold(0.0f64, f64::max);
    let lo = out
        .iter()
        .map(|&(_, a)| a.abs())
        .filter(|&a| a > 0.0)
        .fold(f64::INFINITY, f64::min);
    if hi > MAX_CUT_COEFF || ub.abs() > MAX_CUT_COEFF || hi / lo > MAX_CUT_DYNAMISM {
        crate::sepstat::bump(&crate::sepstat::LATE_ABSURD);
        return None;
    }

    Some(Cut {
        coeffs: out,
        lb: f64::NEG_INFINITY,
        ub,
    })
}

/// STRENGTHENED CHVÁTAL-GOMORY rounding (Letchford & Lodi 2002, Theorem 1) of the substituted row
/// divided by `delta`, mapped back to `x`. A strictly tighter coefficient rule than `mir_round`'s on
/// the INTEGER columns — the family Gurobi's log lists as `StrongCG` beside its MIR cuts on qnet1.
///
/// # The strengthened coefficient
///
/// Write the pure-integer row (after the continuous handling below) as `Σ a_i t_i <= b`, `t_i >= 0`
/// integer, `f = f(b) ∈ (0,1)`. MIR rounds each coefficient with the single-breakpoint function
/// `⌊a⌋ + max(0, (f(a) − f)/(1 − f))`. Strong CG uses the integrality of the `t_i` to reduce it:
/// let `k >= 1` be the unique integer with `1/(k+1) <= f < 1/k` (`k = ⌈1/f⌉ − 1`), partition
/// `(f, 1)` into the `k` equal sub-intervals `(f + (p−1)(1−f)/k, f + p(1−f)/k]`, and round
///
/// ```text
///   g(a) = ⌊a⌋ + p/(k+1),   p = ⌈k·(f(a) − f)/(1 − f)⌉ ∈ {1,…,k}   when f(a) > f,
///   g(a) = ⌊a⌋                                                      when f(a) <= f,
/// ```
///
/// with right-hand side `⌊b⌋`. Dividing Letchford–Lodi's inequality (14) by `k+1` gives exactly
/// this; their Theorem 1 proves it valid for the integer hull and dominating the plain CG cut.
/// Strong CG and MIR do NOT dominate each other (the paper's own remark): near the top of a
/// sub-interval strong CG is WEAKER than MIR, near the bottom STRONGER, so it separates points MIR
/// leaves and the pool keeps whichever is deeper. Its coefficients also carry a bounded denominator
/// `k+1` (unlike MIR's `1/(1−f)`), which is kinder to the exact basis and to `snap`.
///
/// # Why pure-integer, and how the continuous columns are handled
///
/// The strengthened coefficient is a STEP function of `f(a)`, so its continuous extension has
/// unbounded slope — there is NO valid finite per-term coefficient for a continuous column (measured
/// by brute force: the tight multiplier is noisy and reaches `7.5·|a|`, no closed form). So strong
/// CG is applied to the INTEGER part only, and every continuous displacement — a substituted
/// continuous column, and the continuous VUB SLACK the substitution drags in — is projected out by
/// bound substitution: a displacement `t ∈ [0, R]` with coefficient `c` is dropped, paying `|c|·R`
/// into the right-hand side when `c < 0` (it can shrink the LHS by that much) and nothing when
/// `c >= 0` (then `c·t >= 0`, so dropping it only lowers the LHS). No finite range on the paying
/// side kills the cut, exactly as an unbounded column kills a MIR row. The switch binary the VUB
/// substitution folded into the row is an INTEGER column and STAYS — so on a fixed-charge row this is
/// strong CG on the switches with the flow slack paid off, the structure qnet1 and rout are made of.
///
/// EXACTNESS: every coefficient is derived in exact rationals; the `f64` cut has its right-hand side
/// relaxed by the rounding damage exactly as `mir_round`'s does, so the stored cut is IMPLIED by the
/// exact one. `mir_cuts_never_remove_an_integer_point` brute-forces this family too.
fn strongcg_round(
    model: &Model,
    subs: &[Sub],
    b: &BigRational,
    delta: &BigRational,
) -> Option<Cut> {
    // ATTRIBUTION (measurement only, gated); see `mir_round`.
    let _attrib = crate::attrib::on().then(|| {
        crate::attrib::STRONGCG_ROUND_CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    });
    if !crate::sepstat::on() {
        return strongcg_round_inner(model, subs, b, delta);
    }
    crate::sepstat::bump(&crate::sepstat::SCG_PASS);
    let r = strongcg_round_inner(model, subs, b, delta);
    if r.is_some() {
        crate::sepstat::bump(&crate::sepstat::SCG_SOME);
    }
    r
}

fn strongcg_round_inner(
    model: &Model,
    subs: &[Sub],
    b: &BigRational,
    delta: &BigRational,
) -> Option<Cut> {
    let one = BigRational::one();
    let zero = BigRational::zero();

    // Project the continuous displacements out into the right-hand side (undivided units), leaving a
    // pure-integer row. `c·t`, `t ∈ [0,R]`: `c < 0` can lower the LHS by `|c|·R`, so relaxing the
    // RHS by that keeps the dropped cut IMPLIED; `c >= 0` only raises the LHS, so it drops for free.
    let mut b_pen = b.clone();
    for s in subs {
        if s.integral {
            continue;
        }
        if s.a < zero {
            // no finite range on the paying side: no cut
            let Some(r) = strongcg_range(model, &s.var) else {
                crate::sepstat::bump(&crate::sepstat::SCG_RANGE_NONE);
                return None;
            };
            b_pen += (-&s.a) * &r;
        }
    }

    let bd = &b_pen / delta;
    let fb = &bd - bd.floor();
    if fb.is_zero() {
        crate::sepstat::bump(&crate::sepstat::SCG_EARLY);
        return None;
    }
    // Same fractionality guard as `mir_round`: a row a hair from integral rounds to a catastrophe of
    // a cut. It also caps `k = ⌈1/f⌉ − 1 <= 99`, so the `p/(k+1)` denominators stay small.
    let fmin = BigRational::new(1.into(), 100.into()); // 0.01
    if fb < fmin || fb > &one - &fmin {
        crate::sepstat::bump(&crate::sepstat::SCG_EARLY);
        return None;
    }
    // k = ⌈1/f⌉ − 1, the unique integer with 1/(k+1) <= f < 1/k (kept as an integer-valued rational).
    let k_rat = (&one / &fb).ceil() - &one;
    if k_rat < one {
        crate::sepstat::bump(&crate::sepstat::SCG_EARLY);
        return None;
    }
    let kp1 = &k_rat + &one;
    let inv = &one / (&one - &fb);

    // The strengthened coefficients on the integer displacements.
    let mut ct: Vec<(&Sub, BigRational)> = Vec::with_capacity(subs.len());
    for s in subs {
        if !s.integral {
            continue;
        }
        let a = &s.a / delta;
        let fl = a.floor();
        let fj = &a - &fl;
        let c = if fj <= fb {
            fl
        } else {
            // p = ⌈k·(f(a) − f)/(1 − f)⌉, clamped to {1,…,k}.
            let mut p = (&k_rat * (&fj - &fb) * &inv).ceil();
            if p < one {
                p = one.clone();
            }
            if p > k_rat {
                p = k_rat.clone();
            }
            fl + &p / &kp1
        };
        if !c.is_zero() {
            ct.push((s, c));
        }
    }
    if ct.is_empty() {
        return None;
    }
    let mut rhs = bd.floor();

    // Map back to the model's own columns -- identical to `mir_round`. Only Var::Col integer subs
    // reach here (the VUB slack is continuous and was projected out above); the VubSlack arm is kept
    // for parity and can never fire.
    let mut xc: std::collections::BTreeMap<usize, BigRational> = std::collections::BTreeMap::new();
    for (s, c) in ct {
        match &s.var {
            Var::Col(j) => {
                if s.complemented {
                    rhs -= &c * &s.bound;
                    *xc.entry(*j).or_insert_with(BigRational::zero) -= c;
                } else {
                    rhs += &c * &s.bound;
                    *xc.entry(*j).or_insert_with(BigRational::zero) += c;
                }
            }
            Var::VubSlack { x, y, u } => {
                *xc.entry(*x).or_insert_with(BigRational::zero) -= &c;
                *xc.entry(*y).or_insert_with(BigRational::zero) += &c * u;
            }
        }
    }

    // To f64, paying for the rounding in the right-hand side so the stored cut is IMPLIED by the
    // exact one -- verbatim from `mir_round`, `<=` store and all.
    let mut damage = BigRational::zero();
    let mut out: Vec<(Col, f64)> = Vec::with_capacity(xc.len());
    for (j, c) in xc {
        if c.is_zero() {
            continue;
        }
        let col = Col(j as u32);
        let (cf, cost) = coef_to_f64(model, col, &c, CutSide::Le)?;
        damage += cost;
        if cf != 0.0 {
            out.push((col, cf));
        }
    }
    if out.is_empty() {
        crate::sepstat::bump(&crate::sepstat::LATE_EMPTY);
        return None;
    }
    let relaxed = &rhs + &damage;
    let ub0 = to_f64(&relaxed);
    if !ub0.is_finite() {
        crate::sepstat::bump(&crate::sepstat::LATE_NONFINITE);
        return None;
    }
    let ub = if exact(ub0)? < relaxed {
        next_up(ub0)
    } else {
        ub0
    };

    // ...and refuse the finished cut if its numbers are absurd regardless -- verbatim from `mir_round`.
    let hi = out.iter().map(|&(_, a)| a.abs()).fold(0.0f64, f64::max);
    let lo = out
        .iter()
        .map(|&(_, a)| a.abs())
        .filter(|&a| a > 0.0)
        .fold(f64::INFINITY, f64::min);
    if hi > MAX_CUT_COEFF || ub.abs() > MAX_CUT_COEFF || hi / lo > MAX_CUT_DYNAMISM {
        crate::sepstat::bump(&crate::sepstat::LATE_ABSURD);
        return None;
    }

    Some(Cut {
        coeffs: out,
        lb: f64::NEG_INFINITY,
        ub,
    })
}

/// The width of a continuous displacement's range `[0, R]`, for the drop penalty in `strongcg_round`.
/// A substituted continuous column ranges over its box `up − lo`; the VUB slack `s = u·y − x` ranges
/// over `[0, u − lo_x]` (`y ∈ {0,1}`, `x >= lo_x`), and `u − lo_x` upper-bounds it. `None` when the
/// paying side is unbounded — the cut cannot be paid for and is refused.
///
/// NOT a candidate for the directed rounding in [`coef_to_f64`], and deliberately left alone when
/// the other five unbounded-column bails in this file were replaced by it. Those five were paying
/// for `f64` CONVERSION, an artefact the exact derivation never asked for; this one is paying
/// `|a|·R` for genuinely DROPPING a continuous displacement out of the row, which is a term of the
/// Letchford–Lodi inequality itself. An infinite `R` means the dropped term really can move the
/// left-hand side without limit, and no rounding direction changes that. The refusal is the maths.
fn strongcg_range(model: &Model, var: &Var) -> Option<BigRational> {
    match var {
        Var::Col(j) => {
            let (lo, up) = model.col_bounds(Col(*j as u32));
            if !lo.is_finite() || !up.is_finite() {
                return None;
            }
            exact(up - lo)
        }
        Var::VubSlack { x, u, .. } => {
            let (lo, _) = model.col_bounds(Col(*x as u32));
            if !lo.is_finite() {
                return None;
            }
            Some(u - exact(lo)?)
        }
    }
}

fn to_f64(v: &BigRational) -> f64 {
    v.to_f64().unwrap_or(f64::NAN)
}

/// The next `f64` above `v` -- one ulp outward, so a rounded right-hand side can only ever be
/// LOOSER than the exact one it represents.
fn next_up(v: f64) -> f64 {
    if !v.is_finite() {
        return v;
    }
    if v == 0.0 {
        return f64::from_bits(1);
    }
    let b = v.to_bits();
    f64::from_bits(if v > 0.0 { b + 1 } else { b - 1 })
}

/// Which side a cut is STORED on. The direction a coefficient may be rounded depends on it, and
/// getting it backwards manufactures an invalid cut, so it is passed explicitly rather than
/// inferred at each call site.
#[derive(Clone, Copy)]
enum CutSide {
    /// `Σ c·x >= lb`, i.e. `Cut { lb, ub: f64::INFINITY }` -- GMI and mixing store this way.
    Ge,
    /// `Σ c·x <= ub`, i.e. `Cut { lb: f64::NEG_INFINITY, ub }` -- MIR, strong CG and the
    /// aggregated tableau MIR store this way.
    Le,
}

/// ONE exact cut coefficient down to `f64`, plus the exact damage the conversion owes the
/// right-hand side. `None` refuses the whole cut.
///
/// # The bail this replaces, and how much of the corpus it was silencing
///
/// Every separator in this file derives in exact rationals and then has to store an `f64` row. The
/// only way that store can be made safe is to pay for the rounding: `ĉ_j` differs from `c_j` by
/// `|ĉ_j − c_j|`, the term moves by that times `x_j`, and relaxing the right-hand side by
/// `Σ |ĉ_j − c_j| · max|x_j|` over the column's BOX makes the stored cut IMPLIED by the exact one.
/// That argument needs a finite box, so the code did the only other safe thing available and threw
/// the entire cut away the moment one column was unbounded:
///
/// ```text
///     let span = lo.abs().max(up.abs());
///     if !span.is_finite() { return None; }
/// ```
///
/// ONE such column anywhere in a dense row killed the row. Counted over the 90 smallest instances
/// of `~/ay-bench/milp` by replaying the reader's bound defaults (`mps.rs`: a column with no
/// `BOUNDS` entry is `[0, +inf)`), 60 of them -- 67% -- carry at least one column with an infinite
/// side, and only 13 carry a genuinely FREE one. So the bail was firing on the ordinary case and
/// the case it was actually written for is rare. A model whose general integers are ALL unbounded
/// -- gen-ip002, gen-ip021, gen-ip054, ej -- got literally zero cuts out of this engine, at the
/// root and at every node.
///
/// # Directed rounding, which pays nothing and needs no bound
///
/// The span payment is not the only sound conversion. For a `>=` cut and a column with `lo >= 0`,
/// round `c_j` UP to the next representable `f64`:
///
/// ```text
///   ĉ_j >= c_j  and  x_j >= 0   =>   ĉ_j·x_j >= c_j·x_j   =>   Σ ĉ·x >= Σ c·x >= lb
/// ```
///
/// so every point the exact cut admits the stored one admits too -- with the SAME right-hand side,
/// no payment, and no reference to `up` at all. The three mirrors follow from the same two-line
/// argument: a `>=` cut with `up <= 0` rounds DOWN, a `<=` cut with `lo >= 0` rounds DOWN, a `<=`
/// cut with `up <= 0` rounds UP. That is strictly MORE sound than the bail (which had to discard a
/// valid inequality) and never less: it is the exact cut, weakened.
///
/// The one column shape neither argument reaches is the genuinely FREE one, `-inf..+inf`, where
/// `x_j` has no sign and `(ĉ_j − c_j)·x_j` has no sign either. Those still refuse the cut. A column
/// bounded on one side only but straddling zero (`-3..+inf`) is the same case and refuses too.
///
/// This is not a new argument in this file: `emit_le_cut` already runs the `<=` / `lo == 0` corner
/// of it, and its note records that it is what keeps khb05250's unbounded flow columns admissible.
/// What is new is that the other four corners exist and that the five general emitters now use
/// them, instead of every one of them refusing the row.
///
/// # Why the box path is kept where the box exists
///
/// A two-sided-finite box gets the ORIGINAL nearest-`f64` coefficient and pays the span, because
/// that is a strictly tighter row than the directed one: the directed store moves the coefficient
/// by up to a full ulp to buy a zero payment, and on a bounded column the ulp is worth more than
/// the payment it saves. Only a column the span argument cannot serve at all takes the new path.
///
/// A coefficient that is ALREADY an `f64` (`err == 0`) now short-circuits before the box is even
/// consulted -- it owes nothing, so an unbounded column carrying an exact coefficient no longer
/// kills a cut either. That case was previously lost purely to the order of the two tests.
///
/// # What it is worth
///
/// `AY_ROOT_CLOSURE=1`, 10s cut share, the 90 smallest instances of `~/ay-bench/milp`, two
/// binaries built from the same tree and differing only in this file:
///
/// ```text
///   instances shipping ZERO root cuts   28  ->  10
///   mean root closure                 4.97% -> 7.34%
///   closure improved on 28, regressed on 1, root-loop wall 30.3s -> 30.5s over the 90
/// ```
///
/// The eighteen that went from "separates nothing" to a live pool: ej, enlight4, enlight8,
/// enlight9, enlight11, enlight_hard, b-ball, blend2, dcmulti, gen-ip002, gen-ip016, gen-ip021,
/// gen-ip036, gen-ip054, misc05inf, neos-3072252-nete, neos-3754480-nidda, neos-5192052-neckar.
/// The largest single gains are b-ball 0 -> 75.35% and neos-3754480-nidda 0 -> 5.94%; the
/// unbounded-general-integer family lands at gen-ip002 1.81%, gen-ip021 1.80%, gen-ip054 0.91%.
/// Instances that already had a pool gain too, because the bail was also silencing individual
/// ROWS inside them: gr4x6 38.3% -> 71.8%, ran13x13 7.5% -> 17.6%, flugpl 2.0% -> 9.3%,
/// rout 0.32% -> 0.61%.
///
/// THE ONE CLOSURE REGRESSION is nexp-50-20-1-1, 14.5% -> 5.9%, and it is a SELECTION effect
/// rather than a weaker row: the instance goes from 3 cuts to 6, and `select_cuts` ranks the
/// newly-admissible rows above the ones that were moving the bound. That is the known open problem
/// this file already records at `separate_mir`'s note ("the unsolved problem here is not which
/// family: it is WHICH CUTS TO KEEP"), now with one more instance in its evidence.
///
/// A 15s FULL-SOLVE sweep over the same 90 instances moves no verdict that survives a re-run.
/// Zero disagreements against the MIPLIB reference in either arm. Two differences appeared:
///   * newdano UNKNOWN -> FEASIBLE (incumbent 92.667), and it REPRODUCES on repeat runs — the
///     search had no incumbent at all before and now finds one;
///   * neos-3610040-iskar OPTIMAL -> FEASIBLE, and it does NOT reproduce: run alone at a 15s
///     limit both arms prove OPTIMAL 37 in ~11.98s at an identical 68,681 nodes, so the sweep was
///     measuring its own machine load against a 15s wall, not this change.
///
/// # Which bounds these are
///
/// `model.col_bounds` is the GLOBAL bound array in every caller (`bab.rs:4887` passes the root
/// loop's model; `bab.rs:22447` passes the root `model` itself at tree nodes), so `lo >= 0` here is
/// a fact about the model, not about a node. A node's bounds are tighter, so `lo_node >= lo >= 0`
/// and the sign argument survives being carried down the tree -- which is what makes a cut derived
/// once safe to keep everywhere. This is the same license the span payment already ran on.
fn coef_to_f64(
    model: &Model,
    col: Col,
    c: &BigRational,
    side: CutSide,
) -> Option<(f64, BigRational)> {
    let cf = c.to_f64()?;
    if !cf.is_finite() {
        return None;
    }
    let back = exact(cf)?;
    let err = (&back - c).abs();
    if err.is_zero() {
        return Some((cf, BigRational::zero()));
    }
    let (lo, up) = model.col_bounds(col);
    if lo.is_finite() && up.is_finite() {
        return Some((cf, err * exact(lo.abs().max(up.abs()))?));
    }

    // No finite box. `lo >= 0.0` is false for `-inf` and `up <= 0.0` is false for `+inf`, so these
    // two tests already exclude the free and the straddling column without a separate check.
    let round_up = match (side, lo >= 0.0, up <= 0.0) {
        (CutSide::Ge, true, _) | (CutSide::Le, _, true) => true,
        (CutSide::Ge, _, true) | (CutSide::Le, true, _) => false,
        _ => return None,
    };
    // `to_f64`'s rounding mode is not part of its contract, so the direction is not assumed from
    // it: take the neighbour only when the nearest value is on the wrong side, then PROVE the
    // result lies where the argument above needs it. A cut is the one thing here that can delete
    // an optimum, so the inequality is checked exactly rather than reasoned about.
    let adj = if round_up {
        if &back > c {
            cf
        } else {
            next_up(cf)
        }
    } else if &back < c {
        cf
    } else {
        next_down(cf)
    };
    let adj_exact = exact(adj)?; // `None` if a neighbour step overflowed to an infinity
    let sound = if round_up {
        &adj_exact >= c
    } else {
        &adj_exact <= c
    };
    sound.then(|| (adj, BigRational::zero()))
}

#[cfg(test)]
mod gmi_tests;

#[cfg(test)]
mod selection_tests {
    use super::*;

    fn cut(coeffs: &[(u32, f64)], ub: f64) -> Cut {
        Cut {
            coeffs: coeffs.iter().map(|&(c, a)| (Col(c), a)).collect(),
            lb: f64::NEG_INFINITY,
            ub,
        }
    }

    /// The identity settings must return the input UNTOUCHED — same cuts, same order.
    /// This is what makes `AY_MILP_CUT_MAX_PARALLEL=1 the cut-topk knob=0` a valid A/B
    /// control: if the identity path perturbed the order, every ablation against it would
    /// be measuring the reordering rather than the selection.
    #[test]
    fn identity_settings_are_the_identity() {
        let cuts = vec![
            cut(&[(0, 1.0), (1, 1.0)], 1.0),
            cut(&[(0, 1.0)], 0.5),
            cut(&[(1, 3.0), (2, -1.0)], 2.0),
        ];
        let want: Vec<Vec<(Col, f64)>> = cuts.iter().map(|c| c.coeffs.clone()).collect();
        let x = vec![1.0, 1.0, 1.0];
        let (got, tags) = select_cuts(cuts, vec![0u8, 1, 2], &x, usize::MAX, 1.0, 3, 0.0, &[]);
        assert_eq!(tags, vec![0, 1, 2]);
        let got: Vec<Vec<(Col, f64)>> = got.into_iter().map(|c| c.coeffs).collect();
        assert_eq!(got, want);
    }

    /// A duplicate row — same inequality written twice — must not survive the filter, and
    /// the one that DOES survive must be the deeper of the two.
    #[test]
    fn exact_duplicates_are_rejected_keeping_the_deeper() {
        // Both cuts are `x0 + x1 <= b`; the second is scaled by 10, which leaves the
        // inequality (and so the cosine) identical while multiplying the raw violation.
        // Ranking on raw violation would call them different; ranking on EFFICACY does not.
        let shallow = cut(&[(0, 1.0), (1, 1.0)], 1.5);
        let deep = cut(&[(0, 10.0), (1, 10.0)], 5.0); // depth 1.5/√2 vs 0.5/√2
        let x = vec![1.0, 1.0, 0.0];
        let (got, tags) = select_cuts(
            vec![shallow, deep],
            vec!["shallow", "deep"],
            &x,
            usize::MAX,
            0.99,
            3,
            0.0,
            &[],
        );
        assert_eq!(got.len(), 1, "a duplicated inequality must be kept once");
        assert_eq!(tags, vec!["deep"], "the survivor must be the deeper row");
    }

    /// Cuts pointing in genuinely different directions all survive: the filter must reject
    /// redundancy, not diversity. An orthogonality filter that dropped independent rows
    /// would cost bound, which is the whole point of the exercise.
    #[test]
    fn orthogonal_cuts_all_survive() {
        let cuts = vec![
            cut(&[(0, 1.0)], 0.5),
            cut(&[(1, 1.0)], 0.5),
            cut(&[(2, 1.0)], 0.5),
        ];
        let x = vec![1.0, 1.0, 1.0];
        let (got, _) = select_cuts(cuts, vec![0u8, 1, 2], &x, usize::MAX, 0.5, 3, 0.0, &[]);
        assert_eq!(got.len(), 3);
    }

    /// The top-K cap keeps the K DEEPEST, not the first K separated.
    #[test]
    fn topk_keeps_the_deepest() {
        // Three mutually orthogonal rows so the parallelism filter cannot interfere;
        // depths are 0.9, 0.1, 0.5 in separation order.
        let cuts = vec![
            cut(&[(0, 1.0)], 0.1),
            cut(&[(1, 1.0)], 0.9),
            cut(&[(2, 1.0)], 0.5),
        ];
        let x = vec![1.0, 1.0, 1.0];
        let (got, tags) = select_cuts(cuts, vec!["a", "b", "c"], &x, 2, 1.0, 3, 0.0, &[]);
        assert_eq!(got.len(), 2);
        assert_eq!(
            tags,
            vec!["a", "c"],
            "deepest first: a (0.9), c (0.5), then b (0.1)"
        );
    }

    /// Anti-parallel rows (cosine −1) are as redundant as parallel ones for this purpose:
    /// `a·x <= b` and `−a·x <= −b'` bracket the same hyperplane direction, so one of them
    /// adds a dimension of freight the other already priced. The filter tests |cos|.
    #[test]
    fn antiparallel_counts_as_parallel() {
        let up = cut(&[(0, 1.0), (1, 1.0)], 1.0);
        let down = Cut {
            coeffs: vec![(Col(0), -1.0), (Col(1), -1.0)],
            lb: 2.5,
            ub: f64::INFINITY,
        };
        let x = vec![1.0, 1.0, 0.0];
        let (got, _) = select_cuts(
            vec![up, down],
            vec![0u8, 1],
            &x,
            usize::MAX,
            0.9,
            3,
            0.0,
            &[],
        );
        assert_eq!(got.len(), 1);
    }

    // ---------------------------------------------------------------------------------
    // W2 — the fractionality-penalised rank (default off; see the doc on `select_cuts`).
    // ---------------------------------------------------------------------------------

    /// `frac_penalty = 0` MUST be the pre-W2 depth rank, whatever mask it is handed.
    ///
    /// This is the A/B control for the whole W2 measurement. If a zero penalty perturbed
    /// the order even once, the arm would be measuring the reordering and not the rule,
    /// which is the exact mistake `identity_settings_are_the_identity` exists to prevent
    /// one level up. `depth / (1 + 0·k)` is `depth / 1.0`, and dividing an `f64` by exactly
    /// `1.0` is exact — so this is a bit-for-bit claim, not a tolerance claim.
    #[test]
    fn frac_penalty_zero_is_the_depth_rank() {
        let mk = || {
            vec![
                cut(&[(0, 1.0)], 0.1),
                cut(&[(1, 1.0)], 0.9),
                cut(&[(2, 1.0)], 0.5),
            ]
        };
        let x = vec![1.0, 1.0, 1.0];
        // A mask that WOULD reorder everything if it were consulted: the DEEPEST row's
        // column (0, depth 0.9) is the only "newly fractionable" one, so any nonzero
        // penalty would demote it below `c`.
        let mask = [true, false, false];
        let (plain, plain_tags) = select_cuts(mk(), vec!["a", "b", "c"], &x, 2, 1.0, 3, 0.0, &[]);
        let (masked, masked_tags) =
            select_cuts(mk(), vec!["a", "b", "c"], &x, 2, 1.0, 3, 0.0, &mask);
        assert_eq!(plain_tags, masked_tags);
        assert_eq!(
            plain_tags,
            vec!["a", "c"],
            "deepest first: a (0.9), c (0.5)"
        );
        let coeffs =
            |cs: Vec<Cut>| -> Vec<Vec<(Col, f64)>> { cs.into_iter().map(|c| c.coeffs).collect() };
        assert_eq!(coeffs(plain), coeffs(masked));
    }

    /// With the penalty ON, a budget spends itself on the row that buys its bound over
    /// FEWER currently-integral integer columns.
    ///
    /// `b` is the deepest row (0.9) but touches three integral integer columns, so at
    /// `lambda = 1` its key is `0.9/4 = 0.225`; `a` is shallower (0.6) and touches one, so
    /// its key is `0.6/2 = 0.30`. A one-row budget takes `a` under W2 and `b` without it.
    /// That inversion is the entire mechanism, so it is pinned in both directions.
    #[test]
    fn frac_penalty_prefers_bound_per_added_fractional_column() {
        let mk = || {
            vec![
                cut(&[(0, 1.0)], 0.4), // depth 0.6 at x0 = 1, one masked column
                cut(&[(1, 1.0), (2, 0.0), (3, 0.0)], 0.1), // depth 0.9, three masked columns
            ]
        };
        // Columns 2 and 3 appear with coefficient ZERO in row `b`. They must not be
        // charged: a structurally-present-but-zero entry does not touch the column, and a
        // count that ignored the coefficient would price padding.
        let x = vec![1.0, 1.0, 1.0, 1.0];
        let mask = [true, true, true, true];
        let (_, off) = select_cuts(mk(), vec!["a", "b"], &x, 1, 1.0, 4, 0.0, &mask);
        assert_eq!(off, vec!["b"], "without the penalty the deepest row wins");
        let (_, zero_pad) = select_cuts(mk(), vec!["a", "b"], &x, 1, 1.0, 4, 1.0, &mask);
        assert_eq!(
            zero_pad,
            vec!["b"],
            "zero coefficients are not touches: b still charges 1, key 0.45 > a's 0.30"
        );
        // Now give `b` three REAL touches and the ranking must invert.
        let real = || {
            vec![
                cut(&[(0, 1.0)], 0.4),
                cut(&[(1, 1.0), (2, 1.0), (3, 1.0)], 2.1),
            ]
        };
        let (_, on) = select_cuts(real(), vec!["a", "b"], &x, 1, 1.0, 4, 1.0, &mask);
        assert_eq!(
            on,
            vec!["a"],
            "with the penalty the row that fractionalises fewer columns wins the budget"
        );
    }

    /// Only columns that are INTEGRAL at the vertex are chargeable, and an out-of-range
    /// column is charged nothing rather than panicking.
    ///
    /// The mask the root loop builds is `integer column AND integral at x`. A cut may still
    /// name a column outside it — the aggregated family introduces rows over a working
    /// model the caller's mask was not sized for — and a ranking heuristic must not be able
    /// to abort the solve. It is charged zero, which is the conservative direction: it can
    /// only make the row look BETTER, never invent a penalty.
    #[test]
    fn frac_penalty_ignores_unmasked_and_out_of_range_columns() {
        let cuts = vec![
            cut(&[(0, 1.0), (9, 1.0)], 0.4), // column 9 is past the end of the mask
            cut(&[(1, 1.0)], 0.4),
        ];
        let x = vec![1.0, 1.0, 1.0, 1.0];
        let mask = [true, false, false, false];
        // Row 0 charges 1 (column 0 masked, column 9 unknown -> free) -> key 0.6/√2/2.
        // Row 1 charges 0 (column 1 not in the mask) -> key 0.6.
        let (got, tags) = select_cuts(cuts, vec!["wide", "narrow"], &x, 1, 1.0, 4, 1.0, &mask);
        assert_eq!(tags, vec!["narrow"]);
        assert_eq!(got.len(), 1);
    }

    /// SELECTION CANNOT REMOVE A FEASIBLE INTEGER POINT — brute-forced over the whole box,
    /// with the penalty on and off, at every budget.
    ///
    /// The argument is short and it is worth writing down because it is what licenses
    /// shipping a *ranking* change at all: `select_cuts` is a pure SUBSET-AND-PERMUTE of its
    /// input. It never constructs a `Cut`, never edits one's `coeffs`, `lb` or `ub`, and
    /// every row it is handed has already passed the family's own validity proof plus
    /// `clean`/`snap` in the root loop. So the set of inequalities the search ends up
    /// carrying is a SUBSET of a set that is valid for the integer hull, and a subset of
    /// valid inequalities is valid. Changing WHICH ones are kept — which is all W2 does —
    /// therefore cannot move a verdict or an objective; it can only change the search.
    ///
    /// A proof by inspection is not a test, though, and the failure it guards against is
    /// silent: an invalid row that survives selection produces a witness that is genuinely
    /// feasible for the model the solver was left holding. So: random models with mixed
    /// integer/continuous columns, separate the real families against a real vertex, run
    /// selection at every budget and both penalties, and assert on the OUTPUT that (a) no
    /// feasible point of the box is deleted and (b) every emitted row is byte-identical to
    /// one of the inputs. (b) is what makes (a) transitive from the families' own guards:
    /// it pins that selection is subset-and-permute rather than merely happening to be
    /// valid on this seed.
    #[test]
    fn selection_never_removes_a_feasible_integer_point() {
        use crate::model::Sense;

        let mut seed = 0x0F27_2026_u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };
        const HI: i64 = 4;
        let mut selected_rows = 0usize;

        for case in 0..120 {
            let mut m = Model::new();
            // Two integer columns and one continuous one: enough structure for the MIR /
            // strong-CG split to matter, small enough to enumerate exhaustively.
            let cols = [
                m.add_int_col(0.0, HI as f64),
                m.add_int_col(0.0, HI as f64),
                m.add_col(0.0, HI as f64),
            ];
            let n = cols.len();
            let mut rows: Vec<(Vec<f64>, f64, f64)> = Vec::new();
            for _ in 0..3 {
                let a: Vec<f64> = (0..n).map(|_| (rnd() % 9 - 4) as f64).collect();
                if a.iter().all(|&v| v == 0.0) {
                    continue;
                }
                let hi = (rnd() % 13) as f64;
                let lo = hi - (1 + rnd() % 10) as f64;
                let terms: Vec<_> = cols
                    .iter()
                    .zip(&a)
                    .filter(|(_, &v)| v != 0.0)
                    .map(|(&c, &v)| (c, v))
                    .collect();
                m.add_row(lo, hi, &terms);
                rows.push((a, lo, hi));
            }
            if rows.is_empty() {
                continue;
            }
            m.set_objective(&[(cols[0], 1.0)], Sense::Minimize);

            let x: Vec<f64> = (0..n).map(|_| (rnd() % 40) as f64 / 10.0).collect();
            let mut cuts = separate_mir(&m, &x, m.num_rows(), cuts_per_round());
            cuts.extend(separate_strongcg(&m, &x, m.num_rows(), cuts_per_round()));
            if cuts.is_empty() {
                continue;
            }
            let inputs: Vec<(Vec<(Col, f64)>, f64, f64)> = cuts
                .iter()
                .map(|c| (c.coeffs.clone(), c.lb, c.ub))
                .collect();
            let mask: Vec<bool> = (0..n)
                .map(|j| m.col_kind(cols[j]).is_integral() && (x[j] - x[j].round()).abs() <= 1e-9)
                .collect();

            for &penalty in &[0.0, 0.5, 1.0, 8.0] {
                for keep in [1usize, 2, 3, usize::MAX] {
                    for &par in &[0.5, 0.99, 1.0] {
                        let tags: Vec<usize> = (0..cuts.len()).collect();
                        let (sel, sel_tags) =
                            select_cuts(cuts.clone(), tags, &x, keep, par, n, penalty, &mask);
                        assert!(sel.len() <= inputs.len(), "selection invented rows");
                        assert_eq!(sel.len(), sel_tags.len());
                        selected_rows += sel.len();
                        for (row, &t) in sel.iter().zip(&sel_tags) {
                            // (b) SUBSET-AND-PERMUTE: byte-identical to the tagged input.
                            let (want_c, want_lb, want_ub) = &inputs[t];
                            assert_eq!(&row.coeffs, want_c, "case {case}: coefficients edited");
                            assert!(
                                row.lb.to_bits() == want_lb.to_bits()
                                    && row.ub.to_bits() == want_ub.to_bits(),
                                "case {case}: bounds edited by selection"
                            );
                        }
                        // (a) NO FEASIBLE INTEGER POINT DELETED, exact rational activity.
                        for x0 in 0..=HI {
                            for x1 in 0..=HI {
                                for x2 in 0..=HI {
                                    let pt = [x0 as f64, x1 as f64, x2 as f64];
                                    let feasible = rows.iter().all(|(a, lo, hi)| {
                                        let act: f64 =
                                            a.iter().zip(pt).map(|(&ai, xi)| ai * xi).sum();
                                        act >= *lo - 1e-9 && act <= *hi + 1e-9
                                    });
                                    if !feasible {
                                        continue;
                                    }
                                    for c in &sel {
                                        let mut act = BigRational::zero();
                                        for &(col, a) in &c.coeffs {
                                            act +=
                                                exact(a).unwrap() * exact(pt[col.index()]).unwrap();
                                        }
                                        if c.lb.is_finite() {
                                            assert!(
                                                act >= exact(c.lb).unwrap(),
                                                "case {case} (penalty {penalty}, keep {keep}, \
                                                 par {par}): a SELECTED `>=` row deleted the \
                                                 feasible integer point {pt:?}"
                                            );
                                        }
                                        if c.ub.is_finite() {
                                            assert!(
                                                act <= exact(c.ub).unwrap(),
                                                "case {case} (penalty {penalty}, keep {keep}, \
                                                 par {par}): a SELECTED `<=` row deleted the \
                                                 feasible integer point {pt:?}"
                                            );
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        // A guard that selected nothing proves nothing. Pin that the generator actually fed
        // the assertions -- this is the "quasi-vacuous success" failure mode.
        assert!(
            selected_rows > 500,
            "brute-force guard was near-vacuous: only {selected_rows} rows ever selected"
        );
    }
}

#[cfg(test)]
mod mir_tests {
    use super::*;
    use crate::model::Sense;

    fn assert_mir_cuts_admit_integer_points(
        case: usize,
        model: &Model,
        columns: &[Col],
        rows: &[(Vec<f64>, f64, f64)],
        cuts: &[Cut],
    ) {
        let ranges: Vec<i64> = columns
            .iter()
            .map(|&column| {
                let (lo, up) = model.col_bounds(column);
                (up - lo).round() as i64 + 1
            })
            .collect();
        let total: i64 = ranges.iter().product();
        for code in 0..total {
            let mut point = vec![0.0; columns.len()];
            let mut rest = code;
            for (value, &range) in point.iter_mut().zip(&ranges) {
                *value = (rest % range) as f64;
                rest /= range;
            }
            let feasible = rows.iter().all(|(coefficients, lower, upper)| {
                let activity: f64 = coefficients
                    .iter()
                    .zip(&point)
                    .map(|(&coefficient, &value)| coefficient * value)
                    .sum();
                activity >= lower - 1e-9 && activity <= upper + 1e-9
            });
            if !feasible {
                continue;
            }
            for cut in cuts {
                let activity: f64 = cut
                    .coeffs
                    .iter()
                    .map(|&(column, coefficient)| coefficient * point[column.index()])
                    .sum();
                assert!(
                    activity <= cut.ub + 1e-6,
                    "case {case}: a MIR cut deleted the integer point {point:?} -- \
                     activity {activity} exceeds its bound {}",
                    cut.ub
                );
            }
        }
    }

    /// A CUT MAY NOT DELETE AN INTEGER POINT. Brute-forced.
    ///
    /// This is the one guarantee a cut family owes, and the only one that matters: an invalid
    /// inequality removes integer points, and the search then proves an optimum that was never
    /// there. Nothing downstream catches it -- not the exact rim, not the verdict gate, because
    /// every witness it produces is genuinely feasible for the model it was handed. The model is
    /// just no longer the caller's.
    ///
    /// It is not hypothetical. The first cut of this family had the complemented constant crossing
    /// to the right-hand side with the wrong SIGN, and on MIPLIB's qnet1 it lifted the root bound
    /// to 46629 against an optimum of 16030 -- it had deleted the optimum outright.
    ///
    /// So: random models, enumerate every point of the box, and check that every point the MODEL
    /// admits also satisfies every cut separated from it.
    #[test]
    fn mir_cuts_never_remove_an_integer_point() {
        let mut seed = 0xBEEF_2026_u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };
        const HI: i64 = 5;

        for case in 0..400 {
            let n = 3usize;
            let mut m = Model::new();
            // A mix of integer and continuous columns -- MIR treats them differently, and the
            // continuous branch of the formula is the easy one to get wrong.
            let cols: Vec<Col> = (0..n)
                .map(|j| {
                    if j % 3 == 2 {
                        m.add_col(0.0, HI as f64)
                    } else {
                        m.add_int_col(0.0, HI as f64)
                    }
                })
                .collect();
            // FIXED-CHARGE STRUCTURE: a continuous flow gated by a binary switch, `x <= u·y`.
            // This is what the VUB substitution keys off, and a substitution that forgets to bring
            // the binary back produces an invalid cut. The guard has to contain the structure or it
            // is not guarding the code that matters.
            let sw = m.add_binary_col();
            let flow = m.add_col(0.0, HI as f64);
            m.add_row(f64::NEG_INFINITY, 0.0, &[(flow, 1.0), (sw, -(HI as f64))]);
            let cols: Vec<Col> = cols.into_iter().chain([sw, flow]).collect();
            let n = cols.len();
            // ...and the VUB row goes into the model's own row list too, or the enumeration below
            // will call `flow = 5, sw = 0` feasible and blame the cut for excluding it.
            let mut vub_a = vec![0.0f64; n];
            vub_a[n - 1] = 1.0; // flow
            vub_a[n - 2] = -(HI as f64); // sw
            let mut rows: Vec<(Vec<f64>, f64, f64)> = vec![(vub_a, f64::NEG_INFINITY, 0.0)];
            for _ in 0..2 {
                let a: Vec<f64> = (0..n).map(|_| (rnd() % 9 - 4) as f64).collect();
                if a.iter().all(|&v| v == 0.0) {
                    continue;
                }
                let hi = (rnd() % 15) as f64;
                let lo = hi - (1 + rnd() % 12) as f64;
                let terms: Vec<_> = cols
                    .iter()
                    .zip(&a)
                    .filter(|(_, &v)| v != 0.0)
                    .map(|(&c, &v)| (c, v))
                    .collect();
                m.add_row(lo, hi, &terms);
                rows.push((a, lo, hi));
            }
            if rows.is_empty() {
                continue;
            }
            m.set_objective(&[(cols[0], 1.0)], Sense::Minimize);

            // A point to separate against -- an arbitrary interior one will do; validity may not
            // depend on WHERE the cut was separated from.
            let x: Vec<f64> = (0..n).map(|_| (rnd() % 50) as f64 / 10.0).collect();
            // BOTH COMPLEMENTATIONS. `BoundPolicy::Knapsack` shifts columns to the FAR bound, which
            // is the sign-sensitive half of the derivation (`b -= a·u` with `a < 0` moves a POSITIVE
            // constant into the right-hand side, and getting that backwards is exactly the bug this
            // test was written for). The knapsack path is default-off, so without `knap_scope` the
            // enumeration below would never see a single cut it produced.
            let mut cuts = Vec::new();
            for knap in [false, true] {
                knap_scope(knap, || {
                    cuts.extend(separate_mir(&m, &x, m.num_rows(), cuts_per_round()));
                    // ...and the STRENGTHENED CHVÁTAL-GOMORY family, which rounds the same rows
                    // harder: its step-function coefficient and its continuous-drop RHS penalty are
                    // exactly the places a strengthening can cross from "valid" to "deletes the
                    // optimum", so it is brute-forced on the same models (including the fixed-charge
                    // VUB structure below).
                    cuts.extend(separate_strongcg(&m, &x, m.num_rows(), cuts_per_round()));
                });
            }
            // ...and the TABLEAU family too: it is the one whose multipliers come from a float
            // BTRAN, so it is the one most likely to produce something that is nearly-but-not-quite
            // an equation, and a cut that is nearly-but-not-quite valid deletes the optimum.
            let objective: Vec<(u32, f64)> = vec![(0, 1.0)];
            if let Some(lp) = FloatLp::from_model(&m, &objective, Sense::Minimize) {
                let cand = lp.solve_bounded(&lp.lower.clone(), &lp.upper.clone(), None, None);
                if cand.status == crate::simplex::SimplexStatus::Optimal {
                    cuts.extend(separate_mir_tableau(&m, &lp, &cand));
                    // The dual-aggregate MIR family rides the same enumeration guard (audit
                    // must-fix: it was the only new family with zero validity coverage).
                    cuts.extend(separate_mir_dual_agg(&m, &lp, &cand));
                }
            }

            // Every point of the box the MODEL admits must satisfy every cut. Each column is
            // enumerated over ITS OWN range -- the binary switch is 0/1, not 0..5.
            assert_mir_cuts_admit_integer_points(case, &m, &cols, &rows, &cuts);
        }
    }

    /// THE AGGREGATED FAMILY OWES THE SAME GUARANTEE, and its extra failure mode is the
    /// aggregation itself: a multiplier with the wrong SIGN on a one-sided partner, or an
    /// equality folded in against the wrong right-hand side, produces a plausible-looking row
    /// that no combination of model rows implies -- and the MIR of an invalid row is an invalid
    /// cut. Random models carrying exactly the structure the walk keys on (an equality
    /// threading a continuous column through integer columns, plus one-sided rows over the same
    /// columns), every point of the box enumerated -- the continuous column on a HALF-integer
    /// grid, so a cut leaning on a fractional continuous value is caught too.
    #[test]
    fn aggregated_mir_cuts_never_remove_an_integer_point() {
        let mut seed = 0xA66_2026_u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };
        const HI: i64 = 4;
        let mut total_cuts = 0usize;

        for case in 0..300 {
            let mut m = Model::new();
            let y1 = m.add_int_col(0.0, HI as f64);
            let y2 = m.add_int_col(0.0, HI as f64);
            let z = m.add_int_col(0.0, HI as f64);
            let w = m.add_col(0.0, (2 * HI) as f64); // continuous
            let cols = [y1, y2, z, w];
            let n = cols.len();
            let mut rows: Vec<(Vec<f64>, f64, f64)> = Vec::new();
            // The DEFINING EQUALITY -- the partner the aggregation walk cancels through.
            let a = (1 + rnd().rem_euclid(3)) as f64;
            let b = (1 + rnd().rem_euclid(3)) as f64;
            let c = rnd().rem_euclid(3) as f64;
            m.add_row(c, c, &[(w, 1.0), (y1, -a), (y2, -b)]);
            rows.push((vec![-a, -b, 0.0, 1.0], c, c));
            // One-sided rows over the same columns: base rows for the walk, and candidate
            // partners whose multiplier sign the walk must get right.
            for _ in 0..2 {
                let av: Vec<f64> = (0..n).map(|_| (rnd().rem_euclid(7) - 3) as f64).collect();
                if av.iter().all(|&v| v == 0.0) {
                    continue;
                }
                let hi_r = rnd().rem_euclid(13) as f64;
                let lo_r = hi_r - (1 + rnd().rem_euclid(10)) as f64;
                let terms: Vec<_> = cols
                    .iter()
                    .zip(&av)
                    .filter(|(_, &v)| v != 0.0)
                    .map(|(&cc, &v)| (cc, v))
                    .collect();
                m.add_row(lo_r, hi_r, &terms);
                rows.push((av, lo_r, hi_r));
            }
            m.set_objective(&[(cols[0], 1.0)], Sense::Minimize);

            // An arbitrary separation point; validity may not depend on where the cut was
            // separated from.
            let x: Vec<f64> = (0..n)
                .map(|_| (rnd().rem_euclid(40)) as f64 / 10.0)
                .collect();
            // Both complementations here too — `separate_mir_agg` rounds through `mir_from_row`,
            // so the knapsack policy applies to the AGGREGATE, where the constant that moves into
            // the right-hand side is itself a sum of scaled partner right-hand sides.
            let mut cuts = Vec::new();
            for knap in [false, true] {
                knap_scope(knap, || {
                    cuts.extend(separate_mir_agg(&m, &x, m.num_rows(), 8));
                });
            }
            total_cuts += cuts.len();

            // Integer columns on their integer grids, the continuous column on halves.
            for code in 0..(HI + 1).pow(3) {
                let (mut t, mut p) = (code, vec![0.0f64; n]);
                for v in p.iter_mut().take(3) {
                    *v = (t % (HI + 1)) as f64;
                    t /= HI + 1;
                }
                for wk in 0..=(4 * HI) {
                    p[3] = wk as f64 / 2.0;
                    let feasible = rows.iter().all(|(av, lo, hi)| {
                        let act: f64 = av.iter().zip(&p).map(|(&cf, &v)| cf * v).sum();
                        act >= lo - 1e-9 && act <= hi + 1e-9
                    });
                    if !feasible {
                        continue;
                    }
                    for cut in &cuts {
                        let act: f64 = cut
                            .coeffs
                            .iter()
                            .map(|&(col, cf)| cf * p[col.index()])
                            .sum();
                        assert!(
                            act <= cut.ub + 1e-6 && act >= cut.lb - 1e-6,
                            "case {case}: an aggregated MIR cut deleted the feasible point {p:?} \
                             -- activity {act} outside [{}, {}]",
                            cut.lb,
                            cut.ub
                        );
                    }
                }
            }
        }
        // A guard that never sees a cut guards nothing.
        assert!(
            total_cuts > 0,
            "no aggregated MIR cut was ever separated: the guard is vacuous"
        );
    }

    /// THE KNAPSACK-FORM COMPLEMENTATION IS EXERCISED, AND WHAT IT PRODUCES IS VALID.
    ///
    /// The row is the qnet1 capacity shape in miniature: `3y₁ + 2y₂ + 2y₃ − 2b <= 0` with `y`
    /// binary, `b ∈ {0,1,2}` a general integer, and a RIGHT-HAND SIDE OF ZERO. At a point where
    /// `b` sits nearer its lower bound, `BoundPolicy::Near` substitutes `b` at 0, the shifted
    /// right-hand side stays 0, and `b/δ` is integral for EVERY `δ` — so MIR yields nothing at all.
    /// `BoundPolicy::Knapsack` complements `b` at its upper bound, moving `2·2 = 4` into the
    /// right-hand side, and `δ = 3` then gives `y₁ + ½y₂ + ½y₃ <= ½b`.
    ///
    /// The test pins three things: `Near` really is empty here, `Knapsack` really is not (so the
    /// brute-force guards above are not vacuous on this path), and every feasible integer point
    /// satisfies what `Knapsack` emits.
    #[test]
    fn knapsack_complementation_fires_and_stays_valid() {
        let mut m = Model::new();
        let y1 = m.add_binary_col();
        let y2 = m.add_binary_col();
        let y3 = m.add_binary_col();
        let b = m.add_int_col(0.0, 2.0);
        // The self-gate wants a continuous column somewhere in the model.
        let s = m.add_col(0.0, 1.0);
        m.add_row(
            f64::NEG_INFINITY,
            0.0,
            &[(y1, 3.0), (y2, 2.0), (y3, 2.0), (b, -2.0)],
        );
        m.set_objective(&[(b, 1.0)], Sense::Minimize);
        let x = vec![0.5, 0.5, 0.5, 0.5, 0.5];
        let _ = (s, y1, y2, y3);

        let near = knap_scope(false, || separate_mir(&m, &x, m.num_rows(), 8));
        let knap = knap_scope(true, || separate_mir(&m, &x, m.num_rows(), 8));
        assert!(
            near.is_empty(),
            "the nearest-bound rule should say nothing about a zero-right-hand-side row, got {} cuts",
            near.len()
        );
        assert!(
            !knap.is_empty(),
            "the knapsack complementation must separate the capacity row it exists for"
        );

        // Every feasible integer point of the row satisfies every cut. `s` is not in the row, so
        // it is enumerated at its two bounds only; the rest is the full box.
        for c1 in 0..2 {
            for c2 in 0..2 {
                for c3 in 0..2 {
                    for bv in 0..3 {
                        for sv in [0.0, 1.0] {
                            let p = [c1 as f64, c2 as f64, c3 as f64, bv as f64, sv];
                            if 3.0 * p[0] + 2.0 * p[1] + 2.0 * p[2] - 2.0 * p[3] > 1e-9 {
                                continue;
                            }
                            for cut in &knap {
                                let act: f64 = cut
                                    .coeffs
                                    .iter()
                                    .map(|&(col, cf)| cf * p[col.index()])
                                    .sum();
                                assert!(
                                    act <= cut.ub + 1e-6 && act >= cut.lb - 1e-6,
                                    "a knapsack-form MIR cut deleted the feasible point {p:?} \
                                     -- activity {act} outside [{}, {}]",
                                    cut.lb,
                                    cut.ub
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    /// THE COMPLEMENTATION SEARCH IS OFF BY DEFAULT, AND OFF MEANS BIT-IDENTICAL.
    ///
    /// It is a measured negative (nothing separated on 16 of 17 corpus instances, one cut
    /// displaced on `gen`), so it ships off — and "off" has to mean the historical derivation runs
    /// alone, not the historical derivation plus a tie-break. Same models as the validity guard,
    /// compared cut for cut.
    #[test]
    fn complementation_search_off_is_the_historical_family() {
        let mut seed = 0x5EED_2026_u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };
        for _ in 0..120 {
            let mut m = Model::new();
            let cols: Vec<Col> = (0..4)
                .map(|j| {
                    if j == 3 {
                        m.add_col(0.0, 4.0)
                    } else {
                        m.add_int_col(0.0, 4.0)
                    }
                })
                .collect();
            for _ in 0..2 {
                let a: Vec<f64> = (0..4).map(|_| (rnd().rem_euclid(9) - 4) as f64).collect();
                if a.iter().all(|&v| v == 0.0) {
                    continue;
                }
                let hi = rnd().rem_euclid(11) as f64;
                let lo = hi - (1 + rnd().rem_euclid(9)) as f64;
                let terms: Vec<_> = cols
                    .iter()
                    .zip(&a)
                    .filter(|(_, &v)| v != 0.0)
                    .map(|(&c, &v)| (c, v))
                    .collect();
                m.add_row(lo, hi, &terms);
            }
            m.set_objective(&[(cols[0], 1.0)], Sense::Minimize);
            let x: Vec<f64> = (0..4).map(|_| rnd().rem_euclid(40) as f64 / 10.0).collect();
            let off = knap_scope(false, || separate_mir(&m, &x, m.num_rows(), 8));
            let dflt = separate_mir(&m, &x, m.num_rows(), 8);
            assert_eq!(off.len(), dflt.len(), "default arm changed the cut count");
            for (a, b) in off.iter().zip(&dflt) {
                assert_eq!(a.coeffs, b.coeffs);
                assert_eq!(a.ub.to_bits(), b.ub.to_bits());
                assert_eq!(a.lb.to_bits(), b.lb.to_bits());
            }
        }
    }

    mod chain;

    /// THE STRENGTHENED COEFFICIENT IS THE ONE LETCHFORD & LODI DERIVE, AND IT IS STRONGER THAN MIR.
    ///
    /// Their worked Example 1 is `P = {x ∈ Z²₊ : 6x₁ + 4x₂ <= 9}` with the CG cut `x₁ <= 1`, and the
    /// strong CG cut `2x₁ + x₂ <= 2`. Separating that row at the LP vertex `x = (3/2, 0)` — which the
    /// strong CG cut cuts off (`2·3/2 = 3 > 2`) and the CG cut does not — the c-MIR scaling that wins
    /// is `δ = 6`, giving the stored cut `x₁ + ½x₂ <= 1`, i.e. exactly `2x₁ + x₂ <= 2`. Plain MIR on
    /// the same row and scaling gives `x₁ + ⅓x₂ <= 1` (`3x₁ + x₂ <= 3`), a WEAKER coefficient on
    /// `x₂` — so this pins both the correctness of the strengthened rule and that it strictly
    /// strengthens MIR here.
    #[test]
    fn strongcg_reproduces_letchford_lodi_example_1() {
        let mut m = Model::new();
        let x1 = m.add_int_col(0.0, 5.0);
        let x2 = m.add_int_col(0.0, 5.0);
        // A continuous column not in the row, so the family's all-integral self-gate lets the row
        // through; the derivation on `6x₁+4x₂<=9` is untouched by it.
        let _z = m.add_col(0.0, 1.0);
        m.add_row(f64::NEG_INFINITY, 9.0, &[(x1, 6.0), (x2, 4.0)]);
        m.set_objective(&[(x1, 1.0)], Sense::Maximize);
        let x = vec![1.5, 0.0, 0.0]; // the LP vertex the cut must remove

        let scg = separate_strongcg(&m, &x, m.num_rows(), cuts_per_round());
        // The deepest strong CG cut is `x₁ + ½x₂ <= 1` (≡ `2x₁ + x₂ <= 2`): normalise by the RHS.
        let hit = scg.iter().find(|c| {
            let a1 = c
                .coeffs
                .iter()
                .find(|&&(col, _)| col == x1)
                .map_or(0.0, |&(_, a)| a);
            let a2 = c
                .coeffs
                .iter()
                .find(|&&(col, _)| col == x2)
                .map_or(0.0, |&(_, a)| a);
            c.ub.is_finite()
                && c.ub > 0.0
                && (a1 / c.ub - 1.0).abs() < 1e-9
                && (a2 / c.ub - 0.5).abs() < 1e-9
        });
        assert!(
            hit.is_some(),
            "strong CG did not reproduce Example 1's 2x1+x2<=2; got {:?}",
            scg.iter()
                .map(|c| (c.coeffs.clone(), c.ub))
                .collect::<Vec<_>>()
        );
        // It cuts the vertex off, and by more than MIR would on `x₂`.
        let c = hit.unwrap();
        assert!(violation(c, &x) > MIN_VIOLATION);
        let mir = separate_mir(&m, &x, m.num_rows(), cuts_per_round());
        // MIR's cut on this row has an `x₂` coefficient of ⅓·rhs, strictly less than strong CG's ½.
        for cm in &mir {
            let a1 = cm
                .coeffs
                .iter()
                .find(|&&(col, _)| col == x1)
                .map_or(0.0, |&(_, a)| a);
            let a2 = cm
                .coeffs
                .iter()
                .find(|&&(col, _)| col == x2)
                .map_or(0.0, |&(_, a)| a);
            if cm.ub.is_finite() && cm.ub > 0.0 && (a1 / cm.ub - 1.0).abs() < 1e-9 {
                assert!(
                    a2 / cm.ub < 0.5 - 1e-9,
                    "MIR unexpectedly matched strong CG's strengthened x2 coefficient"
                );
            }
        }
    }

    /// The strengthened family must actually SEPARATE where it should — a guard that never fires
    /// guards nothing. An integer row that lands fractional, with a continuous column present so the
    /// self-gate lets the family run, is the minimal case: strong CG strengthens the integer
    /// coefficients and the point is cut off.
    #[test]
    fn strongcg_separates() {
        let mut m = Model::new();
        let y1 = m.add_int_col(0.0, 5.0);
        let y2 = m.add_int_col(0.0, 5.0);
        let _z = m.add_col(0.0, 1.0); // a continuous column, so the all-integral self-gate opens
        m.add_row(f64::NEG_INFINITY, 7.0, &[(y1, 3.0), (y2, 2.0)]);
        m.set_objective(&[(y1, 1.0)], Sense::Maximize);
        let x = vec![7.0 / 3.0, 0.0, 0.0]; // y1 = 7/3 at the LP vertex
        let scg = separate_strongcg(&m, &x, m.num_rows(), cuts_per_round());
        assert!(
            !scg.is_empty(),
            "strong CG separated nothing: the family is inert where it should cut"
        );
        for c in &scg {
            assert!(violation(c, &x) > MIN_VIOLATION);
        }
        // (The `--no-strongcg` kill switch is a single env check at the top of
        // `separate_strongcg`; it is not exercised here because mutating process env would race the
        // other separators' tests running in parallel.)
    }

    /// THE MIR-CLASS SELF-GATE KEYS ON *BINARY*, NOT ON INTEGRALITY.
    ///
    /// `mir_family_inert` used to read "every column is integral", which swept a GENERAL integer
    /// column into the same bin as a 0/1 column on the reasoning that neither is continuous. The
    /// reasoning holds for 0/1 and fails for `{0..u}`: MIR's `⌊a/δ⌋ + (f_j−f)⁺/(1−f)` step
    /// function and the Letchford–Lodi strengthening above it are exactly the tools for a
    /// non-unit coefficient on a bounded integer. On the corpus the old predicate cost haprp its
    /// proof outright — 0 cuts and a 300s BOUND with no incumbent at all, against 24 MIR + 24 SCG
    /// cuts, 96.2% root closure and OPTIMAL in 16.1s. This is that gate at unit scale.
    ///
    /// Three arms, and the last two are a KIND-ONLY control: they hold the rows, the bounds and
    /// the point fixed and differ solely in whether the column was declared `Integer` or
    /// `Binary`. So neither the "it separates" nor the "it separates nothing" half can pass by
    /// accident about the row shape — the gate is reading the column kind and nothing else.
    #[test]
    fn mir_family_gate_admits_general_integers_and_still_excludes_binaries() {
        // ARM 1 — the haprp shape at unit scale: an ALL-INTEGRAL model, no continuous column
        // anywhere, general integer columns with non-unit coefficients. `6x₁ + 4x₂ <= 9` over
        // `{0..5}²` is Letchford–Lodi's Example 1 with the test-only continuous column REMOVED;
        // the historical gate returned `Vec::new()` here without ever looking at the row.
        let mut m = Model::new();
        let x1 = m.add_int_col(0.0, 5.0);
        let x2 = m.add_int_col(0.0, 5.0);
        m.add_row(f64::NEG_INFINITY, 9.0, &[(x1, 6.0), (x2, 4.0)]);
        m.set_objective(&[(x1, 1.0)], Sense::Maximize);
        assert!(
            (0..m.num_cols()).all(|j| m.col_kind(Col(j as u32)).is_integral()),
            "arm 1 must be all-integral or it does not exercise the gate at all"
        );
        let x = vec![1.5, 0.0];
        let mir = separate_mir(&m, &x, m.num_rows(), cuts_per_round());
        let scg = separate_strongcg(&m, &x, m.num_rows(), cuts_per_round());
        assert!(
            !mir.is_empty() && !scg.is_empty(),
            "the MIR class separated nothing on an all-integral model with GENERAL integer \
             columns (mir={} scg={}): the narrowed gate is not in force",
            mir.len(),
            scg.len()
        );
        for c in mir.iter().chain(scg.iter()) {
            assert!(violation(c, &x) > MIN_VIOLATION);
        }

        // ARM 2 / ARM 3 — the kind-only control. `3a + 3b <= 4` at `a = b = 2/3` is a row whose
        // Chvátal-Gomory rounding (`a + b <= 1`) cuts the point off, written twice over columns
        // with IDENTICAL `[0, 1]` bounds: once as `ColKind::Integer` (the shape a presolve
        // tightening of a `{0..u}` column leaves behind) and once as `ColKind::Binary`.
        let build = |binary: bool| {
            let mut m = Model::new();
            let (a, b) = if binary {
                (m.add_binary_col(), m.add_binary_col())
            } else {
                // `add_int_col` classifies `[0, 1]` as Binary, so the general-integer kind has to
                // be taken first and the bounds tightened after — exactly what presolve does.
                let (a, b) = (m.add_int_col(0.0, 2.0), m.add_int_col(0.0, 2.0));
                m.set_col_bounds(a, 0.0, 1.0);
                m.set_col_bounds(b, 0.0, 1.0);
                (a, b)
            };
            m.add_row(f64::NEG_INFINITY, 4.0, &[(a, 3.0), (b, 3.0)]);
            m.set_objective(&[(a, 1.0), (b, 1.0)], Sense::Maximize);
            m
        };
        let pt = vec![2.0 / 3.0, 2.0 / 3.0];
        let m_int = build(false);
        let m_bin = build(true);
        assert_eq!(
            m_int.col_bounds(Col(0)),
            m_bin.col_bounds(Col(0)),
            "the control arms must differ ONLY in column kind"
        );
        let int_cuts = separate_mir(&m_int, &pt, m_int.num_rows(), cuts_per_round());
        assert!(
            !int_cuts.is_empty(),
            "the general-integer control separated nothing, so the binary arm below proves nothing"
        );
        let bin_cuts = separate_mir(&m_bin, &pt, m_bin.num_rows(), cuts_per_round());
        assert!(
            bin_cuts.is_empty(),
            "the MIR class ran on an ALL-BINARY model: the 66 pure-binary corpus instances are \
             no longer bit-for-bit (got {} cuts)",
            bin_cuts.len()
        );
        assert!(
            separate_strongcg(&m_bin, &pt, m_bin.num_rows(), cuts_per_round()).is_empty(),
            "strong CG ran on an ALL-BINARY model"
        );
        assert!(
            separate_mir_agg(&m_bin, &pt, m_bin.num_rows(), cuts_per_round()).is_empty(),
            "aggregated MIR ran on an ALL-BINARY model"
        );
    }

    /// A model with an exact-rational side store must be declined before the
    /// separator reads any f64 proxy row. The exact control keeps this guard
    /// non-vacuous: the same proxy matrix separates before an override exists.
    #[test]
    fn mixing_fails_closed_on_exact_side_store_models() {
        let mut m = Model::new();
        let s = m.add_col(0.0, 20.0);
        let y = m.add_int_col(0.0, 3.0);
        let mut rows = Vec::new();
        for r in 0..12 {
            let (row, proxy_ub) = if r % 2 == 0 {
                (
                    m.add_row(f64::NEG_INFINITY, 1.0, &[(s, -1.0), (y, 3.0)]),
                    1_i64,
                )
            } else {
                (
                    m.add_row(f64::NEG_INFINITY, 2.0, &[(s, -1.0), (y, 4.0)]),
                    2_i64,
                )
            };
            rows.push((row, proxy_ub));
        }
        m.set_objective(&[(y, 1.0)], Sense::Minimize);
        let x = vec![1.25, 0.75];
        assert!(
            !separate_mixing(&m, &x, m.num_rows(), 8).is_empty(),
            "the exact proxy-matrix control must separate"
        );

        // 1 + 2^-53 rounds to the stored f64 proxy 1.0. The true row is
        // marginally looser, so a cut proved only from the proxy is not licensed.
        let eps = BigRational::new(1_i64.into(), 9_007_199_254_740_992_i64.into());
        for (row, proxy_ub) in rows {
            let true_ub = BigRational::from_integer(proxy_ub.into()) + &eps;
            m.record_inexact_row_bound(row, false, true_ub);
        }
        assert!(m.has_inexact_coeffs());
        assert!(!is_mixed_integer_knapsack(&m));
        assert!(
            separate_mixing(&m, &x, m.num_rows(), 8).is_empty(),
            "mixing must fail closed instead of cutting the f64 proxy model"
        );
    }

    /// Exercise the full structural domain admitted by the separator: signed
    /// integer coefficients, continuous coefficients throughout `[−1, 0]`, and
    /// differing continuous subsets. Every integer point uses `s0` alone to
    /// construct an exactly feasible continuous completion; every separated cut
    /// must retain it.
    #[test]
    fn mixing_cuts_cover_signed_weighted_and_subset_rows() {
        const U: i64 = 3;
        const SCAP: f64 = 256.0;
        let mut m = Model::new();
        let s: Vec<Col> = (0..3).map(|_| m.add_col(0.0, SCAP)).collect();
        let y: Vec<Col> = (0..3).map(|_| m.add_int_col(0.0, U as f64)).collect();
        let specs = [
            ([1.0, 0.0, 0.0], [3.0, 0.0, 0.0], 1.0),
            ([1.0, 0.0, 0.0], [4.0, 0.0, 0.0], 2.0),
            ([0.5, 0.25, 0.0], [-2.0, 3.0, 0.0], -1.0),
            ([0.25, 0.0, 1.0], [5.0, -1.0, 2.0], 2.0),
            ([0.75, 0.5, 0.0], [-3.0, 0.0, 4.0], 0.0),
            ([1.0, 0.0, 0.25], [2.0, -2.0, 5.0], 3.0),
            ([0.5, 0.75, 0.0], [1.0, 4.0, -1.0], 1.0),
            ([0.25, 0.0, 0.5], [-1.0, 5.0, 3.0], -2.0),
            ([1.0, 0.25, 0.25], [4.0, -3.0, 1.0], 4.0),
            ([0.75, 0.0, 0.5], [3.0, 2.0, -2.0], 0.0),
            ([0.5, 1.0, 0.0], [-2.0, 1.0, 5.0], 2.0),
            ([0.25, 0.5, 1.0], [5.0, -1.0, -3.0], -1.0),
        ];
        for (sw, ya, b) in specs {
            let mut terms = Vec::new();
            for k in 0..s.len() {
                if sw[k] != 0.0 {
                    terms.push((s[k], -sw[k]));
                }
            }
            for j in 0..y.len() {
                if ya[j] != 0.0 {
                    terms.push((y[j], ya[j]));
                }
            }
            m.add_row(f64::NEG_INFINITY, b, &terms);
        }
        m.set_objective(&[(y[0], 1.0)], Sense::Minimize);

        // The first two rows expose the deterministic violated chain s0 >= 2*y0.
        let x = vec![1.25, 0.0, 0.0, 0.75, 0.0, 0.0];
        let cuts = separate_mixing(&m, &x, m.num_rows(), 8);
        assert!(!cuts.is_empty(), "the broad structural guard is vacuous");

        for code in 0..(U + 1).pow(y.len() as u32) {
            let mut t = code;
            let mut p = vec![0.0f64; s.len() + y.len()];
            for &yc in &y {
                p[yc.index()] = (t % (U + 1)) as f64;
                t /= U + 1;
            }
            // Every row includes s0 with weight sw[0] > 0. Set the optional
            // continuous columns to zero and choose the least s0 that satisfies
            // all rows under that completion.
            let mut s0 = 0.0f64;
            for (sw, ya, b) in specs {
                let rho: f64 = (0..y.len()).map(|j| ya[j] * p[y[j].index()]).sum::<f64>() - b;
                s0 = s0.max(rho / sw[0]);
            }
            assert!(s0 <= SCAP);
            p[s[0].index()] = s0;

            for (sw, ya, b) in specs {
                let act = (0..s.len()).map(|k| -sw[k] * p[s[k].index()]).sum::<f64>()
                    + (0..y.len()).map(|j| ya[j] * p[y[j].index()]).sum::<f64>();
                assert!(act <= b + 1e-9, "constructed completion is infeasible");
            }
            for cut in &cuts {
                let act: f64 = cut
                    .coeffs
                    .iter()
                    .map(|&(col, cf)| cf * p[col.index()])
                    .sum();
                assert!(
                    act >= cut.lb - 1e-6,
                    "mixing cut deleted signed/weighted feasible point {p:?}: {act} < {}",
                    cut.lb
                );
            }
        }
    }

    /// THE MIXING FAMILY OWES THE SAME GUARANTEE, and its own failure modes are the two invariants
    /// the derivation leans on: the ordered subset MUST be sorted by INCREASING `μ` (a wrong order
    /// makes a telescoping weight `μ_{l+1} − μ_l` NEGATIVE and the cut invalid), and the aggregate
    /// continuous `S` must genuinely lower-bound `ρ_i(x)` for every row it is built from (so the
    /// continuous coefficients must be in `[−1,0]` and `S` the sum of `s_k >= 0`).
    ///
    /// Random mixing sets carrying exactly that structure — a handful of shared continuous columns
    /// with coefficient `−1` across many `<=` knapsack rows over small integer columns — with every
    /// integer point enumerated and the continuous columns pinned to the MINIMAL feasible `S` (the
    /// binding case for a `>=` cut whose continuous coefficients are all `+1`). If any cut deleted a
    /// feasible integer point, this catches it.
    #[test]
    fn mixing_cuts_never_remove_an_integer_point() {
        let mut seed = 0x31C1_2026_u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };
        const U: i64 = 3; // integer column range [0, U]
        const NROWS: usize = 12; // >= 10 so `is_mixed_integer_knapsack` fires
        const NY: usize = 3; // integer columns
        const NS: usize = 2; // shared continuous columns
        const SCAP: f64 = 60.0; // continuous upper bound (>= any achievable S)
        let mut total_cuts = 0usize;

        for case in 0..400 {
            let mut m = Model::new();
            // Continuous columns first, then integer — the mixing separator sums the continuous
            // that lower-bound the rows into `S`.
            let s: Vec<Col> = (0..NS).map(|_| m.add_col(0.0, SCAP)).collect();
            let y: Vec<Col> = (0..NY).map(|_| m.add_int_col(0.0, U as f64)).collect();
            let ncols = NS + NY;

            // Each row: `Σ_j a_ij y_j − Σ_k s_k <= b_i`, `a` small positive, `b` a small constant so
            // `ρ_i(y) = Σ a y − b` is sometimes positive (a non-trivial mixing set).
            let mut rows: Vec<(Vec<f64>, f64)> = Vec::new(); // (dense coeffs over all cols, rhs)
            for _ in 0..NROWS {
                let mut dense = vec![0.0f64; ncols];
                for sc in &s {
                    dense[sc.index()] = -1.0;
                }
                let mut terms: Vec<(Col, f64)> = s.iter().map(|&c| (c, -1.0)).collect();
                for (jj, &yc) in y.iter().enumerate() {
                    let a = (1 + rnd().rem_euclid(5)) as f64;
                    dense[yc.index()] = a;
                    terms.push((yc, a));
                    let _ = jj;
                }
                let b = rnd().rem_euclid(9) as f64;
                m.add_row(f64::NEG_INFINITY, b, &terms);
                rows.push((dense, b));
            }
            m.set_objective(&[(y[0], 1.0)], Sense::Minimize);

            // Separate from a point with the continuous columns pinned LOW (so `S* = 0` and any
            // cut with a positive right-hand side value is violated) and the integers fractional.
            let mut x = vec![0.0f64; ncols];
            for &yc in &y {
                x[yc.index()] = rnd().rem_euclid(U * 10) as f64 / 10.0;
            }
            let cuts = separate_mixing(&m, &x, m.num_rows(), 8);
            total_cuts += cuts.len();
            if cuts.is_empty() {
                continue;
            }

            // Enumerate every integer y; pin the continuous columns to the MINIMAL feasible S.
            for code in 0..(U + 1).pow(NY as u32) {
                let mut t = code;
                let mut p = vec![0.0f64; ncols];
                for &yc in &y {
                    p[yc.index()] = (t % (U + 1)) as f64;
                    t /= U + 1;
                }
                // Minimal feasible S = max(0, max_i ρ_i(y)); split across the continuous columns.
                let mut s_min = 0.0f64;
                for (dense, b) in &rows {
                    let rho: f64 = y
                        .iter()
                        .map(|&yc| dense[yc.index()] * p[yc.index()])
                        .sum::<f64>()
                        - *b;
                    s_min = s_min.max(rho);
                }
                if s_min > SCAP * NS as f64 {
                    continue; // not representable within the continuous box: skip
                }
                let mut rem = s_min;
                for &sc in &s {
                    let v = rem.min(SCAP);
                    p[sc.index()] = v;
                    rem -= v;
                }
                // Confirm the point is feasible for every row (it is, by construction of s_min).
                let feasible = rows.iter().all(|(dense, b)| {
                    let act: f64 = (0..ncols).map(|k| dense[k] * p[k]).sum();
                    act <= *b + 1e-7
                });
                if !feasible {
                    continue;
                }
                for cut in &cuts {
                    let act: f64 = cut
                        .coeffs
                        .iter()
                        .map(|&(col, cf)| cf * p[col.index()])
                        .sum();
                    assert!(
                        act >= cut.lb - 1e-6,
                        "case {case}: a mixing cut deleted the feasible point {p:?} -- \
                         activity {act} < lb {}",
                        cut.lb
                    );
                }
            }
        }
        // A guard that never sees a cut guards nothing.
        assert!(
            total_cuts > 0,
            "no mixing cut was ever separated: the guard is vacuous"
        );
    }

    /// THE VIOLATION SCREEN CHANGES NOTHING IT RETURNS.
    ///
    /// `best_over_deltas` skips exact-rational derivations the `f64` screen can prove cannot end up
    /// in the answer (see `ScreenRow`). "Cannot" is a claim about every row of every model, not
    /// about the corpus it was measured on, so it is checked here the only way it can be: run BOTH
    /// paths on random models — including the fixed-charge VUB structure, which is what puts a
    /// continuous slack and a dragged-in binary into the same substituted row — and require the
    /// returned cuts to be identical to the BIT.
    ///
    /// A screen that is merely a good heuristic passes the validity guard above (it never invents
    /// a cut) and fails this one. That is the distinction worth a test.
    #[test]
    fn the_violation_screen_is_bit_identical() {
        let mut seed = 0x5EED_2026_u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };
        const HI: i64 = 5;
        let mut seen_cuts = 0usize;
        let mut seen_skips = 0usize;

        for case in 0..600 {
            let mut m = Model::new();
            let cols: Vec<Col> = (0..3)
                .map(|j| {
                    if j % 3 == 2 {
                        m.add_col(0.0, HI as f64)
                    } else {
                        m.add_int_col(0.0, HI as f64)
                    }
                })
                .collect();
            let sw = m.add_binary_col();
            let flow = m.add_col(0.0, HI as f64);
            m.add_row(f64::NEG_INFINITY, 0.0, &[(flow, 1.0), (sw, -(HI as f64))]);
            let cols: Vec<Col> = cols.into_iter().chain([sw, flow]).collect();
            let n = cols.len();
            for _ in 0..3 {
                let a: Vec<f64> = (0..n).map(|_| (rnd() % 13 - 6) as f64).collect();
                if a.iter().all(|&v| v == 0.0) {
                    continue;
                }
                let hi = (rnd() % 21) as f64;
                let lo = hi - (1 + rnd() % 17) as f64;
                let terms: Vec<_> = cols
                    .iter()
                    .zip(&a)
                    .filter(|(_, &v)| v != 0.0)
                    .map(|(&c, &v)| (c, v))
                    .collect();
                m.add_row(lo, hi, &terms);
            }
            m.set_objective(&[(cols[0], 1.0)], Sense::Minimize);
            // DELIBERATELY NOT CLAMPED TO THE COLUMN BOX. A separation point outside a column's
            // bounds gives that column a NEGATIVE displacement, and a negative displacement flips
            // which end of a step-function coefficient the screen must take. Rounding strong CG's
            // `⌈·⌉` the same way in both directions was a real defect this generator caught in 16
            // cases out of 600; clamping the point would have hidden it. `box_excess` in
            // `ScreenRow` prices the other half of the same situation.
            let x: Vec<f64> = (0..n).map(|_| (rnd() % 50) as f64 / 10.0).collect();

            for family in [0u8, 1] {
                let run = |on: bool| {
                    screen_scope(on, || {
                        if family == 0 {
                            separate_mir(&m, &x, m.num_rows(), cuts_per_round())
                        } else {
                            separate_strongcg(&m, &x, m.num_rows(), cuts_per_round())
                        }
                    })
                };
                let with = run(true);
                let without = run(false);
                seen_cuts += without.len();
                assert_eq!(
                    with.len(),
                    without.len(),
                    "case {case} family {family}: the screen changed the cut COUNT"
                );
                for (i, (a, b)) in with.iter().zip(&without).enumerate() {
                    assert_eq!(
                        a.ub.to_bits(),
                        b.ub.to_bits(),
                        "case {case} family {family} cut {i}: right-hand side moved"
                    );
                    assert_eq!(a.lb.to_bits(), b.lb.to_bits());
                    assert_eq!(a.coeffs.len(), b.coeffs.len());
                    for (&(ca, va), &(cb, vb)) in a.coeffs.iter().zip(&b.coeffs) {
                        assert_eq!(ca, cb);
                        assert_eq!(
                            va.to_bits(),
                            vb.to_bits(),
                            "case {case} family {family} cut {i}: coefficient moved"
                        );
                    }
                }
            }
            // ...and the screen must actually be DOING something on this family of models, or the
            // equality above is the equality of two identical code paths.
            let before = crate::sepstat::SCREEN_SKIP.load(std::sync::atomic::Ordering::Relaxed);
            screen_scope(true, || {
                separate_mir(&m, &x, m.num_rows(), cuts_per_round());
            });
            seen_skips += (crate::sepstat::SCREEN_SKIP.load(std::sync::atomic::Ordering::Relaxed)
                - before) as usize;
        }
        assert!(
            seen_cuts > 0,
            "the screen guard never saw a cut: it is vacuous"
        );
        // `SCREEN_SKIP` only moves when `--sepstat` is set, so this half of the guard is
        // only meaningful under it -- assert it exactly then.
        if crate::sepstat::on() {
            assert!(
                seen_skips > 0,
                "the screen skipped nothing on 600 random models: it is inert, \
                 so the equality above proves nothing"
            );
        }
    }
}

/// Separate MIR cuts from the TABLEAU, with the row multipliers computed in floats.
///
/// This is GMI's cut, reached without GMI's price. GMI derives its tableau row from an EXACTLY
/// factored basis -- an `O(m³)` rational LU -- and that, measured, is what makes a cut loop
/// unaffordable: on rout separation costs 1.94s in round zero, 9.13s in round one and 16.36s in
/// round two, while the LP it feeds solves in hundredths of a second throughout. The loop is
/// separation-bound, and it dies after three rounds.
///
/// But the multipliers do not have to be exact. In computational form every point of the model
/// satisfies `M z = 0` (with `z = (x, s)`), so `uᵀ M z = 0` is an exact equation for ANY rational
/// `u` whatsoever -- the multipliers are free, only the COMBINATION has to be exact. So take `u`
/// from a float BTRAN (`O(nnz)`), snap it to a coarse dyadic grid to keep the denominators small,
/// and form `Σ_j (u·M_j) z_j = 0` in exact rationals. Then round it.
///
/// The price of approximate `u` is that the other basic variables no longer drop out exactly: they
/// arrive with coefficients around 1e-12 instead of zero. MIR absorbs them -- they are substituted
/// to a bound like anything else, and at that magnitude they contribute nothing to the cut. The
/// derivation stays exact; only its sharpness is at risk, never its validity.
pub(crate) fn separate_mir_tableau(model: &Model, lp: &FloatLp, cand: &Candidate) -> Vec<Cut> {
    let m = lp.rows();
    if m == 0 {
        return Vec::new();
    }
    let is_int = |j: usize| -> bool {
        j < lp.n && !matches!(model.col_kind(Col(j as u32)), ColKind::Continuous)
    };
    // The basis rows worth cutting on: a structural INTEGER column sitting fractional.
    let mut want: Vec<usize> = Vec::new();
    for (i, &b) in cand.basis.iter().enumerate() {
        if !is_int(b) {
            continue;
        }
        let v = cand.values[b];
        let f = v - v.floor();
        if (FRAC_TOL..=1.0 - FRAC_TOL).contains(&f) {
            want.push(i);
        }
        if want.len() >= cuts_per_round() * 2 {
            break;
        }
    }
    if want.is_empty() {
        return Vec::new();
    }
    let Some(us) = lp.btran_rows(cand, &want) else {
        return Vec::new();
    };

    let mut cuts: Vec<Cut> = Vec::new();
    for u in &us {
        if cuts.len() >= cuts_per_round() {
            break;
        }
        // Snap the multipliers: exactness is required of the COMBINATION, not of `u`, and a raw
        // f64 turns into a rational with a 2^60 denominator that poisons every product after it.
        let uq: Vec<BigRational> = u.iter().map(|&v| snap_dyadic(v)).collect();
        if uq.iter().all(Zero::is_zero) {
            continue;
        }

        // The exact equation `Σ_j (u·M_j) z_j = 0`, over structurals AND slacks.
        let mut terms: Vec<(usize, BigRational)> = Vec::new();
        for j in 0..lp.n {
            let mut c = BigRational::zero();
            for (r, a) in lp.column(j) {
                if uq[r].is_zero() {
                    continue;
                }
                let Some(a) = exact(a) else { return Vec::new() };
                c += a * &uq[r];
            }
            if !c.is_zero() {
                terms.push((j, c));
            }
        }
        for (r, uqr) in uq.iter().enumerate() {
            if !uqr.is_zero() {
                terms.push((lp.n + r, -uqr.clone())); // the slack's column is -e_r
            }
        }
        if terms.is_empty() {
            continue;
        }

        // An equation gives two inequalities; the useful one is whichever the point breaks.
        for flip in [false, true] {
            let signed: Vec<(usize, BigRational)> = terms
                .iter()
                .map(|(j, c)| (*j, if flip { -c.clone() } else { c.clone() }))
                .collect();
            if let Some(cut) = mir_from_lp_row(model, lp, cand, &signed) {
                cuts.push(cut);
                break;
            }
        }
    }
    cuts
}

/// MIR on the DUAL-WEIGHTED aggregation of the model's rows, at this candidate's duals.
///
/// The tableau families cut a VERTEX: a row of `B⁻¹` prices exactly one basic variable, and the
/// cut it yields is violated at that vertex and, measured on rout's plateau, almost nowhere else
/// (a branch-and-bound frontier is thousands of vertices; killing one per round moves nothing).
/// The dual vector prices the REGION: `u = cand.duals` is the certificate for the node's whole LP
/// bound, so `uᵀ M z = 0` aggregated and MIR-rounded is a rounding argument against the bound
/// itself — if it separates, it binds on the face the plateau's bound lives on, not at one vertex.
///
/// Validity is the same license as `separate_mir_tableau`: `M z = 0` holds for EVERY point of the
/// model (computational form), so ANY snapped rational `u` gives an exact equation, and
/// `mir_from_lp_row` bound-substitutes and rounds it exactly. The duals' float noise costs
/// sharpness, never soundness.
pub(crate) fn separate_mir_dual_agg(model: &Model, lp: &FloatLp, cand: &Candidate) -> Vec<Cut> {
    let m = lp.rows();
    if m == 0 || cand.duals.len() < m {
        return Vec::new();
    }
    let uq: Vec<BigRational> = cand.duals.iter().take(m).map(|&v| snap_dyadic(v)).collect();
    if uq.iter().all(Zero::is_zero) {
        return Vec::new();
    }
    let mut terms: Vec<(usize, BigRational)> = Vec::new();
    for j in 0..lp.n {
        let mut c = BigRational::zero();
        for (r, a) in lp.column(j) {
            if uq[r].is_zero() {
                continue;
            }
            let Some(a) = exact(a) else { return Vec::new() };
            c += a * &uq[r];
        }
        if !c.is_zero() {
            terms.push((j, c));
        }
    }
    for (r, uqr) in uq.iter().enumerate() {
        if !uqr.is_zero() {
            terms.push((lp.n + r, -uqr.clone())); // the slack's column is -e_r
        }
    }
    if terms.is_empty() {
        return Vec::new();
    }
    let mut cuts = Vec::new();
    for flip in [false, true] {
        let signed: Vec<(usize, BigRational)> = terms
            .iter()
            .map(|(j, c)| (*j, if flip { -c.clone() } else { c.clone() }))
            .collect();
        if let Some(cut) = mir_from_lp_row(model, lp, cand, &signed) {
            cuts.push(cut);
        }
    }
    cuts
}

/// Round the given `<= 0` inequality over `(x, s)` and fold the slacks back out.
fn mir_from_lp_row(
    model: &Model,
    lp: &FloatLp,
    cand: &Candidate,
    terms: &[(usize, BigRational)],
) -> Option<Cut> {
    // Bound-substitute every variable to its NEARER bound -- structurals from the model, slacks
    // from the row they belong to. A variable with no finite bound on the side it must be measured
    // from cannot be shifted to zero, and the derivation does not hold without it.
    let mut subs: Vec<(usize, BigRational, bool, BigRational, bool)> = Vec::new(); // j, a, compl, bound, integral
    let mut b = BigRational::zero(); // rhs, starting from `<= 0`
    for (j, a) in terms {
        let (lo, up) = (lp.lower[*j], lp.upper[*j]);
        let xs = cand.values[*j];
        let d_lo = if lo.is_finite() {
            xs - lo
        } else {
            f64::INFINITY
        };
        let d_up = if up.is_finite() {
            up - xs
        } else {
            f64::INFINITY
        };
        let compl = d_up < d_lo;
        let bnd_f = if compl { up } else { lo };
        if !bnd_f.is_finite() {
            return None;
        }
        let bnd = exact(bnd_f)?;
        b -= a * &bnd;
        let at = if compl { -a.clone() } else { a.clone() };
        let integral = *j < lp.n && !matches!(model.col_kind(Col(*j as u32)), ColKind::Continuous);
        subs.push((*j, at, compl, bnd, integral));
    }

    // MIR, with delta = 1.
    let one = BigRational::one();
    let fb = &b - b.floor();
    if fb.is_zero() {
        return None;
    }
    let inv = &one / (&one - &fb);
    let mut ct: Vec<(usize, BigRational)> = Vec::new();
    for (j, a, _, _, integral) in &subs {
        let c = if *integral {
            let fl = a.floor();
            let fj = a - &fl;
            if fj > fb {
                fl + (&fj - &fb) * &inv
            } else {
                fl
            }
        } else if *a < BigRational::zero() {
            a * &inv
        } else {
            BigRational::zero()
        };
        if !c.is_zero() {
            ct.push((*j, c));
        }
    }
    if ct.is_empty() {
        return None;
    }
    let mut rhs = b.floor();

    // Map the displacements back to `(x, s)`.
    let mut zc: std::collections::HashMap<usize, BigRational> = std::collections::HashMap::new();
    for (j, c) in ct {
        let (_, _, compl, bnd, _) = subs.iter().find(|(k, ..)| *k == j)?;
        if *compl {
            rhs -= &c * bnd;
            *zc.entry(j).or_insert_with(BigRational::zero) -= c;
        } else {
            rhs += &c * bnd;
            *zc.entry(j).or_insert_with(BigRational::zero) += c;
        }
    }

    // Fold the slacks out: `s_r = Σ_j a_rj x_j`.
    let mut xc: std::collections::HashMap<usize, BigRational> = std::collections::HashMap::new();
    for (j, c) in zc {
        if j < lp.n {
            *xc.entry(j).or_insert_with(BigRational::zero) += c;
        } else {
            let r = j - lp.n;
            for (k, a) in lp.row(r) {
                let a = exact(a)?;
                *xc.entry(k).or_insert_with(BigRational::zero) += &c * a;
            }
        }
    }

    // To f64, paying for the rounding in the right-hand side. A `<=` store, like the other two
    // MIR roundings.
    let mut damage = BigRational::zero();
    let mut out: Vec<(Col, f64)> = Vec::new();
    for (j, c) in xc {
        if c.is_zero() {
            continue;
        }
        let col = Col(j as u32);
        let (cf, cost) = coef_to_f64(model, col, &c, CutSide::Le)?;
        damage += cost;
        if cf != 0.0 {
            out.push((col, cf));
        }
    }
    if out.is_empty() {
        return None;
    }
    let relaxed = &rhs + &damage;
    let ub0 = relaxed.to_f64()?;
    if !ub0.is_finite() {
        return None;
    }
    let ub = if exact(ub0)? < relaxed {
        next_up(ub0)
    } else {
        ub0
    };

    let cut = Cut {
        coeffs: out,
        lb: f64::NEG_INFINITY,
        ub,
    };
    // Only worth a row if the point actually breaks it.
    let act: f64 = cut
        .coeffs
        .iter()
        .map(|&(c, a)| a * cand.values[c.index()])
        .sum();
    let v = act - cut.ub;
    if v <= min_violation() {
        charge_min_violation(&cut, v);
        return None;
    }
    Some(cut)
}

/// Snap to a multiple of `2^-20`: exactness is required of the COMBINATION, not of the multipliers,
/// and a raw `f64` becomes a rational with a `2^60` denominator that poisons every product after it.
fn snap_dyadic(v: f64) -> BigRational {
    const SCALE: i64 = 1 << 20;
    if !v.is_finite() {
        return BigRational::zero();
    }
    let n = (v * SCALE as f64).round();
    if n.abs() > 1e15 {
        return BigRational::zero();
    }
    BigRational::new((n as i64).into(), SCALE.into())
}

/// The VARIABLE upper bounds of a model: `x_j <= u_j · y_j`, `y_j` binary.
///
/// This is the structure a fixed-charge model IS -- a continuous flow that only exists if a binary
/// switch is on -- and it is the structure MIR cannot see while it substitutes continuous columns
/// to their CONSTANT bounds. `x_j <= 40` says nothing the relaxation does not already know. But
///
/// ```text
///   x_j = u_j·y_j − s_j ,      s_j >= 0
/// ```
///
/// is an exact rewriting (the row itself guarantees `s_j >= 0`), and it puts the BINARY into the
/// row. MIR then rounds against `y_j`, and what comes out is a flow-cover-class inequality: the
/// family that rout and qnet1 are actually made of, and the reason GMI saturates 8.7% into their
/// gap while HiGHS closes 99.9% of it.
fn variable_upper_bounds(model: &Model) -> std::collections::HashMap<usize, (BigRational, usize)> {
    let mut vubs = std::collections::HashMap::new();
    for r in 0..model.num_rows() {
        let (coeffs, lb, ub) = model.row(Row(r as u32));
        // `a·x + c·y <= ub` with exactly two columns, `ub` finite.
        if coeffs.len() != 2 || !ub.is_finite() {
            continue;
        }
        for (p, q) in [(0usize, 1usize), (1, 0)] {
            let (cx, ax) = coeffs[p];
            let (cy, ay) = coeffs[q];
            let (x, y) = (cx as usize, cy as usize);
            // THE BOUNDING COLUMN MUST BE BINARY. THE BOUNDED ONE MAY BE ANYTHING.
            //
            // This used to demand that `x` be Continuous, and that single word cost qnet1 its cut
            // family. qnet1 has 168 rows of exactly the shape `56·x0 - 56·x1257 <= 0` -- textbook
            // `x <= u·y` -- and every one of them was thrown away because `x` is declared Binary or
            // Integer rather than Continuous. The detector reported ZERO variable upper bounds on a
            // fixed-charge network built out of nothing else, and I believed it, and went looking
            // for the missing bound in the wrong place.
            //
            // The bounded column's KIND is irrelevant to the derivation. All the VUB substitution
            // needs is `s = u·y - x >= 0`, which the row itself asserts whatever `x` is declared to
            // be; MIR then treats `s` as continuous, and treating an integer `s` as continuous is a
            // RELAXATION -- it weakens the cut, it cannot invalidate it. Only `y` must really be
            // binary, because the fixed-charge argument turns on `y in {0,1}`.
            let ky = model.col_kind(Col(cy));
            if x == y || !matches!(ky, ColKind::Binary) {
                continue;
            }
            // Normalise to `x <= u·y`: need a_x > 0, a_y < 0, and the row's `ub` at zero.
            if ax <= 0.0 || ay >= 0.0 || ub.abs() > 1e-9 || lb.is_finite() && lb > f64::NEG_INFINITY
            {
                // A range row would need both sides honoured; only a pure `<= 0` is this shape.
                if !(ax > 0.0 && ay < 0.0 && ub.abs() <= 1e-9 && !lb.is_finite()) {
                    continue;
                }
            }
            let (Some(ax), Some(ay)) = (exact(ax), exact(ay)) else {
                continue;
            };
            let u = -(&ay / &ax); // x <= u·y
            if u.is_positive() {
                vubs.insert(x, (u, y));
            }
        }
    }
    vubs
}

/// FLOW COVER CUTS — the family a fixed-charge network is actually made of.
///
/// GMI is read off the tableau and MIR off a single row, and on rout both of them SATURATE: the
/// root bound goes 981.86 -> ~990 and stops, against an optimum of 1077.56, and no budget of either
/// moves it further. That is not a tuning problem, it is a language problem. Neither family can say
/// the thing rout's structure actually implies.
///
/// The structure is the single-node flow set. A capacity row
///
/// ```text
///     Σ_{j∈N} a_j·x_j  ≤  b,        0 ≤ x_j ≤ u_j·y_j,   y_j ∈ {0,1}
/// ```
///
/// says the flow into a node is bounded, and each arc `j` can only carry flow if its switch `y_j`
/// is on. Write `m_j = a_j·u_j` for the most arc `j` can carry. Pick a set `C` of arcs whose
/// capacities OVERSHOOT the bound -- `λ = Σ_{j∈C} m_j − b > 0`, a "cover", because they cannot all
/// run full. Then for every integer point:
///
/// ```text
///     Σ_{j∈C} a_j·x_j  +  Σ_{j∈C} (m_j − λ)⁺·(1 − y_j)  ≤  b
/// ```
///
/// The second term is what GMI and MIR cannot express: it charges for every arc that is switched
/// OFF. Turning an arc off does not merely zero its flow, it forfeits capacity the cover was
/// counting on, and the inequality makes the rest of the cover pay for it.
///
/// Why it holds. Let `T = {j ∈ C : y_j = 0}`, so `x_j = 0` for `j ∈ T` and the left side is
/// `Σ_{C∖T} x_j + Σ_T (m_j − λ)⁺`. Write `M_T = Σ_T m_j`.
///   * If `M_T < λ`: every `m_j ≤ M_T < λ`, so every `(m_j − λ)⁺ = 0`, and the left side is just
///     `Σ_{C∖T} a_j·x_j ≤ b` -- which is the row.
///   * If `M_T ≥ λ`: capacity bounds the flow, `Σ_{C∖T} a_j·x_j ≤ Σ_{C∖T} m_j = b + λ − M_T`, so it
///     suffices that `Σ_T [m_j − (m_j − λ)⁺] ≥ λ`, i.e. `Σ_T min(m_j, λ) ≥ λ`. If some `m_j ≥ λ`
///     that term alone is `λ`; otherwise every `min` is `m_j` and the sum is `M_T ≥ λ`. Either way.
///
/// So validity needs `x_j ≥ 0`, a VUB per member of `C`, and care with the terms NOT in `C`: a
/// positive one may simply be dropped (`a_j·x_j ≥ 0` only helps), but a NEGATIVE one is holding the
/// row down and dropping it must be paid for out of `b`.
///
/// ⚠ AND IT SEPARATES NOTHING ON ROUT, WHICH IS THE INSTANCE IT WAS WRITTEN FOR. The reason is a
/// PROOF, not a tuning failure, and it is worth writing down so nobody pays for this family twice.
///
/// rout has 230 variable upper bounds, and its VUB'd columns appear in exactly one kind of row: the
/// flow-CONSERVATION equalities (42 columns, 13 arcs in, 11 arcs out, `lb = ub = 0`). Its capacity
/// rows (63 columns, `<= 625`) contain no VUB'd column at all. So the only rows this family can even
/// look at have `b = 0` -- and on `b = 0`,
///
/// ```text
///     λ = Σ_{j∈C} m_j − b = Σ_{j∈C} m_j  ≥  m_k   for every k ∈ C
/// ```
///
/// so EVERY `(m_j − λ)⁺` is zero, every switch term vanishes, and the cut degenerates into the row it
/// came from. Measured exactly that: 370 covers found, best violation 0.0000. A flow cover has
/// something to say only about a row with real CAPACITY on its right-hand side; a conservation row
/// has none, and no choice of cover changes that.
///
/// To reach rout the single-node relaxation has to be BUILT rather than found -- aggregate a
/// conservation row with the capacity row that bounds its arcs, and separate on the aggregate. That
/// is the next piece of work, and note that row aggregation for MIR was tried and made things worse
/// (see `Sub`), so it needs to be done for a reason and measured on its own.
pub(crate) fn separate_flow_cover(model: &Model, x: &[f64], n_rows: usize) -> Vec<Cut> {
    let vubs = variable_upper_bounds(model);
    if vubs.is_empty() {
        return Vec::new(); // no `x <= u·y` anywhere: this family has nothing to say
    }

    let mut cuts: Vec<Cut> = Vec::new();
    for r in 0..n_rows.min(model.num_rows()) {
        if cuts.len() >= cuts_per_round() {
            break;
        }
        let (coeffs, lb, ub) = model.row(Row(r as u32));
        // Both orientations: `a·x <= ub` as it stands, and `-a·x <= -lb` for the other side.
        for (sign, rhs) in [(1.0f64, ub), (-1.0f64, lb)] {
            if !rhs.is_finite() || coeffs.len() < 2 {
                continue;
            }
            let Some(cut) = flow_cover_from_row(model, x, coeffs, sign, sign * rhs, &vubs) else {
                continue;
            };
            if clears_min_violation(&cut, x) {
                cuts.push(cut);
                break;
            }
        }
    }
    cuts
}

fn flow_cover_from_row(
    model: &Model,
    x: &[f64],
    coeffs: &[(u32, f64)],
    sign: f64,
    rhs: f64,
    vubs: &std::collections::HashMap<usize, (BigRational, usize)>,
) -> Option<Cut> {
    // The right-hand side, which pays only for what it MUST -- see the out-arc note below.
    let b = exact(rhs)?;

    struct Arc {
        j: usize,
        y: usize,
        a: BigRational,
        m: BigRational, // |a_j| · u_j -- the most this arc can carry
    }
    let mut arcs: Vec<Arc> = Vec::new(); // in-arcs: a_j > 0, with a VUB. The cover comes from here.
    let mut out: Vec<Arc> = Vec::new(); // out-arcs: a_j < 0, with a VUB. These stay as `y` terms.

    for &(c, raw) in coeffs {
        let j = c as usize;
        let a = exact(sign * raw)?;
        if a.is_zero() {
            continue;
        }
        let (lo, _up) = model.col_bounds(Col(c));
        // The derivation is written for `x >= 0`. A column with a nonzero lower bound would need
        // shifting, and a free one cannot be bounded at all -- leave those rows to MIR.
        if lo != 0.0 {
            return None;
        }
        match (a.is_positive(), vubs.get(&j)) {
            // An in-arc: a candidate for the cover.
            (true, Some((u, yj))) if *yj != j => arcs.push(Arc {
                j,
                y: *yj,
                a: a.clone(),
                m: &a * u,
            }),
            // Positive, but no switch to charge: `a_j·x_j >= 0`, so dropping it only makes the left
            // side smaller. Free.
            (true, _) => {}
            // AN OUT-ARC. KEEP IT EXACTLY AS IT IS. This is what the simple cover threw away, and
            // throwing it away is what made this family useless on rout.
            //
            // A negative term holds the row down, so REMOVING it lets the left side grow -- by as
            // much as `|a_j|·u_j`, which the simple cover paid to the right-hand side. On a
            // flow-CONSERVATION row (which is where rout's variable upper bounds actually live: 13
            // arcs in, 11 arcs out) that payment inflates `b` so far that `λ = Σ_C m_j − b` is never
            // positive: no cover exists at all, and 322 row-sides yield nothing.
            //
            // Relaxing the arc to `−m_j·y_j` instead of paying a constant does restore the cover
            // (0 covers -> 300 on rout) and it is still the wrong move: at ANY LP-feasible point
            // `x_j <= m_j·y_j`, so `−m_j·y_j` is always the MORE negative of the two and the cut
            // gives away exactly the violation it was separated for. Measured: 300 covers, best
            // violation 0.0000.
            //
            // The derivation permits any subset of the out-arcs to stay explicit -- the proof only
            // ever uses `x_j >= 0` for them -- so keep them ALL, with their own coefficients. No
            // relaxation, no payment, and no variable upper bound needed on an out-arc at all.
            (false, _) => out.push(Arc {
                j,
                y: usize::MAX, // unused: the arc keeps its own `x` term, not a `y` term
                a: a.clone(),
                m: BigRational::zero(),
            }),
        }
    }
    if arcs.len() < 2 {
        return None;
    }

    // CHOOSE THE COVER. It must overshoot (`Σ_C m_j > b`, or there is nothing to say), and among the
    // covers that do we want the one this point violates hardest. Take the arcs the relaxation is
    // leaning on first, then keep going only while the violation improves.
    let mut order: Vec<usize> = (0..arcs.len()).collect();
    let val = |k: usize, arcs: &Vec<Arc>| -> f64 {
        to_f64(&arcs[k].a) * x.get(arcs[k].j).copied().unwrap_or(0.0)
    };
    order.sort_by(|&p, &q| {
        val(q, &arcs)
            .partial_cmp(&val(p, &arcs))
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    let mut chosen: Vec<usize> = Vec::new();
    let mut cap = BigRational::zero();
    let mut best: Option<(f64, Cut)> = None;

    for &k in &order {
        chosen.push(k);
        cap += &arcs[k].m;
        let lambda = &cap - &b;
        if !lambda.is_positive() {
            continue; // not yet a cover: the capacity still fits inside the bound
        }
        //   Σ_{j∈C} a_j·x_j  −  Σ_{j∈C} (m_j − λ)⁺·y_j  −  Σ_{j∈M} m_j·y_j
        //                                             ≤  b − Σ_{j∈C} (m_j − λ)⁺
        let mut terms: std::collections::HashMap<usize, BigRational> =
            std::collections::HashMap::new();
        let mut rhs = b.clone();
        for &i in &chosen {
            let arc = &arcs[i];
            *terms.entry(arc.j).or_insert_with(BigRational::zero) += &arc.a;
            let excess = &arc.m - &lambda;
            if excess.is_positive() {
                *terms.entry(arc.y).or_insert_with(BigRational::zero) -= &excess;
                rhs -= &excess;
            }
        }
        // Every out-arc, exactly as the row states it.
        for o in &out {
            *terms.entry(o.j).or_insert_with(BigRational::zero) += &o.a;
        }
        let coeffs: Vec<(Col, f64)> = terms
            .into_iter()
            .filter(|(_, v)| !v.is_zero())
            .map(|(j, v)| (Col(j as u32), to_f64(&v)))
            .collect();
        let too_wide = coeffs.len() > MAX_CUT_NNZ_LOCAL;
        if coeffs.is_empty() || too_wide {
            // FORGONE COST — same shape as the aggregated sibling below. The exact `coeffs`/`rhs`
            // pair is fully built, so charging costs one f64 dot product on the refusal branch.
            // `separate_flow_cover` returns ONE cut (the arg-max over cover prefixes), so a wide
            // candidate no deeper than the incumbent cost nothing: charge only the candidates
            // that would have BEEN the returned cut, using the very test two lines down.
            if too_wide {
                let n = coeffs.len() as u64;
                let refused = Cut {
                    coeffs,
                    lb: f64::NEG_INFINITY,
                    ub: to_f64(&rhs),
                };
                let v = violation(&refused, x);
                if v > best.as_ref().map_or(min_violation(), |(bv, _)| *bv) {
                    crate::sepstat::gate_charge(crate::sepstat::GATE_FLOWCOVER_NNZ, n);
                }
            }
            continue;
        }
        let cut = Cut {
            coeffs,
            lb: f64::NEG_INFINITY,
            ub: to_f64(&rhs),
        };
        let v = violation(&cut, x);
        if v > best.as_ref().map_or(min_violation(), |(bv, _)| *bv) {
            best = Some((v, cut));
        }
    }
    best.map(|(_, c)| c)
}

/// A flow cover is naturally sparse (one term per arc in the cover, plus its switch), so this only
/// ever fires on a pathological row.
///
/// MEASURED 2026-08-01 and the sentence above is exactly right: `sepstat::GATE_FLOWCOVER_NNZ` and
/// `GATE_FLOWCOVER_AGG_NNZ` **never fire** over 101 instances (66 across all three corpus tiers
/// plus the 35-instance named set). No pathological row was reached at either site, so both of
/// this constant's uses have an EMPTY excluded population and neither is the "absolute nnz cap"
/// the cause-6 diagnosis is about.
const MAX_CUT_NNZ_LOCAL: usize = 400;

#[cfg(test)]
mod flow_cover_tests {
    use super::*;
    use crate::model::Sense;

    /// A FLOW COVER MUST NOT DELETE AN INTEGER POINT.
    ///
    /// This needs its own model, and the reason is worth stating: the MIR guard's model carries a
    /// single `x <= u·y` pair, and a COVER needs at least two arcs to overshoot with. Adding
    /// `separate_flow_cover` to that test produced no cuts at all -- it passed with the switch term's
    /// sign deliberately flipped, which is the definition of a guard that is not guarding anything.
    ///
    /// The model is a single-node flow set with arcs IN and arcs OUT, because the out-arcs are the
    /// whole difficulty: they are what the cut keeps as `−m_j·y_j` terms rather than paying for as
    /// constants, and the argument that this is sound is the one most likely to be wrong.
    ///
    /// The arcs carry UNIT coefficients on purpose. Enumerating integer points only proves validity
    /// if every vertex of the relaxation is integral, and for `{0 <= x_j <= u_j·y_j,
    /// Σ_in x − Σ_out x <= b}` the constraint matrix is `[I; 1 −1]`, which is totally unimodular, so
    /// it is. Give the arcs general coefficients and the violating point can sit at a fractional
    /// vertex an integer sweep never visits: the test would pass and the cut would still be wrong.
    #[test]
    fn flow_cover_cuts_never_remove_an_integer_point() {
        let mut seed = 0x51DE_2026_u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };

        let mut fired = 0usize;
        for _case in 0..400 {
            const IN: usize = 3;
            const OUT: usize = 2;
            let cin: Vec<i64> = (0..IN).map(|_| 1 + rnd() % 4).collect();
            let cout: Vec<i64> = (0..OUT).map(|_| 1 + rnd() % 3).collect();

            let mut m = Model::new();
            let fin: Vec<Col> = cin.iter().map(|&u| m.add_col(0.0, u as f64)).collect();
            let fout: Vec<Col> = cout.iter().map(|&u| m.add_col(0.0, u as f64)).collect();
            let sin: Vec<Col> = (0..IN).map(|_| m.add_binary_col()).collect();
            let sout: Vec<Col> = (0..OUT).map(|_| m.add_binary_col()).collect();
            // Every arc is gated by its own switch: `x <= u·y`.
            for k in 0..IN {
                m.add_row(
                    f64::NEG_INFINITY,
                    0.0,
                    &[(fin[k], 1.0), (sin[k], -(cin[k] as f64))],
                );
            }
            for k in 0..OUT {
                m.add_row(
                    f64::NEG_INFINITY,
                    0.0,
                    &[(fout[k], 1.0), (sout[k], -(cout[k] as f64))],
                );
            }
            // ...and the node's balance row: what comes in, less what goes out, is bounded.
            let total: i64 = cin.iter().sum();
            let b = 1 + rnd() % total.max(2);
            if b >= total {
                continue; // no cover to find: the in-arcs already fit
            }
            let mut bal: Vec<(Col, f64)> = fin.iter().map(|&c| (c, 1.0)).collect();
            bal.extend(fout.iter().map(|&c| (c, -1.0)));
            m.add_row(f64::NEG_INFINITY, b as f64, &bal);
            m.set_objective(&[(fin[0], 1.0)], Sense::Minimize);

            let n = 2 * (IN + OUT);
            let x: Vec<f64> = (0..n).map(|_| (rnd() % 40) as f64 / 10.0).collect();
            let cuts = separate_flow_cover(&m, &x, m.num_rows());
            fired += cuts.len();

            // Every integer point the MODEL admits must satisfy every cut.
            let caps: Vec<i64> = cin.iter().chain(cout.iter()).copied().collect();
            let flows: Vec<Col> = fin.iter().chain(fout.iter()).copied().collect();
            let sws: Vec<Col> = sin.iter().chain(sout.iter()).copied().collect();
            let k = IN + OUT;
            for code in 0..(1i64 << k) {
                let y: Vec<i64> = (0..k).map(|t| (code >> t) & 1).collect();
                let mut idx = vec![0i64; k];
                loop {
                    let gated = (0..k).all(|t| idx[t] <= caps[t] * y[t]);
                    let net: i64 = idx[..IN].iter().sum::<i64>() - idx[IN..].iter().sum::<i64>();
                    if gated && net <= b {
                        let mut p = vec![0.0f64; n];
                        for t in 0..k {
                            p[flows[t].index()] = idx[t] as f64;
                            p[sws[t].index()] = y[t] as f64;
                        }
                        for c in &cuts {
                            let act: f64 = c.coeffs.iter().map(|&(j, a)| a * p[j.index()]).sum();
                            assert!(
                                act <= c.ub + 1e-7,
                                "flow cover deleted an integer point: cin={cin:?} cout={cout:?} \
                                 b={b} y={y:?} x={idx:?} activity={act} > ub={}",
                                c.ub
                            );
                        }
                    }
                    let mut t = 0;
                    while t < k {
                        idx[t] += 1;
                        if idx[t] <= caps[t] {
                            break;
                        }
                        idx[t] = 0;
                        t += 1;
                    }
                    if t == k {
                        break;
                    }
                }
            }
        }
        // ...and the guard has to actually SEE cuts, or it proves nothing.
        assert!(
            fired > 0,
            "no flow cover was ever separated: the guard is vacuous"
        );
    }
}

// ---------------------------------------------------------------------------------------------
// AGGREGATED FLOW COVERS -- the single-node relaxation, BUILT rather than found.
// ---------------------------------------------------------------------------------------------

/// How many aggregated flow covers one round may emit. This family gets its OWN budget rather than
/// `cuts_per_round()`'s four, and the number is measured, not guessed: khb05250's root gap needs
/// ~60 of these rows across the two default rounds to close (prototyped against the real LP:
/// 37 + 25 cuts take the bound 95.92M -> 106.15M of a 106.94M optimum, 93% of the gap, where the
/// whole rest of the arsenal manages 7.7%). Four per round would strand it at a third of that.
/// The rows are sparse -- 2 to ~50 nonzeros, nothing like a GMI row -- so forty of them cost the
/// LP less than two tableau cuts.
const MAX_FLOW_AGG_CUTS: usize = 40;

fn flow_agg_cuts_per_round() -> usize {
    MAX_FLOW_AGG_CUTS
}

/// Work caps for the aggregation enumeration, so a pathological model cannot turn the root loop
/// into a quadratic scan. rout uses 15 equalities x ~10 partners x 4 multipliers; the caps sit an
/// order of magnitude above what the corpus needs.
const MAX_AGG_EQUALITIES: usize = 256;
const MAX_AGG_PARTNERS: usize = 24;
const MAX_AGG_THETAS: usize = 4;

/// Deterministic backstop on the number of aggregates one call may BUILD (each is a full exact
/// merge plus a cover search). Counted, not timed, so the cut set never depends on the machine.
const MAX_AGG_EVALS: usize = 4096;

/// Skip a capacity partner whose oriented slack at the LP point exceeds this fraction of
/// `1 + |b|`. ADVICE, not validity: the aggregate keeps exactly the partner's slack at the point
/// (the equality contributes zero to it), and a cover on a comfortably-slack row almost never
/// bites -- measured: rout's productive space keeps 234 of 240 partner orientations at 10%,
/// blend2 (which separates NOTHING here and was paying +7% wall for the search) sheds 78% of its
/// evaluations.
const AGG_SLACK_SKIP: f64 = 0.1;

/// IMPLIED variable upper bounds -- the VUB chained through one bounding row.
///
/// `variable_upper_bounds` only sees the two-column rows `x ≤ u·y`, and on khb05250 that misses
/// every column that matters. Its warehouse rows say `Σ_j x_ij = z_i` (flow out equals flow in)
/// and a separate row says `z_i ≤ 5000·y_i` -- so every `x_ij` is switched by `y_i`, but no single
/// row states it, and the flow-cover family reported "no structure" on a model that is nothing
/// but fixed-charge structure.
///
/// The chain is sound row arithmetic, not a heuristic. Given an oriented row
///
/// ```text
///     Σ_j a_j·x_j − a_z·z  ≤  0,      a_j, a_z > 0,   every x_j ≥ 0,   z ≤ u·y
/// ```
///
/// each term is squeezed by the others: `a_j·x_j ≤ a_z·z − Σ_{k≠j} a_k·x_k ≤ a_z·z ≤ a_z·u·y`,
/// so `x_j ≤ (a_z·u / a_j)·y`. Everything here is exact rational, and the row shapes accepted are
/// deliberately narrow: right-hand side EXACTLY zero (a positive one would shift the bound off the
/// switch; equalities contribute both orientations), exactly ONE negative term, and every positive
/// column bounded below by zero or better -- a term that can go negative cannot be dropped from the
/// squeeze. One hop only: khb needs one, and chains of chains would make the map depend on row
/// order.
fn implied_variable_upper_bounds(
    model: &Model,
    n_rows: usize,
    vubs: &std::collections::HashMap<usize, (BigRational, usize)>,
) -> std::collections::HashMap<usize, (BigRational, usize)> {
    let mut out = vubs.clone();
    for r in 0..n_rows.min(model.num_rows()) {
        let (coeffs, lb, ub) = model.row(Row(r as u32));
        if coeffs.len() < 2 {
            continue;
        }
        'orient: for (sign, rhs) in [(1.0f64, ub), (-1.0, lb)] {
            if !rhs.is_finite() || rhs != 0.0 {
                continue;
            }
            let mut z: Option<(usize, BigRational)> = None; // (column, |a_z|)
            let mut pos: Vec<(usize, BigRational)> = Vec::with_capacity(coeffs.len());
            for &(c, raw) in coeffs {
                let a = sign * raw;
                if a == 0.0 {
                    continue;
                }
                let j = c as usize;
                if a > 0.0 {
                    let (lo, _) = model.col_bounds(Col(c));
                    if lo < 0.0 {
                        continue 'orient; // this term can help z upward: no squeeze
                    }
                    let Some(av) = exact(a) else { continue 'orient };
                    pos.push((j, av));
                } else {
                    if z.is_some() {
                        continue 'orient; // two bounding terms: not a chain
                    }
                    let Some(av) = exact(-a) else {
                        continue 'orient;
                    };
                    z = Some((j, av));
                }
            }
            let Some((zj, az)) = z else { continue };
            let Some((u, y)) = vubs.get(&zj) else {
                continue;
            };
            for (j, aj) in pos {
                if j == *y || j == zj {
                    continue;
                }
                let (lo, up) = model.col_bounds(Col(j as u32));
                // An arc must live in `[0, u·y]`; a fixed column is a constant, not an arc.
                if lo != 0.0 || lo == up {
                    continue;
                }
                let cand = &az * u / &aj;
                if !cand.is_positive() {
                    continue;
                }
                // Keep the TIGHTEST switch bound per column; both are valid, the smaller cuts more.
                match out.entry(j) {
                    std::collections::hash_map::Entry::Occupied(mut e) => {
                        if cand < e.get().0 {
                            e.insert((cand, *y));
                        }
                    }
                    std::collections::hash_map::Entry::Vacant(e) => {
                        e.insert((cand, *y));
                    }
                }
            }
        }
    }
    out
}

/// The next `f64` BELOW `v` -- the mirror of [`next_up`], for rounding a coefficient OUTWARD.
/// Used by `emit_le_cut` below and by the generalisation of its argument in [`coef_to_f64`].
fn next_down(v: f64) -> f64 {
    if !v.is_finite() {
        return v;
    }
    if v == 0.0 {
        return -f64::from_bits(1);
    }
    let b = v.to_bits();
    f64::from_bits(if v > 0.0 { b - 1 } else { b + 1 })
}

/// An exact `Σ a_j·x_j ≤ b` stored as an `f64` [`Cut`], rounded so the stored cut is IMPLIED by
/// the exact one.
///
/// `to_f64` rounds to NEAREST, which can round a coefficient UP -- and a larger coefficient on a
/// non-negative column TIGHTENS a `≤` cut, which is how a valid inequality silently deletes
/// integer points. The GMI and MIR emitters pay for that with a right-hand-side damage term
/// bounded over the box, and refuse columns whose box is unbounded. Here there is a cheaper move:
/// every column an aggregated flow cover touches has `lo == 0` (arcs and kept out-arcs are
/// checked, switches are binary), and on `x ≥ 0` rounding every coefficient DOWNWARD and the
/// right-hand side UPWARD can only RELAX the inequality -- no damage term, no bounded-box
/// requirement, and khb05250's unbounded flow columns stay admissible.
fn emit_le_cut(
    model: &Model,
    terms: &std::collections::BTreeMap<usize, BigRational>,
    rhs: &BigRational,
) -> Option<Cut> {
    let mut coeffs: Vec<(Col, f64)> = Vec::with_capacity(terms.len());
    for (&j, a) in terms {
        if a.is_zero() {
            continue;
        }
        let (lo, _) = model.col_bounds(Col(j as u32));
        if lo < 0.0 {
            return None; // the outward-rounding argument needs x >= 0; nothing here has less
        }
        let f = to_f64(a);
        if !f.is_finite() {
            return None;
        }
        let f = if exact(f)? > *a { next_down(f) } else { f };
        if f != 0.0 {
            coeffs.push((Col(j as u32), f));
        }
        // (f == 0.0 drops the term: on x >= 0 a dropped POSITIVE term relaxes the cut, and a
        // negative one cannot round to zero -- next_down keeps it strictly negative.)
    }
    if coeffs.is_empty() {
        return None;
    }
    let ub0 = to_f64(rhs);
    if !ub0.is_finite() {
        return None;
    }
    let ub = if exact(ub0)? < *rhs {
        next_up(ub0)
    } else {
        ub0
    };
    // Refuse a cut whose numbers are absurd, exactly as `mir_round` does: an aggregate multiplier
    // is a ratio of arbitrary model coefficients, and a row the LP cannot be conditioned around is
    // not a cut, it is a wrecked basis.
    let hi = coeffs.iter().map(|&(_, a)| a.abs()).fold(0.0f64, f64::max);
    let lo = coeffs
        .iter()
        .map(|&(_, a)| a.abs())
        .filter(|&a| a > 0.0)
        .fold(f64::INFINITY, f64::min);
    if hi > MAX_CUT_COEFF || ub.abs() > MAX_CUT_COEFF || hi / lo > MAX_CUT_DYNAMISM {
        crate::sepstat::bump(&crate::sepstat::LATE_ABSURD);
        return None;
    }
    Some(Cut {
        coeffs,
        lb: f64::NEG_INFINITY,
        ub,
    })
}

/// One flow cover on an exact aggregate row `Σ a_j·x_j ≤ b`.
///
/// The derivation is `flow_cover_from_row`'s -- cover from the VUB'd positive terms, out-arcs kept
/// verbatim, positive terms without a switch dropped for free -- with two additions the aggregate
/// path needs:
///
///   * a FIXED column (`lo == up`, finite) is a constant in disguise and moves to the right-hand
///     side. khb05250 writes its demands this way -- `Σ_i x_ij − d_j = 0` with `d_j` a column fixed
///     at 146 -- and without the substitution every demand row is refused for its "nonzero lower
///     bound" and the instance shows no structure at all.
///   * SINGLE-ARC covers are admitted (the caller guarantees at least one real VUB'd arc exists).
///     On khb they are the whole point: cover `{x_ij}` with `m = 5000·1`, `λ = 5000 − d_j`, switch
///     term `d_j` gives exactly `x_ij ≤ d_j·y_i` -- the implied-bound cut, the family Gurobi
///     separates 83 of to close this instance at the root.
fn agg_flow_cover(
    model: &Model,
    x: &[f64],
    terms: &std::collections::BTreeMap<usize, BigRational>,
    b0: &BigRational,
    vubs: &std::collections::HashMap<usize, (BigRational, usize)>,
) -> Option<Cut> {
    struct Arc {
        j: usize,
        y: usize,
        a: BigRational,
        m: BigRational,
    }
    let mut b = b0.clone();
    let mut arcs: Vec<Arc> = Vec::new();
    let mut keep: Vec<(usize, BigRational)> = Vec::new(); // negative terms, kept verbatim
    for (&j, a) in terms {
        if a.is_zero() {
            continue;
        }
        let (lo, up) = model.col_bounds(Col(j as u32));
        if lo != 0.0 {
            if lo.is_finite() && lo == up {
                b -= a * &exact(lo)?; // fixed column: a constant wearing a column's name
                continue;
            }
            return None; // the derivation is written for x >= 0; shifted columns are MIR's job
        }
        if a.is_positive() {
            match vubs.get(&j) {
                Some((u, y)) if *y != j => arcs.push(Arc {
                    j,
                    y: *y,
                    a: a.clone(),
                    m: a * u,
                }),
                // No switch to charge: a_j·x_j >= 0, dropping it only relaxes.
                _ => {}
            }
        } else {
            keep.push((j, a.clone()));
        }
    }
    if arcs.is_empty() {
        return None;
    }

    // Greedy prefix covers, the arcs the relaxation leans on first -- as the plain family does.
    let mut order: Vec<usize> = (0..arcs.len()).collect();
    let val = |k: usize, arcs: &Vec<Arc>| -> f64 {
        to_f64(&arcs[k].a) * x.get(arcs[k].j).copied().unwrap_or(0.0)
    };
    order.sort_by(|&p, &q| {
        val(q, &arcs)
            .partial_cmp(&val(p, &arcs))
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    let mut chosen: Vec<usize> = Vec::new();
    let mut cap = BigRational::zero();
    let mut best: Option<(f64, Cut)> = None;
    for &k in &order {
        chosen.push(k);
        cap += &arcs[k].m;
        let lambda = &cap - &b;
        if !lambda.is_positive() {
            continue; // not yet a cover
        }
        let mut t: std::collections::BTreeMap<usize, BigRational> =
            std::collections::BTreeMap::new();
        let mut rhs = b.clone();
        for &i in &chosen {
            let arc = &arcs[i];
            *t.entry(arc.j).or_insert_with(BigRational::zero) += &arc.a;
            let excess = &arc.m - &lambda;
            if excess.is_positive() {
                *t.entry(arc.y).or_insert_with(BigRational::zero) -= &excess;
                rhs -= &excess;
            }
        }
        for (j, a) in &keep {
            *t.entry(*j).or_insert_with(BigRational::zero) += a;
        }
        let Some(cut) = emit_le_cut(model, &t, &rhs) else {
            continue;
        };
        if cut.coeffs.len() > MAX_CUT_NNZ_LOCAL {
            // FORGONE COST — the same shape as the `coef_to_f64` refusal: `emit_le_cut`
            // has returned Some, so an exact aggregated flow cover is fully derived and
            // then discarded unexamined. `agg_flow_cover` returns ONE cut (the arg-max
            // over cover prefixes), so a wide candidate that is violated but no deeper
            // than the incumbent cost nothing: charge only candidates that would have
            // BEEN the returned cut, using the very test the surviving branch applies
            // two lines down. One f64 dot product, below the rational aggregation of
            // the same loop iteration — not free, but strictly dominated by it.
            let v = violation(&cut, x);
            crate::sepstat::gate_charge(
                crate::sepstat::GATE_FLOWCOVER_AGG_NNZ,
                u64::from(v > best.as_ref().map_or(min_violation(), |(bv, _)| *bv)),
            );
            continue;
        }
        let v = violation(&cut, x);
        if v > best.as_ref().map_or(min_violation(), |(bv, _)| *bv) {
            best = Some((v, cut));
        }
    }
    best.map(|(_, c)| c)
}

/// AGGREGATED FLOW-COVER SEPARATION -- reaching the rows where `separate_flow_cover` provably
/// degenerates.
///
/// The proof at `separate_flow_cover` stands: on a `b = 0` row every switch term `(m_j − λ)⁺`
/// vanishes and no choice of cover changes that. And on rout and khb05250 the VUB'd columns sit
/// ONLY in `b = 0` rows, so the family that was written for fixed-charge networks separates
/// nothing on either. The fix it names is implemented here: BUILD the single-node relaxation by
/// aggregation instead of hoping to find it as a row.
///
/// Two constructions, both exact rational end to end:
///
///   1. ENRICHED SINGLE ROWS. The row is taken as it stands, but the arc model is widened: implied
///      VUBs chained through a bounding row (`implied_variable_upper_bounds` -- khb05250's
///      `x_ij ≤ 5000·y_i` through the warehouse equality) and FIXED columns substituted into the
///      right-hand side (khb writes demands as columns pinned at their value, so its `b` was
///      hiding). Together they turn khb's 26 demand equalities into textbook single-node flow
///      sets, and the single-arc covers on them are the implied-bound family: measured on the real
///      LP (HiGHS prototype), two rounds take the root bound 95.92M -> 106.15M of a 106.94M
///      optimum -- 93% of the gap the whole rest of the arsenal leaves at 7.7%.
///
///   2. CONSERVATION + CAPACITY AGGREGATES. A conservation equality `E` (finite `lb == ub`,
///      carrying VUB'd arcs) is added to a one-sided capacity row `K` sharing columns with it,
///      with an exact multiplier `θ = −k_c/e_c` chosen to CANCEL a shared column -- one candidate
///      per high-LP-mass shared column. A non-negative combination is not required: `E` is an
///      equality, so ANY `θ` keeps `K + θ·E ≤ b_K + θ·b_E` valid. The aggregate has `K`'s
///      right-hand side -- REAL capacity, not zero -- and `E`'s VUB'd arcs, which is the
///      single-node set the plain family needed. On rout this separates covers violated by up to
///      3.9 where the row-by-row search measured 0.0000 forever.
///
/// ⚠ WHAT THIS BUYS, MEASURED HONESTLY (prototyped on the real LPs before porting): khb05250's
/// root closes to 93%+ (the decisive move there). rout's cuts are genuinely violated and genuinely
/// tight -- and its ROOT bound still barely moves (981.86 -> 981.92 at saturation, 200+ cuts),
/// because rout's relaxation is so degenerate that the optimal FACE survives every family anyone
/// has (Gurobi's own root closes 5%). rout's payoff, if any, is in the TREE: these rows are
/// carried by every node, and a node that fixes a switch makes them bite. qnet1 has no VUB
/// structure this can see (its lever is MIR budget, per the journal above); air/gt2/flugpl/mas76
/// have no VUBs at all and pay one hash-map probe to find that out.
pub(crate) fn separate_flow_cover_agg(model: &Model, x: &[f64], n_rows: usize) -> Vec<Cut> {
    let base = variable_upper_bounds(model);
    if base.is_empty() {
        return Vec::new(); // no `x <= u·y` anywhere: nothing to chain, nothing to aggregate
    }
    let n_rows = n_rows.min(model.num_rows());
    let vubs = implied_variable_upper_bounds(model, n_rows, &base);

    let mut cand: Vec<(f64, Cut)> = Vec::new();
    let mut seen: std::collections::HashSet<Vec<(u32, u64)>> = std::collections::HashSet::new();
    let mut push = |cut: Cut, cand: &mut Vec<(f64, Cut)>| {
        let mut sig: Vec<(u32, u64)> = cut
            .coeffs
            .iter()
            .map(|&(c, a)| (c.0, a.to_bits()))
            .collect();
        sig.sort_unstable();
        sig.push((u32::MAX, cut.ub.to_bits()));
        if seen.insert(sig) {
            let v = violation(&cut, x);
            cand.push((v, cut));
        }
    };

    // ---- pass 1: single rows under the ENRICHED arc model ---------------------------------
    for r in 0..n_rows {
        let (coeffs, lb, ub) = model.row(Row(r as u32));
        if coeffs.len() < 2 {
            continue;
        }
        for (sign, rhs) in [(1.0f64, ub), (-1.0, lb)] {
            if !rhs.is_finite() {
                continue;
            }
            // Only where the enrichment says something the plain family cannot: a fixed column to
            // substitute, or an arc whose only switch is an IMPLIED bound. Anything else is
            // `separate_flow_cover`'s turf, and re-separating it would only duplicate rows.
            let mut enriched = false;
            for &(c, raw) in coeffs {
                let a = sign * raw;
                let j = c as usize;
                let (lo, up) = model.col_bounds(Col(c));
                if lo != 0.0 && lo.is_finite() && lo == up {
                    enriched = true;
                    break;
                }
                if a > 0.0 && lo == 0.0 && !base.contains_key(&j) && vubs.contains_key(&j) {
                    enriched = true;
                    break;
                }
            }
            if !enriched {
                continue;
            }
            let Some(b) = exact(sign * rhs) else { continue };
            let mut terms: std::collections::BTreeMap<usize, BigRational> =
                std::collections::BTreeMap::new();
            let mut ok = true;
            for &(c, raw) in coeffs {
                let Some(a) = exact(sign * raw) else {
                    ok = false;
                    break;
                };
                if !a.is_zero() {
                    *terms.entry(c as usize).or_insert_with(BigRational::zero) += a;
                }
            }
            if !ok {
                continue;
            }
            if let Some(cut) = agg_flow_cover(model, x, &terms, &b, &vubs) {
                push(cut, &mut cand);
            }
        }
    }

    // ---- pass 2: conservation-like equality + capacity row, exact multiplier --------------
    // One-sided rows with at least three terms, indexed by column. Two-term partners are the VUB
    // rows themselves, and aggregating a VUB into its own conservation row is exactly the
    // "relax the arc to −m·y" move the plain family's journal measured useless.
    let mut by_col: std::collections::HashMap<usize, Vec<usize>> = std::collections::HashMap::new();
    for r in 0..n_rows {
        let (coeffs, lb, ub) = model.row(Row(r as u32));
        if coeffs.len() < 3 || (lb == ub && lb.is_finite()) {
            continue;
        }
        if !lb.is_finite() && !ub.is_finite() {
            continue;
        }
        for &(c, a) in coeffs {
            if a != 0.0 {
                by_col.entry(c as usize).or_default().push(r);
            }
        }
    }

    let mut eqs_seen = 0usize;
    let mut evals = 0usize;
    'eqs: for e in 0..n_rows {
        if eqs_seen >= MAX_AGG_EQUALITIES {
            break;
        }
        let (ecoeffs, elb, eub) = model.row(Row(e as u32));
        if !(elb == eub && eub.is_finite()) || ecoeffs.len() < 2 {
            continue;
        }
        if !ecoeffs
            .iter()
            .any(|&(c, _)| vubs.contains_key(&(c as usize)))
        {
            continue; // no arc for a cover to charge: aggregation has nothing to aim at
        }
        eqs_seen += 1;
        let Some(be) = exact(eub) else { continue };
        let mut eterms: std::collections::BTreeMap<usize, BigRational> =
            std::collections::BTreeMap::new();
        let mut ok = true;
        for &(c, raw) in ecoeffs {
            let Some(a) = exact(raw) else {
                ok = false;
                break;
            };
            if !a.is_zero() {
                *eterms.entry(c as usize).or_insert_with(BigRational::zero) += a;
            }
        }
        if !ok {
            continue;
        }
        // Partner rows, deterministically ordered, capped.
        let mut partners: std::collections::BTreeSet<usize> = std::collections::BTreeSet::new();
        for &j in eterms.keys() {
            if let Some(rs) = by_col.get(&j) {
                partners.extend(rs.iter().copied());
            }
        }
        for k in partners.into_iter().take(MAX_AGG_PARTNERS) {
            let (kcoeffs, klb, kub) = model.row(Row(k as u32));
            // The partner's activity at the point, once per row -- the slack filter below reads it
            // in both orientations.
            let kact: f64 = kcoeffs
                .iter()
                .map(|&(c, a)| a * x.get(c as usize).copied().unwrap_or(0.0))
                .sum();
            for (ksign, krhs) in [(1.0f64, kub), (-1.0, klb)] {
                if !krhs.is_finite() {
                    continue;
                }
                // A SLACK partner makes a slack aggregate -- the equality contributes exactly zero
                // to the activity at the LP point, so the aggregate's slack IS the partner's, and
                // a cover on a comfortably-slack row almost never bites. Advice, not validity:
                // skipping a row can only miss a cut, never admit a wrong one.
                if ksign * (krhs - kact) > AGG_SLACK_SKIP * (1.0 + krhs.abs()) {
                    continue;
                }
                let Some(bk) = exact(ksign * krhs) else {
                    continue;
                };
                let mut kterms: std::collections::BTreeMap<usize, BigRational> =
                    std::collections::BTreeMap::new();
                let mut ok = true;
                for &(c, raw) in kcoeffs {
                    let Some(a) = exact(ksign * raw) else {
                        ok = false;
                        break;
                    };
                    if !a.is_zero() {
                        *kterms.entry(c as usize).or_insert_with(BigRational::zero) += a;
                    }
                }
                if !ok {
                    continue;
                }
                // Multiplier candidates: cancel a shared column, highest LP mass first. The θ that
                // cancels the column the relaxation leans on hardest is the one that leaves a
                // violated aggregate behind -- measured on rout, where the winning aggregates all
                // cancel a heavy shared binary out of the capacity row.
                let mut shared: Vec<usize> = kterms
                    .keys()
                    .filter(|j| eterms.contains_key(j))
                    .copied()
                    .collect();
                if shared.is_empty() {
                    continue;
                }
                shared.sort_by(|&p, &q| {
                    let mp = to_f64(&kterms[&p]).abs() * x.get(p).copied().unwrap_or(0.0).abs();
                    let mq = to_f64(&kterms[&q]).abs() * x.get(q).copied().unwrap_or(0.0).abs();
                    mq.partial_cmp(&mp).unwrap_or(std::cmp::Ordering::Equal)
                });
                let mut thetas: Vec<BigRational> = Vec::new();
                for &j in shared.iter() {
                    if thetas.len() >= MAX_AGG_THETAS {
                        break;
                    }
                    let th = -(&kterms[&j] / &eterms[&j]);
                    if !th.is_zero() && !thetas.contains(&th) {
                        thetas.push(th);
                    }
                }
                for th in &thetas {
                    if evals >= MAX_AGG_EVALS {
                        break 'eqs; // the deterministic work backstop
                    }
                    evals += 1;
                    let mut agg = kterms.clone();
                    for (j, a) in &eterms {
                        *agg.entry(*j).or_insert_with(BigRational::zero) += a * th;
                    }
                    agg.retain(|_, a| !a.is_zero());
                    if agg.len() < 2 {
                        continue;
                    }
                    let b = &bk + th * &be;
                    if let Some(cut) = agg_flow_cover(model, x, &agg, &b, &vubs) {
                        push(cut, &mut cand);
                    }
                }
            }
        }
    }

    // Most violated first; stable sort keeps ties in deterministic row order.
    cand.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap_or(std::cmp::Ordering::Equal));
    cand.truncate(flow_agg_cuts_per_round());
    cand.into_iter().map(|(_, c)| c).collect()
}

/// IMPLIED-BOUND cuts — the `x_j ≤ u·y` rows the variable-upper-bound structure IMPLIES but the
/// model does not carry, for the LP points that violate one.
///
/// Gurobi separates 83 of these on khb05250 and calls them the decisive family, and the target here
/// is broad: a `x_j ≤ u·y` inequality (`y` binary) that cuts a fractional point off is exactly the
/// simplest fixed-charge cut there is. The construction reuses [`implied_variable_upper_bounds`] --
/// the chain khb05250's warehouse equalities and rout's conservation rows are made of -- and admits
/// each row through [`emit_le_cut`], which rounds it so the stored `f64` cut is IMPLIED by the exact
/// one (every column here has `lo == 0`, so the outward-rounding argument holds with no damage term).
///
/// ⚠ WHAT THIS SEPARATES ON THE CORPUS, MEASURED (2026-07-16): NOTHING. And the reason is a PROOF,
/// so it is written down to spare the next reader the build. Every bound this can emit is a
/// SINGLE-ROW CONSEQUENCE of two constraints the LP already satisfies. `implied_variable_upper_bounds`
/// derives `x_j ≤ (a_z·u_z/a_j)·y` from a bounding row `a_j·x_j + Σ(other ≥0 terms) − a_z·z ≤ 0`
/// (so `a_j·x_j ≤ a_z·z` at any point respecting the row, the other positive terms being ≥ 0) and
/// `z`'s own VUB `z ≤ u_z·y` -- BOTH original rows, hence in every LP of the loop and every node
/// under it. So `a_j·x_j ≤ a_z·z ≤ a_z·u_z·y` holds at the LP point by construction: the "cut" is
/// never violated. (The base VUBs are skipped for the same reason one level down -- they are the
/// explicit two-column rows themselves.) The khb05250 implied bounds Gurobi separates are a DIFFERENT
/// object: `x_ij ≤ d_j·y_i` comes from a demand EQUALITY whose right-hand side is a fixed demand
/// COLUMN, and `d_j` is not a binary switch, so no chain reaches it -- the single-arc flow cover in
/// `agg_flow_cover` builds it instead, and that is why khb05250 already closes to 98.5% without this.
/// The 500-1700 implications a probing engine would find are `y=1 ⇒ x≤v` facts NO single row states;
/// reaching them needs the probing lane (built once, HELD as a corpus no-win), not this chain.
///
/// Kept EXACT-admitted and TESTED as opt-in infrastructure (`--implied-bound`): the moment a
/// probing source of genuinely-violated `x_j ≤ u·y` implications exists, this is the separator that
/// turns them into sound cuts. Default-off, so every default tree is bit-identical.
/// `AY_MILP_IMPLIED_BOUND_DEBUG=1` prints the census (base / chained / violated / admitted).
pub(crate) fn separate_implied_bound(model: &Model, x: &[f64], n_rows: usize) -> Vec<Cut> {
    let base = variable_upper_bounds(model);
    if base.is_empty() {
        return Vec::new(); // no `x ≤ u·y` anywhere: nothing to chain
    }
    let n_rows = n_rows.min(model.num_rows());
    let vubs = implied_variable_upper_bounds(model, n_rows, &base);

    // Deterministic order: a HashMap iterated raw would pick a different vertex on a degenerate LP.
    let mut items: Vec<(usize, BigRational, usize)> = vubs
        .iter()
        .filter(|(j, _)| !base.contains_key(j)) // base VUBs are explicit rows: the LP satisfies them
        .map(|(&j, (u, y))| (j, u.clone(), *y))
        .collect();
    items.sort_by_key(|a| (a.0, a.2));

    let mut cuts = Vec::new();
    let mut violated = 0usize;
    for (j, u, y) in items {
        if j == y {
            continue;
        }
        let xj = x.get(j).copied().unwrap_or(0.0);
        let xy = x.get(y).copied().unwrap_or(0.0);
        if xj - to_f64(&u) * xy <= MIN_VIOLATION {
            continue; // the LP already respects this bound -- see the proof above
        }
        violated += 1;
        // `x_j − u·y ≤ 0`, admitted EXACTLY. Both columns have `lo == 0` (checked when the chain was
        // formed), so `emit_le_cut`'s downward coefficient rounding only relaxes the row.
        let mut terms: std::collections::BTreeMap<usize, BigRational> =
            std::collections::BTreeMap::new();
        terms.insert(j, <BigRational as One>::one());
        terms.insert(y, -u);
        if let Some(cut) = emit_le_cut(model, &terms, &BigRational::zero()) {
            if clears_min_violation(&cut, x) {
                cuts.push(cut);
            }
        }
    }
    if false {
        // B22 retired the census env spelling; flip this literal for a one-off diagnosis.
        eprintln!(
            "--implied-bound base={} chained_extra={} violated={} admitted={}",
            base.len(),
            vubs.len().saturating_sub(base.len()),
            violated,
            cuts.len()
        );
    }
    cuts
}

#[cfg(test)]
mod implied_bound_tests {
    use super::*;
    use crate::model::Sense;

    /// AN IMPLIED-BOUND CUT MUST NOT REMOVE AN INTEGER POINT.
    ///
    /// The chained bound `x_j ≤ u·y` is exact by construction, but the STORED cut is an `f64`
    /// rounding of it, and this is the test that the rounding stayed on the safe side. The model is a
    /// miniature chain: `x ≤ u_z·z` (a VUB) and a bounding row `a·x_j − a_z·z ≤ 0` that implies
    /// `x_j ≤ (a_z·u_z/a)·y` through `z` -- exactly the shape `implied_variable_upper_bounds` reads.
    /// Every point of the mixed hull (the binary fixed) is swept and checked against every emitted
    /// cut, so a coefficient rounded the wrong way would be caught here.
    #[test]
    fn implied_bound_cuts_never_remove_an_integer_point() {
        let mut seed = 0x1B0D_2026_u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };

        let mut fired = 0usize;
        for _case in 0..400 {
            let az = 1 + rnd() % 4; // z's coefficient in the bounding row
            let aj = 1 + rnd() % 4; // x_j's coefficient
            let uz = 1 + rnd() % 5; // z ≤ uz·y

            let mut m = Model::new();
            let y = m.add_binary_col();
            let z = m.add_col(0.0, (uz * 3) as f64); // z is bounded generously; its VUB row binds it
            let xj = m.add_col(0.0, (az * uz * 3) as f64);
            // z's variable upper bound: `z − uz·y ≤ 0`.
            m.add_row(f64::NEG_INFINITY, 0.0, &[(z, 1.0), (y, -(uz as f64))]);
            // The bounding row `aj·x_j − az·z ≤ 0`, implying `x_j ≤ (az·uz/aj)·y`.
            m.add_row(
                f64::NEG_INFINITY,
                0.0,
                &[(xj, aj as f64), (z, -(az as f64))],
            );
            m.set_objective(&[(xj, -1.0)], Sense::Minimize);

            let n = m.num_cols();
            // A random point (need not be feasible): the cuts must hold at every INTEGER point regardless.
            let pt: Vec<f64> = (0..n).map(|_| (rnd() % 60) as f64 / 10.0).collect();
            let cuts = separate_implied_bound(&m, &pt, m.num_rows());
            if cuts.is_empty() {
                continue;
            }
            fired += 1;
            // Sweep the mixed hull: y ∈ {0,1}, z and x_j over their integer boxes, keeping only points
            // that satisfy the two model rows, and assert every cut holds there.
            for yv in 0..=1i64 {
                for zv in 0..=(uz * 3) {
                    for xv in 0..=(az * uz * 3) {
                        // row 1: z ≤ uz·y ; row 2: aj·x_j ≤ az·z
                        if zv > uz * yv {
                            continue;
                        }
                        if aj * xv > az * zv {
                            continue;
                        }
                        let p = [yv as f64, zv as f64, xv as f64];
                        for c in &cuts {
                            let act: f64 =
                                c.coeffs.iter().map(|&(col, a)| a * p[col.index()]).sum();
                            assert!(
                                act <= c.ub + 1e-9,
                                "implied-bound cut removed integer point (y={yv} z={zv} x={xv}): \
                                 act={act} ub={} az={az} aj={aj} uz={uz}",
                                c.ub
                            );
                        }
                    }
                }
            }
        }
        // The construction must actually fire on this family, or the test proves nothing. (The chain
        // bound is LP-implied, so it fires only on the RANDOM points that violate it -- which the
        // seed above is chosen to include.)
        assert!(
            fired > 0,
            "no implied-bound cut ever separated: test is vacuous"
        );
    }
}

#[cfg(test)]
mod agg_flow_cover_tests {
    use super::*;
    use crate::model::Sense;

    /// AN AGGREGATED FLOW COVER MUST NOT DELETE AN INTEGER POINT.
    ///
    /// The model is rout in miniature: a conservation EQUALITY (in-flows with VUB switches,
    /// out-flows, and binary demand columns) sharing its binaries with a CAPACITY row -- the shape
    /// where the plain family provably degenerates (`b = 0`) and only the aggregate can speak.
    /// Every arc coefficient is UNIT, for the same reason the plain family's guard insists on it:
    /// with `[I; 1 −1]`-shaped flow constraints every fiber of the mixed hull (integers fixed) is
    /// totally unimodular, so its vertices are integral and an integer sweep visits every point a
    /// linear cut could be tight against. The capacity row touches only binaries, where
    /// integrality is enumeration itself.
    #[test]
    fn aggregated_flow_cover_cuts_never_remove_an_integer_point() {
        let mut seed = 0xA66F_2026_u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };

        let mut fired = 0usize;
        for _case in 0..300 {
            const IN: usize = 3;
            const OUT: usize = 1;
            const DEM: usize = 3;
            let cin: Vec<i64> = (0..IN).map(|_| 1 + rnd() % 3).collect();
            let cout: Vec<i64> = (0..OUT).map(|_| 1 + rnd() % 3).collect();
            let dcap: Vec<i64> = (0..DEM).map(|_| 1 + rnd() % 4).collect(); // capacity row coeffs

            let mut m = Model::new();
            let fin: Vec<Col> = cin.iter().map(|&u| m.add_col(0.0, u as f64)).collect();
            let fout: Vec<Col> = cout.iter().map(|&u| m.add_col(0.0, u as f64)).collect();
            let sin: Vec<Col> = (0..IN).map(|_| m.add_binary_col()).collect();
            let dem: Vec<Col> = (0..DEM).map(|_| m.add_binary_col()).collect();
            // In-arcs gated by their switches: `f <= u·y`.
            for k in 0..IN {
                m.add_row(
                    f64::NEG_INFINITY,
                    0.0,
                    &[(fin[k], 1.0), (sin[k], -(cin[k] as f64))],
                );
            }
            // The conservation EQUALITY, b = 0: in − out − demands = 0.
            let mut bal: Vec<(Col, f64)> = fin.iter().map(|&c| (c, 1.0)).collect();
            bal.extend(fout.iter().map(|&c| (c, -1.0)));
            bal.extend(dem.iter().map(|&c| (c, -1.0)));
            m.add_row(0.0, 0.0, &bal);
            // The CAPACITY row the demands share with it.
            let total: i64 = dcap.iter().sum();
            let b = 1 + rnd() % total.max(2);
            let cap_terms: Vec<(Col, f64)> = dem
                .iter()
                .zip(&dcap)
                .map(|(&c, &w)| (c, w as f64))
                .collect();
            m.add_row(f64::NEG_INFINITY, b as f64, &cap_terms);
            m.set_objective(&[(fin[0], 1.0)], Sense::Minimize);

            let n = m.num_cols();
            let x: Vec<f64> = (0..n).map(|_| (rnd() % 40) as f64 / 10.0).collect();
            let cuts = separate_flow_cover_agg(&m, &x, m.num_rows());
            fired += cuts.len();
            if cuts.is_empty() {
                continue;
            }

            // Sweep EVERY integer point the model admits.
            let caps: Vec<i64> = cin.iter().chain(cout.iter()).copied().collect();
            let k_flows = IN + OUT;
            let k_bins = IN + DEM;
            for code in 0..(1i64 << k_bins) {
                let y: Vec<i64> = (0..k_bins).map(|t| (code >> t) & 1).collect();
                let mut idx = vec![0i64; k_flows];
                loop {
                    let gated = (0..IN).all(|t| idx[t] <= cin[t] * y[t]);
                    let net: i64 = idx[..IN].iter().sum::<i64>()
                        - idx[IN..].iter().sum::<i64>()
                        - y[IN..].iter().sum::<i64>();
                    let cap_ok: bool = (0..DEM).map(|t| dcap[t] * y[IN + t]).sum::<i64>() <= b;
                    if gated && net == 0 && cap_ok {
                        let mut p = vec![0.0f64; n];
                        for t in 0..IN {
                            p[fin[t].index()] = idx[t] as f64;
                            p[sin[t].index()] = y[t] as f64;
                        }
                        for t in 0..OUT {
                            p[fout[t].index()] = idx[IN + t] as f64;
                        }
                        for t in 0..DEM {
                            p[dem[t].index()] = y[IN + t] as f64;
                        }
                        for c in &cuts {
                            let act: f64 = c.coeffs.iter().map(|&(j, a)| a * p[j.index()]).sum();
                            assert!(
                                act <= c.ub + 1e-7,
                                "aggregated flow cover deleted an integer point: cin={cin:?} \
                                 cout={cout:?} dcap={dcap:?} b={b} y={y:?} flows={idx:?} \
                                 activity={act} > ub={}",
                                c.ub
                            );
                        }
                    }
                    let mut t = 0;
                    while t < k_flows {
                        idx[t] += 1;
                        if idx[t] <= caps[t] {
                            break;
                        }
                        idx[t] = 0;
                        t += 1;
                    }
                    if t == k_flows {
                        break;
                    }
                }
            }
        }
        assert!(
            fired > 0,
            "no aggregated flow cover was ever separated: the guard is vacuous"
        );
    }

    /// ...AND NEITHER MUST THE ENRICHED SINGLE-ROW PASS (implied VUBs + fixed-column
    /// substitution).
    ///
    /// khb05250 in miniature: two warehouses, each `z_w <= U_w·y_w` and `Σ_c x_wc = z_w`
    /// (the chain that yields the implied VUB `x_wc <= U_w·y_w`), and per-customer demand
    /// equalities `Σ_w x_wc − D_c = 0` with `D_c` a column FIXED at its value -- exactly how khb
    /// writes its right-hand sides. The single-arc covers here are the implied-bound family
    /// `x_wc <= d_c·y_w`, which is where the validity argument is most likely to be wrong
    /// (`λ = m − d`, the switch term IS the cut).
    #[test]
    fn enriched_flow_cover_cuts_never_remove_an_integer_point() {
        let mut seed = 0x01B0_5250_u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };

        let mut fired = 0usize;
        for _case in 0..300 {
            const W: usize = 2; // warehouses
            const C: usize = 2; // customers
            let ucap: Vec<i64> = (0..W).map(|_| 3 + rnd() % 4).collect();
            let dval: Vec<i64> = (0..C).map(|_| 1 + rnd() % 3).collect();

            let mut m = Model::new();
            let z: Vec<Col> = ucap.iter().map(|&u| m.add_col(0.0, u as f64)).collect();
            let y: Vec<Col> = (0..W).map(|_| m.add_binary_col()).collect();
            // x[w][c], each in [0, ucap[w]]
            let x: Vec<Vec<Col>> = (0..W)
                .map(|w| (0..C).map(|_| m.add_col(0.0, ucap[w] as f64)).collect())
                .collect();
            let d: Vec<Col> = dval
                .iter()
                .map(|&v| m.add_col(v as f64, v as f64))
                .collect();
            for w in 0..W {
                // z_w <= U_w · y_w
                m.add_row(
                    f64::NEG_INFINITY,
                    0.0,
                    &[(z[w], 1.0), (y[w], -(ucap[w] as f64))],
                );
                // Σ_c x_wc − z_w = 0 : the chain the implied VUB reads.
                let mut t: Vec<(Col, f64)> = x[w].iter().map(|&c| (c, 1.0)).collect();
                t.push((z[w], -1.0));
                m.add_row(0.0, 0.0, &t);
            }
            for c in 0..C {
                // Σ_w x_wc − D_c = 0, D_c fixed.
                let mut t: Vec<(Col, f64)> = (0..W).map(|w| (x[w][c], 1.0)).collect();
                t.push((d[c], -1.0));
                m.add_row(0.0, 0.0, &t);
            }
            m.set_objective(&[(y[0], 1.0)], Sense::Minimize);

            let n = m.num_cols();
            let pt: Vec<f64> = (0..n).map(|_| (rnd() % 30) as f64 / 10.0).collect();
            let cuts = separate_flow_cover_agg(&m, &pt, m.num_rows());
            fired += cuts.len();
            if cuts.is_empty() {
                continue;
            }

            // Sweep every integer point: y ∈ {0,1}^W, x[w][c] ∈ 0..ucap[w]; z is determined.
            let k = W * C;
            for code in 0..(1i64 << W) {
                let yv: Vec<i64> = (0..W).map(|t| (code >> t) & 1).collect();
                let mut idx = vec![0i64; k];
                loop {
                    let zval: Vec<i64> = (0..W)
                        .map(|w| (0..C).map(|c| idx[w * C + c]).sum())
                        .collect();
                    let gated = (0..W).all(|w| zval[w] <= ucap[w] * yv[w]);
                    let met =
                        (0..C).all(|c| (0..W).map(|w| idx[w * C + c]).sum::<i64>() == dval[c]);
                    if gated && met {
                        let mut p = vec![0.0f64; n];
                        for w in 0..W {
                            p[z[w].index()] = zval[w] as f64;
                            p[y[w].index()] = yv[w] as f64;
                            for c in 0..C {
                                p[x[w][c].index()] = idx[w * C + c] as f64;
                            }
                        }
                        for c in 0..C {
                            p[d[c].index()] = dval[c] as f64;
                        }
                        for cut in &cuts {
                            let act: f64 = cut.coeffs.iter().map(|&(j, a)| a * p[j.index()]).sum();
                            assert!(
                                act <= cut.ub + 1e-7,
                                "enriched flow cover deleted an integer point: ucap={ucap:?} \
                                 dval={dval:?} y={yv:?} x={idx:?} activity={act} > ub={}",
                                cut.ub
                            );
                        }
                    }
                    let mut t = 0;
                    while t < k {
                        idx[t] += 1;
                        if idx[t] <= ucap[t / C] {
                            break;
                        }
                        idx[t] = 0;
                        t += 1;
                    }
                    if t == k {
                        break;
                    }
                }
            }
        }
        assert!(
            fired > 0,
            "no enriched flow cover was ever separated: the guard is vacuous"
        );
    }
}

/// LIFTED COVER WITH THE GENERAL INTEGERS LIFTED *IN*.
///
/// rout's capacity rows are mixed knapsacks --
/// `Σ(60 binaries) d_j·y_j + 4.99·x302 + 5.71·x307 + 4.28·x312 ≤ 12.5`, the integers in `[0,2]` --
/// and every family in this crate misses them for the same reason: they stop CHARGING the integers.
/// Paying them off (`separate`'s mixed-row relaxation) is valid and SLACK: it hands their share of
/// the capacity back to the binaries, which then sit comfortably inside it, so a cover exists and
/// nothing violates one. MIR sees these rows and reaches 982.49. rout's bound has not moved off
/// 982.486176 through GMI, MIR, aggregated MIR, flow covers or generalized flow covers.
///
/// The cut that BINDS keeps them charged.
///
/// 1. On the face `x_G = 0` this is a pure binary knapsack, and a violated cover `C` gives
///    `Σ_{j∈C} y_j ≤ |C| − 1`. (That base cut is in fact valid off the face too -- if every item of
///    `C` were on, the row is already broken whatever the integers do -- but it is WEAK there, and
///    the weakness is the whole problem.)
/// 2. Lift each integer back in, sequentially. With the cut so far reading `Λ ≤ rhs`, the largest
///    coefficient `x_k` may take is
///
///    ```text
///    γ_k  =  min_{t = 1..u_k}  ( rhs − Ψ(b − a_k·t) ) / t
///    ```
///
///    where `Ψ(c)` is the most the cut-so-far can be worth when only `c` capacity is left. For the
///    base cut every cover coefficient is 1, so `Ψ` is a max-CARDINALITY knapsack and the
///    ascending-weight greedy solves it exactly. A lifted integer then joins `Ψ` as an item with
///    `u_k` copies -- and with three of them, each `≤ 2`, that is 27 combinations.
///
/// Validity, for one lift: the row gives `Σ_C a_j·y_j ≤ b − a_k·x_k` (dropping the non-cover
/// binaries only lowers the left side, every coefficient being ≥ 0), so `Σ_C y_j ≤ Ψ(b − a_k·x_k)`;
/// and `γ_k·x_k ≤ rhs − Ψ(b − a_k·x_k)` is exactly what the minimum defining `γ_k` asserts. Add them.
/// `x_k = 0` is the base cut. Sequential lifting repeats the argument with the previous lift folded
/// into `Ψ`, and any order is valid.
///
/// ⚠ Guarded by `lifted_cover_cuts_never_remove_an_integer_point`, which FAILS on a lift one step
/// too greedy (`γ + 1`: `wb=[4,6,5,3,2] wg=[2,5] ug=[1,2] b=7`, the point `y=0, x=(1,1)` has
/// activity 3 against an ub of 2).
///
/// ⚠⚠ AND IT STILL DOES NOT CLOSE ROUT -- THE COVER FAMILY IS EXHAUSTED. Two aiming bugs were found
/// and fixed on the way, and they are worth keeping because each looked like the answer:
///
///   * separating at the face `x_G = 0`. rout's LP is nowhere near it: the LP satisfies those rows
///     precisely BY spending the integers, so with them at zero the binaries have the whole 12.5 to
///     themselves and no cover is even tight. Fixed: separate at `x_G = ⌊x*_G⌋`, the face the point
///     is standing on, and lift back from a NON-ZERO reference (hence the two-sided window below).
///   * ranking the cover by `y*` alone. A cover is violated iff `Σ_{j∈C}(1 − y*_j) < 1`, so the
///     separation must reach the capacity while spending as little `1 − y*` as possible -- which is
///     cheapest `1 − y*` PER UNIT WEIGHT, not highest `y*`. Ranking by `y*` found a cover on every
///     capacity row and violated none of them.
///
/// With both fixed the family finally BITES -- rout's root bound moves off 982.486176, the number it
/// had held through GMI, MIR, aggregated MIR, flow covers and generalized flow covers, to 982.498862.
/// **And that is 0.013 against a gap of 95.** The cut is right, the aim is right, and rout's LP point
/// simply is not cover-violating in any way that matters: no cover inequality on these rows separates
/// it by more than a rounding error. **The cover family is not what closes rout, and this is now a
/// measurement rather than a guess.** (What HiGHS gets, it does not get from here.)
pub(crate) fn separate_lifted_cover(model: &Model, x: &[f64], n_rows: usize) -> Vec<Cut> {
    let mut cuts: Vec<Cut> = Vec::new();
    for r in 0..n_rows.min(model.num_rows()) {
        if cuts.len() >= cuts_per_round() {
            break;
        }
        let (coeffs, _lb, ub) = model.row(Row(r as u32));
        if !ub.is_finite() || coeffs.len() < 3 {
            continue;
        }
        if let Some(cut) = lifted_cover_from_row(model, x, coeffs, ub) {
            cuts.push(cut);
        }
    }
    cuts
}

/// The most a set of UNIT-value items of weights `w` (ascending) is worth inside capacity `c`.
/// Exact for max-cardinality: take the lightest first.
fn max_cardinality(sorted_w: &[f64], c: f64) -> Option<usize> {
    if c < -1e-9 {
        return None; // no capacity at all -- the point is infeasible, so it bounds nothing
    }
    let mut left = c;
    let mut n = 0usize;
    for &w in sorted_w {
        if w <= left + 1e-9 {
            left -= w;
            n += 1;
        } else {
            break;
        }
    }
    Some(n)
}

/// The largest lifting space `Π(u_k + 1)` a row may have before `separate_lifted_cover` refuses it
/// — the odometer inside `phi` is that size. 4096 admits a handful of small-bounded integers and
/// rejects the pathological wide-integer rows. See the guard at its use.
const LIFT_SPACE_CAP: u128 = 4096;

fn lifted_cover_from_row(model: &Model, x: &[f64], coeffs: &[(u32, f64)], ub: f64) -> Option<Cut> {
    // Every coefficient non-negative, every column boxed at zero: the derivation leans on both.
    let mut bins: Vec<(u32, f64, f64)> = Vec::new(); // (col, weight, y*)
    let mut gens: Vec<(u32, f64, i64, i64)> = Vec::new(); // (col, weight, ub, reference t*)
    for &(c, a) in coeffs {
        if a <= 0.0 {
            return None;
        }
        let (lo, up) = model.col_bounds(Col(c));
        if lo != 0.0 || !up.is_finite() {
            return None;
        }
        match model.col_kind(Col(c)) {
            ColKind::Binary => bins.push((c, a, x[c as usize].clamp(0.0, 1.0))),
            ColKind::Integer => {
                let u = up.round();
                if !(1.0..=32.0).contains(&u) || (up - u).abs() > 1e-9 {
                    return None; // a wide integer makes the lifting knapsack a real one
                }
                // ⭐ THE REFERENCE FACE IS THE ONE THE RELAXATION IS ON.
                //
                // Separating at `x_G = 0` -- the obvious face -- finds a cover on every one of
                // rout's capacity rows and NOT ONE OF THEM IS VIOLATED, so there is nothing to lift.
                // rout's LP satisfies those rows precisely BY spending the integers; with them at
                // zero the binaries have the whole capacity to themselves and no cover is even tight.
                // The face to separate on is the one the point is standing on.
                let t = (x[c as usize].max(0.0)).floor().min(u) as i64;
                gens.push((c, a, u as i64, t));
            }
            ColKind::Continuous => return None,
        }
    }
    if bins.len() < 2 || gens.is_empty() {
        return None; // an all-binary row is `separate`'s job
    }
    // ODOMETER GUARD. `phi` maximises over every multiplicity vector of the lifted integers, a
    // product `Π(u_k + 1)` — with wide bounds and many integers that explodes (7-8 integers at
    // `u = 32` is 33^8), and there is no deadline inside the closure. This family is for rows with a
    // FEW small-bounded integers (rout: three, each `[0,2]`); refuse a row whose lifting space is
    // large. Sound either way — refusing a row only forgoes a cut.
    let lift_space: u128 = gens
        .iter()
        .try_fold(1u128, |acc, &(_, _, u, _)| acc.checked_mul(u as u128 + 1))
        .unwrap_or(u128::MAX);
    if lift_space > LIFT_SPACE_CAP {
        return None;
    }

    // The capacity the binaries actually face, once the integers have taken their reference share.
    let spent: f64 = gens.iter().map(|g| g.1 * g.3 as f64).sum();
    let cap = ub - spent;
    if cap < 0.0 {
        return None;
    }

    // A COVER AGAINST THAT RESIDUAL CAPACITY. Most-committed binaries first; violated exactly when
    // `Σ_{j∈C} (1 − y*_j) < 1`.
    // A cover `C` is violated iff `Σ_{j∈C} (1 − y*_j) < 1`, so the separation is: reach the capacity
    // while spending as little `1 − y*` as possible. Ranking by `y*` alone ignores what each item
    // BUYS -- the right order is cheapest `1 − y*` PER UNIT OF WEIGHT, so a heavy item that is nearly
    // one is taken before a light item that is merely quite high.
    let mut order: Vec<usize> = (0..bins.len()).collect();
    order.sort_by(|&p, &q| {
        let rp = (1.0 - bins[p].2) / bins[p].1;
        let rq = (1.0 - bins[q].2) / bins[q].1;
        rp.partial_cmp(&rq).unwrap_or(std::cmp::Ordering::Equal)
    });
    let mut cover: Vec<usize> = Vec::new();
    let mut w = 0.0f64;
    for &i in &order {
        cover.push(i);
        w += bins[i].1;
        if w > cap + 1e-9 {
            break;
        }
    }
    if w <= cap + 1e-9 || cover.len() < 2 {
        return None; // the binaries never overshoot the residual: no cover on this face
    }
    let rhs0 = (cover.len() - 1) as f64;
    let lhs0: f64 = cover.iter().map(|&i| bins[i].2).sum();
    if lhs0 <= rhs0 + MIN_VIOLATION {
        return None; // the face cut does not even cut: nothing to lift
    }

    let mut cw: Vec<f64> = cover.iter().map(|&i| bins[i].1).collect();
    cw.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));

    // `Φ`: the most the cut-so-far can be worth when integer `k` is pinned at `tk` -- maximising over
    // every value of the integers ALREADY lifted, with the cover filled in greedily underneath.
    //
    //     Φ(tk) = max { Σ_C y_j + Σ_{i∈L} γ_i·(t_i − t*_i) }
    //             s.t.  Σ_C a_j·y_j + Σ_{i∈L} a_i·t_i + a_k·tk  ≤  ub
    let phi =
        |a_k: f64, tk: i64, lifted: &[(u32, f64, i64, i64, f64)], cw: &[f64]| -> Option<f64> {
            let mut best: Option<f64> = None;
            let mut idx = vec![0i64; lifted.len()];
            loop {
                // (col, weight, ub, t*, gamma)
                let used: f64 = idx
                    .iter()
                    .zip(lifted)
                    .map(|(&t, l)| t as f64 * l.1)
                    .sum::<f64>()
                    + a_k * tk as f64;
                let val: f64 = idx
                    .iter()
                    .zip(lifted)
                    .map(|(&t, l)| (t - l.3) as f64 * l.4)
                    .sum();
                if let Some(n) = max_cardinality(cw, ub - used) {
                    let v = val + n as f64;
                    if best.is_none_or(|b| v > b) {
                        best = Some(v);
                    }
                }
                let mut k = 0;
                while k < lifted.len() {
                    idx[k] += 1;
                    if idx[k] <= lifted[k].2 {
                        break;
                    }
                    idx[k] = 0;
                    k += 1;
                }
                if k == lifted.len() {
                    break;
                }
            }
            best
        };

    // SEQUENTIAL LIFTING FROM A NON-ZERO REFERENCE, so each integer needs a coefficient valid in BOTH
    // directions. Writing `z_k = x_k − t*_k`, validity of `Σ_C y_j + Σ γ_k·z_k ≤ rhs` demands, for
    // every `t_k ∈ [0, u_k]`,  `Φ(t_k) + γ_k·(t_k − t*_k) ≤ rhs`, i.e.
    //
    //     z > 0  (it eats more capacity)   ->   γ_k ≤ (rhs − Φ(t_k)) / z          [an UPPER bound]
    //     z < 0  (it hands capacity back)  ->   γ_k ≥ (Φ(t_k) − rhs) / (−z)       [a LOWER bound]
    //
    // Take the largest admissible `γ_k` -- at the LP point `z* = x*_k − ⌊x*_k⌋ ≥ 0`, so a larger
    // coefficient is a deeper cut. And if the window is EMPTY the cut simply cannot be lifted off its
    // face, and a cut valid only on a face is not valid: abandon it. That check is what keeps this
    // sound, and it is the one an over-eager implementation drops.
    let mut lifted: Vec<(u32, f64, i64, i64, f64)> = Vec::new();
    for &(c, a, u, tstar) in &gens {
        let (mut lo_g, mut up_g) = (f64::NEG_INFINITY, f64::INFINITY);
        for t in 0..=u {
            if t == tstar {
                continue;
            }
            let Some(p) = phi(a, t, &lifted, &cw) else {
                continue; // that value already breaks the row: it constrains nothing
            };
            let z = (t - tstar) as f64;
            if z > 0.0 {
                up_g = up_g.min((rhs0 - p) / z);
            } else {
                lo_g = lo_g.max((p - rhs0) / -z);
            }
        }
        let gamma = if up_g.is_finite() {
            up_g
        } else {
            lo_g.max(0.0)
        };
        if !gamma.is_finite() || gamma < lo_g - 1e-9 {
            return None; // no admissible coefficient: this cut does not leave its face
        }
        lifted.push((c, a, u, tstar, gamma));
    }

    //   Σ_{j∈C} y_j + Σ_k γ_k·(x_k − t*_k) ≤ |C| − 1
    let mut terms: Vec<(Col, f64)> = cover.iter().map(|&i| (Col(bins[i].0), 1.0)).collect();
    let mut rhs = rhs0;
    for l in &lifted {
        if l.4.abs() <= 1e-9 {
            continue;
        }
        terms.push((Col(l.0), l.4));
        rhs += l.4 * l.3 as f64;
    }
    let cut = Cut {
        coeffs: terms,
        lb: f64::NEG_INFINITY,
        ub: rhs,
    };
    clears_min_violation(&cut, x).then_some(cut)
}

mod relax_lift;
pub(crate) use relax_lift::{relax_lift_enabled, separate_relax_lift};

// ---------------------------------------------------------------------------------------------
// CLIQUE CUTS, from the conflict graph of the set-packing/partitioning structure.
// ---------------------------------------------------------------------------------------------

/// How many clique cuts a round may admit. Cliques are the cheapest rows this crate produces --
/// all-ones coefficients over a handful of columns, so they cost the LP almost nothing to carry --
/// and on a set-partitioning model they are the only family with anything to say (air03: GMI
/// separates ZERO cuts on the pure `Σx = 1` rows, and the whole 338864.25 -> 340160 root gap
/// belongs to cliques; HiGHS closes it with 12 cuts). So they get their own budget rather than
/// competing with GMI for the shared four. (Measured on air03: the budget is not what binds --
/// the greedy finds 1-9 violated cliques per vertex, and 12, 24 and 48 give bit-identical bounds.)
const MAX_CLIQUE_PER_ROUND: usize = 12;

pub(crate) fn clique_cuts_per_round() -> usize {
    MAX_CLIQUE_PER_ROUND
}

/// A column belongs to the separation SUPPORT when the LP gives it at least this much. The graph
/// is built over the support only -- air03's rows run to 3,861 columns and its conflict graph over
/// ALL columns would be tens of millions of edges, nearly all of them between columns the point
/// does not use and the separation cannot violate.
const CLIQUE_SUPPORT_EPS: f64 = 1e-6;

/// The most support columns the conflict graph will carry (largest `x` first). Adjacency is an
/// `O(ns²)` bitset pass, so this caps it at ~10⁷ word operations.
const MAX_CLIQUE_SUPPORT: usize = 3072;

/// Per row-side, the most support columns whose PAIRS are enumerated for knapsack-implied
/// conflicts (lane B). The biggest surpluses conflict first, so truncation only forgoes edges.
const MAX_CLIQUE_ROW_SUPPORT: usize = 128;

/// The most members an EXTENDED clique may carry. Extension to maximality is what gives the
/// family its strength (see the note in `separate_clique`), but an air03 packing row is itself a
/// clique of 3,861 columns, and a cut that wide is a row the LP cannot carry -- the pool's nnz cap
/// would throw it away whole. A clique cut is valid at ANY size, so stopping early only forgoes
/// strength it could not have kept anyway. Held under the pool's `MAX_CUT_NNZ` (200) on purpose.
const MAX_CLIQUE_MEMBERS: usize = 96;

/// Separate CLIQUE cuts from the conflict graph implied by the model's rows.
///
/// # Why this family, and why nothing already here can do its job
///
/// A set-partitioning model (air03, air05, mod010: every row `Σ x_j = 1` over binaries) gives the
/// families in this crate nothing to hold on to: there is no knapsack for a cover to overshoot, no
/// continuous column for MIR to round against, and the LP is so degenerate that GMI's tableau cuts
/// move the bound by nothing (air03's trace: "separation took 0.55s for 0 cuts"). What the rows DO
/// say, pairwise, is `x_j + x_k <= 1` -- and the transitive strength of that statement lives in the
/// CONFLICT GRAPH: put an edge between every two binaries that cannot both be 1, and for any clique
/// `Q` of that graph
///
/// ```text
///   Σ_{j∈Q} x_j  <=  1
/// ```
///
/// is valid. The LP cannot see this across rows: `a+b <= 1`, `b+c <= 1`, `a+c <= 1` admits
/// `a = b = c = 1/2`, and the clique `{a,b,c}` cuts that point off by a full 1/2. A violated clique
/// is always a MIX of rows -- one contained in a single satisfied row cannot be violated -- which is
/// exactly why the row list alone is weak and the graph is not.
///
/// # Where the edges come from, exactly
///
/// * **Lane A -- packing rows.** A row whose binary columns all carry the SAME coefficient `v > 0`
///   with `2v > ub` (a set-packing `Σ x <= 1` or partitioning `Σ x = 1` row is `v = ub = 1`) makes
///   every pair of its columns an edge: forcing two on already contributes `2v > ub`, and every
///   other term's least contribution is `>= 0` (`v > 0`, binary `lb >= 0`). The comparisons are
///   f64-EXACT (`a == v`, `2v > ub` -- a power-of-two product), and the adjacency test is "do the
///   two columns share a packing row", a bitset intersection over row indices; no per-row pair
///   enumeration, which matters when one row has 3,861 columns.
/// * **Lane B -- knapsack-implied edges.** For any other row-side `Σ a_j x_j <= b` (a `>=` side is
///   the negated `<=` side), pay every column its LEAST possible contribution over its box (exact
///   rationals; a side with an unbounded column pays ∞ and is skipped) and write
///   `slack = b − Σ_j min_j`. Forcing binary `j` to 1 adds its SURPLUS `s_j = a_j − min_j >= 0`,
///   so `j` and `k` conflict exactly when `s_j + s_k > slack`. Sorted by surplus, a two-pointer
///   enumerates precisely the conflicting pairs in `O(n + edges)` exact comparisons.
///
/// # Exactness is in the ADMISSION, not the search
///
/// The greedy below decides only WHICH cliques to propose; validity never depends on it. A clique
/// inequality is valid iff its members are PAIRWISE in conflict -- that is the entire proof: if no
/// two can be 1 together, at most one is 1 -- and every edge above is established by an exact
/// comparison against the model's own rows and bounds. The emitted cut re-verifies every pair of
/// its members against the graph and is dropped if any fails, and its f64 form (all-ones
/// coefficients, right-hand side 1) is exact by construction: nothing to relax, nothing to trust.
pub(crate) fn separate_clique(model: &Model, x: &[f64], n_rows: usize) -> Vec<Cut> {
    let n_rows = n_rows.min(model.num_rows());
    let is_binary = |c: u32| matches!(model.col_kind(Col(c)), ColKind::Binary);

    // THE SUPPORT: binary columns the point actually uses. Columns at 1 belong in it -- a clique
    // pairing an integral 1 with a fractional 0.6 is violated by 0.6, and perfectly valid.
    let mut support: Vec<usize> = (0..model.num_cols().min(x.len()))
        .filter(|&j| is_binary(j as u32) && x[j] > CLIQUE_SUPPORT_EPS)
        .collect();
    if support.len() < 2 {
        return Vec::new();
    }
    if support.len() > MAX_CLIQUE_SUPPORT {
        support.sort_by(|&a, &b| x[b].partial_cmp(&x[a]).unwrap_or(std::cmp::Ordering::Equal));
        support.truncate(MAX_CLIQUE_SUPPORT);
        support.sort_unstable();
    }
    let ns = support.len();
    let sidx: std::collections::HashMap<u32, usize> = support
        .iter()
        .enumerate()
        .map(|(i, &j)| (j as u32, i))
        .collect();

    // LANE A: the packing rows, found by exact f64 comparison.
    let mut pack: Vec<usize> = Vec::new();
    for r in 0..n_rows {
        let (coeffs, _lb, ub) = model.row(Row(r as u32));
        if coeffs.len() < 2 || !ub.is_finite() {
            continue;
        }
        let v = coeffs[0].1;
        // `2.0 * v` is exact (a power-of-two product), so the overshoot test never rounds.
        if v <= 0.0 || 2.0 * v <= ub {
            continue;
        }
        if coeffs
            .iter()
            .all(|&(c, a)| a == v && is_binary(c) && model.col_bounds(Col(c)).0 >= 0.0)
        {
            pack.push(r);
        }
    }
    // EVERY column's packing-row membership, as a bitset over `pack` indices -- every column, not
    // just the support, because the EXTENSION below asks about columns the point does not use.
    let wr = pack.len().div_ceil(64);
    let ncols = model.num_cols();
    let mut allrow = vec![0u64; ncols * wr];
    for (pi, &r) in pack.iter().enumerate() {
        for &(c, _) in model.row(Row(r as u32)).0 {
            allrow[c as usize * wr + pi / 64] |= 1 << (pi % 64);
        }
    }

    // LANE B: knapsack-implied pair conflicts, in exact rationals.
    let mut pairs: std::collections::HashSet<(u32, u32)> = std::collections::HashSet::new();
    for r in 0..n_rows {
        if pack.contains(&r) {
            continue; // lane A already made every pair an edge
        }
        let (coeffs, lb, ub) = model.row(Row(r as u32));
        if coeffs.len() < 2 {
            continue;
        }
        for (sign, rhs) in [(1.0f64, ub), (-1.0, lb)] {
            if !rhs.is_finite() {
                continue;
            }
            let Some(rhs) = exact(sign * rhs) else {
                continue;
            };
            // Pay every column its least contribution; collect each support binary's surplus.
            let mut minact = BigRational::zero();
            let mut surplus: Vec<(usize, BigRational)> = Vec::new();
            let mut ok = true;
            for &(c, raw) in coeffs {
                let Some(a) = exact(sign * raw) else {
                    ok = false;
                    break;
                };
                if a.is_zero() {
                    continue;
                }
                let (lo, up) = model.col_bounds(Col(c));
                let bnd = if a.is_positive() { lo } else { up };
                if !bnd.is_finite() {
                    ok = false; // an unbounded least contribution: this side proves nothing
                    break;
                }
                let Some(bnd) = exact(bnd) else {
                    ok = false;
                    break;
                };
                let m = &a * &bnd;
                if let Some(&si) = sidx.get(&c) {
                    // Forcing the column to 1 adds `a − m` over its floor. Support implies the
                    // binary's upper bound is 1, so 1 is inside its box and the forcing is real.
                    let s = &a - &m;
                    if s.is_positive() {
                        surplus.push((si, s));
                    }
                }
                minact += m;
            }
            if !ok || surplus.len() < 2 {
                continue;
            }
            let slack = &rhs - &minact;
            if slack.is_negative() {
                // The row is violated at its own box minimum: the node is infeasible, and an
                // infeasibility is the LP's news to break, not a cut's.
                continue;
            }
            surplus.sort_by(|a, b| a.1.cmp(&b.1));
            if surplus.len() > MAX_CLIQUE_ROW_SUPPORT {
                // Keep the LARGEST surpluses: they are the ones that conflict at all.
                let cut_from = surplus.len() - MAX_CLIQUE_ROW_SUPPORT;
                // FORGONE COST. The doc claims "the biggest surpluses conflict first, so
                // truncation only forgoes edges" — but conflict is s_j + s_k > slack, so a
                // SMALL surplus still conflicts with a large one. Count the dropped
                // columns that PROVABLY carried an edge: ascending order makes that a
                // suffix of the drained prefix. A missing lane-B edge does not merely
                // shrink the search — `adjacent` is the ground-truth oracle and the
                // emitted cut re-verifies every pair against it, so a VALID clique can be
                // rejected at admission. `thresh` may be negative, in which case every
                // dropped column conflicted: that reading refutes the doc outright and is
                // the number worth having. O(log cut_from) rational compares against the
                // full rational sort already performed on the line above.
                let thresh = &slack - &surplus[surplus.len() - 1].1;
                let lost = cut_from - surplus[..cut_from].partition_point(|(_, s)| s <= &thresh);
                crate::sepstat::gate_charge(crate::sepstat::GATE_CLIQUE_ROW_SUPPORT, lost as u64);
                surplus.drain(..cut_from);
            }
            // Two pointers over ascending surpluses: `(p, hi)` conflicts iff s_p + s_hi > slack,
            // and the threshold only moves right as `hi` moves left.
            let mut lo_i = 0usize;
            for hi in (1..surplus.len()).rev() {
                while lo_i < hi && &surplus[lo_i].1 + &surplus[hi].1 <= slack {
                    lo_i += 1;
                }
                if lo_i >= hi {
                    break;
                }
                for p in lo_i..hi {
                    let (a, b) = (surplus[p].0 as u32, surplus[hi].0 as u32);
                    pairs.insert((a.min(b), a.max(b)));
                }
            }
        }
    }

    // THE ADJACENCY ORACLE on original columns: lane A (share a packing row) OR lane B (a pair
    // edge, which only support columns can have). This is the ground truth the admission check
    // runs against.
    let adjacent = |c1: usize, c2: usize| -> bool {
        if c1 == c2 {
            return false;
        }
        if wr > 0 && (0..wr).any(|w| allrow[c1 * wr + w] & allrow[c2 * wr + w] != 0) {
            return true;
        }
        match (sidx.get(&(c1 as u32)), sidx.get(&(c2 as u32))) {
            (Some(&p), Some(&q)) => {
                let (p, q) = (p as u32, q as u32);
                pairs.contains(&(p.min(q), p.max(q)))
            }
            _ => false,
        }
    };

    // THE ADJACENCY BITSETS over the support, for the greedy growth.
    let words = ns.div_ceil(64);
    let mut adj = vec![0u64; ns * words];
    let mut any_edge = false;
    if wr > 0 {
        for p in 0..ns {
            let cp = support[p];
            if allrow[cp * wr..(cp + 1) * wr].iter().all(|&w| w == 0) {
                continue;
            }
            for q in (p + 1)..ns {
                let cq = support[q];
                let hit = (0..wr).any(|w| allrow[cp * wr + w] & allrow[cq * wr + w] != 0);
                if hit {
                    adj[p * words + q / 64] |= 1 << (q % 64);
                    adj[q * words + p / 64] |= 1 << (p % 64);
                    any_edge = true;
                }
            }
        }
    }
    for &(p, q) in &pairs {
        let (p, q) = (p as usize, q as usize);
        adj[p * words + q / 64] |= 1 << (q % 64);
        adj[q * words + p / 64] |= 1 << (p % 64);
        any_edge = true;
    }
    if !any_edge {
        return Vec::new();
    }

    // GREEDY GROWTH around every support node, heaviest first. The candidate set starts as the
    // seed's neighbourhood and is intersected with each member's as it joins, so membership in
    // `cand` IS pairwise adjacency to everything taken so far -- one descending sweep is the greedy.
    let mut order: Vec<usize> = (0..ns).collect();
    order.sort_by(|&p, &q| {
        x[support[q]]
            .partial_cmp(&x[support[p]])
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    let bit = |set: &[u64], i: usize| set[i / 64] >> (i % 64) & 1 == 1;
    let mut seen: std::collections::HashSet<Vec<u32>> = std::collections::HashSet::new();
    // (efficacy of the un-extended clique, members as original columns)
    let mut grown: Vec<(f64, Vec<u32>)> = Vec::new();
    for &s in &order {
        if adj[s * words..(s + 1) * words].iter().all(|&w| w == 0) {
            continue;
        }
        let mut cand: Vec<u64> = adj[s * words..(s + 1) * words].to_vec();
        let mut members: Vec<usize> = vec![s];
        let mut weight = x[support[s]];
        for &t in &order {
            if t != s && bit(&cand, t) {
                members.push(t);
                weight += x[support[t]];
                for w in 0..words {
                    cand[w] &= adj[t * words + w];
                }
            }
        }
        if weight <= 1.0 + MIN_VIOLATION {
            continue;
        }
        let mut cols: Vec<u32> = members.iter().map(|&i| support[i] as u32).collect();
        cols.sort_unstable();
        if !seen.insert(cols.clone()) {
            continue;
        }
        // The efficacy of the un-extended clique: extension adds zero-valued columns, which
        // cannot change what the cut cuts TODAY, only what it forbids tomorrow -- so the ranking
        // is decided before the extension pads the norm.
        #[allow(clippy::cast_precision_loss)]
        let eff = (weight - 1.0) / (cols.len() as f64).sqrt();
        grown.push((eff, cols));
    }

    grown.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap_or(std::cmp::Ordering::Equal));
    grown.truncate(clique_cuts_per_round());

    // EXTEND THE WINNERS TOWARD MAXIMALITY, and this is where the family's strength actually
    // lives. An un-extended clique names only the columns the LP is USING, and a degenerate
    // partitioning LP answers it by shifting the same weight onto sibling columns of the same
    // rows -- a new vertex, the same objective, another round. Measured on air03: support-only
    // cliques move the root bound ~0.7 per round against a gap of 1,296, a hundred-round crawl;
    // extended, the same 14 rounds close twice as much. A maximal clique names the siblings too,
    // so the retreat is cut off before it is tried. Any clique is valid at any size, so the
    // extension is bounded (`MAX_CLIQUE_MEMBERS`) and greedy: a zero column joins when it
    // conflicts with every member so far.
    let mut out: Vec<Cut> = Vec::new();
    let mut emitted: std::collections::HashSet<Vec<u32>> = std::collections::HashSet::new();
    for (_, mut cols) in grown {
        if cols.len() < MAX_CLIQUE_MEMBERS {
            for c in 0..ncols {
                let cu = c as u32;
                if !is_binary(cu)
                    || x.get(c).copied().unwrap_or(0.0) > CLIQUE_SUPPORT_EPS // support: settled by the growth
                    || model.col_bounds(Col(cu)).1 <= 0.0 // fixed off: nothing to forbid
                    || cols.contains(&cu)
                {
                    continue;
                }
                if cols.iter().all(|&q| adjacent(c, q as usize)) {
                    cols.push(cu);
                    if cols.len() >= MAX_CLIQUE_MEMBERS {
                        break;
                    }
                }
            }
            cols.sort_unstable();
        }
        // ADMISSION: the inequality is valid iff its members are PAIRWISE in conflict -- that is
        // the whole proof -- so exactly that is re-checked against the oracle the exact
        // comparisons built. The growth and the extension both guarantee it; neither is trusted.
        let pairwise = cols.iter().enumerate().all(|(i, &p)| {
            cols[i + 1..]
                .iter()
                .all(|&q| adjacent(p as usize, q as usize))
        });
        if !pairwise || !emitted.insert(cols.clone()) {
            continue;
        }
        out.push(Cut {
            coeffs: cols.into_iter().map(|c| (Col(c), 1.0)).collect(),
            lb: f64::NEG_INFINITY,
            ub: 1.0,
        });
    }
    out
}

// ---------------------------------------------------------------------------------------------
// ODD-HOLE (ODD-CYCLE) CUTS, the set-packing facets clique cuts cannot express.
// ---------------------------------------------------------------------------------------------

/// A support column must be strictly fractional by this much to sit on an odd cycle. An odd hole
/// is violated only THROUGH fractional vertices: an integral 1 makes an incident edge weight
/// `1 − 1 − x_j < 0` (breaks the non-negative shortest-path search), and an integral 0 makes every
/// incident edge weight ~1 (a cycle through it can never drop below 1).
const ODD_CYCLE_FRAC_EPS: f64 = 1e-6;

/// The most fractional support columns the odd-cycle search will carry (closest to 1/2 first). The
/// doubled-graph Dijkstra is `O(sources · E log V)`, so this caps the graph.
const ODD_CYCLE_MAX_SUPPORT: usize = 2048;

/// The most Dijkstra SOURCES tried (vertices closest to 1/2 first — the lightest edges, where a
/// violated cycle is likeliest). Each source is one full shortest-odd-walk search.
const ODD_CYCLE_MAX_SOURCES: usize = 192;

/// The most odd-hole cuts a round may admit.
const ODD_CYCLE_MAX_CUTS: usize = 24;

/// The most members an odd-hole cut may carry (a long cycle is a wide, weak row the pool evicts).
const ODD_CYCLE_MAX_LEN: usize = 96;

/// The most EXTERNAL variables a lifted odd hole may absorb. Lifting turns the bare hole into a
/// wheel/facet, but every term is fill the node LP re-solves, so it is bounded like the hole length.
const ODD_LIFT_MAX_TERMS: usize = 48;

/// A total order on the non-negative, finite edge-distances the odd-cycle Dijkstra produces, so
/// they can key a `BinaryHeap`. Distances here are sums of `max(0, 1 − x_i − x_j)` — never NaN.
#[derive(Copy, Clone, PartialEq)]
struct OrdF64(f64);
impl Eq for OrdF64 {}
impl PartialOrd for OrdF64 {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for OrdF64 {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0
            .partial_cmp(&other.0)
            .unwrap_or(std::cmp::Ordering::Equal)
    }
}

/// Separate ODD-HOLE (odd-cycle) inequalities from the conflict graph of the set-partitioning rows.
///
/// # Why this family, and why the cliques and zero-half cannot do its job
///
/// On the conflict graph `G` (an edge between two binaries that cannot both be 1), a CLIQUE `Q`
/// gives `Σ_Q x ≤ 1`. But an ODD HOLE — a chordless odd cycle `C = v_0 … v_{2k}` where only
/// CONSECUTIVE vertices conflict — gives a facet the cliques miss:
///
/// ```text
///   Σ_{v∈C} x_v  ≤  k          (k = (|C|−1)/2)
/// ```
///
/// Its proof is the independence number of an odd cycle: a feasible 0/1 point restricted to `C` is
/// an independent set of the cycle (consecutive vertices conflict, so at most one of each pair is
/// 1), and `C_{2k+1}` admits at most `k`. The five-cycle `a-b-c-d-e-a` at `x = 1/2` everywhere is
/// the canonical case: every clique `{v_i, v_{i+1}}` is satisfied (`1/2 + 1/2 = 1`), yet
/// `Σ x = 5/2 > 2 = k` — the hole cuts it off and no clique can. Zero-half ({0,1/2}-CG) cuts on the
/// MODEL ROWS also miss it: the hole is a parity combination of the pairwise EDGE inequalities, and
/// a set-partition row `Σ x = 1` is not that edge — measured on air05, `separate_zero_half` returns
/// zero cuts at every root vertex while these holes (if any) live on the conflict graph.
///
/// # Separation (Grötschel–Lovász–Schrijver), exactly
///
/// Weight each edge `(i,j)` by `w_ij = 1 − x_i − x_j ≥ 0` (non-negative for a packing-row edge at
/// any LP-feasible point: `x_i + x_j ≤ Σ_row x = 1`). For an odd cycle `C`,
/// `Σ_{edges} w = |C| − 2 Σ_{v∈C} x_v`, so the hole is VIOLATED iff `Σ_{edges} w < 1`. The
/// minimum-weight odd cycle through a vertex `s` is the shortest path from `s` to its twin in the
/// DOUBLED graph (two copies of every vertex; edge `(i,j)` becomes `(iᵉ,jᵒ)` and `(iᵒ,jᵉ)`); a
/// path across the parity layers is an odd closed walk. Non-negative weights ⇒ Dijkstra.
///
/// # Exactness is in the ADMISSION, not the search
///
/// The float weights decide only WHICH cycle to propose. The emitted inequality is valid iff its
/// consecutive members are PAIRWISE in conflict — exactly that is re-checked against the same exact
/// packing-row oracle the cliques use, and the cycle must be simple and odd. The cut's f64 form
/// (all-ones coefficients, integer right-hand side `k`) is exact by construction. This is a
/// SET-PARTITIONING family: it takes edges only from packing rows (lane A of `separate_clique`),
/// which on `Σ x = 1` models is the entire conflict graph.
/// Max independent set of the odd cycle `C_l` after DELETING the vertices flagged in `mask`
/// (unit weights). The survivors form a union of arcs (paths); the MIS of a path on `g` vertices is
/// `⌈g/2⌉`. This deliberately IGNORES any chords of the cycle, so the value is an UPPER BOUND on the
/// true induced MIS — exactly what a SOUND (never over-lifting) sequential coefficient needs.
fn path_mis_after_removal(l: usize, mask: u128) -> usize {
    let removed_count = mask.count_ones() as usize;
    if removed_count == 0 {
        return (l - 1) / 2; // odd cycle: independence number is (l−1)/2
    }
    if removed_count >= l {
        return 0;
    }
    let removed: Vec<usize> = (0..l).filter(|&i| mask & (1u128 << i) != 0).collect();
    let t = removed.len();
    let mut total = 0usize;
    for i in 0..t {
        let a = removed[i];
        // Arc AFTER `a`, up to the next removed vertex (cyclically). Its vertex count:
        let gap = if i + 1 < t {
            removed[i + 1] - a - 1
        } else {
            // wrap-around arc: (a+1 .. l-1) then (0 .. removed[0]-1)
            (l - a - 1) + removed[0]
        };
        total += gap.div_ceil(2);
    }
    total
}

/// SEQUENTIALLY LIFT the odd-hole inequality `Σ_{i∈C} x_i ≤ k` (k = (|C|−1)/2) with external
/// variables, turning the bare hole into a wheel/near-facet. `cyc` is the cycle IN ORDER
/// (consecutive columns conflict; the last wraps to the first) and `pack` the packing-row indices
/// whose `Σx ≤ ub, 2·coeff > ub` shape is the conflict-graph oracle.
///
/// For a candidate `w ∉ C`, standard sequential lifting sets `α_w = k − Z` where
/// `Z = max{ Σ current-LHS : x independent, x_w = 1 }`. With `x_w = 1` every conflict-neighbour of
/// `w` is forced to 0, so `Z` is the weighted MIS of the survivors. We upper-bound `Z` by
/// `path_mis_after_removal` over the cycle part (ignoring chords) PLUS the full coefficient sum of
/// everything lifted so far (ignoring their conflicts) — any valid UPPER bound `Z⁺ ≥ Z` yields a
/// coefficient `α_w = k − Z⁺ ≤ k − Z` that UNDER-lifts, so the lifted inequality is always IMPLIED
/// by set-packing validity: `Σ_C x_i + Σ lifted ≤ k` holds at every integer feasible point. The
/// enumeration test `lifted_odd_hole_cuts_never_remove_an_integer_point` brute-forces this.
///
/// Returns the extra `(column, coefficient ≥ 1)` terms only.
fn lift_odd_hole(model: &Model, x: &[f64], cyc: &[usize], pack: &[usize]) -> Vec<(usize, i64)> {
    let l = cyc.len();
    // Bit masks are `u128`; `ODD_CYCLE_MAX_LEN ≤ 96 < 128` keeps every position addressable.
    if l < 5 || l.is_multiple_of(2) || l > 128 {
        return Vec::new();
    }
    let k = ((l - 1) / 2) as i64;
    let pos: std::collections::HashMap<u32, usize> = cyc
        .iter()
        .enumerate()
        .map(|(i, &c)| (c as u32, i))
        .collect();

    // For each external column, the mask of cycle POSITIONS it conflicts with. A packing row that
    // holds cycle members at positions `cvmask` makes every OTHER column in the row conflict with
    // all of them (they cannot both be 1 under `Σx ≤ ub`).
    let mut neigh: std::collections::HashMap<u32, u128> = std::collections::HashMap::new();
    for &r in pack {
        let (coeffs, _lb, _ub) = model.row(Row(r as u32));
        let mut cvmask: u128 = 0;
        for &(c, _) in coeffs {
            if let Some(&p) = pos.get(&c) {
                cvmask |= 1u128 << p;
            }
        }
        if cvmask == 0 {
            continue;
        }
        for &(c, _) in coeffs {
            if pos.contains_key(&c) {
                continue; // cycle members are not lift candidates
            }
            *neigh.entry(c).or_insert(0) |= cvmask;
        }
    }
    if neigh.is_empty() {
        return Vec::new();
    }

    // Best hubs first: most cycle-conflicts (largest lift), then most fractional (deepest at x*).
    let mut cands: Vec<(u32, u128)> = neigh.into_iter().collect();
    cands.sort_by(|a, b| {
        b.1.count_ones()
            .cmp(&a.1.count_ones())
            .then_with(|| {
                let xa = x.get(a.0 as usize).copied().unwrap_or(0.0);
                let xb = x.get(b.0 as usize).copied().unwrap_or(0.0);
                xb.partial_cmp(&xa).unwrap_or(std::cmp::Ordering::Equal)
            })
            .then_with(|| a.0.cmp(&b.0))
    });

    let mut lifted: Vec<(usize, i64)> = Vec::new();
    let mut lifted_sum: i64 = 0;
    for (c, mask) in cands {
        if lifted_sum >= k {
            break; // the RHS budget is spent; no further term can be positive
        }
        let pmis = path_mis_after_removal(l, mask) as i64;
        let alpha = k - pmis - lifted_sum;
        if alpha >= 1 {
            lifted.push((c as usize, alpha));
            lifted_sum += alpha;
            if lifted.len() >= ODD_LIFT_MAX_TERMS {
                break;
            }
        }
    }
    lifted
}

pub(crate) fn separate_odd_cycle(model: &Model, x: &[f64], n_rows: usize) -> Vec<Cut> {
    use std::cmp::Reverse;
    use std::collections::BinaryHeap;

    let n_rows = n_rows.min(model.num_rows());
    let is_binary = |c: u32| matches!(model.col_kind(Col(c)), ColKind::Binary);

    // FRACTIONAL support, ranked by closeness to 1/2 (the lightest edges).
    let mut support: Vec<usize> = (0..model.num_cols().min(x.len()))
        .filter(|&j| {
            is_binary(j as u32) && x[j] > ODD_CYCLE_FRAC_EPS && x[j] < 1.0 - ODD_CYCLE_FRAC_EPS
        })
        .collect();
    if support.len() < 5 {
        return Vec::new(); // no room for an odd cycle of length ≥ 5
    }
    if support.len() > ODD_CYCLE_MAX_SUPPORT {
        support.sort_by(|&a, &b| {
            (x[a] - 0.5)
                .abs()
                .partial_cmp(&(x[b] - 0.5).abs())
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        support.truncate(ODD_CYCLE_MAX_SUPPORT);
    }
    support.sort_unstable();
    let ns = support.len();
    let sidx: std::collections::HashMap<u32, usize> = support
        .iter()
        .enumerate()
        .map(|(i, &j)| (j as u32, i))
        .collect();

    // LANE A packing rows (`Σ v·x ≤ ub`, all coeffs `v`, `2v > ub`), by exact f64 comparison — the
    // same test `separate_clique` uses. On a pure set-partitioning model this is every row.
    let mut pack: Vec<usize> = Vec::new();
    for r in 0..n_rows {
        let (coeffs, _lb, ub) = model.row(Row(r as u32));
        if coeffs.len() < 2 || !ub.is_finite() {
            continue;
        }
        let v = coeffs[0].1;
        if v <= 0.0 || 2.0 * v <= ub {
            continue;
        }
        if coeffs
            .iter()
            .all(|&(c, a)| a == v && is_binary(c) && model.col_bounds(Col(c)).0 >= 0.0)
        {
            pack.push(r);
        }
    }
    if pack.is_empty() {
        return Vec::new();
    }

    // Packing-row membership per support column, as a bitset over `pack`.
    let wr = pack.len().div_ceil(64);
    let mut rowbits = vec![0u64; ns * wr];
    for (pi, &r) in pack.iter().enumerate() {
        for &(c, _) in model.row(Row(r as u32)).0 {
            if let Some(&si) = sidx.get(&c) {
                rowbits[si * wr + pi / 64] |= 1u64 << (pi % 64);
            }
        }
    }
    let share_row = |p: usize, q: usize| -> bool {
        (0..wr).any(|w| rowbits[p * wr + w] & rowbits[q * wr + w] != 0)
    };

    // WEIGHTED ADJACENCY over the support: edge `(p,q)` iff they share a packing row, weight
    // `1 − x_p − x_q` (clamped non-negative for the shortest-path search).
    let mut adj: Vec<Vec<(u32, f64)>> = vec![Vec::new(); ns];
    let mut n_edges = 0usize;
    for p in 0..ns {
        if rowbits[p * wr..(p + 1) * wr].iter().all(|&w| w == 0) {
            continue;
        }
        for q in (p + 1)..ns {
            if share_row(p, q) {
                let w = (1.0 - x[support[p]] - x[support[q]]).max(0.0);
                adj[p].push((q as u32, w));
                adj[q].push((p as u32, w));
                n_edges += 1;
            }
        }
    }
    if n_edges == 0 {
        return Vec::new();
    }

    // SOURCES: the most-fractional vertices first (lightest incident edges), bounded.
    let mut sources: Vec<usize> = (0..ns).filter(|&p| !adj[p].is_empty()).collect();
    sources.sort_by(|&a, &b| {
        (x[support[a]] - 0.5)
            .abs()
            .partial_cmp(&(x[support[b]] - 0.5).abs())
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    let max_sources = ODD_CYCLE_MAX_SOURCES;
    sources.truncate(max_sources);

    // Doubled graph: node `p` is the EVEN copy of support vertex `p`, node `p + ns` the ODD copy.
    // Edge `(p,q,w)` links `(pᵉ,qᵒ)`, `(qᵉ,pᵒ)`, `(pᵒ,qᵉ)`, `(qᵒ,pᵉ)` — a walk that changes layer
    // each step, so a path `sᵉ → sᵒ` is an odd closed walk through `s`.
    let vn = 2 * ns;
    let mut best: f64;
    let mut min_dist = f64::INFINITY;
    let mut n_violated = 0usize;
    let mut raw: Vec<(f64, Vec<usize>)> = Vec::new(); // (edge-weight sum, base-vertex cycle)
    let mut seen: std::collections::HashSet<Vec<u32>> = std::collections::HashSet::new();

    let mut dist = vec![f64::INFINITY; vn];
    let mut prev = vec![usize::MAX; vn];
    for &s in &sources {
        // Dijkstra from sᵉ (= s) to sᵒ (= s + ns).
        for d in dist.iter_mut() {
            *d = f64::INFINITY;
        }
        let target = s + ns;
        dist[s] = 0.0;
        let mut heap: BinaryHeap<Reverse<(OrdF64, usize)>> = BinaryHeap::new();
        heap.push(Reverse((OrdF64(0.0), s)));
        while let Some(Reverse((OrdF64(d), u))) = heap.pop() {
            if d > dist[u] + 1e-12 {
                continue;
            }
            if u == target {
                break;
            }
            let base = if u < ns { u } else { u - ns };
            let to_odd = u < ns; // even node → odd copies of neighbours
            for &(q, w) in &adj[base] {
                let q = q as usize;
                let vnode = if to_odd { q + ns } else { q };
                let nd = d + w;
                if nd + 1e-12 < dist[vnode] {
                    dist[vnode] = nd;
                    prev[vnode] = u;
                    heap.push(Reverse((OrdF64(nd), vnode)));
                }
            }
        }
        best = dist[target];
        if best < min_dist {
            min_dist = best;
        }
        if best.partial_cmp(&(1.0 - MIN_VIOLATION)) != Some(std::cmp::Ordering::Less) {
            continue;
        }
        n_violated += 1;
        // Reconstruct the doubled-graph path, map to base vertices.
        let mut walk: Vec<usize> = Vec::new();
        let mut node = target;
        let mut guard = 0usize;
        while node != usize::MAX && guard <= vn {
            walk.push(if node < ns { node } else { node - ns });
            if node == s {
                break;
            }
            node = prev[node];
            guard += 1;
        }
        walk.reverse();
        // `walk` is s, …, s (closed). Drop the trailing duplicate of the start for the cycle set.
        if walk.len() < 6 || walk.first() != walk.last() {
            continue;
        }
        walk.pop(); // remove closing duplicate
        let len = walk.len();
        if len < 5 || len.is_multiple_of(2) {
            continue; // need a simple ODD cycle of length ≥ 5
        }
        // The ODD_CYCLE_MAX_LEN arm moved DOWN, past the simplicity dedup, the
        // consecutive-conflict re-verification and the `seen` dedup, so the census
        // charges only holes that are genuinely cuts. Output-identical: a duplicate
        // `seen` key is the same COLUMN SET and therefore the same length, so a long
        // cycle entering `seen` can never displace a short one.
        // Simplicity: the shortest odd walk need not be a simple cycle; only emit when it is.
        let mut sorted = walk.clone();
        sorted.sort_unstable();
        sorted.dedup();
        if sorted.len() != len {
            continue;
        }
        // Re-verify every CONSECUTIVE pair is a real conflict (share a packing row) — the whole
        // validity proof, re-checked against the exact oracle.
        let ok = (0..len).all(|i| share_row(walk[i], walk[(i + 1) % len]));
        if !ok {
            continue;
        }
        // ORDERED cycle (walk order): consecutive columns conflict, last wraps to first.
        // Lifting needs this adjacency; the dedup key is the SORTED column set.
        let ordered: Vec<usize> = walk.iter().map(|&i| support[i]).collect();
        let mut key: Vec<u32> = ordered.iter().map(|&c| c as u32).collect();
        key.sort_unstable();
        if !seen.insert(key) {
            continue;
        }
        if len > ODD_CYCLE_MAX_LEN {
            // FORGONE COST. A violated, simple, re-verified, non-duplicate odd hole
            // refused for length. Depth = violation/‖a‖ = ((1 − best)/2)/√len — the same
            // quantity the pool's efficacy floor tests (bab.rs, MEASURED 2026-07-22), so
            // the charge is directly comparable to the doc's "wide, weak row" claim.
            // Edge weights are CLAMPED non-negative, so `best` over-states the walk
            // weight and this charge UNDER-states the true violation: conservative by
            // construction. Value lies in [0, 500_000].
            crate::sepstat::gate_charge(
                crate::sepstat::GATE_ODD_CYCLE_LEN,
                ((((1.0 - best) / 2.0) / (len as f64).sqrt()) * 1e6) as u64,
            );
            continue;
        }
        raw.push((best, ordered));
    }

    if crate::debug_flags::milp_debug_flags().trace {
        eprintln!(
            "--trace odd_cycle: ns={ns} edges={n_edges} sources={} min_odd_walk={min_dist:.4} violated_walks={n_violated} valid_cuts={}",
            sources.len(),
            raw.len(),
        );
    }

    // Build cuts: Σ_{v∈C} x_v ≤ (|C|−1)/2, LIFTED with external variables (each a sound sequential
    // lift — see `lift_odd_hole`), deepest first, bounded. `--no-odd-lift` drops back to the
    // bare hole. The lifted row DOMINATES the bare one (adds non-negative terms at the same RHS), so
    // it is at least as deep at `x*` and strictly stronger in the tree.
    let lift_on = crate::tune::caller_flag(crate::tune::Knob::NoOddLift).map_or(true, |no| !no);
    let mut cuts: Vec<Cut> = Vec::new();
    for (_w, cyc) in raw {
        let k = (cyc.len() - 1) / 2;
        let mut coeffs: Vec<(Col, f64)> = cyc.iter().map(|&c| (Col(c as u32), 1.0)).collect();
        if lift_on {
            for (col, a) in lift_odd_hole(model, x, &cyc, &pack) {
                coeffs.push((Col(col as u32), a as f64));
            }
        }
        let cut = Cut {
            coeffs,
            lb: f64::NEG_INFINITY,
            ub: k as f64,
        };
        if clears_min_violation(&cut, x) {
            cuts.push(cut);
        }
    }
    cuts.sort_by(|a, b| {
        efficacy(b, x)
            .partial_cmp(&efficacy(a, x))
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    let max_cuts = ODD_CYCLE_MAX_CUTS;
    cuts.truncate(max_cuts);
    cuts
}

#[cfg(test)]
mod clique_tests {
    use super::*;
    use crate::model::Sense;

    /// A CLIQUE CUT MUST NOT DELETE AN INTEGER POINT. Brute-forced, like every family here.
    ///
    /// The one place this family can go wrong is an EDGE that is not real -- a pair the arithmetic
    /// claims cannot both be 1 when the model admits a point with both at 1. Any such point is in
    /// the enumeration below, so a false edge fails the assert. (Checked by breaking it on
    /// purpose: relax the lane-B conflict test to `s_j + s_k >= slack` -- off by one closed
    /// bound -- and this test fails in its first case, "activity 2 exceeds its bound 1". A guard
    /// that cannot catch the off-by-one is not guarding the part that matters.)
    ///
    /// The models mix the two edge sources deliberately: packing AND partitioning rows over random
    /// subsets (lane A), and small-integer knapsack rows (lane B), so cliques that mix lanes are
    /// exercised too.
    #[test]
    fn clique_cuts_never_remove_an_integer_point() {
        let mut seed = 0xC11C_2026_0714_u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };

        let mut fired = 0usize;
        for _case in 0..400 {
            const NB: usize = 10;
            let mut m = Model::new();
            let cols: Vec<Col> = (0..NB).map(|_| m.add_binary_col()).collect();
            let mut rows: Vec<(Vec<f64>, f64, f64)> = Vec::new();

            // Packing / partitioning rows over random subsets (lane A).
            for _ in 0..3 {
                let k = 2 + (rnd() % 4) as usize;
                let mut sub: Vec<usize> = (0..NB).collect();
                for i in 0..k {
                    let j = i + (rnd() as usize) % (NB - i);
                    sub.swap(i, j);
                }
                sub.truncate(k);
                let eq = rnd() % 3 == 0;
                let lo = if eq { 1.0 } else { f64::NEG_INFINITY };
                let terms: Vec<(Col, f64)> = sub.iter().map(|&j| (cols[j], 1.0)).collect();
                m.add_row(lo, 1.0, &terms);
                let mut a = vec![0.0; NB];
                for &j in &sub {
                    a[j] = 1.0;
                }
                rows.push((a, lo, 1.0));
            }
            // Small-integer knapsack rows (lane B), both orientations.
            for _ in 0..2 {
                let a: Vec<f64> = (0..NB).map(|_| (rnd() % 9 - 2) as f64).collect();
                if a.iter().all(|&v| v == 0.0) {
                    continue;
                }
                let hi = (1 + rnd() % 8) as f64;
                let lo = if rnd() % 2 == 0 {
                    hi - (1 + rnd() % 6) as f64
                } else {
                    f64::NEG_INFINITY
                };
                let terms: Vec<(Col, f64)> = cols
                    .iter()
                    .zip(&a)
                    .filter(|(_, &v)| v != 0.0)
                    .map(|(&c, &v)| (c, v))
                    .collect();
                m.add_row(lo, hi, &terms);
                rows.push((a, lo, hi));
            }
            m.set_objective(&[(cols[0], 1.0)], Sense::Minimize);

            // An arbitrary interior point: validity may not depend on WHERE it was separated from.
            let x: Vec<f64> = (0..NB).map(|_| (rnd() % 21) as f64 / 20.0).collect();
            let cuts = separate_clique(&m, &x, m.num_rows());
            fired += cuts.len();

            // Every 0/1 point the MODEL admits must satisfy every cut.
            for code in 0..(1i64 << NB) {
                let p: Vec<f64> = (0..NB).map(|j| ((code >> j) & 1) as f64).collect();
                let feasible = rows.iter().all(|(a, lo, hi)| {
                    let act: f64 = a.iter().zip(&p).map(|(&c, &v)| c * v).sum();
                    act >= lo - 1e-9 && act <= hi + 1e-9
                });
                if !feasible {
                    continue;
                }
                for c in &cuts {
                    let act: f64 = c.coeffs.iter().map(|&(col, a)| a * p[col.index()]).sum();
                    assert!(
                        act <= c.ub + 1e-9,
                        "a clique cut deleted the integer point {p:?} -- \
                         activity {act} exceeds its bound {}",
                        c.ub
                    );
                }
            }
        }
        assert!(
            fired > 0,
            "no clique cut was ever separated: the guard is vacuous"
        );
    }

    /// THE POINT OF THE FAMILY: a violated clique MIXES rows. Three pairwise-packing rows admit
    /// the LP point (1/2, 1/2, 1/2); each row is satisfied, and only the cross-row clique
    /// `a + b + c <= 1` cuts it -- by a full 1/2. If this stops separating, the family is dead
    /// even if it is still "valid".
    #[test]
    fn clique_separation_mixes_rows() {
        let mut m = Model::new();
        let a = m.add_binary_col();
        let b = m.add_binary_col();
        let c = m.add_binary_col();
        m.add_row(f64::NEG_INFINITY, 1.0, &[(a, 1.0), (b, 1.0)]);
        m.add_row(f64::NEG_INFINITY, 1.0, &[(b, 1.0), (c, 1.0)]);
        m.add_row(f64::NEG_INFINITY, 1.0, &[(a, 1.0), (c, 1.0)]);
        m.set_objective(&[(a, 1.0)], Sense::Minimize);

        let x = vec![0.5, 0.5, 0.5];
        let cuts = separate_clique(&m, &x, m.num_rows());
        assert!(
            cuts.iter()
                .any(|c| c.coeffs.len() == 3 && c.ub == 1.0 && violation(c, &x) > 0.49),
            "the triangle clique was not separated"
        );
    }

    /// AN ODD-HOLE CUT MUST NOT DELETE AN INTEGER POINT. Brute-forced, like every family here.
    ///
    /// The one place this family can go wrong is emitting `Σ_C x ≤ (|C|−1)/2` for a vertex set that
    /// is NOT a genuine odd cycle of the conflict graph — a non-edge between two consecutive members
    /// would make the bound too tight and delete a feasible independent set. Every 0/1 point the
    /// model admits is enumerated below, so any bad cut fails the assert. Packing/partitioning rows
    /// over random subsets give the conflict graph its cycles.
    #[test]
    fn odd_cycle_cuts_never_remove_an_integer_point() {
        let mut seed = 0x0DDC_2026_0718_u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };

        let mut fired = 0usize;
        for _case in 0..600 {
            const NB: usize = 12;
            let mut m = Model::new();
            let cols: Vec<Col> = (0..NB).map(|_| m.add_binary_col()).collect();
            let mut rows: Vec<(Vec<f64>, f64, f64)> = Vec::new();

            // Packing / partitioning rows over random subsets — the source of conflict-graph edges.
            let nrows = 4 + (rnd().rem_euclid(4)) as usize;
            for _ in 0..nrows {
                let k = 2 + (rnd().rem_euclid(3)) as usize;
                let mut sub: Vec<usize> = (0..NB).collect();
                for i in 0..k {
                    let j = i + (rnd() as usize) % (NB - i);
                    sub.swap(i, j);
                }
                sub.truncate(k);
                let eq = rnd().rem_euclid(3) == 0;
                let lo = if eq { 1.0 } else { f64::NEG_INFINITY };
                let terms: Vec<(Col, f64)> = sub.iter().map(|&j| (cols[j], 1.0)).collect();
                m.add_row(lo, 1.0, &terms);
                let mut a = vec![0.0; NB];
                for &j in &sub {
                    a[j] = 1.0;
                }
                rows.push((a, lo, 1.0));
            }
            m.set_objective(&[(cols[0], 1.0)], Sense::Minimize);

            // An arbitrary point: validity may not depend on WHERE it was separated from.
            let x: Vec<f64> = (0..NB)
                .map(|_| (rnd().rem_euclid(21)) as f64 / 20.0)
                .collect();
            let cuts = separate_odd_cycle(&m, &x, m.num_rows());
            fired += cuts.len();

            for code in 0..(1i64 << NB) {
                let p: Vec<f64> = (0..NB).map(|j| ((code >> j) & 1) as f64).collect();
                let feasible = rows.iter().all(|(a, lo, hi)| {
                    let act: f64 = a.iter().zip(&p).map(|(&c, &v)| c * v).sum();
                    act >= lo - 1e-9 && act <= hi + 1e-9
                });
                if !feasible {
                    continue;
                }
                for c in &cuts {
                    let act: f64 = c.coeffs.iter().map(|&(col, a)| a * p[col.index()]).sum();
                    assert!(
                        act <= c.ub + 1e-9,
                        "an odd-hole cut deleted the integer point {p:?} -- \
                         activity {act} exceeds its bound {}",
                        c.ub
                    );
                }
            }
        }
        assert!(
            fired > 0,
            "no odd-hole cut was ever separated: the guard is vacuous"
        );
    }

    /// THE POINT OF THE FAMILY: the five-hole `a-b-c-d-e-a` at `x = 1/2` is cut by NO clique. Each
    /// edge `{v_i, v_{i+1}}` is satisfied (`1/2 + 1/2 = 1`) and there is no triangle, yet the point
    /// packs `Σ x = 5/2 > 2`. Only the odd-hole facet `Σ x ≤ 2` cuts it — by exactly `1/2`.
    #[test]
    fn odd_cycle_separates_the_five_hole() {
        let mut m = Model::new();
        let v: Vec<Col> = (0..5).map(|_| m.add_binary_col()).collect();
        // Consecutive-pair packing rows form the 5-cycle; no chord, so no triangle/clique cut.
        for i in 0..5 {
            m.add_row(
                f64::NEG_INFINITY,
                1.0,
                &[(v[i], 1.0), (v[(i + 1) % 5], 1.0)],
            );
        }
        m.set_objective(&[(v[0], 1.0)], Sense::Minimize);

        let x = vec![0.5; 5];
        // The cliques cannot cut this point (the graph is triangle-free).
        assert!(
            separate_clique(&m, &x, m.num_rows())
                .iter()
                .all(|c| violation(c, &x) <= MIN_VIOLATION),
            "a clique cut the triangle-free 5-hole -- impossible"
        );
        // The odd-hole family must.
        let cuts = separate_odd_cycle(&m, &x, m.num_rows());
        assert!(
            cuts.iter()
                .any(|c| c.coeffs.len() == 5 && c.ub == 2.0 && violation(c, &x) > 0.49),
            "the 5-hole facet Σx ≤ 2 was not separated"
        );
    }

    /// LIFTING TURNS THE HOLE INTO A WHEEL — the coefficient math, tested directly on `lift_odd_hole`
    /// (going through the full search would shadow the hole: a hub with `α ≥ 1` must touch two
    /// CONSECUTIVE hole vertices, and that triangle is a shorter odd cycle the shortest-walk search
    /// returns first). Take the 7-hole `0-1-…-6` and a hub `h` conflicting with the five consecutive
    /// vertices `{0,1,2,3,4}`. Deleting them leaves the arc `{5,6}` (MIS 1), so `α_h = k − 1 = 3 − 1`
    /// … no — the surviving arc after removing `{0,1,2,3,4}` is `{5,6}`, `⌈2/2⌉ = 1`, giving
    /// `α_h = 3 − 1 = 2`. The wheel facet is `Σ_{i} x_i + 2·h ≤ 3`.
    #[test]
    fn lifted_odd_hole_separates_the_wheel() {
        let mut m = Model::new();
        let v: Vec<Col> = (0..7).map(|_| m.add_binary_col()).collect();
        let h = m.add_binary_col();
        let mut pack: Vec<usize> = Vec::new();
        for i in 0..7 {
            m.add_row(
                f64::NEG_INFINITY,
                1.0,
                &[(v[i], 1.0), (v[(i + 1) % 7], 1.0)],
            );
            pack.push(m.num_rows() - 1);
        }
        for &sp in &[0usize, 1, 2, 3, 4] {
            m.add_row(f64::NEG_INFINITY, 1.0, &[(h, 1.0), (v[sp], 1.0)]);
            pack.push(m.num_rows() - 1);
        }
        m.set_objective(&[(v[0], 1.0)], Sense::Minimize);
        let x = vec![0.5; 8];
        let cyc: Vec<usize> = (0..7).map(|i| v[i].index()).collect();
        let lifted = lift_odd_hole(&m, &x, &cyc, &pack);
        assert_eq!(
            lifted,
            vec![(h.index(), 2)],
            "the hub should lift with coefficient 2 (k − MIS of the {{5,6}} arc = 3 − 1)"
        );
        // Assemble the wheel and brute-force soundness: no integer feasible point may violate it.
        let mut coeffs: Vec<(Col, f64)> = cyc.iter().map(|&c| (Col(c as u32), 1.0)).collect();
        coeffs.push((h, 2.0));
        let wheel = Cut {
            coeffs,
            lb: f64::NEG_INFINITY,
            ub: 3.0,
        };
        assert!(violation(&wheel, &x) > 0.49, "wheel must cut x=1/2");
        for code in 0..(1u32 << 8) {
            let p: Vec<f64> = (0..8).map(|j| ((code >> j) & 1) as f64).collect();
            let ok = (0..7).all(|i| p[i] + p[(i + 1) % 7] <= 1.0)
                && [0, 1, 2, 3, 4].iter().all(|&sp| p[7] + p[sp] <= 1.0);
            if !ok {
                continue;
            }
            let act: f64 = wheel
                .coeffs
                .iter()
                .map(|&(col, a)| a * p[col.index()])
                .sum();
            assert!(act <= wheel.ub + 1e-9, "wheel deleted feasible point {p:?}");
        }
    }

    /// Equal-strength hubs must consume the sequential-lifting budget in a
    /// stable order. `neigh` is a randomized `HashMap`, so omitting the final
    /// column-id tie-break makes this alternate across maps/processes.
    #[test]
    fn lifted_odd_hole_ties_use_column_order() {
        let mut m = Model::new();
        let v: Vec<Col> = (0..7).map(|_| m.add_binary_col()).collect();
        let first_hub = m.add_binary_col();
        let second_hub = m.add_binary_col();
        let mut pack: Vec<usize> = Vec::new();
        for i in 0..7 {
            m.add_row(
                f64::NEG_INFINITY,
                1.0,
                &[(v[i], 1.0), (v[(i + 1) % 7], 1.0)],
            );
            pack.push(m.num_rows() - 1);
        }
        for &hub in &[second_hub, first_hub] {
            for &spoke in &[0usize, 1, 2, 3, 4] {
                m.add_row(f64::NEG_INFINITY, 1.0, &[(hub, 1.0), (v[spoke], 1.0)]);
                pack.push(m.num_rows() - 1);
            }
        }
        let x = vec![0.5; 9];
        let cycle: Vec<usize> = (0..7).map(|i| v[i].index()).collect();
        for _ in 0..128 {
            assert_eq!(
                lift_odd_hole(&m, &x, &cycle, &pack),
                vec![(first_hub.index(), 2)],
                "equal hubs must assign the limited lift budget to the lower column id"
            );
        }
    }

    /// EXHAUSTIVE SOUNDNESS OF THE LIFT. Random packing/partitioning models built so that a handful
    /// of "hub" columns share rows with many others — the regime where `lift_odd_hole` produces
    /// non-trivial coefficients — with EVERY integer feasible point of the model brute-forced against
    /// every emitted (lifted) cut. A wrong lifting coefficient deletes a feasible point here.
    #[test]
    fn lifted_odd_hole_cuts_never_remove_an_integer_point() {
        let mut seed = 0x11F7_2026_0719_u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };
        let mut lifted_fired = 0usize;
        for _case in 0..800 {
            const NB: usize = 14;
            let mut m = Model::new();
            let cols: Vec<Col> = (0..NB).map(|_| m.add_binary_col()).collect();
            let mut rows: Vec<(Vec<usize>, f64, f64)> = Vec::new();
            let add =
                |m: &mut Model, sub: &[usize], eq: bool, rows: &mut Vec<(Vec<usize>, f64, f64)>| {
                    let lo = if eq { 1.0 } else { f64::NEG_INFINITY };
                    let terms: Vec<(Col, f64)> = sub.iter().map(|&j| (cols[j], 1.0)).collect();
                    m.add_row(lo, 1.0, &terms);
                    rows.push((sub.to_vec(), lo, 1.0));
                };
            // A 5- or 7-cycle backbone (consecutive-pair packing rows) — the hole.
            let clen = if rnd().rem_euclid(2) == 0 { 5 } else { 7 };
            for i in 0..clen {
                add(&mut m, &[i, (i + 1) % clen], false, &mut rows);
            }
            // Hubs: columns outside the cycle sharing rows with several cycle vertices (wheels),
            // plus random extra packing rows for chords/noise.
            let nhub = 1 + (rnd().rem_euclid(3)) as usize;
            for hraw in 0..nhub {
                let hub = clen + hraw;
                if hub >= NB {
                    break;
                }
                let touch = 2 + (rnd().rem_euclid((clen - 1) as i64)) as usize;
                let mut spokes: Vec<usize> = (0..clen).collect();
                for i in 0..touch {
                    let j = i + (rnd() as usize) % (clen - i);
                    spokes.swap(i, j);
                }
                for &sp in spokes.iter().take(touch) {
                    add(&mut m, &[hub, sp], false, &mut rows);
                }
            }
            let extra = (rnd().rem_euclid(4)) as usize;
            for _ in 0..extra {
                let ksz = 2 + (rnd().rem_euclid(3)) as usize;
                let mut sub: Vec<usize> = (0..NB).collect();
                for i in 0..ksz {
                    let j = i + (rnd() as usize) % (NB - i);
                    sub.swap(i, j);
                }
                sub.truncate(ksz);
                add(&mut m, &sub, rnd().rem_euclid(4) == 0, &mut rows);
            }
            m.set_objective(&[(cols[0], 1.0)], Sense::Minimize);
            let x: Vec<f64> = (0..NB)
                .map(|_| (rnd().rem_euclid(21)) as f64 / 20.0)
                .collect();
            let cuts = separate_odd_cycle(&m, &x, m.num_rows());
            // A coefficient above one can only come from sequential lifting;
            // a longer bare cycle still has unit coefficients and must not make
            // this coverage guard pass. With `--no-odd-lift`, this
            // counter therefore remains zero and the final assertion fails.
            lifted_fired += cuts
                .iter()
                .filter(|c| c.coeffs.iter().any(|&(_, a)| a > 1.0))
                .count();
            for code in 0..(1i64 << NB) {
                let p: Vec<f64> = (0..NB).map(|j| ((code >> j) & 1) as f64).collect();
                let feasible = rows.iter().all(|(sub, lo, hi)| {
                    let act: f64 = sub.iter().map(|&j| p[j]).sum();
                    act >= lo - 1e-9 && act <= hi + 1e-9
                });
                if !feasible {
                    continue;
                }
                for c in &cuts {
                    let act: f64 = c.coeffs.iter().map(|&(col, a)| a * p[col.index()]).sum();
                    assert!(
                        act <= c.ub + 1e-9,
                        "a LIFTED odd-hole cut deleted the integer point {p:?} — \
                         activity {act} exceeds its bound {} (cut {:?})",
                        c.ub,
                        c.coeffs
                    );
                }
            }
        }
        assert!(
            lifted_fired > 0,
            "no lifted odd-hole cut was ever separated: the lift guard is vacuous"
        );
    }

    /// THE WIDTH GATE DESCRIBES THE SEPARATOR, NOT AN INSTANCE. It must admit
    /// the set-partition models the odd-hole family is FOR — including one
    /// carrying side rows, which is what the all-or-nothing predicate it
    /// replaced could not do — and must reject the shapes where the conflict
    /// graph is not a wide 0/1 object. Each admitted model is checked against
    /// the separator itself, so the gate cannot drift into arming a class the
    /// family is silent on. (The CUTS are validity-guarded by
    /// `odd_cycle_cuts_never_remove_an_integer_point`; this guards the gate.)
    #[test]
    fn wide_set_partition_gate_matches_structure() {
        // `rows` disjoint sum-to-1 rows over `width` columns each, plus
        // `side` rows that are NOT sum-to-1 equalities.
        let build = |rows: usize, width: usize, side: usize, continuous: bool| -> Model {
            let mut m = Model::new();
            let mut sp: Vec<Vec<Col>> = Vec::new();
            for _ in 0..rows {
                let cols: Vec<Col> = (0..width)
                    .map(|_| {
                        if continuous {
                            m.add_col(0.0, 1.0)
                        } else {
                            m.add_binary_col()
                        }
                    })
                    .collect();
                let terms: Vec<(Col, f64)> = cols.iter().map(|&c| (c, 1.0)).collect();
                m.add_row(1.0, 1.0, &terms);
                sp.push(cols);
            }
            for s in 0..side {
                let terms: Vec<(Col, f64)> = sp.iter().map(|r| (r[s % width], 3.0)).collect();
                m.add_row(f64::NEG_INFINITY, 5.0, &terms);
            }
            m.set_objective(&[(sp[0][0], 1.0)], Sense::Maximize);
            m
        };

        // The class: 4 sum-to-1 rows, 40 columns each — wide, all binary.
        assert!(is_wide_set_partition(&build(4, 40, 0, false)));
        // SIDE ROWS ARE TOLERATED while the sum-to-1 rows stay the majority.
        // This is mod010's shape, and exactly what the old gate refused.
        assert!(is_wide_set_partition(&build(4, 40, 2, false)));
        assert!(
            !is_pure_set_partitioning(&build(4, 40, 2, false)),
            "the old all-or-nothing predicate is what this case escapes"
        );
        // Side rows in the MAJORITY: no longer a set-partitioning model.
        assert!(!is_wide_set_partition(&build(4, 40, 5, false)));
        // NOT WIDE: 4 rows of 9 columns is 36 columns, under the 10x ratio.
        assert!(!is_wide_set_partition(&build(4, 9, 0, false)));
        // NOT BINARY: the conflict graph and its independence-number argument
        // are 0/1 objects.
        assert!(!is_wide_set_partition(&build(4, 40, 0, true)));
        // A single sum-to-1 row is a clique, never a hole.
        assert!(!is_wide_set_partition(&build(1, 40, 0, false)));
        // The empty model must not fire.
        assert!(!is_wide_set_partition(&Model::new()));

        // AND THE ADMITTED CLASS SEPARATES. A 5-hole of sum-to-1 rows over a
        // wide column set, at the half-integral vertex the LP would land on:
        // every pair-clique is satisfied, the hole is not.
        let mut m = Model::new();
        let v: Vec<Col> = (0..5).map(|_| m.add_binary_col()).collect();
        let filler: Vec<Col> = (0..120).map(|_| m.add_binary_col()).collect();
        for i in 0..5 {
            m.add_row(
                1.0,
                1.0,
                &[
                    (v[i], 1.0),
                    (v[(i + 1) % 5], 1.0),
                    (filler[i], 1.0),
                    (filler[i + 5], 1.0),
                ],
            );
        }
        m.set_objective(&[(v[0], 1.0)], Sense::Maximize);
        assert!(
            is_wide_set_partition(&m),
            "125 columns over 5 sum-to-1 rows"
        );
        let mut x = vec![0.0; m.num_cols()];
        for &c in &v {
            x[c.index()] = 0.5;
        }
        assert!(
            !separate_odd_cycle(&m, &x, m.num_rows()).is_empty(),
            "the admitted class must actually separate: the gate would be inert"
        );
    }
}

#[cfg(test)]
mod lifted_cover_tests {
    use super::*;
    use crate::model::Sense;

    /// A LIFTED COVER MUST NOT DELETE AN INTEGER POINT.
    ///
    /// Everything that makes this cut worth having is in the LIFTING, and a lifting coefficient one
    /// step too large deletes points silently. So the guard must SEE lifted cuts (`fired > 0`) and it
    /// must FAIL when the lift is greedy -- with `γ + 1` it does, on
    /// `wb=[4,6,5,3,2] wg=[2,5] ug=[1,2] b=7`, at the point `y = 0, x = (1,1)`: activity 3 > ub 2.
    ///
    /// Integral data on purpose: the feasible set IS the integer grid, so enumerating it is a proof
    /// rather than a sample.
    #[test]
    fn lifted_cover_cuts_never_remove_an_integer_point() {
        let mut seed = 0xC0FF_EE01_u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };

        let mut fired = 0usize;
        for _case in 0..500 {
            const NB: usize = 5;
            const NG: usize = 2;
            let wb: Vec<i64> = (0..NB).map(|_| 1 + rnd() % 6).collect();
            let wg: Vec<i64> = (0..NG).map(|_| 1 + rnd() % 5).collect();
            let ug: Vec<i64> = (0..NG).map(|_| 1 + rnd() % 2).collect();
            let total: i64 = wb.iter().sum::<i64>();
            let b = 2 + rnd() % total.max(3);
            if b >= total {
                continue; // the binaries never overshoot: no cover to find
            }

            let mut m = Model::new();
            let bc: Vec<Col> = (0..NB).map(|_| m.add_binary_col()).collect();
            let gc: Vec<Col> = (0..NG).map(|k| m.add_int_col(0.0, ug[k] as f64)).collect();
            let mut terms: Vec<(Col, f64)> = bc
                .iter()
                .enumerate()
                .map(|(j, &c)| (c, wb[j] as f64))
                .collect();
            terms.extend(gc.iter().enumerate().map(|(k, &c)| (c, wg[k] as f64)));
            m.add_row(f64::NEG_INFINITY, b as f64, &terms);
            m.set_objective(&[(bc[0], 1.0)], Sense::Minimize);

            // ⚠ THE POINT MUST REACH THE INTEGERS' RANGE, or the guard never leaves the face.
            //
            // With `x*` drawn in [0,1] every integer has `⌊x*⌋ = 0`, so the separator only ever
            // separates at `x_G = 0` and the whole non-zero-reference lifting -- the part that is
            // hard and the part that is the point -- is never executed. Draw the integers across
            // their OWN box.
            let n = NB + NG;
            let mut x: Vec<f64> = (0..n).map(|_| (rnd() % 20) as f64 / 20.0).collect();
            for k in 0..NG {
                x[gc[k].index()] = (rnd() % (20 * ug[k] + 1)) as f64 / 20.0;
            }
            let cuts = separate_lifted_cover(&m, &x, m.num_rows());
            fired += cuts.len();

            for code in 0..(1i64 << NB) {
                let y: Vec<i64> = (0..NB).map(|j| (code >> j) & 1).collect();
                let mut t = vec![0i64; NG];
                loop {
                    let load: i64 = (0..NB).map(|j| wb[j] * y[j]).sum::<i64>()
                        + (0..NG).map(|k| wg[k] * t[k]).sum::<i64>();
                    if load <= b {
                        let mut p = vec![0.0f64; n];
                        for j in 0..NB {
                            p[bc[j].index()] = y[j] as f64;
                        }
                        for k in 0..NG {
                            p[gc[k].index()] = t[k] as f64;
                        }
                        for c in &cuts {
                            let act: f64 = c.coeffs.iter().map(|&(j, a)| a * p[j.index()]).sum();
                            assert!(
                                act <= c.ub + 1e-7,
                                "lifted cover deleted an integer point: wb={wb:?} wg={wg:?} \
                                 ug={ug:?} b={b} y={y:?} x={t:?} activity={act} > ub={}",
                                c.ub
                            );
                        }
                    }
                    let mut k = 0;
                    while k < NG {
                        t[k] += 1;
                        if t[k] <= ug[k] {
                            break;
                        }
                        t[k] = 0;
                        k += 1;
                    }
                    if k == NG {
                        break;
                    }
                }
            }
        }
        assert!(
            fired > 0,
            "no lifted cover was ever separated: the guard is vacuous"
        );
    }
}

// ---------------------------------------------------------------------------
// {0,1/2}-Chvátal–Gomory ("zero-half") cuts
// ---------------------------------------------------------------------------

/// Longest row-combination the separator will assemble, and the most cuts it returns per call.
const ZH_MAX_ROWS: u32 = 12;
const ZH_MAX_CUTS: usize = 40;
/// Cap the nonzeros of an emitted zero-half cut — a dense cut slows every LP that carries it.
///
/// MEASURED 2026-08-01, `sepstat::GATE_ZH_NNZ`: **never fires**. Over 101 instances (66 spanning
/// all three corpus tiers plus the 35-instance named set) not one violated, slack-feasible
/// zero-half row was refused for width. Its excluded population is EMPTY, so it is neither a cost
/// control that is paying nor a filter that is costing — it is a backstop that has never been
/// reached, and the cause-6 diagnosis's "the absolute nnz cap" does not mean this one.
const ZH_MAX_NNZ: usize = 200;

/// Is `model` PURE SET PARTITIONING — every row an all-binary, all-ones,
/// sum-to-1 EQUALITY (`Σ_j x_j = 1`), every column binary?
///
/// This is the structure gate that turns the zero-half family on by default:
/// on exactly this structure every constraint row has integer data, odd RHS,
/// and slack 0 at every LP vertex, so every even-column-parity combination of
/// an odd number of rows is a zero-half cut violated by exactly 1/2 at a
/// fractional vertex — the parity family is what the model is MADE of. A
/// model without the structure keeps the historical default (off) and its
/// trajectory bit-for-bit.
///
/// A MEASURED property of the model, never an instance name: all coefficients
/// exactly `1.0`, every row `lb == ub == 1.0`, every column integral with
/// bounds in `{0, 1}` (a presolve-fixed binary still counts — fixing a column
/// does not change the rows' parity structure).
pub(crate) fn is_pure_set_partitioning(model: &Model) -> bool {
    let (n, m) = (model.num_cols(), model.num_rows());
    if n == 0 || m == 0 {
        return false;
    }
    for j in 0..n {
        let col = Col(j as u32);
        if !model.col_kind(col).is_integral() {
            return false;
        }
        let (lb, ub) = model.col_bounds(col);
        if !(lb == 0.0 || lb == 1.0) || !(ub == 0.0 || ub == 1.0) || lb > ub {
            return false;
        }
    }
    for r in 0..m {
        let Some(row) = model.row_at(r) else {
            return false;
        };
        let (coeffs, lb, ub) = model.row(row);
        if coeffs.is_empty() || lb != 1.0 || ub != 1.0 {
            return false;
        }
        if coeffs.iter().any(|&(_, a)| a != 1.0) {
            return false;
        }
    }
    true
}

/// The default-on gate for `separate_odd_cycle` (see `bab.rs`): is this model a
/// WIDE set-partitioning model — one whose sum-to-1 rows are the bulk of the
/// model and whose columns vastly outnumber them?
///
/// Written to describe the SEPARATOR's input rather than a named model class.
/// The odd-hole separator builds a conflict graph out of all-binary packing
/// rows and looks for chordless odd cycles in it, so the two things that decide
/// whether it can find anything are:
///
///  * every column binary — the conflict graph, the independence-number
///    argument behind `Σ_{v∈C} x_v ≤ (|C|−1)/2`, and the wheel lifts are all
///    0/1 objects; and
///  * many columns per sum-to-1 row. A sum-to-1 row over `k` columns is a
///    `k`-clique in the conflict graph; odd HOLES (the facets the cliques miss)
///    only appear once the rows overlap in many different ways, which is what a
///    large column-to-row ratio buys.
///
/// The sum-to-1 rows must also be the MAJORITY, so this stays a statement about
/// what the model IS. Rows that are not sum-to-1 equalities are simply invisible
/// to the separator — it never aggregates them — so tolerating a handful of side
/// rows cannot make an emitted cut wrong. That tolerance is the whole point:
/// `is_pure_set_partitioning` is all-or-nothing and two side rows out of 146
/// disqualified mod010, an instance where the family is worth +8.6% of root
/// closure.
pub(crate) fn is_wide_set_partition(model: &Model) -> bool {
    let (n, m) = (model.num_cols(), model.num_rows());
    if n == 0 || m == 0 {
        return false;
    }
    for j in 0..n {
        let col = Col(j as u32);
        if !model.col_kind(col).is_integral() {
            return false;
        }
        let (lb, ub) = model.col_bounds(col);
        // A presolve-FIXED binary still counts: fixing a column does not change
        // the conflict structure of the rows it sits in.
        if !(lb == 0.0 || lb == 1.0) || !(ub == 0.0 || ub == 1.0) || lb > ub {
            return false;
        }
    }
    let mut sp_rows = 0usize;
    for r in 0..m {
        let Some(row) = model.row_at(r) else {
            return false;
        };
        let (coeffs, lb, ub) = model.row(row);
        if coeffs.is_empty() || lb != 1.0 || ub != 1.0 {
            continue;
        }
        if coeffs.iter().all(|&(_, a)| a == 1.0) {
            sp_rows += 1;
        }
    }
    sp_rows >= 2 && 2 * sp_rows >= m && n >= 10 * sp_rows
}

/// Separate {0,1/2}-Chvátal–Gomory ("zero-half") cuts (Caprara–Fischetti, GF(2) elimination).
///
/// A zero-half cut takes multipliers `u ∈ {0, 1/2}` on a subset `S` of the model's `≤` rows. When
/// every column's coefficient sum over `S` is EVEN, the combined row `(1/2)Σ_S a_i·x ≤ (1/2)Σ_S b_i`
/// has an INTEGER left-hand side at every integer `x` (integer coefficients × integer variables), so
/// it rounds to `≤ ⌊(1/2)Σ_S b_i⌋`. That floor bites exactly when `Σ_S b_i` is ODD, and the cut is
/// then violated at `x*` iff the selected rows' total slack is `< 1` (violation `= (1 − Σ_S s_i)/2`).
///
/// Validity needs no `x ≥ 0` shift: the LHS is integral for ANY integer point whatever its bounds —
/// the one requirement is that every column carrying a nonzero cut coefficient is integer-constrained
/// (a continuous column would break LHS integrality), so only ALL-INTEGER rows are candidates.
///
/// Separation = find `S` with every column-parity even and the `b`-parity odd, minimising total
/// slack — a min-weight GF(2) combination (NP-hard exactly). The heuristic is greedy Gaussian
/// elimination over the parity vectors in increasing-slack order: cheap rows enter the basis first,
/// so a combination that reaches the odd-`b` target tends to be cheap. Provenance (the XOR of the
/// original candidate indices) recovers `S`. Set partitioning (`Σx = 1`, every RHS odd, slack 0 at
/// the LP optimum) is the canonical target — every odd-`b` combination is violated by exactly 1/2.
pub(crate) fn separate_zero_half(model: &Model, x: &[f64]) -> Vec<Cut> {
    let n = model.num_cols();
    let nr = model.num_rows();
    if n == 0 || nr == 0 {
        return Vec::new();
    }
    let words = n.div_ceil(64); // parity bitset width over columns

    // A candidate: one all-integer row in `≤` orientation, its parity fingerprint and slack.
    struct Cand {
        parity: Vec<u64>,     // columns with ODD coefficient (bit j set)
        prov: Vec<u64>,       // candidate indices XORed to form this (starts as {self})
        bpar: bool,           // parity of the `≤`-oriented integer RHS
        pivot: Option<usize>, // lowest set parity bit, kept current through elimination
    }
    let set_bit = |bs: &mut [u64], j: usize| bs[j / 64] |= 1u64 << (j % 64);
    let lowest = |bs: &[u64]| -> Option<usize> {
        for (w, &word) in bs.iter().enumerate() {
            if word != 0 {
                return Some(w * 64 + word.trailing_zeros() as usize);
            }
        }
        None
    };

    let mut cands: Vec<Cand> = Vec::new();
    let mut slack_of: Vec<f64> = Vec::new();
    let mut coeffs_of: Vec<Vec<(u32, i64)>> = Vec::new();
    let mut b_of: Vec<i64> = Vec::new();

    for r in 0..nr {
        let row = model.row_at(r).unwrap();
        let (coeffs, lb, ub) = model.row(row);
        if coeffs.is_empty() {
            continue;
        }
        // All-integer rows only (a continuous column would break LHS integrality) with integer data.
        let mut ok = true;
        for &(c, a) in coeffs {
            let integral = (a - a.round()).abs() < 1e-6;
            let intcol = !matches!(model.col_kind(Col(c)), ColKind::Continuous);
            if !integral || !intcol {
                ok = false;
                break;
            }
        }
        if !ok {
            continue;
        }
        let act: f64 = coeffs
            .iter()
            .map(|&(c, a)| a * x.get(c as usize).copied().unwrap_or(0.0))
            .sum();
        // Choose the `≤` orientation with the smaller slack. `≤ ub`: slack `ub − act`, RHS `ub`.
        // `≥ lb` becomes `−a·x ≤ −lb`: slack `act − lb`, RHS `−lb`, coefficients negated.
        let up_ok = ub.is_finite() && (ub - ub.round()).abs() < 1e-6;
        let lo_ok = lb.is_finite() && (lb - lb.round()).abs() < 1e-6;
        let up = up_ok.then(|| (ub - act, 1i64, ub.round() as i64));
        let lo = lo_ok.then(|| (act - lb, -1i64, -(lb.round() as i64)));
        let pick = match (up, lo) {
            (Some(u), Some(l)) => {
                if u.0 <= l.0 {
                    u
                } else {
                    l
                }
            }
            (Some(u), None) => u,
            (None, Some(l)) => l,
            (None, None) => continue,
        };
        let (slack, sign, b) = pick;
        // A row with slack ≥ 1 cannot sit in any violated combination (slacks are ≥ 0 and must sum to
        // < 1), so it is dead weight for separation — drop it. Set-partition rows have slack 0.
        if !(-1e-6..1.0 - 1e-9).contains(&slack) {
            continue;
        }
        let id = cands.len();
        let mut parity = vec![0u64; words];
        let mut oriented: Vec<(u32, i64)> = Vec::with_capacity(coeffs.len());
        for &(c, a) in coeffs {
            let ai = sign * (a.round() as i64);
            if ai == 0 {
                continue;
            }
            if ai.rem_euclid(2) == 1 {
                set_bit(&mut parity, c as usize);
            }
            oriented.push((c, ai));
        }
        let mut prov = vec![0u64; nr.div_ceil(64)];
        prov[id / 64] |= 1u64 << (id % 64);
        let bpar = b.rem_euclid(2) == 1;
        let pivot = lowest(&parity);
        cands.push(Cand {
            parity,
            prov,
            bpar,
            pivot,
        });
        slack_of.push(slack.max(0.0));
        coeffs_of.push(oriented);
        b_of.push(b);
    }
    if cands.is_empty() {
        return Vec::new();
    }

    // Greedy Gaussian elimination over GF(2), cheapest rows first.
    let mut order: Vec<usize> = (0..cands.len()).collect();
    order.sort_by(|&i, &j| {
        slack_of[i]
            .partial_cmp(&slack_of[j])
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    let mut basis: std::collections::HashMap<usize, usize> = std::collections::HashMap::new(); // pivot col -> cand index in `reduced`
    let mut reduced: Vec<Cand> = Vec::new();
    let mut hits: Vec<Vec<u64>> = Vec::new(); // provenance sets of found zero-half combinations

    let pcount = nr.div_ceil(64);
    for &start in &order {
        // Work on a private copy we reduce down.
        let mut cur = Cand {
            parity: cands[start].parity.clone(),
            prov: cands[start].prov.clone(),
            bpar: cands[start].bpar,
            pivot: cands[start].pivot,
        };
        while let Some(p) = cur.pivot {
            let Some(&bi) = basis.get(&p) else { break };
            let b = &reduced[bi];
            for w in 0..words {
                cur.parity[w] ^= b.parity[w];
            }
            for w in 0..pcount {
                cur.prov[w] ^= b.prov[w];
            }
            cur.bpar ^= b.bpar;
            cur.pivot = lowest(&cur.parity);
        }
        match cur.pivot {
            None => {
                // All column parities cancelled. Odd b-parity ⇒ a genuine zero-half combination.
                if cur.bpar {
                    let popcount: u32 = cur.prov.iter().map(|w| w.count_ones()).sum();
                    if (1..=ZH_MAX_ROWS).contains(&popcount) {
                        hits.push(cur.prov.clone());
                    }
                }
            }
            Some(p) => {
                basis.insert(p, reduced.len());
                reduced.push(cur);
            }
        }
    }

    // Build cuts from the combinations found.
    let mut cuts: Vec<Cut> = Vec::new();
    for prov in hits {
        // Sum the oriented integer coefficients over the selected candidates.
        let mut acc: std::collections::HashMap<u32, i64> = std::collections::HashMap::new();
        let mut bsum: i64 = 0;
        let mut total_slack = 0.0f64;
        for id in 0..cands.len() {
            if prov[id / 64] & (1u64 << (id % 64)) == 0 {
                continue;
            }
            for &(c, a) in &coeffs_of[id] {
                *acc.entry(c).or_insert(0) += a;
            }
            bsum += b_of[id];
            total_slack += slack_of[id];
        }
        // Defensive: the construction guarantees even column sums; if any is odd (a parity miscount
        // from noisy data) the halved cut would be invalid, so refuse it. Same for an even RHS (no
        // floor gain). Neither should fire on truly all-integer rows.
        if bsum.rem_euclid(2) != 1 {
            continue;
        }
        if acc.values().any(|&v| v.rem_euclid(2) != 0) {
            continue;
        }
        let mut out: Vec<(Col, f64)> = acc
            .into_iter()
            .filter(|&(_, v)| v != 0)
            .map(|(c, v)| (Col(c), (v / 2) as f64))
            .collect();
        if out.is_empty() || out.len() > ZH_MAX_NNZ {
            // FORGONE COST — `out` is the finished halved coefficient vector and `rhs` follows
            // from `bsum` alone, so the refused row is fully derived and one f64 dot product
            // says whether the refusal cost anything. Charged only when the row is BOTH
            // violated and slack-feasible, i.e. only when it would otherwise have been kept:
            // charging a row the next test would have thrown out anyway overstates the loss.
            if !out.is_empty() {
                let refused = Cut {
                    coeffs: out,
                    lb: f64::NEG_INFINITY,
                    ub: bsum.div_euclid(2) as f64,
                };
                if total_slack < 1.0 - 1e-9 && violation(&refused, x) > min_violation() {
                    crate::sepstat::gate_charge(
                        crate::sepstat::GATE_ZH_NNZ,
                        refused.coeffs.len() as u64,
                    );
                }
            }
            continue;
        }
        out.sort_by_key(|&(c, _)| c.index());
        let rhs = bsum.div_euclid(2) as f64; // floor(bsum/2); bsum odd ⇒ strict gain
        let cut = Cut {
            coeffs: out,
            lb: f64::NEG_INFINITY,
            ub: rhs,
        };
        // Keep only genuinely violated cuts (total_slack < 1 is necessary but the f64 activity is the
        // ground truth the pool ranks on).
        if total_slack < 1.0 - 1e-9 && clears_min_violation(&cut, x) {
            cuts.push(cut);
        }
    }
    // Deepest first, and bounded — a working set, not an archive.
    cuts.sort_by(|a, b| {
        efficacy(b, x)
            .partial_cmp(&efficacy(a, x))
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    cuts.truncate(ZH_MAX_CUTS);
    cuts
}

#[cfg(test)]
mod zero_half_tests {
    use super::*;
    use crate::model::{Model, Sense};

    #[test]
    fn zero_half_cuts_never_remove_an_integer_point() {
        let mut seed = 0x000F_F1CE_u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };
        let mut fired = 0usize;
        const HI: i64 = 4;

        for _case in 0..500 {
            let n = 4usize;
            let mut m = Model::new();
            let cols: Vec<Col> = (0..n).map(|_| m.add_int_col(0.0, HI as f64)).collect();
            // A handful of small-integer rows — the parity structure zero-half keys off.
            let mut rows: Vec<(Vec<f64>, f64, f64)> = Vec::new();
            let nrows = 2 + (rnd().rem_euclid(3)) as usize;
            for _ in 0..nrows {
                let a: Vec<f64> = (0..n).map(|_| (rnd().rem_euclid(5) - 2) as f64).collect();
                if a.iter().all(|&v| v == 0.0) {
                    continue;
                }
                let hi = (rnd().rem_euclid(9)) as f64;
                let terms: Vec<(Col, f64)> = cols
                    .iter()
                    .zip(&a)
                    .filter(|(_, &v)| v != 0.0)
                    .map(|(&c, &v)| (c, v))
                    .collect();
                // Mix equalities and ≤ rows.
                if rnd().rem_euclid(2) == 0 {
                    m.add_row(hi, hi, &terms);
                    rows.push((a, hi, hi));
                } else {
                    m.add_row(f64::NEG_INFINITY, hi, &terms);
                    rows.push((a, f64::NEG_INFINITY, hi));
                }
            }
            if rows.is_empty() {
                continue;
            }
            m.set_objective(&[(cols[0], 1.0)], Sense::Minimize);
            let x: Vec<f64> = (0..n)
                .map(|_| (rnd().rem_euclid(40)) as f64 / 10.0)
                .collect();
            let cuts = separate_zero_half(&m, &x);
            fired += cuts.len();

            // Every integer point the MODEL admits must satisfy every cut.
            let total: i64 = (HI + 1).pow(n as u32);
            for code in 0..total {
                let mut p = vec![0.0f64; n];
                let mut t = code;
                for v in p.iter_mut() {
                    *v = (t % (HI + 1)) as f64;
                    t /= HI + 1;
                }
                let feasible = rows.iter().all(|(a, lo, hi)| {
                    let act: f64 = a.iter().zip(&p).map(|(&c, &v)| c * v).sum();
                    act >= lo - 1e-9 && act <= hi + 1e-9
                });
                if !feasible {
                    continue;
                }
                for c in &cuts {
                    let act: f64 = c.coeffs.iter().map(|&(col, a)| a * p[col.index()]).sum();
                    assert!(
                        act <= c.ub + 1e-6,
                        "a zero-half cut deleted integer point {p:?}: activity {act} > bound {}",
                        c.ub
                    );
                }
            }
        }
        assert!(
            fired > 0,
            "no zero-half cut was ever separated: guard is vacuous"
        );
    }

    /// The auto-enable gate fires on EXACTLY the structure it names. A genuine
    /// set-partitioning model passes; every single structural mutation — a
    /// non-unit coefficient, a non-1 RHS, an inequality row, a continuous or
    /// wide-integer column — kills it. (The zero-half CUTS themselves are
    /// validity-guarded by `zero_half_cuts_never_remove_an_integer_point`
    /// above; this guards the default-on gate.)
    #[test]
    fn pure_set_partitioning_gate_matches_structure() {
        let build = |mutation: u8| -> Model {
            let mut m = Model::new();
            let cols: Vec<Col> = (0..4)
                .map(|j| {
                    if mutation == 4 && j == 3 {
                        m.add_col(0.0, 1.0) // continuous column
                    } else if mutation == 5 && j == 3 {
                        m.add_int_col(0.0, 2.0) // wide general integer
                    } else {
                        m.add_binary_col()
                    }
                })
                .collect();
            let rhs = if mutation == 2 { 2.0 } else { 1.0 };
            let a0 = if mutation == 1 { 2.0 } else { 1.0 };
            m.add_row(rhs, rhs, &[(cols[0], a0), (cols[1], 1.0), (cols[2], 1.0)]);
            if mutation == 3 {
                // Inequality, not an equality.
                m.add_row(f64::NEG_INFINITY, 1.0, &[(cols[1], 1.0), (cols[3], 1.0)]);
            } else {
                m.add_row(1.0, 1.0, &[(cols[1], 1.0), (cols[3], 1.0)]);
            }
            m.set_objective(&[(cols[0], 1.0), (cols[3], 2.0)], Sense::Minimize);
            m
        };
        assert!(
            is_pure_set_partitioning(&build(0)),
            "the gate must fire on a genuine set-partitioning model (vacuous otherwise)"
        );
        for mutation in 1..=5u8 {
            assert!(
                !is_pure_set_partitioning(&build(mutation)),
                "mutation {mutation} should have killed the gate"
            );
        }
        // A presolve-fixed binary (bounds pinched to a point in {0,1}) keeps
        // the gate alive: fixing a column does not change row parity.
        let mut m = Model::new();
        let a = m.add_binary_col();
        let b = m.add_int_col(1.0, 1.0);
        m.add_row(1.0, 1.0, &[(a, 1.0), (b, 1.0)]);
        m.set_objective(&[(a, 1.0)], Sense::Minimize);
        assert!(is_pure_set_partitioning(&m));
        // The empty model must not fire.
        assert!(!is_pure_set_partitioning(&Model::new()));
    }
}

// ======================= LIFT-AND-PROJECT (Balas–Ceria–Cornuéjols) =======================
//
// The DISJUNCTIVE family. For an integer column `x_j` fractional at the point to separate
// (`f = floor(x*_j)`), every integer-feasible point satisfies `x_j <= f` OR `x_j >= f+1`,
// and any inequality valid for BOTH `conv(P ∩ {x_j <= f})` and `conv(P ∩ {x_j >= f+1})`
// is valid for every integer point of `P`. Finding the most violated such inequality is
// itself a (small) LP — the Cut-Generating LP, "CGLP" — over the nonnegative aggregation
// multipliers of the two sides. `P` here is the ROOT relaxation: original rows plus GLOBAL
// column bounds, so a cut from this family is globally valid wherever it is derived.
//
// WHY THIS FAMILY when the single-row families are exhausted: a GMI/MIR/cover cut is
// derived from ONE row (of the tableau, or one aggregation), so its geometry is anchored
// to the vertex that produced the row — the measured rout failure mode (plateau-GMI cuts
// separate but do not TRANSFER: 0-1 in 6 binding at later bound-owning vertices). The
// CGLP searches the whole cone of multipliers over ALL rows of BOTH branch polyhedra at
// once; what it returns is a supporting inequality of the disjunctive hull itself, not a
// rounding of one vertex row.
//
// VALIDITY IS PROVEN EXACTLY, never trusted from the float lane. The float CGLP solution
// only PROPOSES nonnegative multipliers `(u, u0)` / `(v, v0)`. Those are snapped to a
// dyadic grid, clamped `>= 0`, and both sides are re-derived in exact rationals over the
// exactly-read model rows (`Ã x >= b̃` is the `>=`-form of rows and global bounds):
//
//   side 0 (`x_j <= f`):    a0 = Ãᵀu − u0·e_j     b0 = u·b̃ − u0·f
//   side 1 (`x_j >= f+1`):  a1 = Ãᵀv + v0·e_j     b1 = v·b̃ + v0·(f+1)
//
// Each side is a conic combination of rows valid on its branch, so `a_s·x >= b_s` holds
// on branch `s` BY CONSTRUCTION — whatever the floats proposed, however wrong. The two
// sides are then MERGED into one inequality `α·x >= β`: per column, `α_c` is chosen
// between `a0_c` and `a1_c` and each side pays the difference out of its right-hand side
// over the column's box (`min(d·lo, d·up)`, exact) — the same implied-by-the-original
// license `snap`/`clean` operate under — and `β = min(b0 + pay0, b1 + pay1)`. The final
// f64 embedding rounds each `α_c` to a representable value and pays the rounding the same
// way, with `β` rounded DOWN. Every admitted cut is therefore exactly valid end to end;
// the float CGLP influences only WHICH valid cut is found. Guard:
// `lift_project_cuts_never_remove_an_integer_point` (brute-force, verified fail-on-bug).
//
// MEASURED VERDICT (2026-07-17, rout, seeded, 20s, baseline tree bound 1043.31): OPT-IN
// and staying so. The family WORKS as machinery — at rout's exhausted root vertex (every
// default family dry, bound flat at 981.864286) the CGLP separates cuts violated by
// 0.20–0.25 — and loses as economics, three ways:
//   1. ROOT: the cuts do not move the bound ONE ULP. With two of them adopted into the
//      round-1 LP (nnz cap lifted to let them in), the re-solve returns 981.864286
//      bit-identically — rout's root optimum is a wide degenerate FACE, the cut removes
//      one vertex, and the LP retreats along the face (the clique-stall shape). Round 1
//      then separates the NEW vertex just as deeply (0.20): vertex whack-a-mole.
//   2. NODE (plateau cadence, `the node-gmi knob=8`): a CGLP at a node vertex is
//      stall-prone even with `eager_perturb` + row dedup (most hit their 0.25–0.5s cap;
//      phase-2 crawls at 97–99% degenerate pivots), the ones that solve (~0.4s) yield
//      fviol ~0.18–0.19 cuts that bind at 6–12/64 later slots, and a round costs ~3s
//      against a baseline doing ~1.1k nodes/s: 20s bound 1043.3 -> 1026.1 (second
//      config, cheaper cadence: 1031.3). The reference point is decisive: plateau-GMI
//      derivations cost 0.01–0.03s a round and were ALREADY net-negative; a CGLP is a
//      whole LP per cut, 100x that, in the same transfer market.
//   3. The cuts arrive ~90% dense (the aggregation spans the model) and `clean` at half
//      the violation drops almost nothing on rout's boxes (500 -> 487 nnz), so every
//      admitted row is also a carry tax on all subsequent LPs.
// Kept: exactly-valid separator + guards + the `lnp_probe` dev harness, as the base a
// local-cut pool or a Balas–Perregaard pivot-space variant would build on. The CGLP
// conditioning fixes (2-nnz normalization `u0+v0=1`, per-instance `eager_perturb`, ge-row
// dedup, power-of-two row scaling) are load-bearing for anyone who returns here: the
// textbook simplex-sum normalization made the CGLP UNSOLVABLE outright (120s+, 16.3k of
// 17k pivots degenerate).

/// `>=`-form image of the root relaxation: rows `coeffs·x >= rhs`, plus the equality rows
/// kept exactly (multiplier sign-free) for the free-column repair in [`lnp_exact_cut`].
struct LnpGeForm {
    rows: Vec<(Vec<(u32, f64)>, f64)>,
    /// column -> (row index, coefficient) incidence over `rows`.
    cols: Vec<Vec<(u32, f64)>>,
    /// Original EQUALITY rows, exact: `coeffs·x == rhs`.
    eq_rows: Vec<(Vec<(u32, BigRational)>, BigRational)>,
}

fn lnp_ge_form(model: &Model, n_rows: usize) -> LnpGeForm {
    let n = model.num_cols();
    let mut rows: Vec<(Vec<(u32, f64)>, f64)> = Vec::new();
    let mut eq_rows = Vec::new();
    for r in 0..n_rows.min(model.num_rows()) {
        let (coeffs, lb, ub) = model.row(Row(r as u32));
        if coeffs.is_empty() || coeffs.iter().any(|&(_, a)| !a.is_finite()) {
            continue;
        }
        // POWER-OF-TWO row scaling: divide the row by `2^ceil(log2 max|a|)` — the same
        // inequality (a positive scaling permutes nothing in the multiplier cone, it only
        // reconditions the CGLP), and EXACT in f64, so the rational lane aggregates
        // precisely the numbers the CGLP saw. Without it the CGLP mixes rout's
        // coefficients (up to ~3e2, rhs ~1e3) with the normalization row's 1.0s and the
        // simplex crawls.
        let amax = coeffs.iter().fold(0.0f64, |m, &(_, a)| m.max(a.abs()));
        let mut scale = if amax > 0.0 {
            (2.0f64).powi(amax.log2().ceil() as i32).recip()
        } else {
            1.0
        };
        // Power-of-two scaling is EXACT only while every product stays a normal f64 (an
        // exponent shift; the mantissa is untouched). A subnormal result rounds, and a
        // rounded right-hand side may round UP — a row no longer implied by the model's.
        // A row that cannot be scaled exactly is used as-is.
        let exact_scaled = |v: f64| -> bool {
            let s = v * scale;
            // ⚠ `s == 0.0` is exact ONLY when the INPUT was zero (audit must-fix): a nonzero
            // coefficient whose power-of-two product UNDERFLOWS to 0.0 (1e-17 · 2^-1023) would
            // otherwise be silently dropped from a row the exact lane treats as ground truth —
            // an invalid-cut corner. Zero stays exact iff it started zero.
            s.is_finite() && ((s == 0.0 && v == 0.0) || s.abs() >= 1e-300)
        };
        if !scale.is_finite()
            || !coeffs.iter().all(|&(_, a)| exact_scaled(a))
            || (lb.is_finite() && !exact_scaled(lb))
            || (ub.is_finite() && !exact_scaled(ub))
        {
            scale = 1.0;
        }
        let scaled: Vec<(u32, f64)> = coeffs.iter().map(|&(c, a)| (c, a * scale)).collect();
        if lb.is_finite() {
            rows.push((scaled.clone(), lb * scale));
        }
        if ub.is_finite() {
            rows.push((scaled.iter().map(|&(c, a)| (c, -a)).collect(), -ub * scale));
        }
        if lb.is_finite() && lb == ub {
            let ex: Option<Vec<(u32, BigRational)>> = coeffs
                .iter()
                .map(|&(c, a)| exact(a).map(|e| (c, e)))
                .collect();
            if let (Some(ex), Some(b)) = (ex, exact(lb)) {
                eq_rows.push((ex, b));
            }
        }
    }
    for c in 0..n {
        let (lo, up) = model.col_bounds(Col(c as u32));
        if lo.is_finite() {
            rows.push((vec![(c as u32, 1.0)], lo));
        }
        if up.is_finite() {
            rows.push((vec![(c as u32, -1.0)], -up));
        }
    }
    // DEDUPLICATE: a singleton model row in `>=`-form IS a bound row, and two identical
    // rows are two identical CGLP columns — a numerically singular basis waiting to be
    // repaired mid-walk (observed on rout in-solve: "dependent column kicked" during the
    // CGLP). Keep the TIGHTER right-hand side per distinct coefficient vector.
    {
        let mut best: std::collections::HashMap<Vec<(u32, u64)>, usize> =
            std::collections::HashMap::with_capacity(rows.len());
        let mut keep: Vec<(Vec<(u32, f64)>, f64)> = Vec::with_capacity(rows.len());
        for (rc, rb) in rows.drain(..) {
            let mut key: Vec<(u32, u64)> = rc.iter().map(|&(c, a)| (c, a.to_bits())).collect();
            key.sort_unstable();
            match best.entry(key) {
                std::collections::hash_map::Entry::Occupied(e) => {
                    let k = *e.get();
                    if rb > keep[k].1 {
                        keep[k].1 = rb; // same left-hand side: the larger rhs dominates
                    }
                }
                std::collections::hash_map::Entry::Vacant(e) => {
                    e.insert(keep.len());
                    keep.push((rc, rb));
                }
            }
        }
        rows = keep;
    }
    let mut cols: Vec<Vec<(u32, f64)>> = vec![Vec::new(); n];
    for (i, (rc, _)) in rows.iter().enumerate() {
        for &(c, a) in rc {
            if (c as usize) < n {
                cols[c as usize].push((i as u32, a));
            }
        }
    }
    LnpGeForm {
        rows,
        cols,
        eq_rows,
    }
}

/// A CGLP multiplier, snapped onto a dyadic grid (denominator `<= 2^24`) and clamped
/// nonnegative. `None` means "drop the row from the aggregation" — always valid, since any
/// nonnegative multiplier vector certifies its side.
fn lnp_snap_mult(v: f64) -> Option<BigRational> {
    const GRID: f64 = 16_777_216.0; // 2^24
    if !v.is_finite() || v <= 1e-11 {
        return None;
    }
    let s = (v * GRID).round() / GRID;
    if s <= 0.0 {
        return None;
    }
    exact(s)
}

/// How many CGLPs a root round may solve. `--lnp-budget` holds the budget (`=1`..; a bare
/// or unparsable value means 4); unset/0 disables the family.
pub(crate) fn lnp_budget() -> Option<usize> {
    // B39: `--lnp-budget N` (0 or unset disables the family).
    crate::tune::count_opt(crate::tune::Knob::LnpBudget).filter(|b| *b > 0)
}

/// Separate lift-and-project cuts for `model` violated at `x`, deriving only from rows
/// `< n_rows` (callers exclude cut-slot rows) plus GLOBAL bounds — globally valid.
///
/// `budget` bounds the number of disjunction columns tried (one CGLP each, most
/// fractional first); `deadline` bounds the wall clock at CGLP boundaries.
pub(crate) fn separate_lift_project(
    model: &Model,
    x: &[f64],
    n_rows: usize,
    budget: usize,
    deadline: Option<std::time::Instant>,
) -> Vec<Cut> {
    use crate::model::Sense;
    let n = model.num_cols();
    if n == 0 || budget == 0 {
        return Vec::new();
    }
    let xv = |c: usize| x.get(c).copied().unwrap_or(0.0);
    // Disjunction candidates: integer columns fractional at `x`, most fractional first.
    let mut cand_js: Vec<(usize, f64)> = (0..n)
        .filter(|&j| !matches!(model.col_kind(Col(j as u32)), ColKind::Continuous))
        .filter_map(|j| {
            let v = xv(j);
            if !v.is_finite() || v.abs() >= 1e9 {
                return None;
            }
            let f = v - v.floor();
            let d = f.min(1.0 - f);
            (d > 1e-4).then_some((j, d))
        })
        .collect();
    if cand_js.is_empty() {
        return Vec::new();
    }
    cand_js.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
    cand_js.truncate(budget);

    let ge = lnp_ge_form(model, n_rows);
    let mr = ge.rows.len();
    if mr == 0 {
        return Vec::new();
    }
    // Row activities at `x` — the CGLP objective's data.
    let s: Vec<f64> = ge
        .rows
        .iter()
        .map(|(rc, _)| rc.iter().map(|&(c, a)| a * xv(c as usize)).sum())
        .collect();

    let trace = crate::debug_flags::milp_debug_flags().trace;
    let t0 = std::time::Instant::now();
    let mut solved = 0usize;
    let mut best_fviol = 0.0f64;
    let mut out = Vec::new();
    for &(j, _) in &cand_js {
        if deadline.is_some_and(|d| std::time::Instant::now() >= d) {
            break;
        }
        let xj = xv(j);
        let f0 = xj.floor();
        // ---- the CGLP ----
        // Variables: β and u, u0 (side 0) / v, v0 (side 1) in [0,1] boxes (the
        // normalization row caps the multipliers at 1 anyway, and `β <= u·b̃ − u0·f0`
        // bounds β by the largest right-hand side over the simplex — this engine's phase I
        // is measured to spin on genuinely free columns, so β gets the box it provably
        // lives in rather than (−inf, inf)).
        let bmax = ge
            .rows
            .iter()
            .fold(0.0f64, |m, (_, b)| m.max(b.abs()))
            .max(f0.abs() + 1.0)
            + 1.0;
        let mut g = Model::new();
        let beta = g.add_col(-bmax, bmax);
        let u: Vec<Col> = (0..mr).map(|_| g.add_col(0.0, 1.0)).collect();
        let u0 = g.add_col(0.0, 1.0);
        let v: Vec<Col> = (0..mr).map(|_| g.add_col(0.0, 1.0)).collect();
        let v0 = g.add_col(0.0, 1.0);
        // α-matching, one equality per structural column: (Ãᵀu − u0·e_j) = (Ãᵀv + v0·e_j).
        for c in 0..n {
            let mut terms: Vec<(Col, f64)> = Vec::with_capacity(2 * ge.cols[c].len() + 2);
            for &(i, a) in &ge.cols[c] {
                terms.push((u[i as usize], a));
                terms.push((v[i as usize], -a));
            }
            if c == j {
                terms.push((u0, -1.0));
                terms.push((v0, -1.0));
            }
            if !terms.is_empty() {
                g.add_row(0.0, 0.0, &terms);
            }
        }
        // β <= u·b̃ − u0·f0   and   β <= v·b̃ + v0·(f0+1).
        let mut t0: Vec<(Col, f64)> = vec![(beta, 1.0)];
        let mut t1: Vec<(Col, f64)> = vec![(beta, 1.0)];
        for i in 0..mr {
            let b = ge.rows[i].1;
            if b != 0.0 {
                t0.push((u[i], -b));
                t1.push((v[i], -b));
            }
        }
        if f0 != 0.0 {
            t0.push((u0, f0));
        }
        t1.push((v0, -(f0 + 1.0)));
        g.add_row(f64::NEG_INFINITY, 0.0, &t0);
        g.add_row(f64::NEG_INFINITY, 0.0, &t1);
        // Normalization: `u0 + v0 = 1` (with the [0,1] boxes on `u`/`v` keeping the cone
        // bounded). The textbook `Σu + u0 + Σv + v0 = 1` was tried first and is what made
        // the CGLP unsolvable here: a 2·m'-nonzero row coupling EVERY column, on whose
        // face almost every multiplier sits at zero — the simplex walked 17k pivots,
        // 16.3k of them degenerate, and never finished (measured, rout root, 120s). This
        // one is 2 nonzeros, normalizes the disjunction usage directly, and the same
        // CGLP solves in seconds.
        g.add_row(1.0, 1.0, &[(u0, 1.0), (v0, 1.0)]);
        // Objective: the cut's violation at x*, `β − α·x* = β − Σ s_i u_i + u0·x*_j`.
        let mut obj: Vec<(u32, f64)> = Vec::with_capacity(mr + 2);
        obj.push((beta.index() as u32, 1.0));
        for i in 0..mr {
            if s[i] != 0.0 {
                obj.push((u[i].index() as u32, -s[i]));
            }
        }
        obj.push((u0.index() as u32, xj));
        let Some(mut clp) = FloatLp::from_model(&g, &obj, Sense::Maximize) else {
            continue;
        };
        // The CGLP is a measured degenerate crawl on the lazy path (rout: 8/12 solves
        // ground 20k+ zero-length pivots; eagerly all 12 solve in 0.1-0.3s) — see the
        // field's note. Scoped to THIS instance; nothing else changes path.
        clp.eager_perturb = true;
        // One CGLP may not eat the round.
        let cglp_secs: f64 = 2.0;
        let cglp_deadline = {
            let cap = std::time::Instant::now() + std::time::Duration::from_secs_f64(cglp_secs);
            Some(deadline.map_or(cap, |d| d.min(cap)))
        };
        let t_one = std::time::Instant::now();
        // A degenerate CGLP is abandoned at an iteration budget, not ridden to the wall
        // clock: the healthy ones solve in ~2-3k pivots (measured), the stalled ones walk
        // 50k+ degenerate pivots without moving — spend the round's time on the next
        // candidate instead.
        let sol = {
            let _cap = crate::simplex::IterCap::set(20_000);
            clp.solve(cglp_deadline)
        };
        solved += 1;
        if trace {
            eprintln!(
                "--trace     lnp cglp j={j} x_j={xj:.4} status={:?} t={:.2}s",
                sol.status,
                t_one.elapsed().as_secs_f64()
            );
        }
        if sol.status != crate::simplex::SimplexStatus::Optimal {
            continue;
        }
        // Float screen: the CGLP's own violation estimate. The exact lane re-decides.
        let fviol: f64 = sol.values[beta.index()]
            - (0..mr)
                .map(|i| s[i] * sol.values[u[i].index()])
                .sum::<f64>()
            + xj * sol.values[u0.index()];
        best_fviol = best_fviol.max(fviol);
        if fviol <= MIN_VIOLATION {
            continue;
        }
        let mult = |c: Col| sol.values.get(c.index()).copied().unwrap_or(0.0);
        let mu: Vec<Option<BigRational>> = u.iter().map(|&c| lnp_snap_mult(mult(c))).collect();
        let mv: Vec<Option<BigRational>> = v.iter().map(|&c| lnp_snap_mult(mult(c))).collect();
        if let Some(cut) = lnp_exact_cut(
            model,
            x,
            &ge,
            j,
            f0,
            &mu,
            lnp_snap_mult(mult(u0)),
            &mv,
            lnp_snap_mult(mult(v0)),
        ) {
            let mut cut = cut;
            // A CGLP cut arrives DENSE (rout: ~500 nnz on 556 columns — the aggregation
            // covers most of the model), and the root pool refuses anything past its nnz
            // cap. Spend half the violation sparsifying HERE, where the violation is
            // still whole — the same trade the node-GMI block makes, same license
            // (`clean` pays for every dropped term out of the right-hand side).
            if cut.clean(model, x, 0.5) {
                out.push(cut);
            }
        }
    }
    if trace {
        let nnz_max = out.iter().map(|c| c.coeffs.len()).max().unwrap_or(0);
        eprintln!(
            "--trace   lnp: {} cuts from {solved}/{} CGLPs (ge_rows={mr}) fviol_max={best_fviol:.4} nnz_max={nnz_max} t={:.2}s",
            out.len(),
            cand_js.len(),
            t0.elapsed().as_secs_f64()
        );
    }
    out
}

/// Exact reconstruction: from nonnegative rational multipliers, derive both branch
/// inequalities, merge them over the box, and embed in f64 — every step outward-rigorous.
/// `None` when the merge cannot be paid (an unbounded column the repair cannot reach) or
/// the surviving cut no longer cuts.
#[allow(clippy::too_many_arguments)]
fn lnp_exact_cut(
    model: &Model,
    x: &[f64],
    ge: &LnpGeForm,
    j: usize,
    f0: f64,
    mu: &[Option<BigRational>],
    mu0: Option<BigRational>,
    mv: &[Option<BigRational>],
    mv0: Option<BigRational>,
) -> Option<Cut> {
    let n = model.num_cols();
    let mut a0 = vec![BigRational::zero(); n];
    let mut a1 = vec![BigRational::zero(); n];
    let mut b0 = BigRational::zero();
    let mut b1 = BigRational::zero();
    for (side_m, side_a, side_b) in [(mu, &mut a0, &mut b0), (mv, &mut a1, &mut b1)] {
        for (i, m) in side_m.iter().enumerate() {
            let Some(m) = m else { continue };
            let (rc, rb) = &ge.rows[i];
            for &(c, a) in rc {
                if (c as usize) < n {
                    side_a[c as usize] += m * exact(a)?;
                }
            }
            *side_b += m * exact(*rb)?;
        }
    }
    let ef0 = exact(f0)?;
    if let Some(m0) = &mu0 {
        a0[j] -= m0;
        b0 -= m0 * &ef0;
    }
    if let Some(m1) = &mv0 {
        a1[j] += m1;
        b1 += m1 * (&ef0 + BigRational::one());
    }

    // FREE-COLUMN REPAIR. The merge below pays a per-column difference over the column's
    // box, so a column with NO finite bound must have `a0_c == a1_c` — and equal to an
    // exactly-representable f64, or the embedding cannot be paid either. An equality row's
    // multiplier is sign-free, so adding `t·(row)` to a side keeps it valid for any
    // rational `t`; solve for the `t` that lands the free column's coefficient exactly on
    // the f64 target. The row's other columns get perturbed and their boxes pay for it —
    // rows containing a SECOND unbounded column are refused.
    for c in 0..n {
        let (lo, up) = model.col_bounds(Col(c as u32));
        if lo.is_finite() || up.is_finite() {
            continue;
        }
        if a0[c] == a1[c] {
            if a0[c].is_zero() {
                continue; // 0 is representable; nothing to repair
            }
            if exact(to_f64(&a0[c])).as_ref() == Some(&a0[c]) {
                continue;
            }
        }
        let target = exact(to_f64(&a0[c]))?;
        let row = ge.eq_rows.iter().find(|(rc, _)| {
            rc.iter().any(|(cc, aa)| *cc as usize == c && !aa.is_zero())
                && rc.iter().all(|(cc, _)| {
                    *cc as usize == c || {
                        let (l2, u2) = model.col_bounds(Col(*cc));
                        l2.is_finite() || u2.is_finite()
                    }
                })
        })?;
        let gcoef = &row.0.iter().find(|(cc, _)| *cc as usize == c)?.1;
        for (side_a, side_b) in [(&mut a0, &mut b0), (&mut a1, &mut b1)] {
            let d = &target - &side_a[c];
            if d.is_zero() {
                continue;
            }
            let t = d / gcoef;
            for (cc, aa) in &row.0 {
                side_a[*cc as usize] += &t * aa;
            }
            *side_b += &t * &row.1;
        }
    }

    // MERGE: per column, α_c ∈ {a0_c, a1_c}; the side left behind pays
    // `min(d·lo, d·up)` (exact) into its right-hand side. Choosing the MAX when the lower
    // bound is finite makes `d >= 0` so the payment is `d·lo` (finite); the MIN when only
    // the upper is finite makes `d <= 0` so it is `d·up`.
    let mut alpha = a0; // reuse side 0's vector; `alpha[c]` still holds `a0_c` until chosen
    let mut pay0 = BigRational::zero();
    let mut pay1 = BigRational::zero();
    for c in 0..n {
        if alpha[c] == a1[c] {
            continue;
        }
        let (lo, up) = model.col_bounds(Col(c as u32));
        let pick_max = lo.is_finite();
        if !pick_max && !up.is_finite() {
            return None; // free column the repair could not reach
        }
        let a0c = alpha[c].clone();
        let chosen = if pick_max {
            if a0c >= a1[c] {
                a0c.clone()
            } else {
                a1[c].clone()
            }
        } else if a0c <= a1[c] {
            a0c.clone()
        } else {
            a1[c].clone()
        };
        let bnd = exact(if pick_max { lo } else { up })?;
        for (a_sc, pay) in [(&a0c, &mut pay0), (&a1[c], &mut pay1)] {
            let d = &chosen - a_sc;
            if !d.is_zero() {
                *pay += d * &bnd;
            }
        }
        alpha[c] = chosen;
    }
    let beta = {
        let s0 = b0 + pay0;
        let s1 = b1 + pay1;
        if s0 <= s1 {
            s0
        } else {
            s1
        }
    };

    // f64 EMBEDDING: round each α_c to a representable value, pay the rounding over the
    // box (forcing the payable sign when only one side is finite), and round β DOWN.
    let mut coeffs: Vec<(Col, f64)> = Vec::new();
    let mut adjust = BigRational::zero();
    for c in 0..n {
        if alpha[c].is_zero() {
            continue;
        }
        let (lo, up) = model.col_bounds(Col(c as u32));
        let mut af = to_f64(&alpha[c]);
        if !af.is_finite() {
            return None;
        }
        let mut d = exact(af)? - &alpha[c];
        if !d.is_zero() {
            if !lo.is_finite() && !up.is_finite() {
                return None; // repaired columns land exactly; anything else is unpayable
            }
            if !up.is_finite() && d < BigRational::zero() {
                af = next_up(af); // need d >= 0: pay via lo
                d = exact(af)? - &alpha[c];
            } else if !lo.is_finite() && d > BigRational::zero() {
                af = next_down(af); // need d <= 0: pay via up
                d = exact(af)? - &alpha[c];
            }
            if !d.is_zero() {
                let contrib = match (lo.is_finite(), up.is_finite()) {
                    (true, true) => {
                        let p = &d * exact(lo)?;
                        let q = d * exact(up)?;
                        if p <= q {
                            p
                        } else {
                            q
                        }
                    }
                    (true, false) => d * exact(lo)?,
                    (false, true) => d * exact(up)?,
                    (false, false) => return None,
                };
                adjust += contrib;
            }
        }
        if af != 0.0 {
            coeffs.push((Col(c as u32), af));
        }
    }
    if coeffs.is_empty() {
        return None;
    }
    let beta_adj = beta + adjust;
    let mut lbf = to_f64(&beta_adj);
    if !lbf.is_finite() {
        return None;
    }
    if exact(lbf)? > beta_adj {
        lbf = next_down(lbf);
    }
    let cut = Cut {
        coeffs,
        lb: lbf,
        ub: f64::INFINITY,
    };
    clears_min_violation(&cut, x).then_some(cut)
}

#[cfg(test)]
mod lnp_tests {
    use super::*;
    use crate::model::Sense;

    /// The textbook disjunctive hull, as non-vacuity: `P = {2x1 + 2x2 <= 3, x ∈ [0,1]^2}`
    /// at the fractional point `(1/2, 1)`. The hull of the `x1`-disjunction is
    /// `x2 <= 1 − x1/2` (through `(0,1)` and `(1,1/2)`), so the point is violated by `1/4`
    /// and the CGLP must find a cut at least that deep. This is the test that fails if
    /// the family silently separates nothing.
    #[test]
    fn lift_project_separates_the_textbook_disjunction() {
        let mut m = Model::new();
        let x1 = m.add_binary_col();
        let x2 = m.add_col(0.0, 1.0);
        m.add_row(f64::NEG_INFINITY, 3.0, &[(x1, 2.0), (x2, 2.0)]);
        m.set_objective(&[(x1, -1.0), (x2, -1.0)], Sense::Minimize);
        let x = vec![0.5, 1.0];
        let cuts = separate_lift_project(&m, &x, m.num_rows(), 4, None);
        assert!(
            !cuts.is_empty(),
            "the CGLP must separate the textbook point (1/2, 1)"
        );
        // Violation is not scale-invariant (the CGLP normalizes the MULTIPLIERS, so the
        // returned cut is a scaled copy of the hull facet); efficacy — violation over the
        // coefficient norm, i.e. Euclidean depth — is. The facet `x1/2 + x2 <= 1` has
        // depth `0.25/√1.25 ≈ 0.2236` at `(1/2, 1)`.
        let best = cuts.iter().map(|c| efficacy(c, &x)).fold(0.0f64, f64::max);
        assert!(
            best > 0.2,
            "hull depth at (1/2,1) is ~0.2236; the CGLP found only {best}"
        );
        // ...and the hull's own integer points must all survive every cut.
        for p in [[0.0, 0.0], [0.0, 1.0], [1.0, 0.0], [1.0, 0.5]] {
            for c in &cuts {
                let act: f64 = c.coeffs.iter().map(|&(col, a)| a * p[col.index()]).sum();
                assert!(
                    act >= c.lb - 1e-9,
                    "cut deleted the integer point {p:?}: activity {act} < lb {}",
                    c.lb
                );
            }
        }
    }

    /// A CUT MAY NOT DELETE AN INTEGER POINT — the same brute-force guarantee every other
    /// family in this file owes (see `mir_cuts_never_remove_an_integer_point`), on models
    /// carrying exactly the structures this family's exact lane has to get right: general
    /// (non-binary) integers, continuous columns, EQUALITY rows (the sign-free multiplier
    /// split AND the free-column repair path), a FREE continuous column threaded through
    /// an equality (the repair itself), and one-sided boxes (the `pick_max`/`pick_min`
    /// payment directions).
    ///
    /// FAIL-ON-BUG VERIFIED (2026-07-17), against the construction's actual trust
    /// surface. The exact lane RE-DERIVES validity from the aggregation, so most
    /// plausible-looking injections are provably absorbed rather than missed: a sign flip
    /// on the side-1 disjunction coefficient re-enters through the merge's `max` and the
    /// side-1 points over-deliver exactly what the `lo = 0` payment under-counts (checked
    /// by hand AND observed: the guard keeps passing because the emitted cuts are still
    /// valid), and a one-sided rhs inflation is masked by the `min` taking the honest
    /// side. What the construction actually TRUSTS is the conic arithmetic itself, and
    /// corrupting that is caught: `beta_adj + 1/10` (rhs over-claim past the payments)
    /// fails this test at case 0 — on a point with the FREE column at `-2.0`, so the
    /// repair path is under the enumeration too — and fails the textbook test at
    /// `[0,1]`; inflating every aggregated right-hand side by `1/4` inside
    /// `lnp_exact_cut` fails both as well.
    #[test]
    fn lift_project_cuts_never_remove_an_integer_point() {
        let mut seed = 0x1AF7_2026_u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };
        const HI: i64 = 3;
        let mut produced = 0usize;

        for case in 0..200 {
            let mut m = Model::new();
            // Columns: two general integers, one binary, one continuous box, and (every
            // third case) a FREE continuous column defined by an equality — the repair's
            // home turf.
            let c0 = m.add_int_col(0.0, HI as f64);
            let c1 = m.add_int_col(0.0, HI as f64);
            let c2 = m.add_binary_col();
            let c3 = m.add_col(0.0, HI as f64);
            let mut cols = vec![c0, c1, c2, c3];
            let mut rows: Vec<(Vec<f64>, f64, f64)> = Vec::new();
            let free_defined = case % 3 == 0;
            if free_defined {
                let cf = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
                cols.push(cf);
                // cf == Σ small · (c0..c3)  — an equality DEFINING the free column.
                let a: Vec<f64> = (0..4).map(|_| (rnd() % 5 - 2) as f64).collect();
                let mut terms: Vec<(Col, f64)> = cols[..4]
                    .iter()
                    .zip(&a)
                    .filter(|(_, &v)| v != 0.0)
                    .map(|(&c, &v)| (c, v))
                    .collect();
                terms.push((cf, -1.0));
                m.add_row(0.0, 0.0, &terms);
                let mut ra = a.clone();
                ra.push(-1.0);
                rows.push((ra, 0.0, 0.0));
                // ...and the free column has to MATTER: it appears in an inequality.
                let b = (rnd() % 7) as f64;
                m.add_row(f64::NEG_INFINITY, b, &[(cf, 1.0), (c0, 1.0)]);
                rows.push((vec![1.0, 0.0, 0.0, 0.0, 1.0], f64::NEG_INFINITY, b));
            }
            let n = cols.len();
            for _ in 0..2 {
                let a: Vec<f64> = (0..n)
                    .map(|k| if k == 4 { 0.0 } else { (rnd() % 9 - 4) as f64 })
                    .collect();
                if a.iter().all(|&v| v == 0.0) {
                    continue;
                }
                let hi = (rnd() % 13) as f64;
                // Every third row an EQUALITY: the sign-free multiplier structure.
                let lo = if rnd() % 3 == 0 {
                    hi
                } else {
                    hi - (1 + rnd() % 10) as f64
                };
                let terms: Vec<(Col, f64)> = cols
                    .iter()
                    .zip(&a)
                    .filter(|(_, &v)| v != 0.0)
                    .map(|(&c, &v)| (c, v))
                    .collect();
                if terms.is_empty() {
                    continue;
                }
                m.add_row(lo, hi, &terms);
                rows.push((a, lo, hi));
            }
            if rows.is_empty() {
                continue;
            }
            m.set_objective(&[(cols[0], 1.0)], Sense::Minimize);

            // TWO separation points. An arbitrary fractional point (validity may not
            // depend on where the cut was asked for) — but a point OUTSIDE `P` lets the
            // CGLP cut it with a plain conic combination (`u0 = v0 = 0`), never touching
            // the disjunction bookkeeping. So ALSO the LP OPTIMUM of a random objective:
            // a point of `P` can only be cut THROUGH the disjunction (`u0, v0 > 0` — a
            // pure conic combination is satisfied by every point of `P`), which is what
            // pins the `f`/`f+1` right-hand sides and the `e_j` terms under the
            // enumeration.
            let x: Vec<f64> = (0..n).map(|_| (rnd() % 60) as f64 / 20.0).collect();
            let mut cuts = separate_lift_project(&m, &x, m.num_rows(), 3, None);
            let objective: Vec<(u32, f64)> =
                (0..4u32).map(|c| (c, (rnd() % 5 - 2) as f64)).collect();
            if let Some(lp) = FloatLp::from_model(&m, &objective, Sense::Minimize) {
                let cand = lp.solve_bounded(&lp.lower.clone(), &lp.upper.clone(), None, None);
                if cand.status == crate::simplex::SimplexStatus::Optimal {
                    cuts.extend(separate_lift_project(
                        &m,
                        &cand.values[..n],
                        m.num_rows(),
                        3,
                        None,
                    ));
                }
            }
            produced += cuts.len();

            // Enumerate: integers on their integer grid, the bounded continuous column on
            // a HALF-integer grid (a cut leaning on fractional continuous values must be
            // caught too), and the free column COMPUTED from its defining equality — any
            // feasible point has exactly that value, so the enumeration covers the
            // feasible set it claims to.
            let grids: Vec<Vec<f64>> = cols
                .iter()
                .take(4)
                .map(|&c| {
                    let (lo, up) = m.col_bounds(c);
                    let step = if matches!(m.col_kind(c), ColKind::Continuous) {
                        0.5
                    } else {
                        1.0
                    };
                    assert!(
                        lo.is_finite() && up.is_finite() && lo <= up,
                        "enumerated columns must have finite, ordered bounds"
                    );
                    let last_candidate = ((up - lo) / step).ceil() as usize;
                    (0..=last_candidate)
                        .map(|offset| lo + offset as f64 * step)
                        .filter(|&value| value <= up + 1e-9)
                        .collect()
                })
                .collect();
            let total: usize = grids.iter().map(Vec::len).product();
            for code in 0..total {
                let mut p = vec![0.0f64; n];
                let mut t = code;
                for (k, g) in grids.iter().enumerate() {
                    p[k] = g[t % g.len()];
                    t /= g.len();
                }
                if free_defined {
                    // rows[0] is the defining equality `Σ a·(c0..c3) − cf == 0`.
                    let a = &rows[0].0;
                    p[4] = (0..4).map(|k| a[k] * p[k]).sum();
                }
                let feasible = rows.iter().all(|(a, lo, hi)| {
                    let act: f64 = a.iter().zip(&p).map(|(&c, &v)| c * v).sum();
                    act >= lo - 1e-9 && act <= hi + 1e-9
                });
                if !feasible {
                    continue;
                }
                for c in &cuts {
                    let act: f64 = c.coeffs.iter().map(|&(col, a)| a * p[col.index()]).sum();
                    assert!(
                        act >= c.lb - 1e-6,
                        "case {case}: a lift-and-project cut deleted the point {p:?} -- \
                         activity {act} below its bound {}",
                        c.lb
                    );
                }
            }
        }
        eprintln!("LNP GUARD produced {produced} cuts");
        assert!(produced > 0, "the guard never exercised a single cut");
    }

    /// Exercise the root-LP-to-CGLP pipeline on a deterministic in-memory
    /// model. `--lnp-probe=<file.mps>` optionally runs the same
    /// diagnostic on a developer model after the mandatory regression.
    #[test]
    fn lnp_root_lp_pipeline_produces_a_valid_cut() {
        let mut model = Model::new();
        let x1 = model.add_binary_col();
        let x2 = model.add_col(0.0, 1.0);
        model.add_row(f64::NEG_INFINITY, 3.0, &[(x1, 2.0), (x2, 2.0)]);
        // Weight x2 more heavily so the unique root optimum is (1/2, 1):
        // the integer column itself is fractional and must be separated.
        model.set_objective(&[(x1, -1.0), (x2, -3.0)], Sense::Minimize);
        let objective = vec![(x1.index() as u32, -1.0), (x2.index() as u32, -3.0)];
        let lp = FloatLp::from_model(&model, &objective, Sense::Minimize).expect("bounded root LP");
        let candidate = lp.solve_bounded(&lp.lower.clone(), &lp.upper.clone(), None, None);
        assert_eq!(
            candidate.status,
            crate::simplex::SimplexStatus::Optimal,
            "textbook root relaxation must solve"
        );
        assert!(
            (candidate.values[x1.index()] - 0.5).abs() <= 1e-9
                && (candidate.values[x2.index()] - 1.0).abs() <= 1e-9,
            "weighted root objective must expose the intended fractional point, got {:?}",
            &candidate.values[..model.num_cols()]
        );
        let cuts = separate_lift_project(
            &model,
            &candidate.values[..model.num_cols()],
            model.num_rows(),
            4,
            Some(std::time::Instant::now() + std::time::Duration::from_secs(5)),
        );
        assert!(
            cuts.iter()
                .any(|cut| violation(cut, &candidate.values) > 1e-7),
            "root-LP pipeline must separate its fractional optimum"
        );
        for point in [[0.0, 0.0], [0.0, 1.0], [1.0, 0.0], [1.0, 0.5]] {
            for cut in &cuts {
                let activity: f64 = cut
                    .coeffs
                    .iter()
                    .map(|&(col, coeff)| coeff * point[col.index()])
                    .sum();
                assert!(
                    activity >= cut.lb - 1e-9,
                    "root-pipeline cut removed integer point {point:?}"
                );
            }
        }

        let Some(path) = crate::debug_flags::milp_debug_flags().lnp_probe else {
            return;
        };
        let text = std::fs::read_to_string(&path).expect("readable mps");
        let p = crate::mps::read_mps(&text).expect("parses");
        let mut owned = p.model.clone();
        if crate::tune::caller_flag(crate::tune::Knob::LnpProbePresolve) == Some(true) {
            if let crate::presolve::Presolved::Tightened(t) =
                crate::presolve::tighten_bounds(&owned, None)
            {
                owned = *t;
                eprintln!("probe: presolved");
            }
        }
        let m = &owned;
        let obj: Vec<(u32, f64)> = (0..m.num_cols())
            .filter_map(|j| {
                let c = m.obj_coeff(Col(j as u32));
                (c != 0.0).then_some((j as u32, c))
            })
            .collect();
        let lp = FloatLp::from_model(m, &obj, m.sense()).expect("lp");
        let t0 = std::time::Instant::now();
        let cand = lp.solve_bounded(&lp.lower.clone(), &lp.upper.clone(), None, None);
        eprintln!(
            "root LP: {:?} in {:.2}s",
            cand.status,
            t0.elapsed().as_secs_f64()
        );
        let budget: usize = std::env::var("--lnp-budget")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(4);
        let t1 = std::time::Instant::now();
        let cuts = separate_lift_project(
            m,
            &cand.values[..m.num_cols()],
            m.num_rows(),
            budget,
            Some(std::time::Instant::now() + std::time::Duration::from_mins(10)),
        );
        eprintln!(
            "lnp probe: {} cuts in {:.2}s",
            cuts.len(),
            t1.elapsed().as_secs_f64()
        );
        for c in &cuts {
            eprintln!(
                "  cut nnz={} viol={:.5} eff={:.5}",
                c.coeffs.len(),
                violation(c, &cand.values),
                efficacy(c, &cand.values)
            );
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
/// of the crate: 4 accessors here cache their value in a `OnceLock` and call
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
    let _ = min_violation();
    let _ = mir_genint_off();
    let _ = relax_lift_enabled();
    let _ = screen_audit();
    let _ = screen_off();
}

#[cfg(test)]
mod post_filter_census_tests;

#[cfg(test)]
mod shape_gate_tests {
    use super::{is_wide_shape, MAX_CUTS_PER_ROUND, NARROW_CUTS_PER_ROUND, WIDE_CUTS_PER_ROUND};

    /// The corpus shapes this gate was measured on, as `(rows, cols)`.
    ///
    /// NARROW summed **-3.746 s** under `--cuts-per-round=8` with both arms seeded;
    /// WIDE summed **+2.645 s**. The predicate has to reproduce that partition exactly, or the
    /// default it drives is not the one that was measured.
    const NARROW: &[(usize, usize, &str)] = &[
        (503, 1541, "qnet1 -2.053s"),
        (1192, 840, "qiu -1.009s"),
        (212, 260, "misc07 -0.665s"),
        (133, 201, "p0201 -0.068s"),
        (290, 548, "dcmulti -0.048s"),
        (274, 353, "blend2 -0.037s"),
        (18, 18, "flugpl 0.000s"),
        (291, 556, "rout 0.000s"),
        (780, 870, "gen +0.003s"),
        (45, 86, "pk1 +0.131s"),
    ];
    const WIDE: &[(usize, usize, &str)] = &[
        (12, 151, "mas76 +1.994s"),
        (101, 1350, "khb05250 +0.546s"),
        (124, 10757, "air03 +0.100s"),
        (146, 2655, "mod010 +0.012s"),
        (6, 62, "markshare1 -0.002s"),
        (7, 74, "markshare2 -0.005s"),
        (13, 151, "mas74 (held out; sibling of mas76)"),
        (426, 7195, "air05 (held out)"),
    ];

    #[test]
    fn the_shape_predicate_reproduces_the_measured_partition() {
        for &(r, c, who) in NARROW {
            assert!(
                !is_wide_shape(r, c),
                "{who}: {r}x{c} (ratio {:.2}) must be NARROW -- it GAINED under the wider budget",
                c as f64 / r as f64
            );
        }
        for &(r, c, who) in WIDE {
            assert!(
                is_wide_shape(r, c),
                "{who}: {r}x{c} (ratio {:.2}) must be WIDE -- it LOST under the wider budget",
                c as f64 / r as f64
            );
        }
    }

    /// What the corpus actually pins, stated honestly: the measurement separates the two classes
    /// anywhere in `(3.06, 10.33]`, NOT at 4 uniquely. Four is chosen because
    /// `default_root_cut_eff_floor` already uses that exact predicate for the same reason
    /// (knapsack-shaped models want fewer, better cuts), so the gate adds no new fitted number.
    /// This test fails if someone "tunes" the threshold outside the measured margin.
    #[test]
    fn the_threshold_sits_inside_the_measured_margin() {
        let widest_narrow = NARROW
            .iter()
            .map(|&(r, c, _)| c as f64 / r as f64)
            .fold(0.0_f64, f64::max);
        let narrowest_wide = WIDE
            .iter()
            .map(|&(r, c, _)| c as f64 / r as f64)
            .fold(f64::INFINITY, f64::min);
        assert!(
            widest_narrow < 4.0 && 4.0 <= narrowest_wide,
            "threshold 4 left the measured margin ({widest_narrow:.2}, {narrowest_wide:.2}]"
        );
    }

    #[test]
    fn a_degenerate_shape_is_never_wide() {
        // `num_rows == 0` would divide by zero; the guard must hold before the ratio is formed.
        assert!(!is_wide_shape(0, 100));
        assert!(!is_wide_shape(0, 0));
    }

    #[test]
    fn the_narrow_budget_is_strictly_wider_than_the_flat_default() {
        assert!(
            NARROW_CUTS_PER_ROUND > MAX_CUTS_PER_ROUND,
            "the gate only means anything if narrow models get MORE cuts than the flat default"
        );
    }

    /// The gate moves the two regimes in OPPOSITE directions, and that is the whole point: the
    /// corpus says narrow models are starved of cuts and wide models are over-served by them.
    /// A change that collapsed either side back onto the flat four would silently discard one
    /// half of the measurement.
    #[test]
    fn the_two_regimes_straddle_the_flat_default() {
        assert!(
            WIDE_CUTS_PER_ROUND < MAX_CUTS_PER_ROUND
                && MAX_CUTS_PER_ROUND < NARROW_CUTS_PER_ROUND,
            "expected wide {WIDE_CUTS_PER_ROUND} < flat {MAX_CUTS_PER_ROUND} < narrow {NARROW_CUTS_PER_ROUND}"
        );
    }

    /// Wide models keep a MINIMAL cut stream rather than none. `cpr=0` measured as a statistical
    /// tie (26.564 s vs 26.596 s over the wide subset) and was declined as the larger behavioural
    /// change; if someone later drops this to zero they should do it on evidence, not by drift.
    #[test]
    fn the_wide_budget_still_separates_something() {
        assert!(
            WIDE_CUTS_PER_ROUND > 0,
            "wide models keep one cut per round; zero ties it on this corpus but disables              separation outright, which the corpus cannot justify"
        );
    }
}

// =================================================================================================
// ACTIVE ADVERSARIAL SOUNDNESS HARNESS.
//
// Independent of the patch author's guards: its own model generator, its own enumerator, its own
// feasibility algebra. The contract under test is the only one that matters for an EXACT solver:
//
//    every point that is feasible for the MODEL must satisfy every cut the family emits.
//
// Design choices that make the check a PROOF rather than a sample:
//   * every column but one is integer/binary, and they are enumerated over their whole grid;
//   * the single continuous column's feasible set, given the fixed integers, is an INTERVAL that
//     is computed exactly from the rows -- and a cut is linear in it, so checking the two
//     endpoints checks the whole interval. Nothing is sampled.
// =================================================================================================
#[cfg(test)]
mod adversarial_knap_soundness;
#[cfg(test)]
mod adversarial_knap_soundness2;

mod rlt;
pub(crate) use rlt::separate_rlt;
