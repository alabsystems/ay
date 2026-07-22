// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Standalone primal stochastic local search (SLS) for pseudo-Boolean
//! optimization — a WalkSAT / min-conflicts-style flip search that finds a
//! *feasible* assignment from scratch (no warm start required) and then drives
//! the objective down while staying feasible. This is the missing "first-class
//! primal" capability described in
//! the development design notes: on OPT-LIN
//! instances where the complete engine cannot land even a first incumbent within
//! budget (returning UNKNOWN with no `o` line), SLS can often find and stream a
//! verified feasible incumbent.
//!
//! # Two-phase search
//! 1. **Feasibility hunt** (the dominant win): treat every hard constraint as a
//!    weighted penalty and flip variables to reduce total weighted violation,
//!    PAWS-style (bump the weights of constraints that stay violated to escape
//!    plateaus), with WalkSAT random-walk noise. Pure feasibility — the objective
//!    is ignored until the first feasible point is reached.
//! 2. **Objective descent**: once feasible, greedily look for flips that *keep
//!    every constraint feasible* and strictly lower the objective, with occasional
//!    randomized sideways/uphill moves to escape local optima. Each strictly
//!    better feasible point is streamed as a new incumbent.
//!
//! OPT-IN ([`SlsOptions::restarts`], the diversified-worker arm — design §2.3;
//! default OFF): on stagnation ([`RESTART_DWELL_THRESHOLD`] progress-free
//! flips, scaled up on very large instances — see [`RESTART_DWELL_OCC_DIVISOR`]
//! — and growing geometrically per fired restart — see
//! [`RESTART_DWELL_GROWTH`]) the search fires LAYERED RESTARTS (design §3.1),
//! cycling biased-random → best-incumbent intensification →
//! externally-provided seed point (the last only when the caller passes
//! candidates via [`SlsOptions::external_seeds`]). PAWS weights persist across
//! restarts; see [`reseat_assignment`].
//!
//! OPT-IN quality increments (design §2.2 — "PAWS default now, DDFW+CC as
//! earn-as-you-go A/B increments" on the 60-strictly-suboptimal axis; both
//! DEFAULT OFF, both A/B-gated diversified-worker arms, both riding the same
//! O(touched) incremental update loop):
//! * **DDFW weight transfer** ([`SlsOptions::weighting`] =
//!   [`WeightScheme::Ddfw`]): stuck events TRANSFER weight into each violated
//!   row from its max-weight satisfied neighbor instead of bumping additively
//!   — see [`Tracker::ddfw_transfer_weights`].
//! * **Smoothed Configuration Checking** ([`SlsOptions::scc`]): one
//!   configuration bit per variable gates the feasibility-phase greedy pick,
//!   with cadenced random smoothing — see [`Tracker::scc_mark_flip`] /
//!   [`Tracker::scc_smooth`].
//!
//! Either becomes a default only on a demonstrated net A/B win; until then the
//! default trajectory is bit-identical to the pre-DDFW/SCC search.
//!
//! # Scope (v1, honestly linear)
//! Like LNS, this v1 is **linear-PB only**: every term must be a single literal.
//! The incremental left-hand-side tracker is exact only for linear terms. The
//! caller (`crate::portfolio`) gates on `is_linear` before invoking SLS; this
//! module additionally rejects any non-linear term defensively.
//!
//! # Soundness (NON-NEGOTIABLE)
//! This module can only ever PROPOSE feasible incumbents; it can NEVER claim a
//! global OPTIMUM or UNSAT.
//!
//! 1. The incremental constraint/objective trackers are *advisory* — used only to
//!    steer the search. They never decide what is reported. A bug in them can
//!    only degrade search quality, never correctness.
//! 2. Every candidate the search wants to report is first re-verified by the
//!    caller through `sanitize_optimization_incumbent`, which runs
//!    `verify_all_constraints` against ALL original constraints AND recomputes the
//!    objective exactly with `eval_objective`. Defensively, this module ALSO
//!    re-verifies with `verify_all_constraints` and recomputes the objective with
//!    `eval_objective` before invoking `on_improve`, and only ever reports a
//!    strictly-improving feasible point. An infeasible or mis-valued "incumbent"
//!    is therefore impossible to emit.
//! 3. The function returns at most an improved feasible assignment plus its exact
//!    objective. It NEVER returns a "proven optimum" or "infeasible" verdict; the
//!    caller treats the result as `Satisfiable` only.
//! 4. The PRNG is seeded deterministically from instance *structure* only (reusing
//!    [`crate::optimize::lns::structural_seed`]), never from system entropy and
//!    never from any instance identity, so runs are bit-for-bit reproducible.

use crate::eval::verify_all_constraints;
use crate::optimize::lns::{structural_seed, SplitMix64};
use crate::optimize::unified_score::{rows_fit, ScoreInt};
use crate::solver::eval_objective;
use crate::types::{PbInstance, PbObjective, PbRel, PbTerm};

/// Maximum number of variables an SLS run will accept. Above this the
/// per-flip bookkeeping and the periodic full re-verification become too coarse
/// to help within a time slice; decline (mirrors LNS's `MAX_LNS_VARS`).
const MAX_SLS_VARS: usize = 200_000;

/// Maximum total number of constraint *occurrences* (sum of constraint sizes) the
/// inverse index will build. Declining above this keeps the index from blowing up
/// on the very large families (e.g. the DEC-LIN-13 shape of 24M constraints).
///
/// This size-decline check ALSO bounds the optional DDFW/SCC row-members index
/// ([`RowMembers`], built only for those A/B arms): it holds exactly one `u32`
/// per occurrence plus one `u32` per row, so its memory (≤ ~32 MB at this cap,
/// on top of the base tracker) can never exceed the occurrence index it mirrors
/// — an instance too large for the CSR was already declined here.
const MAX_SLS_OCCURRENCES: usize = 8_000_000;

/// Hard cap on flips per call, independent of the deadline, so an absent deadline
/// still terminates (e.g. in unit tests).
const MAX_FLIPS: u64 = 200_000_000;

/// How often (in flips) to poll the stop signal / deadline. Polling every flip
/// would dominate the cost; a coarse interval keeps the inner loop tight while
/// still stopping promptly.
const STOP_POLL_INTERVAL: u64 = 1024;

/// WalkSAT random-walk probability (in 1/1000): with this probability the
/// feasibility phase picks a random variable from the chosen violated constraint
/// rather than the greedy best one. Classic WalkSAT noise to escape plateaus.
const WALK_NOISE_PERMILLE: u64 = 200;

/// Number of consecutive non-improving feasibility flips after which the PAWS-style
/// constraint weights are bumped (raising the cost of currently-violated
/// constraints so the search is pushed out of a plateau).
const PAWS_BUMP_INTERVAL: u64 = 1;

// ---- DDFW weight-transfer scheme (design §2.2, A/B-gated diversified arm) ----

/// DDFW stuck-event cadence (A/B-tunable pin): consecutive non-improving
/// feasibility flips before a DDFW weight-transfer sweep fires — the
/// [`WeightScheme::Ddfw`] counterpart of [`PAWS_BUMP_INTERVAL`], kept at the
/// same trigger cadence so the two schemes differ only in HOW weight moves,
/// not WHEN escalation happens. Improving flips reset the counter, so the
/// sweep never runs on a converging trajectory — only on plateau flips.
const DDFW_STUCK_INTERVAL: u64 = 1;

/// DDFW weight floor (named per design §2.2): donors NEVER drop below this —
/// the initial constraint weight, so every row always retains at least its
/// original unit penalty and the violated-set steering can never be starved
/// to zero by transfers.
const DDFW_WEIGHT_FLOOR: i128 = 1;

/// DDFW transfer fraction (named per design §2.2): the amount moved from a
/// donor is `spare / DDFW_TRANSFER_DIVISOR` (at least 1) where
/// `spare = donor_weight - DDFW_WEIGHT_FLOOR` — i.e. HALF the spare above the
/// floor at the shipped value, the classic DDFW choice: big enough to tilt
/// the landscape in one stuck event, never enough to breach the floor.
const DDFW_TRANSFER_DIVISOR: i128 = 2;

/// Per-stuck-event neighbor-scan budget for the DDFW donor search (occurrence
/// probes across ALL violated rows). Donor selection is O(neighbors of the
/// violated row) per stuck event — never paid on improving flips — and this
/// cap bounds the worst case (a plateau with a huge violated set, e.g. the
/// early hunt) at a constant well below the default PAWS rescan bump's
/// O(constraints): rows whose scan does not fit the remaining budget fall
/// back to the PAWS additive `+1` (see [`Tracker::ddfw_transfer_weights`]),
/// so escalation never silently stops.
const DDFW_SWEEP_NEIGHBOR_BUDGET: usize = 65_536;

// ---- Smoothed Configuration Checking (design §2.2, A/B-gated diversified arm) ----

/// SCC smoothing cadence (named per design §2.2): every this-many flips, a
/// random small fraction of variables is re-marked configuration-changed (see
/// [`SCC_SMOOTH_FRACTION_DIVISOR`]), so the CC tabu ages out instead of
/// permanently freezing variables whose neighborhood happens to go quiet.
const SCC_SMOOTH_INTERVAL: u64 = 512;

/// SCC smoothing fraction (named per design §2.2): each smoothing event
/// re-enables `max(1, num_vars / SCC_SMOOTH_FRACTION_DIVISOR)` uniformly
/// random variables. Amortized cost per flip is `num_vars /
/// (SCC_SMOOTH_FRACTION_DIVISOR × SCC_SMOOTH_INTERVAL)` — negligible against
/// the O(touched) flip work.
const SCC_SMOOTH_FRACTION_DIVISOR: usize = 64;

/// Feasibility-phase weighting scheme (design §2.2): how constraint penalty
/// weights escalate on plateaus. [`WeightScheme::Paws`] is the measured
/// default; [`WeightScheme::Ddfw`] is the A/B-gated quality increment for
/// DIVERSIFIED workers on the 60-strictly-suboptimal axis — it becomes the
/// default only on a demonstrated net A/B win. Both ride the same O(touched)
/// incremental update loop; the scheme changes only how weight moves at a
/// stuck event, never soundness (weights are advisory search state).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum WeightScheme {
    /// Additive `+1` bump of every violated row (the shipped default; see
    /// [`Tracker::bump_violated_weights`]).
    #[default]
    Paws,
    /// Divide-and-distribute weight TRANSFER: each violated row pulls weight
    /// from its max-weight satisfied neighbor (a row sharing a variable),
    /// conserving total weight within the floor rules (see
    /// [`Tracker::ddfw_transfer_weights`]).
    Ddfw,
}

/// Objective-descent random-walk probability (in 1/1000): occasionally take a
/// feasibility-preserving sideways/uphill objective move to escape a local optimum.
const OBJ_NOISE_PERMILLE: u64 = 50;

/// Layered-restart stagnation dwell threshold (design §3.1): the number of
/// consecutive flips with NO search progress — no new best feasible incumbent and
/// no new minimum violated-count since the last restart — before the next restart
/// layer fires. Large enough that PAWS gets a full plateau-escape budget between
/// restarts; small enough that a genuinely stuck trajectory is re-seeded many
/// times within a competition time slice.
const RESTART_DWELL_THRESHOLD: u64 = 20_000;

/// Instance-size scaling divisor for the restart dwell (A/B-tunable pin): the
/// effective dwell is `RESTART_DWELL_THRESHOLD.max(total_occurrences /
/// RESTART_DWELL_OCC_DIVISOR)`. Belt-and-suspenders on top of the incremental
/// O(diff × occ) reseat ([`reseat_assignment`]): even in the worst reseat case
/// (biased-random scramble with no incumbent, diff ≈ n/2, i.e. ≈
/// total_occurrences/2 tracker work), the per-restart reseat cost stays a
/// bounded fraction (≤ divisor/2 flips' worth) of the inter-restart search
/// work, so restarts can never dominate the flip budget on huge instances.
const RESTART_DWELL_OCC_DIVISOR: u64 = 64;

/// GEOMETRIC dwell growth multiplier (A/B-tunable pin): each fired restart
/// multiplies the scheduler's current dwell by this factor, so restarts fire
/// after ~20k, 80k, 320k, ... progress-free flips. Rationale (diag-set A/B,
/// 30s budget): with a FLAT dwell, once the min-shortfall watermark bottoms
/// out in a plateau a restart fires every ~effective_dwell flips FOR THE REST
/// OF THE RUN, and each scramble destroys a whole-budget anytime grind whose
/// answer only lands in the final flush (j120 RCPSP / benchsMusee
/// _binary/_ladder SAT→UNKNOWN, hw128 o 43→48). Geometric growth keeps the
/// EARLY basin escape (the SMTI-class UNKNOWN→SAT rescue fires at the original
/// dwell) while the late-run scramble frequency decays geometrically.
/// Saturating u64 arithmetic, so no cap is needed.
const RESTART_DWELL_GROWTH: u64 = 4;

/// Biased-random restart layer: probability (in 1/1000) that each variable KEEPS
/// its value from the anchor assignment — the best-so-far feasible assignment
/// when one exists (equivalently: each var is true with probability 0.9 if it
/// is true in the best-so-far, 0.1 otherwise), else the CURRENT assignment
/// (the locality-preserving pre-feasibility kick: a uniform scramble would
/// repeatedly reset a whole-budget feasibility grind to a random point, see
/// [`RESTART_DWELL_GROWTH`]).
const RESTART_BIAS_KEEP_PERMILLE: u64 = 900;

/// Best-incumbent intensification restart layer: number of random kick flips
/// applied ON TOP of the best feasible incumbent, so the search re-explores the
/// incumbent's basin from a nearby (possibly mildly infeasible) point instead of
/// replaying the identical trajectory.
const RESTART_INTENSIFY_KICKS: usize = 3;

/// Default near-feasible **endgame** threshold for the DETERMINISTIC
/// best-compensator swap ([`endgame_compensator_swap`]): the swap is only attempted
/// when the number of currently-violated constraints is `<=` this value (and `0`
/// disables it entirely). On the multi-row equality wall (market-split /
/// Cornuéjols–Dawande systems) a single flip can never reduce total weighted
/// violation — turning one variable on/off trades violation between rows — so
/// single-flip min-conflicts plateaus there. A swap (flip one more variable to
/// *cancel* the residual) is the smallest move that can cross such an equality ridge.
///
/// # Design (Task W4 — replaces the W3 global random swap)
/// The earlier W3 lever fired a *random-sampled* swap on *every* non-improving
/// plateau across the whole feasibility hunt; its per-plateau scan trimmed the flip
/// budget and measured net neutral-to-negative. The W4 redesign is strictly cleaner:
/// a fully DETERMINISTIC best-partner scan (no RNG), confined to the near-feasible
/// endgame (few violated rows, so the scan is cheap), that — on success — is treated
/// as the progress move and SKIPS the PAWS bump to avoid endgame oscillation.
///
/// # Default OFF — honest negative result (Task W4)
/// Controlled A/B on *planted-feasible* market split (see
/// `sls_sweep::market_split_planted_swap_ab`, m=4, n=30, 24 instances, 1 s/inst)
/// found the endgame swap **net neutral-to-negative**: across thresholds 1–3 the
/// pure two-phase feasibility hit-rate *consistently regressed* (baseline 10/24 OFF
/// -> 4–7/24 ON — the deterministic 2-flip pulls the late search out of basins PAWS
/// would have completed), while the shipped best-of-passes modes (`combined`/`both`)
/// moved only within noise (4/24 -> 3–6/24). On the easy single-equality families
/// (subset_sum / cardinality) both arms already hit feasibility, so there is no
/// headroom. It therefore ships DISABLED (`0`) so the default trajectory is
/// byte-identical to the single-flip search (guaranteed 0 regression), while
/// remaining a live, reproducible A/B lever: set
/// `AY_PB_SLS_ENDGAME_THRESHOLD=<1..>` to enable it.
const ENDGAME_VIOLATED_THRESHOLD: usize = 0;

/// Reads the endgame swap threshold from `AY_PB_SLS_ENDGAME_THRESHOLD`, falling back
/// to [`ENDGAME_VIOLATED_THRESHOLD`]. `0` disables the endgame swap entirely
/// (recovering the historical single-flip search), keeping it as a live, reproducible
/// A/B lever. Values are clamped to a sane bound so a typo cannot make the per-plateau
/// scan run over a huge violated set.
fn endgame_threshold() -> usize {
    /// Upper clamp: above this the violated set is no longer an "endgame" and the
    /// deterministic scan would cost too much per plateau.
    const MAX_THRESHOLD: usize = 4096;
    match std::env::var("AY_PB_SLS_ENDGAME_THRESHOLD") {
        Ok(v) => v
            .trim()
            .parse::<usize>()
            .map(|n| n.min(MAX_THRESHOLD))
            .unwrap_or(ENDGAME_VIOLATED_THRESHOLD),
        Err(_) => ENDGAME_VIOLATED_THRESHOLD,
    }
}

/// Whether the NuPBO-class unified loop ([`search_unified`]) is the active
/// from-scratch primal. Default OFF (opt-in): a real-corpus A/B on the PB24
/// OPT-LIN set showed the unified loop net-negative vs the historical two-phase
/// PAWS search — it lost real incumbents (e.g. linpeb `layeredfan_up` r24/r33:
/// `o 12675` / SAT under the legacy path → `UNKNOWN` under the unified loop) with
/// no compensating gain. The legacy [`search_with_options`] is the default;
/// set `AY_PB_SLS_UNIFIED=1` to re-enable the unified loop for measurement.
pub(crate) fn unified_enabled() -> bool {
    match std::env::var_os("AY_PB_SLS_UNIFIED").as_deref() {
        None => false,
        Some(v) => v.to_str().map_or(false, |v| {
            matches!(
                v.trim().to_ascii_lowercase().as_str(),
                "1" | "true" | "yes" | "on"
            )
        }),
    }
}

/// Whether the structure-aware BNN feasibility seed is enabled, per the
/// `AY_PB_BNN_FEAS` environment variable (∈ {`1`, `true`, `yes`, `on`}). Default
/// OFF so the all-false start path is unchanged; gated for clean A/B comparison.
/// The seed is ADVISORY ONLY (a starting point for the same search); soundness
/// does not depend on this flag in any way.
fn bnn_feas_enabled() -> bool {
    std::env::var_os("AY_PB_BNN_FEAS").is_some_and(|v| {
        matches!(
            v.to_str()
                .map(str::trim)
                .map(str::to_ascii_lowercase)
                .as_deref(),
            Some("1" | "true" | "yes" | "on")
        )
    })
}

/// Outcome of an SLS run: the best feasible incumbent found, or `None` if no
/// feasible assignment was reached.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SlsResult {
    pub(crate) assignment: Vec<bool>,
    pub(crate) objective: i128,
}

/// Per-constraint cached state for the incremental tracker, generic over the
/// per-row arithmetic scalar `T` (design §3.1: the **i64 fast path** with an
/// exact per-instance overflow flag — see [`ScoreInt`]). `T = i64` halves the
/// memory traffic of the hot per-flip loops and removes every 128-bit
/// saturating operation from them; `T = i128` is the exact historical wide
/// path. A row is only ever tracked in `i64` when `Σ|coeff| + |rhs|` provably
/// fits (checked at construction), so BOTH widths compute identical values —
/// the dispatch is a pure speed choice, never a trajectory change.
struct ConstraintState<T> {
    /// Current exact left-hand-side value `Σ coeff_i · [literal_i true]`.
    lhs: T,
    rhs: T,
    rel: PbRel,
    /// PAWS-style penalty weight for this constraint (>= 1). Raised on plateaus.
    /// Weight×shortfall products feed the aggregate counters, which stay
    /// `i128` on both paths: for `T = i64` the product is a widening 64→128
    /// multiply (exact, cheap — never saturates); for `T = i128` it is the
    /// historical saturating multiply, bit-for-bit.
    weight: T,
}

impl<T: ScoreInt> ConstraintState<T> {
    /// Non-negative "amount short": how far the LHS is from satisfying the
    /// relation (0 when satisfied). For `Ge`: `max(0, rhs - lhs)`. For `Eq`:
    /// `|lhs - rhs|`. Saturating so it can never panic on pathological coeffs.
    /// The `i128` instantiation runs the LITERAL contract-carrying
    /// [`shortfall_for`]; see [`ScoreInt::shortfall`].
    fn shortfall(&self) -> T {
        T::shortfall(self.rel, self.lhs, self.rhs)
    }
}

/// A single occurrence of a variable in a constraint: when the variable's value
/// changes, this constraint's LHS changes by `delta_if_var_true - delta_if_var_false`.
/// We precompute the signed coefficient contribution so the inner loop is just an
/// add. `contrib` is the amount this term adds to the constraint LHS *when the
/// variable is true* minus *when it is false*. For a positive literal with
/// coefficient `c` that is `+c`; for a negated literal `~v` with coefficient `c`
/// the term contributes `c` when `v` is FALSE, so the delta on `v` going
/// false->true is `-c`.
struct Occurrence<T> {
    constraint: u32,
    /// LHS delta when the variable flips from false to true.
    delta_false_to_true: T,
}

/// Row → member-variables index in CSR form: the inverse of the per-variable
/// occurrence lists. Built ONCE (lazily, only for the DDFW / SCC A/B arms —
/// see [`Tracker::build_row_members`]) so the default trajectory pays neither
/// its memory nor its build time.
///
/// # Memory cost (documented per design §2.2)
/// One `u32` per occurrence (`vars`) plus one `u32` per row + 1 (`offsets`):
/// ≤ ~32 MB at the [`MAX_SLS_OCCURRENCES`] cap, which is the size-decline
/// check that bounds it — the tracker declines larger instances before this
/// index can ever be built.
struct RowMembers {
    /// `offsets[c]..offsets[c + 1]` is row `c`'s slice of `vars`; len = rows + 1.
    offsets: Vec<u32>,
    /// Concatenated member variable indices, row-major, ascending within a row.
    vars: Vec<u32>,
}

impl RowMembers {
    /// The member variables of row `c`.
    #[inline]
    fn row(&self, c: usize) -> &[u32] {
        &self.vars[self.offsets[c] as usize..self.offsets[c + 1] as usize]
    }
}

/// Linear incremental tracker over all hard constraints. Maintains each
/// constraint's exact LHS so that a single variable flip costs `O(occ(v))`.
/// Generic over the per-row scalar `T` (i64 fast path / i128 exact — see
/// [`ConstraintState`]); the search loop is monomorphized per width by
/// [`search_with_seeds`]'s dispatch, so the hot loop pays zero dynamic cost.
struct Tracker<T> {
    states: Vec<ConstraintState<T>>,
    /// For each variable index, the list of (constraint, lhs-delta) occurrences.
    occurrences: Vec<Vec<Occurrence<T>>>,
    /// Total weighted violation (Σ over violated constraints of weight·shortfall).
    /// Maintained incrementally and used to score feasibility-phase moves.
    weighted_violation: i128,
    /// RAW total shortfall (Σ over ALL rows of `shortfall()`, UNWEIGHTED),
    /// maintained incrementally alongside `weighted_violation` (still O(touched)
    /// per flip; reading it is O(1)). Deliberately independent of the PAWS
    /// weights: the weighted total inflates as plateau bumps accrue even while
    /// the underlying system is genuinely converging, so it cannot serve as a
    /// progress signal. This raw total is what the layered-restart scheduler
    /// watches ([`RestartState::note_step`]): on Eq-heavy instances (RCPSP /
    /// pbEq1 shapes) the violated-row COUNT plateaus while the raw shortfall
    /// still improves steadily, and firing a restart mid-grind destroys a
    /// converging trajectory.
    total_shortfall: i128,
    /// The set of currently-violated constraint indices, maintained incrementally
    /// with O(1) swap-remove so the feasibility phase can pick a violated
    /// constraint without an O(num_constraints) rescan every flip.
    violated_list: Vec<usize>,
    /// Position of constraint `c` in `violated_list`, or `usize::MAX` if `c` is not
    /// currently violated. Kept in sync with `violated_list`.
    violated_pos: Vec<usize>,
    /// When true, [`Tracker::bump_violated_weights`] updates only the violated
    /// constraints' weights (O(violated)) instead of doing a full
    /// `recompute_violation()` rescan (O(constraints)). Both compute identical
    /// weights; the fast path also leaves `violated_list` un-reordered, which is a
    /// *different but equally valid* search trajectory. Exposed as a per-run option
    /// so the portfolio can run both trajectories in parallel and keep the best.
    fast_bump: bool,
    /// Row → member-variables CSR, `Some` only for the DDFW / SCC A/B arms
    /// ([`Tracker::build_row_members`]). `None` on the default path: zero
    /// memory, zero build time, bit-identical trajectory.
    row_members: Option<RowMembers>,
    /// Smoothed Configuration Checking bits (design §2.2), `Some` only when the
    /// SCC arm is on ([`Tracker::enable_scc`]): `scc_bits[v]` is true iff a
    /// NEIGHBORING variable (sharing a constraint) flipped since `v` last
    /// flipped — `v` is then "configuration-changed" and eligible for the
    /// feasibility-phase greedy pick. Maintained in O(touched) by
    /// [`Tracker::apply_flip`]; smoothed on a cadence by [`Tracker::scc_smooth`].
    scc_bits: Option<Vec<bool>>,
}

impl<T: ScoreInt> Tracker<T> {
    /// Builds the tracker for a linear instance under the given assignment.
    /// Returns `None` if the instance is non-linear, too large, a coefficient
    /// computation overflows, or — fail-closed, narrow scalars only — any row
    /// fails the exact `Σ|coeff| + |rhs|` bound ([`ScoreInt::row_fits`]) or
    /// any narrowing fails. The dispatch in [`search_with_seeds`] uses the
    /// SAME per-row predicate, so a dispatch bug can only decline, never wrap.
    fn new(
        instance: &PbInstance,
        num_vars: usize,
        assignment: &[bool],
        fast_bump: bool,
    ) -> Option<Self> {
        let mut occurrences: Vec<Vec<Occurrence<T>>> = Vec::new();
        occurrences.resize_with(num_vars, Vec::new);
        let mut states = Vec::with_capacity(instance.constraints.len());
        let mut total_occ = 0usize;

        for (ci, constraint) in instance.constraints.iter().enumerate() {
            let constraint_index = u32::try_from(ci).ok()?;
            let mut lhs: i128 = 0;
            let mut coeff_abs_sum: i128 = 0;
            for term in &constraint.terms {
                // Linear only: a non-linear (product) term makes the per-variable
                // LHS delta non-constant, which the incremental tracker cannot
                // model. Decline rather than track it incorrectly.
                let [lit] = term.lits.as_slice() else {
                    return None;
                };
                let var_index = (lit.var as usize).checked_sub(1)?;
                if var_index >= num_vars {
                    return None;
                }
                let value = assignment.get(var_index).copied().unwrap_or(false);
                let literal_true = if lit.negated { !value } else { value };
                if literal_true {
                    lhs = lhs.checked_add(term.coeff)?;
                }
                // LHS delta when `var` goes false -> true. Positive literal: the
                // literal tracks `var`, so the term turns on (adds coeff) -> +coeff.
                // Negated literal: the literal tracks `!var`, so the term turns OFF
                // -> -coeff.
                let delta_false_to_true = if lit.negated {
                    term.coeff.checked_neg()?
                } else {
                    term.coeff
                };
                coeff_abs_sum = coeff_abs_sum.saturating_add(term.coeff.saturating_abs());
                total_occ = total_occ.checked_add(1)?;
                if total_occ > MAX_SLS_OCCURRENCES {
                    return None;
                }
                occurrences[var_index].push(Occurrence {
                    constraint: constraint_index,
                    // Fail-closed narrowing: a delta the scalar cannot
                    // represent declines this tracker (never wraps).
                    delta_false_to_true: T::from_i128(delta_false_to_true)?,
                });
            }
            // The per-instance exact overflow flag, re-checked per row here
            // (i128: always true — the wide path keeps its historical
            // saturating semantics bit-for-bit).
            if !T::row_fits(coeff_abs_sum, constraint.rhs) {
                return None;
            }
            states.push(ConstraintState {
                lhs: T::from_i128(lhs)?,
                rhs: T::from_i128(constraint.rhs)?,
                rel: constraint.rel,
                weight: T::ONE,
            });
        }

        let constraint_count = states.len();
        let mut tracker = Tracker {
            states,
            occurrences,
            weighted_violation: 0,
            total_shortfall: 0,
            violated_list: Vec::new(),
            violated_pos: vec![usize::MAX; constraint_count],
            fast_bump,
            row_members: None,
            scc_bits: None,
        };
        tracker.recompute_violation();
        Some(tracker)
    }

    /// Builds the row → member-variables CSR ([`RowMembers`]) by inverting the
    /// per-variable occurrence lists. Idempotent; called ONLY for the DDFW /
    /// SCC A/B arms, so the default path never pays for it. O(total
    /// occurrences) time and one `u32` per occurrence (+ one per row) memory —
    /// bounded by the [`MAX_SLS_OCCURRENCES`] size-decline check in
    /// [`Tracker::new`].
    fn build_row_members(&mut self) {
        if self.row_members.is_some() {
            return;
        }
        let rows = self.states.len();
        let mut offsets = vec![0u32; rows + 1];
        for occ_list in &self.occurrences {
            for occ in occ_list {
                offsets[occ.constraint as usize + 1] += 1;
            }
        }
        for c in 0..rows {
            offsets[c + 1] += offsets[c];
        }
        let mut vars = vec![0u32; offsets[rows] as usize];
        let mut cursor: Vec<u32> = offsets[..rows].to_vec();
        for (v, occ_list) in self.occurrences.iter().enumerate() {
            for occ in occ_list {
                let c = occ.constraint as usize;
                vars[cursor[c] as usize] = v as u32;
                cursor[c] += 1;
            }
        }
        self.row_members = Some(RowMembers { offsets, vars });
    }

    /// Turns on Smoothed Configuration Checking (design §2.2): every variable
    /// starts configuration-changed (the standard CC initialization — nothing
    /// is tabu before the first flip). Requires [`Tracker::build_row_members`]
    /// to have run (the caller enables both together).
    fn enable_scc(&mut self) {
        debug_assert!(
            self.row_members.is_some(),
            "SCC needs the row-members index for O(touched) neighbor marking"
        );
        if self.scc_bits.is_none() {
            self.scc_bits = Some(vec![true; self.occurrences.len()]);
        }
    }

    /// Whether `var` is eligible for the feasibility-phase GREEDY pick under
    /// SCC: configuration-changed (a neighbor flipped since `var` last did),
    /// or SCC is off entirely (every variable eligible — the default path).
    #[inline]
    fn scc_eligible(&self, var: usize) -> bool {
        self.scc_bits.as_ref().is_none_or(|bits| bits[var])
    }

    /// SCC maintenance for a flip of `var` (O(touched), design §2.2): every
    /// member of every row containing `var` becomes configuration-changed (a
    /// neighbor of theirs — `var` — just flipped), and `var` itself becomes
    /// configuration-UNCHANGED (nothing in its neighborhood has moved since it
    /// last flipped). No-op unless SCC is on.
    fn scc_mark_flip(&mut self, var: usize) {
        let Tracker {
            occurrences,
            row_members,
            scc_bits,
            ..
        } = self;
        let (Some(members), Some(bits)) = (row_members.as_ref(), scc_bits.as_mut()) else {
            return;
        };
        for occ in &occurrences[var] {
            for &u in members.row(occ.constraint as usize) {
                bits[u as usize] = true;
            }
        }
        bits[var] = false;
    }

    /// SCC smoothing (design §2.2, [`SCC_SMOOTH_INTERVAL`] cadence): re-enables
    /// `max(1, num_vars / SCC_SMOOTH_FRACTION_DIVISOR)` uniformly random
    /// variables so the configuration tabu ages out. Draws from the caller's
    /// structurally-seeded PRNG only — deterministic per seed. No-op unless
    /// SCC is on.
    fn scc_smooth(&mut self, rng: &mut SplitMix64) {
        let num_vars = self.occurrences.len();
        let Some(bits) = self.scc_bits.as_mut() else {
            return;
        };
        if num_vars == 0 {
            return;
        }
        let k = (num_vars / SCC_SMOOTH_FRACTION_DIVISOR).max(1);
        for _ in 0..k {
            bits[rng.below(num_vars)] = true;
        }
    }

    /// Number of currently-violated constraints (the feasibility target is 0).
    fn num_violated(&self) -> usize {
        self.violated_list.len()
    }

    /// Marks constraint `c` as violated (idempotent: no-op if already tracked).
    fn mark_violated(&mut self, c: usize) {
        if self.violated_pos[c] == usize::MAX {
            self.violated_pos[c] = self.violated_list.len();
            self.violated_list.push(c);
        }
    }

    /// Marks constraint `c` as satisfied, removing it from the violated set with an
    /// O(1) swap-remove (idempotent: no-op if not tracked).
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

    /// Recomputes `weighted_violation`, the RAW `total_shortfall`, and the
    /// violated-set from scratch.
    fn recompute_violation(&mut self) {
        let mut total: i128 = 0;
        let mut raw: i128 = 0;
        self.violated_list.clear();
        for pos in self.violated_pos.iter_mut() {
            *pos = usize::MAX;
        }
        for ci in 0..self.states.len() {
            let state = &self.states[ci];
            let short = state.shortfall();
            if short > T::ZERO {
                total =
                    total.saturating_add(state.weight.to_i128().saturating_mul(short.to_i128()));
                raw = raw.saturating_add(short.to_i128());
                self.violated_pos[ci] = self.violated_list.len();
                self.violated_list.push(ci);
            }
        }
        self.weighted_violation = total;
        self.total_shortfall = raw;
    }

    /// Applies a flip of `var` (0-indexed) in `assignment`, updating every touched
    /// constraint's LHS and the aggregate violation counters. `assignment[var]`
    /// must already reflect the NEW value (the caller flips it first).
    fn apply_flip(&mut self, var: usize, new_value: bool) {
        // new_value is the value AFTER the flip. If it is now true, the variable
        // went false->true, so add `delta_false_to_true`; if now false, subtract.
        // Iterate by index so we can mutate `states` / the violated-set without
        // holding an immutable borrow of `self.occurrences[var]`.
        let occ_len = self.occurrences[var].len();
        for i in 0..occ_len {
            let occurrence = &self.occurrences[var][i];
            let c = occurrence.constraint as usize;
            let delta = if new_value {
                occurrence.delta_false_to_true
            } else {
                occurrence.delta_false_to_true.saturating_neg()
            };
            let state = &mut self.states[c];
            let before_short = state.shortfall();
            let before_weighted = if before_short > T::ZERO {
                state
                    .weight
                    .to_i128()
                    .saturating_mul(before_short.to_i128())
            } else {
                0
            };
            state.lhs = state.lhs.saturating_add(delta);
            let after_short = state.shortfall();
            let after_weighted = if after_short > T::ZERO {
                state.weight.to_i128().saturating_mul(after_short.to_i128())
            } else {
                0
            };
            if before_short == T::ZERO && after_short > T::ZERO {
                self.mark_violated(c);
            } else if before_short > T::ZERO && after_short == T::ZERO {
                self.mark_satisfied(c);
            }
            self.weighted_violation = self
                .weighted_violation
                .saturating_sub(before_weighted)
                .saturating_add(after_weighted);
            self.total_shortfall = self
                .total_shortfall
                .saturating_sub(before_short.to_i128())
                .saturating_add(after_short.to_i128());
        }
        // SCC maintenance (no-op unless the SCC arm is on): O(touched), where
        // touched = the rows `var` occurs in and their members — the same
        // neighborhood the design's shared update loop already walks.
        if self.scc_bits.is_some() {
            self.scc_mark_flip(var);
        }
    }

    /// The weighted-violation delta that flipping `var` would produce, WITHOUT
    /// mutating any state. Lower (more negative) is better in the feasibility
    /// phase. Returns the delta in `weighted_violation`.
    fn flip_violation_delta(&self, var: usize, current_value: bool) -> i128 {
        let occ = &self.occurrences[var];
        let mut delta: i128 = 0;
        for occurrence in occ {
            let state = &self.states[occurrence.constraint as usize];
            let before_short = state.shortfall();
            let before_weighted = if before_short > T::ZERO {
                state
                    .weight
                    .to_i128()
                    .saturating_mul(before_short.to_i128())
            } else {
                0
            };
            let signed = if current_value {
                occurrence.delta_false_to_true.saturating_neg()
            } else {
                occurrence.delta_false_to_true
            };
            let new_lhs = state.lhs.saturating_add(signed);
            let after_short = T::shortfall(state.rel, new_lhs, state.rhs);
            let after_weighted = if after_short > T::ZERO {
                state.weight.to_i128().saturating_mul(after_short.to_i128())
            } else {
                0
            };
            delta = delta
                .saturating_sub(before_weighted)
                .saturating_add(after_weighted);
        }
        delta
    }

    /// Whether flipping `var` would keep EVERY constraint satisfied (used in the
    /// objective-descent phase, where we never leave the feasible region). Assumes
    /// the current assignment is feasible.
    fn flip_preserves_feasibility(&self, var: usize, current_value: bool) -> bool {
        let occ = &self.occurrences[var];
        for occurrence in occ {
            let state = &self.states[occurrence.constraint as usize];
            let signed = if current_value {
                occurrence.delta_false_to_true.saturating_neg()
            } else {
                occurrence.delta_false_to_true
            };
            let new_lhs = state.lhs.saturating_add(signed);
            if T::shortfall(state.rel, new_lhs, state.rhs) > T::ZERO {
                return false;
            }
        }
        true
    }

    /// Raises the penalty weight of every currently-violated constraint by 1
    /// (PAWS additive bump) and recomputes the aggregate violation so subsequent
    /// flip scores reflect the new weights. Called on plateaus to escape them.
    fn bump_violated_weights(&mut self) {
        if self.fast_bump {
            // Fast path: a weight bump cannot change which constraints are
            // violated (each shortfall is unchanged), so the violated-set is left
            // intact and only the violated constraints' weights are touched —
            // O(violated), not O(constraints). The aggregate `weighted_violation`
            // is updated incrementally (each +1 weight adds that constraint's
            // shortfall). Equivalent weights to the rescan path, far cheaper when
            // `violated << constraints` (the late feasibility hunt and the
            // perturb/re-feasibilize cycles during objective descent).
            let mut added: i128 = 0;
            for i in 0..self.violated_list.len() {
                let c = self.violated_list[i];
                let short = self.states[c].shortfall(); // > 0 by invariant
                self.states[c].weight = self.states[c].weight.saturating_add(T::ONE);
                added = added.saturating_add(short.to_i128());
            }
            self.weighted_violation = self.weighted_violation.saturating_add(added);
            return;
        }
        for state in &mut self.states {
            if state.shortfall() > T::ZERO {
                state.weight = state.weight.saturating_add(T::ONE);
            }
        }
        self.recompute_violation();
    }

    /// DDFW weight-TRANSFER stuck-event sweep (design §2.2, the
    /// [`WeightScheme::Ddfw`] arm): each currently-violated row pulls weight
    /// IN from the max-weight SATISFIED neighbor (a row sharing a variable,
    /// found via the row-members CSR + occurrence index; ties broken by the
    /// smallest row index for bit-for-bit determinism). The amount moved is
    /// `spare / DDFW_TRANSFER_DIVISOR` (at least 1) of the donor's spare above
    /// [`DDFW_WEIGHT_FLOOR`], so donors NEVER drop below the initial weight.
    /// Rows with no eligible donor — every neighbor violated or already at the
    /// floor, or the [`DDFW_SWEEP_NEIGHBOR_BUDGET`] scan budget exhausted —
    /// fall back to the PAWS additive `+1` so plateau escalation never stalls.
    ///
    /// Total weight is therefore CONSERVED except for those explicit additive
    /// fallbacks: `Σ weight (after) = Σ weight (before) + returned count`.
    /// The return value is the number of fallback bumps (load-bearing for the
    /// conservation invariant test; callers in the search loop ignore it).
    ///
    /// Cost: O(violated) plus at most [`DDFW_SWEEP_NEIGHBOR_BUDGET`] occurrence
    /// probes per stuck event — never paid on improving flips, and bounded
    /// below the default PAWS rescan bump's O(constraints) on large instances.
    /// Draws no RNG; `weighted_violation` is maintained incrementally (donors
    /// are satisfied, so only the receiving violated rows' contributions move).
    fn ddfw_transfer_weights(&mut self) -> usize {
        let Some(members) = self.row_members.as_ref() else {
            // Defensive: the search loop always builds the CSR for the DDFW
            // arm. Without it there is no neighbor index; keep escalating via
            // the additive bump (equivalent fallback for EVERY violated row).
            let fallbacks = self.violated_list.len();
            self.bump_violated_weights();
            return fallbacks;
        };
        // The generic arithmetic below implements the pinned constants via
        // `div2` / `T::ONE`; this compile-time assert welds them together.
        const {
            assert!(DDFW_TRANSFER_DIVISOR == 2 && DDFW_WEIGHT_FLOOR == 1);
        }
        let mut budget = DDFW_SWEEP_NEIGHBOR_BUDGET;
        let mut fallbacks = 0usize;
        let mut added: i128 = 0; // delta to `weighted_violation`
        for i in 0..self.violated_list.len() {
            let c = self.violated_list[i];
            // Donor scan: max-weight satisfied neighbor with spare above the
            // floor. Scan order (row members ascending, occurrence lists in
            // build order) does not affect the result — max weight wins, ties
            // to the smallest row index — so the pick is order-independent.
            let mut donor: Option<usize> = None;
            'scan: for &v in members.row(c) {
                for occ in &self.occurrences[v as usize] {
                    if budget == 0 {
                        break 'scan;
                    }
                    budget -= 1;
                    let d = occ.constraint as usize;
                    if d == c {
                        continue;
                    }
                    let state = &self.states[d];
                    if state.shortfall() > T::ZERO || state.weight.to_i128() <= DDFW_WEIGHT_FLOOR {
                        continue; // donors must be satisfied and have spare
                    }
                    let better = match donor {
                        None => true,
                        Some(best) => {
                            let bw = self.states[best].weight;
                            state.weight > bw || (state.weight == bw && d < best)
                        }
                    };
                    if better {
                        donor = Some(d);
                    }
                }
            }
            let short = self.states[c].shortfall(); // > 0 by invariant
            match donor {
                Some(d) => {
                    // spare = weight - DDFW_WEIGHT_FLOOR (the floor is T::ONE);
                    // transfer = (spare / DDFW_TRANSFER_DIVISOR).max(1), i.e.
                    // half the spare — identical values on both widths.
                    let spare = self.states[d].weight.saturating_sub(T::ONE); // >= 1
                    let transfer = spare.div2().max(T::ONE);
                    self.states[d].weight = self.states[d].weight.saturating_sub(transfer); // stays >= the floor
                    self.states[c].weight = self.states[c].weight.saturating_add(transfer);
                    added =
                        added.saturating_add(transfer.to_i128().saturating_mul(short.to_i128()));
                }
                None => {
                    self.states[c].weight = self.states[c].weight.saturating_add(T::ONE);
                    added = added.saturating_add(short.to_i128());
                    fallbacks += 1;
                }
            }
        }
        self.weighted_violation = self.weighted_violation.saturating_add(added);
        fallbacks
    }

    /// Total number of variable occurrences the tracker indexes (Σ constraint
    /// sizes). Used to scale the restart dwell so the per-restart reseat cost
    /// stays a bounded fraction of the inter-restart flip work.
    fn total_occurrences(&self) -> u64 {
        self.occurrences.iter().map(|occ| occ.len() as u64).sum()
    }
}

/// Incrementally re-seats the search on `target` (a layered restart): flips only
/// the variables where `target` differs from the current `assignment`, applying
/// each one through [`Tracker::apply_flip`] so every touched constraint's LHS,
/// the violated set, and the weighted violation stay incrementally maintained.
/// O(diff × occ) and allocation-free — the design budget (§4) — instead of the
/// historical from-scratch full LHS rescan plus violated-set rebuild
/// (O(total terms + constraints)) on EVERY fired restart.
///
/// The PAWS penalty weights are deliberately PRESERVED — the standard PAWS
/// choice: the learned which-rows-are-hard profile is instance-level knowledge,
/// not trajectory-level, so it carries across restart layers; only the
/// assignment-dependent state is re-seated.
///
/// The resulting tracker state is EXACT (equal to a from-scratch rebuild on
/// `target`; see `incremental_reseat_matches_fresh_tracker_oracle`), but the
/// `violated_list` ORDER can differ from a from-scratch rebuild's — a different
/// but equally valid search trajectory. The tracker is advisory either way:
/// every reported incumbent is independently re-verified.
fn reseat_assignment<T: ScoreInt>(
    assignment: &mut [bool],
    target: &[bool],
    tracker: &mut Tracker<T>,
) {
    debug_assert_eq!(assignment.len(), target.len());
    for var in 0..assignment.len().min(target.len()) {
        if assignment[var] != target[var] {
            assignment[var] = target[var];
            tracker.apply_flip(var, target[var]);
        }
    }
}

/// Fires one layered restart (the search loop calls this exactly when
/// [`RestartState::should_fire`] is true):
///
/// 1. If the very flip that crossed the dwell threshold landed on a FEASIBLE
///    point, record it FIRST — otherwise a feasible improvement produced by
///    that flip would be silently lost, because the feasible-branch record in
///    the search loop only runs on the NEXT iteration, after the reseat below
///    has already overwritten the assignment. The call is identical to the
///    loop's other record sites and draws no RNG, so per-seed determinism is
///    preserved (see `restart_records_threshold_crossing_feasible_improvement`).
/// 2. Consume the stagnation event and build the next layer's target in the
///    caller-hoisted `scratch` buffer (no allocation).
/// 3. Incrementally re-seat the search on the target ([`reseat_assignment`]:
///    O(diff × occ), PAWS weights persist).
#[allow(clippy::too_many_arguments)]
fn fire_restart<T: ScoreInt>(
    instance: &PbInstance,
    objective: &PbObjective,
    restart: &mut RestartState<'_>,
    assignment: &mut [bool],
    scratch: &mut [bool],
    tracker: &mut Tracker<T>,
    best: &mut Option<SlsResult>,
    rng: &mut SplitMix64,
    on_improve: &mut dyn FnMut(i128, &[bool]),
    stop: &dyn Fn() -> bool,
) {
    if tracker.num_violated() == 0 {
        try_record_incumbent(instance, objective, assignment, best, on_improve, stop);
    }
    let layer = restart.begin_restart();
    restart.fill_restart_target(
        layer,
        scratch,
        assignment,
        best.as_ref().map(|b| b.assignment.as_slice()),
        rng,
    );
    reseat_assignment(assignment, scratch, tracker);
}

/// A layered-restart layer (design §3.1). Cycled in order on successive
/// stagnation events: biased-random → best-incumbent → external-seed (the last
/// only when the caller provided seed points) → repeat.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RestartLayer {
    /// Each variable keeps its ANCHOR value with probability
    /// [`RESTART_BIAS_KEEP_PERMILLE`]/1000; the anchor is the best-so-far
    /// feasible assignment when one exists, else the CURRENT assignment (the
    /// locality-preserving pre-feasibility kick — never a uniform scramble).
    BiasedRandom,
    /// Restart AT the best feasible incumbent plus [`RESTART_INTENSIFY_KICKS`]
    /// random kick flips (intensification). Falls back to the biased
    /// current-anchored kick when no incumbent exists yet.
    BestIncumbent,
    /// Restart at the next externally-provided candidate assignment (e.g. a
    /// future LP-rounded point — design §3.1's third layer). Falls back to
    /// biased-random when no valid seed is available.
    ExternalSeed,
}

/// Stagnation-triggered layered-restart scheduler (design §3.1).
///
/// Progress = a new best feasible incumbent, a new MINIMUM violated-count, or
/// a new MINIMUM raw total shortfall since the last restart (see
/// [`RestartState::note_step`] for why the shortfall signal is load-bearing on
/// Eq-heavy instances). `dwell` consecutive progress-free flips (at least
/// [`RESTART_DWELL_THRESHOLD`], scaled up on very large instances via
/// [`RESTART_DWELL_OCC_DIVISOR`], and GROWING by [`RESTART_DWELL_GROWTH`] per
/// fired restart) fire the next layer in the cycle. All randomness comes from
/// the caller's structurally-seeded PRNG, so trajectories stay deterministic
/// per seed. PAWS weights are NOT reset on restart (see [`reseat_assignment`]).
struct RestartState<'a> {
    /// Flips since the last progress event.
    stagnant: u64,
    /// Minimum violated-count observed since the last restart.
    min_violated: usize,
    /// Minimum RAW total shortfall ([`Tracker::total_shortfall`]) observed
    /// since the last restart.
    min_shortfall: i128,
    /// Cursor into the layer cycle (advances once per fired restart).
    layer_cursor: usize,
    /// Externally-provided candidate seed assignments; may be empty.
    seeds: &'a [Vec<bool>],
    /// Cursor into `seeds` (advances once per ExternalSeed restart).
    seed_cursor: usize,
    /// CURRENT stagnation dwell threshold: starts at the caller's effective
    /// dwell and is multiplied by [`RESTART_DWELL_GROWTH`] on each fired
    /// restart (geometric back-off; saturating).
    dwell: u64,
}

impl<'a> RestartState<'a> {
    fn new(seeds: &'a [Vec<bool>], dwell: u64) -> Self {
        RestartState {
            stagnant: 0,
            min_violated: usize::MAX,
            min_shortfall: i128::MAX,
            layer_cursor: 0,
            seeds,
            seed_cursor: 0,
            dwell,
        }
    }

    /// Records one search step: progress resets the dwell counter; anything
    /// else accrues stagnation. Progress is any of THREE signals since the
    /// last restart:
    /// 1. a strictly better feasible incumbent,
    /// 2. a new minimum violated-count (feasibility-hunt progress),
    /// 3. a new minimum RAW total shortfall.
    ///
    /// Signal 3 exists because on Eq-heavy instances (RCPSP / pbEq1 shapes)
    /// the violated-row COUNT plateaus while the total shortfall still shrinks
    /// steadily — a genuinely converging grind that a restart scramble would
    /// destroy (measured: j120opt SAT→UNKNOWN, hw128 o 43→48 without this
    /// signal). A genuinely flatlined hunt makes no new shortfall minimum
    /// either, so the dwell still fires there (the SMTI-class rescue is kept).
    /// The shortfall is the RAW unweighted total, immune to PAWS weight drift.
    fn note_step(&mut self, num_violated: usize, total_shortfall: i128, best_improved: bool) {
        if best_improved || num_violated < self.min_violated || total_shortfall < self.min_shortfall
        {
            self.min_violated = self.min_violated.min(num_violated);
            self.min_shortfall = self.min_shortfall.min(total_shortfall);
            self.stagnant = 0;
        } else {
            self.stagnant = self.stagnant.saturating_add(1);
        }
    }

    /// Whether the stagnation dwell threshold has been reached.
    fn should_fire(&self) -> bool {
        self.stagnant >= self.dwell
    }

    /// Consumes the pending stagnation event: resets the dwell bookkeeping,
    /// GROWS the dwell geometrically ([`RESTART_DWELL_GROWTH`] — each
    /// successive restart needs proportionally more stagnation, so late-run
    /// scrambles decay), and returns the next layer in the cycle (ExternalSeed
    /// participates only when seed points were provided).
    fn begin_restart(&mut self) -> RestartLayer {
        self.stagnant = 0;
        self.min_violated = usize::MAX;
        self.min_shortfall = i128::MAX;
        self.dwell = self.dwell.saturating_mul(RESTART_DWELL_GROWTH);
        let cycle_len = if self.seeds.is_empty() { 2 } else { 3 };
        let layer = match self.layer_cursor % cycle_len {
            0 => RestartLayer::BiasedRandom,
            1 => RestartLayer::BestIncumbent,
            _ => RestartLayer::ExternalSeed,
        };
        self.layer_cursor = self.layer_cursor.wrapping_add(1);
        layer
    }

    /// Fills `target` IN PLACE with the restart target assignment for `layer`
    /// (see [`RestartLayer`]). Deterministic given the PRNG state; one RNG
    /// draw per variable on the biased paths, in variable order. `current` is
    /// the search's assignment at the moment the restart fires: every biased
    /// fallback anchors on `best.unwrap_or(current)`, so before the first
    /// feasible incumbent the kick stays LOCAL to the current point (a uniform
    /// scramble would repeatedly reset a whole-budget feasibility grind — the
    /// j120/hw128 loss mode; see [`RESTART_DWELL_GROWTH`]). No allocation: the
    /// caller hoists one reusable scratch buffer for the whole run.
    fn fill_restart_target(
        &mut self,
        layer: RestartLayer,
        target: &mut [bool],
        current: &[bool],
        best: Option<&[bool]>,
        rng: &mut SplitMix64,
    ) {
        let num_vars = target.len();
        let anchor = best.unwrap_or(current);
        match layer {
            RestartLayer::BiasedRandom => fill_biased_random(target, anchor, rng),
            RestartLayer::BestIncumbent => match best {
                Some(b) => {
                    target.copy_from_slice(b);
                    // Small perturbation so the intensified run does not replay
                    // the identical trajectory out of the incumbent.
                    for _ in 0..RESTART_INTENSIFY_KICKS.min(num_vars) {
                        let v = rng.below(num_vars);
                        target[v] = !target[v];
                    }
                }
                None => fill_biased_random(target, anchor, rng),
            },
            RestartLayer::ExternalSeed => {
                // Cycle to the next VALID (correct-length) external seed;
                // wrong-length candidates are skipped, never truncated/padded.
                for _ in 0..self.seeds.len() {
                    let candidate = &self.seeds[self.seed_cursor % self.seeds.len()];
                    self.seed_cursor = self.seed_cursor.wrapping_add(1);
                    if candidate.len() == num_vars {
                        target.copy_from_slice(candidate);
                        return;
                    }
                }
                fill_biased_random(target, anchor, rng);
            }
        }
    }
}

/// Fills `target` with a biased-random restart assignment around `anchor`:
/// each variable keeps its anchor value with probability
/// [`RESTART_BIAS_KEEP_PERMILLE`]/1000 and is flipped otherwise. The anchor is
/// the best-so-far feasible assignment when one exists, else the CURRENT
/// assignment (locality-preserving pre-feasibility kick — never a uniform
/// scramble). One RNG draw per variable, in variable order, regardless of
/// anchor choice, so per-seed determinism holds.
fn fill_biased_random(target: &mut [bool], anchor: &[bool], rng: &mut SplitMix64) {
    for (v, slot) in target.iter_mut().enumerate() {
        let keep = (rng.below(1000) as u64) < RESTART_BIAS_KEEP_PERMILLE;
        *slot = if keep { anchor[v] } else { !anchor[v] };
    }
}

/// Shortfall for a relation given an LHS and RHS (free function so it can be used
/// in the lookahead `flip_*` methods without borrowing a `ConstraintState`).
///
/// `pub` (widened from private) only so the sibling proof crate `ay-pb-verified`
/// can re-import the LITERAL function — via the `#[doc(hidden)]`
/// `optimize::verified_shortfall_for` re-export — for a runtime smoke test that
/// echoes the proven postcondition. The enclosing `sls` module is `pub(crate)`,
/// so the only external reach is the explicit doc-hidden re-export; widening
/// visibility is zero-cost and changes no behavior, so the competition binary is
/// byte-identical.
///
/// # Machine-checked contract (load-bearing SLS invariant)
///
/// The ``
/// below states the invariant the whole SLS scoring layer relies on:
///
/// > **The shortfall of any constraint under any `(lhs, rhs)` is non-negative.**
///
/// `shortfall() > 0` is the "constraint is violated" predicate and the feasibility
/// objective is `Σ weight · shortfall`; a negative shortfall would corrupt the
/// violated-set bookkeeping and move scoring. `offline deductive checker check` discharges
/// `ret >= 0` for ALL `i128` inputs (including the `i128::MIN` `abs` overflow
/// corner) directly against THIS function — the literal solver code — by reading
/// the source via `syn`. The proof is therefore welded to the code the solver
/// actually runs, with no verbatim twin.
///
/// The `deductive_checks` cfg is NEVER set in the normal / competition build, so the
/// `cfg_attr` expands to nothing: no `deductive_checks` dependency is pulled, no runtime
/// assertion is emitted, and the binary is byte-identical. The verifier still
/// sees the contract because it unwraps `cfg_attr`-gated deductive_checks attributes when
/// scanning source (see `cargo-deductive-checks/src/scan.rs` /
/// `deductive-checks-core/src/tracked_syntax.rs`).
pub fn shortfall_for(rel: PbRel, lhs: i128, rhs: i128) -> i128 {
    match rel {
        PbRel::Ge => (rhs.saturating_sub(lhs)).max(0),
        PbRel::Eq => lhs.saturating_sub(rhs).saturating_abs(),
    }
}

/// Per-variable objective contribution: the change in the objective when the
/// variable flips from false to true. Only objective variables have a nonzero
/// entry. For a positive literal with coefficient `c` that is `+c`; for a negated
/// literal `~v` it is `-c`.
fn objective_deltas(objective: &PbObjective, num_vars: usize) -> Option<Vec<i128>> {
    let mut deltas = vec![0i128; num_vars];
    for term in &objective.terms {
        // Objective terms in the linear track are single-literal.
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
        deltas[var_index] = deltas[var_index].checked_add(contribution)?;
    }
    Some(deltas)
}

/// Runs SLS to find a feasible incumbent (and improve it) for `instance` /
/// `objective`, starting from scratch. Reports every adopted, re-verified
/// improvement through `on_improve` and returns the best feasible incumbent found,
/// or `None` if no feasible assignment was reached. See the module docs for the
/// soundness argument.
///
/// `should_stop` is polled periodically; SLS stops promptly on `true`, on
/// `deadline` expiry, or after [`MAX_FLIPS`] flips.
///
/// Test-only baseline wrapper: production callers go through
/// [`search_with_options`] / [`search_with_seeds`] directly.
#[cfg(test)]
pub(crate) fn search(
    instance: &PbInstance,
    objective: &PbObjective,
    deadline: Option<std::time::Instant>,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
) -> Option<SlsResult> {
    search_with_options(
        instance,
        objective,
        deadline,
        should_stop,
        on_improve,
        false,
    )
}

/// As `search`, but with `fast_bump` selecting the O(violated) PAWS bump (see
/// [`Tracker::bump_violated_weights`]). `search` keeps the historical O(constraints)
/// rescan bump (`fast_bump = false`); the two are independent valid trajectories,
/// so the portfolio runs one of each and keeps the best incumbent — a strict
/// improvement over either alone.
pub(crate) fn search_with_options(
    instance: &PbInstance,
    objective: &PbObjective,
    deadline: Option<std::time::Instant>,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
    fast_bump: bool,
) -> Option<SlsResult> {
    search_with_limits(
        instance,
        objective,
        deadline,
        should_stop,
        on_improve,
        fast_bump,
        MAX_SLS_VARS,
    )
}

/// As [`search_with_options`], but with an explicit per-run variable cap.
///
/// The default callers use [`MAX_SLS_VARS`]; the WBO-reduction primal path
/// ([`crate::portfolio::solve_wbo_reduced_sls`]) passes a higher cap because the
/// WBO-to-PBO relaxation inflates the variable count by one auxiliary relaxation
/// variable per paid soft constraint. Those relaxation variables are cheap to
/// track (a single occurrence each) and their value is effectively determined by
/// the original variables, so the per-flip bookkeeping stays tractable well above
/// the conservative default. SOUNDNESS is unaffected: the cap only gates whether
/// the (advisory) search runs at all; every reported incumbent is still
/// re-verified by `try_record_incumbent` here and by
/// `sanitize_optimization_incumbent` in the caller.
pub(crate) fn search_with_limits(
    instance: &PbInstance,
    objective: &PbObjective,
    deadline: Option<std::time::Instant>,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
    fast_bump: bool,
    max_vars: usize,
) -> Option<SlsResult> {
    search_with_seeds(
        instance,
        objective,
        deadline,
        should_stop,
        on_improve,
        &SlsOptions {
            fast_bump,
            max_vars,
            ..SlsOptions::default()
        },
    )
}

/// Additive per-run options for [`search_with_seeds`]. `Default` reproduces the
/// exact behavior of `search` (`fast_bump = false`, default caps, no external
/// seeds), so existing call sites keep compiling and behaving unchanged through
/// the thin wrappers above.
pub(crate) struct SlsOptions<'a> {
    /// O(violated) PAWS bump — see [`Tracker::bump_violated_weights`].
    pub(crate) fast_bump: bool,
    /// Per-run variable cap — see [`search_with_limits`].
    pub(crate) max_vars: usize,
    /// Hard cap on flips (defaults to [`MAX_FLIPS`]). A small cap lets tests run
    /// the loop fully deterministically, with no wall-clock deadline.
    pub(crate) max_flips: u64,
    /// OPTIONAL externally-provided restart seed points (design §3.1's third
    /// restart layer, e.g. a future LP-rounded fractional point): candidate
    /// assignments the [`RestartLayer::ExternalSeed`] layer cycles through.
    /// Empty disables the layer (the cycle is then biased-random ↔
    /// best-incumbent only). Only consulted when `restarts` is on. ADVISORY
    /// ONLY — a bad seed just wastes a restart; every incumbent is still
    /// independently re-verified before it is reported.
    pub(crate) external_seeds: &'a [Vec<bool>],
    /// Layered stagnation restarts (design §3.1) — DEFAULT OFF. Restarts are
    /// the DIVERSIFICATION arm for parallel primal workers (design §2.3), not
    /// part of the single default trajectory: the full-slice A/B (2026-07-10,
    /// 30s, 107 instances) measured enabled-by-default as net-negative in the
    /// sequential trajectory — answer coverage identical to baseline (95/107,
    /// 0 wrong) but per-instance quality net −4, because restarts rescue
    /// SMTI-class FLATLINED feasibility hunts (SMTI_10000 UNKNOWN→SAT,
    /// plain-cod2 o −2805→−7458) while interfering with whole-budget
    /// CONVERGING grinds (RCPSP j120 SAT→UNKNOWN, benchsMusee_binary
    /// −1791→−35) whose answers only land in the final flush. When off, the
    /// scheduler is never constructed and the loop reproduces the pre-restart
    /// trajectory bit-for-bit; a diversified worker opts in explicitly.
    pub(crate) restarts: bool,
    /// XOR-diversifier folded into the structural RNG seed (design §2.3): a
    /// diversified parallel worker passes its own fixed nonzero constant so
    /// its trajectory deterministically differs from the default worker's on
    /// the same instance (and from the other diversified workers'). Still
    /// structure-only — no entropy, no instance identity — so every run stays
    /// bit-for-bit reproducible. `0` (the default) reproduces the unmodified
    /// [`structural_seed`] exactly.
    pub(crate) seed_xor: u64,
    /// OPTIONAL starting assignment (e.g. the LP-rounded point of the
    /// `lp-round-sls-opt` worker). Used only when its length matches the
    /// variable count; otherwise the default all-false start applies.
    /// ADVISORY ONLY — the start point steers the trajectory, never
    /// soundness: every incumbent is still independently re-verified.
    pub(crate) start: Option<&'a [bool]>,
    /// Feasibility-phase plateau weighting scheme (design §2.2) — DEFAULT
    /// [`WeightScheme::Paws`], which reproduces the historical trajectory
    /// bit-for-bit. [`WeightScheme::Ddfw`] is the A/B-gated quality-increment
    /// arm for DIVERSIFIED workers (the 60-strictly-suboptimal axis): at each
    /// stuck event, weight is TRANSFERRED into every violated row from its
    /// max-weight satisfied neighbor instead of additively bumped (see
    /// [`Tracker::ddfw_transfer_weights`]). ADVISORY ONLY — weights steer the
    /// search; every incumbent is still independently re-verified.
    pub(crate) weighting: WeightScheme,
    /// Smoothed Configuration Checking (design §2.2) — DEFAULT OFF (the
    /// default trajectory stays bit-identical). When on (an A/B-gated
    /// diversified-worker arm), only configuration-changed variables — those
    /// with a neighbor flipped since their own last flip — are eligible for
    /// the feasibility-phase GREEDY pick (falling back to the existing noise
    /// pick when no candidate is eligible), with a random small fraction
    /// re-enabled on the [`SCC_SMOOTH_INTERVAL`] smoothing cadence. ADVISORY
    /// ONLY — eligibility steers the search, never soundness.
    pub(crate) scc: bool,
}

impl Default for SlsOptions<'_> {
    fn default() -> Self {
        SlsOptions {
            fast_bump: false,
            max_vars: MAX_SLS_VARS,
            max_flips: MAX_FLIPS,
            external_seeds: &[],
            restarts: false,
            seed_xor: 0,
            start: None,
            weighting: WeightScheme::Paws,
            scc: false,
        }
    }
}

/// As [`search_with_limits`], but taking the full additive option set
/// ([`SlsOptions`]), including the externally-provided restart seed points.
/// This is the real two-phase search entry; every other `search*` entry point
/// is a thin source-compatible wrapper over it.
///
/// # i64 fast path (design §3.1 / §4)
/// Dispatches the monomorphized [`search_loop`] on the per-instance exact
/// overflow flag ([`rows_fit`]): when every row's `Σ|coeff| + |rhs|` provably
/// fits `i64`, the whole flip loop runs on the `i64` tracker (half the memory
/// traffic, no 128-bit saturating ops in the hot path); otherwise on the
/// exact `i128` tracker. Both compute identical values, so the trajectory is
/// bit-identical either way (pinned by
/// `search_loop_i64_and_i128_trajectories_identical` over the full
/// weighting/SCC options matrix, i.e. including the DDFW/SCC worker
/// configuration) — the flag is purely a throughput lever, and
/// [`Tracker::new`] re-checks it fail-closed.
/// Measured (`bench_tracker_i64_vs_i128_flip_rate`, release, busy host, best
/// of 2, 2026-07-11): i64 is 1.95–2.08× the i128 flip rate on the 10k-var and
/// 2.42–2.48× on the 100k-var mixed Ge/Eq synthetic instances.
pub(crate) fn search_with_seeds(
    instance: &PbInstance,
    objective: &PbObjective,
    deadline: Option<std::time::Instant>,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
    options: &SlsOptions<'_>,
) -> Option<SlsResult> {
    if rows_fit::<i64>(&instance.constraints) {
        search_loop::<i64>(
            instance,
            objective,
            deadline,
            should_stop,
            on_improve,
            options,
        )
    } else {
        search_loop::<i128>(
            instance,
            objective,
            deadline,
            should_stop,
            on_improve,
            options,
        )
    }
}

/// The real two-phase search loop, monomorphized per tracker width `T` (see
/// [`search_with_seeds`] for the dispatch contract).
fn search_loop<T: ScoreInt>(
    instance: &PbInstance,
    objective: &PbObjective,
    deadline: Option<std::time::Instant>,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
    options: &SlsOptions<'_>,
) -> Option<SlsResult> {
    let fast_bump = options.fast_bump;
    let num_vars = usize::try_from(instance.num_vars).ok()?;
    if num_vars == 0 || num_vars > options.max_vars {
        return None;
    }
    if objective.terms.is_empty() {
        return None;
    }

    let stop = || should_stop() || deadline.is_some_and(|dl| std::time::Instant::now() >= dl);
    if stop() {
        return None;
    }

    let obj_deltas = objective_deltas(objective, num_vars)?;

    let mut rng = SplitMix64::new(structural_seed(instance, objective) ^ options.seed_xor);

    // Start from an all-false assignment (a deterministic, structure-free seed).
    // The feasibility phase finds a feasible point from here; the seed choice only
    // affects search trajectory, never soundness.
    //
    // Opt-in (AY_PB_BNN_FEAS): on recognized binarized-neural-net OPT-LIN instances
    // (the `bnn_mnist_*` family), forward-propagate a structure-aware feasibility
    // seed instead of all-false. This is purely a different STARTING POINT for the
    // same search — ADVISORY ONLY. Every incumbent is still re-verified by
    // `try_record_incumbent` below and by `sanitize_optimization_incumbent` in the
    // portfolio, so a recognizer bug can only waste cycles, never emit a wrong
    // answer. The flag gates it (like `AY_PB_LNS2`) for clean A/B comparison; when
    // unset, the all-false path is byte-identical to before.
    let mut assignment = vec![false; num_vars];
    if bnn_feas_enabled() {
        if let Some(seed) = crate::optimize::bnn_feas::seed(instance, objective) {
            if seed.len() == num_vars {
                assignment = seed;
            }
        }
    }
    // An explicit caller-provided start ([`SlsOptions::start`], e.g. the
    // LP-rounded point) wins over both defaults. ADVISORY ONLY — a bad start
    // just costs feasibility-hunt flips; wrong lengths are ignored, never
    // truncated/padded. Default `None` keeps the path above byte-identical.
    if let Some(start) = options.start {
        if start.len() == num_vars {
            assignment.copy_from_slice(start);
        }
    }
    let mut tracker = Tracker::<T>::new(instance, num_vars, &assignment, fast_bump)?;
    // DDFW / SCC A/B arms (design §2.2, default OFF): the row-members CSR and
    // the configuration bits are built ONLY when a diversified worker opts in,
    // so the default path pays neither memory nor build time and its
    // trajectory stays bit-identical (see `ddfw_scc_default_off_matches_
    // disabled_run`). Both are ADVISORY search state.
    if options.weighting == WeightScheme::Ddfw || options.scc {
        tracker.build_row_members();
        if options.scc {
            tracker.enable_scc();
        }
    }

    let mut best: Option<SlsResult> = None;
    let mut flips: u64 = 0;
    let mut stale: u64 = 0;
    // Layered restarts (design §3.1) are OPT-IN (`SlsOptions::restarts`, the
    // diversified-worker arm): when off, the scheduler and its scratch buffer
    // are never constructed and the hot loop pays a single `is-Some` branch,
    // reproducing the pre-restart trajectory bit-for-bit. When on, the dwell
    // is instance-size-scaled (see `RESTART_DWELL_OCC_DIVISOR`) so the
    // per-restart reseat cost stays a bounded fraction of the inter-restart
    // work even in the worst kick case (no incumbent yet, diff ≈ n/10), and
    // the scratch is hoisted so a fired restart never allocates (design §4
    // budget: O(touched) work, no realloc).
    let mut restart: Option<(RestartState<'_>, Vec<bool>)> = if options.restarts {
        let effective_dwell =
            RESTART_DWELL_THRESHOLD.max(tracker.total_occurrences() / RESTART_DWELL_OCC_DIVISOR);
        Some((
            RestartState::new(options.external_seeds, effective_dwell),
            vec![false; num_vars],
        ))
    } else {
        None
    };
    // The endgame best-compensator swap targets the multi-row EQUALITY wall; a
    // pure-`Ge` (covering / knapsack) instance has no equality ridge for it to cross
    // (a single flip can always satisfy a violated `Ge` row), so disable it there to
    // keep the trajectory byte-identical and avoid paying its scan for no benefit.
    let has_eq = instance
        .constraints
        .iter()
        .any(|c| matches!(c.rel, PbRel::Eq));
    let endgame_threshold = if has_eq { endgame_threshold() } else { 0 };

    while flips < options.max_flips {
        if flips.is_multiple_of(STOP_POLL_INTERVAL) && stop() {
            break;
        }

        // ---- SCC smoothing (design §2.2, opt-in) ----
        // On the aging cadence, re-enable a random small fraction of
        // configuration bits so the CC tabu never freezes permanently. Only
        // the SCC arm draws these RNG values (default trajectory unchanged).
        if options.scc && flips > 0 && flips.is_multiple_of(SCC_SMOOTH_INTERVAL) {
            tracker.scc_smooth(&mut rng);
        }

        // ---- Layered restart on stagnation (design §3.1, opt-in) ----
        // Re-seat the search at the next layer's target point; PAWS weights
        // persist across the restart (see `reseat_assignment`). Purely a
        // trajectory change — soundness is untouched (every incumbent is still
        // re-verified in `try_record_incumbent`).
        if let Some((restart, scratch)) = restart.as_mut() {
            if restart.should_fire() {
                fire_restart(
                    instance,
                    objective,
                    restart,
                    &mut assignment,
                    scratch,
                    &mut tracker,
                    &mut best,
                    &mut rng,
                    on_improve,
                    &stop,
                );
            }
        }

        let best_before = best.as_ref().map(|b| b.objective);
        if tracker.num_violated() > 0 {
            // ---- Feasibility phase ----
            feasibility_step(
                instance,
                &mut assignment,
                &mut tracker,
                &mut rng,
                &mut stale,
                endgame_threshold,
                options.weighting,
            );
        } else {
            // Reached (or are at) a feasible point. Re-verify and record before
            // descending, so even a single feasible touch yields an incumbent.
            try_record_incumbent(
                instance,
                objective,
                &assignment,
                &mut best,
                on_improve,
                &stop,
            );
            // ---- Objective-descent phase ----
            let made_progress = objective_step(
                num_vars,
                &mut assignment,
                &mut tracker,
                &obj_deltas,
                &mut rng,
            );
            if !made_progress {
                // Local optimum under feasibility-preserving single flips. Take a
                // random feasibility-preserving flip to diversify; if none exists,
                // perturb by allowing a small infeasible excursion (the feasibility
                // phase will repair it, and we already recorded the best feasible).
                if !random_feasible_flip(num_vars, &mut assignment, &mut tracker, &mut rng) {
                    perturb(num_vars, &mut assignment, &mut tracker, &mut rng);
                }
            }
        }
        let best_after = best.as_ref().map(|b| b.objective);
        if let Some((restart, _)) = restart.as_mut() {
            restart.note_step(
                tracker.num_violated(),
                tracker.total_shortfall,
                best_after != best_before,
            );
        }

        flips += 1;
    }

    // Final feasibility check: if we ended on a feasible point not yet recorded,
    // record it.
    if tracker.num_violated() == 0 {
        try_record_incumbent(
            instance,
            objective,
            &assignment,
            &mut best,
            on_improve,
            &stop,
        );
    }

    best
}

/// NuPBO-class **unified** local search: a single loop driven by the shared
/// incremental [`crate::optimize::unified_score::Scorer`] (objective-as-soft cost), which
/// — unlike the two-phase `search` above — may move through *mildly-infeasible*
/// regions to reach a better optimum. It can warm-start from an EXISTING feasible
/// incumbent (`warm_start`) to escape a suboptimal feasible point that no single
/// feasibility-preserving flip can improve (the "trapped suboptimal" case), or
/// start from all-false to find a first incumbent from scratch.
///
/// The scorer's objective-pressure weight λ is HARD-LOCKED at 0 until the first
/// feasible assignment (design §2.1): an infeasible start runs a pure
/// feasibility hunt first. A FEASIBLE warm start (the polish path) releases the
/// lock at step 0 with λ = [`crate::optimize::unified_score::LAMBDA_INIT`], so
/// polish runs do objective descent immediately.
///
/// # Soundness (identical guarantee to `search`)
/// The scorer is advisory only. Every assignment this loop wants to report is
/// re-verified by [`verify_all_constraints`] against ALL original constraints and
/// re-valued exactly by [`eval_objective`] inside [`try_record_incumbent`] before
/// `on_improve` is called (and the caller re-verifies again). This function NEVER
/// returns a proven OPTIMUM or UNSAT — only strictly-improving feasible incumbents.
///
/// Returns the best feasible incumbent found, or `None` if none was reached.
pub(crate) fn search_unified(
    instance: &PbInstance,
    objective: &PbObjective,
    deadline: Option<std::time::Instant>,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
    warm_start: Option<&[bool]>,
) -> Option<SlsResult> {
    /// Random-goodvar diversification probability (in 1/1000) for [`Scorer::pick_var`].
    const RD_PROB_PERMILLE: u64 = 10;
    /// Best-from-Multiple-Selections sample size for [`Scorer::pick_var`].
    const BMS: usize = 50;

    let num_vars = usize::try_from(instance.num_vars).ok()?;
    if num_vars == 0 || num_vars > MAX_SLS_VARS {
        return None;
    }
    if objective.terms.is_empty() {
        return None;
    }

    let stop = || should_stop() || deadline.is_some_and(|dl| std::time::Instant::now() >= dl);
    if stop() {
        return None;
    }

    let mut rng = SplitMix64::new(structural_seed(instance, objective));

    // Seed assignment: a valid-length warm start (e.g. an existing incumbent),
    // else all-false. The seed only affects the search trajectory, never soundness.
    let assignment = match warm_start {
        Some(ws) if ws.len() == num_vars => ws.to_vec(),
        _ => vec![false; num_vars],
    };

    let mut scorer = crate::optimize::unified_score::Scorer::new(
        &instance.constraints,
        objective,
        num_vars,
        &assignment,
    )?;

    let mut best: Option<SlsResult> = None;

    // If the warm start (or all-false) is already feasible, record it first so a
    // warm-started run never *loses* the incumbent it was handed.
    if scorer.is_feasible() {
        try_record_incumbent(
            instance,
            objective,
            scorer.assignment(),
            &mut best,
            on_improve,
            &stop,
        );
    }

    let mut flips: u64 = 0;
    while flips < MAX_FLIPS {
        if flips.is_multiple_of(STOP_POLL_INTERVAL) && stop() {
            break;
        }
        let Some(v) = scorer.pick_var(&mut rng, RD_PROB_PERMILLE, BMS) else {
            break;
        };
        scorer.flip(v);
        if scorer.is_feasible() {
            try_record_incumbent(
                instance,
                objective,
                scorer.assignment(),
                &mut best,
                on_improve,
                &stop,
            );
        }
        flips += 1;
    }

    best
}

/// A single normalized (all-coefficients-positive) `>=` row term: the variable,
/// the value of that variable that makes the normalized literal TRUE, and the
/// positive coefficient.
struct NormTerm {
    var: u32,
    want: bool,
    coeff: i128,
}

/// Normalizes a linear `Σ coeff·lit >= rhs` row to all-positive coefficients,
/// pushing each `(var, want, |coeff|)` term and returning the adjusted degree.
/// Returns `None` on a non-linear term, out-of-range var, or overflow. `out` is
/// appended to; the count of pushed terms is bounded by the caller via `budget`.
fn normalize_ge_row(
    terms: &[PbTerm],
    rhs: i128,
    num_vars: usize,
    out: &mut Vec<NormTerm>,
) -> Option<i128> {
    let mut deg = rhs;
    for term in terms {
        let [lit] = term.lits.as_slice() else {
            return None; // non-linear
        };
        let var_index = (lit.var as usize).checked_sub(1)?;
        if var_index >= num_vars {
            return None;
        }
        let c = term.coeff;
        // literal true <=> var == !negated.
        let (a, want) = if c >= 0 {
            (c, !lit.negated)
        } else {
            // c·l = c + |c|·(~l); ~l true <=> literal false <=> var == negated.
            deg = deg.checked_add(c.checked_neg()?)?;
            (c.checked_neg()?, lit.negated)
        };
        if a == 0 {
            continue;
        }
        out.push(NormTerm {
            var: u32::try_from(var_index).ok()?,
            want,
            coeff: a,
        });
    }
    Some(deg)
}

/// Sound unit-propagation seed for the SLS feasibility phase. Performs bounded
/// pseudo-Boolean unit propagation over the NORMALIZED hard constraints
/// (equalities contribute both their `>=` and `<=` directions, where propagation
/// is strongest) to fix the variables that are forced to one value in EVERY
/// feasible assignment, then fills the rest with `false`.
///
/// # Soundness
/// This is used ONLY as a starting assignment for [`search_unified`]; it never
/// decides any verdict. Even a propagation bug could only change the search
/// trajectory, never correctness — every incumbent is still independently
/// re-verified by [`verify_all_constraints`]. Returns `None` (caller falls back to
/// the all-false seed) on a non-linear / oversized instance, or when propagation
/// derives a conflict (no information to seed from).
pub(crate) fn up_seed(instance: &PbInstance) -> Option<Vec<bool>> {
    /// Max propagation rounds. A seed needs only the cheap, shallow forced units;
    /// a fixpoint is not required (the search repairs the rest).
    const MAX_ROUNDS: usize = 32;

    let num_vars = usize::try_from(instance.num_vars).ok()?;
    if num_vars == 0 || num_vars > MAX_SLS_VARS {
        return None;
    }

    // Build the normalized `>=` rows once (each row: contiguous slice of NormTerm).
    let mut rows: Vec<(std::ops::Range<usize>, i128)> = Vec::new();
    let mut flat: Vec<NormTerm> = Vec::new();
    for constraint in &instance.constraints {
        let start = flat.len();
        let deg = normalize_ge_row(&constraint.terms, constraint.rhs, num_vars, &mut flat)?;
        rows.push((start..flat.len(), deg));
        if flat.len() > MAX_SLS_OCCURRENCES {
            return None;
        }
        if constraint.rel == PbRel::Eq {
            // The `<=` direction: Σ coeff·lit <= rhs  <=>  Σ (-coeff)·lit >= -rhs.
            let start = flat.len();
            // Re-emit with negated coefficients by normalizing a negated view.
            let neg_terms: Vec<PbTerm> = constraint
                .terms
                .iter()
                .map(|t| PbTerm {
                    coeff: t.coeff.checked_neg().unwrap_or(i128::MIN / 2),
                    lits: t.lits.clone(),
                })
                .collect();
            let deg = normalize_ge_row(
                &neg_terms,
                constraint.rhs.checked_neg()?,
                num_vars,
                &mut flat,
            )?;
            rows.push((start..flat.len(), deg));
            if flat.len() > MAX_SLS_OCCURRENCES {
                return None;
            }
        }
    }

    let mut val: Vec<Option<bool>> = vec![None; num_vars];
    let mut forced_any = false;
    for _round in 0..MAX_ROUNDS {
        let mut changed = false;
        for (range, deg) in &rows {
            let slice = &flat[range.clone()];
            // fixed = Σ coeff of terms whose normalized literal is already TRUE.
            // free_sum = Σ coeff of terms whose var is unassigned.
            let mut fixed: i128 = 0;
            let mut free_sum: i128 = 0;
            for t in slice {
                match val[t.var as usize] {
                    Some(b) if b == t.want => fixed = fixed.saturating_add(t.coeff),
                    Some(_) => {}
                    None => free_sum = free_sum.saturating_add(t.coeff),
                }
            }
            let deg_remaining = deg.saturating_sub(fixed);
            let slack = free_sum.saturating_sub(deg_remaining);
            if slack < 0 {
                return None; // conflict: nothing to seed from, fall back
            }
            for t in slice {
                if val[t.var as usize].is_none() && t.coeff > slack {
                    val[t.var as usize] = Some(t.want);
                    changed = true;
                    forced_any = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    if !forced_any {
        return None; // no forced units: no benefit over the all-false seed
    }
    Some(val.into_iter().map(|v| v.unwrap_or(false)).collect())
}

/// One feasibility-phase flip: pick a random violated constraint, then flip the
/// variable in it that most reduces weighted violation (WalkSAT noise: sometimes
/// a random variable from that constraint). On a non-improving move, escalate
/// weights to escape the plateau — PAWS additive bump by default, or the DDFW
/// weight transfer when the diversified worker opted into
/// [`WeightScheme::Ddfw`] (design §2.2). Under SCC (also opt-in, design §2.2)
/// the greedy pick considers only configuration-changed candidates, falling
/// back to the existing noise pick when none is eligible.
#[allow(clippy::too_many_arguments)]
fn feasibility_step<T: ScoreInt>(
    instance: &PbInstance,
    assignment: &mut [bool],
    tracker: &mut Tracker<T>,
    rng: &mut SplitMix64,
    stale: &mut u64,
    endgame_threshold: usize,
    weighting: WeightScheme,
) {
    // Pick a random violated constraint directly from the incrementally-maintained
    // violated-set (O(1), no full constraint rescan).
    if tracker.violated_list.is_empty() {
        return;
    }
    // Near-feasible endgame? Captured BEFORE the primary flip: this is the regime
    // (few violated rows) where the deterministic best-compensator swap is both
    // cheap and the precise move to cross the last equality ridge.
    let in_endgame = endgame_threshold > 0 && tracker.num_violated() <= endgame_threshold;
    let pick = tracker.violated_list[rng.below(tracker.violated_list.len())];
    let constraint = &instance.constraints[pick];

    // Candidate variables: those appearing in the chosen violated constraint.
    let mut candidate_vars: Vec<usize> = Vec::with_capacity(constraint.terms.len());
    for term in &constraint.terms {
        if let Some([lit]) = Some(term.lits.as_slice()).filter(|s| s.len() == 1) {
            if let Some(idx) = (lit.var as usize).checked_sub(1) {
                if idx < assignment.len() {
                    candidate_vars.push(idx);
                }
            }
        }
    }
    if candidate_vars.is_empty() {
        return;
    }

    let chosen = if rng.below(1000) < WALK_NOISE_PERMILLE as usize {
        // Random-walk: pick any variable from the constraint.
        candidate_vars[rng.below(candidate_vars.len())]
    } else {
        // Greedy: pick the variable whose flip most reduces weighted violation.
        // Under SCC (design §2.2, opt-in) only configuration-changed candidates
        // are eligible; `scc_eligible` is `true` for every variable when SCC is
        // off, so the default path is bit-identical (first candidate wins ties,
        // no RNG draw — exactly the historical scan).
        let mut best: Option<(usize, i128)> = None;
        for &v in &candidate_vars {
            if !tracker.scc_eligible(v) {
                continue;
            }
            let d = tracker.flip_violation_delta(v, assignment[v]);
            if best.is_none_or(|(_, bd)| d < bd) {
                best = Some((v, d));
            }
        }
        match best {
            Some((v, _)) => v,
            // SCC fallback: every candidate is configuration-UNCHANGED (its
            // whole neighborhood is quiet since it last flipped) — fall back
            // to the existing noise pick rather than replaying a stale greedy
            // choice. Only reachable with SCC on.
            None => candidate_vars[rng.below(candidate_vars.len())],
        }
    };

    let chosen_delta = tracker.flip_violation_delta(chosen, assignment[chosen]);
    let improving = chosen_delta < 0;
    let new_value = !assignment[chosen];
    assignment[chosen] = new_value;
    tracker.apply_flip(chosen, new_value);

    if improving {
        *stale = 0;
        return;
    }

    // Non-improving single flip: this is the equality-wall plateau where
    // single-flip min-conflicts stalls. In the near-feasible endgame, extend the
    // just-applied flip into a 2-flip SWAP — DETERMINISTICALLY find the partner
    // variable whose flip best CANCELS the residual violation the single flip left,
    // yielding a net strictly-improving move that no single flip could. The
    // just-applied flip is the first half; `chosen_delta` is its standalone
    // violation delta, so a partner with combined delta < 0 is a real improvement.
    // (Soundness unaffected: the tracker is advisory; every incumbent is still
    // re-verified by `verify_all_constraints`.)
    //
    // The swap SUPPLEMENTS the PAWS weight escalation; it never replaces it. An
    // earlier design returned right after a successful swap (resetting `stale`),
    // which starved the PAWS bumps that are the dominant plateau-escape mechanism
    // for these equality systems and measured as a net regression. Here the
    // stale-counter / weight-bump logic always runs, so the swap is purely additive
    // exploration: it can only help, never disable PAWS.
    if in_endgame && endgame_compensator_swap(instance, assignment, tracker, chosen, chosen_delta) {
        // A successful endgame swap is a genuine strict reduction in total weighted
        // violation, i.e. real progress. Treat it like an improving single flip:
        // reset the staleness counter and SKIP the PAWS bump, so the weight
        // landscape is not perturbed away from the basin the swap just entered (an
        // unconditional bump here caused the endgame to oscillate and lowered the
        // feasibility hit-rate in measurement).
        *stale = 0;
        return;
    }

    // Weight escalation: no improving single flip and no successful endgame
    // swap. PAWS bumps additively; the DDFW arm (design §2.2) TRANSFERS weight
    // into the violated rows from their satisfied neighbors instead.
    *stale += 1;
    match weighting {
        WeightScheme::Paws => {
            if *stale >= PAWS_BUMP_INTERVAL {
                tracker.bump_violated_weights();
                *stale = 0;
            }
        }
        WeightScheme::Ddfw => {
            if *stale >= DDFW_STUCK_INTERVAL {
                tracker.ddfw_transfer_weights();
                *stale = 0;
            }
        }
    }
}

/// Deterministic best-compensator second half of a 2-flip SWAP, confined to the
/// near-feasible endgame. The primary flip (`primary`, with standalone
/// weighted-violation delta `primary_delta`) has ALREADY been applied and was
/// non-improving. This DETERMINISTICALLY scans EVERY variable occurring in the
/// currently-violated rows for the partner `w` whose flip yields the most-negative
/// combined delta `primary_delta + delta(w)`; if that best combined delta is
/// strictly negative it applies `w` (a net strict reduction in total weighted
/// violation that crosses the equality ridge no single flip could) and returns
/// `true`. Ties are broken by smallest variable index for bit-for-bit
/// reproducibility. Otherwise it leaves the primary flip in place and returns
/// `false` (the caller then bumps weights as usual).
///
/// Unlike the historical W3 swap (random-sampled partners on every plateau), this
/// is fully deterministic (no RNG draw) and only ever runs when the violated set is
/// small (the endgame), so the per-plateau scan — bounded by the sum of violated-row
/// sizes — is cheap, and the move is the precise one needed to repair the last few
/// equality rows.
///
/// Correctness of the combined delta: `delta(w)` is evaluated on the CURRENT tracker
/// state, which already reflects the primary flip, so `primary_delta + delta(w)` is
/// exactly the change in total weighted violation versus the pre-primary state —
/// including any rows the two variables share. A candidate that occurs in several
/// violated rows is simply re-evaluated to the same delta, so the running minimum is
/// unaffected (correct, just a few wasted ops — negligible in the endgame).
fn endgame_compensator_swap<T: ScoreInt>(
    instance: &PbInstance,
    assignment: &mut [bool],
    tracker: &mut Tracker<T>,
    primary: usize,
    primary_delta: i128,
) -> bool {
    let mut best_w: Option<usize> = None;
    let mut best_total: i128 = 0; // strictly negative combined delta required
    for vi in 0..tracker.violated_list.len() {
        let c = tracker.violated_list[vi];
        for term in &instance.constraints[c].terms {
            let [lit] = term.lits.as_slice() else {
                continue;
            };
            let Some(w) = (lit.var as usize).checked_sub(1) else {
                continue;
            };
            if w >= assignment.len() || w == primary {
                continue;
            }
            let total =
                primary_delta.saturating_add(tracker.flip_violation_delta(w, assignment[w]));
            if total >= 0 {
                continue; // not a net improvement over the pre-primary state
            }
            match best_w {
                None => {
                    best_total = total;
                    best_w = Some(w);
                }
                Some(b) => {
                    // Most-negative wins; ties -> smallest index (deterministic).
                    if total < best_total || (total == best_total && w < b) {
                        best_total = total;
                        best_w = Some(w);
                    }
                }
            }
        }
    }
    if let Some(w) = best_w {
        let new_value = !assignment[w];
        assignment[w] = new_value;
        tracker.apply_flip(w, new_value);
        true
    } else {
        false
    }
}

/// One objective-descent flip while staying feasible. Scans objective variables
/// for a feasibility-preserving flip that strictly lowers the objective and takes
/// the best one. Returns `true` if a strictly-improving feasible flip was made.
fn objective_step<T: ScoreInt>(
    num_vars: usize,
    assignment: &mut [bool],
    tracker: &mut Tracker<T>,
    obj_deltas: &[i128],
    rng: &mut SplitMix64,
) -> bool {
    // Occasionally take a random feasibility-preserving move (possibly worsening
    // the objective) to escape a local optimum.
    if rng.below(1000) < OBJ_NOISE_PERMILLE as usize {
        return false;
    }

    let mut best_var: Option<usize> = None;
    let mut best_gain: i128 = 0; // require strictly negative objective delta
    for var in 0..num_vars {
        // Objective delta of flipping `var`: if currently true, flipping to false
        // subtracts `obj_deltas[var]`; if false, adds it.
        let delta = if assignment[var] {
            obj_deltas[var].saturating_neg()
        } else {
            obj_deltas[var]
        };
        if delta >= 0 {
            continue;
        }
        if delta < best_gain {
            // Only commit to feasibility check for promising candidates.
            if tracker.flip_preserves_feasibility(var, assignment[var]) {
                best_gain = delta;
                best_var = Some(var);
            }
        }
    }

    if let Some(var) = best_var {
        let new_value = !assignment[var];
        assignment[var] = new_value;
        tracker.apply_flip(var, new_value);
        true
    } else {
        false
    }
}

/// Takes one random feasibility-preserving flip (any variable). Returns `true` if
/// such a flip was found and applied. Used to diversify when objective descent is
/// stuck at a local optimum.
fn random_feasible_flip<T: ScoreInt>(
    num_vars: usize,
    assignment: &mut [bool],
    tracker: &mut Tracker<T>,
    rng: &mut SplitMix64,
) -> bool {
    // Try a bounded number of random variables; if one preserves feasibility, flip
    // it. Bounded so this never dominates the loop.
    let attempts = 32usize.min(num_vars);
    for _ in 0..attempts {
        let var = rng.below(num_vars);
        if tracker.flip_preserves_feasibility(var, assignment[var]) {
            let new_value = !assignment[var];
            assignment[var] = new_value;
            tracker.apply_flip(var, new_value);
            return true;
        }
    }
    false
}

/// Perturbs the assignment by flipping a few random variables (which may break
/// feasibility); the feasibility phase will repair it. Used only when no
/// feasibility-preserving diversification flip exists. The best feasible incumbent
/// has already been recorded, so this can only help explore — never lose progress.
fn perturb<T: ScoreInt>(
    num_vars: usize,
    assignment: &mut [bool],
    tracker: &mut Tracker<T>,
    rng: &mut SplitMix64,
) {
    let kicks = 1 + rng.below(3);
    for _ in 0..kicks {
        let var = rng.below(num_vars);
        let new_value = !assignment[var];
        assignment[var] = new_value;
        tracker.apply_flip(var, new_value);
    }
}

/// Re-verifies `assignment` against ALL original constraints and recomputes the
/// objective exactly. If it is feasible AND strictly better than the current best,
/// records it as the new incumbent and streams it via `on_improve`.
///
/// This is the module-local soundness gate: nothing is ever reported that does not
/// pass `verify_all_constraints` with an exactly-recomputed objective. (The caller
/// re-verifies again via `sanitize_optimization_incumbent` — two independent
/// checks.)
fn try_record_incumbent(
    instance: &PbInstance,
    objective: &PbObjective,
    assignment: &[bool],
    best: &mut Option<SlsResult>,
    on_improve: &mut dyn FnMut(i128, &[bool]),
    stop: &dyn Fn() -> bool,
) {
    if stop() {
        return;
    }
    // SOUNDNESS GATE: feasibility against the ORIGINAL constraints (exact, i128,
    // products via eval_term), and an exact objective recompute.
    if !verify_all_constraints(&instance.constraints, assignment) {
        return;
    }
    let objective_value = eval_objective(objective, assignment);
    let is_improvement = match best {
        Some(current) => objective_value < current.objective,
        None => true,
    };
    if !is_improvement {
        return;
    }
    let assignment_vec = assignment.to_vec();
    on_improve(objective_value, &assignment_vec);
    *best = Some(SlsResult {
        assignment: assignment_vec,
        objective: objective_value,
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{PbConstraint, PbLit, PbTerm};

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

    fn no_stop() -> impl Fn() -> bool {
        || false
    }

    /// Vertex-cover: edges require `x_u + x_v >= 1`; minimize `Σ x_i`. The
    /// all-false start is INFEASIBLE, so SLS must first reach feasibility, then
    /// descend.
    fn vertex_cover_instance(num_vertices: u32, edges: &[(u32, u32)]) -> (PbInstance, PbObjective) {
        let constraints: Vec<PbConstraint> = edges
            .iter()
            .map(|&(u, v)| ge(vec![term(1, lit(u)), term(1, lit(v))], 1))
            .collect();
        let objective = PbObjective {
            terms: (1..=num_vertices).map(|v| term(1, lit(v))).collect(),
        };
        let instance = PbInstance {
            num_vars: num_vertices,
            num_constraints: constraints.len() as u32,
            constraints,
            objective: Some(objective.clone()),
        };
        (instance, objective)
    }

    #[test]
    fn sls_finds_feasible_from_infeasible_start() {
        // Path 1-2-3-4-5-6. All-false is infeasible (every edge violated). SLS
        // must reach a feasible cover and report it.
        let (instance, objective) =
            vertex_cover_instance(6, &[(1, 2), (2, 3), (3, 4), (4, 5), (5, 6)]);
        let stop = no_stop();
        let mut reported = Vec::new();
        let mut on_improve = |obj: i128, model: &[bool]| {
            assert!(verify_all_constraints(&instance.constraints, model));
            reported.push(obj);
        };
        let result = search(
            &instance,
            &objective,
            Some(std::time::Instant::now() + std::time::Duration::from_millis(500)),
            &stop,
            &mut on_improve,
        )
        .expect("SLS should find a feasible cover");
        assert!(verify_all_constraints(
            &instance.constraints,
            &result.assignment
        ));
        assert_eq!(
            eval_objective(&objective, &result.assignment),
            result.objective
        );
        // The optimum cover of this path has size 3; SLS should at least be
        // feasible (<= 6) and typically much better. Soundness is the hard
        // requirement; quality is a bonus.
        assert!(result.objective <= 6);
        // Every reported value must be a real, monotone improvement.
        for window in reported.windows(2) {
            assert!(window[1] < window[0]);
        }
    }

    #[test]
    fn sls_drives_objective_down_on_star() {
        // Star: center 1 connected to leaves 2..=8. Optimum cover is {1} (cost 1).
        let edges: Vec<(u32, u32)> = (2..=8).map(|leaf| (1, leaf)).collect();
        let (instance, objective) = vertex_cover_instance(8, &edges);
        let stop = no_stop();
        let mut on_improve = |_obj: i128, _model: &[bool]| {};
        let result = search(
            &instance,
            &objective,
            Some(std::time::Instant::now() + std::time::Duration::from_millis(800)),
            &stop,
            &mut on_improve,
        )
        .expect("SLS should find a feasible star cover");
        assert!(verify_all_constraints(
            &instance.constraints,
            &result.assignment
        ));
        // Should drive well below the trivial all-true cost of 8.
        assert!(result.objective < 8);
    }

    #[test]
    fn sls_never_reports_infeasible_or_nonimproving_fuzz() {
        // Across many pseudo-random covering instances, every reported incumbent
        // (via on_improve and the returned value) must be feasible and strictly
        // improving. SLS must never emit an infeasible/non-improving "incumbent".
        let mut rng = SplitMix64::new(0x1357_9BDF_2468_ACE0);
        for _ in 0..30 {
            let num_vertices = 4 + rng.below(9) as u32;
            let edge_count = 3 + rng.below(12);
            let mut edges = Vec::new();
            for _ in 0..edge_count {
                let u = 1 + rng.below(num_vertices as usize) as u32;
                let mut v = 1 + rng.below(num_vertices as usize) as u32;
                if v == u {
                    v = 1 + (v % num_vertices);
                }
                edges.push((u, v));
            }
            let (instance, objective) = vertex_cover_instance(num_vertices, &edges);

            let stop = no_stop();
            let mut violations = 0usize;
            let mut prev: Option<i128> = None;
            let mut on_improve = |obj: i128, model: &[bool]| {
                if !verify_all_constraints(&instance.constraints, model) {
                    violations += 1;
                }
                if eval_objective(&objective, model) != obj {
                    violations += 1;
                }
                if let Some(p) = prev {
                    if obj >= p {
                        violations += 1;
                    }
                }
                prev = Some(obj);
            };
            let result = search(
                &instance,
                &objective,
                Some(std::time::Instant::now() + std::time::Duration::from_millis(60)),
                &stop,
                &mut on_improve,
            );
            assert_eq!(violations, 0, "SLS reported a bad incumbent");
            if let Some(r) = result {
                assert!(verify_all_constraints(&instance.constraints, &r.assignment));
                assert_eq!(eval_objective(&objective, &r.assignment), r.objective);
            }
        }
    }

    #[test]
    fn sls_respects_should_stop() {
        let (instance, objective) = vertex_cover_instance(6, &[(1, 2), (2, 3)]);
        let stop = || true;
        let mut called = false;
        let mut on_improve = |_obj: i128, _model: &[bool]| called = true;
        let result = search(&instance, &objective, None, &stop, &mut on_improve);
        assert!(result.is_none());
        assert!(!called);
    }

    #[test]
    fn sls_declines_nonlinear() {
        // A non-linear (product) constraint must make SLS decline (return None),
        // never track it incorrectly.
        let constraints = vec![PbConstraint {
            terms: vec![PbTerm {
                coeff: 1,
                lits: vec![lit(1), lit(2)],
            }],
            rel: PbRel::Ge,
            rhs: 1,
        }];
        let objective = PbObjective {
            terms: vec![term(1, lit(1)), term(1, lit(2))],
        };
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints,
            objective: Some(objective.clone()),
        };
        let stop = no_stop();
        let mut on_improve = |_obj: i128, _model: &[bool]| {};
        let result = search(&instance, &objective, None, &stop, &mut on_improve);
        assert!(result.is_none());
    }

    #[test]
    fn sls_with_limits_declines_above_cap_and_accepts_below() {
        // A small instance with 6 variables. With a per-run cap of 5 the search
        // must DECLINE (return None, no incumbent); with a cap of 6 (or more) it
        // must run and find a verified feasible incumbent. This locks in the
        // variable-cap override used by the WBO-reduction primal path, which
        // raises the cap so the soft-relaxation variable blow-up does not make
        // the SLS decline outright. Soundness is unaffected by the cap: it only
        // gates whether the advisory search runs.
        let (instance, objective) =
            vertex_cover_instance(6, &[(1, 2), (2, 3), (3, 4), (4, 5), (5, 6)]);
        let stop = no_stop();

        // Cap below the variable count -> decline.
        let mut on_improve_low = |_obj: i128, _model: &[bool]| {};
        let declined = search_with_limits(
            &instance,
            &objective,
            Some(std::time::Instant::now() + std::time::Duration::from_millis(200)),
            &stop,
            &mut on_improve_low,
            false,
            5,
        );
        assert!(declined.is_none(), "cap below var count must decline");

        // Cap at/above the variable count -> run and find a verified incumbent.
        let mut on_improve_ok = |obj: i128, model: &[bool]| {
            assert!(verify_all_constraints(&instance.constraints, model));
            assert_eq!(eval_objective(&objective, model), obj);
        };
        let accepted = search_with_limits(
            &instance,
            &objective,
            Some(std::time::Instant::now() + std::time::Duration::from_millis(500)),
            &stop,
            &mut on_improve_ok,
            false,
            6,
        )
        .expect("cap at var count must allow SLS to find a feasible cover");
        assert!(verify_all_constraints(
            &instance.constraints,
            &accepted.assignment
        ));
        assert_eq!(
            eval_objective(&objective, &accepted.assignment),
            accepted.objective
        );
        assert!(accepted.objective <= 6);
    }

    #[test]
    fn sls_handles_negated_literals_and_eq_rows() {
        // Eq row with negated literals: ~x1 + ~x2 = 1 means exactly one of x1, x2
        // is false. Objective min x1 + x2. Optimal feasible: one true, one false
        // -> objective 1. SLS must track the Eq/negated slack correctly enough to
        // find SOME feasible point, and (soundly) report only verified incumbents.
        let constraints = vec![PbConstraint {
            terms: vec![term(1, neg(1)), term(1, neg(2))],
            rel: PbRel::Eq,
            rhs: 1,
        }];
        let objective = PbObjective {
            terms: vec![term(1, lit(1)), term(1, lit(2))],
        };
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints,
            objective: Some(objective.clone()),
        };
        let stop = no_stop();
        let mut on_improve = |obj: i128, model: &[bool]| {
            assert!(verify_all_constraints(&instance.constraints, model));
            assert_eq!(eval_objective(&objective, model), obj);
        };
        let result = search(
            &instance,
            &objective,
            Some(std::time::Instant::now() + std::time::Duration::from_millis(300)),
            &stop,
            &mut on_improve,
        )
        .expect("SLS should find the exactly-one feasible point");
        assert!(verify_all_constraints(
            &instance.constraints,
            &result.assignment
        ));
        // Exactly one of x1/x2 is false -> exactly one is true -> objective 1.
        assert_eq!(result.objective, 1);
    }

    /// Differential + invariant test of the 2-flip SWAP move
    /// (`endgame_compensator_swap`). Across many random equality-heavy instances and
    /// random primary flips:
    /// (a) the incremental tracker's per-row LHS after primary+partner flips MUST
    ///     equal a from-scratch recompute (the advisory tracker stays exact through
    ///     a 2-flip move — the property the soundness gate relies on for steering),
    /// and (b) whenever `complete_swap` reports a swap, total weighted violation
    /// MUST have strictly decreased versus the pre-primary state (the move it claims
    /// is a real improvement, never a worsening one).
    #[test]
    fn endgame_compensator_swap_is_exact_and_improving() {
        let mut rng = SplitMix64::new(0x5A5A_1234_9876_F0F0);
        for _ in 0..200 {
            let n = 4 + rng.below(8); // 4..=11 vars
            let rows = 2 + rng.below(3); // 2..=4 equality rows
            let mut constraints = Vec::new();
            for _ in 0..rows {
                let k = 2 + rng.below(n - 1); // row size
                let mut terms = Vec::new();
                let mut used = vec![false; n];
                while terms.len() < k {
                    let v = rng.below(n);
                    if !used[v] {
                        used[v] = true;
                        terms.push(term(1 + rng.below(5) as i128, lit(v as u32 + 1)));
                    }
                }
                let rhs = rng.below(2 * k) as i128;
                constraints.push(eq(terms, rhs));
            }
            let objective = PbObjective {
                terms: (1..=n as u32).map(|v| term(1, lit(v))).collect(),
            };
            let instance = PbInstance {
                num_vars: n as u32,
                num_constraints: constraints.len() as u32,
                constraints,
                objective: Some(objective),
            };

            let mut assignment: Vec<bool> = (0..n).map(|_| rng.below(2) == 1).collect();
            let mut tracker = Tracker::<i128>::new(&instance, n, &assignment, false).unwrap();

            for _ in 0..20 {
                let pre = tracker.weighted_violation;
                let primary = rng.below(n);
                let primary_delta = tracker.flip_violation_delta(primary, assignment[primary]);
                let nv = !assignment[primary];
                assignment[primary] = nv;
                tracker.apply_flip(primary, nv);

                let swapped = endgame_compensator_swap(
                    &instance,
                    &mut assignment,
                    &mut tracker,
                    primary,
                    primary_delta,
                );

                // (a) incremental LHS == from-scratch recompute on the final assignment.
                let fresh = Tracker::<i128>::new(&instance, n, &assignment, false).unwrap();
                let inc: Vec<i128> = tracker.states.iter().map(|s| s.lhs).collect();
                let oracle: Vec<i128> = fresh.states.iter().map(|s| s.lhs).collect();
                assert_eq!(inc, oracle, "swap drifted tracker LHS from oracle");

                // (b) a reported swap strictly reduced total weighted violation
                // (weights are all 1 here — no PAWS bumps — so this is exactly the
                // combined <0 guarantee `complete_swap` enforces).
                if swapped {
                    assert!(
                        tracker.weighted_violation < pre,
                        "swap claimed improvement but violation did not drop: {} -> {}",
                        pre,
                        tracker.weighted_violation
                    );
                }
            }
        }
    }

    /// Exact LHS of a single linear row under `assignment`, computed directly
    /// from the ORIGINAL constraint (independent of the incremental tracker).
    fn oracle_row_lhs(constraint: &PbConstraint, assignment: &[bool]) -> i128 {
        let mut lhs: i128 = 0;
        for t in &constraint.terms {
            let l = t.lits[0];
            let var_true = assignment[(l.var - 1) as usize];
            let lit_true = if l.negated { !var_true } else { var_true };
            if lit_true {
                lhs = lhs.saturating_add(t.coeff);
            }
        }
        lhs
    }

    /// M0 differential-fuzz gate (design §2.6) for the two-phase `Tracker`: the
    /// cached per-row LHS, shortfall, violated set, and weighted violation must
    /// equal a from-scratch recompute over ARBITRARY flip sequences on random
    /// instances whose Eq rows AND Ge rows BOTH contain random negated literals
    /// — the slack-sign interaction the 2-flip swap fuzz (positive-only Eq rows)
    /// does not cover. Runs both PAWS-bump paths (`fast_bump` on/off), on BOTH
    /// tracker widths (design §3.1: "the differential-oracle fuzz tests must
    /// cover BOTH paths"): the i64 fast tracker on small coefficients and the
    /// i128 tracker on the same instances PLUS a huge-coefficient variant
    /// (values around 2⁷⁷, forcing genuinely 128-bit arithmetic).
    ///
    /// DDFW leg: interleaved [`Tracker::ddfw_transfer_weights`] sweeps (after
    /// [`Tracker::build_row_members`]) run on `Tracker::<T>` AND a forced
    /// `Tracker::<i128>` twin driven with identical flips/bumps, asserting
    /// per-row weight and `weighted_violation` equality between the widths —
    /// the weight-TRANSFER arithmetic (spare halving, floor, fallback bump)
    /// must be value-identical on both widths, like every other tracker op.
    fn tracker_differential_fuzz_impl<T: ScoreInt>(coeff_base: i128) {
        let mut rng = SplitMix64::new(0x0E60_57A1_D1FF_F022);
        for round in 0..40 {
            let n = 3 + rng.below(7); // 3..=9 vars
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
                    terms.push(term(coeff_base + 1 + rng.below(5) as i128, l));
                }
                if !any_neg {
                    // Guarantee EVERY row (Eq and Ge alike) exercises the
                    // negated slack-delta sign.
                    terms[0].lits[0].negated = true;
                }
                let rhs = coeff_base * (k as i128 / 2) + rng.below(3 * k) as i128 - k as i128;
                // Alternate Eq / Ge so both row kinds carry negated literals.
                constraints.push(if r % 2 == 0 {
                    eq(terms, rhs)
                } else {
                    ge(terms, rhs)
                });
            }
            let instance = PbInstance {
                num_vars: n as u32,
                num_constraints: rows as u32,
                constraints,
                objective: None,
            };
            // The width under test must actually accept these rows (the i64
            // instantiation is only ever called with small coefficients).
            assert!(rows_fit::<T>(&instance.constraints), "fuzz premise broken");

            let mut assignment: Vec<bool> = (0..n).map(|_| rng.below(2) == 1).collect();
            let fast_bump = round % 2 == 0;
            let mut tracker = Tracker::<T>::new(&instance, n, &assignment, fast_bump).unwrap();
            // Forced-i128 twin for the DDFW width differential: driven with
            // the exact same flip/bump/sweep sequence as the tracker under
            // test, so every per-row weight and violation total must stay
            // bit-identical between the widths at every step.
            let mut twin = Tracker::<i128>::new(&instance, n, &assignment, fast_bump).unwrap();
            // The DDFW sweep needs the row-members CSR on both trackers (the
            // search loop builds it for the DDFW/SCC arms).
            tracker.build_row_members();
            twin.build_row_members();

            let flips = 300 + rng.below(501); // 300..=800 steps
            for step in 0..flips {
                if step % 11 == 0 {
                    tracker.bump_violated_weights();
                    twin.bump_violated_weights();
                } else if step % 13 == 0 {
                    // DDFW leg: a weight-TRANSFER stuck-event sweep on both
                    // widths. The fallback count is part of the trajectory
                    // (it decides additive-vs-transfer per row), so it must
                    // match too.
                    let fallbacks = tracker.ddfw_transfer_weights();
                    assert_eq!(
                        twin.ddfw_transfer_weights(),
                        fallbacks,
                        "DDFW fallback-count drift between widths (round {round}, step {step})"
                    );
                } else {
                    let v = rng.below(n);
                    let nv = !assignment[v];
                    assignment[v] = nv;
                    tracker.apply_flip(v, nv);
                    twin.apply_flip(v, nv);
                }
                // Oracle: recompute every row's LHS / shortfall / violation from
                // the ORIGINAL constraint under the current assignment, in exact
                // i128 (independent of the tracker width under test).
                let mut oracle_weighted: i128 = 0;
                let mut oracle_raw: i128 = 0;
                let mut oracle_violated: Vec<usize> = Vec::new();
                for (ci, c) in instance.constraints.iter().enumerate() {
                    let lhs = oracle_row_lhs(c, &assignment);
                    assert_eq!(
                        tracker.states[ci].lhs.to_i128(),
                        lhs,
                        "lhs drift on row {ci} (round {round}, step {step})"
                    );
                    let short = shortfall_for(c.rel, lhs, c.rhs);
                    assert_eq!(
                        tracker.states[ci].shortfall().to_i128(),
                        short,
                        "shortfall drift on row {ci} (round {round}, step {step})"
                    );
                    // RAW total: sum over ALL rows (satisfied rows contribute 0).
                    oracle_raw = oracle_raw.saturating_add(short);
                    if short > 0 {
                        oracle_violated.push(ci);
                        oracle_weighted = oracle_weighted.saturating_add(
                            tracker.states[ci].weight.to_i128().saturating_mul(short),
                        );
                    }
                    // DDFW width differential: identical driving sequence ->
                    // identical per-row weights on both widths.
                    assert_eq!(
                        tracker.states[ci].weight.to_i128(),
                        twin.states[ci].weight.to_i128(),
                        "per-row weight drift between widths on row {ci} (round {round}, step {step})"
                    );
                }
                assert_eq!(
                    tracker.weighted_violation, oracle_weighted,
                    "weighted violation drift (round {round}, step {step})"
                );
                assert_eq!(
                    tracker.weighted_violation, twin.weighted_violation,
                    "weighted-violation drift between widths (round {round}, step {step})"
                );
                assert_eq!(
                    tracker.total_shortfall, oracle_raw,
                    "raw total-shortfall drift (round {round}, step {step})"
                );
                let mut got = tracker.violated_list.clone();
                got.sort_unstable();
                assert_eq!(
                    got, oracle_violated,
                    "violated-set drift (round {round}, step {step})"
                );
            }
        }
    }

    #[test]
    fn tracker_differential_fuzz_eq_and_ge_rows_with_negated_literals_i64() {
        tracker_differential_fuzz_impl::<i64>(0);
    }

    #[test]
    fn tracker_differential_fuzz_eq_and_ge_rows_with_negated_literals_i128() {
        // Same instances as the i64 run (identical values -> identical state),
        // pinning the two widths against the same oracle.
        tracker_differential_fuzz_impl::<i128>(0);
    }

    #[test]
    fn tracker_differential_fuzz_huge_coefficients_i128_only() {
        // Coefficients around 2^77: Σ|coeff| + |rhs| overflows i64 on every
        // row, so ONLY the i128 tracker may accept these instances — the fuzz
        // premise assert inside doubles as the dispatch-flag check, and the
        // i64 tracker must fail closed on the same rows.
        let huge = 1i128 << 77;
        tracker_differential_fuzz_impl::<i128>(huge);
    }

    /// Fail-closed narrowing: rows whose `Σ|coeff| + |rhs|` exceeds i64 must
    /// (a) fail `rows_fit::<i64>` (the dispatch flag), (b) make the i64
    /// tracker decline at construction (never wrap), and (c) still run
    /// end-to-end through the PUBLIC search entry on the i128 path, streaming
    /// only verified incumbents.
    #[test]
    fn huge_coefficients_dispatch_to_i128_and_stay_sound() {
        let huge = 1i128 << 77;
        // Planted-feasible covering system with huge coefficients:
        // huge·x_{2i-1} + huge·x_{2i} >= huge  (a vertex-cover edge, scaled).
        let mut constraints = Vec::new();
        for i in 0..4u32 {
            constraints.push(ge(
                vec![term(huge, lit(2 * i + 1)), term(huge, lit(2 * i + 2))],
                huge,
            ));
        }
        let objective = PbObjective {
            terms: (1..=8u32).map(|v| term(1, lit(v))).collect(),
        };
        let instance = PbInstance {
            num_vars: 8,
            num_constraints: constraints.len() as u32,
            constraints,
            objective: Some(objective.clone()),
        };
        assert!(
            !rows_fit::<i64>(&instance.constraints),
            "dispatch flag must reject huge-coefficient rows"
        );
        assert!(
            Tracker::<i64>::new(&instance, 8, &[false; 8], false).is_none(),
            "the i64 tracker must fail closed on rows it cannot represent"
        );
        assert!(
            Tracker::<i128>::new(&instance, 8, &[false; 8], false).is_some(),
            "the i128 tracker must accept the same rows"
        );

        let stop = no_stop();
        let mut on_improve = |obj: i128, model: &[bool]| {
            assert!(verify_all_constraints(&instance.constraints, model));
            assert_eq!(eval_objective(&objective, model), obj);
        };
        let result = search_with_seeds(
            &instance,
            &objective,
            None,
            &stop,
            &mut on_improve,
            &SlsOptions {
                max_flips: 50_000,
                ..SlsOptions::default()
            },
        )
        .expect("the i128 path must land a verified incumbent");
        assert!(verify_all_constraints(
            &instance.constraints,
            &result.assignment
        ));
        assert_eq!(
            eval_objective(&objective, &result.assignment),
            result.objective
        );
    }

    /// The i64 fast path is a pure throughput lever: on an i64-fitting
    /// instance, `search_loop::<i64>` and `search_loop::<i128>` (forced) must
    /// produce the FULL incumbent stream and final result bit-for-bit
    /// identically — the public dispatch can therefore never change any
    /// default trajectory. Pinned over the full weighting/SCC options matrix
    /// (PAWS and DDFW, each with SCC off and on), so the DDFW/SCC production
    /// worker configuration (`sls-ddfw-opt`) is covered, not just the PAWS
    /// default.
    #[test]
    fn search_loop_i64_and_i128_trajectories_identical() {
        let (instance, objective) =
            vertex_cover_instance(8, &[(1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8)]);
        assert!(rows_fit::<i64>(&instance.constraints));
        for (weighting, scc) in [
            (WeightScheme::Paws, false),
            (WeightScheme::Ddfw, false),
            (WeightScheme::Paws, true),
            (WeightScheme::Ddfw, true),
        ] {
            let run = |wide: bool| {
                let stop = no_stop();
                let mut reported: Vec<(i128, Vec<bool>)> = Vec::new();
                let mut on_improve =
                    |obj: i128, model: &[bool]| reported.push((obj, model.to_vec()));
                let options = SlsOptions {
                    weighting,
                    scc,
                    fast_bump: true,
                    max_flips: 60_000,
                    restarts: true, // cover the reseat path too
                    ..SlsOptions::default()
                };
                let result = if wide {
                    search_loop::<i128>(
                        &instance,
                        &objective,
                        None,
                        &stop,
                        &mut on_improve,
                        &options,
                    )
                } else {
                    search_loop::<i64>(
                        &instance,
                        &objective,
                        None,
                        &stop,
                        &mut on_improve,
                        &options,
                    )
                };
                (reported, result)
            };
            let narrow = run(false);
            let wide = run(true);
            assert!(
                narrow.1.is_some(),
                "the cover must be found ({weighting:?}, scc: {scc})"
            );
            assert_eq!(
                narrow, wide,
                "i64/i128 trajectories diverged ({weighting:?}, scc: {scc}) — the fast path must be value-identical"
            );
        }
    }

    /// Reseat-equivalence differential test for the incremental restart reseat
    /// ([`reseat_assignment`]): after a diff-and-apply reseat onto an arbitrary
    /// target, the tracker's per-row LHS / shortfall, weighted violation, and
    /// violated SET must equal a from-scratch oracle on the same assignment,
    /// and the PAWS weights must persist unchanged. The violated_list ORDER may
    /// legitimately differ from a from-scratch rebuild (a different but equally
    /// valid trajectory), so the violated set is compared sorted.
    #[test]
    fn incremental_reseat_matches_fresh_tracker_oracle() {
        let mut rng = SplitMix64::new(0x7E5E_A700_2026_0710);
        for round in 0..60 {
            let n = 3 + rng.below(8); // 3..=10 vars
            let rows = 2 + rng.below(4); // 2..=5 rows
            let mut constraints = Vec::new();
            for r in 0..rows {
                let k = 2 + rng.below(n - 1);
                let mut terms = Vec::new();
                let mut used = vec![false; n];
                while terms.len() < k {
                    let v = rng.below(n);
                    if used[v] {
                        continue;
                    }
                    used[v] = true;
                    let l = if rng.below(2) == 1 {
                        neg(v as u32 + 1)
                    } else {
                        lit(v as u32 + 1)
                    };
                    terms.push(term(1 + rng.below(5) as i128, l));
                }
                let rhs = rng.below(3 * k) as i128 - k as i128;
                constraints.push(if r % 2 == 0 {
                    eq(terms, rhs)
                } else {
                    ge(terms, rhs)
                });
            }
            let instance = PbInstance {
                num_vars: n as u32,
                num_constraints: rows as u32,
                constraints,
                objective: None,
            };

            let mut assignment: Vec<bool> = (0..n).map(|_| rng.below(2) == 1).collect();
            let mut tracker =
                Tracker::<i128>::new(&instance, n, &assignment, round % 2 == 0).unwrap();

            // Accumulate non-trivial PAWS weights and drift the state around
            // before each reseat, like a real inter-restart trajectory.
            for _ in 0..3 {
                for _ in 0..10 {
                    let v = rng.below(n);
                    let nv = !assignment[v];
                    assignment[v] = nv;
                    tracker.apply_flip(v, nv);
                }
                tracker.bump_violated_weights();

                // Reseat onto a random target (also covers target == current:
                // the diff loop is then a no-op).
                let target: Vec<bool> = if rng.below(4) == 0 {
                    assignment.clone()
                } else {
                    (0..n).map(|_| rng.below(2) == 1).collect()
                };
                let weights_before: Vec<i128> = tracker.states.iter().map(|s| s.weight).collect();
                reseat_assignment(&mut assignment, &target, &mut tracker);
                assert_eq!(assignment, target, "reseat must land exactly on the target");

                // Oracle: from-scratch recompute on the target assignment.
                let fresh = Tracker::<i128>::new(&instance, n, &assignment, false).unwrap();
                let mut oracle_weighted: i128 = 0;
                let mut oracle_violated: Vec<usize> = Vec::new();
                for (ci, c) in instance.constraints.iter().enumerate() {
                    assert_eq!(
                        tracker.states[ci].lhs, fresh.states[ci].lhs,
                        "reseat drifted LHS on row {ci} (round {round})"
                    );
                    assert_eq!(
                        tracker.states[ci].shortfall(),
                        fresh.states[ci].shortfall(),
                        "reseat drifted shortfall on row {ci} (round {round})"
                    );
                    let short = shortfall_for(c.rel, tracker.states[ci].lhs, c.rhs);
                    if short > 0 {
                        oracle_violated.push(ci);
                        oracle_weighted = oracle_weighted
                            .saturating_add(weights_before[ci].saturating_mul(short));
                    }
                }
                assert_eq!(
                    tracker.weighted_violation, oracle_weighted,
                    "reseat drifted weighted violation (round {round})"
                );
                assert_eq!(
                    tracker.total_shortfall, fresh.total_shortfall,
                    "reseat drifted raw total shortfall (round {round})"
                );
                let mut got = tracker.violated_list.clone();
                got.sort_unstable();
                assert_eq!(
                    got, oracle_violated,
                    "reseat drifted violated set (round {round})"
                );
                let weights_after: Vec<i128> = tracker.states.iter().map(|s| s.weight).collect();
                assert_eq!(
                    weights_before, weights_after,
                    "reseat must preserve PAWS weights (round {round})"
                );
            }
        }
    }

    // ---- up_seed (unit-propagation feasibility seed) tests ----

    #[test]
    fn up_seed_fixes_forced_units() {
        // `3 x1 + x2 + x3 >= 4`: max of the free part (x2+x3) is 2, so x1 is forced
        // true in every feasible point (coeff 3 > slack = (3+1+1) - 4 = 1). Also a
        // plain unit `x4 >= 1` forces x4 true.
        let constraints = vec![
            ge(vec![term(3, lit(1)), term(1, lit(2)), term(1, lit(3))], 4),
            ge(vec![term(1, lit(4))], 1),
        ];
        let objective = PbObjective {
            terms: vec![term(1, lit(1)), term(1, lit(4))],
        };
        let instance = PbInstance {
            num_vars: 4,
            num_constraints: constraints.len() as u32,
            constraints,
            objective: Some(objective),
        };
        let seed = up_seed(&instance).expect("forced units exist");
        assert_eq!(seed.len(), 4);
        assert!(seed[0], "x1 must be forced true");
        assert!(seed[3], "x4 must be forced true");
    }

    #[test]
    fn up_seed_propagates_equality_both_directions() {
        // Eq row `x1 + x2 = 0` forces BOTH x1 and x2 false (the `<=` direction).
        let constraints = vec![eq(vec![term(1, lit(1)), term(1, lit(2))], 0)];
        let objective = PbObjective {
            terms: vec![term(1, lit(1))],
        };
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints,
            objective: Some(objective),
        };
        let seed = up_seed(&instance).expect("equality forces both vars false");
        assert_eq!(seed, vec![false, false]);
    }

    #[test]
    fn up_seed_none_when_nothing_forced() {
        // A market-split-style equality with slack on both sides forces nothing, so
        // up_seed declines (None) rather than fabricating a seed.
        let constraints = vec![eq(
            vec![
                term(3, lit(1)),
                term(3, lit(2)),
                term(3, lit(3)),
                term(3, lit(4)),
            ],
            6,
        )];
        let objective = PbObjective {
            terms: vec![term(1, lit(1))],
        };
        let instance = PbInstance {
            num_vars: 4,
            num_constraints: 1,
            constraints,
            objective: Some(objective),
        };
        assert!(up_seed(&instance).is_none());
    }

    // ---- Layered-restart (design §3.1) tests ----

    #[test]
    fn restart_scheduler_fires_on_stagnation_and_cycles_layers() {
        // With external seeds the cycle is biased-random → best-incumbent →
        // external-seed → repeat; without seeds the third layer is skipped.
        let seeds: Vec<Vec<bool>> = vec![vec![true, false, true]];
        let mut rs = RestartState::new(&seeds, RESTART_DWELL_THRESHOLD);

        // Raw total shortfall held constant throughout: only the count/incumbent
        // signals drive this test (the shortfall signal has its own test).
        rs.note_step(5, 10, false); // first observation: new min => progress
        for _ in 0..RESTART_DWELL_THRESHOLD - 1 {
            rs.note_step(5, 10, false);
        }
        assert!(!rs.should_fire(), "must not fire below the dwell threshold");
        rs.note_step(4, 10, false); // new minimum violated-count => progress => reset
        for _ in 0..RESTART_DWELL_THRESHOLD - 1 {
            rs.note_step(4, 10, false);
        }
        assert!(
            !rs.should_fire(),
            "feasibility progress must reset the dwell counter"
        );
        rs.note_step(4, 10, true); // a new best incumbent also resets the counter
        for _ in 0..RESTART_DWELL_THRESHOLD - 1 {
            rs.note_step(4, 10, false);
        }
        assert!(
            !rs.should_fire(),
            "incumbent progress must reset the dwell counter"
        );
        rs.note_step(4, 10, false);
        assert!(
            rs.should_fire(),
            "dwell threshold reached: restart must fire"
        );

        // Layer cycling, in order; begin_restart consumes the stagnation event.
        assert_eq!(rs.begin_restart(), RestartLayer::BiasedRandom);
        assert!(
            !rs.should_fire(),
            "begin_restart must reset the dwell counter"
        );
        // GEOMETRIC DWELL GROWTH: after one fired restart the dwell is
        // RESTART_DWELL_GROWTH x the base, so the base dwell's worth of
        // stagnation no longer fires...
        for _ in 0..=RESTART_DWELL_THRESHOLD {
            rs.note_step(4, 10, false);
        }
        assert!(
            !rs.should_fire(),
            "after a restart the dwell must have grown by RESTART_DWELL_GROWTH"
        );
        // ...and the grown dwell fires only at GROWTH x the base stagnation.
        for _ in 0..RESTART_DWELL_THRESHOLD * (RESTART_DWELL_GROWTH - 1) {
            rs.note_step(4, 10, false);
        }
        assert!(
            rs.should_fire(),
            "the grown dwell must fire at RESTART_DWELL_GROWTH x the base dwell"
        );
        assert_eq!(rs.begin_restart(), RestartLayer::BestIncumbent);
        assert_eq!(rs.begin_restart(), RestartLayer::ExternalSeed);
        assert_eq!(rs.begin_restart(), RestartLayer::BiasedRandom);

        // Without seeds: the external layer never appears in the cycle.
        let mut rs2 = RestartState::new(&[], RESTART_DWELL_THRESHOLD);
        assert_eq!(rs2.begin_restart(), RestartLayer::BiasedRandom);
        assert_eq!(rs2.begin_restart(), RestartLayer::BestIncumbent);
        assert_eq!(rs2.begin_restart(), RestartLayer::BiasedRandom);
    }

    /// The third progress signal (raw total shortfall): an Eq-heavy grind whose
    /// violated-row COUNT plateaus but whose total shortfall still improves
    /// steadily must NOT fire a restart (measured losses without this signal:
    /// j120opt SAT→UNKNOWN, hw128 o 43→48 — a BiasedRandom scramble destroying
    /// a converging trajectory), while a genuinely FLATLINED hunt — no new
    /// minimum in count OR shortfall — must still fire at the dwell (the
    /// SMTI-class rescue).
    #[test]
    fn restart_shortfall_progress_holds_dwell_but_flatline_still_fires() {
        let mut rs = RestartState::new(&[], RESTART_DWELL_THRESHOLD);

        // Converging grind: count stuck at 3 for 3x the dwell, shortfall makes
        // a new minimum every step. Never fires.
        let mut shortfall: i128 = 3_000_000;
        rs.note_step(3, shortfall, false);
        for _ in 0..RESTART_DWELL_THRESHOLD * 3 {
            shortfall -= 1;
            rs.note_step(3, shortfall, false);
            assert!(
                !rs.should_fire(),
                "steady shortfall improvement is progress: the dwell must not fire"
            );
        }

        // Slow grind: a new shortfall minimum only every 1000 steps still
        // holds the dwell (stagnation peaks far below the threshold).
        for _ in 0..100 {
            for _ in 0..999 {
                rs.note_step(3, shortfall, false); // no new minimum
            }
            shortfall -= 1;
            rs.note_step(3, shortfall, false); // new minimum: resets
            assert!(!rs.should_fire());
        }

        // Flatline: count stuck AND shortfall only oscillating ABOVE its
        // minimum (no new minimum in either signal) => genuine stagnation, the
        // dwell must fire after exactly `dwell` progress-free steps.
        for i in 0..RESTART_DWELL_THRESHOLD {
            assert!(
                !rs.should_fire(),
                "must not fire before the dwell threshold"
            );
            let bounce = if i % 2 == 0 { 5 } else { 3 }; // > min, never a new min
            rs.note_step(3, shortfall + bounce, false);
        }
        assert!(
            rs.should_fire(),
            "a flatlined hunt (no new min in count or shortfall) must still fire"
        );

        // begin_restart resets the shortfall watermark like min_violated: the
        // stale minimum from before the restart is forgotten, so the first
        // post-restart observation counts as progress again.
        rs.begin_restart();
        rs.note_step(3, i128::MAX - 1, false); // far above the old minimum
        assert!(!rs.should_fire());
        assert_eq!(
            rs.stagnant, 0,
            "post-restart first observation must be progress"
        );
    }

    /// Pre-feasibility locality-preserving kick: with NO best incumbent the
    /// BiasedRandom layer must anchor on the CURRENT assignment — keeping each
    /// variable with probability [`RESTART_BIAS_KEEP_PERMILLE`]/1000 and
    /// flipping the rest — NOT draw a uniform scramble. A uniform target
    /// differs from the current point in ~n/2 variables and repeatedly resets
    /// a whole-budget feasibility grind (the j120 / benchsMusee / hw128 loss
    /// mode); the local kick differs in ~(1000−KEEP)‰.
    #[test]
    fn pre_feasibility_biased_random_kick_is_local_to_current() {
        let n = 4000usize;
        let current: Vec<bool> = (0..n).map(|v| v % 3 == 0).collect();
        let mut rs = RestartState::new(&[], RESTART_DWELL_THRESHOLD);
        let mut rng = SplitMix64::new(0x10CA_1517_2026_0710);
        let mut target = vec![false; n];
        rs.fill_restart_target(
            RestartLayer::BiasedRandom,
            &mut target,
            &current,
            None,
            &mut rng,
        );

        // Expected flips: (1000 − KEEP)‰ of n = 400 at the shipped 900‰. The
        // seed is deterministic; [expected/2, 2×expected] = [200, 800] is a
        // generous band, and a uniform scramble (~n/2 = 2000) is far outside.
        let dist = target.iter().zip(&current).filter(|(a, b)| a != b).count();
        let expected = n * usize::try_from(1000 - RESTART_BIAS_KEEP_PERMILLE).unwrap() / 1000;
        assert!(
            dist >= expected / 2 && dist <= expected * 2,
            "pre-feasibility kick must flip ~(1000-KEEP)permille of vars: \
             dist={dist}, expected~{expected}"
        );
        assert!(
            dist < n / 4,
            "pre-feasibility kick must not be a uniform scramble: dist={dist}"
        );

        // With a best incumbent the layer anchors on BEST exactly as before,
        // ignoring the current point (current and best differ in ~38% of vars
        // here, so an accidental current-anchor would land far outside the
        // band around best).
        let best_anchor: Vec<bool> = (0..n).map(|v| v % 7 == 0).collect();
        rs.fill_restart_target(
            RestartLayer::BiasedRandom,
            &mut target,
            &current,
            Some(&best_anchor),
            &mut rng,
        );
        let dist_best = target
            .iter()
            .zip(&best_anchor)
            .filter(|(a, b)| a != b)
            .count();
        assert!(
            dist_best >= expected / 2 && dist_best <= expected * 2,
            "with an incumbent the kick must anchor on best: dist={dist_best}, expected~{expected}"
        );

        // The BestIncumbent layer's no-incumbent fallback uses the same local
        // kick (no uniform scramble anywhere pre-feasibility).
        rs.fill_restart_target(
            RestartLayer::BestIncumbent,
            &mut target,
            &current,
            None,
            &mut rng,
        );
        let dist_fallback = target.iter().zip(&current).filter(|(a, b)| a != b).count();
        assert!(
            dist_fallback >= expected / 2 && dist_fallback <= expected * 2,
            "BestIncumbent fallback must use the local current-anchored kick: dist={dist_fallback}"
        );
    }

    #[test]
    fn best_incumbent_restart_restores_feasibility_instantly() {
        // Reseating the tracker AT the best feasible incumbent restores
        // feasibility with zero search steps, and the PAWS weights learned
        // before the restart persist across it (the standard PAWS choice).
        let (instance, _objective) =
            vertex_cover_instance(6, &[(1, 2), (2, 3), (3, 4), (4, 5), (5, 6)]);
        let n = 6usize;
        let incumbent = vec![true; n]; // the all-true cover is feasible
        assert!(verify_all_constraints(&instance.constraints, &incumbent));

        // Start from all-false (every edge violated) and bump weights so the
        // learned weights are distinguishable from the initial all-1s.
        let mut assignment = vec![false; n];
        let mut tracker = Tracker::<i128>::new(&instance, n, &assignment, false).unwrap();
        assert!(tracker.num_violated() > 0);
        for _ in 0..3 {
            tracker.bump_violated_weights();
        }
        let weights_before: Vec<i128> = tracker.states.iter().map(|s| s.weight).collect();
        assert!(weights_before.iter().any(|&w| w > 1));

        reseat_assignment(&mut assignment, &incumbent, &mut tracker);
        assert_eq!(assignment, incumbent);
        assert_eq!(
            tracker.num_violated(),
            0,
            "best-incumbent reseat must be instantly feasible"
        );
        assert_eq!(tracker.weighted_violation, 0);
        let weights_after: Vec<i128> = tracker.states.iter().map(|s| s.weight).collect();
        assert_eq!(
            weights_before, weights_after,
            "PAWS weights must persist across restarts"
        );

        // The BestIncumbent layer's target stays within the small perturbation
        // radius of the incumbent (restart AT the incumbent + small kicks).
        let mut rs = RestartState::new(&[], RESTART_DWELL_THRESHOLD);
        let mut rng = SplitMix64::new(42);
        let mut target = vec![false; n];
        rs.fill_restart_target(
            RestartLayer::BestIncumbent,
            &mut target,
            &assignment,
            Some(&incumbent),
            &mut rng,
        );
        let dist = target
            .iter()
            .zip(&incumbent)
            .filter(|(a, b)| a != b)
            .count();
        assert!(
            dist <= RESTART_INTENSIFY_KICKS,
            "intensification kicked too far from the incumbent: {dist}"
        );
    }

    #[test]
    fn external_seed_restart_layer_is_used_when_provided() {
        // A planted 4x30 market-split system (Σ_j w_ij x_j = Σ_j w_ij p_j):
        // random search cannot reach feasibility within the flip budget, so an
        // incumbent can only come from the externally-provided seed point
        // (design §3.1's third restart layer). Fully deterministic: structural
        // PRNG seed, fixed flip cap, no wall-clock deadline.
        let mut wrng = SplitMix64::new(0xC0DE_D00D_2026_0710);
        let n = 30usize;
        let m = 4usize;
        let planted: Vec<bool> = (0..n).map(|j| j % 3 == 0).collect();
        let mut constraints = Vec::new();
        for _ in 0..m {
            let weights: Vec<i128> = (0..n).map(|_| 1 + wrng.below(99) as i128).collect();
            let rhs: i128 = weights
                .iter()
                .zip(&planted)
                .filter(|(_, &p)| p)
                .map(|(&w, _)| w)
                .sum();
            constraints.push(eq(
                weights
                    .iter()
                    .enumerate()
                    .map(|(j, &w)| term(w, lit(j as u32 + 1)))
                    .collect(),
                rhs,
            ));
        }
        let objective = PbObjective {
            terms: (1..=n as u32).map(|v| term(1, lit(v))).collect(),
        };
        let instance = PbInstance {
            num_vars: n as u32,
            num_constraints: m as u32,
            constraints,
            objective: Some(objective.clone()),
        };
        assert!(verify_all_constraints(&instance.constraints, &planted));
        let planted_obj = eval_objective(&objective, &planted);

        let stop = no_stop();
        // Room for >= 3 restarts under GEOMETRIC dwell growth: the third
        // (ExternalSeed) restart needs (1 + G + G^2) x dwell = 21 x dwell of
        // cumulative stagnation (20k + 80k + 320k at G = 4), PLUS the
        // post-restart transients where the reset min-violated/min-shortfall
        // watermarks keep absorbing steps as progress (measured on this
        // instance: the seed lands from ~36 x dwell; 48 x leaves margin).
        let budget = RESTART_DWELL_THRESHOLD * 48;

        // Without seeds (restarts on): the flip budget is nowhere near enough
        // for the wall.
        let mut noop = |_o: i128, _m: &[bool]| {};
        let without = search_with_seeds(
            &instance,
            &objective,
            None,
            &stop,
            &mut noop,
            &SlsOptions {
                fast_bump: true,
                max_flips: budget,
                restarts: true,
                ..SlsOptions::default()
            },
        );
        assert!(
            without.is_none(),
            "market-split wall unexpectedly cracked without the seed"
        );

        // With seeds — a wrong-length decoy first (must be SKIPPED, never
        // truncated/padded), then the planted point: the ExternalSeed layer
        // fires on the third restart and lands the verified incumbent.
        let seeds: Vec<Vec<bool>> = vec![vec![true; n - 1], planted.clone()];
        let mut reported = Vec::new();
        let mut on_improve = |obj: i128, model: &[bool]| {
            assert!(verify_all_constraints(&instance.constraints, model));
            reported.push(obj);
        };
        let with = search_with_seeds(
            &instance,
            &objective,
            None,
            &stop,
            &mut on_improve,
            &SlsOptions {
                fast_bump: true,
                max_flips: budget,
                external_seeds: &seeds,
                restarts: true,
                ..SlsOptions::default()
            },
        )
        .expect("external seed layer must land the planted incumbent");
        assert!(verify_all_constraints(
            &instance.constraints,
            &with.assignment
        ));
        assert_eq!(eval_objective(&objective, &with.assignment), with.objective);
        assert!(
            with.objective <= planted_obj,
            "incumbent must be at least as good as the planted seed"
        );
        assert!(!reported.is_empty());
    }

    #[test]
    fn restart_search_deterministic_per_seed() {
        // The layered restarts draw all randomness from the structurally-seeded
        // PRNG: two identical runs (fixed flip cap, no wall-clock deadline) must
        // produce bit-identical results even across several restart cycles.
        let run = || {
            let (instance, objective) =
                vertex_cover_instance(6, &[(1, 2), (2, 3), (3, 4), (4, 5), (5, 6)]);
            let stop = no_stop();
            let mut noop = |_o: i128, _m: &[bool]| {};
            search_with_seeds(
                &instance,
                &objective,
                None,
                &stop,
                &mut noop,
                &SlsOptions {
                    fast_bump: true,
                    // Spans the first restart and deep into the grown second
                    // dwell (geometric growth: 20k, then 80k).
                    max_flips: RESTART_DWELL_THRESHOLD * 7,
                    restarts: true,
                    ..SlsOptions::default()
                },
            )
        };
        let a = run();
        let b = run();
        assert!(a.is_some(), "the path cover must be found");
        assert_eq!(a, b, "restart trajectory not deterministic per seed");
    }

    /// Restarts are the diversified-worker arm (design §2.3) and DEFAULT OFF:
    /// (a) default-constructed options produce a trajectory bit-identical to
    /// an explicit `restarts: false` run — the scheduler is inert unless a
    /// worker opts in — even on budgets where restarts WOULD fire if enabled;
    /// (b) non-vacuity: on the planted market-split wall with external seeds,
    /// a `restarts: true` run lands the planted incumbent via the ExternalSeed
    /// layer while the DEFAULT run stays empty-handed — the flag is
    /// load-bearing, so (a) is not comparing two no-op configs.
    #[test]
    fn restarts_default_off_matches_disabled_run() {
        // (a) Bit-for-bit: full incumbent stream + final result.
        let (instance, objective) =
            vertex_cover_instance(6, &[(1, 2), (2, 3), (3, 4), (4, 5), (5, 6)]);
        let run = |restarts_explicit: Option<bool>| {
            let stop = no_stop();
            let mut reported: Vec<(i128, Vec<bool>)> = Vec::new();
            let mut on_improve = |obj: i128, model: &[bool]| reported.push((obj, model.to_vec()));
            let result = search_with_seeds(
                &instance,
                &objective,
                None,
                &stop,
                &mut on_improve,
                &SlsOptions {
                    fast_bump: true,
                    // Well past the base dwell: restarts WOULD fire if enabled.
                    max_flips: RESTART_DWELL_THRESHOLD * 3,
                    restarts: restarts_explicit.unwrap_or(SlsOptions::default().restarts),
                    ..SlsOptions::default()
                },
            );
            (reported, result)
        };
        let default_run = run(None);
        let disabled_run = run(Some(false));
        assert!(
            !SlsOptions::default().restarts,
            "restarts must be OFF by default (single-trajectory prime directive)"
        );
        assert_eq!(
            default_run, disabled_run,
            "default options must reproduce the restart-disabled trajectory bit-for-bit"
        );

        // (b) Non-vacuity on the planted 4x30 market-split wall (same shape as
        // `external_seed_restart_layer_is_used_when_provided`).
        let mut wrng = SplitMix64::new(0xC0DE_D00D_2026_0710);
        let n = 30usize;
        let m = 4usize;
        let planted: Vec<bool> = (0..n).map(|j| j % 3 == 0).collect();
        let mut constraints = Vec::new();
        for _ in 0..m {
            let weights: Vec<i128> = (0..n).map(|_| 1 + wrng.below(99) as i128).collect();
            let rhs: i128 = weights
                .iter()
                .zip(&planted)
                .filter(|(_, &p)| p)
                .map(|(&w, _)| w)
                .sum();
            constraints.push(eq(
                weights
                    .iter()
                    .enumerate()
                    .map(|(j, &w)| term(w, lit(j as u32 + 1)))
                    .collect(),
                rhs,
            ));
        }
        let objective_ms = PbObjective {
            terms: (1..=n as u32).map(|v| term(1, lit(v))).collect(),
        };
        let instance_ms = PbInstance {
            num_vars: n as u32,
            num_constraints: m as u32,
            constraints,
            objective: Some(objective_ms.clone()),
        };
        let seeds: Vec<Vec<bool>> = vec![planted.clone()];
        let budget = RESTART_DWELL_THRESHOLD * 48; // past the third restart
        let run_wall = |restarts: bool| {
            let stop = no_stop();
            let mut noop = |_o: i128, _m: &[bool]| {};
            search_with_seeds(
                &instance_ms,
                &objective_ms,
                None,
                &stop,
                &mut noop,
                &SlsOptions {
                    fast_bump: true,
                    max_flips: budget,
                    external_seeds: &seeds,
                    restarts,
                    ..SlsOptions::default()
                },
            )
        };
        let with_restarts = run_wall(true);
        let default_off = run_wall(false);
        assert!(
            with_restarts.is_some(),
            "restarts-on must land the planted incumbent via the seed layer"
        );
        assert!(
            default_off.is_none(),
            "with restarts off (the default) the seed layer must be inert"
        );
        assert_ne!(
            with_restarts, default_off,
            "the restarts flag must be load-bearing (non-vacuity for part (a))"
        );
    }

    /// Regression test for the lost threshold-crossing incumbent: when the very
    /// flip that crosses the restart dwell threshold lands on a feasible,
    /// strictly improving assignment, the fired restart must record it (via
    /// `on_improve`) BEFORE the reseat overwrites the assignment — the search
    /// loop's feasible-branch record only runs on the NEXT iteration, which the
    /// restart preempts. This drives [`fire_restart`] — the exact block the
    /// search loop runs on `should_fire()` — directly and deterministically:
    /// the scheduler is walked to the threshold precisely as the loop's
    /// `note_step` would, so the whole scenario is RNG- and wall-clock-free up
    /// to the recording (which draws no RNG by design).
    ///
    /// (An end-to-end plant of this coincidence through `search_with_seeds`
    /// needs the improving repair flip to land on EXACTLY the dwell-crossing
    /// iteration; a 4500-run deterministic sweep over vertex-cover and
    /// market-split families found no organic hit, so the block is pinned at
    /// the unit level instead — same code path, no trajectory brittleness.)
    #[test]
    fn restart_records_threshold_crossing_feasible_improvement() {
        let (instance, objective) =
            vertex_cover_instance(6, &[(1, 2), (2, 3), (3, 4), (4, 5), (5, 6)]);
        let n = 6usize;

        // Current best: the all-true cover (objective 6).
        let worst = vec![true; n];
        assert!(verify_all_constraints(&instance.constraints, &worst));
        let mut best = Some(SlsResult {
            assignment: worst,
            objective: 6,
        });

        // The threshold-crossing flip landed on a strictly better feasible
        // cover {2, 4, 6} (objective 3), not yet recorded.
        let mut assignment = vec![false, true, false, true, false, true];
        assert!(verify_all_constraints(&instance.constraints, &assignment));
        let mut tracker = Tracker::<i128>::new(&instance, n, &assignment, false).unwrap();
        assert_eq!(tracker.num_violated(), 0);

        // Walk the scheduler to the threshold exactly as the search loop's
        // note_step calls would: feasible (num_violated 0), no new best.
        let mut restart = RestartState::new(&[], RESTART_DWELL_THRESHOLD);
        restart.note_step(0, 0, false); // first observation: new min => progress
        for _ in 0..RESTART_DWELL_THRESHOLD {
            restart.note_step(0, 0, false);
        }
        assert!(restart.should_fire());

        let mut rng = SplitMix64::new(0xD3AD_2026_0710_0001);
        let mut scratch = vec![false; n];
        let mut reported: Vec<(i128, Vec<bool>)> = Vec::new();
        {
            let mut on_improve = |obj: i128, model: &[bool]| {
                assert!(verify_all_constraints(&instance.constraints, model));
                reported.push((obj, model.to_vec()));
            };
            let stop = no_stop();
            fire_restart(
                &instance,
                &objective,
                &mut restart,
                &mut assignment,
                &mut scratch,
                &mut tracker,
                &mut best,
                &mut rng,
                &mut on_improve,
                &stop,
            );
        }

        // on_improve fired for the crossing incumbent BEFORE the restart
        // overwrote it, and `best` was advanced to it.
        assert_eq!(
            reported,
            vec![(3, vec![false, true, false, true, false, true])],
            "the threshold-crossing feasible improvement must be recorded before the reseat"
        );
        assert_eq!(best.as_ref().map(|b| b.objective), Some(3));

        // The restart itself still happened: dwell bookkeeping consumed and the
        // search re-seated exactly on the layer target, with the tracker state
        // matching a from-scratch oracle on that target.
        assert!(!restart.should_fire());
        assert_eq!(assignment, scratch);
        let fresh = Tracker::<i128>::new(&instance, n, &assignment, false).unwrap();
        let inc: Vec<i128> = tracker.states.iter().map(|s| s.lhs).collect();
        let oracle: Vec<i128> = fresh.states.iter().map(|s| s.lhs).collect();
        assert_eq!(
            inc, oracle,
            "reseat after the record drifted from the oracle"
        );

        // Control (non-vacuity): an INFEASIBLE crossing state records nothing —
        // the record is gated on num_violated() == 0.
        let mut infeasible = vec![false; n];
        let mut tracker2 = Tracker::<i128>::new(&instance, n, &infeasible, false).unwrap();
        assert!(tracker2.num_violated() > 0);
        let mut restart2 = RestartState::new(&[], RESTART_DWELL_THRESHOLD);
        for _ in 0..=RESTART_DWELL_THRESHOLD {
            restart2.note_step(1, 1, false);
        }
        assert!(restart2.should_fire());
        let mut reported2 = 0usize;
        {
            let mut on_improve = |_obj: i128, _model: &[bool]| reported2 += 1;
            let stop = no_stop();
            fire_restart(
                &instance,
                &objective,
                &mut restart2,
                &mut infeasible,
                &mut scratch,
                &mut tracker2,
                &mut best,
                &mut rng,
                &mut on_improve,
                &stop,
            );
        }
        assert_eq!(
            reported2, 0,
            "an infeasible crossing state must not be recorded"
        );
    }

    // ---- DDFW weight-transfer + SCC (design §2.2) tests ----

    /// Deterministic unit pin of the DDFW donor rules
    /// ([`Tracker::ddfw_transfer_weights`]): max-weight satisfied neighbor
    /// donates, ties break to the smallest row index, the transferred amount
    /// is half the spare above the floor (at least 1), and a violated row
    /// with no eligible donor falls back to the PAWS additive `+1`.
    #[test]
    fn ddfw_transfer_picks_max_weight_satisfied_neighbor() {
        // Row 0: x1 >= 1 (violated under all-false). Rows 1/2: satisfied
        // under all-false (negated literals), sharing x1 with row 0.
        let constraints = vec![
            ge(vec![term(1, lit(1))], 1),
            ge(vec![term(1, neg(1)), term(1, lit(2))], 1),
            ge(vec![term(1, neg(1)), term(1, lit(3))], 1),
        ];
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 3,
            constraints,
            objective: None,
        };
        let build = || {
            let assignment = vec![false; 3];
            let mut tracker = Tracker::<i128>::new(&instance, 3, &assignment, false).unwrap();
            tracker.build_row_members();
            assert_eq!(tracker.violated_list, vec![0]);
            tracker
        };

        // Max-weight donor wins: row 2 (weight 9) over row 1 (weight 5).
        // Transfer = (9 - floor) / 2 = 4.
        let mut t = build();
        t.states[1].weight = 5;
        t.states[2].weight = 9;
        let fallbacks = t.ddfw_transfer_weights();
        assert_eq!(fallbacks, 0);
        assert_eq!(t.states[0].weight, 1 + 4, "receiver must gain the transfer");
        assert_eq!(t.states[1].weight, 5, "non-donor must be untouched");
        assert_eq!(t.states[2].weight, 9 - 4, "donor must give half its spare");
        assert_eq!(
            t.weighted_violation, 5,
            "weighted violation must track the receiver's new weight"
        );

        // Equal weights: the tie breaks to the SMALLEST row index (row 1).
        let mut t = build();
        t.states[1].weight = 9;
        t.states[2].weight = 9;
        assert_eq!(t.ddfw_transfer_weights(), 0);
        assert_eq!(
            t.states[1].weight,
            9 - 4,
            "tie must go to the smaller index"
        );
        assert_eq!(t.states[2].weight, 9);

        // Donor with spare exactly 1 still donates 1 (the `.max(1)`).
        let mut t = build();
        t.states[2].weight = 2;
        assert_eq!(t.ddfw_transfer_weights(), 0);
        assert_eq!(
            t.states[2].weight, DDFW_WEIGHT_FLOOR,
            "donor drained to the floor"
        );
        assert_eq!(t.states[0].weight, 2);

        // No donor with spare (all neighbors at the floor): additive fallback.
        let mut t = build();
        let before: i128 = t.states.iter().map(|s| s.weight).sum();
        assert_eq!(t.ddfw_transfer_weights(), 1, "one fallback bump expected");
        let after: i128 = t.states.iter().map(|s| s.weight).sum();
        assert_eq!(
            t.states[0].weight, 2,
            "fallback must bump the violated row by 1"
        );
        assert_eq!(
            after,
            before + 1,
            "total weight grows exactly by the fallback"
        );
    }

    /// DDFW conservation invariant (design §2.2) over random runs: across
    /// random Eq/Ge instances with negated literals and arbitrary flip
    /// sequences interleaved with transfer sweeps,
    /// `Σ weight (after) = Σ weight (before) + fallback count`, no weight ever
    /// drops below [`DDFW_WEIGHT_FLOOR`], and the incrementally-maintained
    /// `weighted_violation` still equals the from-scratch oracle after every
    /// sweep (the transfer path preserves the tracker-exactness the steering
    /// relies on).
    #[test]
    fn ddfw_transfer_conserves_total_weight_within_floor_rules() {
        let mut rng = SplitMix64::new(0xDDF3_2026_0710_0001);
        for round in 0..40 {
            let n = 3 + rng.below(7); // 3..=9 vars
            let rows = 2 + rng.below(4); // 2..=5 rows
            let mut constraints = Vec::new();
            for r in 0..rows {
                let k = 2 + rng.below(n - 1);
                let mut terms = Vec::new();
                let mut used = vec![false; n];
                while terms.len() < k {
                    let v = rng.below(n);
                    if used[v] {
                        continue;
                    }
                    used[v] = true;
                    let l = if rng.below(2) == 1 {
                        neg(v as u32 + 1)
                    } else {
                        lit(v as u32 + 1)
                    };
                    terms.push(term(1 + rng.below(5) as i128, l));
                }
                let rhs = rng.below(3 * k) as i128 - k as i128;
                constraints.push(if r % 2 == 0 {
                    eq(terms, rhs)
                } else {
                    ge(terms, rhs)
                });
            }
            let instance = PbInstance {
                num_vars: n as u32,
                num_constraints: rows as u32,
                constraints,
                objective: None,
            };

            let mut assignment: Vec<bool> = (0..n).map(|_| rng.below(2) == 1).collect();
            let mut tracker =
                Tracker::<i128>::new(&instance, n, &assignment, round % 2 == 0).unwrap();
            tracker.build_row_members();

            for step in 0..200 {
                if step % 5 == 0 {
                    let before: i128 = tracker.states.iter().map(|s| s.weight).sum();
                    let fallbacks = tracker.ddfw_transfer_weights() as i128;
                    let after: i128 = tracker.states.iter().map(|s| s.weight).sum();
                    assert_eq!(
                        after,
                        before + fallbacks,
                        "transfer must conserve total weight modulo fallbacks \
                         (round {round}, step {step})"
                    );
                    assert!(
                        tracker.states.iter().all(|s| s.weight >= DDFW_WEIGHT_FLOOR),
                        "a donor dropped below the weight floor (round {round}, step {step})"
                    );
                } else {
                    let v = rng.below(n);
                    let nv = !assignment[v];
                    assignment[v] = nv;
                    tracker.apply_flip(v, nv);
                }
                // Differential oracle: weighted violation recomputed from the
                // ORIGINAL rows under the current assignment and weights.
                let mut oracle: i128 = 0;
                for (ci, c) in instance.constraints.iter().enumerate() {
                    let short = shortfall_for(c.rel, oracle_row_lhs(c, &assignment), c.rhs);
                    assert_eq!(
                        tracker.states[ci].shortfall(),
                        short,
                        "transfer must never touch a row's LHS/shortfall \
                         (round {round}, step {step})"
                    );
                    if short > 0 {
                        oracle =
                            oracle.saturating_add(tracker.states[ci].weight.saturating_mul(short));
                    }
                }
                assert_eq!(
                    tracker.weighted_violation, oracle,
                    "weighted-violation drift under DDFW (round {round}, step {step})"
                );
            }
        }
    }

    /// SCC configuration-bit semantics ([`Tracker::scc_mark_flip`] /
    /// [`Tracker::scc_smooth`]): a variable is configuration-changed iff a
    /// NEIGHBOR (sharing a constraint) flipped since it last flipped; a flip
    /// clears the flipped variable's own bit; non-neighbors are untouched;
    /// smoothing re-enables a bounded random fraction; and with SCC off every
    /// variable is unconditionally eligible.
    #[test]
    fn scc_bits_track_neighbor_flips_and_smooth() {
        // Path structure: rows {x1,x2} and {x2,x3} — x1 and x3 are NOT
        // neighbors of each other; x2 neighbors both.
        let constraints = vec![
            ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
            ge(vec![term(1, lit(2)), term(1, lit(3))], 1),
        ];
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 2,
            constraints,
            objective: None,
        };
        let mut assignment = vec![false; 3];
        let mut tracker = Tracker::<i128>::new(&instance, 3, &assignment, false).unwrap();

        // SCC off: everything is eligible, and flips keep it that way.
        assert!((0..3).all(|v| tracker.scc_eligible(v)));
        assignment[0] = true;
        tracker.apply_flip(0, true);
        assert!((0..3).all(|v| tracker.scc_eligible(v)));
        assignment[0] = false;
        tracker.apply_flip(0, false);

        tracker.build_row_members();
        tracker.enable_scc();
        // Standard CC init: every variable starts configuration-changed.
        assert!((0..3).all(|v| tracker.scc_eligible(v)));

        // Flip x3 (idx 2): clears its own bit, marks its row-1 neighbor x2.
        assignment[2] = true;
        tracker.apply_flip(2, true);
        assert!(
            !tracker.scc_eligible(2),
            "a flipped var must become UNchanged"
        );

        // Flip x1 (idx 0): marks row-0 members {x1,x2}, then clears x1. x3 is
        // NOT a neighbor of x1 and must stay unchanged.
        assignment[0] = true;
        tracker.apply_flip(0, true);
        assert!(!tracker.scc_eligible(0));
        assert!(
            tracker.scc_eligible(1),
            "x2 neighbors x1: must be re-enabled"
        );
        assert!(
            !tracker.scc_eligible(2),
            "x3 does not share a row with x1: its bit must be untouched"
        );

        // Flip x2 (idx 1): neighbors {x1, x3} become changed, x2 clears.
        assignment[1] = true;
        tracker.apply_flip(1, true);
        assert!(tracker.scc_eligible(0));
        assert!(!tracker.scc_eligible(1));
        assert!(tracker.scc_eligible(2));

        // Smoothing: from an all-false state, exactly max(1, n/64) = 1 random
        // bit per event is re-enabled (deterministic per seed).
        for b in tracker.scc_bits.as_mut().unwrap().iter_mut() {
            *b = false;
        }
        let mut rng = SplitMix64::new(0x5CC5_2026_0710_0002);
        tracker.scc_smooth(&mut rng);
        let enabled = tracker
            .scc_bits
            .as_ref()
            .unwrap()
            .iter()
            .filter(|&&b| b)
            .count();
        assert_eq!(
            enabled, 1,
            "smoothing must re-enable max(1, n/64) variables"
        );
    }

    /// SCC greedy-eligibility fallback in [`feasibility_step`]: when EVERY
    /// candidate in the picked violated row is configuration-unchanged, the
    /// step must fall back to the noise pick (still flipping SOMETHING from
    /// the row) rather than stalling — and the flip re-marks the flipped
    /// variable's neighbors as changed.
    #[test]
    fn scc_all_ineligible_falls_back_to_noise_pick() {
        let constraints = vec![ge(vec![term(1, lit(1)), term(1, lit(2))], 1)];
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints,
            objective: None,
        };
        let mut assignment = vec![false; 2];
        let mut tracker = Tracker::<i128>::new(&instance, 2, &assignment, false).unwrap();
        tracker.build_row_members();
        tracker.enable_scc();
        for b in tracker.scc_bits.as_mut().unwrap().iter_mut() {
            *b = false; // force the all-ineligible endgame of the CC tabu
        }
        let mut rng = SplitMix64::new(0x5CC5_2026_0710_0003);
        let mut stale = 0u64;
        feasibility_step(
            &instance,
            &mut assignment,
            &mut tracker,
            &mut rng,
            &mut stale,
            0,
            WeightScheme::Paws,
        );
        let flipped: Vec<usize> = (0..2).filter(|&v| assignment[v]).collect();
        assert_eq!(flipped.len(), 1, "the fallback must still flip one row var");
        let v = flipped[0];
        assert!(!tracker.scc_eligible(v), "the flipped var's own bit clears");
        assert!(
            tracker.scc_eligible(1 - v),
            "the flipped var's neighbor must be configuration-changed again"
        );
        assert_eq!(tracker.num_violated(), 0, "the row is satisfied either way");
    }

    /// Standing soundness fuzz extended to BOTH §2.2 schemes: across random
    /// covering and planted-equality instances, DDFW- and SCC-enabled runs
    /// (and the combined arm) must stream only verified, exactly-valued,
    /// strictly-improving incumbents — the same zero-wrong bar as the default
    /// PAWS trajectory. Deterministic: fixed flip caps, no wall clock.
    #[test]
    fn ddfw_scc_never_report_infeasible_or_nonimproving_fuzz() {
        let mut rng = SplitMix64::new(0xF022_2026_0710_0D0F);
        for iter in 0..18 {
            let (instance, objective) = if iter % 2 == 0 {
                let num_vertices = 4 + rng.below(9) as u32;
                let edge_count = 3 + rng.below(12);
                let mut edges = Vec::new();
                for _ in 0..edge_count {
                    let u = 1 + rng.below(num_vertices as usize) as u32;
                    let mut v = 1 + rng.below(num_vertices as usize) as u32;
                    if v == u {
                        v = 1 + (v % num_vertices);
                    }
                    edges.push((u, v));
                }
                vertex_cover_instance(num_vertices, &edges)
            } else {
                // Planted single-equality subset-sum (feasible by construction).
                let n = 5 + rng.below(8);
                let weights: Vec<i128> = (0..n).map(|_| 1 + rng.below(20) as i128).collect();
                let planted: Vec<bool> = (0..n).map(|_| rng.below(2) == 1).collect();
                let target: i128 = weights
                    .iter()
                    .zip(&planted)
                    .filter(|(_, &p)| p)
                    .map(|(&w, _)| w)
                    .sum();
                let constraints = vec![eq(
                    weights
                        .iter()
                        .enumerate()
                        .map(|(i, &w)| term(w, lit(i as u32 + 1)))
                        .collect(),
                    target,
                )];
                let objective = PbObjective {
                    terms: (1..=n as u32).map(|v| term(1, lit(v))).collect(),
                };
                let instance = PbInstance {
                    num_vars: n as u32,
                    num_constraints: 1,
                    constraints,
                    objective: Some(objective.clone()),
                };
                (instance, objective)
            };

            let (weighting, scc) = match iter % 3 {
                0 => (WeightScheme::Ddfw, false),
                1 => (WeightScheme::Paws, true),
                _ => (WeightScheme::Ddfw, true),
            };
            let stop = no_stop();
            let mut violations = 0usize;
            let mut prev: Option<i128> = None;
            {
                let mut on_improve = |obj: i128, model: &[bool]| {
                    if !verify_all_constraints(&instance.constraints, model) {
                        violations += 1;
                    }
                    if eval_objective(&objective, model) != obj {
                        violations += 1;
                    }
                    if let Some(p) = prev {
                        if obj >= p {
                            violations += 1;
                        }
                    }
                    prev = Some(obj);
                };
                let result = search_with_seeds(
                    &instance,
                    &objective,
                    None,
                    &stop,
                    &mut on_improve,
                    &SlsOptions {
                        weighting,
                        scc,
                        max_flips: 30_000,
                        ..SlsOptions::default()
                    },
                );
                if let Some(r) = result {
                    assert!(verify_all_constraints(&instance.constraints, &r.assignment));
                    assert_eq!(eval_objective(&objective, &r.assignment), r.objective);
                }
            }
            assert_eq!(
                violations, 0,
                "DDFW/SCC arm reported a bad incumbent (iter {iter})"
            );
        }
    }

    /// Per-seed determinism for both §2.2 arms: identical option sets (fixed
    /// flip caps, no wall clock) must reproduce the FULL incumbent stream and
    /// final result bit-for-bit — DDFW draws no RNG at all, and the SCC
    /// smoothing draws only from the structurally-seeded PRNG.
    #[test]
    fn ddfw_scc_search_deterministic_per_seed() {
        let (instance, objective) = vertex_cover_instance(
            8,
            &[
                (1, 2),
                (2, 3),
                (3, 4),
                (4, 5),
                (5, 6),
                (6, 7),
                (7, 8),
                (1, 8),
            ],
        );
        for (weighting, scc) in [
            (WeightScheme::Ddfw, false),
            (WeightScheme::Paws, true),
            (WeightScheme::Ddfw, true),
        ] {
            let run = || {
                let stop = no_stop();
                let mut reported: Vec<(i128, Vec<bool>)> = Vec::new();
                let mut on_improve =
                    |obj: i128, model: &[bool]| reported.push((obj, model.to_vec()));
                let result = search_with_seeds(
                    &instance,
                    &objective,
                    None,
                    &stop,
                    &mut on_improve,
                    &SlsOptions {
                        weighting,
                        scc,
                        max_flips: 50_000,
                        ..SlsOptions::default()
                    },
                );
                (reported, result)
            };
            let a = run();
            let b = run();
            assert!(
                a.1.is_some(),
                "the cycle cover must be found ({weighting:?}, scc={scc})"
            );
            assert_eq!(
                a, b,
                "trajectory not deterministic per seed ({weighting:?}, scc={scc})"
            );
        }
    }

    /// DDFW and SCC are DEFAULT OFF (design §2.2 — A/B-gated diversified
    /// worker arms): default-constructed options must produce a trajectory
    /// bit-identical to an explicit `weighting: Paws, scc: false` run (the
    /// scheme machinery is inert unless a worker opts in). Non-vacuity — that
    /// the flags are load-bearing rather than ignored — is pinned by
    /// `ddfw_transfer_picks_max_weight_satisfied_neighbor` and
    /// `scc_bits_track_neighbor_flips_and_smooth`.
    #[test]
    fn ddfw_scc_default_off_matches_disabled_run() {
        assert_eq!(
            SlsOptions::default().weighting,
            WeightScheme::Paws,
            "PAWS must stay the default weighting (design §2.2)"
        );
        assert!(!SlsOptions::default().scc, "SCC must be OFF by default");

        let (instance, objective) =
            vertex_cover_instance(6, &[(1, 2), (2, 3), (3, 4), (4, 5), (5, 6)]);
        let run = |explicit_off: bool| {
            let stop = no_stop();
            let mut reported: Vec<(i128, Vec<bool>)> = Vec::new();
            let mut on_improve = |obj: i128, model: &[bool]| reported.push((obj, model.to_vec()));
            let options = if explicit_off {
                SlsOptions {
                    weighting: WeightScheme::Paws,
                    scc: false,
                    max_flips: 40_000,
                    ..SlsOptions::default()
                }
            } else {
                SlsOptions {
                    max_flips: 40_000,
                    ..SlsOptions::default()
                }
            };
            let result = search_with_seeds(
                &instance,
                &objective,
                None,
                &stop,
                &mut on_improve,
                &options,
            );
            (reported, result)
        };
        assert_eq!(
            run(false),
            run(true),
            "default options must reproduce the DDFW/SCC-disabled trajectory bit-for-bit"
        );
    }

    /// Planted-instance escape test (design §2.2's quality claim, and the
    /// non-vacuity pin for the DDFW arm): a planted-feasible 4×24 market-split
    /// system (Σ_j w_ij·x_j = Σ_j w_ij·p_j — the multi-row equality wall where
    /// single-flip min-conflicts plateaus and the uniform PAWS `+1` cannot
    /// tilt the landscape within budget) on which, under the SAME structural
    /// seed and the SAME fixed flip budget, the PAWS trajectory ends
    /// empty-handed while the DDFW weight-transfer trajectory lands a
    /// verified feasible incumbent. Fully deterministic — structural PRNG
    /// seed, fixed flip cap, no wall clock — the configuration was picked by
    /// a deterministic sweep over planted market-split shapes, so this can
    /// never flake; it re-runs the exact trajectories that A/B'd apart.
    #[test]
    fn ddfw_escapes_paws_stuck_weight_plateau() {
        let mut wrng = SplitMix64::new(0xAB12_34CD_5678_EF90);
        let n = 24usize;
        let m = 4usize;
        let planted: Vec<bool> = (0..n).map(|j| j % 3 == 0).collect();
        let mut constraints = Vec::new();
        for _ in 0..m {
            let weights: Vec<i128> = (0..n).map(|_| 1 + wrng.below(99) as i128).collect();
            let rhs: i128 = weights
                .iter()
                .zip(&planted)
                .filter(|(_, &p)| p)
                .map(|(&w, _)| w)
                .sum();
            constraints.push(eq(
                weights
                    .iter()
                    .enumerate()
                    .map(|(j, &w)| term(w, lit(j as u32 + 1)))
                    .collect(),
                rhs,
            ));
        }
        let objective = PbObjective {
            terms: (1..=n as u32).map(|v| term(1, lit(v))).collect(),
        };
        let instance = PbInstance {
            num_vars: n as u32,
            num_constraints: m as u32,
            constraints,
            objective: Some(objective.clone()),
        };
        assert!(verify_all_constraints(&instance.constraints, &planted));

        let run = |weighting: WeightScheme| {
            let stop = no_stop();
            let mut reported = Vec::new();
            let mut on_improve = |obj: i128, model: &[bool]| {
                assert!(verify_all_constraints(&instance.constraints, model));
                assert_eq!(eval_objective(&objective, model), obj);
                reported.push(obj);
            };
            let result = search_with_seeds(
                &instance,
                &objective,
                None,
                &stop,
                &mut on_improve,
                &SlsOptions {
                    weighting,
                    fast_bump: true,
                    max_flips: 100_000,
                    ..SlsOptions::default()
                },
            );
            (result, reported)
        };

        let (paws, paws_reported) = run(WeightScheme::Paws);
        assert!(
            paws.is_none() && paws_reported.is_empty(),
            "sweep premise broken: PAWS unexpectedly cracked the equality wall \
             within the pinned budget (re-pin the instance/budget)"
        );

        let (ddfw, ddfw_reported) = run(WeightScheme::Ddfw);
        let ddfw = ddfw.expect("DDFW must escape the plateau and land an incumbent");
        assert!(verify_all_constraints(
            &instance.constraints,
            &ddfw.assignment
        ));
        assert_eq!(eval_objective(&objective, &ddfw.assignment), ddfw.objective);
        assert!(!ddfw_reported.is_empty());
    }

    // ---- Unified (NuPBO-class) search tests ----

    #[test]
    fn unified_polish_warm_start_releases_lambda_lock() {
        // The always-on polish path seeds `search_unified` with an EXISTING
        // feasible incumbent. The λ hard-lock (design §2.1) must release at
        // step 0 (λ = LAMBDA_INIT) so the polish run does objective descent
        // immediately — it must NOT silently degrade to a feasibility-only
        // search just because it never made an infeasible->feasible transition.
        let costs: Vec<i128> = (1..=8).collect();
        let (instance, objective) = market_split_instance(&costs, 3);
        let mut warm = vec![false; 8];
        warm[5] = true;
        warm[6] = true;
        warm[7] = true; // worst feasible point: objective 21
        assert!(verify_all_constraints(&instance.constraints, &warm));

        // Scorer-level: a feasible seed releases the lock at construction.
        let scorer = crate::optimize::unified_score::Scorer::new(
            &instance.constraints,
            &objective,
            8,
            &warm,
        )
        .unwrap();
        assert!(scorer.is_feasible());
        assert_eq!(
            scorer.lambda(),
            crate::optimize::unified_score::LAMBDA_INIT,
            "feasible warm start must unlock λ at LAMBDA_INIT from step 0"
        );

        // Search-level: with objective pressure live from step 0, the polish
        // run strictly escapes the trapped feasible warm start (no single flip
        // preserves the equality, so a feasibility-only search cannot improve).
        let stop = no_stop();
        let mut on_improve = |obj: i128, model: &[bool]| {
            assert!(verify_all_constraints(&instance.constraints, model));
            assert_eq!(eval_objective(&objective, model), obj);
        };
        let result = search_unified(
            &instance,
            &objective,
            Some(std::time::Instant::now() + std::time::Duration::from_millis(500)),
            &stop,
            &mut on_improve,
            Some(&warm),
        )
        .expect("polish run must retain/improve the warm incumbent");
        assert!(
            result.objective < 21,
            "polish run degraded to a feasibility-only search"
        );
    }

    fn eq(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Eq,
            rhs,
        }
    }

    /// Market-split style instance: choose EXACTLY `k` of `n` items (`Σ x_i = k`),
    /// minimizing `Σ cost_i · x_i`. The optimum picks the `k` cheapest. From a
    /// feasible point, NO single flip preserves the equality (any flip changes the
    /// count), so a feasibility-preserving-only local search is fully trapped; the
    /// unified loop must swap an expensive-out / cheap-in pair through a transient
    /// infeasible state.
    fn market_split_instance(costs: &[i128], k: i128) -> (PbInstance, PbObjective) {
        let n = costs.len() as u32;
        let constraint = eq((1..=n).map(|v| term(1, lit(v))).collect(), k);
        let objective = PbObjective {
            terms: costs
                .iter()
                .enumerate()
                .map(|(i, &c)| term(c, lit(i as u32 + 1)))
                .collect(),
        };
        let instance = PbInstance {
            num_vars: n,
            num_constraints: 1,
            constraints: vec![constraint],
            objective: Some(objective.clone()),
        };
        (instance, objective)
    }

    #[test]
    fn unified_escapes_suboptimal_ridge_where_baseline_traps() {
        // 8 items, pick exactly 3; costs 1..=8. Optimum = items {1,2,3} -> 6.
        let costs: Vec<i128> = (1..=8).collect();
        let (instance, objective) = market_split_instance(&costs, 3);

        // Warm start at the WORST feasible point: the 3 most expensive (6,7,8) true
        // -> objective 21. This is feasible, so the soundness gate accepts it.
        let mut warm = vec![false; 8];
        warm[5] = true; // item 6
        warm[6] = true; // item 7
        warm[7] = true; // item 8
        assert!(verify_all_constraints(&instance.constraints, &warm));
        assert_eq!(eval_objective(&objective, &warm), 21);

        let stop = no_stop();
        let mut on_improve = |obj: i128, model: &[bool]| {
            assert!(verify_all_constraints(&instance.constraints, model));
            assert_eq!(eval_objective(&objective, model), obj);
        };
        let result = search_unified(
            &instance,
            &objective,
            Some(std::time::Instant::now() + std::time::Duration::from_millis(800)),
            &stop,
            &mut on_improve,
            Some(&warm),
        )
        .expect("unified SLS should keep at least the warm-start incumbent");
        assert!(verify_all_constraints(
            &instance.constraints,
            &result.assignment
        ));
        assert_eq!(
            eval_objective(&objective, &result.assignment),
            result.objective
        );
        // It must strictly improve on the trapped warm start (21) by crossing the
        // equality ridge, and should reach the optimum (6) on this small instance.
        assert!(result.objective < 21, "did not escape the suboptimal ridge");
        assert_eq!(result.objective, 6, "did not reach the optimum");
    }

    #[test]
    fn unified_warm_start_never_loses_incumbent() {
        // A feasible warm start must always be recorded (and verified) even if the
        // search makes no further progress.
        let costs: Vec<i128> = vec![5, 5, 5, 5];
        let (instance, objective) = market_split_instance(&costs, 2); // any 2 -> 10
        let mut warm = vec![false; 4];
        warm[0] = true;
        warm[1] = true;
        let stop = no_stop();
        let mut on_improve = |_obj: i128, _model: &[bool]| {};
        let result = search_unified(
            &instance,
            &objective,
            Some(std::time::Instant::now() + std::time::Duration::from_millis(200)),
            &stop,
            &mut on_improve,
            Some(&warm),
        )
        .expect("warm-started feasible incumbent must be retained");
        assert!(verify_all_constraints(
            &instance.constraints,
            &result.assignment
        ));
        assert!(result.objective <= 10);
    }

    #[test]
    fn unified_finds_first_incumbent_from_scratch() {
        // No warm start: unified search must still find a feasible cover from the
        // all-false (infeasible) start, like the baseline.
        let (instance, objective) =
            vertex_cover_instance(6, &[(1, 2), (2, 3), (3, 4), (4, 5), (5, 6)]);
        let stop = no_stop();
        let mut on_improve = |obj: i128, model: &[bool]| {
            assert!(verify_all_constraints(&instance.constraints, model));
            assert_eq!(eval_objective(&objective, model), obj);
        };
        let result = search_unified(
            &instance,
            &objective,
            Some(std::time::Instant::now() + std::time::Duration::from_millis(500)),
            &stop,
            &mut on_improve,
            None,
        )
        .expect("unified SLS should find a feasible cover from scratch");
        assert!(verify_all_constraints(
            &instance.constraints,
            &result.assignment
        ));
        assert!(result.objective <= 6);
    }

    #[test]
    fn unified_never_reports_infeasible_or_nonimproving_fuzz() {
        // Soundness fuzz mirroring the baseline: across many pseudo-random covering
        // AND market-split instances, every reported incumbent (stream + return)
        // must be feasible, exactly-valued, and strictly improving.
        let mut rng = SplitMix64::new(0x2468_ACE0_1357_9BDF);
        for iter in 0..40 {
            let (instance, objective) = if iter % 2 == 0 {
                let num_vertices = 4 + rng.below(9) as u32;
                let edge_count = 3 + rng.below(12);
                let mut edges = Vec::new();
                for _ in 0..edge_count {
                    let u = 1 + rng.below(num_vertices as usize) as u32;
                    let mut v = 1 + rng.below(num_vertices as usize) as u32;
                    if v == u {
                        v = 1 + (v % num_vertices);
                    }
                    edges.push((u, v));
                }
                vertex_cover_instance(num_vertices, &edges)
            } else {
                let n = 4 + rng.below(8);
                let costs: Vec<i128> = (0..n).map(|_| 1 + rng.below(20) as i128).collect();
                let k = 1 + rng.below(n.max(1)) as i128;
                market_split_instance(&costs, k.min(n as i128))
            };

            let stop = no_stop();
            let mut violations = 0usize;
            let mut prev: Option<i128> = None;
            {
                let mut on_improve = |obj: i128, model: &[bool]| {
                    if !verify_all_constraints(&instance.constraints, model) {
                        violations += 1;
                    }
                    if eval_objective(&objective, model) != obj {
                        violations += 1;
                    }
                    if let Some(p) = prev {
                        if obj >= p {
                            violations += 1;
                        }
                    }
                    prev = Some(obj);
                };
                let result = search_unified(
                    &instance,
                    &objective,
                    Some(std::time::Instant::now() + std::time::Duration::from_millis(40)),
                    &stop,
                    &mut on_improve,
                    None,
                );
                if let Some(r) = result {
                    assert!(verify_all_constraints(&instance.constraints, &r.assignment));
                    assert_eq!(eval_objective(&objective, &r.assignment), r.objective);
                }
            }
            assert_eq!(violations, 0, "unified SLS reported a bad incumbent");
        }
    }

    /// Tracker for the Task V4 feasibility-wall lever: the SHIPPED portfolio
    /// combination — a feasibility-first two-phase pass (which breaks the equality
    /// wall) followed by the unified objective-as-soft descent, keeping the best of
    /// the two — must (a) report ONLY VIG-verified, exactly-valued incumbents
    /// (0-wrong), and (b) on a FEASIBLE single-equality subset-sum instance, find a
    /// feasible incumbent (the union never loses what either pass finds). This
    /// mirrors `solve_optimization_sls`'s feasibility-first path on `Eq` instances.
    #[test]
    fn feasibility_first_union_is_sound_and_finds_incumbent() {
        // Σ w_i x_i = T with a PLANTED feasible point (T = Σ over a chosen subset),
        // minimize Σ x_i. Feasible by construction, so the union of the two passes
        // must land a verified incumbent.
        let weights: Vec<i128> = vec![7, 3, 11, 5, 9, 2, 13, 6, 8, 4, 10, 1, 12, 15, 14];
        let planted = [
            true, false, true, true, false, true, false, true, false, true, false, false, true,
            false, true,
        ];
        let target: i128 = weights
            .iter()
            .zip(planted.iter())
            .filter(|(_, &p)| p)
            .map(|(&w, _)| w)
            .sum();
        let n = weights.len() as u32;
        let constraints = vec![eq(
            weights
                .iter()
                .enumerate()
                .map(|(i, &w)| term(w, lit(i as u32 + 1)))
                .collect(),
            target,
        )];
        let objective = PbObjective {
            terms: (1..=n).map(|v| term(1, lit(v))).collect(),
        };
        let instance = PbInstance {
            num_vars: n,
            num_constraints: 1,
            constraints,
            objective: Some(objective.clone()),
        };
        assert!(verify_all_constraints(&instance.constraints, &planted));

        let stop = no_stop();
        let mut violations = 0usize;
        let best: Option<i128>;
        {
            let mut on_improve = |obj: i128, model: &[bool]| {
                if !verify_all_constraints(&instance.constraints, model)
                    || eval_objective(&objective, model) != obj
                {
                    violations += 1;
                }
            };
            // Feasibility-first pass (two-phase PAWS), then unified descent — the
            // shipped combination. Best kept across both.
            let half = std::time::Duration::from_millis(300);
            let r1 = search_with_options(
                &instance,
                &objective,
                Some(std::time::Instant::now() + half),
                &stop,
                &mut on_improve,
                true,
            );
            let r2 = search_unified(
                &instance,
                &objective,
                Some(std::time::Instant::now() + half),
                &stop,
                &mut on_improve,
                None,
            );
            best = match (r1, r2) {
                (Some(a), Some(b)) => Some(a.objective.min(b.objective)),
                (Some(a), None) => Some(a.objective),
                (None, Some(b)) => Some(b.objective),
                (None, None) => None,
            };
        }
        assert_eq!(
            violations, 0,
            "feasibility-first union reported a bad incumbent"
        );
        assert!(
            best.is_some(),
            "union must find a feasible incumbent on a planted instance"
        );
    }

    /// Measurement: unified vs. the two-phase baseline on the trapped market-split
    /// family, both given the SAME warm start and time budget. Printed under
    /// `cargo test -- --nocapture`. The baseline `search` ignores the warm start
    /// (starts from all-false) and accepts only feasibility-preserving flips, so on
    /// the equality ridge it cannot improve past whatever its from-scratch descent
    /// reaches; unified crosses the ridge from the warm start.
    #[test]
    fn bench_unified_vs_baseline_market_split() {
        let budget = std::time::Duration::from_millis(200);
        let mut unified_wins = 0;
        let mut total = 0;
        println!("\n=== unified (warm) vs baseline (from-scratch) on market-split ridge ===");
        println!(
            "{:>5} {:>6} {:>9} {:>9} {:>9}",
            "n", "k", "warm", "baseline", "unified"
        );
        for &(n, k) in &[
            (10u32, 4i128),
            (16, 6),
            (20, 8),
            (30, 12),
            (60, 30),
            (100, 50),
        ] {
            let costs: Vec<i128> = (1..=n as i128).collect();
            let (instance, objective) = market_split_instance(&costs, k);
            // Warm start at the k MOST expensive (worst feasible).
            let mut warm = vec![false; n as usize];
            for i in 0..k as usize {
                warm[n as usize - 1 - i] = true;
            }
            let warm_obj = eval_objective(&objective, &warm);

            // Baseline (from scratch, feasibility-preserving descent).
            let stop = no_stop();
            let mut noop = |_o: i128, _m: &[bool]| {};
            let base = search(
                &instance,
                &objective,
                Some(std::time::Instant::now() + budget),
                &stop,
                &mut noop,
            )
            .map(|r| r.objective)
            .unwrap_or(i128::MAX);

            // Unified, warm-started from the worst feasible point.
            let uni = search_unified(
                &instance,
                &objective,
                Some(std::time::Instant::now() + budget),
                &stop,
                &mut noop,
                Some(&warm),
            )
            .map(|r| r.objective)
            .unwrap_or(i128::MAX);

            println!("{n:>5} {k:>6} {warm_obj:>9} {base:>9} {uni:>9}");
            total += 1;
            if uni <= base {
                unified_wins += 1;
            }
            // The load-bearing claim: warm-started unified ALWAYS strictly escapes
            // the trapped suboptimal warm start (which a feasibility-preserving-only
            // descent cannot, since no single flip preserves the equality). This is
            // the capability that unlocks the 60 suboptimal OPT-LIN cases.
            assert!(
                uni < warm_obj,
                "unified failed to escape the ridge: warm={warm_obj} uni={uni} (n={n}, k={k})"
            );
        }
        println!("unified(warm) <= baseline(scratch) on {unified_wins}/{total} shapes");
    }

    // ---- microbenchmark (design §4 performance contract) ----
    //
    // Ignored by default: run explicitly, release build, e.g.
    //   cargo test -p ay-pb --release -j 4 --lib -- --ignored bench_ --nocapture
    // Deterministic synthetic instances (10k/100k vars, mixed Ge/Eq, negated
    // literals) and fixed flip budgets; wall clock printed. Justifies the i64
    // fast-path benefit for the two-phase tracker (Change 1).

    /// Deterministic synthetic instance: mixed Ge/Eq rows (every 3rd Eq),
    /// ~half negated literals, small (i64-fitting) coefficients, objective
    /// over all variables.
    fn synth_mixed_instance(
        num_vars: usize,
        rows: usize,
        row_len: usize,
        seed: u64,
    ) -> (PbInstance, PbObjective) {
        let mut rng = SplitMix64::new(seed);
        let mut constraints = Vec::with_capacity(rows);
        for r in 0..rows {
            let mut terms = Vec::with_capacity(row_len);
            let mut sum: i128 = 0;
            for _ in 0..row_len {
                let v = rng.below(num_vars) as u32 + 1;
                let negated = rng.below(2) == 1;
                let c = 1 + rng.below(16) as i128;
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
        let instance = PbInstance {
            num_vars: num_vars as u32,
            num_constraints: constraints.len() as u32,
            constraints,
            objective: Some(objective.clone()),
        };
        (instance, objective)
    }

    #[test]
    #[ignore = "microbench: run explicitly with --ignored --nocapture (release)"]
    fn bench_tracker_i64_vs_i128_flip_rate() {
        println!("\n=== two-phase tracker flip-rate: i64 fast path vs i128 (search_loop) ===");
        println!(
            "{:>8} {:>9} {:>6} {:>10} {:>12} {:>12}",
            "vars", "rows", "width", "flips", "secs", "flips/sec"
        );
        for &(num_vars, rows, flips) in &[
            (10_000usize, 20_000usize, 1_000_000u64),
            (100_000, 200_000, 1_000_000),
        ] {
            let (instance, objective) = synth_mixed_instance(num_vars, rows, 5, 0x5EED_5EED);
            assert!(rows_fit::<i64>(&instance.constraints));
            let mut secs = [0.0f64; 2];
            for (i, wide) in [(0, false), (1, true)] {
                let stop = no_stop();
                let mut noop = |_o: i128, _m: &[bool]| {};
                let options = SlsOptions {
                    fast_bump: true,
                    max_flips: flips,
                    ..SlsOptions::default()
                };
                let t0 = std::time::Instant::now();
                let result = if wide {
                    search_loop::<i128>(&instance, &objective, None, &stop, &mut noop, &options)
                } else {
                    search_loop::<i64>(&instance, &objective, None, &stop, &mut noop, &options)
                };
                secs[i] = t0.elapsed().as_secs_f64();
                println!(
                    "{:>8} {:>9} {:>6} {:>10} {:>12.3} {:>12.0}   (best {:?})",
                    num_vars,
                    rows,
                    if wide { "i128" } else { "i64" },
                    flips,
                    secs[i],
                    flips as f64 / secs[i],
                    result.map(|r| r.objective)
                );
            }
            println!("          i64 speedup: {:.2}x", secs[1] / secs[0]);
        }
    }
}
