// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{WeightScheme, MAX_FLIPS, MAX_SLS_VARS, WALK_NOISE_PERMILLE};

/// Additive per-run options for [`super::search_with_seeds`]. `Default`
/// reproduces the exact behavior of `search` (`fast_bump = false`, default
/// caps, no external seeds), so the parent module's thin wrapper entry points
/// retain their existing behavior.
pub(crate) struct SlsOptions<'a> {
    /// O(violated) PAWS bump — see [`super::Tracker::bump_violated_weights`].
    pub(crate) fast_bump: bool,
    /// Per-run variable cap — see [`super::search_with_limits`].
    pub(crate) max_vars: usize,
    /// Hard cap on flips (defaults to [`MAX_FLIPS`]). A small cap lets tests run
    /// the loop fully deterministically, with no wall-clock deadline.
    pub(crate) max_flips: u64,
    /// OPTIONAL externally-provided restart seed points (design §3.1's third
    /// restart layer, e.g. a future LP-rounded fractional point): candidate
    /// assignments the [`super::RestartLayer::ExternalSeed`] layer cycles through.
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
    /// [`super::structural_seed`] exactly.
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
    /// [`super::Tracker::ddfw_transfer_weights`]). ADVISORY ONLY — weights
    /// steer the search; every incumbent is still independently re-verified.
    pub(crate) weighting: WeightScheme,
    /// Smoothed Configuration Checking (design §2.2) — DEFAULT OFF (the
    /// default trajectory stays bit-identical). When on (an A/B-gated
    /// diversified-worker arm), only configuration-changed variables — those
    /// with a neighbor flipped since their own last flip — are eligible for
    /// the feasibility-phase GREEDY pick (falling back to the existing noise
    /// pick when no candidate is eligible), with a random small fraction
    /// re-enabled on the [`super::SCC_SMOOTH_INTERVAL`] smoothing cadence.
    /// ADVISORY ONLY — eligibility steers the search, never soundness.
    pub(crate) scc: bool,
    /// WalkSAT feasibility-phase noise in 1/1000 — DEFAULT
    /// [`WALK_NOISE_PERMILLE`] (200), which reproduces the historical
    /// trajectory bit-for-bit. A 2026-06-27 lever sweep (local branch wf2-sls,
    /// never landed) measured 400 as +net incumbents / 0 wrong, but mostly on
    /// synthetic set-cover/knapsack families (one real instance) and the SLS
    /// has changed materially since — so 400 is a PENDING A/B axis for a
    /// diversified worker arm, not a default. ADVISORY ONLY — noise steers
    /// the search; every incumbent is still independently re-verified.
    pub(crate) walk_permille: u64,
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
            walk_permille: WALK_NOISE_PERMILLE,
        }
    }
}
