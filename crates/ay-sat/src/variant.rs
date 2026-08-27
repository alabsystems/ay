// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT-COMP solver-variant presets.
//!
//! These presets sit above the low-level `Solver` setters so frontends and
//! packaging scripts can build named SAT variants without duplicating tuning
//! blocks across crates.
//!
//! ## Competition Variants
//!
//! SAT-COMP allows up to 4 solver variants per team. Each variant uses a
//! different configuration profile targeting different problem classes:
//!
//! | Variant | Strategy | Best For |
//! |---------|----------|----------|
//! | `default` | DIMACS SAT packet: stable-only + reduced effort | Baseline CNF |
//! | `aggressive` | Same packet + unconditional full preprocessing | Structured/BMC |
//! | `probe` | Probing + backbone + HBR emphasis | Hard combinatorial |
//! | `minimal` | No inprocessing, fast BCP | Easy/industrial |
//!
//! ## Usage
//!
//! Runtime selection via `AY_SAT_VARIANT` environment variable or
//! per-variant StarExec run scripts in `competition/bin/`.

use crate::auto::DecisionSource;
#[cfg(test)]
use crate::features::InstanceClass;
use crate::features::SatFeatures;
use crate::proof_capability::{self, ProofMode};
use crate::{BranchHeuristic, InprocessingFeatureProfile, Solver};

mod capability_plan;
mod input;
pub use capability_plan::VariantProfilePlan;
pub use input::{VariantInput, VariantProofMode};

/// Named SAT-COMP preset selector.
///
/// Four distinct competition variants for SAT-COMP submission. Each targets
/// a different problem class to maximize the portfolio coverage:
///
/// - **Default**: DIMACS SAT packet with stable-only search and reduced BVE/subsumption effort.
/// - **Aggressive**: Same packet, but always runs full preprocessing.
/// - **Probe**: Emphasis on failed-literal probing and backbone detection.
/// - **Minimal**: No inprocessing, fast BCP, conservative search.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum SolverVariant {
    /// Current DIMACS-oriented baseline with all standard features enabled.
    /// Balanced VSIDS + Glucose restarts, quick-mode preprocessing.
    #[default]
    Default,
    /// Higher preprocessing effort and more aggressive simplification.
    /// Full preprocessing, all inprocessing techniques enabled with
    /// tighter scheduling intervals for BVE, subsumption, and vivification.
    Aggressive,
    /// Minimal preprocessing, relying more heavily on CDCL search.
    /// No inprocessing except walk/warmup/shrink for fast BCP throughput.
    Minimal,
    /// Probe-focused: emphasis on failed-literal probing and backbone
    /// detection. Enables probing, backbone, HBR, subsumption, and
    /// transitive reduction while disabling heavyweight techniques
    /// (BVE, vivification, conditioning, sweep, congruence).
    /// Uses Luby restarts (base=250) for more stable search on hard instances.
    Probe,
    /// Caller-provided inprocessing feature profile for programmatic consumers.
    ///
    /// Allows downstream crates (e.g., the model-checker consumer's IC3/BMC engines) to specify
    /// exactly which inprocessing techniques to enable, without being
    /// constrained to one of the four competition presets.
    Custom(InprocessingFeatureProfile),
}

impl SolverVariant {
    /// All currently supported SAT-COMP variants.
    pub const ALL: [Self; 4] = [Self::Default, Self::Aggressive, Self::Minimal, Self::Probe];

    /// Stable external name for the preset.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Default => "default",
            Self::Aggressive => "aggressive",
            Self::Minimal => "minimal",
            Self::Probe => "probe",
            Self::Custom(_) => "custom",
        }
    }

    /// Stable executable name used by the build script.
    #[must_use]
    pub const fn binary_name(self) -> &'static str {
        match self {
            Self::Default => "ay-default",
            Self::Aggressive => "ay-aggressive",
            Self::Minimal => "ay-minimal",
            Self::Probe => "ay-probe",
            Self::Custom(_) => "ay-custom",
        }
    }

    /// Parse a preset name.
    #[must_use]
    pub fn parse(name: &str) -> Option<Self> {
        if name.eq_ignore_ascii_case("default") {
            Some(Self::Default)
        } else if name.eq_ignore_ascii_case("aggressive") {
            Some(Self::Aggressive)
        } else if name.eq_ignore_ascii_case("minimal") {
            Some(Self::Minimal)
        } else if name.eq_ignore_ascii_case("probe") {
            Some(Self::Probe)
        } else if name.eq_ignore_ascii_case("custom") {
            Some(Self::Custom(InprocessingFeatureProfile::default()))
        } else {
            None
        }
    }

    /// Resolve a preset into concrete solver settings for the given input.
    #[must_use]
    pub fn config(self, input: VariantInput) -> VariantConfig {
        VariantConfig::for_variant(self, input)
    }

    /// Auto-route the Default preset to Probe when load-time `features` land in
    /// the probe-route band (see [`SatFeatures::matches_probe_route_band`]).
    ///
    /// Non-Default variants are returned unchanged (an explicit `--sat-variant`
    /// choice is always honored). Kill-switch: `--sat-no-probe-route` disables
    /// the re-route entirely. The caller must only apply this when no explicit
    /// `--sat-variant` was requested.
    #[must_use]
    pub fn auto_probe_route(self, features: &SatFeatures) -> Self {
        self.auto_probe_route_if_with_source(
            features.matches_probe_route_band(),
            DecisionSource::Default,
        )
        .0
    }

    /// Raw-count variant of [`Self::auto_probe_route`] for the streaming parse
    /// path, which computes the band inputs from a content pre-scan rather than
    /// a full [`SatFeatures`] extraction. `num_vars` must be the content-driven
    /// max-variable count.
    #[must_use]
    pub fn auto_probe_route_from_counts(
        self,
        num_vars: usize,
        num_clauses: usize,
        num_binary: usize,
    ) -> Self {
        self.auto_probe_route_if_with_source(
            crate::features::probe_route_band_from_counts(num_vars, num_clauses, num_binary),
            DecisionSource::Default,
        )
        .0
    }

    /// Shared core: re-route Default -> Probe when `in_band`, honoring the
    /// `--sat-no-probe-route` kill-switch and leaving non-Default variants intact.
    #[must_use]
    fn auto_probe_route_if_with_source(
        self,
        in_band: bool,
        source: DecisionSource,
    ) -> (Self, DecisionSource) {
        if !matches!(self, Self::Default) || !in_band {
            return (self, source);
        }
        if ay_core::sat_ab_switches().no_probe_route {
            // B34: the operator vetoed the in-band route (--sat-no-probe-route).
            (self, DecisionSource::Cli)
        } else {
            (Self::Probe, DecisionSource::Auto)
        }
    }

    /// Combined load-time auto-route for an unspecified `--sat-variant`: apply
    /// the probe-route band first (Default -> Probe), then — only if the input
    /// is still Default — the aggressive-route band (Default -> Aggressive).
    ///
    /// The two bands are disjoint by the clause/var ratio (probe owns
    /// `ratio <= 4.0`, aggressive owns `4.0 < ratio <= 6.5`), so the order is
    /// not load-bearing for correctness; probe is evaluated first to match the
    /// landed precedence. Each band has its own kill-switch
    /// (`--sat-no-probe-route` / `--sat-no-aggressive-route`); disabling one
    /// leaves the other active. The caller must only apply this when no explicit
    /// `--sat-variant` was requested.
    #[must_use]
    pub fn auto_route(self, features: &SatFeatures) -> Self {
        self.auto_route_with_source(features, DecisionSource::Default)
            .0
    }

    /// Resolve the combined auto-route while preserving the last decisive
    /// source, including a compatibility kill-switch that vetoes an otherwise
    /// in-band route.
    #[must_use]
    pub fn auto_route_with_source(
        self,
        features: &SatFeatures,
        source: DecisionSource,
    ) -> (Self, DecisionSource) {
        let (variant, source) =
            self.auto_probe_route_if_with_source(features.matches_probe_route_band(), source);
        variant
            .auto_aggressive_route_if_with_source(features.matches_aggressive_route_band(), source)
    }

    /// Raw-count variant of [`Self::auto_route`] for the streaming parse path,
    /// which computes the band inputs from a content pre-scan rather than a full
    /// [`SatFeatures`] extraction. `num_vars` must be the content-driven
    /// max-variable count.
    #[must_use]
    pub fn auto_route_from_counts(
        self,
        num_vars: usize,
        num_clauses: usize,
        num_binary: usize,
    ) -> Self {
        self.auto_route_from_counts_with_source(
            num_vars,
            num_clauses,
            num_binary,
            DecisionSource::Default,
        )
        .0
    }

    /// Raw-count counterpart of [`Self::auto_route_with_source`].
    #[must_use]
    pub fn auto_route_from_counts_with_source(
        self,
        num_vars: usize,
        num_clauses: usize,
        num_binary: usize,
        source: DecisionSource,
    ) -> (Self, DecisionSource) {
        let (variant, source) = self.auto_probe_route_if_with_source(
            crate::features::probe_route_band_from_counts(num_vars, num_clauses, num_binary),
            source,
        );
        variant.auto_aggressive_route_if_with_source(
            crate::features::aggressive_route_band_from_counts(num_vars, num_clauses, num_binary),
            source,
        )
    }

    /// Auto-route the Default preset to Aggressive when load-time `features`
    /// land in the aggressive-route band (see
    /// [`SatFeatures::matches_aggressive_route_band`]).
    ///
    /// Non-Default variants are returned unchanged (an explicit `--sat-variant`
    /// choice — and any prior probe re-route — is always honored). Kill-switch:
    /// `--sat-no-aggressive-route` disables the re-route entirely.
    #[must_use]
    pub fn auto_aggressive_route(self, features: &SatFeatures) -> Self {
        self.auto_aggressive_route_if_with_source(
            features.matches_aggressive_route_band(),
            DecisionSource::Default,
        )
        .0
    }

    /// Raw-count variant of [`Self::auto_aggressive_route`] for the streaming
    /// parse path. `num_vars` must be the content-driven max-variable count.
    #[must_use]
    pub fn auto_aggressive_route_from_counts(
        self,
        num_vars: usize,
        num_clauses: usize,
        num_binary: usize,
    ) -> Self {
        self.auto_aggressive_route_if_with_source(
            crate::features::aggressive_route_band_from_counts(num_vars, num_clauses, num_binary),
            DecisionSource::Default,
        )
        .0
    }

    /// Shared core: re-route Default -> Aggressive when `in_band`, honoring the
    /// `--sat-no-aggressive-route` kill-switch and leaving non-Default variants
    /// intact (so a prior probe re-route to Probe is preserved).
    #[must_use]
    fn auto_aggressive_route_if_with_source(
        self,
        in_band: bool,
        source: DecisionSource,
    ) -> (Self, DecisionSource) {
        if !matches!(self, Self::Default) || !in_band {
            return (self, source);
        }
        if ay_core::sat_ab_switches().no_aggressive_route {
            // B34: the operator vetoed the in-band route
            // (--sat-no-aggressive-route).
            (self, DecisionSource::Cli)
        } else {
            (Self::Aggressive, DecisionSource::Auto)
        }
    }
}

/// Route-level profile selected by a frontend before formula-class adaptation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum VariantRouteProfile {
    /// Standard variant behavior with no route-specific competition clamps.
    #[default]
    Standard,
    /// Official SAT-COMP Main/default/LRAT route.
    OfficialSatCompMainLrat,
}

impl VariantRouteProfile {
    /// Stable telemetry/config name.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Standard => "standard",
            Self::OfficialSatCompMainLrat => "official-satcomp-main-lrat",
        }
    }

    /// Whether this frontend route must reject proof-incomplete specialists.
    #[must_use]
    pub const fn requires_proof_safe_specialist_routing(self) -> bool {
        matches!(self, Self::OfficialSatCompMainLrat)
    }
}

/// Startup phase-initialization policy selected by a frontend route.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VariantStartupPolicy {
    /// Keep the variant's normal warmup/walk feature settings.
    Preserve,
    /// Disable startup warmup and walk so CDCL starts after preprocessing/JW.
    DisableWarmupWalk,
}

impl VariantStartupPolicy {
    /// Stable telemetry/config name.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Preserve => "preserve",
            Self::DisableWarmupWalk => "disable-warmup-walk",
        }
    }
}

/// Restart behavior selected by a variant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VariantRestartPolicy {
    /// Use the solver's Glucose-style restart controller.
    Glucose,
    /// Use Luby restarts with the provided base interval.
    Luby {
        /// Conflicts per Luby unit.
        base: u64,
    },
}

/// Branch heuristic selector chosen by a SAT variant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VariantBranchPolicy {
    /// Preserve the solver's focused/stable coupling: focused mode uses VMTF,
    /// stable mode uses EVSIDS.
    LegacyCoupled,
    /// Force one branching heuristic regardless of focused/stable mode.
    Fixed(BranchHeuristic),
    /// Use restart-boundary UCB1 MAB selection with the provided minimum
    /// conflicts per scored epoch.
    MabUcb1 {
        /// Minimum conflicts before a MAB epoch can be scored.
        epoch_min_conflicts: u64,
    },
}

impl VariantBranchPolicy {
    /// Stable telemetry name for this branch policy.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::LegacyCoupled => "legacy_coupled",
            Self::Fixed(_) => "fixed",
            Self::MabUcb1 { .. } => "mab_ucb1",
        }
    }

    fn apply_to_solver(self, solver: &mut Solver) {
        match self {
            Self::LegacyCoupled => solver.set_branch_selector_ucb1(false),
            Self::Fixed(heuristic) => solver.set_branch_heuristic(heuristic),
            Self::MabUcb1 {
                epoch_min_conflicts,
            } => {
                solver.set_branch_selector_ucb1(true);
                solver.set_branch_selector_epoch_min_conflicts(epoch_min_conflicts);
            }
        }
    }
}

/// Fully-resolved runtime configuration for a solver variant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VariantConfig {
    /// Preset that produced this config.
    pub variant: SolverVariant,
    /// Formula/proof metadata used to resolve the preset.
    input: VariantInput,
    /// Whether to request full preprocessing instead of quick mode.
    pub full_preprocessing: bool,
    /// Restart behavior for the preset.
    pub restart_policy: VariantRestartPolicy,
    /// Branching heuristic selector for the preset.
    pub branch_policy: VariantBranchPolicy,
    /// Feature-enable profile applied to the solver.
    pub features: InprocessingFeatureProfile,
    /// Precomputed hot-loop gates for this resolved variant.
    pub hot_path: VariantHotPathConfig,
}

/// Precomputed CDCL hot-loop gates selected by the variant/profile plan.
///
/// These values are frozen at solver startup from route/proof/profile metadata
/// so conflict-analysis and other hot paths consume simple booleans rather
/// than re-checking SAT-COMP route shape or formula-class policy.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct VariantHotPathConfig {
    /// Bypass optional conflict-analysis experiments and stats-only hooks.
    pub prune_conflict_analysis_experiments: bool,
    /// Restrict periodic rephases to stable mode.
    pub stable_only_rephase: bool,
    /// Enable the default-off dense-mutex focused restart gate experiment.
    pub dense_mutex_focused_restart_gate_experiment: bool,
    /// Enable the default-off dense-clique MAB branch-policy experiment.
    pub dense_clique_mab_branch_experiment: bool,
}

impl VariantHotPathConfig {
    fn for_variant_input(variant: SolverVariant, input: VariantInput) -> Self {
        let official_main_lrat_default = is_official_main_lrat_default_route(variant, input);
        Self {
            prune_conflict_analysis_experiments: official_main_lrat_default,
            stable_only_rephase: official_main_lrat_default,
            dense_mutex_focused_restart_gate_experiment: false,
            dense_clique_mab_branch_experiment: false,
        }
    }
}

fn is_official_main_lrat_default_route(variant: SolverVariant, input: VariantInput) -> bool {
    matches!(variant, SolverVariant::Default)
        && matches!(input.proof_mode(), VariantProofMode::Lrat)
        && matches!(
            input.route_profile(),
            VariantRouteProfile::OfficialSatCompMainLrat
        )
}

/// Clause threshold for full preprocessing in Default variant.
/// Raised from 3M to 5M: shuffling-2 (4.7M clauses, 138K vars) benefits from
/// full preprocessing (probing, subsumption, HTR) but was previously stuck in
/// quick mode. CaDiCaL runs full preprocessing regardless of clause count.
/// The expensive-technique gates (CONGRUENCE_MAX_CLAUSES, etc.) separately
/// protect against O(clauses) setup costs.
const DIMACS_FULL_PREPROCESS_MAX_CLAUSES: usize = 5_000_000;
/// BVE effort for large formulas (>5K vars) as per-mille of search propagations.
/// Raised from 10 (1%) to 100 (10%): 1% was too aggressive a reduction --
/// BVE barely ran on large formulas, missing elimination opportunities that
/// reduce the search space. CaDiCaL default is 1000 (100%); 100 (10%) gives
/// meaningful elimination while avoiding pathological BVE overhead on formulas
/// where resolvents blow up (e.g., shuffling-2 produces 450K resolvents).
const DIMACS_REDUCED_EFFORT_BVE: u64 = 100;
/// Subsumption effort for large formulas as per-mille of search propagations.
/// Raised from 60 (6%) to 200 (20%): subsumption is cheap per-step and
/// removes redundant clauses that slow BCP. The per-round overhead is
/// bounded by SUBSUME_MAX_EFFORT.
const DIMACS_REDUCED_EFFORT_SUBSUME: u64 = 200;
/// Sparse-band BVE unlock (#sparse-gap Cluster C): enable BVE on the Default
/// DIMACS variant when clause/var density <= this bound. The Cluster-C
/// kissat-only solves span density 3.1-11.3 (kissat eliminates 49-93% of
/// vars via BVE there); the documented BVE losses (clique_n2_k10 1409->148K
/// resolvent blowup, braun.9, shuffling-2) are all dense or covered by the
/// growth/dense guards, so the band excludes them by construction — same
/// pattern as FACTOR_DENSE_MIN_DENSITY banding the factor-dense unlock.
/// The prior net-neutral BVE A/B (variant.rs bve comment below) was over an
/// UNSCOPED sample; this band is the response. Tunable via
/// --sat-bve-sparse-max-density; DEFAULT ON (--sat-no-bve-sparse disables).
/// Default flipped 2026-07-08 after the braun.11 blocker was fixed at root
/// cause (preprocess subsume learned-subsumer promotion, ef818369) and the
/// fixer + an independent adversarial verifier both re-measured the band:
/// braun family 0 FINALIZE_SAT_FAIL, 16/16 in-band verdict-match with all
/// 10 SAT models externally validated, ~+1 measured flip and up-to-5x
/// speedups now landing in default config.
const BVE_SPARSE_MAX_DENSITY: f64 = 12.0;
/// Variable-count cap for the sparse-band BVE unlock.
///
/// Measured 2026-07-08 (same-binary off/on A/B over the 23 in-band
/// main2025 instances AY solves plus the Cluster-C targets): every gained
/// solve and every speedup sits at <= 147K vars (0e1d5620 14K
/// unknown->SAT 7s, cbd09330 8.7K unknown->SAT 15s, 46a8727e 15K 5.8x,
/// e7addace 19K 2.1x, 9dcbf221 91K 2x, 5246b7b9 19K 2.5x, 546f8e06 147K
/// flat), while every lost solve and slowdown sits at >= 184K vars
/// (f406e2b8 184K SAT->unknown, c7ee9446 291K SAT->unknown, fc67d414
/// 842K UNSAT->unknown, 24bde22f 292K 2.2x slower, 18d41243 507K 1.4x).
/// Mechanism: the effective eliminator is the preprocess fastelim pass
/// (growth bound 8), which skip_expensive gates at <= 200K vars; above
/// that only interval-scheduled inproc BVE runs and its growth-bound
/// fixpoint reaches 0.2-1.7% elimination on the huge Cluster-C instances
/// (vs kissat's 49-93%) — all perturbation, no payoff. 150K keeps a
/// margin below both the 200K preprocess gate and the first measured
/// loss (184K). Tunable via --sat-bve-sparse-max-vars.
const BVE_SPARSE_MAX_VARS: usize = 150_000;
/// Small-circuit BVE arm: variable-count cap (second arm of
/// `sparse_band_bve_unlock_active`, 2026-08-21 barrel6 gap fix).
///
/// The 2026-06-04 reconstruction clamp turned BVE off on the whole Default
/// DIMACS route; the 2026-07-08 sparse-band unlock restored it only for
/// density <= 12. That left a gap for SMALL structured circuit instances
/// just above the sparse edge: cmu-bmc-barrel6 (248 vars, 3729 clauses,
/// density 15.04) — the BVE-effectiveness floor benchmark (#3464, CaDiCaL
/// eliminates 25 vars there; AY eliminates 62 once BVE runs, sound UNSAT in
/// <0.3s) — got ZERO eliminations because no route ever armed
/// `features.bve`. This arm re-opens BVE for tiny formulas only:
/// `num_vars <= 10_000 && density <= BVE_SMALL_CIRCUIT_MAX_DENSITY`.
///
/// Cost is bounded: at <= 10K vars x density <= 16 the formula is <= 160K
/// clauses, and the preprocess fastelim walls (#8448 deadline,
/// FASTELIM_WALL_CLOCK_LIMIT_SECS) plus the productivity backoff
/// (#8135/#8482) bound the pass. Verdict safety is unchanged: the braun.11
/// FINALIZE_SAT_FAIL root cause was fixed (ef818369) before the 2026-07-08
/// default flip, and the LRAT route stays fail-closed (the arm sits after
/// the `VariantProofMode::Lrat` refusal). `--sat-no-bve-sparse` kills both arms.
const BVE_SMALL_CIRCUIT_MAX_VARS: usize = 10_000;
/// Small-circuit BVE arm: density cap.
///
/// 16.0 includes the barrel/BMC circuit class (cmu-bmc-barrel6 at 15.04)
/// while staying below the first documented small-dense BVE loss,
/// clique_n2_k10 (180 vars, 3160 clauses, density 17.6 — the 1409->148K
/// resolvent-blowup instance). The other documented losses are excluded by
/// the var cap or far denser: Schur_161_5 (density 37), shuffling-2 (138K
/// vars, density 33.8), d421913d (60K vars, density 40).
const BVE_SMALL_CIRCUIT_MAX_DENSITY: f64 = 16.0;
/// Giant raw-BVE band (lever 3, 2026-07-11 sparse-prize completion round;
/// `AY_AB_BVE_GIANT_RAW`, see `bve_giant_raw_route_active`).
///
/// Variable-count ceiling: 2M — deliberately equal to
/// AUTO_CONGRUENCE_MAX_VARS, the AUTO collapse probe cap. The band is
/// exactly "the probe RAN and found no substitution structure": above the
/// probe caps the probe never executes, so "no collapse" was never
/// established there and the giant SAT controls live there untouched —
/// 4d6e18e5 (7.3M vars / 40.7M clauses, density 5.6, SAT held on main) and
/// 00fd8ac9 (23.4M vars / 63M clauses, density 2.7, SAT held on main) are
/// excluded by construction by BOTH ceilings. The measured target 9d7caee5
/// (1.69M vars / 5.96M clauses, density 3.5, kissat unsat@66s via 93%
/// elimination, AY unknown@120s on main) sits inside with headroom.
const BVE_GIANT_RAW_MAX_VARS: usize = 2_000_000;
/// Clause-count ceiling for the giant raw-BVE band: 10M, re-pinned from 8M to
/// `AUTO_CONGRUENCE_GIANT_MAX_CLAUSES` (2026-08-26).
///
/// The ceiling's whole justification is "equal to the AUTO collapse probe
/// clause cap, for the same probe-reachable-band reason as
/// `BVE_GIANT_RAW_MAX_VARS`" — the band is meant to be exactly the region
/// where the probe RAN and found no substitution structure. It was written
/// against `AUTO_CONGRUENCE_MAX_CLAUSES` (8M); the probe band was subsequently
/// raised to the giant band `AUTO_CONGRUENCE_GIANT_MAX_VARS` /
/// `AUTO_CONGRUENCE_GIANT_MAX_CLAUSES` (4M/10M, default ON off the proof path)
/// and this constant was never re-pinned, so it silently stopped meaning what
/// its own doc comment says.
///
/// The 2M-clause gap is not academic: the `cabp-V-nos6` family (1,529,550 vars
/// / 8,599,702 clauses, density 5.6 — SAT, kissat solves it, AY returns
/// `bve_eliminated: 0` and `factor_count: 0`) sits inside the raised probe
/// band and just outside the stale 8M ceiling, so it was refused here even
/// with the route armed. 10M admits it; the `cabp-X-can__715` family (13.7M -
/// 14.0M clauses) stays out of band, as does everything above the probe caps.
///
/// The O(active_clauses) occ-list rebuild + GC bound the original comment
/// cites is still enforced by the 2M `BVE_GIANT_RAW_MAX_VARS` ceiling, which
/// is deliberately NOT moved: that is what keeps the giant SAT floor controls
/// 4d6e18e5 (7.3M vars / 40.7M clauses) and 00fd8ac9 (23.4M vars / 63M
/// clauses) excluded by construction. Inert unless `--sat-bve-giant-raw true`
/// arms the route (`bve_giant_raw_route_active` refuses before reading it).
const BVE_GIANT_RAW_MAX_CLAUSES: usize = 10_000_000;
/// Default for the giant raw-BVE route arm (`--sat-bve-giant-raw`): OFF.
///
/// See `SatAbSwitches::bve_giant_raw` for why the route is compiled live again
/// and why it nonetheless still ships off.
const BVE_GIANT_RAW_ROUTE_DEFAULT: bool = false;
const DIMACS_PROOF_REDUCED_EFFORT_MIN_VARS: usize = 5_000;
/// Official Main LRAT full preprocessing remains enabled for small/moderate
/// formulas where adaptive symmetry/preprocessing wins matter, but is skipped
/// for large or unknown formulas where the full prepass has been tail-prone.
const OFFICIAL_MAIN_LRAT_FULL_PREPROCESS_MAX_VARS: usize = 50_000;
const OFFICIAL_MAIN_LRAT_FULL_PREPROCESS_MAX_CLAUSES: usize = 250_000;
/// Probe profile MAB epochs should be short enough to react inside Luby windows.
const PROBE_MAB_EPOCH_MIN_CONFLICTS: u64 = 64;
/// Official Main/default/LRAT uses the AE-Kissat MAB epoch default: long enough
/// to avoid noisy scoring, short enough to adapt inside stable phases.
const OFFICIAL_MAIN_LRAT_MAB_EPOCH_MIN_CONFLICTS: u64 =
    crate::mab::DEFAULT_HEURISTIC_EPOCH_MIN_CONFLICTS;
/// Small dense Main/LRAT formulas keep the legacy focused/stable branch coupling.
/// This matches the existing small-dense CDCL tuning threshold in solve/mod.rs.
const OFFICIAL_MAIN_LRAT_LEGACY_BRANCH_MAX_VARS: usize = 1000;
const OFFICIAL_MAIN_LRAT_LEGACY_BRANCH_MIN_RATIO: f64 = 10.0;
/// Exact proof-safe detector surface for the dense-clique/mutex W5 specialist.
///
/// This only classifies the route. It must not enable destructive
/// preprocessing for official Main/LRAT unless the transform has checked proof
/// emission for the original instance.
const OFFICIAL_MAIN_LRAT_DENSE_CLIQUE_MUTEX_MAX_VARS: usize = 512;
const OFFICIAL_MAIN_LRAT_DENSE_CLIQUE_MUTEX_MIN_RATIO: f64 = 10.0;
const OFFICIAL_MAIN_LRAT_DENSE_CLIQUE_MUTEX_MIN_BINARY_FRAC: f64 = 0.95;
const OFFICIAL_MAIN_LRAT_DENSE_CLIQUE_MUTEX_MIN_HORN_FRAC: f64 = 0.95;
const OFFICIAL_MAIN_LRAT_DENSE_CLIQUE_MUTEX_MIN_LONG_CLAUSE: usize = 8;
const OFFICIAL_MAIN_LRAT_DENSE_CLIQUE_MUTEX_MAX_POS_BALANCE: f64 = 0.15;
const DENSE_MUTEX_FOCUSED_RESTART_MAX_VARS: usize = 1000;
const DENSE_MUTEX_FOCUSED_RESTART_MIN_RATIO: f64 = 10.0;
const DENSE_MUTEX_FOCUSED_RESTART_MIN_BINARY_FRAC: f64 = 0.95;
/// Mid-band deep-restart gate (xor-heavy batch-3 root cause, 2026-07;
/// kill-switch `--sat-no-midband-deep-restart`, see
/// [`VariantConfig::apply_midband_deep_restart_gate`]).
///
/// The 100K–1M-clause gate-dense (bin+ternary >= 85%) class keeps the hot
/// Glucose/stable-EMA restart regime that forfeits deep-plunge search:
/// the >1M-clause band already gets Luby-like depth and the <1K-var dense
/// band already disables the stable-EMA gate (#8655), but the mid band kept
/// 1-restart-per-30-conflicts churn. Measured on 557d7d4d (57,935 vars /
/// 229,320 cls, 87% bin+ternary, avg_lbd 34): default UNKNOWN@300s with
/// 52,178 restarts (stable-EMA fired 22,694x vs 431 reluctant); the single
/// delta Default+Luby{250} flips it to SAT@86-87s twice (restarts 52,178 ->
/// 986, model externally validated against the original CNF both times).
/// Conflict throughput is at kissat parity — the forfeit is purely the
/// restart regime, so the gate swaps ONLY the restart policy (focused =
/// Luby, stable = pure reluctant; branching/features stock).
const MIDBAND_DEEP_RESTART_MIN_CLAUSES: usize = 100_000;
/// Upper clause bound of the mid band. The root-cause class extends to 1M
/// clauses (where the >1M band's deep regime starts), but the CLI's
/// streaming DIMACS parser takes over at STREAMING_CLAUSE_THRESHOLD=500K and
/// bypasses the SatFeatures profile plan entirely, so nothing above 500K is
/// reachable by this gate today. The ceiling is pinned to 500K so the
/// DECLARED band equals the MEASURED band: the 500K–1M gap (which holds
/// un-remeasured floor instances like f5c12b1e at 863K cls, bin+tern 0.91)
/// stays stock even if the streaming path later becomes feature-aware —
/// widening the band must be an explicit, floor-gated constant change.
const MIDBAND_DEEP_RESTART_MAX_CLAUSES: usize = 500_000;
/// Gate-dense signature: bin+ternary clause fraction (557d7d4d = 0.872; the
/// declined-XOR-extension mid band this targets is ANDed with the clause
/// floor above, which sits over XOR_EXTENSION_MAX_CLAUSES=50K by
/// construction).
const MIDBAND_DEEP_RESTART_MIN_BIN_TERN_FRAC: f64 = 0.85;
/// Clause/var ratio ceiling for the mid band, measured floor-gate exclusion
/// (2026-07-16 G4 sweep): 6f354fbea13b25a4 (48,032 vars / 448,719 cls, ratio
/// 9.34, bin+tern 0.90) passes the clause+frac arms but LOSES under the deep
/// regime — UNSAT@101s on stock Glucose vs UNKNOWN@120s under Luby, twice
/// (2.1M conflicts, gate confirmed firing via stable_ema_rst=0). The
/// gate-dense XOR-extraction class this gate targets encodes ~4 clauses per
/// 3-input gate with gate count ~ vars (557d7d4d ratio = 3.96); ratio >= 8
/// in this band signals a constraint-dense class where the frequent-restart
/// Glucose regime already wins. 6.0 keeps 1.5x headroom over the measured
/// flip and a 1.36x margin under the measured loss (f5c12b1e, the next
/// lowest at 8.14, is above the 500K ceiling anyway).
const MIDBAND_DEEP_RESTART_MAX_CLAUSE_VAR_RATIO: f64 = 6.0;
/// Lower ratio edge (2026-07-16 interaction fix): 3ef7fa06 (256,580c/87,738v,
/// r2.92, gate-dense UNSAT) is Luby-HOSTILE — the gate turned its
/// equiticks-only UNSAT@74-91s flip into UNKNOWN@120s (measured: gate ON +
/// equiticks OFF also UNKNOWN, so Luby itself is the harm). 557d7d4d (r3.96,
/// the gate's measured flip) sits above 3.5; 70da0b78 (r2.8) and 96dea345
/// exit the band back to stock, where both already solve (0.9s / 14.5s).
const MIDBAND_DEEP_RESTART_MIN_CLAUSE_VAR_RATIO: f64 = 3.5;
/// Luby base for the mid-band deep regime — identical to the Probe variant's
/// measured base (and the flip measurement's exact delta).
const MIDBAND_DEEP_RESTART_LUBY_BASE: u64 = 250;

impl VariantConfig {
    /// Formula and route metadata used to resolve this configuration.
    #[must_use]
    pub const fn input(&self) -> VariantInput {
        self.input
    }

    /// Resolve a preset into concrete solver settings.
    #[must_use]
    pub fn for_variant(variant: SolverVariant, input: VariantInput) -> Self {
        let mut config = match variant {
            SolverVariant::Default => Self {
                variant,
                input,
                full_preprocessing: false,
                restart_policy: VariantRestartPolicy::Glucose,
                branch_policy: VariantBranchPolicy::LegacyCoupled,
                features: dimacs_baseline_features(),
                hot_path: VariantHotPathConfig::default(),
            },
            SolverVariant::Aggressive => Self {
                variant,
                input,
                full_preprocessing: true,
                restart_policy: VariantRestartPolicy::Glucose,
                branch_policy: VariantBranchPolicy::LegacyCoupled,
                features: dimacs_baseline_features(),
                hot_path: VariantHotPathConfig::default(),
            },
            SolverVariant::Minimal => Self {
                variant,
                input,
                full_preprocessing: false,
                restart_policy: VariantRestartPolicy::Glucose,
                branch_policy: VariantBranchPolicy::LegacyCoupled,
                features: minimal_features(),
                hot_path: VariantHotPathConfig::default(),
            },
            SolverVariant::Probe => Self {
                variant,
                input,
                full_preprocessing: false,
                restart_policy: VariantRestartPolicy::Luby { base: 250 },
                branch_policy: VariantBranchPolicy::MabUcb1 {
                    epoch_min_conflicts: PROBE_MAB_EPOCH_MIN_CONFLICTS,
                },
                features: probe_features(),
                hot_path: VariantHotPathConfig::default(),
            },
            SolverVariant::Custom(profile) => Self {
                variant,
                input,
                full_preprocessing: profile.preprocess,
                restart_policy: VariantRestartPolicy::Glucose,
                branch_policy: VariantBranchPolicy::LegacyCoupled,
                features: profile,
                hot_path: VariantHotPathConfig::default(),
            },
        };

        if let Some(proof_mode) = input.capability_mode() {
            config.clamp_for_proof_mode(proof_mode);
        }
        config.apply_startup_policy();
        config.apply_route_profile_clamps();
        config.apply_ab_substitution_knob();
        config.apply_ab_bve_knob();
        config.hot_path = VariantHotPathConfig::for_variant_input(variant, input);

        config
    }

    /// A/B measurement knob (campaign #15): force equivalent-literal
    /// substitution on the Default variant so decompose (SCC over the binary
    /// implication graph) and congruence (gate equivalences) can be measured
    /// against the baseline WITHOUT switching to the probe variant (which also
    /// changes restart/branching). Applied LAST so the EXPLICIT knobs win over
    /// the dense/proof clamps for a clean isolated measurement.
    ///
    ///   (retired B36)   -> features.decompose = true
    ///   (retired B36)  -> features.congruence = true (implies decompose)
    ///   --sat-no-subst-auto    -> route-aware AUTO, see
    ///                          [`Self::subst_auto_collapse_enabled`]:
    ///                          DEFAULT ON (unset) with kill-switch =0;
    ///                          explicit =1 keeps the historical measurement
    ///                          semantics (wins over the proof clamps).
    ///
    /// Proof-capability note (2026-07-10): BOTH Decompose (2026-07-09) and
    /// Congruence (2026-07-10, wf_ff5991a1 — complementary-edge and
    /// vivify-husk fixes, externally verified) are DRAT-open in the registry;
    /// no --sat-no-drat-subst needed, kill-switch --sat-no-drat-subst. LRAT
    /// stays fail-closed for both (see proof_capability.rs). The AUTO DEFAULT
    /// now matches registry truth (ON under DRAT, OFF under LRAT) since
    /// wf_0c7d84e9 fixed and externally re-verified the f0bafebd emission —
    /// see [`Self::subst_auto_collapse_enabled`].
    fn apply_ab_substitution_knob(&mut self) {
        if !matches!(self.variant, SolverVariant::Default) {
            return;
        }
        // B36: the (retired B36)/(retired B36) force-enables are gone —
        // they were redundant measurement shims over this default-ON AUTO
        // path (and the proof registry still clamps either feature under a
        // proof surface regardless).
        if self.subst_auto_collapse_enabled() {
            self.features.decompose = true;
            self.features.congruence = true;
        }
    }

    /// Route-aware substitution-collapse AUTO (#15): congruence+decompose
    /// eligibility on the Default DIMACS variant, with config_preprocess
    /// gating the EXPENSIVE fixpoint on a one-round equivalence-density probe
    /// (substitution-heavy instances collapse; general instances pay only the
    /// single probe round then bail — the measured default-on regression
    /// (general 8→7) from UNCONDITIONAL collapse is why the probe gate
    /// exists).
    ///
    /// DEFAULT ON since 2026-07-10 (collapse+BVE default flip, wf_55735963;
    /// measurement wf_2ee873fc/wf_0552d0f0): scoreboard protocol
    /// (`--competition`, 120s, no proof, main2025) with the 3-knob stack
    /// (SUBST_AUTO + BVE_POST_COLLAPSE + BVE_SPARSE_DEEP) measured **+7
    /// kissat-agreeing UNSAT flips** (df813fe7 80s/188K elims, 6f354fbe,
    /// d88a8a62, 0205e2df, f5c12b1e, 70da0b78 1.8s, 96dea345 pure-congruence)
    /// at sparse density 2.3–9.3, **0 hard lost solves**, dense band (3/3)
    /// provably inert (probe bails, walls <=1s noise), and bounded wall drags
    /// on kept solves (worst 0e1d5620 +50s with 61s margin; prior fdefca5f
    /// catastrophic regression is gone post fast-inner, now +11s).
    ///
    ///   unset -> ON for non-proof AND DRAT-proof solves; OFF (fail-closed)
    ///            only under LRAT — i.e. registry truth (Congruence/
    ///            Decompose { drat: true, lrat: false }).
    ///
    /// HISTORY of the stricter any-proof fail-closed (2026-07-10,
    /// wf_55735963 -> lifted by wf_0c7d84e9 the same day): the G4 re-check
    /// found a congruence/decompose-active DRAT emission on main2025
    /// f0bafebd that dpr-trim REJECTED ("RAT check on proof pivot failed:
    /// [51477] 1163 -2820", proof line 26774) while the identical solve with
    /// --sat-no-subst-auto verified end-to-end. wf_0c7d84e9 root-caused it to
    /// congruence XOR-ladder rungs watched as BINARY clauses (proof_ladder.rs
    /// insert_ladder_rung: a deleted rung husk kept its binary watch and
    /// vivify propagated a proof-less level-0 unit that
    /// collect_level0_garbage baked into strengthened clauses), fixed the
    /// emission, pinned the class with a debug_assert in
    /// attach_clause_watches + a ladder unit test, and re-verified externally
    /// (dpr-trim, cake_lpr on 3): f0bafebd, braun10/12, and EVERY collapse
    /// flip that finishes under proof with the proof-scaled BVE walls
    /// (96dea345, 6f354fbe, 0205e2df, f5c12b1e, d88a8a62) — all s VERIFIED,
    /// kissat agreement everywhere. With PROOF_WALL_BUDGET_SCALE those flips
    /// now materialize under --proof, so the DRAT default trades nothing
    /// away.
    ///   =1    -> ON with the historical explicit-measurement semantics
    ///            (wins over the proof clamps; probe-script compat and the
    ///            switch for future proof-route emission work).
    ///   =0    -> kill-switch OFF (restores the pre-flip opt-in profile).
    ///            Any other explicit value also disables (conservative,
    ///            matching the old `=1`-only opt-in parse).
    ///
    /// Also mirrored into the solver as `cold.subst_auto_collapse` (see
    /// `VariantConfig::apply_to_solver`) so the preprocess probe gate and the
    /// raised congruence caps stay scoped to exactly this resolved config
    /// rather than re-reading the env in variant-blind solver code.
    pub(crate) fn subst_auto_collapse_enabled(&self) -> bool {
        if !matches!(self.variant, SolverVariant::Default) {
            return false;
        }
        match Self::subst_auto_env_explicit() {
            Some(on) => on,
            // Default-ON path: registry truth — ON for non-proof and DRAT
            // solves, fail-closed only under LRAT (Congruence/Decompose ship
            // { drat: true, lrat: false }). The stricter any-proof refusal
            // was lifted by wf_0c7d84e9 after the f0bafebd emission fix was
            // externally re-verified end-to-end; see the doc above.
            None => !matches!(self.input.proof_mode(), VariantProofMode::Lrat),
        }
    }

    /// Cached explicit `--sat-no-subst-auto` parse: `Some(true)` for `=1`,
    /// `Some(false)` for any other explicit value (kill-switch semantics),
    /// `None` when unset (the DEFAULT-ON path). Cached OnceLock per the
    /// #8506 no-per-call-syscall convention.
    fn subst_auto_env_explicit() -> Option<bool> {
        // B34: CLI-owned. `--sat-no-subst-auto` is the kill (Some(false));
        // `--sat-subst-auto-uncapped` keeps the historical explicit-on
        // UNCAPPED measurement semantics (Some(true)); default None.
        let s = ay_core::sat_ab_switches();
        if s.no_subst_auto {
            Some(false)
        } else if s.subst_auto_uncapped {
            Some(true)
        } else {
            None
        }
    }

    /// Dense-band guard rails for the AUTO collapse path (2026-07-11
    /// dense-band regression fix): true iff AUTO is on via the DEFAULT path
    /// (`--sat-no-subst-auto` unset). Arms the EARLY formula-density disarm in
    /// compute_preprocess_policy and the giant decompose re-run bail in
    /// inprocessing_schedule (see `cold.subst_auto_capped` for the
    /// certified remeasure2 measurement: dense 23→19, casualties 43fbacb2 +
    /// 0ec8c5e9 recovered by the guards). Explicit `--sat-no-subst-auto=1`
    /// keeps the historical UNCAPPED measurement semantics — this returns
    /// false there so A/B probe scripts see today's behavior unchanged.
    pub(crate) fn subst_auto_collapse_capped(&self) -> bool {
        self.subst_auto_collapse_enabled() && Self::subst_auto_env_explicit().is_none()
    }

    /// Giant-band AUTO probe raise (giant-3M loss fix, 2026-07): true iff
    /// the raised 4M/10M probe caps + 12s in-band preprocess budget are
    /// armed for this resolved config — see `AUTO_CONGRUENCE_GIANT_MAX_VARS`
    /// for the full measurement (5ceb95f5 SAT@62.0s beating kissat's 82.8s,
    /// bonus flip ac388757 SAT@58.6s/51.8s, models independently validated;
    /// zero regressions across the whole admitted band).
    ///
    /// Scope (each arm load-bearing):
    ///   - DEFAULT-ON capped path only (`subst_auto_collapse_capped`):
    ///     explicit `--sat-no-subst-auto=1` keeps the historical 2M/8M
    ///     measurement semantics, and `--sat-no-subst-auto` kills the whole
    ///     AUTO stack including this band.
    ///   - NON-PROOF only (`VariantProofMode::Disabled`): under DRAT the congruence
    ///     proof ladder RUP-probes per edge (~10.4K edges/s measured); the
    ///     1.31M-edge giant closures would burn >115s emitting the proof, so
    ///     proof solves keep the 2M/8M band bit-for-bit. AUTO already
    ///     fail-closes under LRAT. The scoreboard protocol is non-proof.
    ///   - Kill-switch `AY_AB_SUBST_AUTO_GIANT=0` (any explicit value other
    ///     than `1` disables, matching the AUTO knob's conservative parse;
    ///     unset = ON per the measured +2 flips / 0 floor losses).
    pub(crate) fn subst_auto_giant_band_active(&self) -> bool {
        self.subst_auto_collapse_capped()
            && matches!(self.input.proof_mode(), VariantProofMode::Disabled)
            && Self::subst_auto_giant_env_enabled()
    }

    /// Cached `AY_AB_SUBST_AUTO_GIANT` parse: ON when unset or `=1`, OFF for
    /// any other explicit value (kill-switch semantics, conservative parse
    /// matching `--sat-no-subst-auto`). Cached OnceLock per the #8506
    /// no-per-call-syscall convention.
    fn subst_auto_giant_env_enabled() -> bool {
        // B21: the AY_AB_SUBST_AUTO_GIANT kill-switch is retired (never set;
        // the giant band stays independently guarded by its own registry
        // clamps). Always on.
        true
    }

    /// Sparse-band BVE unlock (#sparse-gap Cluster C, default ON since
    /// 3c9b980b).
    ///
    /// HISTORY: default-on was originally blocked by a measured braun
    /// FINALIZE_SAT_FAIL (eq.atree.braun.11.unsat: reconstruction FLIP at a
    /// witness entry left original clause [-1419, 1449] unsatisfied;
    /// fail-closed gate degraded to Unknown — no wrong verdict). ef818369
    /// root-caused it to preprocess-subsume constraint loss (a learned
    /// subsumer was not promoted to irredundant before the irredundant
    /// original was deleted — fixed in config_preprocess_cleanup.rs), NOT to
    /// BVE reconstruction itself. With the fix, the group_misc
    /// finalize_sat_fail audit (incl. braun_family_no_finalize_sat_fail)
    /// passes and 3c9b980b flipped the default to ON; re-confirmed green
    /// 2026-07-09 during the decompose DRAT-unclamp probes.
    ///
    /// Measured same-binary A/B with the unlock ON (2026-07-08, main2025,
    /// 120s, in-band = density<=12 && vars<=150K): +2 solves (0e1d5620
    /// unknown->SAT 7s with 5980 vars eliminated; cbd09330 unknown->SAT
    /// 15s), 0 lost solves, speedups up to 5.8x (46a8727e 66s->11s,
    /// e7addace 96s->45s, 5246b7b9 12s->5s), and 3 externally-validated
    /// SAT models on BVE-exercised runs.
    ///
    /// The Default DIMACS profile ships `bve: false` (see
    /// `dimacs_baseline_features`), so on the plain/DRAT route BVE never
    /// fires: preprocess BVE returns immediately and the inprocessing gate
    /// reports `BveSkipReason::DisabledFlag` every round. Kissat wins a
    /// cluster of sparse instances (density 3.1-11.3) purely by eliminating
    /// 49-93% of variables. This knob flips `features.bve = true` for the
    /// Default variant ONLY inside the sparse band
    /// (clauses/vars <= BVE_SPARSE_MAX_DENSITY and num_vars <=
    /// BVE_SPARSE_MAX_VARS — see that constant for the measured win/loss
    /// size split) or the small-circuit arm (num_vars <=
    /// BVE_SMALL_CIRCUIT_MAX_VARS and density <=
    /// BVE_SMALL_CIRCUIT_MAX_DENSITY — the #3464 barrel6 gap fix), leaving
    /// dense formulas — the entire historical BVE loss set — and huge
    /// formulas at today's behavior.
    ///
    /// Proof safety: BVE is DRAT-legal in PROOF_CAPABILITY_REGISTRY
    /// (`Bve { drat: true, lrat: false }`), so the default DRAT route needs
    /// no proof change. The official LRAT route is excluded here explicitly
    /// (and `with_proof_overrides` re-clamps BVE on LRAT anyway, fail-closed).
    /// Runtime cost stays bounded by the existing guards: skip_bve_dense,
    /// clause-growth inhibit (BVE_GROWTH_INHIBIT_FACTOR), proportional
    /// transred guard, inprocessing round wall limit, and
    /// DIMACS_REDUCED_EFFORT_BVE for >5K-var formulas. Verdicts remain
    /// guarded by the independent model-validation gate and DRAT
    /// verification — this changes scheduling/completeness only.
    ///
    ///   unset / --sat-no-bve-sparse=1    -> scoped unlock ACTIVE (default)
    ///   --sat-no-bve-sparse            -> kill-switch (pre-unlock behavior)
    ///   --sat-bve-sparse-max-density=<f> -> tune the band edge (default 12.0)
    ///   --sat-bve-sparse-max-vars=<n>    -> tune the size cap (default 150000)
    ///
    /// Cached per-process like the other AY_AB_* knobs.
    fn apply_ab_bve_knob(&mut self) {
        if self.sparse_band_bve_unlock_active() {
            self.features.bve = true;
        }
    }

    /// Whether the sparse-band BVE unlock applies to this route/input.
    ///
    /// (Measured 2026-07-08 on the Cluster-C set: raising the in-band BVE
    /// effort from DIMACS_REDUCED_EFFORT_BVE=100 to full 1000 permille left
    /// eliminated-variable counts byte-identical on all 6 instances — the
    /// growth-bound fixpoint is the binding constraint, not effort — so the
    /// unlock intentionally leaves the effort reduction untouched.)
    fn sparse_band_bve_unlock_active(&self) -> bool {
        if !matches!(self.variant, SolverVariant::Default) {
            return false;
        }
        // Fail-closed on LRAT: the official submission route keeps BVE
        // opt-in via the LRAT-only scout knobs (config_preprocess_bve.rs).
        if matches!(self.input.proof_mode(), VariantProofMode::Lrat) {
            return false;
        }
        use std::sync::OnceLock;
        static ENABLED: OnceLock<bool> = OnceLock::new();
        let enabled = *ENABLED.get_or_init(|| {
            // Default ON; `--sat-no-bve-sparse` is the kill switch (B34).
            !ay_core::sat_ab_switches().no_bve_sparse
        });
        if !enabled {
            return false;
        }
        if self.input.num_vars() == 0 {
            return false;
        }
        let max_vars = ay_core::sat_ab_switches()
            .bve_sparse_max_vars
            .filter(|value| *value > 0)
            .unwrap_or(BVE_SPARSE_MAX_VARS);
        if self.input.num_vars() > max_vars {
            return false;
        }
        let max_density = ay_core::sat_ab_switches()
            .bve_sparse_max_density
            .filter(|value| value.is_finite() && *value > 0.0)
            .unwrap_or(BVE_SPARSE_MAX_DENSITY);
        let density = self.input.num_clauses() as f64 / self.input.num_vars() as f64;
        if density <= max_density {
            return true;
        }
        // Small-circuit arm (#3464 barrel6 gap fix): tiny formulas just
        // above the sparse density edge. Fixed-edge by design (the
        // --sat-bve-sparse-* tunables scope the sparse arm only);
        // `--sat-no-bve-sparse` kills both arms via the shared gate above.
        // See BVE_SMALL_CIRCUIT_MAX_VARS / BVE_SMALL_CIRCUIT_MAX_DENSITY.
        self.input.num_vars() <= BVE_SMALL_CIRCUIT_MAX_VARS
            && density <= BVE_SMALL_CIRCUIT_MAX_DENSITY
    }

    /// Giant raw-BVE unlock route/band predicate (lever 3, 2026-07-11
    /// sparse-prize completion round; kill-switch `AY_AB_BVE_GIANT_RAW=0`).
    ///
    /// The sparse-band unlock stops at 150K vars and the post-collapse
    /// unlock requires substitution structure, so an elimination-shaped
    /// giant with probe equivalence density 0 has NO BVE route at all:
    /// 9d7caee5 (1.69M vars, 5.96M clauses, density 3.5) is solved by kissat
    /// unsat@66s via 93% elimination while AY reaches <1% through
    /// interval-scheduled inproc BVE and stays unknown@120s. This predicate
    /// arms the ROUTE flag for the deep raw-BVE band:
    ///
    ///   Default DIMACS non-LRAT route (same fail-closed scoping as the
    ///   sparse-band unlock), AY_AB_BVE_GIANT_RAW not killed,
    ///   BVE_SPARSE_MAX_VARS(150K) < parsed vars <= BVE_GIANT_RAW_MAX_VARS(2M),
    ///   parsed clauses <= BVE_GIANT_RAW_MAX_CLAUSES(8M),
    ///   parsed density <= BVE_SPARSE_MAX_DENSITY(12) —
    ///
    /// i.e. the sparse-band predicate without its 150K ceiling, capped to
    /// the AUTO-probe-reachable region (see the two ceiling constants: the
    /// currently-SAT giant controls 4d6e18e5/00fd8ac9 are out-of-band by
    /// construction). Qualification is completed at preprocess time by
    /// `Solver::try_qualify_bve_giant_raw` — the collapse must have
    /// substituted NOTHING (collapsed instances stay on the measured
    /// post-collapse path) and the live dense-skip guard is re-checked.
    /// Runtime cost is bounded by the deep sparse budgets this band arms
    /// (BVE_SPARSE_DEEP_* walls/rounds/effort via `bve_sparse_deep_active`);
    /// verdicts stay guarded by the model-validation gate and DRAT
    /// verification — scheduling/eligibility only.
    ///
    /// DEFAULT OFF (2026-07-11 measurement, this round): the unlock arms
    /// and works as designed on the target — 9d7caee5 gets 72,225
    /// preprocess eliminations (~4.3%) in a 7.1s deep pass where main has
    /// NO route at all — but the instance does not flip (verdict
    /// UNKNOWN@120s before and after): its resolution profile is
    /// tautology-heavy (4.1M tautologies, ~330 resolutions/elimination), so
    /// elimination throughput is ~10-20K/s here, structurally short of the
    /// 93% kissat reaches within budget. The giant controls
    /// (4d6e18e5/00fd8ac9 SAT, 0ec8c5e9 SAT) all HELD, so there is no
    /// regression — but the lever spends ~5-7s of wall on every in-band
    /// no-collapse instance and the in-band population beyond the measured
    /// targets/controls is unswept, so per the round's gate ("default-ON
    /// only with clean evidence") it ships opt-in:
    ///
    ///   --sat-bve-giant-raw true  -> route armed (opt-in)
    ///   unset / =false            -> inert (default)
    ///
    /// B21 (`d2bd18e6e2`) had hard-wired this predicate to `return false` as
    /// part of the env-flag retirement sweep, filed under "measured-negative
    /// opt-ins made compiled-inert". Re-read against its own evidence that
    /// label is too strong: neither measurement ever attributed a loss to the
    /// route — `877271de86` recorded "does not flip, controls HELD, no
    /// regression" and `d47bf815de` recorded "neither flips (search-bound)" —
    /// and both were taken on `9d7caee5`/`ac388757` while PAIRED with the
    /// additive Pass-1 fastelim budget that has since shipped default-ON above
    /// 200K vars. The arm is therefore back as a sweepable
    /// `--sat-bve-giant-raw` opt-in (still DEFAULT OFF: nothing here is new
    /// positive evidence, only an argument that the negative was never
    /// established).
    fn bve_giant_raw_route_active(&self) -> bool {
        if !matches!(self.variant, SolverVariant::Default) {
            return false;
        }
        // Fail-closed on LRAT (same scoping as sparse_band_bve_unlock_active).
        if matches!(self.input.proof_mode(), VariantProofMode::Lrat) {
            return false;
        }
        if !ay_core::sat_ab_switches()
            .bve_giant_raw
            .unwrap_or(BVE_GIANT_RAW_ROUTE_DEFAULT)
        {
            return false;
        }
        // Band ceilings. The VAR ceiling is untouched at 2M — it is what keeps
        // the giant SAT floor controls 4d6e18e5 (7.3M vars) and 00fd8ac9
        // (23.4M vars) out of band by construction. The CLAUSE ceiling is
        // re-pinned to the AUTO probe band that shipped after this predicate
        // was written; see BVE_GIANT_RAW_MAX_CLAUSES.
        let max_vars = BVE_GIANT_RAW_MAX_VARS;
        let max_clauses = BVE_GIANT_RAW_MAX_CLAUSES;
        if self.input.num_vars() <= BVE_SPARSE_MAX_VARS
            || self.input.num_vars() > max_vars
            || self.input.num_clauses() > max_clauses
        {
            return false;
        }
        let density = self.input.num_clauses() as f64 / self.input.num_vars() as f64;
        density <= BVE_SPARSE_MAX_DENSITY
    }

    /// Stable external preset name.
    #[must_use]
    pub const fn name(self) -> &'static str {
        self.variant.as_str()
    }

    /// Stable executable name for this preset.
    #[must_use]
    pub const fn binary_name(self) -> &'static str {
        self.variant.binary_name()
    }

    /// Apply the resolved config to a solver instance.
    ///
    /// Intended for fresh solvers before clauses are added. Frontend debug
    /// overrides should run after this so bisection flags still win.
    pub fn apply_to_solver(&self, solver: &mut Solver) {
        let input = self.input;
        let num_vars = input.num_vars();
        let num_clauses = input.num_clauses();
        let official_main_lrat_default = is_official_main_lrat_default_route(self.variant, input);
        let official_main_lrat_exceeds_full_preprocess_cutoff = official_main_lrat_default
            && (num_vars > OFFICIAL_MAIN_LRAT_FULL_PREPROCESS_MAX_VARS
                || num_clauses > OFFICIAL_MAIN_LRAT_FULL_PREPROCESS_MAX_CLAUSES);

        // Keep moderate DIMACS full preprocessing, but avoid it on multi-million-clause CNF.
        let full_preprocessing = match self.variant {
            SolverVariant::Default if official_main_lrat_default => {
                num_vars > 0
                    && num_clauses > 0
                    && num_vars <= OFFICIAL_MAIN_LRAT_FULL_PREPROCESS_MAX_VARS
                    && num_clauses <= OFFICIAL_MAIN_LRAT_FULL_PREPROCESS_MAX_CLAUSES
            }
            SolverVariant::Default => num_clauses <= DIMACS_FULL_PREPROCESS_MAX_CLAUSES,
            _ => self.full_preprocessing,
        };
        // Apply the full feature profile via the unified setter (#8149).
        solver.apply_feature_profile(&self.features);
        if matches!(
            input.startup_policy(),
            VariantStartupPolicy::DisableWarmupWalk
        ) && matches!(self.variant, SolverVariant::Default)
            && matches!(input.proof_mode(), VariantProofMode::Lrat)
        {
            // Official Main/default/LRAT enters CDCL without allocating
            // startup-only warmup shadow watches or startup walk occurrence
            // lists. Periodic rephase walk remains enabled and tick-budgeted.
            solver.set_startup_walk_enabled(false);
            solver.set_startup_warmup_enabled(false);
        }
        solver.set_full_preprocessing(full_preprocessing);
        solver
            .set_sat_comp_main_conflict_pruning(self.hot_path.prune_conflict_analysis_experiments);
        solver.set_stable_only_rephase_enabled(self.hot_path.stable_only_rephase);
        solver.set_dense_mutex_focused_restart_gate_experiment_enabled(
            self.hot_path.dense_mutex_focused_restart_gate_experiment,
        );
        solver.set_dense_clique_mab_branch_route_enabled(
            self.hot_path.dense_clique_mab_branch_experiment,
        );
        // Sparse-band large-formula preprocess-BVE unlock (scoped + kill-switched).
        // The same predicate that flips `features.bve` on the sparse band also
        // arms the preprocess-BVE expensive-pass bypass, so preprocess
        // BVE/fastelim can run on LARGE sparse formulas (num_vars beyond the 200K
        // expensive-pass cap) when the operator raises --sat-bve-sparse-max-vars.
        // BVE-specific only: it does NOT relax skip_expensive for other passes.
        solver.set_sparse_band_bve_preprocess_unlock(self.sparse_band_bve_unlock_active());
        // Giant raw-BVE unlock ROUTE flag (lever 3, 2026-07-11 sparse-prize
        // completion round; OPT-IN via AY_AB_BVE_GIANT_RAW=1 — see
        // bve_giant_raw_route_active for the measured default-OFF call).
        // Arms the deep raw-BVE band for elimination-shaped giants the
        // sparse-band (150K ceiling) and post-collapse (requires
        // substitution structure) unlocks can never reach. Qualification
        // finishes at preprocess time (no-collapse check + live dense-skip
        // re-check) in try_qualify_bve_giant_raw.
        solver.set_bve_giant_raw_unlock(self.bve_giant_raw_route_active());
        // Route-aware substitution-collapse AUTO (default ON since 2026-07-10,
        // wf_55735963 — see subst_auto_collapse_enabled for the measurement):
        // arm the solver-side flag so the preprocess density-probe gate and
        // the raised congruence caps engage exactly for this resolved config
        // (Default DIMACS variant; kill-switch --sat-no-subst-auto), instead of
        // variant-blind env reads in solver code.
        solver.set_subst_auto_collapse(self.subst_auto_collapse_enabled());
        // Dense-band guard rails for the DEFAULT-ON AUTO path (2026-07-11
        // dense-band regression fix): early formula-density disarm + giant
        // decompose re-run bail, scoped so explicit --sat-no-subst-auto=1
        // keeps the historical uncapped A/B semantics. See
        // cold.subst_auto_capped for the measurement.
        solver.set_subst_auto_collapse_capped(self.subst_auto_collapse_capped());
        // Giant-band AUTO probe raise (giant-3M loss fix, 2026-07): raised
        // 4M/10M probe caps + 12s in-band preprocess budget, scoped to
        // NON-PROOF default-path solves only (proof runs keep 2M/8M
        // bit-for-bit — the per-edge RUP proof ladder cannot afford 1.31M-
        // edge closures). Kill-switch AY_AB_SUBST_AUTO_GIANT=0; also rides
        // --sat-no-subst-auto. See subst_auto_giant_band_active.
        solver.set_subst_auto_giant_band(self.subst_auto_giant_band_active());

        if official_main_lrat_default && input.bve_lrat_scout_route() {
            solver.set_bve_lrat_scout_route_enabled(true);
        }
        if official_main_lrat_default && input.fmla_decompose_lrat_preflight_route() {
            solver.set_fmla_decompose_lrat_preflight_route_enabled(true);
        }

        match self.restart_policy {
            VariantRestartPolicy::Glucose => solver.set_glucose_restarts(true),
            VariantRestartPolicy::Luby { base } => {
                solver.set_glucose_restarts(false);
                solver.set_restart_base(base);
            }
        }
        self.branch_policy.apply_to_solver(solver);

        if matches!(
            self.variant,
            SolverVariant::Default | SolverVariant::Aggressive
        ) {
            // CaDiCaL-style focused/stable alternation: the solver starts in
            // focused mode (glucose EMA restarts, VMTF branching) and switches
            // to stable mode (reluctant doubling, VSIDS) after the first phase.
            // This alternation is critical for SAT-COMP performance: focused
            // mode explores broadly via frequent restarts, stable mode exploits
            // via deep search. Previously AY locked to stable-only (#7905),
            // which prevented all focused-mode restarts and caused 0 restarts
            // on 60K+ conflicts during the CDCL loop.
            //
            // Reduced BVE/subsumption effort budgets are kept to avoid
            // pathological preprocessing overhead on large formulas.
            if !matches!(input.proof_mode(), VariantProofMode::Disabled) {
                if num_vars > DIMACS_PROOF_REDUCED_EFFORT_MIN_VARS {
                    solver.set_bve_effort_permille(DIMACS_REDUCED_EFFORT_BVE);
                }
                if official_main_lrat_exceeds_full_preprocess_cutoff {
                    solver.set_subsume_effort_permille(DIMACS_REDUCED_EFFORT_SUBSUME);
                }
            } else if num_vars > DIMACS_PROOF_REDUCED_EFFORT_MIN_VARS {
                // Only reduce BVE/subsumption effort on large formulas (>5K vars).
                // Small formulas (like clique 437 vars) need full BVE effort to
                // achieve high elimination rates. CaDiCaL's --sat config reduces
                // effort globally, but CaDiCaL's BVE is more efficient per-step.
                solver.set_bve_effort_permille(DIMACS_REDUCED_EFFORT_BVE);
                solver.set_subsume_effort_permille(DIMACS_REDUCED_EFFORT_SUBSUME);
            }
        }
    }

    fn clamp_for_proof_mode(&mut self, proof_mode: ProofMode) {
        // Proof variants are fail-closed for transforms without an explicit
        // checked allowlist in the shared proof-capability registry.
        proof_capability::apply_profile_permissions(&mut self.features, proof_mode);
    }

    fn apply_route_profile_clamps(&mut self) -> bool {
        if !self
            .input
            .route_profile()
            .requires_proof_safe_specialist_routing()
        {
            return false;
        }

        let mut changed = false;
        // These specialists are runtime-skipped in proof mode today. Clamp them
        // in route metadata too so adaptive planning cannot advertise them for
        // the official proof-required Main path.
        if self.features.sweep {
            self.features.sweep = false;
            changed = true;
        }
        if self.features.symmetry {
            self.features.symmetry = false;
            changed = true;
        }
        if matches!(self.variant, SolverVariant::Default)
            && matches!(self.input.proof_mode(), VariantProofMode::Lrat)
        {
            let official_policy = VariantBranchPolicy::MabUcb1 {
                epoch_min_conflicts: OFFICIAL_MAIN_LRAT_MAB_EPOCH_MIN_CONFLICTS,
            };
            if self.branch_policy != official_policy {
                self.branch_policy = official_policy;
                changed = true;
            }
        }
        changed
    }

    fn apply_feature_adaptive_branch_policy(&mut self, features: &SatFeatures) -> bool {
        // A/B measurement knob (campaign): AY_SAT_BRANCH_POLICY=mab|legacy forces
        // the brancher on the Default variant, so the plain (non-LRAT) route can
        // be measured against the official route's MAB-UCB1 WITHOUT the other
        // route differences. Unset => current behavior. Mirrors inc7's AY_AB_*
        // knobs; cached per-process (each solver run is a fresh process).
        if matches!(self.variant, SolverVariant::Default) {
            // B21: the AY_SAT_BRANCH_POLICY campaign force is retired; the
            // auto decision below is the shipped rule.
            let forced: Option<VariantBranchPolicy> = None;
            if let Some(forced) = forced {
                if self.branch_policy == forced {
                    return false;
                }
                self.branch_policy = forced;
                return true;
            }
        }
        if !matches!(self.variant, SolverVariant::Default)
            || !matches!(self.input.proof_mode(), VariantProofMode::Lrat)
            || !matches!(
                self.input.route_profile(),
                VariantRouteProfile::OfficialSatCompMainLrat
            )
        {
            return false;
        }

        let branch_policy = if official_main_lrat_uses_legacy_branch_policy(features) {
            VariantBranchPolicy::LegacyCoupled
        } else {
            VariantBranchPolicy::MabUcb1 {
                epoch_min_conflicts: OFFICIAL_MAIN_LRAT_MAB_EPOCH_MIN_CONFLICTS,
            }
        };
        if self.branch_policy == branch_policy {
            false
        } else {
            self.branch_policy = branch_policy;
            true
        }
    }

    /// Mid-band deep-restart routing gate (xor-heavy batch-3 root cause):
    /// swap the Default variant's Glucose restart controller for Luby{250}
    /// (focused = Luby, stable = pure reluctant) on the 100K–500K-clause
    /// gate-dense band — see the MIDBAND_DEEP_RESTART_* constants for the
    /// measured flip (557d7d4d UNKNOWN@300s -> SAT@86-87s twice, models
    /// externally validated) and for why the class's 1M ceiling is pinned
    /// to 500K. Restart regime is proof-neutral (search order only), so the
    /// gate applies on proof routes too — an in-band UNSAT flip found on
    /// the plain route reproduces under `--proof` for its DRAT certificate.
    ///
    /// Kill-switch `--sat-no-midband-deep-restart` (B26: env retired): ON
    /// for any other explicit value (conservative parse matching
    /// `AY_AB_SUBST_AUTO_GIANT`).
    fn apply_midband_deep_restart_gate(&mut self, features: &SatFeatures) -> bool {
        if !matches!(self.variant, SolverVariant::Default)
            || !Self::midband_deep_restart_env_enabled()
            || !midband_deep_restart_feature_candidate(features)
        {
            return false;
        }
        let policy = VariantRestartPolicy::Luby {
            base: MIDBAND_DEEP_RESTART_LUBY_BASE,
        };
        if self.restart_policy == policy {
            false
        } else {
            self.restart_policy = policy;
            true
        }
    }

    /// The midband deep-restart gate (B26: CLI-owned): ON
    /// for any other explicit value (kill-switch semantics). Cached OnceLock
    /// per the #8506 no-per-call-syscall convention.
    fn midband_deep_restart_env_enabled() -> bool {
        // B26: CLI-owned opt-out (--sat-no-midband-deep-restart); env
        // retired.
        !ay_core::sat_ab_switches().no_midband_deep_restart
    }

    fn apply_dense_mutex_focused_restart_gate_experiment(
        &mut self,
        features: &SatFeatures,
    ) -> bool {
        let enabled = self.input.dense_mutex_focused_restart_gate_experiment()
            && dense_mutex_focused_restart_feature_candidate(features);
        if self.hot_path.dense_mutex_focused_restart_gate_experiment == enabled {
            false
        } else {
            self.hot_path.dense_mutex_focused_restart_gate_experiment = enabled;
            true
        }
    }

    fn apply_dense_clique_mab_branch_experiment(&mut self, features: &SatFeatures) -> bool {
        let enabled = self.input.dense_clique_mab_branch_experiment()
            && is_official_main_lrat_default_route(self.variant, self.input)
            && official_main_lrat_dense_clique_mutex_candidate(features);
        let mut changed = false;
        if self.hot_path.dense_clique_mab_branch_experiment != enabled {
            self.hot_path.dense_clique_mab_branch_experiment = enabled;
            changed = true;
        }
        if enabled {
            let branch_policy = VariantBranchPolicy::MabUcb1 {
                epoch_min_conflicts: OFFICIAL_MAIN_LRAT_MAB_EPOCH_MIN_CONFLICTS,
            };
            if self.branch_policy != branch_policy {
                self.branch_policy = branch_policy;
                changed = true;
            }
        }
        changed
    }

    fn apply_startup_policy(&mut self) {
        // Startup warmup/walk policy is applied to solver startup-only gates in
        // `apply_to_solver`. Keep the feature profile intact here so periodic
        // rephase walk remains available after CDCL starts.
    }
}

fn official_main_lrat_uses_legacy_branch_policy(features: &SatFeatures) -> bool {
    official_main_lrat_dense_clique_mutex_candidate(features)
        || (features.num_vars < OFFICIAL_MAIN_LRAT_LEGACY_BRANCH_MAX_VARS
            && features.clause_var_ratio > OFFICIAL_MAIN_LRAT_LEGACY_BRANCH_MIN_RATIO)
}

fn official_main_lrat_dense_clique_mutex_candidate(features: &SatFeatures) -> bool {
    features.num_vars > 0
        && features.num_vars <= OFFICIAL_MAIN_LRAT_DENSE_CLIQUE_MUTEX_MAX_VARS
        && features.clause_var_ratio >= OFFICIAL_MAIN_LRAT_DENSE_CLIQUE_MUTEX_MIN_RATIO
        && features.frac_binary >= OFFICIAL_MAIN_LRAT_DENSE_CLIQUE_MUTEX_MIN_BINARY_FRAC
        && features.frac_horn >= OFFICIAL_MAIN_LRAT_DENSE_CLIQUE_MUTEX_MIN_HORN_FRAC
        && features.clause_size_max >= OFFICIAL_MAIN_LRAT_DENSE_CLIQUE_MUTEX_MIN_LONG_CLAUSE
        && features.pos_neg_balance_mean <= OFFICIAL_MAIN_LRAT_DENSE_CLIQUE_MUTEX_MAX_POS_BALANCE
}

fn dense_mutex_focused_restart_feature_candidate(features: &SatFeatures) -> bool {
    features.num_vars > 0
        && features.num_vars < DENSE_MUTEX_FOCUSED_RESTART_MAX_VARS
        && features.clause_var_ratio > DENSE_MUTEX_FOCUSED_RESTART_MIN_RATIO
        && features.frac_binary >= DENSE_MUTEX_FOCUSED_RESTART_MIN_BINARY_FRAC
}

/// Load-time detector for the mid-band deep-restart gate: 100K–500K clauses
/// (over the 50K XOR-extension decline cap by construction, under the
/// streaming-parser threshold — see MIDBAND_DEEP_RESTART_MAX_CLAUSES) with a
/// gate-dense bin+ternary clause mix (>= 85%) at gate-encoding density
/// (clause/var ratio <= 6 — see MIDBAND_DEEP_RESTART_MAX_CLAUSE_VAR_RATIO
/// for the measured 6f354fbe floor exclusion).
fn midband_deep_restart_feature_candidate(features: &SatFeatures) -> bool {
    features.num_clauses >= MIDBAND_DEEP_RESTART_MIN_CLAUSES
        && features.num_clauses <= MIDBAND_DEEP_RESTART_MAX_CLAUSES
        && features.frac_binary + features.frac_ternary >= MIDBAND_DEEP_RESTART_MIN_BIN_TERN_FRAC
        && features.clause_var_ratio <= MIDBAND_DEEP_RESTART_MAX_CLAUSE_VAR_RATIO
        && features.clause_var_ratio >= MIDBAND_DEEP_RESTART_MIN_CLAUSE_VAR_RATIO
}

fn dimacs_baseline_features() -> InprocessingFeatureProfile {
    InprocessingFeatureProfile {
        preprocess: true,
        walk: true,
        warmup: true,
        shrink: true,
        hbr: true,
        vivify: true,
        subsume: true,
        probe: true,
        // BVE is opt-in until model reconstruction is safe on structured
        // DIMACS instances (Braun/barrel FINALIZE_SAT_FAIL regressions).
        // Measured neutral-to-slightly-negative on the SAT-COMP-2025 sample at
        // 60s (no solved-count gain over the no-BVE baseline), so kept off: the
        // dominant gap vs Kissat is equivalent-literal substitution (Kissat
        // "substitute" reaches ~40% of variables on these instances), not BVE.
        // Confirmed net-neutral-to-negative on both the medium (60s) and large
        // (180s, 13-36MB industrial) SAT-COMP-2025 samples, so kept off.
        //
        // UPDATE (#sparse-gap Cluster C): those A/Bs were UNSCOPED. On the
        // sparse band (density <= 12, vars <= 150K) kissat's wins ARE
        // elimination, and the scoped same-binary A/B measured +2 solves /
        // 0 losses. The braun.11 reconstruction FINALIZE_SAT_FAIL that kept
        // this opt-in was root-caused by ef818369 to preprocess-subsume
        // constraint loss (fixed in config_preprocess_cleanup.rs), so the
        // scoped unlock is now DEFAULT-ON via `apply_ab_bve_knob`
        // (3c9b980b; kill-switch --sat-no-bve-sparse). This baseline flag
        // stays false: the band predicate, not the profile, decides.
        bve: false,
        // CaDiCaL defaults block=0 (DISABLED). BCE removes blocked clauses but
        // adds O(clauses * max_occ) overhead per call. CaDiCaL only enables BCE
        // for specific competition configurations, not the default.
        bce: false,
        // CaDiCaL defaults condition=0 (DISABLED, options.hpp). Conditioning
        // (GBCE) eliminates globally blocked clauses but adds O(clauses) overhead
        // per call building the total assignment. Deferred to specific competition
        // configurations (#8084).
        condition: false,
        // Decompose: SCC-based equivalent-literal substitution over the binary
        // implication graph (Kissat's "substitute"). Kept opt-in. A/B knob:
        // (retired B36) (decompose) / (retired B36) (decompose+congruence)
        // on the Default variant.
        //
        // Measured 2026-06-27 ((retired B36), 60s, satcomp2025): net-negative
        // on solved count. The lost SAT (b5431f41) is NOT a reconstruction
        // degrade as previously believed — it is a SLOWDOWN: decompose takes the
        // 22s default solve to ~87s, so it times out at 60s but still returns a
        // VERIFIED SAT model at 180s (reconstruction is correct; no
        // FINALIZE_SAT_FAIL). No genuine reconstruction degrade-to-Unknown was
        // reproducible on the sample.
        //
        // Gate gap on 70da0b78 (68100 vars): Kissat substitutes 27217 vars and
        // hits UNSAT in 0.04s; AY's congruence finds ~11.7k equivalences and
        // decompose substitutes ~24k cumulatively across rounds but never
        // collapses. Root cause (measured via --debug sat-congruence): AY's
        // congruence extracts 36818 gates vs Kissat's 65558. The miss is
        // dominated by ITE (AY 0 vs Kissat 19792 — ITE extraction is disabled
        // for num_vars>50k in congruence/mod.rs because AY lacks Kissat's `twice`
        // both-polarity pre-filter, so its O(pos_ternary²·neg) detector is too
        // costly) and XOR (AY 8112 vs Kissat 23148, ~35% coverage). AND is at
        // parity (AY 22380 vs 22618). So a real win needs strengthening gate
        // extraction (ITE twice-filter to re-enable >50k vars; XOR coverage),
        // not just the flag flip.
        //
        // UPDATE 2026-07-09 (decompose DRAT unclamp): the proof-capability
        // registry now ships Decompose { drat: true } (externally verified,
        // dpr-trim + cake_lpr — see proof_capability.rs), so an opt-in
        // decompose run no longer needs --sat-no-drat-subst.
        //
        // UPDATE 2026-07-10 (wf_55735963 collapse+BVE default flip): the
        // earlier "zero flips" finding was the collapse WITHOUT bounded
        // elimination behind it. With the post-collapse BVE re-derivation
        // (--sat-no-bve-post-collapse) + deep sparse budgets
        // (AY_AB_BVE_SPARSE_DEEP) composed, the scoreboard protocol measured
        // +7 kissat-agreeing UNSAT flips / 0 hard losses, so the route-aware
        // probe-gated AUTO is now DEFAULT-ON — via `apply_ab_substitution_knob`
        // (kill-switch --sat-no-subst-auto), NOT via this profile flag. This
        // baseline flag stays false: the knob predicate (Default variant,
        // proof-clamp-respecting), not the profile, decides — same pattern
        // as the sparse-band `bve` flag above.
        decompose: false,
        factor: true,
        sbva: true,
        transred: true,
        htr: true,
        gate: true,
        // Congruence feeds equivalence rewrites consumed by decompose; like
        // decompose it is enabled by the default-ON AUTO knob (wf_55735963,
        // see `apply_ab_substitution_knob`), not by this profile flag.
        congruence: false,
        sweep: true,
        backbone: true,
        // CaDiCaL does not implement symmetry detection. AY's symmetry breaking
        // adds orbital SBPs which increase clause count on large formulas without
        // guaranteed benefit. Default OFF for DIMACS; SMT/DPLL(T) retains its own
        // default (#8084).
        symmetry: false,
        // CaDiCaL defaults cover=0 (DISABLED, options.hpp). Covered clause
        // elimination (ACCE) strictly subsumes BCE with the same O(clauses *
        // max_occ) overhead. Default OFF to match CaDiCaL (#8084).
        reorder: true,
        cce: false,
    }
}

fn minimal_features() -> InprocessingFeatureProfile {
    InprocessingFeatureProfile {
        preprocess: false,
        walk: true,
        warmup: true,
        shrink: true,
        hbr: false,
        vivify: false,
        subsume: false,
        probe: false,
        bve: false,
        bce: false,
        condition: false,
        decompose: false,
        factor: false,
        sbva: false,
        transred: false,
        htr: false,
        gate: false,
        congruence: false,
        sweep: false,
        backbone: false,
        symmetry: false,
        reorder: false,
        cce: false,
    }
}

/// Probe-focused feature set for failed-literal probing emphasis.
///
/// Enables: probing, backbone, HBR, subsumption, HTR, transred,
///          decompose (SCC for equivalences), gate extraction.
/// Disables: BVE, vivification, conditioning, sweep, congruence, factor,
///           BCE, CCE, symmetry.
///
/// The rationale is that probing + backbone detection finds fixed literals
/// and binary implications cheaply, while avoiding the heavyweight
/// clause-rewriting techniques that may slow down the search on
/// hard combinatorial instances. BCE, CCE, and symmetry are disabled to
/// match CaDiCaL defaults (block=0, cover=0, no symmetry) -- these add
/// O(clauses * max_occ) overhead without competitive benefit (#8084).
fn probe_features() -> InprocessingFeatureProfile {
    InprocessingFeatureProfile {
        preprocess: true,
        walk: true,
        warmup: true,
        shrink: true,
        hbr: true,
        vivify: false,
        subsume: true,
        probe: true,
        bve: false,
        // CaDiCaL defaults block=0 (DISABLED). BCE adds O(clauses * max_occ)
        // overhead per call without competitive benefit on probe-focused
        // instances (#8084).
        bce: false,
        condition: false,
        decompose: true,
        factor: false,
        sbva: false,
        transred: true,
        htr: true,
        gate: true,
        congruence: false,
        sweep: false,
        backbone: true,
        // CaDiCaL has no symmetry detection. AY's orbital SBP symmetry breaking
        // increases clause count without guaranteed benefit (#8084).
        symmetry: false,
        // CaDiCaL defaults cover=0 (DISABLED). CCE strictly subsumes BCE with
        // same O(clauses * max_occ) overhead (#8084).
        reorder: true,
        cce: false,
    }
}

/// Whether the sparse-band BVE unlock knob is set in this process's
/// environment (test hermeticity helper: default-off assertions only hold
/// when the knob is unset).
#[cfg(test)]
pub(crate) fn ab_bve_sparse_knob_set() -> bool {
    // Default flipped ON 2026-07-08 (post reconstruction fix ef818369):
    // the unlock is active unless explicitly killed (B34: --sat-no-bve-sparse).
    !ay_core::sat_ab_switches().no_bve_sparse
}

#[cfg(test)]
mod tests {
    use super::*;

    fn decision<'a>(
        plan: &'a VariantProfilePlan,
        capability: &str,
    ) -> &'a crate::auto::CapabilityDecision {
        plan.ledger
            .entries()
            .iter()
            .find(|decision| decision.capability == capability)
            .unwrap_or_else(|| panic!("missing capability decision for {capability}"))
    }

    /// B0 records every final feature gate and its deciding layer.
    #[test]
    fn capability_ledger_records_every_decision() {
        let features = SatFeatures::extract(
            4,
            &[
                vec![
                    crate::Literal::positive(crate::Variable::new(0)),
                    crate::Literal::positive(crate::Variable::new(1)),
                ],
                vec![
                    crate::Literal::negative(crate::Variable::new(2)),
                    crate::Literal::positive(crate::Variable::new(3)),
                ],
            ],
        );
        let input = VariantInput::new(4, 2, VariantProofMode::Disabled);
        let config = SolverVariant::Default.config(input);
        let plan = VariantProfilePlan::from_config_features(config, &features);
        assert_eq!(plan.ledger.entries().len(), 23);
        assert_eq!(
            decision(&plan, "preprocess").source,
            DecisionSource::Default
        );
        assert_eq!(
            decision(&plan, "symmetry").source,
            DecisionSource::Auto,
            "small-formula symmetry re-enable is an automatic decision"
        );
    }

    #[test]
    fn capability_ledger_attributes_cli_and_adaptive_decisions_truthfully() {
        let features = SatFeatures::from_streaming_counters(1_000, 101_000, 0, 101_000);
        let profile = InprocessingFeatureProfile {
            condition: true,
            ..Default::default()
        };
        let plan = VariantProfilePlan::for_features_with_source(
            SolverVariant::Custom(profile),
            VariantInput::new(1_000, 101_000, VariantProofMode::Disabled),
            &features,
            DecisionSource::Cli,
        );
        let preprocess = decision(&plan, "preprocess");
        assert_eq!(preprocess.source, DecisionSource::Cli);
        let condition = decision(&plan, "condition");
        assert_eq!(condition.state, crate::auto::CapabilityState::Off);
        assert_eq!(condition.source, DecisionSource::Auto);
        assert!(condition.because.contains("clause_var_ratio="));
    }

    #[test]
    fn capability_ledger_attributes_proof_clamps_to_policy() {
        let features = SatFeatures::from_streaming_counters(10_000, 20_000, 0, 20_000);
        let plan = VariantProfilePlan::for_features_with_source(
            SolverVariant::Probe,
            VariantInput::new(10_000, 20_000, VariantProofMode::Lrat),
            &features,
            DecisionSource::Cli,
        );
        let decompose = decision(&plan, "decompose");
        assert_eq!(decompose.state, crate::auto::CapabilityState::Off);
        assert_eq!(decompose.source, DecisionSource::Auto);
        assert!(decompose.because.contains("proof capability policy"));
    }

    #[test]
    fn capability_ledger_attributes_route_clamps_to_policy() {
        let features = SatFeatures::from_streaming_counters(10_000, 20_000, 0, 20_000);
        let profile = InprocessingFeatureProfile {
            sweep: true,
            ..Default::default()
        };
        let input = VariantInput::new(10_000, 20_000, VariantProofMode::Disabled)
            .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat);
        let plan = VariantProfilePlan::for_features_with_source(
            SolverVariant::Custom(profile),
            input,
            &features,
            DecisionSource::Cli,
        );
        let sweep = decision(&plan, "sweep");
        assert_eq!(sweep.state, crate::auto::CapabilityState::Off);
        assert_eq!(sweep.source, DecisionSource::Auto);
        assert!(sweep.because.contains("route=official-satcomp-main-lrat"));
    }

    /// The combined `auto_route` never overrides a non-Default variant. This is
    /// env-independent (the non-Default early-return precedes any kill-switch
    /// env read) and locks the key composition invariant: once the probe step
    /// has re-routed Default -> Probe, the aggressive step must leave it Probe
    /// (it only fires on Default), and an explicit non-Default preset is
    /// likewise untouched by either step.
    #[test]
    fn auto_route_leaves_non_default_variants_untouched() {
        let counts = (60_000usize, 300_000usize, 240_000usize); // aggressive-band shape
        for v in [
            SolverVariant::Probe,
            SolverVariant::Aggressive,
            SolverVariant::Minimal,
        ] {
            assert_eq!(v.auto_route_from_counts(counts.0, counts.1, counts.2), v);
            assert_eq!(
                v.auto_aggressive_route_from_counts(counts.0, counts.1, counts.2),
                v
            );
        }
    }

    #[test]
    fn test_default_variant_matches_dimacs_baseline() {
        let config = VariantConfig::for_variant(
            SolverVariant::Default,
            VariantInput::new(32, 96, VariantProofMode::Disabled),
        );

        assert!(!config.full_preprocessing);
        assert!(config.features.preprocess);
        // Default flipped 2026-07-08: the sparse-band BVE unlock is ON by
        // default for in-band inputs (32v/96c is in-band); --sat-no-bve-sparse
        // is the kill-switch restoring the old profile.
        if ab_bve_sparse_knob_set() {
            assert!(
                config.features.bve,
                "sparse-band BVE unlock is default-ON for in-band inputs"
            );
        } else {
            assert!(
                !config.features.bve,
                "kill-switch (--sat-no-bve-sparse) restores BVE-off"
            );
        }
        // Default flipped 2026-07-10 (wf_55735963): the route-aware
        // substitution-collapse AUTO is ON by default on the non-proof
        // Default route (+7 measured UNSAT flips / 0 hard losses on the
        // main2025 scoreboard protocol). B34: the kill is CLI-owned
        // (--sat-no-subst-auto), so the default arm is unconditional.
        assert!(
            config.features.congruence,
            "substitution-collapse AUTO is default-ON: congruence \
             eligible (probe-gated) on the non-proof Default route"
        );
        assert!(
            config.features.decompose,
            "substitution-collapse AUTO is default-ON: decompose \
             eligible (probe-gated) on the non-proof Default route"
        );
        assert!(config.features.subsume);
        // Non-competitive features OFF to match CaDiCaL defaults (#8084)
        assert!(!config.features.bce, "BCE should be OFF (CaDiCaL block=0)");
        assert!(
            !config.features.condition,
            "conditioning should be OFF (CaDiCaL condition=0)"
        );
        assert!(
            !config.features.symmetry,
            "symmetry should be OFF (CaDiCaL has no symmetry)"
        );
        assert!(!config.features.cce, "CCE should be OFF (CaDiCaL cover=0)");
    }

    #[test]
    fn test_subst_auto_default_respects_proof_clamps() {
        // The DEFAULT-ON substitution-collapse path (wf_55735963) must never
        // override a proof refusal: LRAT is fail-closed for both Congruence
        // and Decompose in PROOF_CAPABILITY_REGISTRY. B36: every
        // substitution control is CLI-owned, so no hermeticity guard.

        let lrat = VariantConfig::for_variant(
            SolverVariant::Default,
            VariantInput::new(1_000, 3_000, VariantProofMode::Lrat),
        );
        assert!(
            !lrat.features.congruence,
            "default AUTO must not reopen congruence under LRAT (fail-closed)"
        );
        assert!(
            !lrat.features.decompose,
            "default AUTO must not reopen decompose under LRAT (fail-closed)"
        );

        // DRAT: registry truth since wf_0c7d84e9 — Congruence/Decompose ship
        // { drat: true } and the wf_55735963 f0bafebd dpr-trim rejection was
        // root-caused (XOR-ladder rungs watched as binaries) and fixed, then
        // externally re-verified end-to-end (dpr-trim + cake_lpr) on
        // f0bafebd, braun10/12, and the collapse flips under proof. The
        // default AUTO path therefore opens the collapse under DRAT.
        let drat = VariantConfig::for_variant(
            SolverVariant::Default,
            VariantInput::new(1_000, 3_000, VariantProofMode::Drat),
        );
        assert!(
            drat.features.congruence,
            "default AUTO opens congruence under DRAT (registry truth; \
             wf_0c7d84e9 rung-watch fix, externally re-verified)"
        );
        assert!(
            drat.features.decompose,
            "default AUTO opens decompose under DRAT (registry truth; \
             wf_0c7d84e9 rung-watch fix, externally re-verified)"
        );

        // Non-Default variants are untouched by the AUTO knob.
        let probe = VariantConfig::for_variant(
            SolverVariant::Probe,
            VariantInput::new(1_000, 3_000, VariantProofMode::Disabled),
        );
        assert!(
            !probe.features.congruence,
            "AUTO default is scoped to the Default variant"
        );
    }

    #[test]
    fn test_sparse_band_bve_unlock_default_off() {
        // Default flipped ON 2026-07-08 (post ef818369): with the knob
        // unset (or =1) the unlock is ACTIVE — BVE enabled for the in-band
        // sparse shape (density<=12, vars<=150K) plus the small-circuit arm
        // (vars<=10K, density<=16 — the #3464 barrel6 gap fix) and untouched
        // elsewhere. --sat-no-bve-sparse is the kill-switch (asserted
        // hermetically only when set). The LRAT clamp below is unconditional.
        if ab_bve_sparse_knob_set() {
            for (vars, clauses, expect_bve) in [
                (1_000usize, 12_000usize, true), // in-band sparse
                (1_000, 12_001, true),           // small-circuit arm (<=10K vars)
                (248, 3_729, true),              // cmu-bmc-barrel6 shape (#3464)
                (1_000, 16_000, true),           // small-circuit arm density edge
                (1_000, 16_001, false),          // above both density edges
                (10_001, 130_013, false),        // small-arm var cap (density 13)
                (150_000, 450_000, true),        // at the size cap
                (150_001, 450_003, false),       // above the size cap
                (0, 0, false),                   // degenerate header
            ] {
                let plain = VariantConfig::for_variant(
                    SolverVariant::Default,
                    VariantInput::new(vars, clauses, VariantProofMode::Disabled),
                );
                assert_eq!(
                    plain.features.bve, expect_bve,
                    "default-on band scoping for {vars}v/{clauses}c"
                );
            }
        } else {
            for (vars, clauses) in [(1_000usize, 12_000usize), (150_000, 450_000)] {
                let plain = VariantConfig::for_variant(
                    SolverVariant::Default,
                    VariantInput::new(vars, clauses, VariantProofMode::Disabled),
                );
                assert!(
                    !plain.features.bve,
                    "kill-switch: bve off for {vars}v/{clauses}c"
                );
            }
        }

        // LRAT route is additionally fail-closed by the proof clamp.
        let lrat = VariantConfig::for_variant(
            SolverVariant::Default,
            VariantInput::new(1_000, 3_000, VariantProofMode::Lrat),
        );
        assert!(!lrat.features.bve, "LRAT keeps BVE clamped (fail-closed)");
    }

    #[test]
    fn test_aggressive_variant_enables_full_preprocessing() {
        let config = VariantConfig::for_variant(
            SolverVariant::Aggressive,
            VariantInput::new(32, 96, VariantProofMode::Disabled),
        );

        assert!(config.full_preprocessing);
        assert_eq!(config.restart_policy, VariantRestartPolicy::Glucose);
    }

    #[test]
    fn test_minimal_variant_disables_preprocessing_pipeline() {
        let config = VariantConfig::for_variant(
            SolverVariant::Minimal,
            VariantInput::new(32, 96, VariantProofMode::Disabled),
        );

        assert!(!config.features.preprocess);
        assert!(config.features.walk);
        assert!(config.features.warmup);
        assert!(config.features.shrink);
        assert!(!config.features.bve);
        assert!(!config.features.vivify);
        assert!(!config.features.probe);
    }

    #[test]
    fn test_probe_variant_enables_probing_backbone() {
        let config = VariantConfig::for_variant(
            SolverVariant::Probe,
            VariantInput::new(32, 96, VariantProofMode::Disabled),
        );

        // Core probe-focused features enabled
        assert!(config.features.probe);
        assert!(config.features.backbone);
        assert!(config.features.hbr);
        assert!(config.features.subsume);
        assert!(config.features.transred);
        assert!(config.features.htr);
        assert!(config.features.gate);
        assert!(config.features.decompose);

        // Heavyweight and non-competitive techniques disabled (#8084)
        assert!(!config.features.bve);
        assert!(!config.features.vivify);
        assert!(!config.features.condition);
        assert!(!config.features.sweep);
        assert!(!config.features.congruence);
        assert!(!config.features.factor);
        // BCE, CCE, symmetry OFF to match CaDiCaL defaults (#8084)
        assert!(!config.features.bce, "BCE should be OFF (CaDiCaL block=0)");
        assert!(
            !config.features.symmetry,
            "symmetry should be OFF (CaDiCaL has no symmetry)"
        );
        assert!(!config.features.cce, "CCE should be OFF (CaDiCaL cover=0)");

        // Uses Luby restarts
        assert_eq!(
            config.restart_policy,
            VariantRestartPolicy::Luby { base: 250 }
        );
        assert_eq!(
            config.branch_policy,
            VariantBranchPolicy::MabUcb1 {
                epoch_min_conflicts: PROBE_MAB_EPOCH_MIN_CONFLICTS,
            }
        );
        assert!(!config.full_preprocessing);
    }

    #[test]
    fn test_lrat_input_clamps_destructive_features() {
        let config = VariantConfig::for_variant(
            SolverVariant::Aggressive,
            VariantInput::new(32, 96, VariantProofMode::Lrat),
        );

        assert!(config.features.probe, "probe remains LRAT-enabled");
        assert!(!config.features.bve, "BVE must be disabled for LRAT");
        assert!(
            !config.features.decompose,
            "decompose must be disabled for LRAT"
        );
        assert!(!config.features.factor, "factor must be disabled for LRAT");
        assert!(!config.features.sbva, "SBVA must be disabled for LRAT");
        assert!(!config.features.sweep, "sweep must be disabled for LRAT");
        assert!(
            !config.features.symmetry,
            "symmetry must be disabled for LRAT"
        );
    }

    #[test]
    fn test_drat_input_clamps_sweep_in_variant_config() {
        let config = VariantConfig::for_variant(
            SolverVariant::Aggressive,
            VariantInput::new(32, 96, VariantProofMode::Drat),
        );

        assert!(config.features.factor, "factor remains DRAT-enabled");
        assert!(config.features.sbva, "SBVA remains DRAT-enabled");
        assert!(!config.features.sweep, "sweep must be disabled for DRAT");
        assert!(
            !config.features.symmetry,
            "symmetry must be disabled for DRAT"
        );
    }

    #[test]
    fn test_proof_profile_plan_keeps_adaptive_symmetry_clamped() {
        let input = VariantInput::new(32, 96, VariantProofMode::Lrat);
        let clauses: Vec<Vec<crate::Literal>> = Vec::new();
        let features = SatFeatures::extract(32, &clauses);

        let plan = VariantProfilePlan::for_features(SolverVariant::Default, input, &features);

        assert!(
            !plan.config.features.symmetry,
            "adaptive profile adjustment must not reopen proof-unsafe symmetry"
        );
    }

    #[test]
    fn test_official_main_lrat_default_disables_startup_phase_init() {
        let input = VariantInput::new(32, 96, VariantProofMode::Lrat)
            .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat)
            .with_startup_policy(VariantStartupPolicy::DisableWarmupWalk);
        let config = VariantConfig::for_variant(SolverVariant::Default, input);

        assert!(
            config.features.walk,
            "periodic rephase walk must remain enabled"
        );
        assert!(
            config.features.warmup,
            "startup warmup is disabled by startup-only policy, not feature profile"
        );
        assert!(config.features.shrink, "unrelated features remain intact");
        assert!(
            config.hot_path.prune_conflict_analysis_experiments,
            "official Main/default/LRAT hot-loop plan must be frozen in config"
        );
        assert!(
            config.hot_path.stable_only_rephase,
            "official Main/default/LRAT must enable stable-only rephase"
        );
        assert_eq!(
            config.branch_policy,
            VariantBranchPolicy::MabUcb1 {
                epoch_min_conflicts: OFFICIAL_MAIN_LRAT_MAB_EPOCH_MIN_CONFLICTS,
            },
            "official Main/default/LRAT must use the proof-safe adaptive branch profile"
        );

        let mut solver = Solver::new(32);
        config.apply_to_solver(&mut solver);
        assert!(solver.is_walk_enabled(), "periodic rephase walk stays on");
        assert!(
            !solver.is_startup_walk_enabled(),
            "startup walk flag must be off"
        );
        assert!(
            solver.is_warmup_enabled(),
            "warmup feature profile stays on for telemetry/profile parity"
        );
        assert!(
            !solver.is_startup_warmup_enabled(),
            "startup warmup flag must be off"
        );
        assert!(
            solver.sat_comp_main_conflict_pruning_enabled(),
            "official Main/default/LRAT must prune conflict-analysis experiments"
        );
        assert!(
            solver.stable_only_rephase_enabled(),
            "official Main/default/LRAT must apply stable-only rephase"
        );
        assert_eq!(
            solver.branch_selector_mode(),
            crate::BranchSelectorMode::MabUcb1,
            "official Main/default/LRAT must enable adaptive branch selection"
        );
        assert_eq!(
            solver.active_branch_heuristic(),
            BranchHeuristic::Vmtf,
            "focused-mode startup must keep the legacy VMTF brancher before stable MAB scoring"
        );
    }

    #[test]
    fn test_official_main_lrat_full_preprocessing_prunes_large_and_unknown_only() {
        fn full_preprocessing_enabled(num_vars: usize, num_clauses: usize) -> bool {
            let input = VariantInput::new(num_vars, num_clauses, VariantProofMode::Lrat)
                .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat)
                .with_startup_policy(VariantStartupPolicy::DisableWarmupWalk);
            let config = VariantConfig::for_variant(SolverVariant::Default, input);
            let mut solver = Solver::new(num_vars);
            config.apply_to_solver(&mut solver);
            solver.is_full_preprocessing_enabled()
        }

        assert!(
            full_preprocessing_enabled(128, 512),
            "small official Main LRAT formulas keep full preprocessing"
        );
        assert!(
            full_preprocessing_enabled(
                OFFICIAL_MAIN_LRAT_FULL_PREPROCESS_MAX_VARS,
                OFFICIAL_MAIN_LRAT_FULL_PREPROCESS_MAX_CLAUSES,
            ),
            "exact threshold official Main LRAT formulas keep full preprocessing"
        );
        assert!(
            !full_preprocessing_enabled(
                OFFICIAL_MAIN_LRAT_FULL_PREPROCESS_MAX_VARS + 1,
                OFFICIAL_MAIN_LRAT_FULL_PREPROCESS_MAX_CLAUSES,
            ),
            "var-only overflow skips the tail-prone full prepass"
        );
        assert!(
            !full_preprocessing_enabled(
                OFFICIAL_MAIN_LRAT_FULL_PREPROCESS_MAX_VARS,
                OFFICIAL_MAIN_LRAT_FULL_PREPROCESS_MAX_CLAUSES + 1,
            ),
            "clause-only overflow skips the tail-prone full prepass"
        );
        assert!(
            !full_preprocessing_enabled(0, 0),
            "unknown-size official Main LRAT formulas skip the full prepass"
        );
        assert!(
            !full_preprocessing_enabled(0, OFFICIAL_MAIN_LRAT_FULL_PREPROCESS_MAX_CLAUSES),
            "unknown vars skip the full prepass even when clauses are bounded"
        );
        assert!(
            !full_preprocessing_enabled(OFFICIAL_MAIN_LRAT_FULL_PREPROCESS_MAX_VARS, 0),
            "unknown clauses skip the full prepass even when vars are bounded"
        );
    }

    #[test]
    fn test_official_main_lrat_large_formula_reduces_subsume_effort() {
        fn official_main_lrat_subsume_effort(num_vars: usize, num_clauses: usize) -> u64 {
            let input = VariantInput::new(num_vars, num_clauses, VariantProofMode::Lrat)
                .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat)
                .with_startup_policy(VariantStartupPolicy::DisableWarmupWalk);
            let config = VariantConfig::for_variant(SolverVariant::Default, input);
            let mut solver = Solver::new(num_vars);
            config.apply_to_solver(&mut solver);
            solver.subsume_effort_permille()
        }

        assert_eq!(
            official_main_lrat_subsume_effort(
                OFFICIAL_MAIN_LRAT_FULL_PREPROCESS_MAX_VARS,
                OFFICIAL_MAIN_LRAT_FULL_PREPROCESS_MAX_CLAUSES,
            ),
            1000,
            "exact-threshold official Main LRAT formulas keep full subsume effort"
        );
        assert_eq!(
            official_main_lrat_subsume_effort(
                OFFICIAL_MAIN_LRAT_FULL_PREPROCESS_MAX_VARS + 1,
                OFFICIAL_MAIN_LRAT_FULL_PREPROCESS_MAX_CLAUSES,
            ),
            DIMACS_REDUCED_EFFORT_SUBSUME,
            "var-overflow official Main LRAT formulas reduce subsume effort"
        );
        assert_eq!(
            official_main_lrat_subsume_effort(
                OFFICIAL_MAIN_LRAT_FULL_PREPROCESS_MAX_VARS,
                OFFICIAL_MAIN_LRAT_FULL_PREPROCESS_MAX_CLAUSES + 1,
            ),
            DIMACS_REDUCED_EFFORT_SUBSUME,
            "clause-overflow official Main LRAT formulas reduce subsume effort"
        );
        assert_eq!(
            official_main_lrat_subsume_effort(0, 0),
            1000,
            "unknown-size official Main LRAT formulas do not count as cutoff overflow"
        );
    }

    #[test]
    fn test_large_lrat_subsume_effort_reduction_is_official_default_only() {
        let num_vars = OFFICIAL_MAIN_LRAT_FULL_PREPROCESS_MAX_VARS + 1;
        let num_clauses = OFFICIAL_MAIN_LRAT_FULL_PREPROCESS_MAX_CLAUSES;

        let standard_input = VariantInput::new(num_vars, num_clauses, VariantProofMode::Lrat);
        let standard_config = VariantConfig::for_variant(SolverVariant::Default, standard_input);
        let mut standard_solver = Solver::new(num_vars);
        standard_config.apply_to_solver(&mut standard_solver);
        assert_eq!(
            standard_solver.subsume_effort_permille(),
            1000,
            "plain default/LRAT proof runs keep full subsume effort"
        );

        let official_input = VariantInput::new(num_vars, num_clauses, VariantProofMode::Lrat)
            .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat)
            .with_startup_policy(VariantStartupPolicy::DisableWarmupWalk);
        let aggressive_config =
            VariantConfig::for_variant(SolverVariant::Aggressive, official_input);
        let mut aggressive_solver = Solver::new(num_vars);
        aggressive_config.apply_to_solver(&mut aggressive_solver);
        assert_eq!(
            aggressive_solver.subsume_effort_permille(),
            1000,
            "official route non-default variants keep full subsume effort"
        );
    }

    #[test]
    fn test_official_route_profile_requires_proof_safe_specialist_routing() {
        assert_eq!(VariantRouteProfile::Standard.as_str(), "standard");
        assert_eq!(
            VariantRouteProfile::OfficialSatCompMainLrat.as_str(),
            "official-satcomp-main-lrat"
        );
        assert!(
            !VariantRouteProfile::Standard.requires_proof_safe_specialist_routing(),
            "standard routing keeps specialist candidates available"
        );
        assert!(
            VariantRouteProfile::OfficialSatCompMainLrat.requires_proof_safe_specialist_routing(),
            "official Main/default/LRAT routing must reject proof-incomplete specialists"
        );
    }

    #[test]
    fn test_stable_only_rephase_hot_path_is_official_default_lrat_only() {
        fn stable_only_rephase(variant: SolverVariant, input: VariantInput) -> bool {
            VariantConfig::for_variant(variant, input)
                .hot_path
                .stable_only_rephase
        }

        let official_lrat = VariantInput::new(32, 96, VariantProofMode::Lrat)
            .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat);

        assert!(
            stable_only_rephase(SolverVariant::Default, official_lrat),
            "official Main/default/LRAT route enables stable-only rephase"
        );
        assert!(
            !stable_only_rephase(
                SolverVariant::Default,
                VariantInput::new(32, 96, VariantProofMode::Lrat)
            ),
            "plain default/LRAT proof runs keep normal rephase scheduling"
        );
        assert!(
            !stable_only_rephase(SolverVariant::Aggressive, official_lrat),
            "official route non-default variants keep normal rephase scheduling"
        );
        assert!(
            !stable_only_rephase(
                SolverVariant::Default,
                VariantInput::new(32, 96, VariantProofMode::Drat)
                    .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat),
            ),
            "official default non-LRAT proof runs keep normal rephase scheduling"
        );
    }

    #[test]
    fn test_official_main_lrat_clamps_custom_proof_incomplete_specialists() {
        let profile = InprocessingFeatureProfile {
            sweep: true,
            symmetry: true,
            ..InprocessingFeatureProfile::default()
        };
        let input = VariantInput::new(32, 96, VariantProofMode::Lrat)
            .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat);

        let config = VariantConfig::for_variant(SolverVariant::Custom(profile), input);

        assert!(
            !config.features.sweep,
            "official Main/LRAT must not advertise proof-incomplete sweep"
        );
        assert!(
            !config.features.symmetry,
            "official Main/LRAT must not advertise proof-incomplete symmetry"
        );

        let mut solver = Solver::new(32);
        config.apply_to_solver(&mut solver);
        assert!(
            !solver.is_sweep_enabled(),
            "official Main/LRAT must not run proof-incomplete sweep"
        );
        assert!(
            !solver.is_symmetry_enabled(),
            "official Main/LRAT must not run proof-incomplete symmetry"
        );
    }

    #[test]
    fn test_non_official_lrat_default_preserves_startup_phase_init() {
        let config = VariantConfig::for_variant(
            SolverVariant::Default,
            VariantInput::new(32, 96, VariantProofMode::Lrat),
        );

        assert!(
            config.features.walk,
            "plain LRAT/default keeps variant startup walk"
        );
        assert!(
            config.features.warmup,
            "plain LRAT/default keeps variant startup warmup"
        );
        assert!(
            !config.hot_path.prune_conflict_analysis_experiments,
            "plain LRAT/default must not use official Main hot-loop pruning"
        );
        assert!(
            !config.hot_path.stable_only_rephase,
            "plain LRAT/default must not use official Main stable-only rephase"
        );
        assert_eq!(
            config.branch_policy,
            VariantBranchPolicy::LegacyCoupled,
            "plain LRAT/default must not inherit official Main branch routing"
        );

        let mut solver = Solver::new(32);
        config.apply_to_solver(&mut solver);
        assert!(
            !solver.sat_comp_main_conflict_pruning_enabled(),
            "plain LRAT/default keeps conflict-analysis experiments available"
        );
        assert!(
            !solver.stable_only_rephase_enabled(),
            "plain LRAT/default keeps normal rephase scheduling"
        );
    }

    #[test]
    fn test_startup_phase_policy_is_default_lrat_only() {
        let input = VariantInput::new(32, 96, VariantProofMode::Lrat)
            .with_startup_policy(VariantStartupPolicy::DisableWarmupWalk);
        let config = VariantConfig::for_variant(SolverVariant::Aggressive, input);

        assert!(
            config.features.walk,
            "non-default variants preserve their startup policy"
        );
        assert!(
            config.features.warmup,
            "non-default variants preserve their startup policy"
        );
        assert!(
            !config.hot_path.prune_conflict_analysis_experiments,
            "non-default variants must not use official Main hot-loop pruning"
        );
        assert!(
            !config.hot_path.stable_only_rephase,
            "non-default variants must not use official Main stable-only rephase"
        );

        let mut solver = Solver::new(32);
        config.apply_to_solver(&mut solver);
        assert!(
            !solver.sat_comp_main_conflict_pruning_enabled(),
            "non-default variants must not enter the official Main hot path"
        );
        assert!(
            !solver.stable_only_rephase_enabled(),
            "non-default variants keep normal rephase scheduling"
        );
    }

    #[test]
    fn test_variant_profile_plan_freezes_classification_and_hot_path() {
        let a = crate::Literal::positive(crate::Variable(0));
        let b = crate::Literal::negative(crate::Variable(1));
        let clauses = vec![vec![a, b]; 8];
        let features = SatFeatures::extract(128, &clauses);
        let input = VariantInput::new(128, clauses.len(), VariantProofMode::Lrat)
            .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat)
            .with_startup_policy(VariantStartupPolicy::DisableWarmupWalk);

        let plan = VariantProfilePlan::for_features(SolverVariant::Default, input, &features);

        assert_eq!(plan.instance_class, InstanceClass::Small);
        assert_eq!(
            plan.config.input().route_profile(),
            VariantRouteProfile::OfficialSatCompMainLrat
        );
        assert!(
            plan.adjusted_features,
            "small structured formulas should still record profile adjustment"
        );
        assert!(
            !plan.config.features.symmetry,
            "official Main/default/LRAT must clamp proof-incomplete symmetry after adaptation"
        );
        assert!(
            plan.config.hot_path.prune_conflict_analysis_experiments,
            "formula-class adjustment must preserve the precomputed official Main hot path"
        );
        assert!(
            plan.config.hot_path.stable_only_rephase,
            "formula-class adjustment must preserve official Main stable-only rephase"
        );
        assert_eq!(
            plan.config.branch_policy,
            VariantBranchPolicy::MabUcb1 {
                epoch_min_conflicts: OFFICIAL_MAIN_LRAT_MAB_EPOCH_MIN_CONFLICTS,
            },
            "formula-class adjustment must preserve official Main branch routing"
        );
    }

    #[test]
    fn test_official_main_lrat_small_dense_uses_legacy_branch_policy() {
        let features = SatFeatures::from_streaming_counters(999, 10_990, 0, 0);
        let input = VariantInput::new(999, 10_990, VariantProofMode::Lrat)
            .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat)
            .with_startup_policy(VariantStartupPolicy::DisableWarmupWalk);

        let plan = VariantProfilePlan::for_features(SolverVariant::Default, input, &features);

        assert_eq!(plan.instance_class, InstanceClass::Small);
        assert_eq!(
            plan.config.branch_policy,
            VariantBranchPolicy::LegacyCoupled,
            "small dense official Main/default/LRAT formulas use the legacy branch coupling"
        );
        assert!(
            !plan.config.features.bve,
            "small dense branch policy must not relax the LRAT BVE clamp"
        );
        assert!(
            !plan.config.features.factor,
            "small dense branch policy must not relax the LRAT factor clamp"
        );
        assert!(
            !plan.config.features.sbva,
            "small dense branch policy must not relax the LRAT SBVA clamp"
        );
        assert!(
            !plan.config.features.sweep,
            "small dense branch policy must not relax the LRAT sweep clamp"
        );

        let mut solver = Solver::new(999);
        plan.apply_to_solver(&mut solver);
        assert_eq!(
            solver.branch_selector_mode(),
            crate::BranchSelectorMode::LegacyCoupled
        );
        assert!(
            !solver.is_bve_enabled(),
            "applied small dense policy must keep BVE disabled"
        );
        assert!(
            !solver.is_factor_enabled(),
            "applied small dense policy must keep factor disabled"
        );
    }

    /// 557d7d4db5399188f62bc39598c6d868 load-time signature (57,935 vars /
    /// 229,320 clauses, 87,906 binary + 112,112 ternary = 87% bin+tern):
    /// the measured mid-band deep-restart flip target.
    fn midband_557d_feature_signature() -> SatFeatures {
        let mut features = SatFeatures::from_streaming_counters(57_935, 229_320, 112_112, 0);
        features.num_binary = 87_906;
        features.frac_binary = 87_906.0 / 229_320.0;
        features
    }

    /// True when the process env has the mid-band kill-switch thrown
    /// (any explicit value other than `1`); the gate tests branch on this so
    /// they stay hermetic under CLI-disabled runs.
    fn midband_kill_switch_thrown() -> bool {
        // B26: env retired; the only remaining disable is the CLI switch,
        // which tests do not throw.
        ay_core::sat_ab_switches().no_midband_deep_restart
    }

    #[test]
    fn test_midband_deep_restart_gate_flips_default_to_luby() {
        let features = midband_557d_feature_signature();
        let input = VariantInput::new(57_935, 229_320, VariantProofMode::Disabled);
        let plan = VariantProfilePlan::for_features(SolverVariant::Default, input, &features);
        if midband_kill_switch_thrown() {
            assert_eq!(
                plan.config.restart_policy,
                VariantRestartPolicy::Glucose,
                "the midband kill-switch must restore the Glucose regime"
            );
            return;
        }
        assert_eq!(
            plan.config.restart_policy,
            VariantRestartPolicy::Luby {
                base: MIDBAND_DEEP_RESTART_LUBY_BASE
            },
            "in-band (100K-500K cls, bin+tern >= 85%) Default formulas take the deep Luby regime"
        );

        let mut solver = Solver::new(57_935);
        plan.apply_to_solver(&mut solver);
        assert!(
            !solver.glucose_restarts_enabled(),
            "applied mid-band plan must disable the Glucose restart controller"
        );
    }

    #[test]
    fn test_midband_deep_restart_gate_out_of_band_keeps_glucose() {
        // Below the 100K clause floor.
        let small = SatFeatures::from_streaming_counters(20_000, 99_999, 99_999, 0);
        // Above the 500K clause ceiling (streaming-parser territory; the
        // 500K-1M gap is deliberately stock — see the ceiling constant doc).
        // f5c12b1e signature: bin+tern = 0.91 passes the frac arm, so ONLY
        // the clause ceiling excludes it.
        let mut giant = SatFeatures::from_streaming_counters(106_053, 863_565, 418_894, 0);
        giant.num_binary = 368_192;
        giant.frac_binary = 368_192.0 / 863_565.0;
        // In the clause band but bin+tern below 85% (557d clause count with a
        // wide-clause mix: (50,000 + 112,112) / 229,320 = 0.707).
        let mut wide = SatFeatures::from_streaming_counters(57_935, 229_320, 112_112, 0);
        wide.num_binary = 50_000;
        wide.frac_binary = 50_000.0 / 229_320.0;
        // 6f354fbe signature: clause band + bin+tern 0.90 pass, but clause/var
        // ratio 9.34 > 6 — the measured floor-gate exclusion (UNSAT@101s on
        // Glucose vs UNKNOWN@120s x2 under Luby).
        let mut dense = SatFeatures::from_streaming_counters(48_032, 448_719, 299_858, 0);
        dense.num_binary = 105_877;
        dense.frac_binary = 105_877.0 / 448_719.0;
        for (features, why) in [
            (&small, "sub-100K-clause"),
            (&giant, "over-500K-clause"),
            (&wide, "bin+tern < 85%"),
            (&dense, "clause/var ratio > 6 (6f354fbe floor exclusion)"),
        ] {
            let input = VariantInput::new(
                features.num_vars,
                features.num_clauses,
                VariantProofMode::Disabled,
            );
            let plan = VariantProfilePlan::for_features(SolverVariant::Default, input, features);
            assert_eq!(
                plan.config.restart_policy,
                VariantRestartPolicy::Glucose,
                "{why} formulas must keep the stock Glucose regime"
            );
        }
    }

    #[test]
    fn test_midband_deep_restart_gate_default_variant_only() {
        let features = midband_557d_feature_signature();
        let input = VariantInput::new(57_935, 229_320, VariantProofMode::Disabled);
        for variant in [SolverVariant::Minimal, SolverVariant::Aggressive] {
            let plan = VariantProfilePlan::for_features(variant, input, &features);
            assert_eq!(
                plan.config.restart_policy,
                VariantRestartPolicy::Glucose,
                "mid-band deep-restart gate is scoped to the Default variant"
            );
        }
    }

    fn clique_n2_k10_feature_signature() -> SatFeatures {
        let mut features = SatFeatures::from_streaming_counters(180, 3_160, 0, 3_150);
        features.num_binary = 3_150;
        features.frac_binary = 3_150.0 / 3_160.0;
        features.frac_horn = 3_150.0 / 3_160.0;
        features.clause_size_min = 2;
        features.clause_size_max = 18;
        features.clause_size_mean = 2.050_632_911_392_405;
        features.pos_neg_balance_mean = 1.0 / 36.0;
        features.var_degree_mean = 36.0;
        features.var_degree_std = 0.0;
        features.var_degree_max = 36;
        features
    }

    fn battleship_14_26_feature_signature() -> SatFeatures {
        let mut features = SatFeatures::from_streaming_counters(364, 2_562, 0, 2_366);
        features.num_binary = 2_366;
        features.frac_binary = 2_366.0 / 2_562.0;
        features.frac_horn = 2_366.0 / 2_562.0;
        features.clause_size_min = 2;
        features.clause_size_max = 26;
        features.clause_size_mean = 3.835_284_933_645_589;
        features.pos_neg_balance_mean = 0.5;
        features.var_degree_mean = f64::from(2_366 * 2 + 196 * 26) / 364.0;
        features.var_degree_max = 64;
        features
    }

    fn circuit_multiplier22_feature_signature() -> SatFeatures {
        let mut features = SatFeatures::from_streaming_counters(1_013, 18_793, 1_624, 2_786);
        features.num_binary = 304;
        features.frac_binary = 304.0 / 18_793.0;
        features.frac_ternary = 1_624.0 / 18_793.0;
        features.frac_horn = 2_786.0 / 18_793.0;
        features.clause_size_min = 2;
        features.clause_size_max = 25;
        features.clause_size_mean = 6.436_385_888_362_688;
        features.clause_size_std = 2.107_626_652_011_581;
        features.pos_neg_balance_mean = 0.511_132_395_747_332_3;
        features.pos_neg_balance_std = 0.073_354_277_611_605_8;
        features.var_degree_mean = 120.597_208_374_875_38;
        features.var_degree_std = 122.607_778_180_555_61;
        features.var_degree_max = 984;
        features
    }

    #[test]
    fn test_official_main_lrat_detects_dense_clique_mutex_signature() {
        let features = clique_n2_k10_feature_signature();
        assert!(
            official_main_lrat_dense_clique_mutex_candidate(&features),
            "clique_n2_k10 feature signature must enter the deterministic dense-clique/mutex route"
        );

        let input = VariantInput::new(
            features.num_vars,
            features.num_clauses,
            VariantProofMode::Lrat,
        )
        .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat)
        .with_startup_policy(VariantStartupPolicy::DisableWarmupWalk);
        let plan = VariantProfilePlan::for_features(SolverVariant::Default, input, &features);

        assert_eq!(
            plan.config.branch_policy,
            VariantBranchPolicy::LegacyCoupled,
            "the proof-safe dense-clique/mutex route currently selects search-only legacy branching"
        );
        assert!(
            !plan.config.features.bve,
            "dense-clique/mutex routing must not relax the LRAT BVE clamp"
        );
        assert!(
            !plan.config.features.factor,
            "dense-clique/mutex routing must not relax the LRAT factor clamp"
        );
        assert!(
            !plan.config.features.sbva,
            "dense-clique/mutex routing must not relax the LRAT SBVA clamp"
        );
        assert!(
            !plan.config.features.sweep,
            "dense-clique/mutex routing must not relax the LRAT sweep clamp"
        );
        assert!(
            !plan.config.features.symmetry,
            "dense-clique/mutex routing must not enable proof-incomplete symmetry"
        );
        assert!(
            !plan.config.hot_path.dense_clique_mab_branch_experiment,
            "dense-clique MAB branch experiment must stay default-off"
        );
    }

    #[test]
    fn test_dense_clique_mab_branch_experiment_is_default_off() {
        let features = clique_n2_k10_feature_signature();
        let input = VariantInput::new(
            features.num_vars,
            features.num_clauses,
            VariantProofMode::Lrat,
        )
        .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat)
        .with_startup_policy(VariantStartupPolicy::DisableWarmupWalk);
        let plan = VariantProfilePlan::for_features(SolverVariant::Default, input, &features);

        assert_eq!(
            plan.config.branch_policy,
            VariantBranchPolicy::LegacyCoupled,
            "dense-clique default route keeps the legacy branch coupling without opt-in"
        );
        assert!(
            !plan.config.hot_path.dense_clique_mab_branch_experiment,
            "dense-clique MAB branch route must be default-off"
        );

        let mut solver = Solver::new(features.num_vars);
        plan.apply_to_solver(&mut solver);
        assert_eq!(
            solver.branch_selector_mode(),
            crate::BranchSelectorMode::LegacyCoupled
        );
        assert!(
            !solver.dense_clique_mab_branch_route_enabled(),
            "applied default plan must not mark the MAB branch experiment enabled"
        );
    }

    #[test]
    fn test_dense_clique_mab_branch_opt_in_routes_clique_only() {
        let clique = clique_n2_k10_feature_signature();
        let battleship = battleship_14_26_feature_signature();
        let mab = VariantBranchPolicy::MabUcb1 {
            epoch_min_conflicts: OFFICIAL_MAIN_LRAT_MAB_EPOCH_MIN_CONFLICTS,
        };
        let input = VariantInput::new(clique.num_vars, clique.num_clauses, VariantProofMode::Lrat)
            .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat)
            .with_startup_policy(VariantStartupPolicy::DisableWarmupWalk)
            .with_dense_clique_mab_branch_experiment();

        let clique_plan = VariantProfilePlan::for_features(SolverVariant::Default, input, &clique);
        assert_eq!(
            clique_plan.config.branch_policy, mab,
            "opt-in dense-clique route should override LegacyCoupled with MabUcb1"
        );
        assert!(
            clique_plan
                .config
                .hot_path
                .dense_clique_mab_branch_experiment,
            "opt-in dense-clique route should mark the MAB branch experiment enabled"
        );
        assert_eq!(
            clique_plan.config.restart_policy,
            VariantRestartPolicy::Glucose,
            "dense-clique MAB branch experiment must not alter restart policy"
        );
        assert!(
            !clique_plan
                .config
                .hot_path
                .dense_mutex_focused_restart_gate_experiment,
            "dense-clique MAB branch experiment must not enable the restart experiment"
        );
        assert!(
            !clique_plan.config.features.bve,
            "MAB branch experiment must not relax the LRAT BVE clamp"
        );
        assert!(
            !clique_plan.config.features.factor,
            "MAB branch experiment must not relax the LRAT factor clamp"
        );
        assert!(
            !clique_plan.config.features.sbva,
            "MAB branch experiment must not relax the LRAT SBVA clamp"
        );
        assert!(
            !clique_plan.config.features.sweep,
            "MAB branch experiment must not relax the LRAT sweep clamp"
        );

        let mut solver = Solver::new(clique.num_vars);
        clique_plan.apply_to_solver(&mut solver);
        assert_eq!(
            solver.branch_selector_mode(),
            crate::BranchSelectorMode::MabUcb1
        );
        assert!(
            solver.dense_clique_mab_branch_route_enabled(),
            "applied clique plan should mark the MAB branch route enabled"
        );
        assert!(
            !solver.dense_mutex_focused_restart_gate_experiment_enabled(),
            "applied clique plan should leave the restart experiment disabled"
        );

        let battleship_input = VariantInput::new(
            battleship.num_vars,
            battleship.num_clauses,
            VariantProofMode::Lrat,
        )
        .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat)
        .with_startup_policy(VariantStartupPolicy::DisableWarmupWalk)
        .with_dense_clique_mab_branch_experiment();
        let battleship_plan =
            VariantProfilePlan::for_features(SolverVariant::Default, battleship_input, &battleship);
        assert!(
            !battleship_plan
                .config
                .hot_path
                .dense_clique_mab_branch_experiment,
            "battleship-like rows must stay outside the dense-clique MAB branch experiment"
        );

        let mut battleship_solver = Solver::new(battleship.num_vars);
        battleship_plan.apply_to_solver(&mut battleship_solver);
        assert!(
            !battleship_solver.dense_clique_mab_branch_route_enabled(),
            "battleship-like rows must not mark the experiment route enabled"
        );
    }

    #[test]
    fn test_dense_mutex_focused_restart_gate_is_default_off() {
        let features = clique_n2_k10_feature_signature();
        let input = VariantInput::new(
            features.num_vars,
            features.num_clauses,
            VariantProofMode::Lrat,
        )
        .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat)
        .with_startup_policy(VariantStartupPolicy::DisableWarmupWalk);
        let plan = VariantProfilePlan::for_features(SolverVariant::Default, input, &features);

        assert!(
            !plan
                .config
                .hot_path
                .dense_mutex_focused_restart_gate_experiment,
            "dense-mutex focused restart gate must not enter default routing"
        );

        let mut solver = Solver::new(features.num_vars);
        plan.apply_to_solver(&mut solver);
        assert!(
            !solver.dense_mutex_focused_restart_gate_experiment_enabled(),
            "applied default plan must keep the experiment disabled"
        );
    }

    #[test]
    fn test_dense_mutex_focused_restart_gate_opt_in_routes_clique_only() {
        let clique = clique_n2_k10_feature_signature();
        let battleship = battleship_14_26_feature_signature();
        let input = VariantInput::new(clique.num_vars, clique.num_clauses, VariantProofMode::Lrat)
            .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat)
            .with_startup_policy(VariantStartupPolicy::DisableWarmupWalk)
            .with_dense_mutex_focused_restart_gate_experiment();

        let clique_plan = VariantProfilePlan::for_features(SolverVariant::Default, input, &clique);
        assert!(
            clique_plan
                .config
                .hot_path
                .dense_mutex_focused_restart_gate_experiment,
            "opt-in dense-mutex routing should enable the focused restart gate on clique_n2_k10"
        );
        assert!(
            !clique_plan.config.features.bve,
            "restart-only experiment must not relax the LRAT BVE clamp"
        );
        assert!(
            !clique_plan.config.features.factor,
            "restart-only experiment must not relax the LRAT factor clamp"
        );

        let mut solver = Solver::new(clique.num_vars);
        clique_plan.apply_to_solver(&mut solver);
        assert!(
            solver.dense_mutex_focused_restart_gate_experiment_enabled(),
            "applied clique plan should enable the solver restart experiment"
        );

        let battleship_input = VariantInput::new(
            battleship.num_vars,
            battleship.num_clauses,
            VariantProofMode::Lrat,
        )
        .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat)
        .with_startup_policy(VariantStartupPolicy::DisableWarmupWalk)
        .with_dense_mutex_focused_restart_gate_experiment();
        let battleship_plan =
            VariantProfilePlan::for_features(SolverVariant::Default, battleship_input, &battleship);
        assert!(
            !battleship_plan
                .config
                .hot_path
                .dense_mutex_focused_restart_gate_experiment,
            "battleship must stay outside the dense-mutex restart experiment"
        );
    }

    #[test]
    fn test_dense_clique_mutex_detector_does_not_widen_to_circuit_tail() {
        let features = circuit_multiplier22_feature_signature();

        assert!(
            !official_main_lrat_dense_clique_mutex_candidate(&features),
            "Circuit_multiplier22 must not enter the tiny dense-clique/mutex route"
        );
        assert_eq!(
            InstanceClass::classify(&features),
            InstanceClass::Structured,
            "Circuit_multiplier22 must stay on the structured-circuit lane"
        );
        assert_eq!(
            branch_policy_for_official_features(&features),
            VariantBranchPolicy::MabUcb1 {
                epoch_min_conflicts: OFFICIAL_MAIN_LRAT_MAB_EPOCH_MIN_CONFLICTS,
            },
            "the detector must not silently widen official Main/LRAT branch routing"
        );

        let input = VariantInput::new(
            features.num_vars,
            features.num_clauses,
            VariantProofMode::Lrat,
        )
        .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat)
        .with_startup_policy(VariantStartupPolicy::DisableWarmupWalk)
        .with_dense_clique_mab_branch_experiment()
        .with_dense_mutex_focused_restart_gate_experiment();
        let plan = VariantProfilePlan::for_features(SolverVariant::Default, input, &features);

        assert!(
            !plan.config.hot_path.dense_clique_mab_branch_experiment,
            "Circuit_multiplier22 must not exercise the dense-clique MAB route"
        );
        assert!(
            !plan
                .config
                .hot_path
                .dense_mutex_focused_restart_gate_experiment,
            "Circuit_multiplier22 must not exercise the dense-mutex restart route"
        );
        assert!(
            !plan.config.features.bve,
            "circuit feature evidence must not relax the official Main/LRAT BVE clamp"
        );
        assert!(
            !plan.config.features.factor,
            "circuit feature evidence must not relax the official Main/LRAT factor clamp"
        );
        assert!(
            !plan.config.features.sweep,
            "circuit feature evidence must not enable proof-incomplete sweep"
        );
    }

    fn branch_policy_for_official_features(features: &SatFeatures) -> VariantBranchPolicy {
        let input = VariantInput::new(
            features.num_vars,
            features.num_clauses,
            VariantProofMode::Lrat,
        )
        .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat)
        .with_startup_policy(VariantStartupPolicy::DisableWarmupWalk);
        VariantProfilePlan::for_features(SolverVariant::Default, input, features)
            .config
            .branch_policy
    }

    #[test]
    fn test_official_main_lrat_keeps_mab_outside_small_dense_branch_window() {
        fn branch_policy_for_features(num_vars: usize, num_clauses: usize) -> VariantBranchPolicy {
            let features = SatFeatures::from_streaming_counters(num_vars, num_clauses, 0, 0);
            branch_policy_for_official_features(&features)
        }

        let mab = VariantBranchPolicy::MabUcb1 {
            epoch_min_conflicts: OFFICIAL_MAIN_LRAT_MAB_EPOCH_MIN_CONFLICTS,
        };
        assert_eq!(
            branch_policy_for_features(999, 9_990),
            mab,
            "small but non-dense official Main/default/LRAT formulas keep MAB"
        );
        assert_eq!(
            branch_policy_for_features(1000, 11_000),
            mab,
            "dense formulas at the variable cutoff keep MAB"
        );
        assert_eq!(
            branch_policy_for_features(50_000, 600_000),
            mab,
            "large dense official Main/default/LRAT formulas keep MAB"
        );
    }

    #[test]
    fn test_standard_profile_plan_keeps_adaptive_symmetry_specialist() {
        let a = crate::Literal::positive(crate::Variable(0));
        let b = crate::Literal::negative(crate::Variable(1));
        let clauses = vec![vec![a, b]; 8];
        let features = SatFeatures::extract(128, &clauses);
        let input = VariantInput::new(128, clauses.len(), VariantProofMode::Disabled);

        let plan = VariantProfilePlan::for_features(SolverVariant::Default, input, &features);

        assert_eq!(plan.instance_class, InstanceClass::Small);
        assert!(plan.adjusted_features);
        assert!(
            plan.config.features.symmetry,
            "non-official profile planning keeps the small-formula specialist candidate"
        );
        assert!(
            !plan.config.hot_path.prune_conflict_analysis_experiments,
            "standard routing must not inherit official Main hot-loop pruning"
        );
    }

    #[test]
    fn test_lrat_apply_to_solver_clamps_sbva() {
        let config = VariantConfig::for_variant(
            SolverVariant::Aggressive,
            VariantInput::new(32, 96, VariantProofMode::Lrat),
        );
        let mut solver = Solver::new(32);
        config.apply_to_solver(&mut solver);

        assert!(!solver.is_bve_enabled(), "BVE must be disabled for LRAT");
        assert!(
            !solver.is_factor_enabled(),
            "factor must be disabled for LRAT"
        );
        assert!(!solver.is_sbva_enabled(), "SBVA must be disabled for LRAT");
        assert!(
            !solver.is_sweep_enabled(),
            "sweep must be disabled for LRAT"
        );
    }

    #[test]
    fn test_bve_lrat_scout_route_is_default_off_and_official_only() {
        let official_input = VariantInput::new(32, 96, VariantProofMode::Lrat)
            .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat);
        let official_config = VariantConfig::for_variant(SolverVariant::Default, official_input);
        let mut official_solver = Solver::new(32);
        official_config.apply_to_solver(&mut official_solver);

        assert!(
            !official_solver.bve_lrat_scout_route_enabled(),
            "official Main/LRAT BVE scout route must stay default-off"
        );
        assert!(
            !official_solver.is_bve_enabled(),
            "default official Main/LRAT must keep broad BVE clamped"
        );

        let standard_input =
            VariantInput::new(32, 96, VariantProofMode::Lrat).with_bve_lrat_scout_route();
        let standard_config = VariantConfig::for_variant(SolverVariant::Default, standard_input);
        let mut standard_solver = Solver::new(32);
        standard_config.apply_to_solver(&mut standard_solver);

        assert!(
            !standard_solver.bve_lrat_scout_route_enabled(),
            "non-official LRAT route must ignore the internal BVE scout flag"
        );
        assert!(
            !standard_solver.is_bve_enabled(),
            "non-official LRAT must still keep broad BVE clamped"
        );
    }

    #[test]
    fn test_bve_lrat_scout_route_does_not_reopen_broad_lrat_bve() {
        let input = VariantInput::new(32, 96, VariantProofMode::Lrat)
            .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat)
            .with_bve_lrat_scout_route();
        let config = VariantConfig::for_variant(SolverVariant::Default, input);
        let mut solver = Solver::new(32);
        config.apply_to_solver(&mut solver);

        assert!(
            solver.bve_lrat_scout_route_enabled(),
            "official Main/LRAT env hook should enable only the bounded scout route"
        );
        assert!(
            !solver.is_bve_enabled(),
            "bounded scout route must not reopen the broad LRAT BVE feature"
        );
        assert!(
            !solver.is_factor_enabled(),
            "bounded BVE scout route must not relax neighboring LRAT clamps"
        );
        assert!(!solver.is_sbva_enabled());
        assert!(!solver.is_sweep_enabled());
    }

    #[test]
    fn test_fmla_decompose_lrat_preflight_route_is_default_off_and_official_only() {
        let official_input = VariantInput::new(32, 96, VariantProofMode::Lrat)
            .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat);
        let official_config = VariantConfig::for_variant(SolverVariant::Default, official_input);
        let mut official_solver = Solver::new(32);
        official_config.apply_to_solver(&mut official_solver);

        assert!(
            !official_solver.fmla_decompose_lrat_preflight_route_enabled(),
            "official Main/LRAT Fmla decompose route must stay default-off"
        );
        assert!(
            !official_solver.is_decompose_enabled(),
            "default official Main/LRAT must keep broad decompose clamped"
        );

        let standard_input = VariantInput::new(32, 96, VariantProofMode::Lrat)
            .with_fmla_decompose_lrat_preflight_route();
        let standard_config = VariantConfig::for_variant(SolverVariant::Default, standard_input);
        let mut standard_solver = Solver::new(32);
        standard_config.apply_to_solver(&mut standard_solver);

        assert!(
            !standard_solver.fmla_decompose_lrat_preflight_route_enabled(),
            "non-official LRAT route must ignore the internal Fmla decompose flag"
        );
        assert!(
            !standard_solver.is_decompose_enabled(),
            "non-official LRAT must still keep broad decompose clamped"
        );
    }

    #[test]
    fn test_fmla_decompose_lrat_preflight_route_does_not_reopen_broad_lrat_decompose() {
        let input = VariantInput::new(32, 96, VariantProofMode::Lrat)
            .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat)
            .with_fmla_decompose_lrat_preflight_route();
        let config = VariantConfig::for_variant(SolverVariant::Default, input);
        let mut solver = Solver::new(32);
        config.apply_to_solver(&mut solver);

        assert!(
            solver.fmla_decompose_lrat_preflight_route_enabled(),
            "official Main/LRAT env hook should enable only the Fmla preflight route"
        );
        assert!(
            !solver.is_decompose_enabled(),
            "Fmla preflight route must not reopen destructive LRAT decompose"
        );
        assert!(
            !solver.is_bve_enabled(),
            "Fmla preflight route must not relax neighboring LRAT clamps"
        );
        assert!(!solver.is_factor_enabled());
        assert!(!solver.is_sbva_enabled());
        assert!(!solver.is_sweep_enabled());
    }

    #[test]
    fn test_apply_to_solver_sets_feature_profile() {
        let config = VariantConfig::for_variant(
            SolverVariant::Aggressive,
            VariantInput::new(32, 96, VariantProofMode::Disabled),
        );
        let mut solver = Solver::new(32);
        config.apply_to_solver(&mut solver);

        assert!(solver.is_preprocess_enabled());
        assert!(solver.is_full_preprocessing_enabled());
        assert_eq!(solver.inprocessing_feature_profile(), config.features);
        // CaDiCaL-style focused/stable alternation (not stable-only).
        assert!(!solver.stable_only_enabled());
        assert_eq!(
            solver.branch_selector_mode(),
            crate::BranchSelectorMode::LegacyCoupled
        );
        assert!(solver.glucose_restarts_enabled());
        // Small formulas (<5K vars) get full BVE/subsumption effort.
        assert_eq!(solver.bve_effort_permille(), 1000);
    }

    #[test]
    fn test_probe_variant_apply_to_solver_enables_mab_branch_policy() {
        let config = VariantConfig::for_variant(
            SolverVariant::Probe,
            VariantInput::new(32, 96, VariantProofMode::Disabled),
        );
        let mut solver = Solver::new(32);
        config.apply_to_solver(&mut solver);

        assert_eq!(
            solver.branch_selector_mode(),
            crate::BranchSelectorMode::MabUcb1
        );
        assert_eq!(solver.active_branch_heuristic(), BranchHeuristic::Vmtf);
        assert!(!solver.glucose_restarts_enabled());
        assert_eq!(solver.restart_base(), 250);
    }

    #[test]
    fn test_probe_variant_mab_solves_small_unsat_formula() {
        let config = VariantConfig::for_variant(
            SolverVariant::Probe,
            VariantInput::new(2, 4, VariantProofMode::Disabled),
        );
        let mut solver = Solver::new(2);
        config.apply_to_solver(&mut solver);

        let x = crate::Variable(0);
        let y = crate::Variable(1);
        assert!(solver.add_clause(vec![
            crate::Literal::positive(x),
            crate::Literal::positive(y),
        ]));
        assert!(solver.add_clause(vec![
            crate::Literal::positive(x),
            crate::Literal::negative(y),
        ]));
        assert!(solver.add_clause(vec![
            crate::Literal::negative(x),
            crate::Literal::positive(y),
        ]));
        assert!(solver.add_clause(vec![
            crate::Literal::negative(x),
            crate::Literal::negative(y),
        ]));

        let result = solver.solve().into_inner();
        assert!(
            matches!(result, crate::SatResult::Unsat(_)),
            "probe+MAB profile must preserve UNSAT result, got {result:?}"
        );
    }

    #[test]
    fn test_custom_variant_uses_provided_profile() {
        let profile = InprocessingFeatureProfile {
            bve: false,
            vivify: false,
            probe: false,
            ..Default::default()
        };
        let config = VariantConfig::for_variant(
            SolverVariant::Custom(profile),
            VariantInput::new(32, 96, VariantProofMode::Disabled),
        );
        assert!(!config.features.bve);
        assert!(!config.features.vivify);
        assert!(!config.features.probe);
        assert!(config.features.subsume);
        assert!(config.features.sweep);
        let mut solver = Solver::new(32);
        config.apply_to_solver(&mut solver);
        assert_eq!(solver.inprocessing_feature_profile(), profile);
    }

    #[test]
    fn test_custom_variant_default_matches_dimacs_baseline() {
        let custom_default = SolverVariant::Custom(InprocessingFeatureProfile::default());
        let dimacs = SolverVariant::Default;
        let input = VariantInput::new(32, 96, VariantProofMode::Disabled);
        let mut dimacs_features = dimacs.config(input).features;
        // The sparse-band BVE unlock (--sat-no-bve-sparse, default ON) and the
        // substitution-collapse AUTO (--sat-no-subst-auto, default ON since
        // wf_55735963) apply to the Default variant only; Custom profiles are
        // explicit user choices and stay untouched. Normalize so this
        // comparison holds whether or not the A/B knobs are set in the
        // environment.
        dimacs_features.bve = InprocessingFeatureProfile::default().bve;
        dimacs_features.congruence = InprocessingFeatureProfile::default().congruence;
        dimacs_features.decompose = InprocessingFeatureProfile::default().decompose;
        assert_eq!(
            custom_default.config(input).features,
            dimacs_features,
            "Custom(default) should match Default baseline features \
             (modulo the Default-only sparse-band BVE and AUTO-collapse \
             unlocks)"
        );
    }

    #[test]
    fn test_default_variant_restores_dimacs_sat_packet() {
        let config = VariantConfig::for_variant(
            SolverVariant::Default,
            VariantInput::new(32, 96, VariantProofMode::Disabled),
        );
        let mut solver = Solver::new(32);
        config.apply_to_solver(&mut solver);

        // CaDiCaL-style focused/stable alternation (not stable-only).
        assert!(!solver.stable_only_enabled());
        assert!(solver.is_full_preprocessing_enabled());
        // Small formulas (<5K vars) get full BVE/subsumption effort.
        assert_eq!(solver.bve_effort_permille(), 1000);
    }

    #[test]
    fn test_default_variant_large_formula_stays_in_quick_preprocess() {
        let config = VariantConfig::for_variant(
            SolverVariant::Default,
            VariantInput::new(
                10_000,
                DIMACS_FULL_PREPROCESS_MAX_CLAUSES + 1,
                VariantProofMode::Disabled,
            ),
        );
        let mut solver = Solver::new(10_000);
        config.apply_to_solver(&mut solver);

        // CaDiCaL-style focused/stable alternation (not stable-only).
        assert!(!solver.stable_only_enabled());
        assert!(!solver.is_full_preprocessing_enabled());
    }

    #[test]
    fn test_all_variants_have_unique_names() {
        let names: Vec<&str> = SolverVariant::ALL.iter().map(|v| v.as_str()).collect();
        let mut unique = names.clone();
        unique.sort_unstable();
        unique.dedup();
        assert_eq!(names.len(), unique.len(), "variant names must be unique");
    }

    #[test]
    fn test_all_variants_have_unique_binary_names() {
        let names: Vec<&str> = SolverVariant::ALL.iter().map(|v| v.binary_name()).collect();
        let mut unique = names.clone();
        unique.sort_unstable();
        unique.dedup();
        assert_eq!(names.len(), unique.len(), "binary names must be unique");
    }

    #[test]
    fn test_parse_roundtrip() {
        for variant in SolverVariant::ALL {
            let name = variant.as_str();
            let parsed = SolverVariant::parse(name);
            assert_eq!(parsed, Some(variant), "parse('{name}') should roundtrip");
        }
    }

    #[test]
    fn test_parse_unknown_returns_none() {
        assert_eq!(SolverVariant::parse("nonexistent"), None);
        assert_eq!(SolverVariant::parse(""), None);
    }

    /// Parsed header counts of the shapes the giant raw-BVE band arithmetic
    /// turns on. `cabp-V-nos6.mtx.rnd-k275` is the witness this arm exists
    /// for: at HEAD, with the route inert, AY reports `bve_eliminated: 0` and
    /// `factor_count: 0` on it while kissat solves it.
    const CABP_V_NOS6_K275: (usize, usize) = (1_529_550, 8_599_702);
    const CABP_X_CAN715_K108: (usize, usize) = (1_622_335, 13_805_307);
    const GIANT_FLOOR_4D6E18E5: (usize, usize) = (7_300_000, 40_700_000);
    const GIANT_FLOOR_00FD8AC9: (usize, usize) = (23_400_000, 63_000_000);

    fn giant_raw_route_armed(counts: (usize, usize), proof: VariantProofMode) -> bool {
        let _guard = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
            bve_giant_raw: Some(true),
            ..Default::default()
        });
        SolverVariant::Default
            .config(VariantInput::new(counts.0, counts.1, proof))
            .bve_giant_raw_route_active()
    }

    /// The arm ships OFF: with default switches the route refuses the witness
    /// exactly as the retired `if true { return false; }` gate did.
    #[test]
    fn bve_giant_raw_route_is_default_off_on_the_cabp_witness() {
        let _guard = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches::default());
        let config = SolverVariant::Default.config(VariantInput::new(
            CABP_V_NOS6_K275.0,
            CABP_V_NOS6_K275.1,
            VariantProofMode::Disabled,
        ));
        assert!(
            !config.bve_giant_raw_route_active(),
            "default config must leave the giant raw-BVE route inert"
        );
    }

    /// Band arithmetic of the clause-ceiling re-pin (8M ->
    /// `AUTO_CONGRUENCE_GIANT_MAX_CLAUSES` 10M): it admits the `cabp-V`
    /// family, and the untouched 2M VAR ceiling is what still excludes the
    /// giant SAT floor controls. `cabp-X` (13.8M clauses) stays out of band —
    /// the re-pin follows the probe cap, it does not chase instances.
    #[test]
    fn bve_giant_raw_band_admits_cabp_v_and_still_excludes_the_giant_floor() {
        assert!(
            giant_raw_route_armed(CABP_V_NOS6_K275, VariantProofMode::Disabled),
            "the 8.60M-clause witness must be in band at the re-pinned ceiling"
        );
        assert!(
            !giant_raw_route_armed(CABP_X_CAN715_K108, VariantProofMode::Disabled),
            "13.8M clauses is above the probe cap and must stay out of band"
        );
        assert!(
            !giant_raw_route_armed(GIANT_FLOOR_4D6E18E5, VariantProofMode::Disabled),
            "floor control 4d6e18e5 must stay excluded by the 2M var ceiling"
        );
        assert!(
            !giant_raw_route_armed(GIANT_FLOOR_00FD8AC9, VariantProofMode::Disabled),
            "floor control 00fd8ac9 must stay excluded by the 2M var ceiling"
        );
    }

    /// The route fails closed under LRAT even when armed, so a proof-mode A/B
    /// of this arm is only meaningful on a DRAT surface.
    #[test]
    fn bve_giant_raw_route_fails_closed_under_lrat() {
        assert!(
            giant_raw_route_armed(CABP_V_NOS6_K275, VariantProofMode::Drat),
            "DRAT keeps the armed route live"
        );
        assert!(
            !giant_raw_route_armed(CABP_V_NOS6_K275, VariantProofMode::Lrat),
            "LRAT must refuse the route before the band is consulted"
        );
    }

    #[test]
    fn test_four_variants_produce_distinct_configs() {
        let input = VariantInput::new(1000, 5000, VariantProofMode::Disabled);
        let configs: Vec<VariantConfig> =
            SolverVariant::ALL.iter().map(|v| v.config(input)).collect();

        // Verify that no two configs are identical
        for i in 0..configs.len() {
            for j in (i + 1)..configs.len() {
                let same_features = configs[i].features == configs[j].features;
                let same_restart = configs[i].restart_policy == configs[j].restart_policy;
                let same_branch = configs[i].branch_policy == configs[j].branch_policy;
                let same_preproc = configs[i].full_preprocessing == configs[j].full_preprocessing;
                assert!(
                    !(same_features && same_restart && same_branch && same_preproc),
                    "variants {} and {} must differ in at least one dimension",
                    configs[i].name(),
                    configs[j].name(),
                );
            }
        }
    }
}
