// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solve options.

use crate::tune::{Knob, Profile, Setting};
use std::time::{Duration, Instant};

/// A rejected [`EngineEconomics`] setting.
///
/// Returned at *construction*, not at solve time. The alternative — accept
/// anything and clamp during the solve — was measured to be the worse contract
/// for the crate's primary in-process consumer: `AY_MILP_SAT_STOP_MULT=-1`
/// reached `Duration::mul_f64`, which panics, so a malformed value inherited
/// from a CI shell could abort a verifier worker mid-solve
/// (the development design notes §M1, consequence 3). A typed
/// error at the builder puts the failure where the caller can act on it, and
/// makes an accepted `EngineEconomics` a value the solve path can trust
/// without re-checking.
#[derive(Debug, Clone, Copy, PartialEq, thiserror::Error)]
#[non_exhaustive]
pub enum EngineConfigError {
    /// A NaN or infinite setting.
    #[error("{knob} must be finite, got {value}")]
    NotFinite {
        /// The knob's stable name, as an operator would spell it.
        knob: &'static str,
        /// The rejected value.
        value: f64,
    },
    /// A finite setting outside the knob's admissible range.
    #[error("{knob} must lie in [{low}, {high}], got {value}")]
    OutOfRange {
        /// The knob's stable name, as an operator would spell it.
        knob: &'static str,
        /// The rejected value.
        value: f64,
        /// Inclusive lower bound.
        low: f64,
        /// Inclusive upper bound.
        high: f64,
    },
}

fn checked(knob: Knob, value: f64, low: f64, high: f64) -> Result<f64, EngineConfigError> {
    if !value.is_finite() {
        return Err(EngineConfigError::NotFinite {
            knob: knob.env(),
            value,
        });
    }
    if value < low || value > high {
        return Err(EngineConfigError::OutOfRange {
            knob: knob.env(),
            value,
            low,
            high,
        });
    }
    Ok(value)
}

/// Seconds ceiling for a [`Duration`]-valued knob: the engine's own real-knob
/// domain, so the builder cannot admit a value the accessor would then discard.
///
/// `Duration::MAX.as_secs_f64()` rounds *up* past `u64::MAX`, so a caller
/// spelling "no cap" as `Duration::MAX` would hand the consuming site a value
/// that panics `Duration::from_secs_f64` on the way back. Clamping — rather
/// than erroring — is right here because the intent is unambiguous: ~31 million
/// years is "no cap" by any reading, and refusing it would be pedantry, where a
/// negative share is a genuine mistake worth reporting.
const MAX_KNOB_SECS: f64 = crate::tune::MAX_REAL;

/// Per-solve engine search economics.
///
/// # What this is for
///
/// Every knob here was reachable only through a process-global `AY_MILP_*`
/// environment variable. That is not merely inelegant for an in-process
/// consumer: `std::env::set_var` races with a concurrent `getenv` (hence
/// `unsafe` in edition 2024), and ay-milp's primary consumer is a
/// multi-threaded verifier whose workers can be inside one solve while another
/// thread configures the next. It also makes per-instance policy impossible —
/// a recipe for one model class necessarily applies to every concurrent solve
/// in the process. the development design notes §M1 is the
/// full statement of the problem.
///
/// These settings are **per-`SolveOpts`**, carried on the solve rather than on
/// the process, so two concurrent sessions can differ. They also outrank the
/// environment, so a stray `AY_MILP_*` inherited from a CI shell cannot
/// reconfigure a solve that set them.
///
/// # Every field is optional, and that is load-bearing
///
/// `None` means *this solve has no opinion*, and resolution falls through to
/// exactly the environment variable and compiled default the engine used
/// before. A default `EngineEconomics` is therefore bit-identical in behaviour
/// to not having one, which is what makes it safe to put on every
/// [`SolveOpts`].
///
/// # Soundness class
///
/// No setting here can make a reported value, bound, verdict or certificate
/// *wrong*. None of them is consulted when a bound is admitted: every verdict
/// still rests on the exact certificate path, so what a setting changes is
/// which incumbent the search finds, how fast it gets there, and therefore how
/// much it manages to prove inside a budget.
///
/// One documented exception, and it is the reason it is settable:
/// [`with_lattice`](Self::with_lattice) governs a lane that can return
/// `Optimal { cert: None }` — a sound value with no exportable evidence. A
/// consumer that consumes optimal values as rigorous bounds should either
/// disable that lane or, better,
/// [`with_require_certificates`](SolveOpts::with_require_certificates), which
/// degrades exactly that outcome to `Unknown { CertificateUnavailable }`.
///
/// (Classifying the *rest* of the engine's switchable heuristics this way is a
/// separate, larger piece of work; see §M2 of the same document.)
#[derive(Debug, Clone, Copy, PartialEq, Default)]
#[non_exhaustive]
pub struct EngineEconomics {
    lattice: Option<bool>,
    saturation_stop: Option<bool>,
    saturation_stop_floor: Option<f64>,
    saturation_stop_multiplier: Option<f64>,
    bloom_cap_relaxation: Option<bool>,
    flip_lns_cap: Option<f64>,
    flip_lns_share: Option<f64>,
    warm_lu: Option<bool>,
    presolve_share: Option<f64>,
    cuts: Option<bool>,
    pump_restarts: Option<usize>,
    dive_max_pins: Option<usize>,
}

impl EngineEconomics {
    /// No opinion about anything: behaviourally identical to the default
    /// engine.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Run the market-split lattice detector (`AY_MILP_NO_LATTICE`).
    ///
    /// Default on. It is self-gating on the markshare1 shape and silent on
    /// every other model, but it can return `Optimal { cert: None }`, so a
    /// consumer that treats optimal values as rigorous bounds may prefer it
    /// off — or, better, may prefer
    /// [`SolveOpts::with_require_certificates`], which already maps that
    /// outcome to `Unknown { CertificateUnavailable }`.
    #[must_use]
    pub fn with_lattice(mut self, enabled: bool) -> Self {
        self.lattice = Some(enabled);
        self
    }

    /// Run the flip-LNS saturation stop (`AY_MILP_NO_SAT_STOP`).
    ///
    /// Default on, scoped to `tall_lu` models. It hands a saturated incumbent
    /// walk's remaining budget to the tree.
    #[must_use]
    pub fn with_saturation_stop(mut self, enabled: bool) -> Self {
        self.saturation_stop = Some(enabled);
        self
    }

    /// Dry-spell floor before the flip-LNS walk counts as saturated
    /// (`AY_MILP_SAT_STOP_SECS`; default 15 s).
    #[must_use]
    pub fn with_saturation_stop_floor(mut self, floor: Duration) -> Self {
        self.saturation_stop_floor = Some(floor.as_secs_f64().min(MAX_KNOB_SECS));
        self
    }

    /// Multiplier on the largest observed improvement gap, above which a dry
    /// spell counts as saturation (`AY_MILP_SAT_STOP_MULT`; default 1.5).
    ///
    /// # Errors
    ///
    /// [`EngineConfigError`] if `multiplier` is not finite and non-negative;
    /// the value multiplies a `Duration`, which panics on either.
    pub fn with_saturation_stop_multiplier(
        mut self,
        multiplier: f64,
    ) -> Result<Self, EngineConfigError> {
        self.saturation_stop_multiplier =
            Some(checked(Knob::SatStopMult, multiplier, 0.0, MAX_KNOB_SECS)?);
        Ok(self)
    }

    /// Relax the bloom cap on tall-degenerate warm dual walks
    /// (`AY_MILP_NO_BLOOM_RELAX`).
    ///
    /// Default on. Verdict-neutral either way: it changes only the float pivot
    /// sequence, and every exit is re-checked and every leaf re-derived
    /// exactly.
    #[must_use]
    pub fn with_bloom_cap_relaxation(mut self, enabled: bool) -> Self {
        self.bloom_cap_relaxation = Some(enabled);
        self
    }

    /// Absolute cap on the flip-LNS window for `tall_lu` models
    /// (`AY_MILP_FLIP_CAP_SECS`).
    ///
    /// Ignored when [`with_flip_lns_share`](Self::with_flip_lns_share) is also
    /// set, which opts into the pure fractional schedule — the same coupling
    /// the environment variables have always had.
    #[must_use]
    pub fn with_flip_lns_cap(mut self, cap: Duration) -> Self {
        self.flip_lns_cap = Some(cap.as_secs_f64().min(MAX_KNOB_SECS));
        self
    }

    /// Fraction of the remaining budget given to the flip-LNS incumbent walk
    /// (`AY_MILP_FLIP_SHARE`).
    ///
    /// Setting this also **disables the absolute cap**, restoring the pure
    /// fractional schedule on both LP lanes.
    ///
    /// # Errors
    ///
    /// [`EngineConfigError`] unless `share` is finite and in `[0, 1]`. A share
    /// above 1 would ask for a window longer than the budget it is a share of.
    pub fn with_flip_lns_share(mut self, share: f64) -> Result<Self, EngineConfigError> {
        self.flip_lns_share = Some(checked(Knob::FlipShare, share, 0.0, 1.0)?);
        Ok(self)
    }

    /// Install an LU engine in the pooled bound-change re-solver
    /// (`AY_MILP_WARM_LU`).
    ///
    /// Default **off**, and deliberately so: the LU inverse is not bitwise the
    /// eta inverse, so it can move which LP vertex the flip-LNS lands on and
    /// therefore which incumbent it rounds. Gated to `tall_lu`/`wide_tall`
    /// models either way.
    #[must_use]
    pub fn with_warm_lu(mut self, enabled: bool) -> Self {
        self.warm_lu = Some(enabled);
        self
    }

    /// Fraction of the remaining budget given to bound-propagation presolve
    /// (`AY_MILP_PRESOLVE_SHARE`).
    ///
    /// A short presolve deadline yields weaker-but-valid partial bounds, never
    /// a wrong one: the cap trades bound tightness for tree budget and cannot
    /// trade correctness.
    ///
    /// # Errors
    ///
    /// [`EngineConfigError`] unless `share` is finite and in `[0, 1]`.
    pub fn with_presolve_share(mut self, share: f64) -> Result<Self, EngineConfigError> {
        self.presolve_share = Some(checked(Knob::PresolveShare, share, 0.0, 1.0)?);
        Ok(self)
    }

    /// Separate cuts at the root (`AY_MILP_NO_CUTS`).
    ///
    /// Default on.
    #[must_use]
    pub fn with_cuts(mut self, enabled: bool) -> Self {
        self.cuts = Some(enabled);
        self
    }

    /// Feasibility-pump restart allowance (`AY_MILP_PUMP_RESTARTS`).
    ///
    /// `0` skips the pump outright. Unset leaves the engine's own
    /// shape-dependent allowance in force, which is not a single number — so
    /// setting this overrides a *decision*, not just a budget.
    #[must_use]
    pub fn with_pump_restarts(mut self, restarts: usize) -> Self {
        self.pump_restarts = Some(restarts);
        self
    }

    /// Cap on the pins the terminal-salvage dive commits
    /// (`AY_MILP_DIVE_MAX_PINS`; default uncapped).
    ///
    /// Capping both reproduces a solvable pin set run-to-run and stops paying
    /// for doomed deeper probes. Note this knob is instance-family-tuned by
    /// nature; a principled auto-cap inside the engine is the recorded fix and
    /// this is the interim.
    #[must_use]
    pub fn with_dive_max_pins(mut self, pins: usize) -> Self {
        self.dive_max_pins = Some(pins);
        self
    }

    /// Whether the lattice detector is explicitly configured for this solve.
    #[must_use]
    pub fn lattice(&self) -> Option<bool> {
        self.lattice
    }

    /// Whether the flip-LNS saturation stop is explicitly configured.
    #[must_use]
    pub fn saturation_stop(&self) -> Option<bool> {
        self.saturation_stop
    }

    /// The explicitly configured saturation-stop dry-spell floor.
    #[must_use]
    pub fn saturation_stop_floor(&self) -> Option<Duration> {
        self.saturation_stop_floor.map(Duration::from_secs_f64)
    }

    /// The explicitly configured saturation-stop multiplier.
    #[must_use]
    pub fn saturation_stop_multiplier(&self) -> Option<f64> {
        self.saturation_stop_multiplier
    }

    /// Whether the bloom-cap relaxation is explicitly configured.
    #[must_use]
    pub fn bloom_cap_relaxation(&self) -> Option<bool> {
        self.bloom_cap_relaxation
    }

    /// The explicitly configured absolute flip-LNS window cap.
    #[must_use]
    pub fn flip_lns_cap(&self) -> Option<Duration> {
        self.flip_lns_cap.map(Duration::from_secs_f64)
    }

    /// The explicitly configured flip-LNS budget share.
    #[must_use]
    pub fn flip_lns_share(&self) -> Option<f64> {
        self.flip_lns_share
    }

    /// Whether the pooled re-solver's LU engine is explicitly configured.
    #[must_use]
    pub fn warm_lu(&self) -> Option<bool> {
        self.warm_lu
    }

    /// The explicitly configured presolve budget share.
    #[must_use]
    pub fn presolve_share(&self) -> Option<f64> {
        self.presolve_share
    }

    /// Whether root cuts are explicitly configured.
    #[must_use]
    pub fn cuts(&self) -> Option<bool> {
        self.cuts
    }

    /// The explicitly configured feasibility-pump restart allowance.
    #[must_use]
    pub fn pump_restarts(&self) -> Option<usize> {
        self.pump_restarts
    }

    /// The explicitly configured terminal-salvage dive pin cap.
    #[must_use]
    pub fn dive_max_pins(&self) -> Option<usize> {
        self.dive_max_pins
    }

    /// Lower these settings into the engine's internal knob carrier.
    ///
    /// The `No*` inversions happen here and only here: the public surface is
    /// positive-sense (`with_cuts(false)`) because that is what reads correctly
    /// at a call site, while the knob keeps the environment's own spelling
    /// because an operator's `AY_MILP_NO_CUTS=1` has to keep meaning what it
    /// has always meant.
    pub(crate) fn profile(&self) -> Profile {
        let mut p = Profile::EMPTY;
        if let Some(v) = self.lattice {
            p = p.with(Knob::NoLattice, Setting::Flag(!v));
        }
        if let Some(v) = self.saturation_stop {
            p = p.with(Knob::NoSatStop, Setting::Flag(!v));
        }
        if let Some(v) = self.saturation_stop_floor {
            p = p.with(Knob::SatStopSecs, Setting::Real(v));
        }
        if let Some(v) = self.saturation_stop_multiplier {
            p = p.with(Knob::SatStopMult, Setting::Real(v));
        }
        if let Some(v) = self.bloom_cap_relaxation {
            p = p.with(Knob::NoBloomRelax, Setting::Flag(!v));
        }
        if let Some(v) = self.flip_lns_cap {
            p = p.with(Knob::FlipCapSecs, Setting::Real(v));
        }
        if let Some(v) = self.flip_lns_share {
            p = p.with(Knob::FlipShare, Setting::Real(v));
        }
        if let Some(v) = self.warm_lu {
            p = p.with(Knob::WarmLu, Setting::Flag(v));
        }
        if let Some(v) = self.presolve_share {
            p = p.with(Knob::PresolveShare, Setting::Real(v));
        }
        if let Some(v) = self.cuts {
            p = p.with(Knob::NoCuts, Setting::Flag(!v));
        }
        if let Some(v) = self.pump_restarts {
            p = p.with(Knob::PumpRestarts, Setting::Count(v));
        }
        if let Some(v) = self.dive_max_pins {
            p = p.with(Knob::DiveMaxPins, Setting::Count(v));
        }
        p
    }
}

/// Default-off warm-start strategy for complete fixed assignment trees.
///
/// These modes change only how float advice is obtained before exact leaf
/// certification. Root and prefix statuses never contribute evidence. Ordinary
/// leaves exactify `Optimal` duals or `PrimalInfeasible` Farkas multipliers as
/// before. The first configured non-optimal leaf may instead exactify the
/// prefix candidate's cached true-objective duals under the fully fixed leaf;
/// only a strictly sufficient, independently verified row contributes to the
/// returned proof. Local durations are cooperative caps: zero requests an
/// immediate stop poll, finite values are intersected with the outer proof
/// deadline, and `Duration::MAX` removes only the local cap without extending
/// an outer deadline.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum FixedAssignmentTreeWarmStart {
    /// Solve progressively narrower prefixes before the first complete
    /// assignment, changing one split bound per warm solve. The Gray walk is
    /// translated by `start_assignment`, so it starts there while retaining
    /// one-bit transitions and complete coverage. Each prefix is capped by
    /// `prefix_time_limit` and continues primal phase I directly from the
    /// preceding basis; a locally stopped basis remains float advice only.
    /// The first complete proof leaf first attempts to exactify its cached
    /// true-objective row duals, then may continue that stopped primal state.
    /// Either route must pass independent exact leaf verification.
    ProgressivePrefix {
        prefix_time_limit: Duration,
        start_assignment: u8,
    },
    /// Bound the optional root-fast-path search, then bridge progressively to
    /// `start_assignment`.
    ///
    /// If the root reaches `Optimal` within `root_time_limit`, the historical
    /// exact root-row fast path is still attempted. If it stops at the local
    /// limit, its basis is advice only and complete exact leaf harvesting
    /// continues under the session's outer deadline. Each progressive prefix
    /// has its own `prefix_time_limit`.
    RootProbeThenProgressivePrefix {
        root_time_limit: Duration,
        prefix_time_limit: Duration,
        start_assignment: u8,
    },
}

/// Options for a session's solves.
///
/// `#[non_exhaustive]` with builder methods so the engine can grow options
/// without breaking callers.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct SolveOpts {
    /// Hard wall-clock deadline. Checked inside solve loops; expiry yields
    /// `Outcome::Unknown { reason: Timeout }`, never a partial verdict.
    pub deadline: Option<Instant>,
    /// Per-solve time limit; combines with `deadline` (the earlier wins).
    pub time_limit: Option<Duration>,
    /// Per-node time limit for a warm LP attempt in branch-and-bound. When the
    /// limit expires, the node discards its warm-start hint and retries cold
    /// exactly once under the solve's outer deadline. `None` disables the
    /// warm-only limit; it never extends the outer deadline.
    pub node_warm_time_limit: Option<Duration>,
    /// Worker threads a session may use. Advice at L0 (single-threaded).
    pub threads: u32,
    /// When true (default), identical inputs give identical outcomes
    /// run-to-run.
    pub determinism: bool,
    /// Seed for randomized heuristics (unused while `determinism` holds all
    /// current lanes fixed; reserved for the native engine).
    pub seed: u64,
    /// When true, a verdict whose certificate cannot be produced degrades to
    /// `Outcome::Unknown { reason: CertificateUnavailable }` instead of being
    /// reported bare. Off by default: bare verdicts from the exact lanes are
    /// sound, just unevidenced.
    pub require_certificates: bool,
    /// Bytes the branch-and-bound may RETAIN in its open node set (the
    /// dominant memory at scale: parked warm-start bases). Crossing half the
    /// budget stops new parked nodes from carrying warm hints; crossing the
    /// budget stops the frontier growing at all (depth-first from there, which
    /// holds O(depth)). Running into the budget can cost time and can degrade
    /// an exhausted search to `Feasible`/`Unknown` — never a wrong verdict.
    /// `None` disables the guard.
    pub memory_budget: Option<usize>,
    /// Leaf budget for capturing a whole-tree
    /// [`crate::MilpInfeasibilityCertificate`] on `Infeasible` verdicts from
    /// the native branch-and-bound. The capture is fail-closed: a tree that
    /// needs more leaves, outlives the deadline, or cannot be re-derived in
    /// the caller's model frame yields `tree_cert: None` and the verdict is
    /// unaffected. `0` disables capture entirely.
    pub tree_cert_leaves: usize,
    /// Admit the range-logical triangular-crash LP path for this solve.
    ///
    /// This is an advice-only, default-off path choice. The historical exact
    /// `AY_MILP_RANGE_LOGICAL_CRASH=1` process-environment opt-in remains an
    /// independent compatibility fallback.
    pub(crate) range_logical_triangular_crash: bool,
    /// Per-session override for the cold affine-chain distress-probe iteration
    /// budget. `None` preserves the historical
    /// `AY_MILP_CHAIN_PROBE`/20,000-iteration policy; `Some(0)` disables the
    /// probe for LPs lowered by this session.
    pub(crate) chain_distress_probe_iters: Option<u64>,
    /// Default-off float-basis strategy for the complete fixed assignment-tree
    /// proof API. This is advice only and is deliberately not consulted by the
    /// target-FSB or adaptive tree APIs.
    pub(crate) fixed_assignment_tree_warm_start: Option<FixedAssignmentTreeWarmStart>,
    /// Per-solve search economics. Every field defaults to *no opinion*, so
    /// these options resolve exactly as they did before the carrier existed.
    pub(crate) engine: EngineEconomics,
}

impl Default for SolveOpts {
    fn default() -> Self {
        Self {
            deadline: None,
            time_limit: None,
            node_warm_time_limit: None,
            threads: 1,
            determinism: true,
            seed: 0,
            require_certificates: false,
            memory_budget: Some(2 << 30), // 2 GiB
            tree_cert_leaves: 256,
            range_logical_triangular_crash: false,
            chain_distress_probe_iters: None,
            fixed_assignment_tree_warm_start: None,
            engine: EngineEconomics::new(),
        }
    }
}

impl SolveOpts {
    /// Default options.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Set a hard wall-clock deadline.
    #[must_use]
    pub fn with_deadline(mut self, deadline: Instant) -> Self {
        self.deadline = Some(deadline);
        self
    }

    /// Set a per-solve time limit.
    #[must_use]
    pub fn with_time_limit(mut self, limit: Duration) -> Self {
        self.time_limit = Some(limit);
        self
    }

    /// Set (or disable, with `None`) the per-node warm LP time limit.
    ///
    /// A zero duration is normalized to `None`, matching the historical
    /// zero-means-disabled configuration.
    #[must_use]
    pub fn with_node_warm_time_limit(mut self, limit: Option<Duration>) -> Self {
        self.node_warm_time_limit = limit.filter(|limit| !limit.is_zero());
        self
    }

    /// Set the thread budget.
    #[must_use]
    pub fn with_threads(mut self, threads: u32) -> Self {
        self.threads = threads;
        self
    }

    /// Set determinism.
    #[must_use]
    pub fn with_determinism(mut self, determinism: bool) -> Self {
        self.determinism = determinism;
        self
    }

    /// Set the heuristic seed.
    #[must_use]
    pub fn with_seed(mut self, seed: u64) -> Self {
        self.seed = seed;
        self
    }

    /// Require certificates on certificate-bearing verdicts.
    #[must_use]
    pub fn with_require_certificates(mut self, require: bool) -> Self {
        self.require_certificates = require;
        self
    }

    /// Set (or disable, with `None`) the open-set memory budget in bytes.
    #[must_use]
    pub fn with_memory_budget(mut self, bytes: Option<usize>) -> Self {
        self.memory_budget = bytes;
        self
    }

    /// Set the tree-certificate leaf budget (`0` disables capture).
    #[must_use]
    pub fn with_tree_cert_leaves(mut self, leaves: usize) -> Self {
        self.tree_cert_leaves = leaves;
        self
    }

    /// Request the range-logical triangular-crash LP path for this solve.
    ///
    /// The option is scoped to sessions built from these options and does not
    /// mutate process environment or change the global default.
    #[must_use]
    pub fn with_range_logical_triangular_crash(mut self) -> Self {
        self.range_logical_triangular_crash = true;
        self
    }

    /// Whether this option explicitly requests the range-logical
    /// triangular-crash LP path.
    ///
    /// This reports only the typed per-session setting. The solver separately
    /// honors the historical exact `AY_MILP_RANGE_LOGICAL_CRASH=1`
    /// environment opt-in for compatibility.
    #[must_use]
    pub fn range_logical_triangular_crash(&self) -> bool {
        self.range_logical_triangular_crash
    }

    /// Override the cold affine-chain distress-probe iteration budget for LPs
    /// lowered by this session.
    ///
    /// `None` preserves the historical process policy
    /// (`AY_MILP_CHAIN_PROBE`, defaulting to 20,000 iterations). `Some(0)`
    /// disables the probe without mutating process-global environment.
    #[must_use]
    pub fn with_chain_distress_probe_iters(mut self, iters: Option<u64>) -> Self {
        self.chain_distress_probe_iters = iters;
        self
    }

    /// The typed per-session chain distress-probe override.
    ///
    /// This excludes the historical environment/default fallback, which the
    /// simplex resolves only when no typed override is present.
    #[must_use]
    pub fn chain_distress_probe_iters(&self) -> Option<u64> {
        self.chain_distress_probe_iters
    }

    /// Select a default-off warm-start strategy for complete fixed assignment
    /// trees.
    ///
    /// This option is proof-neutral: root probes and prefix solves supply float
    /// bases only, including when their local cap yields `Stopped`. Final
    /// leaves retain the same exactification and independent
    /// certificate-verification requirements as the default path.
    #[must_use]
    pub fn with_fixed_assignment_tree_warm_start(
        mut self,
        strategy: Option<FixedAssignmentTreeWarmStart>,
    ) -> Self {
        self.fixed_assignment_tree_warm_start = strategy;
        self
    }

    /// The typed per-session fixed assignment-tree warm-start strategy.
    #[must_use]
    pub fn fixed_assignment_tree_warm_start(&self) -> Option<FixedAssignmentTreeWarmStart> {
        self.fixed_assignment_tree_warm_start
    }

    /// Configure per-solve search economics.
    ///
    /// The settings are scoped to solves run from these options: they are
    /// carried on the solve, not written to the process, so two concurrent
    /// sessions can differ and neither can disturb the other. They outrank any
    /// `AY_MILP_*` variable in the environment.
    ///
    /// ```
    /// # use ay_milp::{EngineEconomics, SolveOpts};
    /// # fn main() -> Result<(), ay_milp::EngineConfigError> {
    /// let opts = SolveOpts::new().with_engine(
    ///     EngineEconomics::new()
    ///         .with_lattice(false)
    ///         .with_cuts(false)
    ///         .with_presolve_share(0.02)?
    ///         .with_dive_max_pins(16),
    /// );
    /// # let _ = opts;
    /// # Ok(())
    /// # }
    /// ```
    #[must_use]
    pub fn with_engine(mut self, engine: EngineEconomics) -> Self {
        self.engine = engine;
        self
    }

    /// The per-solve search economics configured for these options.
    #[must_use]
    pub fn engine(&self) -> EngineEconomics {
        self.engine
    }

    /// The effective deadline as of `now`: the earlier of `deadline` and
    /// `now + time_limit`.
    #[must_use]
    pub fn effective_deadline(&self, now: Instant) -> Option<Instant> {
        let from_limit = self.time_limit.map(|l| now + l);
        match (self.deadline, from_limit) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The no-behaviour-change property. A `SolveOpts` that was never handed
    /// an `EngineEconomics` carries one that says nothing, and a profile that
    /// says nothing resolves every knob to the environment-and-default it
    /// resolved to before the carrier existed.
    #[test]
    fn engine_economics_default_to_no_opinion() {
        let engine = SolveOpts::new().engine();
        assert!(engine.profile().is_empty());
        assert_eq!(engine.lattice(), None);
        assert_eq!(engine.saturation_stop(), None);
        assert_eq!(engine.saturation_stop_floor(), None);
        assert_eq!(engine.saturation_stop_multiplier(), None);
        assert_eq!(engine.bloom_cap_relaxation(), None);
        assert_eq!(engine.flip_lns_cap(), None);
        assert_eq!(engine.flip_lns_share(), None);
        assert_eq!(engine.warm_lu(), None);
        assert_eq!(engine.presolve_share(), None);
        assert_eq!(engine.cuts(), None);
        assert_eq!(engine.pump_restarts(), None);
        assert_eq!(engine.dive_max_pins(), None);
    }

    /// The twelve settings a consumer pins today, in one chain, with every
    /// value read back. This is the shape `ay_lib.rs` had to spell as twelve
    /// `set_var` calls on the process environment.
    #[test]
    fn engine_economics_round_trip_through_the_builder() -> Result<(), EngineConfigError> {
        let engine = EngineEconomics::new()
            .with_lattice(false)
            .with_saturation_stop(false)
            .with_saturation_stop_floor(Duration::from_secs(15))
            .with_saturation_stop_multiplier(1.5)?
            .with_bloom_cap_relaxation(false)
            .with_flip_lns_cap(Duration::from_secs(900))
            .with_flip_lns_share(0.25)?
            .with_warm_lu(true)
            .with_presolve_share(0.02)?
            .with_cuts(false)
            .with_pump_restarts(0)
            .with_dive_max_pins(16);

        assert_eq!(engine.lattice(), Some(false));
        assert_eq!(engine.saturation_stop(), Some(false));
        assert_eq!(
            engine.saturation_stop_floor(),
            Some(Duration::from_secs(15))
        );
        assert_eq!(engine.saturation_stop_multiplier(), Some(1.5));
        assert_eq!(engine.bloom_cap_relaxation(), Some(false));
        assert_eq!(engine.flip_lns_cap(), Some(Duration::from_secs(900)));
        assert_eq!(engine.flip_lns_share(), Some(0.25));
        assert_eq!(engine.warm_lu(), Some(true));
        assert_eq!(engine.presolve_share(), Some(0.02));
        assert_eq!(engine.cuts(), Some(false));
        assert_eq!(engine.pump_restarts(), Some(0));
        assert_eq!(engine.dive_max_pins(), Some(16));
        Ok(())
    }

    /// The positive-sense public surface must lower to the negative-sense
    /// engine knobs, and it is the resolved knob — not the field — that the
    /// solver reads. An inversion dropped here would be invisible in every
    /// getter and wrong in every solve.
    #[test]
    fn positive_setters_lower_to_the_negative_kill_switches() -> Result<(), EngineConfigError> {
        let engine = EngineEconomics::new()
            .with_lattice(false)
            .with_saturation_stop(false)
            .with_bloom_cap_relaxation(false)
            .with_cuts(false)
            .with_warm_lu(true)
            .with_dive_max_pins(16)
            .with_pump_restarts(0)
            .with_presolve_share(0.02)?;
        let _active = crate::tune::activate_caller(engine.profile());
        assert!(crate::tune::on(Knob::NoLattice));
        assert!(crate::tune::on(Knob::NoSatStop));
        assert!(crate::tune::on(Knob::NoBloomRelax));
        assert!(crate::tune::on(Knob::NoCuts));
        assert!(crate::tune::on(Knob::WarmLu));
        assert_eq!(crate::tune::count(Knob::DiveMaxPins, usize::MAX), 16);
        assert_eq!(crate::tune::count_opt(Knob::PumpRestarts), Some(0));
        assert_eq!(crate::tune::real(Knob::PresolveShare, 0.35), 0.02);

        let on = EngineEconomics::new()
            .with_lattice(true)
            .with_cuts(true)
            .with_warm_lu(false);
        let _active = crate::tune::activate_caller(on.profile());
        assert!(!crate::tune::on(Knob::NoLattice));
        assert!(!crate::tune::on(Knob::NoCuts));
        assert!(!crate::tune::on(Knob::WarmLu));
        Ok(())
    }

    /// Malformed input is refused at construction and cannot reach a solve.
    /// Every value here used to be accepted from the environment, and the two
    /// negatives used to panic `Duration::mul_f64`/`from_secs_f64` mid-solve.
    #[test]
    fn out_of_range_settings_are_rejected_not_clamped() {
        assert_eq!(
            EngineEconomics::new().with_presolve_share(1.5),
            Err(EngineConfigError::OutOfRange {
                knob: "AY_MILP_PRESOLVE_SHARE",
                value: 1.5,
                low: 0.0,
                high: 1.0,
            })
        );
        assert_eq!(
            EngineEconomics::new().with_flip_lns_share(-0.25),
            Err(EngineConfigError::OutOfRange {
                knob: "AY_MILP_FLIP_SHARE",
                value: -0.25,
                low: 0.0,
                high: 1.0,
            })
        );
        assert_eq!(
            EngineEconomics::new().with_saturation_stop_multiplier(-1.0),
            Err(EngineConfigError::OutOfRange {
                knob: "AY_MILP_SAT_STOP_MULT",
                value: -1.0,
                low: 0.0,
                high: MAX_KNOB_SECS,
            })
        );
        assert_eq!(
            EngineEconomics::new().with_presolve_share(f64::INFINITY),
            Err(EngineConfigError::NotFinite {
                knob: "AY_MILP_PRESOLVE_SHARE",
                value: f64::INFINITY,
            })
        );
        assert!(matches!(
            EngineEconomics::new().with_saturation_stop_multiplier(f64::NAN),
            Err(EngineConfigError::NotFinite { .. })
        ));
        // A rejected setter returns the error INSTEAD of a value, so there is
        // no half-configured `EngineEconomics` to carry into a solve.
        assert_eq!(SolveOpts::new().engine(), EngineEconomics::new());
    }

    /// `Duration::MAX` is an unambiguous "no cap" and must not become a value
    /// that panics `Duration::from_secs_f64` at the consuming site.
    #[test]
    fn an_unbounded_duration_clamps_instead_of_overflowing() {
        let engine = EngineEconomics::new()
            .with_flip_lns_cap(Duration::MAX)
            .with_saturation_stop_floor(Duration::MAX);
        let cap = engine.flip_lns_cap().expect("set");
        assert_eq!(cap, Duration::from_secs_f64(MAX_KNOB_SECS));
        assert!(engine.saturation_stop_floor().is_some());
    }

    /// END TO END, THROUGH A REAL SOLVE. The recipe a consumer pins reaches
    /// the engine, and the verdict is the same exact rational either way.
    ///
    /// This is the test that would catch the plumbing being wired to nothing:
    /// `activate_caller` is installed at the branch-and-bound entry, so a
    /// `SolveOpts` carrying twelve settings must produce the same optimum as
    /// one carrying none, on a model whose optimum is known by inspection.
    /// Both directions are exercised — every switch off, then every switch on —
    /// because a knob that is honoured in only one direction is a knob that is
    /// not honoured.
    #[test]
    fn a_configured_solve_returns_the_same_exact_optimum() -> Result<(), EngineConfigError> {
        use crate::model::{Model, Sense};
        use crate::Outcome;

        // min -3a - 2b - 4c  s.t.  a + b + c <= 2, all binary.  Optimum: pick
        // c and a, value -7.
        let mut m = Model::new();
        let a = m.add_binary_col();
        let b = m.add_binary_col();
        let c = m.add_binary_col();
        m.add_row(f64::NEG_INFINITY, 2.0, &[(a, 1.0), (b, 1.0), (c, 1.0)]);
        m.set_objective(&[(a, -3.0), (b, -2.0), (c, -4.0)], Sense::Minimize);

        let want = num_rational::BigRational::from_integer((-7).into());
        let recipes = [
            SolveOpts::new(),
            SolveOpts::new().with_engine(
                EngineEconomics::new()
                    .with_lattice(false)
                    .with_saturation_stop(false)
                    .with_saturation_stop_floor(Duration::from_secs(15))
                    .with_saturation_stop_multiplier(1.5)?
                    .with_bloom_cap_relaxation(false)
                    .with_flip_lns_cap(Duration::from_secs(900))
                    .with_flip_lns_share(0.25)?
                    .with_warm_lu(true)
                    .with_presolve_share(0.02)?
                    .with_cuts(false)
                    .with_pump_restarts(0)
                    .with_dive_max_pins(16),
            ),
            SolveOpts::new().with_engine(
                EngineEconomics::new()
                    .with_lattice(true)
                    .with_saturation_stop(true)
                    .with_bloom_cap_relaxation(true)
                    .with_warm_lu(false)
                    .with_cuts(true)
                    .with_presolve_share(1.0)?,
            ),
        ];
        for (i, opts) in recipes.iter().enumerate() {
            match crate::bab::solve_milp(&m, opts) {
                Outcome::Optimal { value, .. } => {
                    assert_eq!(value, want, "recipe {i} must land the same optimum");
                }
                other => panic!("recipe {i}: expected Optimal, got {other:?}"),
            }
        }
        Ok(())
    }

    /// Per-`SolveOpts`, not per-process: configuring one set of options cannot
    /// reach another.
    #[test]
    fn engine_economics_are_scoped_to_their_options() {
        let default = SolveOpts::new();
        let configured = default
            .clone()
            .with_engine(EngineEconomics::new().with_cuts(false));
        assert_eq!(configured.engine().cuts(), Some(false));
        assert_eq!(
            default.engine().cuts(),
            None,
            "building a configured sibling must not mutate the original options"
        );
    }

    #[test]
    fn node_warm_time_limit_defaults_off() {
        assert_eq!(SolveOpts::new().node_warm_time_limit, None);
    }

    #[test]
    fn node_warm_time_limit_builder_normalizes_zero_and_none() {
        let finite = Duration::from_millis(250);
        assert_eq!(
            SolveOpts::new()
                .with_node_warm_time_limit(Some(finite))
                .node_warm_time_limit,
            Some(finite)
        );
        assert_eq!(
            SolveOpts::new()
                .with_node_warm_time_limit(Some(Duration::ZERO))
                .node_warm_time_limit,
            None
        );
        assert_eq!(
            SolveOpts::new()
                .with_node_warm_time_limit(None)
                .node_warm_time_limit,
            None
        );
    }

    #[test]
    fn range_logical_triangular_crash_defaults_off_and_is_scoped() {
        let default = SolveOpts::new();
        let explicit = default.clone().with_range_logical_triangular_crash();

        assert!(!default.range_logical_triangular_crash());
        assert!(explicit.range_logical_triangular_crash());
        assert!(
            !default.range_logical_triangular_crash(),
            "building an opted-in sibling must not change the original options"
        );
    }

    #[test]
    fn chain_distress_probe_iters_defaults_to_historical_policy() {
        assert_eq!(SolveOpts::new().chain_distress_probe_iters(), None);
    }

    #[test]
    fn chain_distress_probe_iters_builder_is_typed_and_scoped() {
        let default = SolveOpts::new();
        let finite = default
            .clone()
            .with_chain_distress_probe_iters(Some(12_345));
        let disabled = default.clone().with_chain_distress_probe_iters(Some(0));

        assert_eq!(finite.chain_distress_probe_iters(), Some(12_345));
        assert_eq!(disabled.chain_distress_probe_iters(), Some(0));
        assert_eq!(
            finite
                .with_chain_distress_probe_iters(None)
                .chain_distress_probe_iters(),
            None
        );
        assert_eq!(
            default.chain_distress_probe_iters(),
            None,
            "building configured siblings must not mutate the original options"
        );
    }

    #[test]
    fn fixed_assignment_tree_warm_start_defaults_off_and_is_scoped() {
        let default = SolveOpts::new();
        let bridge = default.clone().with_fixed_assignment_tree_warm_start(Some(
            FixedAssignmentTreeWarmStart::ProgressivePrefix {
                prefix_time_limit: Duration::from_millis(100),
                start_assignment: 1,
            },
        ));
        let probe = default.clone().with_fixed_assignment_tree_warm_start(Some(
            FixedAssignmentTreeWarmStart::RootProbeThenProgressivePrefix {
                root_time_limit: Duration::from_millis(250),
                prefix_time_limit: Duration::from_millis(100),
                start_assignment: 9,
            },
        ));

        assert_eq!(default.fixed_assignment_tree_warm_start(), None);
        assert_eq!(
            bridge.fixed_assignment_tree_warm_start(),
            Some(FixedAssignmentTreeWarmStart::ProgressivePrefix {
                prefix_time_limit: Duration::from_millis(100),
                start_assignment: 1,
            })
        );
        assert_eq!(
            probe.fixed_assignment_tree_warm_start(),
            Some(
                FixedAssignmentTreeWarmStart::RootProbeThenProgressivePrefix {
                    root_time_limit: Duration::from_millis(250),
                    prefix_time_limit: Duration::from_millis(100),
                    start_assignment: 9,
                }
            )
        );
        assert_eq!(
            probe
                .with_fixed_assignment_tree_warm_start(None)
                .fixed_assignment_tree_warm_start(),
            None
        );
        assert_eq!(
            default.fixed_assignment_tree_warm_start(),
            None,
            "building configured siblings must not mutate the original options"
        );
    }
}
