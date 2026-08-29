// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! One invocation surface for both frontends.
//!
//! [`EncodeConfig`] is the single knob set both projects pass in. It maps onto
//! AY's two CHC entry points:
//!
//! - **portfolio** ([`ay_chc::AdaptivePortfolio`]) — classification-driven
//!   engine selection (the "auto" engine; there is no literal `Auto` enum in
//!   AY, so [`Engine::Auto`] is the *default* portfolio path);
//! - **PDR-with-proof** ([`ay_chc::engines::solve_pdr_proof`]) — forces
//!   `strict_proofs` and re-validates, returning a [`ay_chc::ChcPdrProofRun`]
//!   whose transcript [`crate::proof`] can digest.
//!
//! Frontends still own *building* the [`ay_chc::ChcProblem`] (model-checker-consumer's typed
//! lowering, the model-checker consumer's `ChcTranslator`); this module only configures and runs.

use std::panic::AssertUnwindSafe;
use std::time::Duration;

use ay_chc::{
    engines, AdaptiveConfig, AdaptivePortfolio, BudgetPolicy, ChcProblem, EngineType,
    InvariantModel, LemmaHint, PdrConfig, VerifiedChcResult,
};

use crate::proof::ProofRun;
use crate::verdict::AyVerdict;

/// Which CHC engine to drive.
///
/// `Auto` is the production default: it does **not** pin an engine but lets the
/// adaptive portfolio classify the problem and pick. Other variants force the
/// portfolio's preferred-engine order to the named engine.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Engine {
    /// Classification-driven portfolio (the "auto" path). Default.
    #[default]
    Auto,
    /// Force PDR (property-directed reachability) first.
    Pdr,
    /// Force bounded model checking first.
    Bmc,
    /// Force property-directed k-induction first.
    Pdkind,
}

impl Engine {
    /// The [`EngineType`] this forces to the front of the portfolio, if any.
    /// `Auto` returns `None` (no forcing — classification decides).
    #[must_use]
    pub fn forced_engine_type(self) -> Option<EngineType> {
        match self {
            Self::Auto => None,
            Self::Pdr => Some(EngineType::Pdr),
            Self::Bmc => Some(EngineType::Bmc),
            Self::Pdkind => Some(EngineType::Pdkind),
        }
    }
}

/// Whether to demand a re-checkable proof artifact on the Safe path.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ProofMode {
    /// Run the plain adaptive portfolio; keep whatever evidence it produces.
    /// Fast path — no `strict_proofs`, no PDR re-validation.
    #[default]
    None,
    /// Route Safe results through [`ay_chc::engines::solve_pdr_proof`], which
    /// forces `strict_proofs = true` and produces a [`ay_chc::ChcPdrProofRun`]
    /// transcript that [`crate::proof::Certificate`] can capture and re-check.
    Strict,
}

/// The single shared invocation config.
///
/// Both model-checker-consumer and ty construct one of these and call [`solve`]. Defaults:
/// `Engine::Auto`, no timeout, `ProofMode::None`.
#[derive(Debug, Clone)]
pub struct EncodeConfig {
    /// Engine selection (default [`Engine::Auto`]).
    pub engine: Engine,
    /// Total wall-clock budget. `None` means unlimited (caller-controlled).
    pub timeout: Option<Duration>,
    /// Whether to demand a re-checkable certificate (default [`ProofMode::None`]).
    pub proof_mode: ProofMode,
    /// Force `strict_proofs = true` on the adaptive portfolio path, independent
    /// of [`proof_mode`](Self::proof_mode) (default `false`).
    ///
    /// model-checker-consumer's adaptive path re-validates *every* `Safe` result
    /// (`strict_proofs = true` unconditionally), while [`ProofMode::Strict`] only
    /// applies on the dedicated PDR-with-proof path. This knob (G1) lets the
    /// portfolio path opt into the same re-validation without switching to the
    /// PDR engine — preserving the "validated `Safe`" vs "unvalidated `Safe`"
    /// distinction that gates borderline invariants. Ignored on the
    /// [`ProofMode::Strict`] path (`solve_pdr_proof` forces strict internally).
    pub strict_validation: bool,
    /// CANDIDATE lemma hints injected into the PDR run (default empty).
    ///
    /// Threaded onto [`ay_chc::PdrConfig::user_hints`], whose consumer
    /// (`apply_lemma_hints`) VALIDATES every hint via `is_inductive_blocking`
    /// before installing it as a frame lemma — "hints are validated, they are
    /// never trusted" — so a wrong candidate costs one SMT check and is
    /// dropped, never assumed. This is the channel a frontend (model-checker-consumer's
    /// native typed-CHC lane) uses to seed loop-invariant candidates —
    /// e.g. accumulator bounds `acc <= i * per_max` — that PDR's own
    /// generalization struggles to discover.
    pub lemma_hints: Vec<LemmaHint>,
}

impl Default for EncodeConfig {
    fn default() -> Self {
        Self {
            engine: Engine::Auto,
            timeout: None,
            proof_mode: ProofMode::None,
            strict_validation: false,
            lemma_hints: Vec::new(),
        }
    }
}

impl EncodeConfig {
    /// A fresh default config (`Auto` / no timeout / no proof).
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Pin the engine.
    #[must_use]
    pub fn with_engine(mut self, engine: Engine) -> Self {
        self.engine = engine;
        self
    }

    /// Set the total time budget.
    #[must_use]
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }

    /// Set the proof mode.
    #[must_use]
    pub fn with_proof_mode(mut self, proof_mode: ProofMode) -> Self {
        self.proof_mode = proof_mode;
        self
    }

    /// Force `strict_proofs` re-validation on the adaptive portfolio path (G1).
    ///
    /// Use this to make the `Auto`/portfolio path re-validate every `Safe`
    /// result the way model-checker-consumer's `solve_typed_chc_with_adaptive_portfolio` does,
    /// without switching to [`ProofMode::Strict`] (which forces the PDR engine).
    #[must_use]
    pub fn with_strict_validation(mut self, strict: bool) -> Self {
        self.strict_validation = strict;
        self
    }

    /// Seed CANDIDATE lemma hints for the PDR run (validated, never trusted —
    /// see [`EncodeConfig::lemma_hints`]).
    #[must_use]
    pub fn with_lemma_hints(mut self, hints: Vec<LemmaHint>) -> Self {
        self.lemma_hints = hints;
        self
    }

    /// Lower to an [`ay_chc::AdaptiveConfig`] for the portfolio path.
    ///
    /// Applies the timeout as the time budget, forces the chosen engine to the
    /// front of the preferred order (no-op for [`Engine::Auto`]), and turns on
    /// `strict_proofs` when [`ProofMode::Strict`] is selected.
    #[must_use]
    pub fn to_adaptive_config(&self) -> AdaptiveConfig {
        let mut cfg = AdaptiveConfig::default();
        if let Some(t) = self.timeout {
            cfg = cfg.with_time_budget(t);
        }
        if let Some(et) = self.engine.forced_engine_type() {
            cfg = cfg
                .with_preferred_engine_order(vec![et])
                .with_engine_budget(et, BudgetPolicy::MinPercent(100));
        }
        // Re-validate every `Safe` when either the proof mode demands it or the
        // caller asks for strict portfolio validation (G1). This matches
        // model-checker-consumer's adaptive path, which sets `strict_proofs = true`
        // unconditionally.
        if matches!(self.proof_mode, ProofMode::Strict) || self.strict_validation {
            cfg.strict_proofs = true;
        }
        // Same validated-candidate hint channel as the PDR path.
        if !self.lemma_hints.is_empty() {
            cfg = cfg.with_user_hints(self.lemma_hints.clone());
        }
        cfg
    }

    /// Lower to an [`ay_chc::PdrConfig`] for the PDR-with-proof path.
    ///
    /// Starts from [`ay_chc::PdrConfig::production`] (G2) — *not* `default()` —
    /// because model-checker-consumer's PDR paths use the production profile, which differs in
    /// technique toggles (frame/iteration/obligation caps, interpolation, no
    /// entry-CEGAR discharge). Behavior preservation requires the *same*
    /// `PdrConfig`, so the shared path adopts the production profile.
    ///
    /// Applies the timeout as PDR's `solve_timeout`. `strict_proofs` is *not*
    /// set here on purpose: [`ay_chc::engines::solve_pdr_proof`] forces it on
    /// internally (see its contract), so setting it twice would be redundant.
    /// The [`Engine`] selection does not apply to this path — `solve_pdr_proof`
    /// always drives the PDR/IC3 engine — so it is ignored here.
    #[must_use]
    pub fn to_pdr_config(&self) -> PdrConfig {
        // `production(verbose)` builds a full owned config (it already sets every
        // technique toggle and falls back to `..Self::default()` for the rest),
        // so the only public knob we layer on is the timeout. We pass
        // `verbose = false` to match model-checker-consumer's `PdrConfig::production(false)`
        // call sites on the proof path.
        let mut cfg = PdrConfig::production(false);
        cfg.solve_timeout = self.timeout;
        // Candidate hints ride user_hints; `apply_lemma_hints` inductively
        // validates each one before installing (production profile keeps
        // `use_lemma_hints: true`).
        cfg.user_hints = self.lemma_hints.clone();
        cfg
    }
}

/// Run the AY CHC layer on `problem` under `config`, returning a frontend-neutral
/// [`AyVerdict`].
///
/// Dispatch:
/// - [`ProofMode::Strict`] → [`ay_chc::engines::solve_pdr_proof`] (proof run),
/// - otherwise → [`ay_chc::AdaptivePortfolio::solve`] (adaptive portfolio).
///
/// In both cases the raw AY verdict is normalized by [`crate::verdict`]. On the
/// [`ProofMode::Strict`] Safe path the proof run's transcript is captured into a
/// [`crate::proof::Certificate`] and threaded onto [`AyVerdict::Proved`].
pub fn solve(problem: ChcProblem, config: &EncodeConfig) -> crate::Result<AyVerdict> {
    match config.proof_mode {
        ProofMode::None => {
            // Catch AY-classified solver panics on the portfolio path and map
            // them to `EncodeError::SolverPanicked` (G3). Non-AY (programmer
            // error) panics re-propagate. The `Strict` path already runs under
            // `ay_chc::engines::solve_pdr_proof`'s own `catch_ay_panics`, so it
            // needs no extra wrapper here.
            let portfolio = AdaptivePortfolio::new(problem, config.to_adaptive_config());
            let raw: VerifiedChcResult =
                ay_core::catch_ay_panics(AssertUnwindSafe(|| Ok(portfolio.solve())), |reason| {
                    Err(crate::EncodeError::SolverPanicked(reason))
                })?;
            Ok(crate::verdict::from_verified(raw, None))
        }
        ProofMode::Strict => {
            let run: ProofRun = solve_with_proof(problem, config)?;
            // On the Safe path attach the re-checkable certificate built from
            // the proof run's transcript; on Unsafe/Unknown there is no proof
            // artifact and `from_verified` ignores the `None`. Mirror the raw
            // AY verdict either way.
            let raw: VerifiedChcResult = run.result().clone();
            let certificate = if run.accepted_as_proof() && raw.is_safe() {
                Some(Box::new(run.certificate()))
            } else {
                None
            };
            Ok(crate::verdict::from_verified(raw, certificate))
        }
    }
}

/// Run the PDR proof engine and return the raw proof run for [`crate::proof`]
/// to digest. Forces `strict_proofs` (via `solve_pdr_proof`'s contract) and a
/// fresh re-validation.
///
/// The [`ay_chc::PdrConfig`] is built from `config` via
/// [`EncodeConfig::to_pdr_config`] (currently just the timeout → `solve_timeout`
/// mapping). Parse/IO/internal AY failures surface as [`crate::EncodeError::Chc`];
/// an inconclusive or unvalidated search comes back as a `ProofRun` whose result
/// is `Unknown` (and `accepted_as_proof() == false`).
pub fn solve_with_proof(problem: ChcProblem, config: &EncodeConfig) -> crate::Result<ProofRun> {
    let run = engines::solve_pdr_proof(problem, config.to_pdr_config())?;
    Ok(ProofRun::new(run))
}

/// Re-validate an externally-produced candidate invariant `model` for `problem`
/// and, on success, return an ACCEPTED proof-grade [`ProofRun`].
///
/// Thin frontend re-export of
/// [`ay_chc::engines::prove_external_invariant_model`]. The candidate — e.g. a
/// word-level invariant back-translated by `ay_chc::ic3_lane::try_prove_chc_loop`,
/// which is explicitly NOT trusted — is FIRST re-validated with the full init +
/// transition + query clause check; only then is it wrapped as accepted
/// `PdrInvariant` evidence. A rejected/unvalidated candidate comes back as a
/// `ProofRun` whose result is `Unknown` (and `accepted_as_proof() == false`);
/// internal AY panics surface as [`crate::EncodeError::Chc`]. This lets the typed
/// full-verification path consume a re-validated candidate through the same
/// `ProofRun`/`certificate` handoff as [`solve_with_proof`], with the
/// re-validation gate strictly in the way of any accepting verdict.
///
/// The [`ay_chc::PdrConfig`] is built from `config` via
/// [`EncodeConfig::to_pdr_config`] (the same production profile / timeout mapping
/// `solve_with_proof` uses).
pub fn prove_with_external_model(
    problem: ChcProblem,
    model: InvariantModel,
    config: &EncodeConfig,
) -> crate::Result<ProofRun> {
    let run = engines::prove_external_invariant_model(problem, model, config.to_pdr_config())?;
    Ok(ProofRun::new(run))
}
