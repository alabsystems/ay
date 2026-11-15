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
use std::time::{Duration, Instant};

use ay_chc::{
    engines, AdaptiveConfig, AdaptiveExecutionMode, AdaptivePortfolio, BudgetPolicy,
    CancellationToken, ChcProblem, ChcProofRunWithBudgetReport, ChcQueryObligation,
    ChcQueryObligationId, EngineType, InvariantModel, LemmaHint, PdrConfig, VerifiedChcResult,
};

use crate::proof::ProofRun;
use crate::verdict::AyVerdict;

mod query_replay;

#[cfg(test)]
mod memory_tests;
#[cfg(test)]
mod proof_cancellation_tests;

pub use crate::query_proof_report::{
    QueryObligationBatchProofReport, QueryObligationBatchVerdict, QueryObligationProofReportRow,
    CHC_QUERY_BATCH_PROOF_REPORT_SCHEMA, CHC_QUERY_OBLIGATION_SET_SCHEMA,
};

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
/// `Engine::Auto`, no timeout, `ProofMode::None`, adaptive/parallel execution.
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
    /// Portfolio scheduling policy (default adaptive/parallel).
    ///
    /// Select [`AdaptiveExecutionMode::DeterministicSequential`] for stable
    /// regression measurements: engines run in the canonical fixed order and
    /// receive deterministic shares of the total timeout.
    pub execution_mode: AdaptiveExecutionMode,
    /// Per-context term-store budget in bytes for portfolio and PDR/proof runs.
    ///
    /// Set this when multiple model-checker jobs may coexist in one process;
    /// `None` uses AY's process-level default.
    pub memory_budget: Option<usize>,
    /// The proof run's tick budget B, in ay-sat search ticks
    /// ([`ay_chc::PdrConfig::effort`]; default `None`: no change).
    ///
    /// Honoured by the [`ProofMode::Strict`] path, which threads it onto the
    /// PDR proof run: the run stops on its count, and a run that
    /// [`timeout`](Self::timeout) ends reports it as its backstop
    /// (`ChcRunWork::stop` reads `Deadline`, the stop reason
    /// `BudgetExhausted`), never as the count's (`Rlimit`,
    /// `EffortExhausted`). Until P4a slices 9 and 10 the timeout also still
    /// sizes clocks that steer the search on its way: the case split's
    /// deadline and branch budgets, and the thread's solve deadline that
    /// clamps each query's slice (the development design notes §14 lists
    /// them). The adaptive portfolio ([`ProofMode::None`]) has no count
    /// before GuardTree S5 gives its workers nodes, so a solve there with an
    /// effort is refused (`EncodeError::Unimplemented`) rather than run on
    /// clocks the caller asked to replace.
    pub effort: Option<u64>,
    /// Maximum PDR frames for the proof path.
    ///
    /// `None` preserves the production profile. An explicit value is forwarded
    /// unchanged, including zero, to [`PdrConfig::with_max_frames`].
    pub pdr_max_frames: Option<usize>,
}

impl Default for EncodeConfig {
    fn default() -> Self {
        // Preserve AY_DETERMINISTIC for consumers that enter through the
        // shared ay-encode facade rather than constructing AdaptiveConfig.
        let execution_mode = AdaptiveConfig::default().execution_mode();
        Self {
            engine: Engine::Auto,
            timeout: None,
            proof_mode: ProofMode::None,
            strict_validation: false,
            lemma_hints: Vec::new(),
            execution_mode,
            memory_budget: None,
            effort: None,
            pdr_max_frames: None,
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

    /// Select the adaptive portfolio scheduling policy.
    #[must_use]
    pub fn with_execution_mode(mut self, mode: AdaptiveExecutionMode) -> Self {
        self.execution_mode = mode;
        self
    }

    /// Bound term-store memory for portfolio and PDR/proof invocations.
    ///
    /// A zero ceiling refuses solving or validation. This is not an aggregate
    /// process-memory bound; a tighter inherited context ceiling still applies.
    #[must_use]
    pub fn with_memory_budget(mut self, bytes: usize) -> Self {
        self.memory_budget = Some(bytes);
        self
    }

    /// Give the PDR proof run a tick budget of `ticks` ay-sat search ticks
    /// ([`Self::effort`]): honoured under [`ProofMode::Strict`] only.
    #[must_use]
    pub fn with_effort(mut self, ticks: u64) -> Self {
        self.effort = Some(ticks);
        self
    }

    /// Set the PDR proof path's frame cap without changing other controls.
    #[must_use]
    pub fn with_pdr_max_frames(mut self, frames: usize) -> Self {
        self.pdr_max_frames = Some(frames);
        self
    }

    /// `Err` when an effort is set on the adaptive portfolio path, which has
    /// no count to honour it with ([`Self::effort`]).
    fn refuse_portfolio_effort(&self) -> crate::Result<()> {
        match self.effort {
            Some(_) => Err(crate::EncodeError::Unimplemented(
                "an effort on the adaptive portfolio path (it gains a count with GuardTree S5)",
            )),
            None => Ok(()),
        }
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
        cfg = cfg.with_execution_mode(self.execution_mode);
        if let Some(bytes) = self.memory_budget {
            cfg = cfg.with_memory_budget(bytes);
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
    /// Applies the timeout as PDR's `solve_timeout`, and the effort, if any,
    /// as its `effort`, and retains the requested per-context term-memory
    /// ceiling, including zero. `strict_proofs` is *not*
    /// set here on purpose: [`ay_chc::engines::solve_pdr_proof`] forces it on
    /// internally (see its contract), so setting it twice would be redundant.
    /// The [`Engine`] selection does not apply to this path — `solve_pdr_proof`
    /// always drives the PDR/IC3 engine — so it is ignored here.
    #[must_use]
    pub fn to_pdr_config(&self) -> PdrConfig {
        // `production(verbose)` builds a full owned config (it already sets every
        // technique toggle and falls back to `..Self::default()` for the rest),
        // so we layer only the explicit invocation controls on it. We pass
        // `verbose = false` to match model-checker-consumer's `PdrConfig::production(false)`
        // call sites on the proof path.
        let mut cfg = PdrConfig::production(false).with_memory_budget(self.memory_budget);
        cfg.solve_timeout = self.timeout;
        cfg.effort = self.effort;
        if let Some(frames) = self.pdr_max_frames {
            cfg = cfg.with_max_frames(frames);
        }
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
/// [`crate::proof::Certificate`] and threaded onto [`AyVerdict::Proved`]. The
/// proof run's metered work ([`ProofRun::work`]) is not in the verdict: to
/// have both, call [`solve_with_proof`] and [`ProofRun::verdict`], the same
/// verdict.
pub fn solve(problem: ChcProblem, config: &EncodeConfig) -> crate::Result<AyVerdict> {
    solve_impl(problem, config, None)
}

/// Run one solve linked to a caller-owned cooperative-cancellation token.
///
/// The caller may cancel `parent` from another thread or arm it with
/// [`CancellationToken::cancel_after`]. Cancellation is fail-closed: an
/// in-flight solve winds down as `Unknown` and can never become Safe or Unsafe
/// merely because cancellation was requested.
pub fn solve_with_cancellation(
    problem: ChcProblem,
    config: &EncodeConfig,
    parent: &CancellationToken,
) -> crate::Result<AyVerdict> {
    solve_impl(problem, config, Some(parent))
}

fn solve_impl(
    problem: ChcProblem,
    config: &EncodeConfig,
    cancellation: Option<&CancellationToken>,
) -> crate::Result<AyVerdict> {
    match config.proof_mode {
        ProofMode::None => {
            config.refuse_portfolio_effort()?;
            // Catch AY-classified solver panics on the portfolio path and map
            // them to `EncodeError::SolverPanicked` (G3). Non-AY (programmer
            // error) panics re-propagate. The `Strict` path already runs under
            // `ay_chc::engines::solve_pdr_proof`'s own `catch_ay_panics`, so it
            // needs no extra wrapper here.
            let adaptive_config = config.to_adaptive_config();
            let portfolio = match cancellation {
                Some(parent) => AdaptivePortfolio::new_for_solve_with_cancellation(
                    problem,
                    adaptive_config,
                    parent,
                ),
                None => AdaptivePortfolio::new_for_solve(problem, adaptive_config),
            };
            let raw: VerifiedChcResult =
                ay_core::catch_ay_panics(AssertUnwindSafe(|| Ok(portfolio.solve())), |reason| {
                    Err(crate::EncodeError::SolverPanicked(reason))
                })?;
            Ok(crate::verdict::from_verified(raw, None))
        }
        // On the Safe path the verdict carries the re-checkable certificate
        // built from the proof run's transcript; on Unsafe/Unknown there is no
        // proof artifact. The run's metered work is dropped here: a caller
        // that wants it calls `solve_with_proof` and `ProofRun::verdict`.
        ProofMode::Strict => Ok(solve_with_proof_impl(problem, config, cancellation)?.verdict()),
    }
}

/// Result for one independently solved safety query.
///
/// Errors and `Unknown` verdicts are local to this obligation; they do not
/// prevent later obligations in the batch from running.
#[derive(Debug)]
#[must_use = "each per-query result must be consumed"]
pub struct QueryObligationOutcome {
    id: ChcQueryObligationId,
    outcome: crate::Result<AyVerdict>,
}

impl QueryObligationOutcome {
    /// Stable identity copied from the source problem's query slice.
    pub fn id(&self) -> &ChcQueryObligationId {
        &self.id
    }

    /// Borrow the verdict or invocation error for this query.
    pub fn outcome(&self) -> &crate::Result<AyVerdict> {
        &self.outcome
    }

    /// Consume this row and return its identity and outcome.
    pub fn into_parts(self) -> (ChcQueryObligationId, crate::Result<AyVerdict>) {
        (self.id, self.outcome)
    }
}

/// Solve every active query independently and return all partial results.
///
/// [`ChcProblem::query_obligations`] unfolds the common nullary aggregate
/// marker and backwards-slices each property before this function invokes AY.
/// Results stay in deterministic source-clause order.  A timeout, `Unknown`,
/// or solver error for one property is recorded in that row and does not block
/// later properties.
///
/// Each row preserves `config`'s dispatch semantics: [`ProofMode::None`] keeps
/// the caller-selected adaptive or deterministic routing, while
/// [`ProofMode::Strict`] remains the same direct-PDR route as [`solve`]. AY
/// synchronously cancels and reaps every worker before an invocation returns,
/// so source-ordered row `i + 1` never overlaps hidden solver workers from row
/// `i` or multiplies the configured portfolio memory envelope.
///
/// `EncodeConfig::timeout` is a **per-obligation** budget here.  Consequently a
/// batch of `N` difficult queries can consume up to `N * timeout`; callers that
/// need a batch-wide deadline should combine this API with cooperative
/// cancellation. Invalid input, including a problem with no query, returns a
/// typed [`crate::EncodeError::Chc`]. `Ok([])` is reserved for a validated
/// problem whose queries were all simplified away as vacuously Safe.
pub fn solve_query_obligations(
    problem: &ChcProblem,
    config: &EncodeConfig,
) -> crate::Result<Vec<QueryObligationOutcome>> {
    let obligations = problem.query_obligations()?;
    Ok(collect_query_obligation_outcomes_with(
        obligations,
        |problem| solve(problem, config),
    ))
}

/// Solve every active query independently under one caller-owned cancellation
/// token, preserving one partial-result row per surviving query.
///
/// A cancellation request reaches the obligation currently in flight. Any
/// later obligation is recorded as [`crate::EncodeError::Cancelled`] without
/// starting another portfolio. A caller can impose a batch-wide wall clock by
/// keeping the guard returned by [`CancellationToken::cancel_after`] alive for
/// this call; `EncodeConfig::timeout` remains the per-obligation cap.
pub fn solve_query_obligations_with_cancellation(
    problem: &ChcProblem,
    config: &EncodeConfig,
    parent: &CancellationToken,
) -> crate::Result<Vec<QueryObligationOutcome>> {
    let obligations = problem.query_obligations()?;
    Ok(collect_query_obligation_outcomes_with(
        obligations,
        |problem| {
            if parent.is_cancelled() {
                Err(crate::EncodeError::Cancelled)
            } else {
                solve_with_cancellation(problem, config, parent)
            }
        },
    ))
}

/// Solve every active query independently and retain each authoritative proof report.
///
/// Unlike [`solve_query_obligations`], this entry point keeps the exact
/// [`ChcProofRunWithBudgetReport`] for every successfully invoked row and binds
/// the complete ordered row set to the normalized aggregate source problem.
/// The returned aggregate reports Safe only when every surviving query has
/// definitive proof-accepted Safe evidence, and reports Unsafe when any row
/// has definitive proof-accepted counterexample evidence.
///
/// Construction and row enumeration remain AY-owned: callers cannot supply a
/// subset, pair a report with a different [`ChcQueryObligationId`], or inject a
/// transformation between slicing and the authoritative solve. As with
/// [`solve_query_obligations`], `EncodeConfig::timeout` is per obligation.
pub fn solve_query_obligations_with_proof_report(
    problem: &ChcProblem,
    config: &EncodeConfig,
) -> crate::Result<QueryObligationBatchProofReport> {
    solve_query_obligations_with_proof_report_impl(
        problem,
        config,
        None,
        QueryProofReplay::MetadataOnly,
    )
}

/// Solve every active query and independently replay each definitive result.
///
/// This is the proof-admission counterpart of
/// [`solve_query_obligations_with_proof_report`]. Each row is solved exactly
/// once, then a replay pass receives `replay_budget`. Successful replay can
/// make the typed in-process batch admissible to the Trust full verifier;
/// failed or exhausted replay remains explicit metadata-only evidence and can
/// never change the row verdict.
///
/// The solve timeout in [`EncodeConfig`] and `replay_budget` are separate
/// per-obligation limits. Rows remain sequential, so at most one solver or
/// replay pass is live at a time.
pub fn solve_query_obligations_with_checked_proof_report(
    problem: &ChcProblem,
    config: &EncodeConfig,
    replay_budget: Duration,
) -> crate::Result<QueryObligationBatchProofReport> {
    solve_query_obligations_with_proof_report_impl(
        problem,
        config,
        None,
        QueryProofReplay::Checked(replay_budget),
    )
}

/// Solve every active query with checked replay under caller-owned cancellation.
///
/// This combines the source-bound, proof-admitting report from
/// [`solve_query_obligations_with_checked_proof_report`] with the cooperative
/// cancellation behavior of
/// [`solve_query_obligations_with_proof_report_with_cancellation`]. The parent
/// token reaches the row currently being solved and its checked-replay pass,
/// and is checked before any later row is started. Consequently a caller may
/// arm one batch-wide deadline with [`CancellationToken::cancel_after`]
/// without losing any source-ordered row identities: work not started after
/// cancellation is recorded as [`crate::EncodeError::Cancelled`].
///
/// `EncodeConfig::timeout` and `replay_budget` remain separate per-obligation
/// limits. During checked replay the same parent token is polled alongside
/// the original replay allowance; an observed refusal is sticky, even if the
/// caller later resets the token. Ground export/validation is cooperative;
/// the full token also reaches active SMT search and mandatory certification.
/// Offline checking, metadata, source slicing and allocation/destruction still
/// contain opaque intervals. This is not a hard deadline or a 100 ms
/// cancellation bound. A failed or pre-cancelled replay cannot newly upgrade
/// a row to Trust-full-verifier-admissible evidence. The report's cancellation
/// snapshot and stop reason still describe the original solve completion.
pub fn solve_query_obligations_with_checked_proof_report_with_cancellation(
    problem: &ChcProblem,
    config: &EncodeConfig,
    replay_budget: Duration,
    parent: &CancellationToken,
) -> crate::Result<QueryObligationBatchProofReport> {
    solve_query_obligations_with_proof_report_impl(
        problem,
        config,
        Some(parent),
        QueryProofReplay::Checked(replay_budget),
    )
}

/// Source-bound multi-query proof reporting under caller-owned cancellation.
///
/// A pre-existing or concurrent request reaches the active row. Rows that have
/// not started when cancellation is observed are retained as
/// [`crate::EncodeError::Cancelled`] instead of being omitted, so an incomplete
/// batch can never look like an all-proved conjunction.
pub fn solve_query_obligations_with_proof_report_with_cancellation(
    problem: &ChcProblem,
    config: &EncodeConfig,
    parent: &CancellationToken,
) -> crate::Result<QueryObligationBatchProofReport> {
    solve_query_obligations_with_proof_report_impl(
        problem,
        config,
        Some(parent),
        QueryProofReplay::MetadataOnly,
    )
}

#[derive(Clone, Copy)]
enum QueryProofReplay {
    MetadataOnly,
    Checked(Duration),
}

fn solve_query_obligations_with_proof_report_impl(
    problem: &ChcProblem,
    config: &EncodeConfig,
    cancellation: Option<&CancellationToken>,
    replay: QueryProofReplay,
) -> crate::Result<QueryObligationBatchProofReport> {
    let started = Instant::now();
    let source_pruned_false_query_ids = problem.pruned_false_query_ids();
    let source_has_stripped_body_forall = problem.has_stripped_body_forall();
    let source_normalized_input = problem.normalized_input();

    let obligations = problem.query_obligations()?;
    let expected_ids: Vec<_> = obligations
        .iter()
        .map(|obligation| obligation.id().clone())
        .collect();

    // Defensive source/slice binding check before starting any solver. The ID
    // constructor already computes this digest from the same slice, but an
    // internal regression here must fail closed rather than produce a batch
    // whose membership claim and solved input disagree.
    for obligation in &obligations {
        let actual = obligation.problem().normalized_input_sha256();
        if actual != obligation.id().content_sha256() {
            return Err(crate::EncodeError::Chc(ay_chc::ChcError::Internal(
                format!(
                    "query obligation {} digest mismatch: id={}, slice={actual}",
                    obligation.id().label(),
                    obligation.id().content_sha256(),
                ),
            )));
        }
    }

    let rows = obligations
        .into_iter()
        .map(|obligation| {
            let (id, problem) = obligation.into_parts();
            let outcome = if cancellation.is_some_and(CancellationToken::is_cancelled) {
                Err(crate::EncodeError::Cancelled)
            } else {
                solve_with_proof_report_impl(problem, config, cancellation).map(|report| {
                    query_replay::checked_replay_if_requested(
                        report,
                        replay,
                        cancellation,
                        |report, budget, progress| match cancellation {
                            Some(token) => {
                                report.with_checked_replay_with_cancellation(budget, token)
                            }
                            None => report.with_checked_replay_with_progress(budget, progress),
                        },
                    )
                })
            };
            QueryObligationProofReportRow::new(id, outcome)
        })
        .collect();

    QueryObligationBatchProofReport::new(
        source_normalized_input,
        &source_pruned_false_query_ids,
        source_has_stripped_body_forall,
        &expected_ids,
        rows,
        started.elapsed(),
    )
}

/// Apply one solver invocation to every already-validated obligation.
///
/// Kept crate-private so tests can inject `Unknown` and error outcomes without
/// relying on timeouts, while production uses the same non-short-circuiting
/// collection path.
pub(crate) fn collect_query_obligation_outcomes_with<F>(
    obligations: Vec<ChcQueryObligation>,
    mut solve_one: F,
) -> Vec<QueryObligationOutcome>
where
    F: FnMut(ChcProblem) -> crate::Result<AyVerdict>,
{
    obligations
        .into_iter()
        .map(|obligation| {
            let (id, problem) = obligation.into_parts();
            QueryObligationOutcome {
                id,
                outcome: solve_one(problem),
            }
        })
        .collect()
}

/// Run one adaptive solve and return its sealed proof artifacts, stop reason,
/// cancellation state, and whole-run timing atomically.
///
/// Unlike calling [`solve`] and a diagnostic solve separately, every field in
/// this bundle describes the invocation that produced the bound verdict.
/// Per-engine budget entries are currently empty because the legacy reporting
/// path uses a different set of prepasses; AY will not substitute that path for
/// the authoritative production solve just to manufacture attribution.
/// Dispatch exactly mirrors [`solve`]: [`ProofMode::None`] uses the adaptive
/// production portfolio, while [`ProofMode::Strict`] uses the proof-grade
/// direct-PDR entry point. Neither branch performs a diagnostic re-run.
pub fn solve_with_proof_report(
    problem: ChcProblem,
    config: &EncodeConfig,
) -> crate::Result<ChcProofRunWithBudgetReport> {
    solve_with_proof_report_impl(problem, config, None)
}

/// Authoritative proof/report solve linked to a caller-owned cancellation
/// token. The returned bundle records the token's completion-boundary snapshot
/// together with the exact problem-bound result from that same invocation.
pub fn solve_with_proof_report_with_cancellation(
    problem: ChcProblem,
    config: &EncodeConfig,
    parent: &CancellationToken,
) -> crate::Result<ChcProofRunWithBudgetReport> {
    solve_with_proof_report_impl(problem, config, Some(parent))
}

fn solve_with_proof_report_impl(
    problem: ChcProblem,
    config: &EncodeConfig,
    cancellation: Option<&CancellationToken>,
) -> crate::Result<ChcProofRunWithBudgetReport> {
    match config.proof_mode {
        ProofMode::None => {
            config.refuse_portfolio_effort()?;
            let adaptive_config = config.to_adaptive_config();
            let portfolio = match cancellation {
                Some(parent) => AdaptivePortfolio::new_for_solve_with_cancellation(
                    problem,
                    adaptive_config,
                    parent,
                ),
                None => AdaptivePortfolio::new_for_solve(problem, adaptive_config),
            };
            ay_core::catch_ay_panics(
                AssertUnwindSafe(|| Ok(portfolio.solve_proof_run_with_budget_report())),
                |reason| Err(crate::EncodeError::SolverPanicked(reason)),
            )
        }
        ProofMode::Strict => {
            let mut pdr_config = config.to_pdr_config();
            if let Some(parent) = cancellation {
                pdr_config.cancellation_token = Some(parent.child());
            }
            Ok(engines::solve_pdr_proof_with_budget_report(
                problem, pdr_config,
            )?)
        }
    }
}

/// Run the PDR proof engine and return the raw proof run for [`crate::proof`]
/// to digest. Forces `strict_proofs` (via `solve_pdr_proof`'s contract) and a
/// fresh re-validation.
///
/// The [`ay_chc::PdrConfig`] is built from `config` via
/// [`EncodeConfig::to_pdr_config`] (production profile, timeout, effort, memory
/// and candidate hints). Parse/IO/internal AY failures surface as [`crate::EncodeError::Chc`];
/// an inconclusive or unvalidated search comes back as a `ProofRun` whose result
/// is `Unknown` (and `accepted_as_proof() == false`).
pub fn solve_with_proof(problem: ChcProblem, config: &EncodeConfig) -> crate::Result<ProofRun> {
    solve_with_proof_impl(problem, config, None)
}

/// [`solve_with_proof`] linked to a caller-owned cancellation token, as
/// [`solve_with_cancellation`] is to [`solve`]: the run's PDR token is a
/// child of `parent`, so a cancel winds the run down as `Unknown`.
///
/// It uses the same private implementation, production profile, timeout,
/// effort, memory budget, candidate hints, independent validation and
/// problem-bound certificate as [`solve_with_proof`]. No separate solve,
/// reporting rerun or resource grant is introduced. A cancellation observed
/// by AY returns a non-accepted `Unknown` proof run; parse/IO/internal
/// failures retain the existing error behavior.
///
/// Passing an attempt created with [`CancellationToken::sticky_child`] also
/// preserves its observed cancellation across resets of the raw parent or
/// descendants. Start an explicit new solve from the uncancelled original
/// parent for a fresh attempt; this entry never resets the supplied token.
pub fn solve_with_proof_with_cancellation(
    problem: ChcProblem,
    config: &EncodeConfig,
    parent: &CancellationToken,
) -> crate::Result<ProofRun> {
    solve_with_proof_impl(problem, config, Some(parent))
}

fn solve_with_proof_impl(
    problem: ChcProblem,
    config: &EncodeConfig,
    cancellation: Option<&CancellationToken>,
) -> crate::Result<ProofRun> {
    let mut pdr_config = config.to_pdr_config();
    if let Some(parent) = cancellation {
        pdr_config.cancellation_token = Some(parent.child());
    }
    let run = engines::solve_pdr_proof(problem, pdr_config)?;
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
/// [`EncodeConfig::to_pdr_config`] (the same production profile / resource mapping
/// `solve_with_proof` uses).
pub fn prove_with_external_model(
    problem: ChcProblem,
    model: InvariantModel,
    config: &EncodeConfig,
) -> crate::Result<ProofRun> {
    let run = engines::prove_external_invariant_model(problem, model, config.to_pdr_config())?;
    Ok(ProofRun::new(run))
}
