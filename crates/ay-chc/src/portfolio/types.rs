// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Portfolio configuration and result types.

use crate::bmc::BmcConfig;
use crate::cancellation::CancellationToken;
use crate::cegar::{CegarConfig, CegarResult};
use crate::dar::DarConfig;
use crate::decomposition::DecompositionConfig;
use crate::engine_result::ChcEngineResult;
use crate::imc::ImcConfig;
use crate::kind::KindConfig;
use crate::lawi::LawiConfig;
use crate::pdkind::PdkindConfig;
use crate::pdr::{
    Counterexample, CounterexampleStep, InvariantModel, PdrConfig, PredicateInterpretation,
};
use crate::tpa::{TpaConfig, TpaResult};
use crate::trl::TrlConfig;
use crate::LemmaHint;
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::time::Duration;

// ---------------------------------------------------------------------------
// Engine type identifier and budget control types (#8418)
// ---------------------------------------------------------------------------

/// Identifies a CHC engine type for budget control purposes.
///
/// This enum is the key for per-engine budget policies. Each variant
/// corresponds to an [`EngineConfig`] variant. It is intentionally separate
/// from `EngineConfig` so that budget policies can be specified without
/// constructing full engine configurations.
///
/// Part of #8418: portfolio engine budget control API.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum EngineType {
    /// PDR (Property-Directed Reachability)
    Pdr,
    /// Bounded Model Checking
    Bmc,
    /// PDKIND (Property-Directed K-Induction)
    Pdkind,
    /// Transition Power Abstraction
    Tpa,
    /// Transitive Relation Learning
    Trl,
    /// K-Induction (forward/backward)
    Kind,
    /// SCC Decomposition
    Decomposition,
    /// Interpolation-based Model Checking
    Imc,
    /// Lazy Abstraction with Interpolants
    Lawi,
    /// Dual Approximated Reachability
    Dar,
    /// Counterexample-Guided Abstraction Refinement
    Cegar,
}

impl std::fmt::Display for EngineType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name())
    }
}

// Part of #8775: make `EngineType` the canonical engine-id for the shared
// `ay-dispatch` scheduler. `EngineType` already satisfies every super-trait
// required by `EngineId` (`Debug + Clone + Copy + PartialEq + Eq + Hash` via
// derive, plus `Send + Sync + 'static` because every variant is a fieldless
// C-like enum). Wiring this impl here unlocks dispatch-side schedulers
// (`FixedOrderSchedule`, bandits) against the real portfolio engine ids, so
// ay-dispatch stops being dead code in ay-chc (AUDIT-2 / Y1).
impl ay_dispatch::EngineId for EngineType {}

impl EngineType {
    /// Human-readable engine name.
    pub fn name(&self) -> &'static str {
        match self {
            Self::Pdr => "PDR",
            Self::Bmc => "BMC",
            Self::Pdkind => "PDKIND",
            Self::Tpa => "TPA",
            Self::Trl => "TRL",
            Self::Kind => "Kind",
            Self::Decomposition => "Decomposition",
            Self::Imc => "IMC",
            Self::Lawi => "LAWI",
            Self::Dar => "DAR",
            Self::Cegar => "CEGAR",
        }
    }
}

/// Per-engine budget allocation policy.
///
/// Controls what fraction of the total timeout budget a specific engine
/// receives. The portfolio respects these policies when splitting time
/// across engines, ensuring no engine is starved.
///
/// Part of #8418: portfolio engine budget control API.
#[derive(Debug, Clone, Copy, PartialEq)]
#[non_exhaustive]
pub enum BudgetPolicy {
    /// Engine receives at least `percent`% of the total budget.
    /// Clamped to [1, 100]. Values above 100 are treated as 100.
    /// The portfolio may give more time if other engines finish early.
    MinPercent(u8),
    /// Engine receives a fixed time budget, independent of the total timeout.
    /// If the fixed budget exceeds the remaining total, it is clamped.
    Fixed(Duration),
    /// Engine is disabled and will not run.
    Disabled,
    /// Default allocation: the engine participates in equal-share splitting
    /// with the standard minimum guarantee (5% of total budget).
    Default,
}

impl BudgetPolicy {
    /// Minimum budget guarantee as a fraction of total, ensuring no engine
    /// that participates in the portfolio receives less than 5% of total.
    ///
    /// This is the absolute floor for any non-disabled engine. Even
    /// `MinPercent(1)` produces at least `MIN_BUDGET_FLOOR_PERCENT`.
    pub const MIN_BUDGET_FLOOR_PERCENT: u8 = 5;
}

/// Post-solve report of how each engine consumed its budget.
///
/// Returned by `AdaptivePortfolio::solve_with_budget_report()` alongside
/// the `VerifiedChcResult`. Each entry describes one engine's time usage.
///
/// Part of #8418: budget reporting for model-checker-consumer integration.
#[derive(Debug, Clone)]
pub struct BudgetReport {
    /// Per-engine entries in the order engines were launched.
    pub entries: Vec<EngineBudgetEntry>,
    /// Total wall-clock time for the entire solve.
    pub total_elapsed: Duration,
}

impl BudgetReport {
    pub(crate) fn new() -> Self {
        Self {
            entries: Vec::new(),
            total_elapsed: Duration::ZERO,
        }
    }

    /// Number of engines that produced a definitive result.
    pub fn completed_count(&self) -> usize {
        self.entries
            .iter()
            .filter(|e| matches!(e.stop_reason, EngineStopReason::Completed))
            .count()
    }

    /// Number of engines that timed out.
    pub fn timeout_count(&self) -> usize {
        self.entries
            .iter()
            .filter(|e| matches!(e.stop_reason, EngineStopReason::Timeout))
            .count()
    }
}

impl std::fmt::Display for BudgetReport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "Budget Report (total: {:.1}s):",
            self.total_elapsed.as_secs_f64()
        )?;
        for entry in &self.entries {
            writeln!(
                f,
                "  {} [{}]: {:.1}s / {:.1}s ({})",
                entry.engine.name(),
                entry.index,
                entry.elapsed.as_secs_f64(),
                entry.budget_allocated.as_secs_f64(),
                entry.stop_reason,
            )?;
        }
        Ok(())
    }
}

/// One engine's budget usage in the post-solve report.
#[derive(Debug, Clone)]
pub struct EngineBudgetEntry {
    /// Which engine this entry describes.
    pub engine: EngineType,
    /// Engine index in the portfolio launch order.
    pub index: usize,
    /// How much budget was allocated to this engine.
    pub budget_allocated: Duration,
    /// How much wall-clock time this engine actually consumed.
    pub elapsed: Duration,
    /// Why this engine stopped.
    pub stop_reason: EngineStopReason,
}

/// Why an engine stopped running.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum EngineStopReason {
    /// Engine completed with a definitive result (Safe or Unsafe).
    Completed,
    /// Engine ran out of its allocated budget.
    Timeout,
    /// Engine was cancelled because another engine found a result.
    Superseded,
    /// Engine returned Unknown within its budget.
    Unknown,
    /// Engine was disabled by budget policy and did not run.
    Disabled,
    /// Engine returned NotApplicable for the problem class.
    NotApplicable,
    /// Engine self-reported hopelessness and gave up early (item 5a):
    /// PDR's convergence monitor reached `Stuck` with the opt-in
    /// `give_up_on_stuck` flag set by a scheduler that had another lane to
    /// try, so the remaining budget was released instead of burned.
    Hopeless,
}

impl std::fmt::Display for EngineStopReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Completed => f.write_str("completed"),
            Self::Timeout => f.write_str("timeout"),
            Self::Superseded => f.write_str("superseded"),
            Self::Unknown => f.write_str("unknown"),
            Self::Disabled => f.write_str("disabled"),
            Self::NotApplicable => f.write_str("not_applicable"),
            Self::Hopeless => f.write_str("hopeless"),
        }
    }
}

/// Configuration for an individual engine
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum EngineConfig {
    /// PDR engine with configuration
    Pdr(PdrConfig),
    /// BMC engine with configuration
    Bmc(BmcConfig),
    /// PDKIND engine with configuration
    Pdkind(PdkindConfig),
    /// TPA engine with configuration
    Tpa(TpaConfig),
    /// TRL engine with configuration
    Trl(TrlConfig),
    /// Kind engine with configuration (forward/backward k-induction)
    Kind(KindConfig),
    /// Decomposition engine with configuration
    /// Decomposes multi-predicate problems into SCCs and solves sequentially
    Decomposition(DecompositionConfig),
    /// IMC engine with configuration
    Imc(ImcConfig),
    /// LAWI engine with configuration
    Lawi(LawiConfig),
    /// DAR engine with configuration (Dual Approximated Reachability)
    Dar(DarConfig),
    /// CEGAR engine with configuration
    Cegar(CegarConfig),
}

impl EngineConfig {
    /// Create a PDKIND engine with default configuration.
    ///
    /// `PdkindConfig` is crate-internal; this is the public way to add a
    /// PDKIND engine to a portfolio.
    pub fn pdkind_default() -> Self {
        Self::Pdkind(PdkindConfig::default())
    }

    /// Human-readable engine name for diagnostics.
    pub(crate) fn name(&self) -> &'static str {
        match self {
            Self::Pdr(_) => "PDR",
            Self::Bmc(_) => "BMC",
            Self::Pdkind(_) => "PDKIND",
            Self::Imc(_) => "IMC",
            Self::Lawi(_) => "LAWI",
            Self::Dar(_) => "DAR",
            Self::Tpa(_) => "TPA",
            Self::Trl(_) => "TRL",
            Self::Kind(_) => "Kind",
            Self::Decomposition(_) => "Decomposition",
            Self::Cegar(_) => "CEGAR",
        }
    }

    /// Return the [`EngineType`] for this engine configuration.
    ///
    /// Used by the budget control API to match policies to engines.
    /// Part of #8418.
    pub fn engine_type(&self) -> EngineType {
        match self {
            Self::Pdr(_) => EngineType::Pdr,
            Self::Bmc(_) => EngineType::Bmc,
            Self::Pdkind(_) => EngineType::Pdkind,
            Self::Tpa(_) => EngineType::Tpa,
            Self::Trl(_) => EngineType::Trl,
            Self::Kind(_) => EngineType::Kind,
            Self::Decomposition(_) => EngineType::Decomposition,
            Self::Imc(_) => EngineType::Imc,
            Self::Lawi(_) => EngineType::Lawi,
            Self::Dar(_) => EngineType::Dar,
            Self::Cegar(_) => EngineType::Cegar,
        }
    }

    /// Create the Unknown EngineResult for this engine type.
    ///
    /// Used for panic recovery (#2728): when an engine panics, we wrap it as Unknown
    /// using the correct variant so downstream logging and validation correctly
    /// attributes the result. This is an exhaustive match — adding a new EngineConfig
    /// variant forces updating this method (compile error).
    pub(super) fn unknown_result(&self) -> EngineResult {
        match self {
            Self::Pdr(_)
            | Self::Bmc(_)
            | Self::Trl(_)
            | Self::Imc(_)
            | Self::Lawi(_)
            | Self::Dar(_)
            | Self::Kind(_)
            | Self::Decomposition(_) => {
                EngineResult::Unified(ChcEngineResult::Unknown, self.name())
            }
            Self::Pdkind(_) => EngineResult::Unified(ChcEngineResult::Unknown, "PDKIND"),
            Self::Tpa(_) => EngineResult::Tpa(TpaResult::Unknown),
            Self::Cegar(_) => EngineResult::Cegar(CegarResult::Unknown),
        }
    }

    /// Inject a cancellation token into the engine config.
    ///
    /// PDR stores the token directly; all other engines store it in `base`.
    pub(super) fn inject_cancellation_token(&mut self, token: CancellationToken) {
        match self {
            Self::Pdr(c) => c.cancellation_token = Some(token),
            Self::Bmc(c) => c.base.cancellation_token = Some(token),
            Self::Pdkind(c) => c.base.cancellation_token = Some(token),
            Self::Imc(c) => c.base.cancellation_token = Some(token),
            Self::Lawi(c) => c.base.cancellation_token = Some(token),
            Self::Dar(c) => c.base.cancellation_token = Some(token),
            Self::Tpa(c) => c.base.cancellation_token = Some(token),
            Self::Trl(c) => c.base.cancellation_token = Some(token),
            Self::Kind(c) => c.base.cancellation_token = Some(token),
            Self::Decomposition(c) => c.base.cancellation_token = Some(token),
            Self::Cegar(c) => c.base.cancellation_token = Some(token),
        }
    }

    /// Opt PDR engines into the early hopeless self-report (item 5a).
    ///
    /// Called ONLY by scheduler contexts that have another lane to try
    /// (sequential mode with a successor engine; adaptive staged strategies
    /// with a subsequent stage). No-op for non-PDR engines.
    pub(super) fn enable_give_up_on_stuck(&mut self) {
        if let Self::Pdr(c) = self {
            c.give_up_on_stuck = true;
        }
    }

    /// Inject strict_proofs into PDR engine configs (#8555).
    ///
    /// When strict_proofs is true, PDR's internal model verification will
    /// reject models when concrete cross-checks are budget-exhausted rather
    /// than trusting the SMT result.
    pub(super) fn inject_strict_proofs(&mut self, strict: bool) {
        if let Self::Pdr(c) = self {
            c.strict_proofs = strict;
        }
    }

    /// Inject a sequential lemma cache into PDR engine configs (#7919).
    pub(super) fn inject_lemma_cache(&mut self, cache: &crate::lemma_cache::LemmaCache) {
        if let Self::Pdr(c) = self {
            c.lemma_cache = Some(cache.clone());
        }
    }

    /// Seed a PDR engine with accumulated lemmas from the cache (#7919).
    pub(super) fn seed_from_lemma_cache(&mut self, cache: &crate::lemma_cache::LemmaCache) {
        if let Self::Pdr(c) = self {
            let pool = cache.snapshot();
            if !pool.is_empty() {
                c.lemma_hints = Some(pool);
            }
        }
    }

    /// Inject a cooperative blackboard and engine index into the engine config.
    ///
    /// PDR and CEGAR engines use the blackboard for sharing learned
    /// lemmas/predicates. Other engines silently ignore it.
    pub(super) fn inject_blackboard(
        &mut self,
        blackboard: std::sync::Arc<crate::blackboard::SharedBlackboard>,
        engine_idx: usize,
    ) {
        match self {
            Self::Pdr(c) => {
                c.blackboard = Some(blackboard);
                c.engine_idx = engine_idx;
            }
            Self::Cegar(c) => {
                c.blackboard = Some(blackboard);
                c.engine_idx = engine_idx;
            }
            _ => {}
        }
    }
}

/// Portfolio solver configuration
#[derive(Debug, Clone)]
pub struct PortfolioConfig {
    /// Engines to run (order matters for sequential mode)
    pub(crate) engines: Vec<EngineConfig>,
    /// Run engines in parallel (true) or sequential (false)
    pub(crate) parallel: bool,
    /// Timeout per engine in sequential mode (None = no timeout).
    ///
    /// When this timeout expires, the current engine is cooperatively cancelled
    /// (via a cancellation token) and treated as returning `Unknown`; the
    /// portfolio then proceeds to the next engine.
    pub(crate) timeout: Option<Duration>,
    /// Overall timeout for parallel mode (None = no timeout)
    /// When specified, portfolio will return Unknown if no engine produces
    /// a definitive result within this duration.
    pub(crate) parallel_timeout: Option<Duration>,
    /// Enable verbose output
    pub(crate) verbose: bool,
    /// Enable preprocessing (clause inlining, etc.)
    /// Default: true - ClauseInliner is applied before solving.
    pub(crate) enable_preprocessing: bool,
    /// Strict proof mode: trust-proof fallbacks become errors (#8555).
    ///
    /// When true, any code path that would accept a result without full
    /// independent proof verification returns a rejection instead. This
    /// catches silent fallbacks where proof generation or verification
    /// failures are accepted without error.
    pub(crate) strict_proofs: bool,
    /// Per-engine budget policies (#8418).
    ///
    /// When non-empty, the portfolio applies these policies during budget
    /// splitting. Engines not mentioned in this map receive `BudgetPolicy::Default`.
    /// Engines with `BudgetPolicy::Disabled` are removed before solving.
    pub(crate) engine_budgets: FxHashMap<EngineType, BudgetPolicy>,
    /// Per-portfolio term memory budget in bytes (#8629).
    ///
    /// When `Some(bytes)`, the portfolio divides this budget equally across
    /// engines: each engine's `term_memory_budget` is `bytes / engine_count`.
    /// This overrides the global `TermStore::per_engine_budget()` for THIS
    /// portfolio, enabling multiple concurrent solves in a shared process
    /// (e.g., model-checker-consumer) without OOM.
    ///
    /// When `None` (default), per-engine budgets fall back to the global
    /// `TermStore::per_engine_budget()`.
    pub(crate) memory_budget: Option<usize>,
    /// External cooperative-cancellation parent token (item 5).
    ///
    /// When set (adaptive layer / embedding driver), the portfolio's internal
    /// cancellation token is created as a CHILD of this token: cancelling the
    /// parent stops all engines and validation sub-solvers, while the
    /// portfolio's own winner-found/timeout cancels never propagate back to
    /// the parent. `None` (default) keeps a standalone token — identical to
    /// the historical behavior.
    pub(crate) external_cancellation: Option<CancellationToken>,
}

impl Default for PortfolioConfig {
    fn default() -> Self {
        // In test builds, default to the lightweight 3-engine config to avoid
        // spawning 12 threads (96 MB) per test. Production code and tests that
        // need the full engine set should use `production_default()`. (#8604)
        #[cfg(test)]
        {
            Self::test_default()
        }
        #[cfg(not(test))]
        {
            Self::production_default()
        }
    }
}

impl PortfolioConfig {
    /// Full 12-engine production portfolio config.
    ///
    /// This always returns the full engine set regardless of `#[cfg(test)]`.
    /// Use this in tests that specifically need to inspect or test the
    /// production engine roster (e.g., verifying engine count, ordering,
    /// or budget policies across all engines). For tests that just need a
    /// working solver, use `default()` or `test_default()` instead. (#8604)
    pub fn production_default() -> Self {
        // Delegate to EngineSelector::default_engines() for the canonical
        // engine roster (#7946: one engine-policy source of truth).
        Self {
            engines: super::selector::EngineSelector::default_engines(),
            parallel: true,
            timeout: None,
            parallel_timeout: None,
            verbose: false,

            enable_preprocessing: true,
            strict_proofs: false,
            engine_budgets: FxHashMap::default(),
            memory_budget: None,
            external_cancellation: None,
        }
    }

    /// Reduced engine set for test use. Uses PDR + BMC + Kind (3 engines)
    /// instead of the full 12-engine portfolio. Most regression tests only
    /// need correctness, not engine diversity coverage.
    ///
    /// Reduces per-test runtime RSS from ~2.5 GB to ~800 MB by spawning
    /// 3 threads instead of 12 (each with 8 MB stacks).
    pub fn test_default() -> Self {
        Self {
            engines: vec![
                EngineConfig::Pdr(PdrConfig::default()),
                EngineConfig::Bmc(BmcConfig::default()),
                EngineConfig::Kind(KindConfig::default()),
            ],
            parallel: true,
            timeout: None,
            parallel_timeout: None,
            verbose: false,

            enable_preprocessing: true,
            strict_proofs: false,
            engine_budgets: FxHashMap::default(),
            memory_budget: None,
            external_cancellation: None,
        }
    }

    /// Create a config with just TPA
    #[cfg(test)]
    pub(crate) fn tpa_only(config: TpaConfig) -> Self {
        Self {
            engines: vec![EngineConfig::Tpa(config)],
            parallel: false,
            timeout: None,
            parallel_timeout: None,
            verbose: false,

            enable_preprocessing: false,
            strict_proofs: false,
            engine_budgets: FxHashMap::default(),
            memory_budget: None,
            external_cancellation: None,
        }
    }

    /// Get the configured engines.
    pub fn engines(&self) -> &[EngineConfig] {
        &self.engines
    }

    /// Create a portfolio config with the given engines and default settings.
    pub fn with_engines(engines: Vec<EngineConfig>) -> Self {
        Self {
            engines,
            parallel: true,
            timeout: None,
            parallel_timeout: None,
            verbose: false,

            enable_preprocessing: true,
            strict_proofs: false,
            engine_budgets: FxHashMap::default(),
            memory_budget: None,
            external_cancellation: None,
        }
    }

    /// Set parallel mode.
    pub fn parallel(mut self, parallel: bool) -> Self {
        self.parallel = parallel;
        self
    }

    /// Set per-engine timeout (sequential mode).
    pub fn timeout(mut self, timeout: Option<Duration>) -> Self {
        self.timeout = timeout;
        self
    }

    /// Set overall parallel timeout.
    pub fn parallel_timeout(mut self, timeout: Option<Duration>) -> Self {
        self.parallel_timeout = timeout;
        self
    }

    /// Set verbose output.
    pub fn verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }

    /// Set preprocessing (clause inlining, etc.).
    pub fn preprocessing(mut self, enable: bool) -> Self {
        self.enable_preprocessing = enable;
        self
    }

    /// Set user hints on all PDR engines in the portfolio.
    ///
    /// This helper ensures hints are applied to ALL PDR configs, avoiding
    /// partial application when the default portfolio has multiple PDR variants.
    ///
    /// # Example
    /// ```text
    /// let mut config = PortfolioConfig::default();
    /// config.set_pdr_user_hints(vec![hint1, hint2]);
    /// ```
    pub fn set_pdr_user_hints(&mut self, hints: Vec<LemmaHint>) {
        for engine in &mut self.engines {
            if let EngineConfig::Pdr(pdr) = engine {
                pdr.user_hints = hints.clone();
            }
        }
    }

    /// Apply runtime hint providers to all PDR engines in the portfolio.
    ///
    /// Similar to [`set_pdr_user_hints`](Self::set_pdr_user_hints), but for
    /// dynamic `LemmaHintProvider` implementations instead of pre-computed hints.
    pub fn set_pdr_user_hint_providers(&mut self, providers: crate::lemma_hints::HintProviders) {
        for engine in &mut self.engines {
            if let EngineConfig::Pdr(pdr) = engine {
                pdr.user_hint_providers = providers.clone();
            }
        }
    }

    /// Seed all PDR engines with a cross-engine lemma pool (#7919).
    ///
    /// Converts the pool's learned lemmas into `PdrConfig::lemma_hints` on each
    /// PDR engine in the portfolio. This is the entry point for transferring
    /// lemmas from a prior non-inlined PDR stage into the portfolio's engines.
    pub(crate) fn set_pdr_lemma_pool(&mut self, pool: &crate::lemma_pool::LemmaPool) {
        if pool.is_empty() {
            return;
        }
        for engine in &mut self.engines {
            if let EngineConfig::Pdr(pdr) = engine {
                pdr.lemma_hints = Some(pool.clone());
            }
        }
    }

    /// Set a budget policy for a specific engine type (#8418).
    ///
    /// Multiple PDR variants in the portfolio share the same policy.
    /// If a policy is set to [`BudgetPolicy::Disabled`], engines of that
    /// type are removed before solving.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ay_chc::{PortfolioConfig, EngineType, BudgetPolicy};
    ///
    /// let config = PortfolioConfig::default()
    ///     .engine_budget(EngineType::Pdr, BudgetPolicy::MinPercent(40))
    ///     .engine_budget(EngineType::Bmc, BudgetPolicy::MinPercent(20))
    ///     .engine_budget(EngineType::Trl, BudgetPolicy::Disabled);
    /// ```
    #[must_use]
    pub fn engine_budget(mut self, engine: EngineType, policy: BudgetPolicy) -> Self {
        self.engine_budgets.insert(engine, policy);
        self
    }

    /// Set multiple engine budget policies at once (#8418).
    #[must_use]
    pub fn engine_budgets(mut self, policies: Vec<(EngineType, BudgetPolicy)>) -> Self {
        for (engine, policy) in policies {
            self.engine_budgets.insert(engine, policy);
        }
        self
    }

    /// Get the budget policy for a specific engine type.
    ///
    /// Returns [`BudgetPolicy::Default`] if no policy was set.
    pub fn budget_policy(&self, engine: EngineType) -> BudgetPolicy {
        self.engine_budgets
            .get(&engine)
            .copied()
            .unwrap_or(BudgetPolicy::Default)
    }

    /// Apply budget policies: remove disabled engines and filter the engine list.
    ///
    /// Called internally before solving. Returns the list of disabled engine
    /// types for verbose logging.
    pub(crate) fn apply_budget_policies(&mut self) -> Vec<EngineType> {
        if self.engine_budgets.is_empty() {
            return Vec::new();
        }

        let disabled: Vec<EngineType> = self
            .engine_budgets
            .iter()
            .filter(|(_, policy)| matches!(policy, BudgetPolicy::Disabled))
            .map(|(engine_type, _)| *engine_type)
            .collect();

        if !disabled.is_empty() {
            self.engines
                .retain(|e| !disabled.contains(&e.engine_type()));
        }

        disabled
    }

    /// Compute a per-engine budget from the policy, given total available time.
    ///
    /// Applies the minimum floor guarantee: no active engine gets less than
    /// `MIN_BUDGET_FLOOR_PERCENT`% of the total timeout.
    ///
    /// Returns `None` if the engine is disabled or the total is zero.
    pub(crate) fn compute_engine_budget(
        &self,
        engine_type: EngineType,
        total: Duration,
        num_active_engines: usize,
    ) -> Option<Duration> {
        if total.is_zero() || num_active_engines == 0 {
            return None;
        }

        let policy = self.budget_policy(engine_type);
        match policy {
            BudgetPolicy::Disabled => None,
            BudgetPolicy::Fixed(dur) => {
                // Clamp to total but respect the floor.
                let floor = total.mul_f64(BudgetPolicy::MIN_BUDGET_FLOOR_PERCENT as f64 / 100.0);
                Some(dur.max(floor).min(total))
            }
            BudgetPolicy::MinPercent(pct) => {
                let pct = pct.clamp(BudgetPolicy::MIN_BUDGET_FLOOR_PERCENT, 100);
                let budget = total.mul_f64(pct as f64 / 100.0);
                Some(budget.min(total))
            }
            BudgetPolicy::Default => {
                // Equal share with minimum floor.
                let equal_share = total / (num_active_engines as u32);
                let floor = total.mul_f64(BudgetPolicy::MIN_BUDGET_FLOOR_PERCENT as f64 / 100.0);
                Some(equal_share.max(floor).min(total))
            }
        }
    }

    /// Reorder the engine list so that engines matching `preferred` appear first.
    ///
    /// Engines listed in `preferred` are moved to the front of the engine list
    /// in the order they appear, followed by all remaining engines in their
    /// original order. This allows callers to hint which engines to try first
    /// based on problem characteristics (e.g., non-recursive -> BMC first).
    ///
    /// Engines not present in the portfolio are silently ignored.
    ///
    /// Part of #8418: engine priority/ordering API.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ay_chc::{PortfolioConfig, EngineType};
    ///
    /// let config = PortfolioConfig::default()
    ///     .preferred_engine_order(vec![EngineType::Bmc, EngineType::Pdr]);
    /// // BMC is now first, followed by PDR variants, then the rest.
    /// ```
    #[must_use]
    pub fn preferred_engine_order(mut self, preferred: Vec<EngineType>) -> Self {
        self.reorder_engines(&preferred);
        self
    }

    /// In-place engine reordering. Moves engines matching `preferred` types
    /// to the front, preserving relative order within each group.
    pub(crate) fn reorder_engines(&mut self, preferred: &[EngineType]) {
        if preferred.is_empty() {
            return;
        }

        // Partition: engines whose type is in `preferred` go first,
        // ordered by position in the preference list.
        let mut priority: Vec<(usize, EngineConfig)> = Vec::new();
        let mut rest: Vec<EngineConfig> = Vec::new();

        for engine in self.engines.drain(..) {
            let et = engine.engine_type();
            if let Some(pos) = preferred.iter().position(|p| *p == et) {
                priority.push((pos, engine));
            } else {
                rest.push(engine);
            }
        }

        // Sort priority engines by their position in the preference list.
        // Stable sort preserves original order for engines with the same type
        // (e.g., two PDR variants both get position 0 if PDR is first).
        priority.sort_by_key(|(pos, _)| *pos);

        self.engines = priority.into_iter().map(|(_, e)| e).chain(rest).collect();
    }

    /// Compute the per-engine term memory budget for this portfolio (#8629).
    ///
    /// When `self.memory_budget` is `Some(bytes)`, divides the budget equally
    /// across `engine_count` engines. Otherwise falls back to the global
    /// `TermStore::per_engine_budget()` (which divides the process-level limit
    /// by engine count).
    ///
    /// This enables per-portfolio memory isolation: multiple concurrent solves
    /// in the same process (e.g., model-checker-consumer) each get their own memory budget,
    /// rather than all sharing the process-wide `DEFAULT_TERM_MEMORY_LIMIT`.
    pub(crate) fn per_engine_term_budget(&self) -> Option<usize> {
        if let Some(total_bytes) = self.memory_budget {
            let engine_count = self.engines.len().max(1);
            Some(total_bytes / engine_count)
        } else {
            // Fall back to global per-engine budget.
            Some(ay_core::TermStore::per_engine_budget())
        }
    }

    /// Cap PDR escalation and remove Kind for DT problems (#7930).
    pub fn apply_dt_guards(&mut self, max_escalation: usize) {
        for engine in &mut self.engines {
            if let EngineConfig::Pdr(pdr) = engine {
                pdr.max_escalation_level = max_escalation;
            }
        }
        self.engines.retain(|e| !matches!(e, EngineConfig::Kind(_)));
    }
}

/// Portfolio result type — alias for the unified ChcEngineResult (#2791).
pub type PortfolioResult = ChcEngineResult;

// From impls for unconverted engines (will be removed as each engine is converted to ChcEngineResult)
// PDR, BMC, TRL already return ChcEngineResult directly.

// From<PdkindResult> removed: PdkindResult is now a type alias for ChcEngineResult,
// so conversion is identity. PDKind conversion logic lives in pdkind.rs convert_raw_result().

impl From<TpaResult> for PortfolioResult {
    fn from(result: TpaResult) -> Self {
        match result {
            TpaResult::Safe {
                invariant,
                power: _,
            } => {
                let mut model = InvariantModel::new();
                if let Some(inv_expr) = invariant {
                    let vars = inv_expr.vars();
                    model.set(
                        crate::PredicateId(0),
                        PredicateInterpretation::new(vars, inv_expr),
                    );
                }
                Self::Safe(model)
            }
            TpaResult::Unsafe { steps, trace: _ } => {
                let step_count = steps.min(100) as usize;
                let cex_steps = (0..=step_count)
                    .map(|_| CounterexampleStep::new(crate::PredicateId(0), FxHashMap::default()))
                    .collect();
                Self::Unsafe(Counterexample {
                    steps: cex_steps,
                    witness: None,
                    ground_derivation: None,
                })
            }
            TpaResult::Unknown => Self::Unknown,
        }
    }
}

impl From<CegarResult> for PortfolioResult {
    fn from(result: CegarResult) -> Self {
        match result {
            CegarResult::Safe(model) => Self::Safe(model),
            CegarResult::Unsafe(cex) => {
                let steps = cex
                    .trace
                    .iter()
                    .map(|(_, state)| {
                        let predicate =
                            state.as_ref().map_or(crate::PredicateId(0), |s| s.relation);
                        CounterexampleStep::new(predicate, FxHashMap::default())
                    })
                    .collect();
                Self::Unsafe(Counterexample {
                    steps,
                    witness: None,
                    ground_derivation: None,
                })
            }
            CegarResult::Unknown => Self::Unknown,
        }
    }
}

/// Internal message for engine results.
/// Engines that have been converted to ChcEngineResult use the Unified variant.
/// Unconverted engines still use their dedicated variants.
#[derive(Debug, Clone)]
pub(super) enum EngineResult {
    /// PDR, BMC, TRL, IMC, Kind, PDKind, Decomposition — return ChcEngineResult
    Unified(ChcEngineResult, &'static str),
    Tpa(TpaResult),
    Cegar(CegarResult),
}

impl EngineResult {
    /// Short summary string for verbose logging.
    pub(super) fn summary(&self) -> &'static str {
        match self {
            Self::Unified(r, _) => match r {
                ChcEngineResult::Safe(_) => "Safe",
                ChcEngineResult::Unsafe(_) => "Unsafe",
                ChcEngineResult::Unknown => "Unknown",
                ChcEngineResult::NotApplicable => "NotApplicable",
            },
            Self::Tpa(r) => match r {
                TpaResult::Safe { .. } => "Safe",
                TpaResult::Unsafe { .. } => "Unsafe",
                TpaResult::Unknown => "Unknown",
            },
            Self::Cegar(r) => match r {
                CegarResult::Safe(_) => "Safe",
                CegarResult::Unsafe(_) => "Unsafe",
                CegarResult::Unknown => "Unknown",
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_engine_stop_reason_hopeless_display() {
        // Item 5a: the budget report renders the new variant.
        assert_eq!(EngineStopReason::Hopeless.to_string(), "hopeless");
    }

    #[test]
    fn test_enable_give_up_on_stuck_sets_pdr_only() {
        // Item 5a: the scheduler helper opts PDR engines in and leaves the
        // flag OFF by default; non-PDR engines are untouched no-ops.
        let mut pdr = EngineConfig::Pdr(PdrConfig::default());
        if let EngineConfig::Pdr(c) = &pdr {
            assert!(!c.give_up_on_stuck, "give_up_on_stuck must default OFF");
        }
        pdr.enable_give_up_on_stuck();
        match &pdr {
            EngineConfig::Pdr(c) => assert!(c.give_up_on_stuck),
            other => panic!("unexpected engine variant: {other:?}"),
        }

        let mut bmc = EngineConfig::Bmc(BmcConfig::default());
        bmc.enable_give_up_on_stuck(); // must be a no-op, not a panic
        assert!(matches!(bmc, EngineConfig::Bmc(_)));
    }

    #[test]
    fn test_apply_dt_guards_caps_pdr_escalation() {
        let mut config = PortfolioConfig::production_default();
        // Production default should have PDR with max_escalation_level=3
        let pdr_count = config
            .engines
            .iter()
            .filter(|e| matches!(e, EngineConfig::Pdr(_)))
            .count();
        assert!(
            pdr_count >= 2,
            "production portfolio should have at least 2 PDR engines"
        );

        config.apply_dt_guards(0);

        for engine in &config.engines {
            if let EngineConfig::Pdr(pdr) = engine {
                assert_eq!(
                    pdr.max_escalation_level, 0,
                    "PDR escalation should be capped to 0"
                );
            }
        }
    }

    #[test]
    fn test_apply_dt_guards_removes_kind() {
        let mut config = PortfolioConfig::production_default();
        let has_kind_before = config
            .engines
            .iter()
            .any(|e| matches!(e, EngineConfig::Kind(_)));
        assert!(has_kind_before, "production portfolio should include Kind");

        config.apply_dt_guards(0);

        let has_kind_after = config
            .engines
            .iter()
            .any(|e| matches!(e, EngineConfig::Kind(_)));
        assert!(
            !has_kind_after,
            "apply_dt_guards should remove Kind engines"
        );
    }

    // ---------------------------------------------------------------------------
    // Budget control API tests (#8418)
    // ---------------------------------------------------------------------------

    #[test]
    fn test_engine_type_name_roundtrip() {
        let types = [
            EngineType::Pdr,
            EngineType::Bmc,
            EngineType::Pdkind,
            EngineType::Tpa,
            EngineType::Trl,
            EngineType::Kind,
            EngineType::Decomposition,
            EngineType::Imc,
            EngineType::Lawi,
            EngineType::Dar,
            EngineType::Cegar,
        ];
        for t in types {
            assert!(!t.name().is_empty(), "engine type name must be non-empty");
            assert_eq!(t.to_string(), t.name(), "Display should match name()");
        }
    }

    #[test]
    fn test_engine_config_engine_type() {
        let configs: Vec<EngineConfig> = vec![
            EngineConfig::Pdr(PdrConfig::default()),
            EngineConfig::Bmc(BmcConfig::default()),
            EngineConfig::Pdkind(PdkindConfig::default()),
            EngineConfig::Tpa(TpaConfig::default()),
            EngineConfig::Trl(TrlConfig::default()),
            EngineConfig::Kind(KindConfig::default()),
            EngineConfig::Decomposition(DecompositionConfig::default()),
            EngineConfig::Imc(ImcConfig::default()),
            EngineConfig::Lawi(LawiConfig::default()),
            EngineConfig::Dar(DarConfig::default()),
            EngineConfig::Cegar(CegarConfig::default()),
        ];
        let expected = [
            EngineType::Pdr,
            EngineType::Bmc,
            EngineType::Pdkind,
            EngineType::Tpa,
            EngineType::Trl,
            EngineType::Kind,
            EngineType::Decomposition,
            EngineType::Imc,
            EngineType::Lawi,
            EngineType::Dar,
            EngineType::Cegar,
        ];
        for (config, expected_type) in configs.iter().zip(expected.iter()) {
            assert_eq!(
                config.engine_type(),
                *expected_type,
                "engine_type() mismatch for {}",
                config.name()
            );
        }
    }

    #[test]
    fn test_budget_policy_default_returns_default() {
        let config = PortfolioConfig::default();
        assert!(
            matches!(config.budget_policy(EngineType::Pdr), BudgetPolicy::Default),
            "unset policy should be Default"
        );
    }

    #[test]
    fn test_budget_policy_builder() {
        let config = PortfolioConfig::default()
            .engine_budget(EngineType::Pdr, BudgetPolicy::MinPercent(40))
            .engine_budget(
                EngineType::Bmc,
                BudgetPolicy::Fixed(Duration::from_secs(10)),
            )
            .engine_budget(EngineType::Trl, BudgetPolicy::Disabled);

        assert!(matches!(
            config.budget_policy(EngineType::Pdr),
            BudgetPolicy::MinPercent(40)
        ));
        assert!(matches!(
            config.budget_policy(EngineType::Bmc),
            BudgetPolicy::Fixed(_)
        ));
        assert!(matches!(
            config.budget_policy(EngineType::Trl),
            BudgetPolicy::Disabled
        ));
        assert!(matches!(
            config.budget_policy(EngineType::Kind),
            BudgetPolicy::Default
        ));
    }

    #[test]
    fn test_apply_budget_policies_removes_disabled() {
        let mut config = PortfolioConfig::production_default()
            .engine_budget(EngineType::Kind, BudgetPolicy::Disabled)
            .engine_budget(EngineType::Trl, BudgetPolicy::Disabled);

        let had_kind = config
            .engines
            .iter()
            .any(|e| matches!(e, EngineConfig::Kind(_)));
        let had_trl = config
            .engines
            .iter()
            .any(|e| matches!(e, EngineConfig::Trl(_)));
        assert!(had_kind, "production portfolio should include Kind");
        assert!(had_trl, "production portfolio should include Trl");

        let disabled = config.apply_budget_policies();
        assert_eq!(disabled.len(), 2);
        assert!(disabled.contains(&EngineType::Kind));
        assert!(disabled.contains(&EngineType::Trl));

        let has_kind = config
            .engines
            .iter()
            .any(|e| matches!(e, EngineConfig::Kind(_)));
        let has_trl = config
            .engines
            .iter()
            .any(|e| matches!(e, EngineConfig::Trl(_)));
        assert!(
            !has_kind,
            "Kind should be removed after apply_budget_policies"
        );
        assert!(
            !has_trl,
            "Trl should be removed after apply_budget_policies"
        );

        // PDR should still be present
        let has_pdr = config
            .engines
            .iter()
            .any(|e| matches!(e, EngineConfig::Pdr(_)));
        assert!(has_pdr, "PDR should remain after disabling Kind and Trl");
    }

    #[test]
    fn test_compute_engine_budget_min_percent() {
        let config =
            PortfolioConfig::default().engine_budget(EngineType::Pdr, BudgetPolicy::MinPercent(40));
        let total = Duration::from_secs(100);

        let budget = config.compute_engine_budget(EngineType::Pdr, total, 10);
        assert!(budget.is_some());
        let budget = budget.unwrap();
        // 40% of 100s = 40s
        assert_eq!(budget, Duration::from_secs(40));
    }

    #[test]
    fn test_compute_engine_budget_min_floor() {
        // Setting MinPercent(1) should be raised to MIN_BUDGET_FLOOR_PERCENT (5%)
        let config =
            PortfolioConfig::default().engine_budget(EngineType::Bmc, BudgetPolicy::MinPercent(1));
        let total = Duration::from_secs(100);

        let budget = config.compute_engine_budget(EngineType::Bmc, total, 10);
        assert!(budget.is_some());
        let budget = budget.unwrap();
        // Floor is 5% of 100s = 5s
        assert_eq!(budget, Duration::from_secs(5));
    }

    #[test]
    fn test_compute_engine_budget_fixed() {
        let config = PortfolioConfig::default().engine_budget(
            EngineType::Tpa,
            BudgetPolicy::Fixed(Duration::from_secs(15)),
        );
        let total = Duration::from_secs(100);

        let budget = config.compute_engine_budget(EngineType::Tpa, total, 10);
        assert!(budget.is_some());
        let budget = budget.unwrap();
        assert_eq!(budget, Duration::from_secs(15));
    }

    #[test]
    fn test_compute_engine_budget_fixed_clamped_to_total() {
        let config = PortfolioConfig::default().engine_budget(
            EngineType::Tpa,
            BudgetPolicy::Fixed(Duration::from_secs(200)),
        );
        let total = Duration::from_secs(100);

        let budget = config.compute_engine_budget(EngineType::Tpa, total, 10);
        assert!(budget.is_some());
        // Fixed(200s) clamped to total(100s)
        assert_eq!(budget.unwrap(), Duration::from_secs(100));
    }

    #[test]
    fn test_compute_engine_budget_fixed_respects_floor() {
        // Fixed(1s) should be raised to floor (5% of 100s = 5s)
        let config = PortfolioConfig::default()
            .engine_budget(EngineType::Tpa, BudgetPolicy::Fixed(Duration::from_secs(1)));
        let total = Duration::from_secs(100);

        let budget = config.compute_engine_budget(EngineType::Tpa, total, 10);
        assert!(budget.is_some());
        assert_eq!(budget.unwrap(), Duration::from_secs(5));
    }

    #[test]
    fn test_compute_engine_budget_disabled_returns_none() {
        let config =
            PortfolioConfig::default().engine_budget(EngineType::Cegar, BudgetPolicy::Disabled);
        let total = Duration::from_secs(100);

        let budget = config.compute_engine_budget(EngineType::Cegar, total, 10);
        assert!(
            budget.is_none(),
            "disabled engine should return None budget"
        );
    }

    #[test]
    fn test_compute_engine_budget_default_equal_share() {
        let config = PortfolioConfig::default();
        let total = Duration::from_secs(100);

        let budget = config.compute_engine_budget(EngineType::Pdr, total, 10);
        assert!(budget.is_some());
        let budget = budget.unwrap();
        // Equal share: 100s / 10 = 10s, but floor is 5s. 10 > 5, so 10s.
        assert_eq!(budget, Duration::from_secs(10));
    }

    #[test]
    fn test_compute_engine_budget_default_floor_kicks_in() {
        let config = PortfolioConfig::default();
        let total = Duration::from_secs(100);

        // With 100 engines, equal share = 1s, but floor = 5s
        let budget = config.compute_engine_budget(EngineType::Pdr, total, 100);
        assert!(budget.is_some());
        assert_eq!(budget.unwrap(), Duration::from_secs(5));
    }

    #[test]
    fn test_budget_report_new() {
        let report = BudgetReport::new();
        assert!(report.entries.is_empty());
        assert_eq!(report.total_elapsed, Duration::ZERO);
    }

    #[test]
    fn test_engine_stop_reason_variants() {
        // Verify all variants exist and are distinct
        let reasons = [
            EngineStopReason::Completed,
            EngineStopReason::Timeout,
            EngineStopReason::Superseded,
            EngineStopReason::Unknown,
            EngineStopReason::Disabled,
            EngineStopReason::NotApplicable,
        ];
        for (i, r1) in reasons.iter().enumerate() {
            for (j, r2) in reasons.iter().enumerate() {
                if i == j {
                    assert_eq!(*r1, *r2);
                } else {
                    assert_ne!(*r1, *r2);
                }
            }
        }
    }

    #[test]
    fn test_engine_budgets_builder_batch() {
        let config = PortfolioConfig::default().engine_budgets(vec![
            (EngineType::Pdr, BudgetPolicy::MinPercent(40)),
            (EngineType::Bmc, BudgetPolicy::MinPercent(20)),
            (EngineType::Trl, BudgetPolicy::Disabled),
        ]);

        assert!(matches!(
            config.budget_policy(EngineType::Pdr),
            BudgetPolicy::MinPercent(40)
        ));
        assert!(matches!(
            config.budget_policy(EngineType::Bmc),
            BudgetPolicy::MinPercent(20)
        ));
        assert!(matches!(
            config.budget_policy(EngineType::Trl),
            BudgetPolicy::Disabled
        ));
    }

    #[test]
    fn test_min_budget_floor_percent_is_five() {
        assert_eq!(BudgetPolicy::MIN_BUDGET_FLOOR_PERCENT, 5);
    }

    // ---------------------------------------------------------------------------
    // Engine priority ordering tests (#8418)
    // ---------------------------------------------------------------------------

    #[test]
    fn test_preferred_engine_order_moves_to_front() {
        let config = PortfolioConfig::production_default()
            .preferred_engine_order(vec![EngineType::Bmc, EngineType::Kind]);

        // BMC should be first, Kind second.
        assert_eq!(
            config.engines[0].engine_type(),
            EngineType::Bmc,
            "BMC should be moved to front"
        );
        // Kind may be second or third depending on original position.
        let kind_pos = config
            .engines
            .iter()
            .position(|e| e.engine_type() == EngineType::Kind)
            .expect("Kind should still be in engine list");
        assert!(kind_pos < 3, "Kind should be near the front");
        // BMC should come before Kind.
        let bmc_pos = config
            .engines
            .iter()
            .position(|e| e.engine_type() == EngineType::Bmc)
            .expect("BMC should be in engine list");
        assert!(bmc_pos < kind_pos, "BMC should come before Kind");
    }

    #[test]
    fn test_preferred_engine_order_preserves_non_preferred() {
        let original = PortfolioConfig::production_default();
        let original_count = original.engines.len();

        let reordered =
            PortfolioConfig::production_default().preferred_engine_order(vec![EngineType::Bmc]);

        assert_eq!(
            reordered.engines.len(),
            original_count,
            "reordering should not add or remove engines"
        );
    }

    #[test]
    fn test_preferred_engine_order_unknown_type_ignored() {
        let original = PortfolioConfig::production_default();
        let original_count = original.engines.len();

        // CEGAR is in the production portfolio, but the list shouldn't break
        // even if we pass something that's already handled.
        let reordered =
            PortfolioConfig::production_default().preferred_engine_order(vec![EngineType::Cegar]);

        assert_eq!(reordered.engines.len(), original_count);
        assert_eq!(
            reordered.engines[0].engine_type(),
            EngineType::Cegar,
            "CEGAR should be first"
        );
    }

    #[test]
    fn test_preferred_engine_order_empty_is_noop() {
        let original = PortfolioConfig::production_default();
        let reordered = PortfolioConfig::production_default().preferred_engine_order(vec![]);

        let original_types: Vec<EngineType> =
            original.engines.iter().map(|e| e.engine_type()).collect();
        let reordered_types: Vec<EngineType> =
            reordered.engines.iter().map(|e| e.engine_type()).collect();

        assert_eq!(
            original_types, reordered_types,
            "empty preferred should be noop"
        );
    }

    #[test]
    fn test_preferred_engine_order_multiple_pdr_variants() {
        // Production portfolio has 2 PDR variants. Preferring PDR should
        // move both to the front.
        let config =
            PortfolioConfig::production_default().preferred_engine_order(vec![EngineType::Pdr]);

        let pdr_count = config
            .engines
            .iter()
            .take(3) // Both PDR variants should be in first 3 positions
            .filter(|e| e.engine_type() == EngineType::Pdr)
            .count();
        assert!(
            pdr_count >= 2,
            "both PDR variants should be near the front, found {} in first 3",
            pdr_count
        );
    }

    // ---------------------------------------------------------------------------
    // BudgetReport structure tests (#8418)
    // ---------------------------------------------------------------------------

    #[test]
    fn test_engine_budget_entry_fields() {
        let entry = EngineBudgetEntry {
            engine: EngineType::Pdr,
            index: 0,
            budget_allocated: Duration::from_secs(10),
            elapsed: Duration::from_secs(3),
            stop_reason: EngineStopReason::Completed,
        };
        assert_eq!(entry.engine, EngineType::Pdr);
        assert_eq!(entry.index, 0);
        assert_eq!(entry.budget_allocated, Duration::from_secs(10));
        assert_eq!(entry.elapsed, Duration::from_secs(3));
        assert_eq!(entry.stop_reason, EngineStopReason::Completed);
    }
}
