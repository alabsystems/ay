// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! What an engine is configured with ([`EngineConfig`], KC2, KC25) and what
//! bounds one check ([`Guard`], design R1).

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, OnceLock};
use std::time::Instant;

use ay_core::resource::{self, ResourceGuard};
use ay_sat::Solver;

/// The SAT search schedule of the one search (KC25).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SearchProfile {
    /// ay-sat's own default: mode-switching restarts, ay-sat's phase and
    /// decision heuristics. The kernel's profile.
    SatDefault,
    /// The QF_LRA lane's MiniSat-era schedule (#8093): geometric restarts
    /// (100, ×1.5) and a random decision every hundredth time. Used only to
    /// compare the kernel with the lanes (`--engine=shadow`), so that the
    /// comparison measures the kernel rather than a different SAT schedule.
    LaneParity,
}

impl SearchProfile {
    /// Configure `solver` for this profile (before the search starts).
    pub(crate) fn apply(self, solver: &mut Solver) {
        match self {
            Self::SatDefault => {}
            Self::LaneParity => {
                solver.set_geometric_restarts(100.0, 1.5);
                solver.set_random_var_freq(0.01);
            }
        }
    }
}

/// How an [`crate::Engine`] decides (KC2: the configuration is the engine's;
/// the term store and the guard are lent per check).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EngineConfig {
    /// Record the refutation while the search runs (design D3): a hint for
    /// every clause the kernel adds, the encoding's clausification rules and
    /// ay-sat's clause trace. A check under assumptions does not record.
    pub record_proofs: bool,
    /// Theory-aware branching (design §3.8): off until measured on the
    /// engine; the lanes use it and needed a wander latch to undo it.
    pub theory_branching: bool,
    /// Let the arithmetic plug-in run its difference-logic sub-module when
    /// every arithmetic atom of the check is a difference atom; `false` keeps
    /// the simplex for every check (measurement and tests).
    pub difference_logic: bool,
    /// Let the integer simplex derive implied bounds during BCP-time checks
    /// (see [`crate::LraPlugin::set_bcp_implied_bounds`]).
    pub integer_bcp_implied_bounds: bool,
    /// The SAT search schedule (KC25).
    pub search: SearchProfile,
    /// Let the hub hand only the propagations of relevant nodes to the
    /// search (KC21). Irrelevant ones are still checked: every assigned
    /// literal reaches the hub, and a clash is a conflict.
    pub hub_relevancy: bool,
}

/// Which terms the hub gives a node (KC24), fixed per check by the
/// registry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnodeMode {
    /// Nodes only where the hub needs them (design H1): uninterpreted
    /// applications, their arguments, and the equalities whose sides matter.
    /// The mode of every check without a quantifier plug-in.
    Sparse,
    /// Every ground subterm of a relevant assertion or instance, created
    /// lazily (KC23): what E-matching needs. Reserved for the quantifier
    /// plug-in; the hub refuses it until that plug-in exists.
    Full,
}

impl EnodeMode {
    /// The mode for a check: `Full` exactly when a quantifier plug-in is
    /// registered (none exists yet).
    #[must_use]
    pub const fn for_check(quantifiers: bool) -> Self {
        if quantifiers {
            Self::Full
        } else {
            Self::Sparse
        }
    }
}

impl Default for EngineConfig {
    /// The kernel's configuration: ay-sat's default search, difference logic
    /// on, no recording.
    fn default() -> Self {
        Self {
            record_proofs: false,
            theory_branching: false,
            difference_logic: true,
            integer_bcp_implied_bounds: false,
            search: SearchProfile::SatDefault,
            hub_relevancy: false,
        }
    }
}

impl EngineConfig {
    /// The named lane-parity configuration (KC25): the default with the
    /// QF_LRA lane's search schedule. For comparisons with the lanes only.
    #[must_use]
    pub fn lane_parity() -> Self {
        Self {
            search: SearchProfile::LaneParity,
            ..Self::default()
        }
    }
}

/// Why a [`Guard`] says stop.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Exhausted {
    /// The deadline passed.
    Deadline,
    /// The cancel flag was raised, or the caller's stop predicate answered
    /// true.
    Interrupted,
    /// The resource guard's rlimit budget of ticks was spent.
    Rlimit,
    /// The process passed its memory budget.
    Memory,
}

impl Exhausted {
    /// The `:reason-unknown` spelling.
    #[must_use]
    pub const fn reason(self) -> &'static str {
        match self {
            Self::Deadline => "timeout",
            Self::Interrupted => "interrupted",
            Self::Rlimit => "resourceout",
            Self::Memory => "memout",
        }
    }
}

/// A caller's live stop question for one check. Clones share its first
/// observed stop; clearing a flag or changing a deadline cannot revive that
/// check. A later caller-owned check must create its control view explicitly,
/// retaining any cumulative ResourceGuard it is required to share.
type StopPredicate = Arc<dyn Fn() -> bool + Send + Sync>;

/// The resources of one check (design R1): a deadline, a cancel flag, a
/// caller's stop predicate (the executor's live solve deadline) and the
/// check's [`ResourceGuard`] (its rlimit, the process-wide cancel and the
/// process memory budget). Lent to [`crate::Engine::check`]; the engine keeps
/// none of it.
///
/// KC6 replaces this with a child of the worker's `GuardTree` (ticks, CPU,
/// memory share, cancel chain); until then the kernel polls exactly these.
#[derive(Clone, Default)]
pub struct Guard {
    deadline: Option<Instant>,
    cancel: Option<Arc<AtomicBool>>,
    stop: Option<StopPredicate>,
    resource: ResourceGuard,
    /// First observed stop for this caller-owned check. Guard clones share
    /// this reason; clearing a live flag cannot renew an ended callback.
    refusal: Arc<OnceLock<Exhausted>>,
}

impl std::fmt::Debug for Guard {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Guard")
            .field("deadline", &self.deadline)
            .field("cancel", &self.cancel)
            .field("stop", &self.stop.is_some())
            .field("resource", &self.resource)
            .finish()
    }
}

impl Guard {
    /// A guard that says stop only when the run itself must end: the
    /// process-wide cancel (the CLI's deadline, memory or SIGTERM watchdog)
    /// or the process memory budget ([`ResourceGuard::new`]).
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Stop once this instant passes (`None`: no deadline).
    #[must_use]
    pub fn with_deadline(mut self, deadline: Option<Instant>) -> Self {
        self.deadline = deadline;
        self
    }

    /// Stop once this flag is raised.
    #[must_use]
    pub fn with_cancel(mut self, cancel: Arc<AtomicBool>) -> Self {
        self.cancel = Some(cancel);
        self
    }

    /// Stop once `stop` answers true.
    #[must_use]
    pub fn with_stop(mut self, stop: impl Fn() -> bool + Send + Sync + 'static) -> Self {
        self.stop = Some(Arc::new(stop));
        self
    }

    /// Stop once this resource owner says so (its deadline, cancel flag
    /// and rlimit, besides the process-wide cancel and memory budget).
    #[must_use]
    pub fn with_resource(mut self, resource: ResourceGuard) -> Self {
        self.resource = resource;
        self
    }

    /// The deadline, if any.
    #[must_use]
    pub const fn deadline(&self) -> Option<Instant> {
        self.deadline
    }

    /// Debit the same caller's resource owner. Statistics never debit it again.
    /// Caller-level deadline/stop polling remains the context's periodic job.
    pub(crate) fn charge_ticks(&self, cost: u64) -> Result<(), Exhausted> {
        // Offer every charge to the original owner, even after this adapter
        // has observed an external stop. Its own sticky semantics decide what
        // is counted/refused; do not create a replacement owner or refund.
        let charged = self.resource.tick(cost).map_err(resource_stop);
        if let Some(&why) = self.refusal.get() {
            return Err(why);
        }
        charged.map_err(|why| self.latch(why))
    }

    fn latch(&self, why: Exhausted) -> Exhausted {
        *self.refusal.get_or_init(|| why)
    }

    /// Why the check must stop now. Preserve deadline/cancel/resource ordering
    /// on its first observation; later polls keep that exact typed reason.
    #[must_use]
    pub fn exhausted(&self) -> Option<Exhausted> {
        if let Some(&why) = self.refusal.get() {
            return Some(why);
        }
        if self.deadline.is_some_and(|d| Instant::now() >= d) {
            return Some(self.latch(Exhausted::Deadline));
        }
        let cancelled = self
            .cancel
            .as_ref()
            .is_some_and(|flag| flag.load(Ordering::Relaxed));
        if cancelled || self.stop.as_ref().is_some_and(|stop| stop()) {
            return Some(self.latch(Exhausted::Interrupted));
        }
        self.resource
            .exhausted()
            .map(resource_stop)
            .map(|why| self.latch(why))
    }

    /// The search's stop question.
    #[must_use]
    pub fn should_stop(&self) -> bool {
        self.exhausted().is_some()
    }
}

/// Retain the exact existing resource-stop mapping, including CPU slices.
fn resource_stop(why: resource::Exhausted) -> Exhausted {
    match why {
        resource::Exhausted::Cancelled => Exhausted::Interrupted,
        resource::Exhausted::Deadline | resource::Exhausted::Cpu => Exhausted::Deadline,
        resource::Exhausted::Rlimit => Exhausted::Rlimit,
        resource::Exhausted::Memory => Exhausted::Memory,
    }
}

#[cfg(test)]
#[test]
fn kernel_plugin_tick_resource_reason_mapping_is_unchanged() {
    assert_eq!(
        resource_stop(resource::Exhausted::Cancelled),
        Exhausted::Interrupted
    );
    assert_eq!(
        resource_stop(resource::Exhausted::Deadline),
        Exhausted::Deadline
    );
    assert_eq!(resource_stop(resource::Exhausted::Cpu), Exhausted::Deadline);
    assert_eq!(
        resource_stop(resource::Exhausted::Rlimit),
        Exhausted::Rlimit
    );
    assert_eq!(
        resource_stop(resource::Exhausted::Memory),
        Exhausted::Memory
    );
}
