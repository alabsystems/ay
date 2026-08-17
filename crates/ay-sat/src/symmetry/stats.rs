// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Minimal symmetry-preprocessing statistics.

/// Reason the symmetry pass did not emit any symmetry-breaking clauses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SymmetrySkipReason {
    Disabled,
    Incremental,
    ProofMode,
    TooLarge,
    NoActiveClauses,
    NoPairs,
    /// A route RAN its search and found nothing. Distinct from every reason
    /// above, all of which mean the route never executed.
    ///
    /// Without this the two are indistinguishable in `--stats`, which is how
    /// `--sat-signed-symmetry` stayed inert long enough for a full-400 A/B to
    /// "reject" a technique that was never running. A detector that reports
    /// nothing must say whether it looked.
    NoGenerators,
}

/// Root symmetry-preprocessing telemetry.
#[derive(Debug, Clone, Default)]
pub(crate) struct SymmetryStats {
    /// One entry per route ATTEMPTED, in order: `(route, outcome)`.
    ///
    /// `last_skipped_reason` is a single slot overwritten by whichever route
    /// runs last, so on a run that tries several routes it reports the last
    /// one's outcome as the run's. That made every route's reachability
    /// unverifiable — see the development design notes. A subsystem that tries N
    /// strategies must report N outcomes.
    pub(crate) routes: Vec<(&'static str, String)>,
    pub(crate) runs: u64,
    pub(crate) candidate_pairs: u64,
    pub(crate) pairs_detected: u64,
    pub(crate) sb_clauses_added: u64,
    /// Refined colour classes with >= 2 variables.
    pub(crate) groups_nontrivial: u64,
    /// Classes dropped for exceeding the detector's group-size budget.
    pub(crate) groups_over_budget: u64,
    /// Largest refined colour class.
    pub(crate) largest_group: u64,
    pub(crate) last_skipped_reason: Option<SymmetrySkipReason>,
}

/// Public snapshot of root symmetry preprocessing, for `--stats` consumers.
///
/// Symmetry breaking is the single largest technique gap on the SAT-COMP 2026
/// Main set (satsuma+Kissat solved 276/400 vs 238 for plain Kissat), so whether
/// the pass ran — and if not, why it bailed — has to be visible from the CLI
/// rather than only from an in-crate debugger.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SymmetryReport {
    /// One entry per route attempted: `(route, outcome)`. Append-only.
    pub routes: Vec<(&'static str, String)>,
    /// Times the root pass was entered.
    pub runs: u64,
    /// Candidate variable pairs the refinement proposed.
    pub candidate_pairs: u64,
    /// Candidate pairs that survived the formula-preserving gate.
    pub pairs_detected: u64,
    /// Symmetry-breaking clauses actually added.
    pub sb_clauses_added: u64,
    /// Refined colour classes with >= 2 variables — how much symmetry the
    /// refinement actually saw.
    pub groups_nontrivial: u64,
    /// Non-trivial classes discarded for exceeding the group-size budget.
    pub groups_over_budget: u64,
    /// Largest refined colour class.
    pub largest_group: u64,
    /// Stable tag for why the last run emitted nothing, or `None` when it did
    /// reach clause emission.
    pub skipped: Option<&'static str>,
}

impl SymmetrySkipReason {
    /// Stable, machine-greppable tag for this skip reason.
    pub(crate) fn tag(self) -> &'static str {
        match self {
            Self::Disabled => "disabled",
            Self::Incremental => "incremental",
            Self::ProofMode => "proof-mode",
            Self::TooLarge => "too-large",
            Self::NoActiveClauses => "no-active-clauses",
            Self::NoPairs => "no-pairs",
            Self::NoGenerators => "ran-found-none",
        }
    }
}

impl SymmetryStats {
    pub(crate) fn report(&self) -> SymmetryReport {
        SymmetryReport {
            runs: self.runs,
            candidate_pairs: self.candidate_pairs,
            pairs_detected: self.pairs_detected,
            sb_clauses_added: self.sb_clauses_added,
            groups_nontrivial: self.groups_nontrivial,
            groups_over_budget: self.groups_over_budget,
            largest_group: self.largest_group,
            skipped: self.last_skipped_reason.map(SymmetrySkipReason::tag),
            routes: self.routes.clone(),
        }
    }

    pub(crate) fn begin_run(&mut self) {
        self.runs = self.runs.saturating_add(1);
        self.last_skipped_reason = None;
    }

    pub(crate) fn skip(&mut self, reason: SymmetrySkipReason) {
        self.last_skipped_reason = Some(reason);
    }

    /// Record that `route` was attempted, with what came of it. Append-only, so
    /// a later route cannot erase an earlier one's result.
    pub(crate) fn record_route(&mut self, route: &'static str, outcome: impl Into<String>) {
        self.routes.push((route, outcome.into()));
    }
}
