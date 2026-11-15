// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The concrete cross-check's time accounting across one verifier run, and
//! what stops a check whatever its budget.

use super::{CheckDomain, Probe};
use crate::cancellation::CancellationToken;
use crate::pdr::solver::PdrTelemetry;
use crate::pdr::PdrSolver;
use crate::smt::SmtValue;
use crate::ChcExpr;
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::time::Instant;
use std::time::Duration;

/// What ends any concrete check early, whatever its budget or allowance: the
/// solver's cancellation tokens (the portfolio's and an embedder's), its
/// solve deadline, and, for a verifier's checks, the thread's SMT deadline and
/// lane cancellation (what `crate::smt::smt_deadline_expired` reads): the
/// conditions of `PdrSolver::is_cancelled` through which a solve is ended from
/// outside or by the clock. The verifiers already reject at the next clause
/// once one holds. A check resolves them once ([`Self::resolve`]) and polls
/// the result before every evaluation; one they stop answers
/// [`ConcreteAnswer::Interrupted`], never a witness, and the verifier rejects
/// the model rather than count the check performed (2026-11-01: abandoned PDR
/// workers sat in this enumeration long after their solve was over). An
/// anchored search under a deadline also keeps to half of what it leaves
/// ([`ConcreteBudget`]), so it never runs into it.
#[derive(Clone, Default)]
pub(in crate::pdr::verification) struct ConcreteStop {
    tokens: Vec<CancellationToken>,
    deadline: Option<Instant>,
    thread: bool,
}

impl ConcreteStop {
    /// A stop that never fires: a check runs to its own end.
    #[cfg(test)]
    pub(in crate::pdr::verification) fn none() -> Self {
        Self::default()
    }

    /// A stop on `tokens` and `deadline` only, without the thread's state.
    #[cfg(test)]
    pub(in crate::pdr::verification) fn new(
        tokens: Vec<CancellationToken>,
        deadline: Option<Instant>,
    ) -> Self {
        Self {
            tokens,
            deadline,
            thread: false,
        }
    }

    /// The stop of `solver`'s verifier runs.
    pub(in crate::pdr::verification) fn of_solver(solver: &PdrSolver) -> Self {
        let tokens = [
            solver.config.cancellation_token.as_ref(),
            solver.config.external_cancellation_token.as_ref(),
        ]
        .into_iter()
        .flatten()
        .cloned()
        .collect();
        Self {
            tokens,
            deadline: solver.solve_deadline,
            thread: true,
        }
    }

    /// This stop as it stands now. For a verifier's stop, the thread's lane
    /// token joins the tokens and its effective SMT deadline (the scoped SMT
    /// deadline and the thread's solve deadline) joins the deadline: exactly
    /// what `smt_deadline_expired` reads. A check resolves its stop once and
    /// polls the result before every evaluation, because nothing a check does
    /// installs or removes a thread's deadline or lane, and a token cancelled
    /// from another thread is seen through the clone (it shares the flags).
    pub(super) fn resolve(&self) -> ResolvedStop {
        let mut tokens = self.tokens.clone();
        let mut deadline = self.deadline;
        if self.thread {
            tokens.extend(crate::smt::deadline::current_lane_token());
            deadline = [deadline, crate::smt::deadline::effective_thread_deadline()]
                .into_iter()
                .flatten()
                .min();
        }
        ResolvedStop { tokens, deadline }
    }
}

/// A [`ConcreteStop`] resolved for one check ([`ConcreteStop::resolve`]): its
/// poll is an atomic load per token, plus one clock read when a deadline is
/// set.
pub(super) struct ResolvedStop {
    tokens: Vec<CancellationToken>,
    deadline: Option<Instant>,
}

impl ResolvedStop {
    /// True once a token is cancelled or the deadline has passed. `now` is the
    /// caller's clock reading, taken when [`Self::needs_clock`].
    pub(super) fn fired(&self, now: Option<Instant>) -> bool {
        self.tokens.iter().any(CancellationToken::is_cancelled)
            || self
                .deadline
                .zip(now)
                .is_some_and(|(deadline, now)| now >= deadline)
    }

    /// True when [`Self::fired`] reads the caller's clock.
    pub(super) fn needs_clock(&self) -> bool {
        self.deadline.is_some()
    }

    /// [`Self::fired`] with its own clock reading.
    fn fired_now(&self) -> bool {
        self.fired(self.needs_clock().then(Instant::now))
    }
}

/// What one concrete check answers.
#[derive(Debug, PartialEq)]
pub(in crate::pdr::verification) enum ConcreteAnswer {
    /// An assignment that makes the query true: the verifier rejects.
    Witness(FxHashMap<String, SmtValue>),
    /// No witness: none of the assignments searched makes the query true, or
    /// an anchored check's allowance ended (or never started) its search,
    /// which is the centred window's answer there. Counted as performed.
    NoWitness,
    /// The [`ConcreteStop`] ended the search: no answer. The verifier rejects,
    /// as it does when the same condition holds between clauses.
    Interrupted,
}

impl ConcreteAnswer {
    /// The witness, if this answer is one.
    #[cfg(test)]
    pub(in crate::pdr::verification) fn witness(self) -> Option<FxHashMap<String, SmtValue>> {
        match self {
            Self::Witness(model) => Some(model),
            Self::NoWitness | Self::Interrupted => None,
        }
    }
}

/// One verifier run's time accounting for the concrete cross-check (#5653).
///
/// `limit` and `elapsed` are the budget the check has always had: a verifier
/// starts a check only while [`Self::has_room`], and every check on a domain
/// the centred window could already search is charged to `elapsed`, as
/// before. So is an anchored domain's construction (an Int range wholly beyond
/// ±100, which the centred window emptied, so the check built its ranges,
/// found the empty one and answered `None`). The search of an anchored domain
/// draws on an allowance of its own, also `limit` but never more than half of
/// what the stop's deadline leaves ([`Self::anchored_allowance`]), and stops
/// evaluating when that allowance is spent. It never moves `elapsed`, so every check that ran
/// before the anchored window existed still runs, under the same accounting.
/// A search the allowance cut short or never started answers `NoWitness`, the
/// answer the centred window gave there, so the verifiers count it as
/// performed, as they always did (2026-11-01, hostile review of 90b40b3908).
///
/// The anchored searches' time is also handed to the verifier
/// ([`Self::take_anchored_spent`]), which moves its own wall-clock budget
/// forward by it: the work before the anchored window existed keeps the wall
/// time it had. Every check also stops at the [`ConcreteStop`].
pub(in crate::pdr::verification) struct ConcreteBudget {
    limit: Duration,
    elapsed: Duration,
    anchored_elapsed: Duration,
    anchored_taken: Duration,
    stop: ConcreteStop,
    #[cfg(test)]
    evaluations: u64,
}

impl ConcreteBudget {
    pub(in crate::pdr::verification) fn new(limit: Duration, stop: ConcreteStop) -> Self {
        Self {
            limit,
            elapsed: Duration::ZERO,
            anchored_elapsed: Duration::ZERO,
            anchored_taken: Duration::ZERO,
            stop,
            #[cfg(test)]
            evaluations: 0,
        }
    }

    /// True while the check's own budget lasts: the verifier may start a
    /// check. Anchored searches never spend it.
    pub(in crate::pdr::verification) fn has_room(&self) -> bool {
        self.elapsed < self.limit
    }

    /// The time charged to the check's own budget so far.
    pub(in crate::pdr::verification) fn elapsed(&self) -> Duration {
        self.elapsed
    }

    /// The time anchored searches have spent of their allowance so far.
    #[cfg(test)]
    pub(in crate::pdr::verification) fn anchored_elapsed(&self) -> Duration {
        self.anchored_elapsed
    }

    /// The query evaluations every check of this run has performed.
    #[cfg(test)]
    pub(in crate::pdr::verification) fn evaluations(&self) -> u64 {
        self.evaluations
    }

    /// The anchored searches' time since the last call, also added to
    /// `telemetry` (`PdrTelemetry::concrete_anchored_search`, which the model
    /// verification cascade reads). The verifier moves its wall-clock budget
    /// (its start, or its deadline) forward by it after each clause, so the
    /// clauses after an anchored search meet the budget they met before the
    /// anchored window existed. The solve deadline still counts the time, and
    /// stops the search.
    pub(in crate::pdr::verification) fn take_anchored_spent(
        &mut self,
        telemetry: &mut PdrTelemetry,
    ) -> Duration {
        let spent = self.anchored_elapsed.saturating_sub(self.anchored_taken);
        self.anchored_taken = self.anchored_elapsed;
        telemetry.add_anchored_search(spent);
        spent
    }

    /// `transition_check` on `body` and `query`, charged as the type
    /// describes and stopped by the [`ConcreteStop`].
    pub(in crate::pdr::verification) fn check(
        &mut self,
        body: &ChcExpr,
        query: &ChcExpr,
    ) -> ConcreteAnswer {
        let stop = self.stop.resolve();
        if stop.fired_now() {
            return ConcreteAnswer::Interrupted;
        }
        let start = Instant::now();
        let domain = CheckDomain::new(body, query);
        let (domain, allowance_deadline) = match domain {
            Some(domain) if domain.anchored => {
                self.elapsed += start.elapsed();
                let search_start = Instant::now();
                let allowance = self.anchored_allowance(stop.deadline, search_start);
                if allowance.is_zero() {
                    return ConcreteAnswer::NoWitness;
                }
                // `Instant + Duration` overflows only past the clock's range; a
                // search with no representable deadline evaluates nothing.
                let deadline = search_start.checked_add(allowance).unwrap_or(search_start);
                (domain, Some((search_start, deadline)))
            }
            Some(domain) => (domain, None),
            None => {
                self.elapsed += start.elapsed();
                return ConcreteAnswer::NoWitness;
            }
        };
        let mut probe = Probe::new(query, allowance_deadline.map(|(_, d)| d), stop);
        let found = domain.search(&mut probe);
        match allowance_deadline {
            Some((search_start, _)) => self.anchored_elapsed += search_start.elapsed(),
            None => self.elapsed += start.elapsed(),
        }
        #[cfg(test)]
        {
            self.evaluations = self.evaluations.saturating_add(probe.evaluated());
        }
        match found {
            Some(model) => ConcreteAnswer::Witness(model),
            None if probe.interrupted() => ConcreteAnswer::Interrupted,
            None => ConcreteAnswer::NoWitness,
        }
    }

    /// The allowance of an anchored search starting at `now`: what is left of
    /// `limit`, and, when the stop has a `deadline`, at most half of the time
    /// to it less the anchored time this run has already spent. So a search
    /// ends (up to one evaluation) with at least as much time left before the
    /// deadline as all of the run's anchored searches have taken, and never
    /// runs into the deadline itself: the clauses after it keep time to
    /// finish, and the search answers `NoWitness`, the centred window's answer,
    /// rather than `Interrupted` (review of b645a840fe, finding A: under a
    /// solve deadline 300 ms away the search spent all of it, and the verifier
    /// rejected a model b35c9df116 accepted in 7 ms). A deadline already
    /// passed never gets here: the stop answers first.
    fn anchored_allowance(&self, deadline: Option<Instant>, now: Instant) -> Duration {
        let allowance = self.limit.saturating_sub(self.anchored_elapsed);
        match deadline {
            Some(deadline) => allowance.min(
                deadline
                    .saturating_duration_since(now)
                    .saturating_sub(self.anchored_elapsed)
                    / 2,
            ),
            None => allowance,
        }
    }
}

impl PdrSolver {
    /// A concrete-check budget of `limit` for one of this solver's verifier
    /// runs, whose checks stop when the solve does
    /// ([`ConcreteStop::of_solver`]).
    pub(in crate::pdr::verification) fn concrete_budget(&self, limit: Duration) -> ConcreteBudget {
        ConcreteBudget::new(limit, ConcreteStop::of_solver(self))
    }
}
