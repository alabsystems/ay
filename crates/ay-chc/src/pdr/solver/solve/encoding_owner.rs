// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Normal PDR search observes its original cancellation at inner SMT polls.

use super::{PdrResult, PdrSolver};
use crate::bmc::memory::Budget;
use crate::smt::deadline::{
    effective_thread_deadline, try_lane_cancellation, ScopedLaneCancellation, ScopedSmtDeadline,
};
use crate::smt::resource_observation::ScopedResourceObservation;
use crate::CancellationToken;
use ay_core::resource::{current_check_stop, enter_check_stop, CheckStop, CheckStopScope};
use ay_core::time::Instant;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc, OnceLock,
};

struct Control {
    deadline: Option<Instant>,
    token: Option<CancellationToken>,
    raw: Option<Arc<AtomicBool>>,
    original: Option<CheckStop>,
    group: Option<ay_sys::MemoryGroupObservation>,
    terms: Budget,
    encoding: OnceLock<ay_bv::BvEncodingGuard>,
    stopped: AtomicBool,
    calling: AtomicBool,
}

impl Control {
    fn capture(solver: &PdrSolver) -> Result<Arc<Self>, ()> {
        let (ambient, raw) = try_lane_cancellation()?;
        let original = current_check_stop().map_err(|_| ())?;
        let group = ay_sys::try_current_memory_group_observation().map_err(|_| ())?;
        let mut token = solver
            .config
            .effective_cancellation_token()
            .map(|t| t.child());
        if let Some(ambient) = ambient {
            if let Some(token) = token.as_mut() {
                token.link_upstream(&ambient);
            } else {
                token = Some(ambient.child());
            }
        }
        let token = token.map(|t| t.sticky_child());
        let requested = match (solver.solve_deadline, solver.config.solve_timeout) {
            (Some(end), _) => Some(end),
            (None, Some(duration)) => Some(Instant::now().checked_add(duration).ok_or(())?),
            (None, None) => None,
        };
        Ok(Arc::new(Self {
            deadline: [
                requested,
                solver.smt.current_global_deadline(),
                effective_thread_deadline(),
            ]
            .into_iter()
            .flatten()
            .min(),
            token,
            raw,
            original,
            group,
            encoding: OnceLock::new(),
            terms: Budget::capture(solver.config.memory_budget(), solver.smt.term_memory_budget),
            stopped: AtomicBool::new(false),
            calling: AtomicBool::new(false),
        }))
    }

    fn open(&self) -> bool {
        if self.stopped.load(Ordering::Relaxed) {
            return false;
        }
        if self.calling.swap(true, Ordering::Relaxed) {
            self.stopped.store(true, Ordering::Relaxed);
            return false;
        }
        let closed = self
            .encoding
            .get()
            .is_some_and(ay_bv::BvEncodingGuard::was_stopped)
            || self.deadline.is_some_and(|d| Instant::now() >= d)
            || self
                .token
                .as_ref()
                .is_some_and(CancellationToken::is_cancelled)
            || self
                .raw
                .as_ref()
                .is_some_and(|flag| flag.load(Ordering::Relaxed))
            || self.original.as_ref().is_some_and(|stop| stop())
            || self.group.as_ref().is_some_and(|group| group.is_tripped())
            || ay_core::resource::process_cancelled()
            || ay_sys::process_memory_exceeded()
            || !self.terms.open()
            || self.deadline.is_some_and(|d| Instant::now() >= d);
        if closed {
            self.stopped.store(true, Ordering::Relaxed);
        }
        self.calling.store(false, Ordering::Relaxed);
        !self.stopped.load(Ordering::Relaxed)
    }
}

pub(super) struct Scope {
    check: CheckStopScope,
    deadline: Option<ScopedSmtDeadline>,
    lane: Option<ScopedLaneCancellation>,
    observation: ScopedResourceObservation,
    encoding: ay_bv::ScopedBvEncodingOwner,
    owner: Arc<Control>,
}

impl Scope {
    pub(super) fn enter(solver: &mut PdrSolver) -> Option<Self> {
        solver.establish_original_solve_deadline()?;
        let owner = Control::capture(solver).ok()?;
        let observation = ScopedResourceObservation::install();
        if observation.first().is_some() || !owner.open() {
            return None;
        }
        let lane = owner
            .token
            .as_ref()
            .map(|token| ScopedLaneCancellation::install(token.clone(), owner.raw.clone()));
        let deadline = owner.deadline.map(ScopedSmtDeadline::install_until);
        // The root guard captures this callback; a weak edge avoids an Arc cycle.
        let poll = Arc::downgrade(&owner);
        let check = enter_check_stop(Arc::new(move || {
            poll.upgrade().is_none_or(|poll| !poll.open())
        }));
        let encoding = ay_bv::ScopedBvEncodingOwner::enter(&solver.smt.terms)?;
        if owner.encoding.set(encoding.guard()).is_err() {
            return None;
        }
        Some(Self {
            check,
            deadline,
            lane,
            observation,
            encoding,
            owner,
        })
    }

    pub(super) fn finish(self, result: PdrResult) -> PdrResult {
        let Self {
            check,
            deadline,
            lane,
            observation,
            encoding,
            owner,
        } = self;
        // Fold an exact inner refusal before restoring thread-local observers.
        if observation.first().is_some() || !owner.open() {
            owner.stopped.store(true, Ordering::Relaxed);
        }
        drop(encoding);
        drop(check);
        drop(deadline);
        drop(lane);
        drop(observation);
        // Retained original handles apply after temporary TLS cleanup.
        if owner.open() {
            result
        } else {
            PdrResult::Unknown
        }
    }
}

#[cfg(test)]
mod tests;

impl PdrSolver {
    /// Establish the original absolute end once, before any encoding starts.
    ///
    /// Startup reuses this end rather than renewing a relative allowance.
    pub(super) fn establish_original_solve_deadline(&mut self) -> Option<ay_core::time::Instant> {
        // Set the solve deadline. A caller-supplied timeout takes precedence;
        // otherwise a generous DEFAULT SAFETY deadline is ALWAYS installed. This
        // is load-bearing: panic-freedom (and other proof-seeking) obligations
        // run WITHOUT a timeout — they want a proof, not Unknown — so without a
        // default the wall-clock deadline is never set, the propagate-level
        // deadline poll (TheoryExtension::propagate_impl) can never fire, and a
        // divergent conflict-free/decision-free level-0 theory-propagation churn
        // spins at 100% CPU forever, hanging the whole verification gate. With
        // the default, such a solve terminates fail-closed to Unknown (never a
        // fabricated Sat/Unsat) after DEFAULT_SAFETY_DEADLINE, which is set far
        // above any legitimate proof time so it only ever kills a true spin.
        const DEFAULT_SAFETY_DEADLINE: std::time::Duration = std::time::Duration::from_mins(5);
        let config_deadline = match self.solve_deadline {
            Some(end) => end,
            None => ay_core::time::Instant::now()
                .checked_add(self.config.solve_timeout.unwrap_or(DEFAULT_SAFETY_DEADLINE))?,
        };
        // Honor any TIGHTER ambient absolute deadline the embedding lane already
        // installed for this obligation, taking the MINIMUM (fail-closed — this
        // only ever SHORTENS the deadline). Two sources are consulted:
        //   * `current_thread_solve_deadline()` — a thread-scoped deadline the
        //     embedder installs ONCE at obligation entry (`ScopedSolveDeadline`).
        //     Because it is ABSOLUTE and thread-wide, every INNER `PdrSolver::solve`
        //     the engine spawns for this obligation (portfolio/validation/probe
        //     sub-solves) inherits the SAME wall-clock ceiling instead of being
        //     re-granted a fresh full budget each time it re-enters `solve_init`
        //     (the per-round fresh-budget regression class, cf. 88c66631).
        //   * `self.smt.current_global_deadline()` — a deadline already pushed
        //     onto THIS `SmtContext` by an enclosing solve; without the min the
        //     line below (`set_global_solve_deadline`) would CLOBBER a tighter
        //     enclosing deadline with our looser (up to 300s default) one.
        // A caller that wants the full default simply installs neither.
        self.solve_deadline = [
            Some(config_deadline),
            crate::smt::current_thread_solve_deadline(),
            self.smt.current_global_deadline(),
            crate::smt::deadline::effective_thread_deadline(),
        ]
        .into_iter()
        .flatten()
        .min();
        // Plumb the absolute solve deadline down to the SMT context so EVERY
        // check_sat (startup discovery, portfolio engines, proof validation —
        // not just the main blocking loop) honors it, even when invoked without
        // a per-query timeout. Without this a single unbounded query on an
        // integer-modulo CHC could spin for minutes/hours past solve_timeout.
        self.smt.set_global_solve_deadline(self.solve_deadline);

        self.solve_deadline
    }
}
