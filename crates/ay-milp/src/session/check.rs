// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ordered orchestration for one [`BabSession`] check.
//!
//! Route modules may either decline or return a fully finalized verdict.  The
//! orchestrator alone advances between route families and drains replay
//! evidence on an early exit.  This keeps route order, the shared deadline,
//! and the deferred-claim join visible in one small function.

use std::num::NonZeroUsize;
#[cfg(test)]
use std::time::Duration;
use std::time::Instant;

use super::*;

mod certified;
mod native;
mod proof_prelude;
mod replay;

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct AttemptObservation {
    deadline: Option<Instant>,
    time_limit: Option<Duration>,
}

#[cfg(test)]
std::thread_local! {
    static TEST_ATTEMPTS: std::cell::RefCell<Vec<AttemptObservation>> = const {
        std::cell::RefCell::new(Vec::new())
    };
    static TEST_PANIC_AFTER_DEADLINE: std::cell::Cell<bool> = const {
        std::cell::Cell::new(false)
    };
}

/// Caller-owned inputs that must survive until the native anchor.
pub(super) struct CheckRequest<'prefix, 'margin, 'target> {
    pub(super) shared_binary_prefix: &'prefix [Col],
    pub(super) proof_first_workers: Option<NonZeroUsize>,
    pub(super) margin_mode: MarginMode<'margin>,
    pub(super) target_fsb_prefix: Option<crate::bab::TargetFsbPrefixRequest<'target>>,
}

/// Caller configuration saved while one check pins an absolute deadline.
///
/// `SolveOpts::time_limit` remains visible during the attempt because bounded
/// post-verdict certificate enrichment is a fraction of that configured
/// duration. The pinned absolute deadline still wins every later
/// `effective_deadline` call, and restoring this latch-bearing snapshot gives a
/// subsequent check a fresh deadline even after an unwind.
pub(super) struct AttemptOptions {
    caller: SolveOpts,
}

impl AttemptOptions {
    pub(super) fn preserve(session: &BabSession) -> Self {
        Self {
            caller: session.opts.clone(),
        }
    }

    /// Pin the search horizon before any objective snapshot, tuning, or route
    /// work, while retaining the configured duration for certificate budgets.
    pub(super) fn begin(&self, session: &mut BabSession, started: Instant) {
        session.opts.deadline = self.caller.effective_deadline(started);
        let _ = crate::cert_io::ledger::take();
        session.invalidate_last_evidence();
        #[cfg(test)]
        TEST_ATTEMPTS.with(|attempts| {
            attempts.borrow_mut().push(AttemptObservation {
                deadline: session.opts.deadline,
                time_limit: session.opts.time_limit,
            });
        });
        #[cfg(test)]
        TEST_PANIC_AFTER_DEADLINE.with(|panic_next| {
            assert!(
                !panic_next.replace(false),
                "injected panic after attempt deadline materialization"
            );
        });
    }

    pub(super) fn restore(self, session: &mut BabSession) {
        session.opts = self.caller;
    }
}

/// Mutable facts shared by ordered route phases.
///
/// The exact objective is owned here for the entire check. Deferrable routes
/// clone it into their temporary finalizer; terminal routes and the anchor take
/// it exactly once.
struct CheckState {
    objective: Vec<(u32, f64)>,
    exact_objective: Option<ExactObjective>,
    has_objective: bool,
    ordinary_native_check: bool,
    pending_sat_relu_fallback: Option<crate::sat_relu::SatReluPlan>,
}

impl CheckState {
    fn begin(session: &BabSession, request: &CheckRequest<'_, '_, '_>) -> Self {
        let objective: Vec<(u32, f64)> = (0..session.model.num_cols())
            .map(|index| (index as u32, session.model.obj_coeff(Col(index as u32))))
            .filter(|&(_, coefficient)| coefficient != 0.0)
            .collect();
        let ordinary_native_check = matches!(&session.lane, MilpLane::Native)
            && request.shared_binary_prefix.is_empty()
            && request.proof_first_workers.is_none()
            && request.target_fsb_prefix.is_none()
            && matches!(&request.margin_mode, MarginMode::Auto)
            && session.model.margin_row().is_none()
            && session.opts.structure_routing;

        Self {
            objective,
            exact_objective: authoritative_exact_objective(&session.model),
            has_objective: session.model.has_objective(),
            ordinary_native_check,
            pending_sat_relu_fallback: None,
        }
    }

    /// Borrow the sparse objective and clone exact ownership for a route that
    /// may defer and therefore must leave the anchor's copy intact.
    fn solved_for_deferral<'a>(&'a self, session: &BabSession) -> SolvedObjective<'a> {
        SolvedObjective {
            coeffs: &self.objective,
            sense: session.model.sense(),
            offset: session.model.objective_offset(),
            exact: self.exact_objective.clone(),
        }
    }

    /// Transfer exact-objective ownership to a terminal finalizer.
    fn take_solved<'a>(&'a mut self, session: &BabSession) -> SolvedObjective<'a> {
        SolvedObjective {
            coeffs: &self.objective,
            sense: session.model.sense(),
            offset: session.model.objective_offset(),
            exact: self.exact_objective.take(),
        }
    }
}

#[cfg(test)]
fn take_attempt_observations() -> Vec<AttemptObservation> {
    TEST_ATTEMPTS.with(|attempts| std::mem::take(&mut *attempts.borrow_mut()))
}

#[cfg(test)]
fn panic_after_next_attempt_deadline() {
    TEST_PANIC_AFTER_DEADLINE.with(|panic_next| panic_next.set(true));
}

/// Result of one optional route family.
enum RouteOutcome {
    Continue,
    Finished(Box<Outcome>),
}

impl RouteOutcome {
    fn finish(outcome: Outcome) -> Self {
        Self::Finished(Box::new(outcome))
    }

    fn finished(self) -> Option<Outcome> {
        match self {
            Self::Continue => None,
            Self::Finished(outcome) => Some(*outcome),
        }
    }
}

fn publish_early(session: &mut BabSession, outcome: Outcome) -> Result<Outcome, MilpError> {
    session.replay_claims = crate::cert_io::ledger::take();
    Ok(outcome)
}

fn deadline_expired(opts: &SolveOpts) -> bool {
    opts.deadline
        .is_some_and(|deadline| Instant::now() >= deadline)
}

pub(super) fn run(
    session: &mut BabSession,
    request: CheckRequest<'_, '_, '_>,
) -> Result<Outcome, MilpError> {
    // The tuning frame must span the prelude and anchor; nested sessions push
    // and restore their own profile on the same stack.
    let _session_tuned = crate::tune::activate_caller(session.opts.engine().profile());
    let mut state = CheckState::begin(session, &request);

    if state.ordinary_native_check {
        if let Some(outcome) = proof_prelude::run(session, &mut state).finished() {
            return publish_early(session, outcome);
        }
        if let Some(outcome) = certified::run(session, &mut state).finished() {
            return publish_early(session, outcome);
        }
    }
    if let Some(outcome) = replay::run_sat_relu_fallback(session, &mut state).finished() {
        return publish_early(session, outcome);
    }
    if state.ordinary_native_check {
        if let Some(outcome) = replay::run(session, &mut state).finished() {
            return publish_early(session, outcome);
        }
    }
    native::run(session, state, request)
}

#[cfg(test)]
mod tests;
