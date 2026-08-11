// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Linear authority for one independently checked constructive quantified
//! model.
//!
//! The three inputs are intentionally produced by separate components:
//!
//! * `ay-model-check` proves the exact universal implication under total
//!   projection functions;
//! * `ay-frontend` positively binds those function heads to live, ordinary
//!   free declarations at one source/scope epoch; and
//! * the authored-query boundary proves that the same roots are the complete
//!   public hard query, with no assumptions, objectives, or soft constraints.
//!
//! No input is a boolean, none can be forged here, and the combined value is
//! non-`Clone`. Only the SAT-emission module consumes it.

use ay_frontend::Context;
use ay_model_check::CheckedProjectionImplication;
use std::sync::atomic::Ordering;

use super::quantifier_loop::projection_candidate::{
    check_projection_source, CheckedProjectionSourceEvidence, ProjectionSourceOutcome,
};
use super::{AuthoredPlainHardQueryPermit, Executor};

/// Outcome of attempting the restricted constructive certificate before the
/// general solver mutates the authored query.
pub(in crate::executor) enum ProjectionSatAttempt {
    Checked(Box<CheckedProjectionSatEvidence>),
    Declined,
    Stopped,
}

/// Opaque, linear evidence for one exact constructive quantified SAT model.
#[derive(Debug)]
pub(in crate::executor) struct CheckedProjectionSatEvidence {
    authored_query: AuthoredPlainHardQueryPermit,
    checked_source: CheckedProjectionSourceEvidence,
}

impl CheckedProjectionSatEvidence {
    /// Combine all three independent evidence layers while they describe the
    /// same live executor query.
    pub(in crate::executor) fn authorize(
        executor: &Executor,
        authored_query: AuthoredPlainHardQueryPermit,
        checked_source: CheckedProjectionSourceEvidence,
    ) -> Result<Self, ProjectionSatAuthorizationError> {
        if !authored_query.is_current(executor) {
            return Err(ProjectionSatAuthorizationError::StaleAuthoredQuery);
        }
        if authored_query.roots() != checked_source.roots() {
            return Err(ProjectionSatAuthorizationError::RootMismatch);
        }
        if authored_query.source_context_stamp() != checked_source.source_context_stamp() {
            return Err(ProjectionSatAuthorizationError::SourceEpochMismatch);
        }
        if !checked_source.is_current(&executor.ctx, authored_query.roots()) {
            return Err(ProjectionSatAuthorizationError::StaleCheckedSource);
        }
        Ok(Self {
            authored_query,
            checked_source,
        })
    }

    /// The independently proved total projection semantics.
    pub(in crate::executor) fn semantics(&self) -> &CheckedProjectionImplication {
        self.checked_source.semantics()
    }

    /// Recheck every query, source, declaration, and semantic snapshot before
    /// and after model installation.
    pub(in crate::executor) fn is_current(&self, executor: &Executor) -> bool {
        self.authored_query.is_current(executor)
            && self.authored_query.roots() == self.checked_source.roots()
            && self.authored_query.source_context_stamp()
                == self.checked_source.source_context_stamp()
            && self
                .checked_source
                .is_current(&executor.ctx, self.authored_query.roots())
    }

    /// Exact hard roots certified by all evidence layers.
    pub(in crate::executor) fn roots(&self) -> &[ay_core::TermId] {
        self.authored_query.roots()
    }

    /// Context-only currentness helper used by the model installer without
    /// granting that model layer access to query authority internals.
    pub(in crate::executor) fn source_is_current(&self, ctx: &Context) -> bool {
        self.checked_source.is_current(ctx, self.roots())
    }
}

/// Fail-closed failure to combine otherwise opaque evidence layers.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub(in crate::executor) enum ProjectionSatAuthorizationError {
    #[error("authored projection query permit is stale")]
    StaleAuthoredQuery,
    #[error("semantic/source roots differ from the authored hard query")]
    RootMismatch,
    #[error("semantic/source binding was checked at another source epoch")]
    SourceEpochMismatch,
    #[error("semantic/source projection evidence is stale")]
    StaleCheckedSource,
}

impl Executor {
    /// Attempt the independently checked projection backend under the active
    /// solve's interrupt, deadline, and memory envelope.
    pub(in crate::executor) fn try_authorize_projection_sat(
        &self,
        authored_query: AuthoredPlainHardQueryPermit,
    ) -> ProjectionSatAttempt {
        if !authored_query.is_current(self) {
            return ProjectionSatAttempt::Declined;
        }

        let interrupt = self.solve_interrupt.clone();
        let deadline = self.solve_deadline.clone();
        let memory_limit = self.memory_limit;
        let mut memory_poll_countdown = 0u8;
        let mut should_stop = || {
            if interrupt
                .as_ref()
                .is_some_and(|flag| flag.load(Ordering::Relaxed))
                || deadline.expired()
            {
                return true;
            }
            if memory_poll_countdown == 0 {
                memory_poll_countdown = 63;
                crate::memory::memory_exceeded(memory_limit) || ay_sys::process_memory_exceeded()
            } else {
                memory_poll_countdown -= 1;
                false
            }
        };

        let checked_source =
            match check_projection_source(&self.ctx, authored_query.roots(), &mut should_stop) {
                ProjectionSourceOutcome::Checked(checked) => checked,
                ProjectionSourceOutcome::Stopped => return ProjectionSatAttempt::Stopped,
                ProjectionSourceOutcome::ResourceLimit => return ProjectionSatAttempt::Declined,
                ProjectionSourceOutcome::NoCandidate => return ProjectionSatAttempt::Declined,
                ProjectionSourceOutcome::Rejected(rejection) => {
                    tracing::debug!(%rejection, "projection SAT certificate declined");
                    return ProjectionSatAttempt::Declined;
                }
            };
        if should_stop() {
            return ProjectionSatAttempt::Stopped;
        }
        match CheckedProjectionSatEvidence::authorize(self, authored_query, checked_source) {
            Ok(checked) => ProjectionSatAttempt::Checked(Box::new(checked)),
            Err(error) => {
                tracing::debug!(%error, "projection SAT evidence became stale before authorization");
                ProjectionSatAttempt::Declined
            }
        }
    }
}
