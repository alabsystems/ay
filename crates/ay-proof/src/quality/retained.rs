// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Retained BV evidence inside the existing strict whole-proof validation.
//! This crate-private checker connection does not authenticate an external
//! query/declaration environment; the owning wire entry lives in bundle.
//! Conditional disjoint/outside-frame routes consume ordered retained
//! prerequisites before installing source-local facts. This private lane still
//! needs public exact-export and CHC/sealed-reader adoption; it does not supply
//! external query authority merely by validating a snapshot.

use super::*;
use crate::bv_blast_solver::retained::wire::WireLimits;
use crate::checker::bv_bitblast::{
    plan_expensive_bv_credits_with_progress,
    retained_session::{RetainedOperation, RetainedSession, RetainedStepPayload},
};
use ay_core::time::Instant;

pub(crate) type Output = Vec<RetainedStepPayload>;
type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;

/// Retained checking requires both the typed declaration table and authored
/// assertion slice; the legacy optional contexts cannot weaken this entry.
pub(crate) struct Context<'a> {
    pub(crate) terms: &'a TermStore,
    pub(crate) dt_decls: Option<&'a [(String, Vec<String>)]>,
    pub(crate) ctor_selectors: Option<&'a [(String, Vec<String>)]>,
    pub(crate) datatype_member_signatures: &'a [DatatypeMemberSignature],
    pub(crate) problem_assertions: &'a [TermId],
}

impl<'a> From<Context<'a>> for StrictProofContext<'a> {
    fn from(context: Context<'a>) -> Self {
        Self {
            terms: context.terms,
            dt_decls: context.dt_decls,
            ctor_selectors: context.ctor_selectors,
            datatype_member_signatures: Some(context.datatype_member_signatures),
            problem_assertions: Some(context.problem_assertions),
        }
    }
}

pub(crate) struct Request<'a> {
    pub(crate) operation: RetainedOperation<'a>,
    pub(crate) deadline: Instant,
    /// Optional transport ceilings only tighten the source-counted envelope.
    pub(crate) wire_limits: Option<WireLimits>,
}

impl Request<'_> {
    pub(crate) fn effective_deadline(&self) -> Instant {
        self.wire_limits
            .map_or(self.deadline, |wire| self.deadline.min(wire.deadline))
    }
}

/// Same census and aggregate precharge as legacy checking. No work is issued
/// by an untrusted inventory, and no second precharge renews a lemma's credit.
pub(super) fn prepare<'proof, 'wire>(
    proof: &'proof Proof,
    terms: &'proof TermStore,
    request: Option<Request<'wire>>,
    progress: Progress<'_>,
) -> Result<Option<RetainedSession<'proof, 'wire>>, ProofCheckError> {
    match request {
        None => {
            let charge =
                crate::checker::validate_expensive_bv_budget_with_progress(proof, terms, progress)?;
            charge_progress(progress, charge.work, charge.bytes)?;
            Ok(None)
        }
        Some(request) => {
            // A supplied earlier wire clock covers census and prepayment too.
            // Keep the existing None path's callback sequence unchanged.
            if request.wire_limits.is_some() {
                with_control(request.effective_deadline(), progress, |progress| {
                    prepare_retained(proof, terms, request, progress)
                })
            } else {
                prepare_retained(proof, terms, request, progress)
            }
        }
    }
}

fn prepare_retained<'proof, 'wire>(
    proof: &'proof Proof,
    terms: &'proof TermStore,
    request: Request<'wire>,
    progress: Progress<'_>,
) -> Result<Option<RetainedSession<'proof, 'wire>>, ProofCheckError> {
    let plan = plan_expensive_bv_credits_with_progress(proof, terms, progress)?;
    let plan = match request.operation {
        RetainedOperation::Capture => plan,
        RetainedOperation::Replay(payloads) => plan.refine_replay(
            payloads,
            request.effective_deadline(),
            request.wire_limits,
            progress,
        )?,
    };
    let prepaid = plan
        .prepay(request.effective_deadline(), progress)
        .map_err(|_| ProofCheckError::ResourceLimit)?;
    RetainedSession::new_with_wire_limits(prepaid, request.operation, request.wire_limits, progress)
        .map(Some)
}

/// Check a complete refutation, capturing or independently reading ordinary
/// retained BV evidence under one original caller deadline. No result or
/// captured inventory escapes if assumption, datatype, other rule, terminal
/// empty-clause, or final control checks fail. The returned bytes remain
/// untrusted input for every subsequent reader, not a reusable proof permit.
pub(crate) fn check(
    proof: &Proof,
    context: Context<'_>,
    request: Request<'_>,
    progress: Progress<'_>,
) -> Result<(ProofQuality, Output), ProofCheckError> {
    with_control(request.effective_deadline(), progress, |progress| {
        let ((quality, clauses, deferred), output) = validate_strict_steps_with_retained(
            proof,
            context.into(),
            GenericTheoryDeferral::Reject,
            Some(request),
            progress,
        )?;
        debug_assert_eq!(deferred, []);
        // Bookkeeping over steps already validated (#completed-check-accepted);
        // this lane's final control is `with_control`'s, around the whole pass.
        ensure_terminal_empty_clause(&clauses)?;
        Ok((quality, output))
    })
}

/// Shared original-clock control for the enclosing snapshot reader as well as
/// the strict pass. Re-entering this wrapper never creates work/byte credit:
/// every debit still reaches the same caller-owned cumulative callback.
pub(crate) fn with_control<T>(
    deadline: Instant,
    progress: Progress<'_>,
    operation: impl FnOnce(Progress<'_>) -> Result<T, ProofCheckError>,
) -> Result<T, ProofCheckError> {
    Control {
        deadline,
        progress,
        refused: false,
    }
    .run(operation)
}

struct Control<'a> {
    deadline: Instant,
    progress: Progress<'a>,
    refused: bool,
}

impl Control<'_> {
    fn charge(&mut self, work: usize, bytes: usize) -> bool {
        if self.refused || Instant::now() >= self.deadline {
            self.refused = true;
            return false;
        }
        // A callback panic caught inside a validator must not revive control.
        self.refused = true;
        if !(self.progress)(work, bytes) || Instant::now() >= self.deadline {
            return false;
        }
        self.refused = false;
        true
    }

    fn run<T>(
        &mut self,
        operation: impl FnOnce(Progress<'_>) -> Result<T, ProofCheckError>,
    ) -> Result<T, ProofCheckError> {
        if !self.charge(0, 0) {
            return Err(ProofCheckError::ResourceLimit);
        }
        let result = operation(&mut |work, bytes| self.charge(work, bytes));
        // Strict-check tables and scratch have dropped. On late refusal the
        // remaining result owner must drop as well, with no partial publish.
        if !self.charge(0, 0) {
            drop(result);
            let _ = self.charge(0, 0);
            return Err(ProofCheckError::ResourceLimit);
        }
        result
    }
}

#[cfg(test)]
#[path = "retained/tests.rs"]
mod tests;

#[cfg(test)]
#[path = "retained/replay_pricing_tests.rs"]
mod replay_pricing_tests;
