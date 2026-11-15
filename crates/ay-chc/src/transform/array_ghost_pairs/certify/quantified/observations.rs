// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original-source authority for joint scalar observations of nested cells.

use super::*;
use source_observations::{replay as observation_replay, ObservationModel};

#[derive(Debug)]
pub(super) struct ObservationCertificate {
    source: Arc<str>,
    interpretation: ObservationModel,
    term_memory_limit: Option<usize>,
}

pub(super) fn try_source(
    problem: &QuantifiedChcProblem,
    control: &SourceControl<'_>,
    requested_memory: Option<usize>,
) -> Option<ObservationCertificate> {
    let certificate = try_source_inner(problem, control, requested_memory)?;
    // Solver contexts and scoped guards have dropped before admission.
    control.poll()?;
    Some(certificate)
}

fn try_source_inner(
    problem: &QuantifiedChcProblem,
    control: &SourceControl<'_>,
    requested_memory: Option<usize>,
) -> Option<ObservationCertificate> {
    control.poll()?;
    let mut context = SmtContext::new();
    let limit = tighter_memory(context.term_memory_budget, requested_memory);
    context.set_term_memory_budget(limit);
    let _memory = SmtContext::scoped_thread_term_memory_budget(limit);
    let _deadline = crate::smt::ScopedSmtDeadline::install_until(control.deadline);
    if context.exact_term_memory_exceeded() || problem.source_smtlib().len() > MAX_REPLAY_BYTES {
        return None;
    }
    let interpretation = source_observations::try_model(problem, control)?;
    control.bytes(problem.source_smtlib().len())?;
    let certificate = ObservationCertificate {
        source: Arc::from(problem.source_smtlib()),
        interpretation,
        term_memory_limit: limit,
    };
    if !certificate.discharge(problem, control) || context.exact_term_memory_exceeded() {
        return None;
    }
    control.poll()?;
    Some(certificate)
}

impl ObservationCertificate {
    fn validate(&self, problem: &QuantifiedChcProblem, control: &SourceControl<'_>) -> Option<()> {
        control.poll()?;
        if self.source.as_ref() != problem.source_smtlib() {
            return None;
        }
        observation_replay::validate(problem, &self.interpretation, control)?;
        control.poll()
    }

    pub(super) fn replay_obligations(
        &self,
        problem: &QuantifiedChcProblem,
        deadline: Instant,
        cancellation: &CancellationToken,
    ) -> crate::ChcResult<Vec<ChcReplayObligation>> {
        let control = SourceControl::new(deadline, cancellation);
        let fail = || {
            ChcError::Verification(
                "nested observation source identity, interpretation or replay budget refused"
                    .into(),
            )
        };
        self.validate(problem, &control).ok_or_else(fail)?;
        let mut result = Vec::new();
        let mut bytes = 0usize;
        for index in 0..problem.source_problem().clauses().len() {
            let prepared =
                observation_replay::prepare(problem, &self.interpretation, index, &control)
                    .ok_or_else(fail)?;
            bytes = bytes
                .checked_add(prepared.obligation.smtlib.len())
                .filter(|bytes| *bytes <= MAX_REPLAY_BYTES)
                .ok_or_else(fail)?;
            control.charge(1).ok_or_else(fail)?;
            result.try_reserve(1).map_err(|_| fail())?;
            result.push(prepared.obligation);
        }
        control.poll().ok_or_else(fail)?;
        Ok(result)
    }

    pub(super) fn recheck(
        &self,
        problem: &QuantifiedChcProblem,
        deadline: Instant,
        cancellation: &CancellationToken,
    ) -> bool {
        let control = SourceControl::new(deadline, cancellation);
        if control.poll().is_none() || self.source.as_ref() != problem.source_smtlib() {
            return false;
        }
        let accepted = {
            let mut context = SmtContext::new();
            let limit = tighter_memory(context.term_memory_budget, self.term_memory_limit);
            context.set_term_memory_budget(limit);
            let _memory = SmtContext::scoped_thread_term_memory_budget(limit);
            let _deadline = crate::smt::ScopedSmtDeadline::install_until(deadline);
            !context.exact_term_memory_exceeded()
                && self.discharge(problem, &control)
                && !context.exact_term_memory_exceeded()
        };
        accepted && control.poll().is_some()
    }

    fn discharge(&self, problem: &QuantifiedChcProblem, control: &SourceControl<'_>) -> bool {
        if self.validate(problem, control).is_none() {
            return false;
        }
        let count = problem.source_problem().clauses().len();
        if count == 0 {
            return false;
        }
        for index in 0..count {
            let Some(prepared) =
                observation_replay::prepare(problem, &self.interpretation, index, control)
            else {
                return false;
            };
            if !observation_replay::discharge(prepared, count - index, control) {
                return false;
            }
        }
        control.poll().is_some()
    }
}
