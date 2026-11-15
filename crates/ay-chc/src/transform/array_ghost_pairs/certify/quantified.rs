// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Distinct original-source authority for typed universal Horn premises.

mod observations;
mod query_anchors;
mod replay;
#[cfg(test)]
mod tests;

use super::super::candidate_houdini::try_query_anchored_model;
use super::super::record_projection::RecordProjection;
use super::super::source_observations;
use super::super::source_premises::{self, SourceControl, MAX_REPLAY_BYTES};
use super::super::ArrayGhostPairTransformer;
use super::*;
use crate::quantified::QuantifiedChcProblem;
use crate::{CancellationToken, ChcError, ChcReplayObligation};

/// No generic ghost certificate or QF model can be extracted from this type.
#[derive(Debug)]
pub(crate) struct QuantifiedSourceCertificate {
    inner: SourceCertificate,
}

#[derive(Debug)]
enum SourceCertificate {
    Ghost(GhostSourceCertificate),
    Observations(observations::ObservationCertificate),
}

#[derive(Debug)]
struct GhostSourceCertificate {
    source: Arc<str>,
    interpretation: GhostPairModel,
    records: Option<RecordSource>,
}

/// Search representation only; neither projection nor its model proves safety.
#[derive(Debug)]
struct RecordSource {
    projection: RecordProjection,
    projected: QuantifiedChcProblem,
}

pub(crate) fn try_quantified_source(
    problem: &QuantifiedChcProblem,
    deadline: Instant,
    cancellation: &CancellationToken,
    term_memory_limit: Option<usize>,
) -> Option<QuantifiedSourceCertificate> {
    let control = SourceControl::new(deadline, cancellation);
    control.poll()?;
    let inner = if source_observations::requires_observations(problem, &control)? {
        SourceCertificate::Observations(observations::try_source(
            problem,
            &control,
            term_memory_limit,
        )?)
    } else {
        SourceCertificate::Ghost(try_source_inner(problem, &control, term_memory_limit)?)
    };
    control.poll()?;
    Some(QuantifiedSourceCertificate { inner })
}

fn try_source_inner(
    problem: &QuantifiedChcProblem,
    control: &SourceControl<'_>,
    requested_memory: Option<usize>,
) -> Option<GhostSourceCertificate> {
    control.poll()?;
    let mut context = SmtContext::new();
    let limit = tighter_memory(context.term_memory_budget, requested_memory);
    context.set_term_memory_budget(limit);
    let _memory = SmtContext::scoped_thread_term_memory_budget(limit);
    let _deadline = crate::smt::ScopedSmtDeadline::install_until(control.deadline);
    if context.exact_term_memory_exceeded() {
        return None;
    }
    let records = if problem.source_problem().uses_datatype_features() {
        let projection = RecordProjection::new(problem, control)?;
        let projected = projection.project(problem, control)?;
        Some(RecordSource {
            projection,
            projected,
        })
    } else {
        None
    };
    let search = records
        .as_ref()
        .map_or(problem, |records| &records.projected);
    let source = search.source_problem();
    if source.uses_datatype_features()
        || source.has_stripped_body_forall()
        || source.clauses().len() != problem.premises().len()
        || problem.source_smtlib().len() > MAX_REPLAY_BYTES
    {
        return None;
    }
    for predicate in source.predicates() {
        control.poll()?;
        if !predicate
            .arg_sorts
            .iter()
            .all(source_premises::supported_sort)
        {
            return None;
        }
    }
    let spec = GhostPairSpec::analyze(source, 1);
    if spec.is_empty() {
        return None;
    }
    let raw_ghost = rewrite_source(search, &spec, control)?;
    // Retain half the remaining envelope for complete original certification.
    let remaining = control.deadline.saturating_duration_since(Instant::now());
    let synthesis_deadline = Instant::now()
        .checked_add(remaining / 2)?
        .min(control.deadline);
    let candidate = try_query_anchored_model(
        source,
        &raw_ghost,
        &spec,
        synthesis_deadline,
        control.cancellation,
    )?;
    control.poll()?;
    control.bytes(problem.source_smtlib().len())?;
    let certificate = GhostSourceCertificate {
        source: Arc::from(problem.source_smtlib()),
        interpretation: GhostPairModel {
            spec,
            model: candidate.model,
            executor_term_memory_limit: limit,
        },
        records,
    };
    if !certificate.discharge(problem, control) || context.exact_term_memory_exceeded() {
        return None;
    }
    control.poll()?;
    Some(certificate)
}

fn rewrite_source(
    problem: &QuantifiedChcProblem,
    spec: &GhostPairSpec,
    control: &SourceControl<'_>,
) -> Option<ChcProblem> {
    let source = problem.source_problem();
    let mut out = ChcProblem::new();
    for predicate in source.predicates() {
        control.poll()?;
        let id = out.declare_predicate(
            &predicate.name,
            spec.extended_sorts(predicate.id, &predicate.arg_sorts)?,
        );
        if id != predicate.id {
            return None;
        }
    }
    for name in source.action_names() {
        control.poll()?;
        out.declare_action(name.clone());
    }
    let transformer = ArrayGhostPairTransformer::new(1);
    for (clause, premises) in source.clauses().iter().zip(problem.premises()) {
        control.poll()?;
        source_premises::preflight_clause(clause, control)?;
        if query_anchors::append_split_queries(
            &mut out,
            problem,
            &transformer,
            spec,
            clause,
            premises,
            control,
        )? {
            continue;
        }
        let global_names = crate::quantified::functions::controlled::names(problem, control)?;
        out.add_clause(transformer.rewrite_source_clause(
            clause,
            spec,
            premises,
            global_names,
            Some(control),
        )?);
    }
    if source.is_fixedpoint_format() {
        out.set_fixedpoint_format();
    }
    control.poll()?;
    out.validate().ok()?;
    control.poll()?;
    Some(out)
}

impl QuantifiedSourceCertificate {
    pub(crate) fn replay_obligations(
        &self,
        problem: &QuantifiedChcProblem,
        deadline: Instant,
        cancellation: &CancellationToken,
    ) -> crate::ChcResult<Vec<ChcReplayObligation>> {
        match &self.inner {
            SourceCertificate::Ghost(certificate) => {
                certificate.replay_obligations(problem, deadline, cancellation)
            }
            SourceCertificate::Observations(certificate) => {
                certificate.replay_obligations(problem, deadline, cancellation)
            }
        }
    }

    pub(crate) fn recheck(
        &self,
        problem: &QuantifiedChcProblem,
        deadline: Instant,
        cancellation: &CancellationToken,
    ) -> bool {
        match &self.inner {
            SourceCertificate::Ghost(certificate) => {
                certificate.recheck(problem, deadline, cancellation)
            }
            SourceCertificate::Observations(certificate) => {
                certificate.recheck(problem, deadline, cancellation)
            }
        }
    }
}

impl GhostSourceCertificate {
    fn projected_source<'a>(
        &'a self,
        problem: &'a QuantifiedChcProblem,
        control: &SourceControl<'_>,
    ) -> Option<&'a ChcProblem> {
        control.poll()?;
        match &self.records {
            Some(records) if records.projection.matches_source(problem, control) => {
                Some(records.projected.source_problem())
            }
            None if !problem.source_problem().uses_datatype_features() => {
                Some(problem.source_problem())
            }
            _ => None,
        }
    }

    pub(crate) fn replay_obligations(
        &self,
        problem: &QuantifiedChcProblem,
        deadline: Instant,
        cancellation: &CancellationToken,
    ) -> crate::ChcResult<Vec<ChcReplayObligation>> {
        let control = SourceControl::new(deadline, cancellation);
        let fail = || {
            ChcError::Verification(
                "quantified source identity, structure or replay budget refused".into(),
            )
        };
        control.poll().ok_or_else(fail)?;
        if self.source.as_ref() != problem.source_smtlib() {
            return Err(fail());
        }
        let search = self.projected_source(problem, &control).ok_or_else(fail)?;
        if !validate_interpretation(search, &self.interpretation, || control.poll().is_none()) {
            return Err(fail());
        }
        let mut result = Vec::new();
        let mut bytes = 0usize;
        for index in 0..problem.source_problem().clauses().len() {
            let prepared = replay::prepare(
                problem,
                &self.interpretation,
                index,
                &control,
                self.records.as_ref().map(|records| &records.projection),
            )
            .ok_or_else(fail)?;
            bytes = bytes
                .checked_add(prepared.obligation.smtlib.len())
                .ok_or_else(fail)?;
            if bytes > MAX_REPLAY_BYTES {
                return Err(fail());
            }
            result.push(prepared.obligation);
        }
        control.poll().ok_or_else(fail)?;
        Ok(result)
    }

    pub(crate) fn recheck(
        &self,
        problem: &QuantifiedChcProblem,
        deadline: Instant,
        cancellation: &CancellationToken,
    ) -> bool {
        let control = SourceControl::new(deadline, cancellation);
        let accepted = self.recheck_inner(problem, &control);
        accepted && control.poll().is_some()
    }

    fn recheck_inner(&self, problem: &QuantifiedChcProblem, control: &SourceControl<'_>) -> bool {
        if control.poll().is_none() || self.source.as_ref() != problem.source_smtlib() {
            return false;
        }
        let mut context = SmtContext::new();
        let limit = tighter_memory(
            context.term_memory_budget,
            self.interpretation.executor_term_memory_limit,
        );
        context.set_term_memory_budget(limit);
        let _memory = SmtContext::scoped_thread_term_memory_budget(limit);
        let _deadline = crate::smt::ScopedSmtDeadline::install_until(control.deadline);
        !context.exact_term_memory_exceeded()
            && self.discharge(problem, control)
            && !context.exact_term_memory_exceeded()
            && control.poll().is_some()
    }

    fn discharge(&self, problem: &QuantifiedChcProblem, control: &SourceControl<'_>) -> bool {
        let mut bytes = 0;
        for (_, interp) in self.interpretation.model.iter() {
            if source_premises::preflight(&interp.formula, control, &mut bytes).is_none() {
                return false;
            }
        }
        let Some(search) = self.projected_source(problem, control) else {
            return false;
        };
        if control.poll().is_none()
            || self.source.as_ref() != problem.source_smtlib()
            || !validate_interpretation(search, &self.interpretation, || control.poll().is_none())
        {
            return false;
        }
        let count = problem.source_problem().clauses().len();
        if count == 0 {
            return false;
        }
        for index in 0..count {
            let Some(prepared) = replay::prepare(
                problem,
                &self.interpretation,
                index,
                control,
                self.records.as_ref().map(|records| &records.projection),
            ) else {
                return false;
            };
            if !replay::discharge(prepared, count - index, control) {
                return false;
            }
        }
        control.poll().is_some()
    }
}

fn tighter_memory(parent: Option<usize>, requested: Option<usize>) -> Option<usize> {
    match (parent, requested) {
        (Some(parent), Some(requested)) => Some(parent.min(requested)),
        (Some(parent), None) => Some(parent),
        (None, requested) => requested,
    }
}
