// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original-source discharge for joint scalar observations, never a QF seal.

mod pullback;
mod render;
#[cfg(test)]
mod tests;
mod validation;

use super::super::source_premises::{self, SourceControl, MAX_REPLAY_BYTES};
use super::ObservationModel;
use crate::quantified::records::{registry_bytes, sort_bytes, Registry};
use crate::quantified::QuantifiedChcProblem;
use crate::smt::{SmtContext, SmtResult};
use crate::{
    ChcExpr, ChcOp, ChcReplayObligation, ChcReplayObligationKind, ChcSort, ChcVar, ClauseHead,
    HornClause, InvariantModel, PredicateId,
};
use ay_core::time::Instant;
use std::sync::Arc;
use std::time::Duration;

pub(in crate::transform::array_ghost_pairs) use validation::validate;

pub(in crate::transform::array_ghost_pairs) struct Prepared<'a> {
    pub(in crate::transform::array_ghost_pairs) obligation: ChcReplayObligation,
    finite_query: ChcExpr,
    source: &'a QuantifiedChcProblem,
    full_source_only: bool,
}

/// The caller validates the immutable whole model once before iterating clauses.
/// Local identity/index checks do not mint authority or accept partial output.
pub(in crate::transform::array_ghost_pairs) fn prepare<'a>(
    problem: &'a QuantifiedChcProblem,
    model: &ObservationModel,
    index: usize,
    control: &SourceControl<'_>,
) -> Option<Prepared<'a>> {
    let prepared = prepare_inner(problem, model, index, control)?;
    // All registry, substitutions and binder-allocation scratch is gone.
    control.poll()?;
    Some(prepared)
}

fn prepare_inner<'a>(
    problem: &'a QuantifiedChcProblem,
    model: &ObservationModel,
    index: usize,
    control: &SourceControl<'_>,
) -> Option<Prepared<'a>> {
    if !model.layout.matches_source(problem, control) {
        return None;
    }
    let full_source_only = !problem.function_declarations().is_empty()
        || super::classify::source(problem, control)? == super::classify::Shape::Wide;
    let clause = problem.source_problem().clauses().get(index)?;
    let premises = problem.premises().get(index)?;
    source_premises::preflight_clause(clause, control)?;
    // Registry construction/rendering and the later finite context's copy.
    control.bytes(registry_bytes(problem.source_problem())?.checked_mul(3)?)?;
    let registry = Registry::new(problem.source_problem()).ok()?;
    let variables = source_premises::clause_variables(clause, premises, control)?;
    let mut fresh = pullback::Fresh::new(problem.source_smtlib());
    let (head, head_axes) = pullback::head(model, clause, &mut fresh, control)?;
    let head_terms = pullback::axis_terms(&head_axes, control)?;
    let indices = super::super::collect_index_terms(clause, super::super::INDEX_TERM_CAP);
    let (bodies, mut hints) =
        pullback::bodies(model, clause, &head_terms, &indices, &mut fresh, control)?;
    let mut source_indices = head_terms;
    control.charge(indices.len())?;
    source_indices.extend(indices);
    hints.extend(source_premises::instances(
        premises,
        &source_indices,
        control,
    )?);
    let mut conjuncts = Vec::new();
    if let Some(constraint) = &clause.body.constraint {
        conjuncts.push(constraint.clone());
    }
    for hint in &hints {
        source_premises::preflight(hint, control, &mut 0)?;
        conjuncts.push(hint.clone());
    }
    conjuncts.extend(head.iter().cloned());
    let finite_query = ChcExpr::and_all_checked(conjuncts, || control.poll().is_none())?;
    source_premises::preflight(&finite_query, control, &mut 0)?;
    let smtlib = render::render(
        problem,
        &registry,
        render::Input {
            clause,
            premises,
            variables: &variables,
            head_axes: &head_axes,
            bodies: &bodies,
            hints: &hints,
            head: head.as_ref(),
        },
        control,
    )?;
    let kind = match clause.head {
        ClauseHead::Predicate(..) if clause.body.predicates.is_empty() => {
            ChcReplayObligationKind::Initiation
        }
        ClauseHead::Predicate(..) => ChcReplayObligationKind::Consecution,
        ClauseHead::False => ChcReplayObligationKind::Safety,
    };
    control.poll()?;
    Some(Prepared {
        obligation: ChcReplayObligation {
            name: format!("source-observation-{index}-{}", kind.as_str()),
            kind,
            clause_index: index,
            smtlib,
        },
        finite_query,
        source: problem,
        full_source_only,
    })
}

pub(in crate::transform::array_ghost_pairs) fn discharge(
    prepared: Prepared<'_>,
    remaining_clauses: usize,
    control: &SourceControl<'_>,
) -> bool {
    if control.poll().is_none() {
        return false;
    }
    let now = Instant::now();
    let remaining = control.deadline.saturating_duration_since(now);
    // This clause's fair share of the caller's own remaining envelope, never
    // the flat ghost lane's five-second `per_rule_budget` ceiling (see
    // `source_premises::clause_budget`). Wide and UF-bearing sources
    // (`full_source_only`) spend the whole share in ONE executor call on the
    // complete original text; the others spend half on the finite instance
    // first. Neither shape settles in milliseconds here: the joint nested-store
    // consecution takes about two seconds of finite solving, which the old cap
    // (2.5 s for the finite half) turned into a load-dependent Unknown.
    // Admission is unchanged: only an UNSAT verdict is accepted, and the
    // deadline below is clamped to `control.deadline`, so no clause can outrun
    // the budget the caller set.
    let budget = source_premises::clause_budget(remaining, remaining_clauses);
    let Some(deadline) = now.checked_add(budget).map(|d| d.min(control.deadline)) else {
        return false;
    };
    let result = discharge_inner(prepared, deadline, budget, control);
    // Destruction of the context/prepared expressions precedes final admission.
    result && control.poll().is_some() && Instant::now() < deadline
}

fn discharge_inner(
    prepared: Prepared<'_>,
    deadline: Instant,
    rule_budget: Duration,
    control: &SourceControl<'_>,
) -> bool {
    let _deadline = crate::smt::ScopedSmtDeadline::install_until(deadline);
    let mut smt = if !prepared.full_source_only {
        prepared.source.source_problem().make_smt_context()
    } else {
        // Full text already carries the complete record and function registry;
        // only inherit the active memory envelope, not another schema copy.
        SmtContext::new()
    };
    if control.poll().is_none() || smt.exact_term_memory_exceeded() {
        return false;
    }
    if !prepared.full_source_only {
        let Some(finite_budget) = super::super::certify::bounded_executor_budget(rule_budget, 2)
        else {
            return false;
        };
        let result =
            smt.check_sat_with_executor_fallback_timeout(&prepared.finite_query, finite_budget);
        if control.poll().is_none()
            || smt.exact_term_memory_exceeded()
            || Instant::now() >= deadline
        {
            return false;
        }
        if matches!(result, SmtResult::Unsat) {
            return true;
        }
    }
    // Wide observations and UF-bearing sources need the complete original
    // obligation, not the legacy finite-certificate shortcut. The finite
    // context infers functions from applications; it cannot authenticate
    // unused or matrix-only declarations. Never fix a selected interpretation:
    // UNSAT must hold with every retained source function uninterpreted.
    let verdict = crate::smt::executor_adapter::smtlib_first_verdict_via_executor_with_limit(
        &prepared.obligation.smtlib,
        crate::smt::executor_adapter::ReplayLimit::Cancellable {
            deadline,
            cancellation: &control.replay_cancellation,
        },
        smt.term_memory_budget,
    );
    verdict.as_deref() == Some("unsat")
        && !smt.exact_term_memory_exceeded()
        && control.poll().is_some()
        && Instant::now() < deadline
}
