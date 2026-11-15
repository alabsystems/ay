// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::control::Control;
use super::runner::{EvidenceKind, Runner};
use super::*;
use ay_chc::quantified::QuantifiedChcQueryObligation;
use std::collections::HashSet;

pub(super) enum Outcome<E> {
    CheckedSafe(E),
    CheckedUnsafe(E),
    Unknown(QuantifiedQueryUnknownReason),
    Error(crate::EncodeError),
}

pub(super) struct Row<E> {
    pub obligation: QuantifiedChcQueryObligation,
    pub outcome: Outcome<E>,
    pub elapsed: Duration,
}

pub(super) struct Batch<E> {
    pub rows: Vec<Row<E>>,
    pub all_checked: bool,
    pub checked_unsafe: bool,
}

pub(super) fn digest(source: &str) -> String {
    ay_chc::ChcProofArtifactDigest::from_bytes("quantified-source", source.as_bytes()).sha256
}

fn invalid_binding() -> crate::EncodeError {
    ay_chc::ChcError::Verification("quantified query source binding mismatch".into()).into()
}

pub(super) fn validate_obligations(
    source_hash: &str,
    obligations: &[QuantifiedChcQueryObligation],
    control: &Control<'_>,
) -> crate::Result<()> {
    if obligations.is_empty() {
        return Err(invalid_binding());
    }
    let mut identities = HashSet::new();
    let mut previous = None;
    for obligation in obligations {
        control.require_live()?;
        let id = obligation.id();
        let key = (
            id.source_query_ordinal(),
            id.query_clause_index(),
            id.defining_clause_index(),
        );
        if id.aggregate_source_sha256() != source_hash
            || id.content_sha256() != digest(obligation.problem().source_smtlib())
            || !identities.insert(key)
            || previous.is_some_and(|last| last >= key)
        {
            return Err(invalid_binding());
        }
        previous = Some(key);
    }
    control.require_live()
}

pub(super) fn run<R: Runner>(
    obligations: Vec<QuantifiedChcQueryObligation>,
    control: &Control<'_>,
    memory: Option<usize>,
    runner: &mut R,
) -> Batch<R::Evidence> {
    let expected: Vec<_> = obligations.iter().map(|o| o.id().clone()).collect();
    let total = obligations.len();
    let mut rows = Vec::with_capacity(total);
    for (index, obligation) in obligations.into_iter().enumerate() {
        let started = control.now();
        let outcome = run_one(obligation.problem(), total - index, control, memory, runner);
        rows.push(Row {
            obligation,
            outcome,
            elapsed: control.now().saturating_duration_since(started),
        });
    }
    let all_checked = complete(&expected, &rows, runner);
    let checked_unsafe = complete_unsafe(&expected, &rows, runner);
    // Drop membership scratch before the final admission checkpoint.
    drop(expected);
    let live = control.reason().is_none();
    Batch {
        rows,
        all_checked: all_checked && live,
        checked_unsafe: checked_unsafe && live,
    }
}

pub(super) fn complete<R: Runner>(
    expected: &[QuantifiedChcQueryId],
    rows: &[Row<R::Evidence>],
    runner: &R,
) -> bool {
    !expected.is_empty()
        && expected.len() == rows.len()
        && expected.iter().zip(rows).all(|(id, row)| {
            id == row.obligation.id()
                && id.content_sha256() == digest(row.obligation.problem().source_smtlib())
                && matches!(&row.outcome, Outcome::CheckedSafe(evidence)
                    if runner.kind(evidence) == EvidenceKind::Safe
                        && runner.source(evidence) == row.obligation.problem().source_smtlib())
        })
}

/// One refuted row suffices, but it must belong to the complete original batch.
/// A missing/reordered/foreign row cannot turn a forged subset into authority.
pub(super) fn complete_unsafe<R: Runner>(
    expected: &[QuantifiedChcQueryId],
    rows: &[Row<R::Evidence>],
    runner: &R,
) -> bool {
    !expected.is_empty()
        && expected.len() == rows.len()
        && expected.iter().zip(rows).all(|(id, row)| {
            id == row.obligation.id()
                && id.content_sha256() == digest(row.obligation.problem().source_smtlib())
        })
        && rows.iter().any(|row| {
            matches!(&row.outcome, Outcome::CheckedUnsafe(evidence)
                if runner.kind(evidence) == EvidenceKind::Unsafe
                    && runner.source(evidence) == row.obligation.problem().source_smtlib())
        })
}

fn run_one<R: Runner>(
    problem: &QuantifiedChcProblem,
    rows_left: usize,
    control: &Control<'_>,
    memory: Option<usize>,
    runner: &mut R,
) -> Outcome<R::Evidence> {
    if let Some(reason) = control.reason() {
        return Outcome::Unknown(reason);
    }
    let Some(row_deadline) = control.row_deadline(rows_left) else {
        return Outcome::Unknown(
            control
                .reason()
                .unwrap_or(QuantifiedQueryUnknownReason::BudgetExhausted),
        );
    };
    let solve_budget = row_deadline.saturating_duration_since(control.now()) / 2;
    if solve_budget.is_zero() {
        return Outcome::Unknown(QuantifiedQueryUnknownReason::BudgetExhausted);
    }
    let candidate = match runner.solve(problem, solve_budget, memory, control.token()) {
        Ok(candidate) => candidate,
        Err(error) => return Outcome::Error(error),
    };
    if let Some(reason) = row_stop(control, row_deadline) {
        drop(candidate);
        return Outcome::Unknown(reason);
    }
    let Some(evidence) = candidate else {
        return Outcome::Unknown(QuantifiedQueryUnknownReason::Inconclusive);
    };
    if runner.source(&evidence) != problem.source_smtlib() {
        return Outcome::Error(invalid_binding());
    }
    let replay_budget = row_deadline.saturating_duration_since(control.now());
    if replay_budget.is_zero() {
        return Outcome::Unknown(QuantifiedQueryUnknownReason::BudgetExhausted);
    }
    let accepted = match runner.recheck(&evidence, problem, replay_budget, control.token()) {
        Ok(accepted) => accepted,
        Err(error) => return Outcome::Error(error),
    };
    let source_matches = runner.source(&evidence) == problem.source_smtlib();
    let kind = runner.kind(&evidence);
    if let Some(reason) = row_stop(control, row_deadline) {
        drop(evidence);
        return Outcome::Unknown(reason);
    }
    if accepted && source_matches {
        match kind {
            EvidenceKind::Safe => Outcome::CheckedSafe(evidence),
            EvidenceKind::Unsafe => Outcome::CheckedUnsafe(evidence),
        }
    } else {
        Outcome::Unknown(QuantifiedQueryUnknownReason::ReplayRejected)
    }
}

fn row_stop(control: &Control<'_>, deadline: Instant) -> Option<QuantifiedQueryUnknownReason> {
    control.reason().or_else(|| {
        (control.now() >= deadline).then_some(QuantifiedQueryUnknownReason::BudgetExhausted)
    })
}
