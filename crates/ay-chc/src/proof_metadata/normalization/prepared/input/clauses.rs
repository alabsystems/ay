// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Body applications and clauses sort lexically; original multiplicity remains.

use super::super::{
    bytes::{self, Bytes},
    expression, order, spelling, Control, QueryError,
};
use super::{append_rows, predicate_app, Labels};
use crate::{ChcProblem, ClauseHead, HornClause};

pub(super) fn write<C: Control>(
    problem: &ChcProblem,
    labels: &Labels,
    out: &mut Bytes,
    control: &mut C,
) -> Result<(), QueryError> {
    control.offer(2 * std::mem::size_of::<Vec<Bytes>>(), 0)?;
    let mut rows = Vec::new();
    for index in 0..problem.clauses().len() {
        control.offer(1, 0)?;
        let row = clause(problem, &problem.clauses()[index], labels, control)?;
        bytes::push(&mut rows, control, || row)?;
    }
    append_rows(&rows, "", out, control)
}

fn clause<C: Control>(
    problem: &ChcProblem,
    clause: &HornClause,
    labels: &Labels,
    control: &mut C,
) -> Result<Bytes, QueryError> {
    let mut out = Bytes::new(control)?;
    out.text("clause action=", control)?;
    control.offer(2, 0)?;
    match clause
        .action_id
        .and_then(|action| problem.action_name(action))
    {
        Some(action) => spelling::quoted(&mut out, action, control)?,
        None => out.text("none", control)?,
    }
    out.text(" body=[", control)?;
    body(clause, labels, &mut out, control)?;
    out.text("] constraint=", control)?;
    control.offer(1, 0)?;
    match &clause.body.constraint {
        Some(expr) => {
            let value = expression::expression(expr, labels, control)?;
            out.append(&value.0, control)?;
        }
        None => out.text("true", control)?,
    }
    out.text(" head=", control)?;
    control.offer(1, 0)?;
    match &clause.head {
        ClauseHead::False => out.text("false", control)?,
        ClauseHead::Predicate(pred, args) => {
            let value = predicate_app(*pred, args, labels, control)?;
            out.append(&value.0, control)?;
        }
    }
    Ok(out)
}

fn body<C: Control>(
    clause: &HornClause,
    labels: &Labels,
    out: &mut Bytes,
    control: &mut C,
) -> Result<(), QueryError> {
    control.offer(2 * std::mem::size_of::<Vec<Bytes>>(), 0)?;
    let mut rows = Vec::new();
    for index in 0..clause.body.predicates.len() {
        control.offer(3, 0)?;
        let (pred, args) = &clause.body.predicates[index];
        let row = predicate_app(*pred, args, labels, control)?;
        bytes::push(&mut rows, control, || row)?;
    }
    let indices = order::indices(rows.len(), control, |a, b, control| {
        order::compare(&rows[a].0, &rows[b].0, control)
    })?;
    for (position, index) in indices.into_iter().enumerate() {
        control.offer(2, 0)?;
        if position != 0 {
            out.text(",", control)?;
        }
        out.append(&rows[index].0, control)?;
    }
    Ok(())
}
