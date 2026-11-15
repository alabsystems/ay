// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Canonical rows; every collection and payload copy uses the same control.

use super::{
    bytes::{self, Bytes},
    expression, order, spelling, ChcProblem, Control, QueryError, NORMALIZED_CHC_INPUT_SCHEMA,
};
use crate::PredicateId;

mod clauses;
mod labels;
pub(super) use labels::Labels;

pub(super) fn build<C: Control>(
    problem: &ChcProblem,
    control: &mut C,
) -> Result<String, QueryError> {
    control.offer(2, 0)?;
    if !problem.datatype_defs().is_empty() {
        return Err(QueryError::Invalid(
            "datatype-bearing normalized input is unsupported",
        ));
    }
    let labels = labels::build(problem, control)?;
    let mut out = Bytes::new(control)?;
    out.text(NORMALIZED_CHC_INPUT_SCHEMA, control)?;
    out.text("\nfixedpoint=", control)?;
    control.offer(1, 0)?;
    out.text(
        if problem.is_fixedpoint_format() {
            "true"
        } else {
            "false"
        },
        control,
    )?;
    out.text("\ndatatypes\nactions\n", control)?;
    actions(problem, &mut out, control)?;
    out.text("predicates\n", control)?;
    predicates(problem, &labels, &mut out, control)?;
    out.text("clauses\n", control)?;
    clauses::write(problem, &labels, &mut out, control)?;
    // Labels and every row/order/visitor collection die before returning bytes.
    out.finish(control)
}

fn actions<C: Control>(
    problem: &ChcProblem,
    out: &mut Bytes,
    control: &mut C,
) -> Result<(), QueryError> {
    control.offer(2 * std::mem::size_of::<Vec<Bytes>>(), 0)?;
    let mut rows = Vec::new();
    for index in 0..problem.action_names().len() {
        control.offer(2, 0)?;
        let mut row = Bytes::new(control)?;
        spelling::quoted(&mut row, &problem.action_names()[index], control)?;
        bytes::push(&mut rows, control, || row)?;
    }
    append_rows(&rows, "action ", out, control)
}

fn predicates<C: Control>(
    problem: &ChcProblem,
    labels: &Labels,
    out: &mut Bytes,
    control: &mut C,
) -> Result<(), QueryError> {
    control.offer(2 * std::mem::size_of::<Vec<Bytes>>(), 0)?;
    let mut rows = Vec::new();
    for index in 0..problem.predicates().len() {
        control.offer(3, 0)?;
        let predicate = &problem.predicates()[index];
        let mut row = Bytes::new(control)?;
        row.text("predicate ", control)?;
        labels.write(&mut row, predicate.id, control)?;
        row.text(" name=", control)?;
        spelling::quoted(&mut row, &predicate.name, control)?;
        row.text(" args=[", control)?;
        for argument in 0..predicate.arg_sorts.len() {
            control.offer(2, 0)?;
            if argument != 0 {
                row.text(",", control)?;
            }
            let sort = expression::sort(&predicate.arg_sorts[argument], control)?;
            row.append(&sort.0, control)?;
        }
        row.text("]", control)?;
        bytes::push(&mut rows, control, || row)?;
    }
    append_rows(&rows, "", out, control)
}

pub(super) fn append_rows<C: Control>(
    rows: &[Bytes],
    prefix: &str,
    out: &mut Bytes,
    control: &mut C,
) -> Result<(), QueryError> {
    let indices = order::indices(rows.len(), control, |a, b, control| {
        order::compare(&rows[a].0, &rows[b].0, control)
    })?;
    for index in indices {
        control.offer(1, 0)?;
        out.text(prefix, control)?;
        out.append(&rows[index].0, control)?;
        out.text("\n", control)?;
    }
    Ok(())
}

pub(super) fn predicate_app<C: Control>(
    pred: PredicateId,
    args: &[crate::ChcExpr],
    labels: &Labels,
    control: &mut C,
) -> Result<Bytes, QueryError> {
    let mut out = Bytes::new(control)?;
    labels.write(&mut out, pred, control)?;
    out.text("(", control)?;
    for index in 0..args.len() {
        control.offer(2, 0)?;
        if index != 0 {
            out.text(",", control)?;
        }
        let argument = expression::expression(&args[index], labels, control)?;
        out.append(&argument.0, control)?;
    }
    out.text(")", control)?;
    Ok(out)
}
