// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Iterative occurrence postorder; no Arc/source clone or deduplication.

use super::{
    bytes::{self, Bytes},
    input::Labels,
    Control, QueryError,
};
use crate::{ChcExpr, ChcSort};

mod finish;

enum Task<'source> {
    Expression(&'source ChcExpr),
    Sort(&'source ChcSort),
    FinishExpression(&'source ChcExpr, usize),
    FinishSort(&'source ChcSort, usize),
}

pub(super) fn expression<C: Control>(
    expr: &ChcExpr,
    labels: &Labels,
    control: &mut C,
) -> Result<Bytes, QueryError> {
    control.offer(std::mem::size_of::<Task<'_>>(), 0)?;
    walk(Task::Expression(expr), labels, control)
}

pub(super) fn sort<C: Control>(sort: &ChcSort, control: &mut C) -> Result<Bytes, QueryError> {
    control.offer(
        std::mem::size_of::<Task<'_>>() + std::mem::size_of::<Labels>(),
        0,
    )?;
    walk(Task::Sort(sort), &Labels::empty(), control)
}

fn walk<C: Control>(
    first: Task<'_>,
    labels: &Labels,
    control: &mut C,
) -> Result<Bytes, QueryError> {
    control.offer(
        2 * std::mem::size_of::<Vec<Task<'_>>>() + 2 * std::mem::size_of::<Vec<Bytes>>(),
        0,
    )?;
    let mut tasks = Vec::new();
    let mut values = Vec::new();
    bytes::push(&mut tasks, control, || first)?;
    while !tasks.is_empty() {
        control.offer(2 * std::mem::size_of::<Task<'_>>() + 8, 0)?;
        let Some(task) = tasks.pop() else {
            return Err(QueryError::Invalid("missing canonical task"));
        };
        match task {
            Task::Expression(expr) => schedule_expression(expr, values.len(), &mut tasks, control)?,
            Task::Sort(sort) => schedule_sort(sort, values.len(), &mut tasks, control)?,
            Task::FinishExpression(expr, start) => {
                let value = finish::expression(expr, &values[start..], labels, control)?;
                values.truncate(start);
                bytes::push(&mut values, control, || value)?;
            }
            Task::FinishSort(sort, start) => {
                let value = finish::sort(sort, &values[start..], control)?;
                values.truncate(start);
                bytes::push(&mut values, control, || value)?;
            }
        }
    }
    control.offer(std::mem::size_of::<Bytes>() + 1, 0)?;
    values
        .pop()
        .ok_or(QueryError::Invalid("missing canonical result"))
}

fn schedule_expression<'source, C: Control>(
    expr: &'source ChcExpr,
    start: usize,
    tasks: &mut Vec<Task<'source>>,
    control: &mut C,
) -> Result<(), QueryError> {
    bytes::push(tasks, control, || Task::FinishExpression(expr, start))?;
    match expr {
        ChcExpr::ArrayLambda(lambda) => {
            for capture in lambda.captures().iter().rev() {
                bytes::push(tasks, control, || Task::Expression(capture))?;
            }
            bytes::push(tasks, control, || Task::Expression(lambda.body()))?;
            for formal in lambda.formals().iter().rev() {
                bytes::push(tasks, control, || Task::Sort(&formal.sort))?;
            }
            bytes::push(tasks, control, || Task::Sort(&lambda.binder().sort))?;
        }
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            for index in (0..args.len()).rev() {
                control.offer(2, 0)?;
                bytes::push(tasks, control, || Task::Expression(&args[index]))?;
            }
            if let ChcExpr::FuncApp(_, sort, _) = expr {
                bytes::push(tasks, control, || Task::Sort(sort))?;
            }
        }
        ChcExpr::Var(var) => bytes::push(tasks, control, || Task::Sort(&var.sort))?,
        ChcExpr::ConstArrayMarker(sort) => bytes::push(tasks, control, || Task::Sort(sort))?,
        ChcExpr::ConstArray(sort, value) => {
            bytes::push(tasks, control, || Task::Expression(value))?;
            bytes::push(tasks, control, || Task::Sort(sort))?;
        }
        ChcExpr::Bool(_)
        | ChcExpr::Int(_)
        | ChcExpr::Real(_, _)
        | ChcExpr::BitVec(_, _)
        | ChcExpr::IsTesterMarker(_) => {}
    }
    Ok(())
}

fn schedule_sort<'source, C: Control>(
    sort: &'source ChcSort,
    start: usize,
    tasks: &mut Vec<Task<'source>>,
    control: &mut C,
) -> Result<(), QueryError> {
    bytes::push(tasks, control, || Task::FinishSort(sort, start))?;
    match sort {
        ChcSort::Array(key, value) => {
            bytes::push(tasks, control, || Task::Sort(value))?;
            bytes::push(tasks, control, || Task::Sort(key))?;
        }
        ChcSort::Datatype { .. } => {
            return Err(QueryError::Invalid(
                "datatype-bearing normalized input is unsupported",
            ))
        }
        ChcSort::Bool
        | ChcSort::Int
        | ChcSort::Real
        | ChcSort::BitVec(_)
        | ChcSort::Uninterpreted(_) => {}
    }
    Ok(())
}
