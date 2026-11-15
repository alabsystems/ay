// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! Exact finite-support elimination for one negative-position BV quantifier.
//!
//! For each admitted implication the unsigned guard denotes an exact interval.
//! Outside that interval the implication is true; inside it all guard atoms are
//! true. Thus `forall i. and_j (guard_j(i) => equality_j(i))` is exactly the
//! conjunction of each equality over its own interval. In particular, this does
//! not constrain the fresh resize array beyond the preserved/filled ranges.
//! This is not general quantifier elimination or symbolic-length resize support.

mod guard;
#[cfg(test)]
mod tests;
mod value;

use super::expr::{MAX_SINGLETON_FORALL_BINDER_NAME_BYTES, MAX_SINGLETON_FORALL_INSPECTION_NODES};
use crate::{ChcExpr, ChcOp, ChcSort};
use std::sync::Arc;
use value::Equality;

const MAX_DEPTH: usize = 64;

struct Budget {
    work_left: usize,
    output_left: usize,
}

impl Budget {
    fn new() -> Self {
        Self {
            work_left: MAX_SINGLETON_FORALL_INSPECTION_NODES,
            output_left: MAX_SINGLETON_FORALL_INSPECTION_NODES,
        }
    }

    fn work(&mut self, count: usize) -> Option<()> {
        self.work_left = self.work_left.checked_sub(count)?;
        Some(())
    }

    fn name(&mut self, name: &str) -> Option<()> {
        if name.len() > MAX_SINGLETON_FORALL_BINDER_NAME_BYTES {
            return None;
        }
        self.work(name.len().checked_add(1)?)
    }

    fn output(&mut self, count: usize) -> Option<()> {
        self.output_left = self.output_left.checked_sub(count)?;
        self.work(count)
    }
}

/// Scheduling is charged before reserving, including every duplicate edge.
fn children<'a>(
    stack: &mut Vec<(&'a ChcExpr, usize)>,
    args: &'a [Arc<ChcExpr>],
    depth: usize,
    budget: &mut Budget,
) -> Option<()> {
    if depth >= MAX_DEPTH {
        return None;
    }
    budget.work(args.len())?;
    stack.try_reserve(args.len()).ok()?;
    stack.extend(args.iter().rev().map(|arg| (arg.as_ref(), depth + 1)));
    Some(())
}

struct GuardedEquality<'a> {
    lower: u128,
    upper: u128,
    equality: Equality<'a>,
}

pub(super) fn eliminate(body: &ChcExpr, binder: &str, sort: &ChcSort) -> Option<ChcExpr> {
    let ChcSort::BitVec(width @ 1..=64) = sort else {
        return None;
    };
    let mut budget = Budget::new();
    budget.name(binder)?;
    budget.work(1)?;
    let mut pending = vec![(body, 0)];
    let mut records = Vec::new();
    let mut count = 0usize;
    while let Some((node, depth)) = pending.pop() {
        match node {
            ChcExpr::Op(ChcOp::And, args) if !args.is_empty() => {
                children(&mut pending, args, depth, &mut budget)?;
            }
            ChcExpr::Op(ChcOp::Implies, args) if args.len() == 2 => {
                let (lower, upper) = guard::support(&args[0], binder, *width, &mut budget)?;
                // Even an empty interval must authenticate the whole consequent.
                let equality = Equality::parse(&args[1], binder, *width, &mut budget)?;
                let instances = usize::try_from(upper.saturating_sub(lower)).ok()?;
                budget.output(instances.checked_mul(equality.output_cost())?)?;
                count = count.checked_add(instances)?;
                records.try_reserve(1).ok()?;
                records.push(GuardedEquality {
                    lower,
                    upper,
                    equality,
                });
            }
            _ => return None,
        }
    }
    emit(records, count, *width)
}

fn emit(records: Vec<GuardedEquality<'_>>, count: usize, width: u32) -> Option<ChcExpr> {
    let mut output = Vec::new();
    output.try_reserve_exact(count).ok()?;
    for record in records {
        for index in record.lower..record.upper {
            output.push(record.equality.instantiate(index, width)?);
        }
    }
    if output.is_empty() {
        Some(ChcExpr::Bool(true))
    } else {
        Some(ChcExpr::Op(ChcOp::And, output))
    }
}
