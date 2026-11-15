// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! Exact finite-support normalization at the existing typed forall constructor.
//!
//! Each admitted guard is an exact unsigned interval. Outside it the guarded
//! equality is true; inside it the equality must hold. Distributing forall over
//! the conjunction therefore yields precisely the emitted ground equalities,
//! in either polarity, with no additional array-tail constraint. This mirrors
//! the CHC parser's narrow algebra without depending on the higher-level parser.
//!
//! All input records and output costs are checked before emission. Refusal
//! leaves the caller's original quantifier intact. Individual allocations and
//! destruction are not a wall-clock bound; there is no new cancellation API.

mod guard;
mod index;
#[cfg(test)]
mod tests;
mod value;

use super::{Expr, ExprValue};
use crate::sort::Sort;
use std::collections::BTreeMap;
use std::sync::Arc;
use value::Equality;

const MAX_WORK: usize = 65_536;
const MAX_OUTPUT: usize = 65_536;
const MAX_NAME_BYTES: usize = 16_384;
const MAX_DEPTH: usize = 64;

#[derive(Clone, Copy, PartialEq, Eq)]
enum ScalarSort {
    Bool,
    BitVec(u32),
}

impl ScalarSort {
    fn from_sort(sort: &Sort) -> Option<Self> {
        if sort.is_bool() {
            Some(Self::Bool)
        } else {
            sort.bitvec_width()
                .filter(|width| *width > 0)
                .map(Self::BitVec)
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum VariableSort {
    Scalar(ScalarSort),
    Array { index: u32, element: ScalarSort },
}

struct Budget<'a> {
    work_left: usize,
    output_left: usize,
    variables: BTreeMap<&'a str, VariableSort>,
}

impl<'a> Budget<'a> {
    fn new() -> Self {
        Self {
            work_left: MAX_WORK,
            output_left: MAX_OUTPUT,
            variables: BTreeMap::new(),
        }
    }

    fn work(&mut self, count: usize) -> Option<()> {
        self.work_left = self.work_left.checked_sub(count)?;
        Some(())
    }

    fn name(&mut self, name: &str) -> Option<()> {
        if name.len() > MAX_NAME_BYTES {
            return None;
        }
        self.work(name.len().checked_add(1)?)
    }

    fn output(&mut self, count: usize) -> Option<()> {
        self.output_left = self.output_left.checked_sub(count)?;
        self.work(count)
    }

    fn variable(&mut self, name: &'a str, sort: VariableSort) -> Option<()> {
        // Charge name bytes before registration. Keys are borrowed, and sorts
        // are shallow signatures: no recursive Sort or Expr equality. This is
        // an admission bound, not an exact meter for BTreeMap comparisons.
        self.name(name)?;
        if let Some(previous) = self.variables.get(name) {
            if *previous != sort {
                return None;
            }
        } else {
            self.variables.insert(name, sort);
        }
        Some(())
    }
}

/// Charge every scheduled edge before reserving, including shared DAG edges.
fn children<'a>(
    stack: &mut Vec<(&'a Expr, usize)>,
    args: &'a [Expr],
    depth: usize,
    budget: &mut Budget<'_>,
) -> Option<()> {
    if depth >= MAX_DEPTH {
        return None;
    }
    budget.work(args.len())?;
    stack.try_reserve(args.len()).ok()?;
    stack.extend(args.iter().rev().map(|arg| (arg, depth + 1)));
    Some(())
}

struct GuardedEquality<'a> {
    lower: u128,
    upper: u128,
    equality: Equality<'a>,
}

pub(super) fn eliminate<'a>(body: &'a Expr, binder: &'a str, sort: &Sort) -> Option<Expr> {
    let width @ 1..=64 = sort.bitvec_width()? else {
        return None;
    };
    let mut budget = Budget::new();
    budget.variable(binder, VariableSort::Scalar(ScalarSort::BitVec(width)))?;
    budget.work(1)?;
    let mut pending = Vec::new();
    pending.try_reserve_exact(1).ok()?;
    pending.push((body, 0));
    let mut records = Vec::new();
    let mut count = 0usize;
    while let Some((node, depth)) = pending.pop() {
        if !node.sort().is_bool() {
            return None;
        }
        match node.value() {
            ExprValue::And(args) if !args.is_empty() => {
                children(&mut pending, args, depth, &mut budget)?;
            }
            ExprValue::Implies(guard, consequent) => {
                let (lower, upper) = guard::support(guard, binder, width, &mut budget)?;
                // Empty support cannot hide malformed or unsupported terms.
                let equality = Equality::parse(consequent, binder, width, &mut budget)?;
                let instances = usize::try_from(upper.checked_sub(lower)?).ok()?;
                budget.output(instances.checked_mul(equality.output_cost()?)?)?;
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
    emit(records, count, width)
}

fn emit(records: Vec<GuardedEquality<'_>>, count: usize, width: u32) -> Option<Expr> {
    let mut output = Vec::new();
    output.try_reserve_exact(count).ok()?;
    for record in records {
        for index in record.lower..record.upper {
            output.push(record.equality.instantiate(index, width));
        }
    }
    Some(Expr {
        sort: Sort::bool(),
        value: Arc::new(if output.is_empty() {
            ExprValue::BoolConst(true)
        } else {
            ExprValue::And(output)
        }),
    })
}
