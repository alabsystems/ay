// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Authenticate emitted source/hint application metadata against declarations.

use super::*;
use crate::quantified::records::{sort_bytes, Registry};
use crate::ChcExpr;

pub(crate) fn expression_sort(
    problem: &QuantifiedChcProblem,
    registry: &Registry,
    expression: &ChcExpr,
    control: &SourceControl<'_>,
) -> Option<ChcSort> {
    typed(problem, registry, expression, control, 0)
}

fn typed(
    problem: &QuantifiedChcProblem,
    registry: &Registry,
    expression: &ChcExpr,
    control: &SourceControl<'_>,
    depth: usize,
) -> Option<ChcSort> {
    control.charge(1)?;
    if depth > 128 {
        return None;
    }
    let result = match expression {
        ChcExpr::Bool(_) => ChcSort::Bool,
        ChcExpr::BitVec(value, width) => {
            if !(1..=crate::MAX_BITVECTOR_WIDTH).contains(width)
                || (*width < 128 && *value >= (1u128 << width))
            {
                return None;
            }
            ChcSort::BitVec(*width)
        }
        ChcExpr::Var(var) => {
            lookup_cost(&problem.functions, &var.name, control)?;
            if problem.functions.contains(&var.name) {
                return None;
            }
            checked_sort(&var.sort, registry, control)?;
            var.sort.clone()
        }
        ChcExpr::ConstArray(key, value) => {
            checked_sort(key, registry, control)?;
            ChcSort::Array(
                Box::new(key.clone()),
                Box::new(typed(problem, registry, value, control, depth + 1)?),
            )
        }
        ChcExpr::Op(_, args) | ChcExpr::FuncApp(_, _, args) => {
            control.charge(args.len())?;
            control.bytes(args.len().checked_mul(std::mem::size_of::<ChcSort>())?)?;
            let mut sorts = Vec::new();
            sorts.try_reserve_exact(args.len()).ok()?;
            for arg in args {
                sorts.push(typed(problem, registry, arg, control, depth + 1)?);
            }
            match expression {
                ChcExpr::Op(op, _) => crate::pdr::validate_qf_operation(*op, &sorts).ok()?,
                ChcExpr::FuncApp(name, recorded, _) => {
                    lookup_cost(&problem.functions, name, control)?;
                    checked_sort(recorded, registry, control)?;
                    if problem.functions.contains(name) {
                        application(&problem.functions, name, &sorts, recorded, control)?
                    } else {
                        let actual = registry.application(name, &sorts).ok()?;
                        if &actual != recorded {
                            return None;
                        }
                        actual
                    }
                }
                _ => return None,
            }
        }
        _ => return None,
    };
    checked_sort(&result, registry, control)?;
    Some(result)
}

fn checked_sort(sort: &ChcSort, registry: &Registry, control: &SourceControl<'_>) -> Option<()> {
    control.bytes(sort_bytes(sort)?)?;
    registry.validate_sort(sort).ok()?;
    control.poll()
}
