// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Authenticate original actuals without rewriting constructor/selector or
/// ordinary function terms. Both namespaces use the immutable source schema.
pub(in super::super) fn authenticate(
    expr: &ChcExpr,
    registry: &Registry,
    functions: &RetainedFunctions,
    control: &SourceControl<'_>,
    depth: usize,
) -> Option<ChcSort> {
    control.charge(1)?;
    if depth > 64 {
        return None;
    }
    let result = match expr {
        ChcExpr::Bool(_) => ChcSort::Bool,
        ChcExpr::BitVec(value, width) if valid_literal(*value, *width) => {
            control.bytes(sort_bytes(&ChcSort::BitVec(*width))?)?;
            ChcSort::BitVec(*width)
        }
        ChcExpr::Var(var) => {
            if functions.contains(&var.name, control)? {
                return None;
            }
            registry.validate_sort(&var.sort).ok()?;
            control.bytes(var.name.len().checked_add(sort_bytes(&var.sort)?)?)?;
            var.sort.clone()
        }
        ChcExpr::Op(_, args) | ChcExpr::FuncApp(_, _, args) => {
            control.charge(args.len())?;
            let mut sorts = Vec::new();
            sorts.try_reserve_exact(args.len()).ok()?;
            for arg in args {
                sorts.push(authenticate(arg, registry, functions, control, depth + 1)?);
            }
            match expr {
                ChcExpr::Op(op, _) => operation_sort(*op, &sorts, registry, control)?,
                ChcExpr::FuncApp(name, claimed, _) => {
                    registry.validate_sort(claimed).ok()?;
                    control.bytes(name.len().checked_add(sort_bytes(claimed)?)?)?;
                    if functions.contains(name, control)? {
                        functions.application(name, &sorts, claimed, control)?
                    } else {
                        let actual = registry.application(name, &sorts).ok()?;
                        if &actual != claimed {
                            return None;
                        }
                        actual
                    }
                }
                _ => return None,
            }
        }
        ChcExpr::ConstArray(key, value)
            if matches!(key, ChcSort::BitVec(1..=crate::MAX_BITVECTOR_WIDTH)) =>
        {
            control.bytes(sort_bytes(key)?)?;
            ChcSort::Array(
                Box::new(key.clone()),
                Box::new(authenticate(
                    value,
                    registry,
                    functions,
                    control,
                    depth + 1,
                )?),
            )
        }
        _ => return None,
    };
    registry.validate_sort(&result).ok()?;
    control.poll()?;
    Some(result)
}
