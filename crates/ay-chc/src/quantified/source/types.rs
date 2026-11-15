// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact source signatures after the complete borrowed occurrence/depth scan.
//! Computed wide results spend the same ledger as declarations and payloads;
//! tiny indexed syntax must not bypass the aggregate width allowance.

use super::*;

pub(super) fn expression_sort(
    expr: &ChcExpr,
    registry: &Registry,
    functions: &Functions,
    budget: &mut Budget,
) -> ChcResult<ChcSort> {
    let sort = match expr {
        ChcExpr::Bool(_) => ChcSort::Bool,
        ChcExpr::BitVec(_, width) => ChcSort::BitVec(*width),
        ChcExpr::Var(var) => var.sort.clone(),
        ChcExpr::ConstArray(key, value) => ChcSort::Array(
            Box::new(key.clone()),
            Box::new(expression_sort(value, registry, functions, budget)?),
        ),
        ChcExpr::Op(op, args) => {
            let sorts = args
                .iter()
                .map(|arg| expression_sort(arg, registry, functions, budget))
                .collect::<ChcResult<Vec<_>>>()?;
            let result = crate::pdr::validate_qf_operation(*op, &sorts)?;
            // This is a new computed sort, not necessarily a declared wide
            // variable or literal visited by the original borrowed scan.
            // Charge before formatting/native parsing can consume the result.
            budget.sort(&result, registry, 0)?;
            result
        }
        ChcExpr::FuncApp(name, recorded, args) => {
            let sorts = args
                .iter()
                .map(|arg| expression_sort(arg, registry, functions, budget))
                .collect::<ChcResult<Vec<_>>>()?;
            let actual = if functions.contains(name) {
                functions.application(name, &sorts)?
            } else {
                registry.application(name, &sorts)?
            };
            if &actual != recorded {
                return Err(invalid("declared operation result sort mismatch"));
            }
            actual
        }
        _ => return Err(invalid("unsupported expression family")),
    };
    registry.validate_sort(&sort)?;
    Ok(sort)
}
