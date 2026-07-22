// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expression utilities used by the PDR solver.

use crate::{ChcExpr, ChcOp};
use ay_core::kani_compat::DetHashSet as FxHashSet;

/// Extract integer constants that are compared against a variable in equality tests.
///
/// Scans an expression recursively for patterns `(= var k)` or `(= k var)` where
/// `var` has the given name and `k` is an integer constant. This is used to discover
/// the mode values that should form case-split branches.
///
/// For `dillig12_m_000.smt2`, scanning the transition clauses with var_name="J" would
/// return `{1}` because the ITE condition is `(= J 1)`.
pub(super) fn extract_equality_constants(expr: &ChcExpr, var_name: &str) -> FxHashSet<i128> {
    let mut constants = FxHashSet::default();
    extract_equality_constants_rec(expr, var_name, &mut constants);
    constants
}

fn extract_equality_constants_rec(expr: &ChcExpr, var_name: &str, out: &mut FxHashSet<i128>) {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            // Check if this is (= var k) or (= k var)
            let (left, right) = (&*args[0], &*args[1]);
            match (left, right) {
                (ChcExpr::Var(v), ChcExpr::Int(k)) if v.name == var_name => {
                    out.insert(*k);
                }
                (ChcExpr::Int(k), ChcExpr::Var(v)) if v.name == var_name => {
                    out.insert(*k);
                }
                _ => {}
            }
            // Still recurse to find nested equalities (e.g., in ITE conditions)
            for arg in args {
                extract_equality_constants_rec(arg, var_name, out);
            }
        }
        ChcExpr::Op(_, args) => {
            for arg in args {
                extract_equality_constants_rec(arg, var_name, out);
            }
        }
        ChcExpr::PredicateApp(_, _, args) => {
            for arg in args {
                extract_equality_constants_rec(arg, var_name, out);
            }
        }
        ChcExpr::FuncApp(_, _, args) => {
            for arg in args {
                extract_equality_constants_rec(arg, var_name, out);
            }
        }
        ChcExpr::ConstArray(_ks, inner) => {
            extract_equality_constants_rec(inner, var_name, out);
        }
        ChcExpr::Bool(_)
        | ChcExpr::Int(_)
        | ChcExpr::BitVec(_, _)
        | ChcExpr::Real(_, _)
        | ChcExpr::Var(_) => {}
        ChcExpr::ConstArrayMarker(_) | ChcExpr::IsTesterMarker(_) => {}
    });
}

#[cfg(test)]
#[path = "expr_utils_tests.rs"]
mod tests;
