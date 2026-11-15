// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact definitional specialization, never finite premise instantiation.
//!
//! Extensional arrays satisfy forall i. select(w,i)=t(i) iff
//! w=lambda i.t(i). This is the array beta/extensionality rule, used by Z3's
//! array rewriter (Z3Prover/z3, src/ast/rewriter/array_rewriter.cpp).
//! The source has already authenticated lexical variables, sorts and matrices.
//! Direct self-reference keeps the original route; this does not unfold
//! other definitions, including mutually dependent ones.

use super::{census, refused, Output, Result, SourceControl, UniversalPremise};
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};

pub(super) struct Definition<'a> {
    array: &'a ChcVar,
    binder: &'a ChcVar,
    body: &'a ChcExpr,
}

pub(super) fn recognize<'a>(
    premise: &'a UniversalPremise,
    control: &SourceControl<'_>,
) -> Result<Option<Definition<'a>>> {
    control.charge(1).ok_or_else(refused)?;
    if premise.binder_count() != 1 {
        return Ok(None);
    }
    let ChcExpr::Op(ChcOp::Eq, sides) = premise.matrix() else {
        return Ok(None);
    };
    if sides.len() != 2 {
        return Ok(None);
    }
    for (read, body) in [
        (sides[0].as_ref(), sides[1].as_ref()),
        (sides[1].as_ref(), sides[0].as_ref()),
    ] {
        let ChcExpr::Op(ChcOp::Select, args) = read else {
            continue;
        };
        let [array, index] = args.as_slice() else {
            continue;
        };
        let (ChcExpr::Var(array), ChcExpr::Var(index)) = (array.as_ref(), index.as_ref()) else {
            continue;
        };
        let binder = premise.binder();
        let ChcSort::Array(key, cell) = &array.sort else {
            continue;
        };
        if index != binder
            || array.name == binder.name
            || key.as_ref() != &binder.sort
            || !matches!(cell.as_ref(), ChcSort::Bool | ChcSort::BitVec(_))
        {
            continue;
        }
        // Meter the complete body before sort computation or scratch creation.
        census::expression_cost(body, control)?;
        if body.sort() != **cell || mentions(body, &array.name, control)? {
            continue;
        }
        return Ok(Some(Definition {
            array,
            binder,
            body,
        }));
    }
    Ok(None)
}

fn mentions(root: &ChcExpr, name: &str, control: &SourceControl<'_>) -> Result<bool> {
    let item_bytes = std::mem::size_of::<(&ChcExpr, usize)>();
    control.bytes(item_bytes).ok_or_else(refused)?;
    let mut stack = Vec::new();
    stack.try_reserve_exact(1).map_err(|_| refused())?;
    stack.push((root, 0usize));
    while let Some((node, depth)) = stack.pop() {
        control.charge(1).ok_or_else(refused)?;
        if depth > 64 {
            return Err(refused());
        }
        match node {
            ChcExpr::Var(variable) => {
                control.charge(variable.name.len()).ok_or_else(refused)?;
                if variable.name == name {
                    return Ok(true);
                }
            }
            ChcExpr::Op(_, args) | ChcExpr::FuncApp(_, _, args) => {
                control
                    .bytes(args.len().checked_mul(item_bytes).ok_or_else(refused)?)
                    .ok_or_else(refused)?;
                stack.try_reserve(args.len()).map_err(|_| refused())?;
                stack.extend(args.iter().rev().map(|arg| (arg.as_ref(), depth + 1)));
            }
            ChcExpr::ConstArray(_, value) => {
                control.bytes(item_bytes).ok_or_else(refused)?;
                stack.try_reserve(1).map_err(|_| refused())?;
                stack.push((value.as_ref(), depth + 1));
            }
            ChcExpr::Bool(_) | ChcExpr::BitVec(_, _) => {}
            _ => return Ok(true),
        }
    }
    control.poll().ok_or_else(refused)?;
    Ok(false)
}

impl Definition<'_> {
    pub(super) fn write(&self, output: &mut Output<'_, '_>) -> Result<()> {
        output.push("(= ")?;
        output.symbol(&self.array.name)?;
        output.push(" (lambda ((")?;
        output.symbol(&self.binder.name)?;
        output.push(" ")?;
        output.sort(&self.binder.sort)?;
        output.push(")) ")?;
        output.expression(self.body)?;
        output.push("))")
    }
}

#[cfg(test)]
mod tests;
