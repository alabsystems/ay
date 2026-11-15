// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Iterative exact reconstruction of an admitted, typed scalar hint.
//! No recursion, simplification, array abstraction or certificate copying.
//! Occurrence pricing intentionally bounds tree expansion of shared DAGs.

use super::super::admission::{MAX_ARITY, MAX_DEPTH, MAX_NODES};
use super::Binding;
use crate::{ChcExpr, ChcOp};
use std::sync::Arc;

const MAX_FRONTIER: usize = MAX_DEPTH * (MAX_ARITY + 1);

enum Work<'a> {
    Visit(&'a ChcExpr, usize),
    Finish(ChcOp, usize),
}

pub(super) fn expression(
    root: &ChcExpr,
    bindings: &[Binding],
    poll: &mut dyn FnMut() -> bool,
) -> Option<ChcExpr> {
    if !poll() {
        return None;
    }
    let mut pending = Vec::new();
    pending.try_reserve_exact(MAX_FRONTIER).ok()?;
    if !poll() {
        return None;
    }
    let mut results = Vec::new();
    results.try_reserve_exact(MAX_NODES).ok()?;
    if !poll() {
        return None;
    }
    pending.push(Work::Visit(root, 1));
    let mut visited = 0usize;
    while let Some(work) = pending.pop() {
        if !poll() {
            return None;
        }
        let result = match work {
            Work::Visit(node, depth) => {
                visited = visited.checked_add(1)?;
                if depth > MAX_DEPTH || visited > MAX_NODES {
                    return None;
                }
                match node {
                    ChcExpr::Bool(value) => ChcExpr::Bool(*value),
                    ChcExpr::Int(value) => ChcExpr::Int(*value),
                    ChcExpr::Real(num, den) => ChcExpr::Real(*num, *den),
                    ChcExpr::BitVec(value, width) => ChcExpr::BitVec(*value, *width),
                    ChcExpr::Var(var) => {
                        let binding = bindings.iter().find(|binding| &binding.original == var)?;
                        ChcExpr::var(binding.reduced.clone())
                    }
                    ChcExpr::Op(op, arguments) => {
                        if matches!(op, ChcOp::Select | ChcOp::Store)
                            || arguments.len() > MAX_ARITY
                            || pending.len().checked_add(arguments.len() + 1)? > MAX_FRONTIER
                        {
                            return None;
                        }
                        pending.push(Work::Finish(*op, arguments.len()));
                        for argument in arguments.iter().rev() {
                            if !poll() {
                                return None;
                            }
                            pending.push(Work::Visit(argument.as_ref(), depth.checked_add(1)?));
                        }
                        continue;
                    }
                    _ => return None,
                }
            }
            Work::Finish(op, arity) => {
                let start = results.len().checked_sub(arity)?;
                let mut arguments = Vec::new();
                arguments.try_reserve_exact(arity).ok()?;
                for argument in results.drain(start..) {
                    if !poll() {
                        return None;
                    }
                    arguments.push(Arc::new(argument));
                }
                ChcExpr::Op(op, arguments)
            }
        };
        if !poll() || results.len() >= MAX_NODES {
            return None;
        }
        results.push(result);
    }
    if results.len() != 1 || !poll() {
        return None;
    }
    results.pop()
}
