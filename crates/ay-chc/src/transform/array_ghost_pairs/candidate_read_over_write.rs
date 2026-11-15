// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded, exact read-over-write normalization for candidates and read probes.
//!
//! `select(store(a, i, v), j) = ite(i = j, v, select(a, j))`.
//! No branch is simplified away, and all original operands are type checked.
//! Trigger discovery may use this exact view; raw constraints, the original
//! problem, ghost layout, Houdini and certification are unchanged.

use std::borrow::Cow;
use std::sync::Arc;

use crate::expr::MAX_EXPR_RECURSION_DEPTH;
use crate::{ChcExpr, ChcOp, ChcSort};

pub(in crate::transform::array_ghost_pairs) fn normalize<'a>(
    expression: &'a ChcExpr,
    remaining: &mut usize,
    stopped: &mut dyn FnMut() -> bool,
) -> Option<Cow<'a, ChcExpr>> {
    let mut meter = Meter { remaining, stopped };
    if !contains_read_over_write(expression, &mut meter)? {
        return Some(Cow::Borrowed(expression));
    }
    let node = build(expression, 0, &mut meter)?;
    meter.charge(0)?;
    // Every root is freshly allocated; children may share their own Arcs.
    Some(Cow::Owned(Arc::try_unwrap(node.expression).ok()?))
}

struct Meter<'a> {
    remaining: &'a mut usize,
    stopped: &'a mut dyn FnMut() -> bool,
}

impl Meter<'_> {
    fn charge(&mut self, amount: usize) -> Option<()> {
        if (self.stopped)() {
            return None;
        }
        let Some(rest) = self.remaining.checked_sub(amount) else {
            *self.remaining = 0;
            return None;
        };
        *self.remaining = rest;
        Some(())
    }
}

fn contains_read_over_write(expression: &ChcExpr, meter: &mut Meter<'_>) -> Option<bool> {
    let mut stack = vec![(expression, 0usize)];
    let mut found = false;
    while let Some((node, depth)) = stack.pop() {
        meter.charge(1)?;
        if depth >= MAX_EXPR_RECURSION_DEPTH {
            return None;
        }
        match node {
            ChcExpr::Op(op, args) => {
                found |= *op == ChcOp::Select
                    && args
                        .first()
                        .is_some_and(|base| matches!(base.as_ref(), ChcExpr::Op(ChcOp::Store, _)));
                meter.charge(args.len())?;
                stack.extend(args.iter().rev().map(|arg| (arg.as_ref(), depth + 1)));
            }
            ChcExpr::FuncApp(_, _, args) | ChcExpr::PredicateApp(_, _, args) => {
                meter.charge(args.len())?;
                stack.extend(args.iter().rev().map(|arg| (arg.as_ref(), depth + 1)));
            }
            ChcExpr::ConstArray(_, value) => {
                meter.charge(1)?;
                stack.push((value.as_ref(), depth + 1));
            }
            _ => {}
        }
    }
    Some(found)
}

struct Node {
    expression: Arc<ChcExpr>,
    sort: ChcSort,
    // Expanded occurrence weight, not distinct Arc count. Includes name bytes.
    weight: usize,
    height: usize,
    store: Option<Box<[Node; 3]>>,
}

fn scalar_sort(sort: &ChcSort) -> bool {
    matches!(sort, ChcSort::Bool | ChcSort::Int | ChcSort::Real)
        || matches!(sort, ChcSort::BitVec(width) if (1..=crate::MAX_BITVECTOR_WIDTH).contains(width))
}

fn admitted_sort(sort: &ChcSort) -> bool {
    scalar_sort(sort)
        || matches!(sort, ChcSort::Array(key, value)
            if matches!(key.as_ref(), ChcSort::Int | ChcSort::BitVec(1..=64))
                && scalar_sort(value))
}

fn build(expression: &ChcExpr, depth: usize, meter: &mut Meter<'_>) -> Option<Node> {
    meter.charge(1)?;
    if depth >= MAX_EXPR_RECURSION_DEPTH {
        return None;
    }
    crate::expr::maybe_grow_expr_stack(|| {
        if let ChcExpr::Op(op, args) = expression {
            meter.charge(args.len())?;
            let children = args
                .iter()
                .map(|arg| build(arg, depth + 1, meter))
                .collect::<Option<Vec<_>>>()?;
            let references: Vec<_> = children.iter().collect();
            let mut result = operation(*op, &references, meter)?;
            if *op == ChcOp::Store {
                result.store = Some(Box::new(children.try_into().ok()?));
            } else if *op == ChcOp::Select && children[0].store.is_some() {
                result = expand_read(&children[0], &children[1], meter)?;
            }
            return Some(result);
        }
        let (sort, weight) = match expression {
            ChcExpr::Bool(_) => (ChcSort::Bool, 1),
            ChcExpr::Int(_) => (ChcSort::Int, 1),
            ChcExpr::Real(_, denominator) if *denominator > 0 => (ChcSort::Real, 1),
            ChcExpr::BitVec(value, width)
                if (1..=crate::MAX_BITVECTOR_WIDTH).contains(width)
                    && (*width >= u128::BITS || *value < (1u128 << width)) =>
            {
                (ChcSort::BitVec(*width), 1)
            }
            ChcExpr::Var(variable) if admitted_sort(&variable.sort) => {
                let weight = variable.name.len().checked_add(1)?;
                meter.charge(weight)?;
                return Some(Node {
                    expression: Arc::new(expression.clone()),
                    sort: variable.sort.clone(),
                    weight,
                    height: 1,
                    store: None,
                });
            }
            _ => return None,
        };
        meter.charge(weight)?;
        Some(Node {
            expression: Arc::new(expression.clone()),
            sort,
            weight,
            height: 1,
            store: None,
        })
    })
}

fn operation(op: ChcOp, args: &[&Node], meter: &mut Meter<'_>) -> Option<Node> {
    // Prepay the entire expanded result before either metadata or AST vectors
    // are allocated. Reusing an index Arc therefore does not hide duplication.
    let weight = args
        .iter()
        .try_fold(1usize, |sum, arg| sum.checked_add(arg.weight))?;
    meter.charge(weight)?;
    let height = args.iter().map(|arg| arg.height).max().unwrap_or(0) + 1;
    if height >= MAX_EXPR_RECURSION_DEPTH {
        return None;
    }
    let sorts: Vec<_> = args.iter().map(|arg| arg.sort.clone()).collect();
    let sort = crate::pdr::validate_qf_operation(op, &sorts).ok()?;
    if !admitted_sort(&sort) {
        return None;
    }
    // No numeric sort coercion is introduced at the array boundary.
    if matches!(op, ChcOp::Select | ChcOp::Store) {
        let ChcSort::Array(key, value) = &args[0].sort else {
            return None;
        };
        if **key != args[1].sort || (op == ChcOp::Store && **value != args[2].sort) {
            return None;
        }
    }
    Some(Node {
        expression: Arc::new(ChcExpr::Op(
            op,
            args.iter().map(|arg| Arc::clone(&arg.expression)).collect(),
        )),
        sort,
        weight,
        height,
        store: None,
    })
}

fn expand_read(array: &Node, index: &Node, meter: &mut Meter<'_>) -> Option<Node> {
    let mut stores = Vec::new();
    let mut base = array;
    while let Some(store) = base.store.as_deref() {
        meter.charge(1)?;
        stores.push(store);
        base = &store[0];
    }
    // Constant arrays, array-valued ITEs, and opaque producers remain outside
    // candidate admission. Only the existing bare-array ghost identity is used.
    if !matches!(base.expression.as_ref(), ChcExpr::Var(_)) {
        return None;
    }
    let mut read = operation(ChcOp::Select, &[base, index], meter)?;
    for store in stores.into_iter().rev() {
        let condition = operation(ChcOp::Eq, &[&store[1], index], meter)?;
        read = operation(ChcOp::Ite, &[&condition, &store[2], &read], meter)?;
    }
    Some(read)
}

#[cfg(test)]
#[path = "candidate_read_over_write/tests.rs"]
mod tests;
