// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::{guard::is_binder, Budget};
use crate::{ChcExpr, ChcOp, ChcSort, MAX_BITVECTOR_WIDTH};
use std::sync::Arc;

#[derive(Clone, Copy, PartialEq, Eq)]
enum ScalarSort {
    Bool,
    BitVec(u32),
}

impl ScalarSort {
    fn from_sort(sort: &ChcSort) -> Option<Self> {
        match sort {
            ChcSort::Bool => Some(Self::Bool),
            ChcSort::BitVec(width) if (1..=MAX_BITVECTOR_WIDTH).contains(width) => {
                Some(Self::BitVec(*width))
            }
            // No recursive sort equality/clone, even for malformed raw values.
            _ => None,
        }
    }
}

enum Value<'a> {
    Read(&'a Arc<ChcExpr>),
    Scalar(&'a Arc<ChcExpr>),
}

impl<'a> Value<'a> {
    fn parse(
        node: &'a Arc<ChcExpr>,
        binder: &str,
        width: u32,
        budget: &mut Budget,
    ) -> Option<(Self, ScalarSort)> {
        budget.work(1)?;
        match node.as_ref() {
            ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
                budget.work(2)?;
                if !is_binder(&args[1], binder, width, budget)? {
                    return None;
                }
                let ChcExpr::Var(var) = args[0].as_ref() else {
                    return None;
                };
                budget.name(&var.name)?;
                let ChcSort::Array(key, element) = &var.sort else {
                    return None;
                };
                if var.name == binder || !matches!(key.as_ref(), ChcSort::BitVec(w) if *w == width)
                {
                    return None;
                }
                Some((Self::Read(&args[0]), ScalarSort::from_sort(element)?))
            }
            ChcExpr::Var(var) => {
                budget.name(&var.name)?;
                if var.name == binder {
                    return None;
                }
                Some((Self::Scalar(node), ScalarSort::from_sort(&var.sort)?))
            }
            ChcExpr::Bool(_) => Some((Self::Scalar(node), ScalarSort::Bool)),
            ChcExpr::BitVec(value, width) => {
                if *width == 0
                    || *width > MAX_BITVECTOR_WIDTH
                    || (*width < 128 && *value >= (1u128 << width))
                {
                    return None;
                }
                Some((Self::Scalar(node), ScalarSort::BitVec(*width)))
            }
            _ => None,
        }
    }

    fn instantiate(&self, index: &Arc<ChcExpr>) -> Option<Arc<ChcExpr>> {
        match self {
            Self::Read(array) => binary(ChcOp::Select, Arc::clone(array), Arc::clone(index)),
            Self::Scalar(value) => Some(Arc::clone(value)),
        }
    }
}

pub(super) struct Equality<'a> {
    left: Value<'a>,
    right: Value<'a>,
}

impl<'a> Equality<'a> {
    pub(super) fn parse(
        node: &'a ChcExpr,
        binder: &str,
        width: u32,
        budget: &mut Budget,
    ) -> Option<Self> {
        budget.work(1)?;
        let ChcExpr::Op(ChcOp::Eq, args) = node else {
            return None;
        };
        let [left, right] = args.as_slice() else {
            return None;
        };
        let (left, left_sort) = Value::parse(left, binder, width, budget)?;
        let (right, right_sort) = Value::parse(right, binder, width, budget)?;
        if left_sort != right_sort
            || !matches!((&left, &right), (Value::Read(_), _) | (_, Value::Read(_)))
        {
            return None;
        }
        Some(Self { left, right })
    }

    pub(super) fn output_cost(&self) -> usize {
        // Index, equality and parent slot, plus at most two three-cell reads.
        // Includes the equality's two argument cells; scalar roots are shared.
        11
    }

    pub(super) fn instantiate(&self, index: u128, width: u32) -> Option<Arc<ChcExpr>> {
        let index = Arc::new(ChcExpr::BitVec(index, width));
        binary(
            ChcOp::Eq,
            self.left.instantiate(&index)?,
            self.right.instantiate(&index)?,
        )
    }
}

fn binary(op: ChcOp, left: Arc<ChcExpr>, right: Arc<ChcExpr>) -> Option<Arc<ChcExpr>> {
    let mut args = Vec::new();
    args.try_reserve_exact(2).ok()?;
    args.push(left);
    args.push(right);
    Some(Arc::new(ChcExpr::Op(op, args)))
}
