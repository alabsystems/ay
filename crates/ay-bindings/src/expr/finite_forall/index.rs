// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! One translated read index, preserving the source BV operation modulo its width.

use super::{guard::is_binder, Budget, Expr, ExprValue, ScalarSort, VariableSort};
use num_bigint::Sign;
use std::sync::Arc;

enum Operation {
    Add,
    Subtract,
}

enum BinderSide {
    Left,
    Right,
}

pub(super) struct ReadIndex<'a>(IndexKind<'a>);

enum IndexKind<'a> {
    Direct,
    Translated {
        operation: Operation,
        binder_side: BinderSide,
        offset: &'a Expr,
    },
}

impl<'a> ReadIndex<'a> {
    pub(super) fn parse(
        node: &'a Expr,
        binder: &str,
        width: u32,
        budget: &mut Budget<'a>,
    ) -> Option<Self> {
        // Keep the pre-existing direct-index name/metadata checks and charges.
        if is_binder(node, binder, width, budget)? {
            return Some(Self(IndexKind::Direct));
        }
        let (operation, left, right) = match node.value() {
            ExprValue::BvAdd(left, right) => (Operation::Add, left, right),
            ExprValue::BvSub(left, right) => (Operation::Subtract, left, right),
            _ => return None,
        };
        if node.sort().bitvec_width() != Some(width) {
            return None;
        }
        // The outer Select already charged this index node. Charge its two
        // children before inspecting them; do not traverse arbitrary terms.
        budget.work(2)?;
        let left_binder = is_binder(left, binder, width, budget)?;
        let right_binder = is_binder(right, binder, width, budget)?;
        let (binder_side, offset) = match (left_binder, right_binder) {
            (true, false) => (BinderSide::Left, right),
            (false, true) => (BinderSide::Right, left),
            _ => return None,
        };
        validate_offset(offset, binder, width, budget)?;
        Some(Self(IndexKind::Translated {
            operation,
            binder_side,
            offset,
        }))
    }

    pub(super) fn extra_output_cost(&self) -> usize {
        match &self.0 {
            IndexKind::Direct => 0,
            IndexKind::Translated { .. } => 3,
        }
    }

    pub(super) fn instantiate(&self, ground_index: &Expr) -> Expr {
        let IndexKind::Translated {
            operation,
            binder_side,
            offset,
        } = &self.0
        else {
            return ground_index.clone();
        };
        let (left, right) = match binder_side {
            BinderSide::Left => (ground_index.clone(), (*offset).clone()),
            BinderSide::Right => ((*offset).clone(), ground_index.clone()),
        };
        Expr {
            sort: ground_index.sort().clone(),
            value: Arc::new(match operation {
                Operation::Add => ExprValue::BvAdd(left, right),
                Operation::Subtract => ExprValue::BvSub(left, right),
            }),
        }
    }
}

fn validate_offset<'a>(
    offset: &'a Expr,
    binder: &str,
    width: u32,
    budget: &mut Budget<'a>,
) -> Option<()> {
    if offset.sort().bitvec_width() != Some(width) {
        return None;
    }
    match offset.value() {
        ExprValue::Var { name } if name != binder => {
            // The shared registry also sees array/fill names and other reads,
            // including records whose guard has empty support.
            budget.variable(name, VariableSort::Scalar(ScalarSort::BitVec(width)))
        }
        ExprValue::BitVecConst {
            value,
            width: literal_width,
        } if *literal_width == width
            && value.sign() != Sign::Minus
            && value.bits() <= u64::from(width) =>
        {
            // Keep the canonical source literal behind its Arc; no width-sized
            // arithmetic, clamping, or conversion to a host-sized index.
            Some(())
        }
        _ => None,
    }
}
