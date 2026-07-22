// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::sync::Arc;

use crate::{ChcExpr, ChcOp, ChcSort};

pub(super) fn infer_bv_width(expr: &ChcExpr) -> Option<u32> {
    match expr {
        ChcExpr::BitVec(_, width) => Some(*width),
        ChcExpr::Var(var) => match &var.sort {
            ChcSort::BitVec(width) => Some(*width),
            _ => None,
        },
        ChcExpr::Op(op, args) if is_bv_op(op) => {
            // For comparisons that return 1-bit results, infer width from
            // operands, not the result (which is always 1).
            if is_bv_comparison(op) {
                return Some(1);
            }
            // Try first arg, then second arg (for concat, the first may be
            // the high part; for most ops the first arg carries the width).
            args.first()
                .and_then(|arg| infer_bv_width(arg))
                .or_else(|| args.get(1).and_then(|arg| infer_bv_width(arg)))
        }
        // ITE on BV: infer width from then/else branches.
        ChcExpr::Op(op, args) if matches!(op, ChcOp::Ite) && args.len() >= 3 => {
            infer_bv_width(&args[1]).or_else(|| infer_bv_width(&args[2]))
        }
        _ => None,
    }
}

fn is_bv_comparison(op: &ChcOp) -> bool {
    matches!(
        op,
        ChcOp::BvULt
            | ChcOp::BvULe
            | ChcOp::BvUGt
            | ChcOp::BvUGe
            | ChcOp::BvSLt
            | ChcOp::BvSLe
            | ChcOp::BvSGt
            | ChcOp::BvSGe
    )
}

pub(super) fn infer_result_width(op: &ChcOp, args: &[Arc<ChcExpr>]) -> Option<u32> {
    match op {
        ChcOp::BvExtract(hi, lo) => Some(hi - lo + 1),
        ChcOp::BvComp => Some(1),
        ChcOp::BvConcat => Some(infer_bv_width(&args[0])? + infer_bv_width(&args[1])?),
        ChcOp::BvZeroExtend(extra) | ChcOp::BvSignExtend(extra) => {
            Some(infer_bv_width(&args[0])? + extra)
        }
        ChcOp::BvRepeat(times) => Some(infer_bv_width(&args[0])? * times),
        // Comparisons always produce 1-bit result.
        _ if is_bv_comparison(op) => Some(1),
        _ => args
            .first()
            .and_then(|arg| infer_bv_width(arg))
            .or_else(|| args.get(1).and_then(|arg| infer_bv_width(arg))),
    }
}

pub(super) fn has_bv_operand(expr: &ChcExpr) -> bool {
    match expr {
        ChcExpr::BitVec(_, _) => true,
        ChcExpr::Var(var) => matches!(&var.sort, ChcSort::BitVec(_)),
        ChcExpr::Op(op, args) => is_bv_op(op) || args.iter().any(|arg| has_bv_operand(arg)),
        _ => false,
    }
}

/// Check whether `expr_to_bits` can correctly decompose this expression.
///
/// Returns false for expressions containing operations that `expr_to_bits`
/// and `bitblast_op` don't handle (Select, Store, Ite, etc.), which would
/// silently produce all-zero bit vectors and corrupt equality/comparison
/// results. When this returns false, callers should fall through to the
/// generic `bitblast_expr` handler instead of attempting bit-level decomposition.
pub(super) fn can_bitblast_to_bits(expr: &ChcExpr) -> bool {
    match expr {
        ChcExpr::BitVec(_, _) | ChcExpr::Bool(_) | ChcExpr::Int(_) => true,
        ChcExpr::Var(var) => matches!(&var.sort, ChcSort::BitVec(_)),
        ChcExpr::Op(op, args) => {
            if is_bv_op(op) {
                args.iter().all(|arg| can_bitblast_to_bits(arg))
            } else if matches!(op, ChcOp::Ite) && args.len() >= 3 {
                // ITE on BV: condition can be anything (bitblast_expr handles it),
                // but branches must be bitblastable.
                can_bitblast_to_bits(&args[1]) && can_bitblast_to_bits(&args[2])
            } else {
                // Select, Store, and other non-BV ops cannot be decomposed
                // into individual bit expressions by expr_to_bits.
                false
            }
        }
        // FuncApp gets unconstrained bits (safe), but other forms (Let,
        // Quantifier, PredicateApp, ConstArray) hit the zeros fallback.
        ChcExpr::FuncApp(_, _, _) => true,
        _ => false,
    }
}

pub(crate) fn is_bv_op(op: &ChcOp) -> bool {
    matches!(
        op,
        ChcOp::BvAdd
            | ChcOp::BvSub
            | ChcOp::BvMul
            | ChcOp::BvAnd
            | ChcOp::BvOr
            | ChcOp::BvXor
            | ChcOp::BvNot
            | ChcOp::BvNeg
            | ChcOp::BvShl
            | ChcOp::BvLShr
            | ChcOp::BvAShr
            | ChcOp::BvUDiv
            | ChcOp::BvURem
            | ChcOp::BvSDiv
            | ChcOp::BvSRem
            | ChcOp::BvSMod
            | ChcOp::BvNand
            | ChcOp::BvNor
            | ChcOp::BvXnor
            | ChcOp::BvConcat
            | ChcOp::BvComp
            | ChcOp::BvExtract(_, _)
            | ChcOp::BvZeroExtend(_)
            | ChcOp::BvSignExtend(_)
            | ChcOp::BvRotateLeft(_)
            | ChcOp::BvRotateRight(_)
            | ChcOp::BvRepeat(_)
            | ChcOp::BvULt
            | ChcOp::BvULe
            | ChcOp::BvUGt
            | ChcOp::BvUGe
            | ChcOp::BvSLt
            | ChcOp::BvSLe
            | ChcOp::BvSGt
            | ChcOp::BvSGe
    )
}
