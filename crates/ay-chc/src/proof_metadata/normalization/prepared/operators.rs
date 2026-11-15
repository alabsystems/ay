// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact derived-Debug spelling, with fixed tags and paid u32 parameters.

use super::{bytes::Bytes, spelling, Control, QueryError};
use crate::ChcOp;

pub(super) fn write<C: Control>(
    out: &mut Bytes,
    op: ChcOp,
    control: &mut C,
) -> Result<(), QueryError> {
    control.offer(2, 0)?;
    let name = tag(op);
    out.text(name, control)?;
    match op {
        ChcOp::BvExtract(high, low) => {
            out.text("(", control)?;
            spelling::unsigned(out, u128::from(high), control)?;
            out.text(", ", control)?;
            spelling::unsigned(out, u128::from(low), control)?;
            out.text(")", control)
        }
        ChcOp::BvZeroExtend(n)
        | ChcOp::BvSignExtend(n)
        | ChcOp::BvRotateLeft(n)
        | ChcOp::BvRotateRight(n)
        | ChcOp::BvRepeat(n)
        | ChcOp::Int2Bv(n) => {
            out.text("(", control)?;
            spelling::unsigned(out, u128::from(n), control)?;
            out.text(")", control)
        }
        _ => Ok(()),
    }
}

fn tag(op: ChcOp) -> &'static str {
    match op {
        ChcOp::Not => "Not",
        ChcOp::And => "And",
        ChcOp::Or => "Or",
        ChcOp::Implies => "Implies",
        ChcOp::Iff => "Iff",
        ChcOp::Add => "Add",
        ChcOp::Sub => "Sub",
        ChcOp::Mul => "Mul",
        ChcOp::Div => "Div",
        ChcOp::Mod => "Mod",
        ChcOp::Neg => "Neg",
        ChcOp::Eq => "Eq",
        ChcOp::Ne => "Ne",
        ChcOp::Lt => "Lt",
        ChcOp::Le => "Le",
        ChcOp::Gt => "Gt",
        ChcOp::Ge => "Ge",
        ChcOp::Ite => "Ite",
        ChcOp::Select => "Select",
        ChcOp::Store => "Store",
        ChcOp::BvAdd => "BvAdd",
        ChcOp::BvSub => "BvSub",
        ChcOp::BvMul => "BvMul",
        ChcOp::BvUDiv => "BvUDiv",
        ChcOp::BvURem => "BvURem",
        ChcOp::BvSDiv => "BvSDiv",
        ChcOp::BvSRem => "BvSRem",
        ChcOp::BvSMod => "BvSMod",
        ChcOp::BvAnd => "BvAnd",
        ChcOp::BvOr => "BvOr",
        ChcOp::BvXor => "BvXor",
        ChcOp::BvNand => "BvNand",
        ChcOp::BvNor => "BvNor",
        ChcOp::BvXnor => "BvXnor",
        ChcOp::BvNot => "BvNot",
        ChcOp::BvNeg => "BvNeg",
        ChcOp::BvShl => "BvShl",
        ChcOp::BvLShr => "BvLShr",
        ChcOp::BvAShr => "BvAShr",
        ChcOp::BvULt => "BvULt",
        ChcOp::BvULe => "BvULe",
        ChcOp::BvUGt => "BvUGt",
        ChcOp::BvUGe => "BvUGe",
        ChcOp::BvSLt => "BvSLt",
        ChcOp::BvSLe => "BvSLe",
        ChcOp::BvSGt => "BvSGt",
        ChcOp::BvSGe => "BvSGe",
        ChcOp::BvComp => "BvComp",
        ChcOp::BvConcat => "BvConcat",
        ChcOp::Bv2Nat => "Bv2Nat",
        ChcOp::BvExtract(_, _) => "BvExtract",
        ChcOp::BvZeroExtend(_) => "BvZeroExtend",
        ChcOp::BvSignExtend(_) => "BvSignExtend",
        ChcOp::BvRotateLeft(_) => "BvRotateLeft",
        ChcOp::BvRotateRight(_) => "BvRotateRight",
        ChcOp::BvRepeat(_) => "BvRepeat",
        ChcOp::Int2Bv(_) => "Int2Bv",
    }
}
