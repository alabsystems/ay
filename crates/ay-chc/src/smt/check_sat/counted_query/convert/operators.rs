// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_core::term::CountedBuiltin;

use super::{Error, Result};
use crate::ChcOp;

/// Exact typed vocabulary correspondence. Arity was checked for every source
/// arm by the census and is independently checked by the raw core builder.
pub(super) fn builtin(op: ChcOp) -> Result<CountedBuiltin> {
    use CountedBuiltin as B;
    Ok(match op {
        ChcOp::Not => B::Not,
        ChcOp::And => B::And,
        ChcOp::Or => B::Or,
        ChcOp::Implies => B::Implies,
        ChcOp::Iff => B::Iff,
        ChcOp::Eq => B::Eq,
        ChcOp::Ne => B::Distinct,
        ChcOp::Ite => B::Ite,
        ChcOp::Select => B::Select,
        ChcOp::Store => B::Store,
        ChcOp::BvAdd => B::BvAdd,
        ChcOp::BvSub => B::BvSub,
        ChcOp::BvMul => B::BvMul,
        ChcOp::BvUDiv => B::BvUDiv,
        ChcOp::BvURem => B::BvURem,
        ChcOp::BvSDiv => B::BvSDiv,
        ChcOp::BvSRem => B::BvSRem,
        ChcOp::BvSMod => B::BvSMod,
        ChcOp::BvAnd => B::BvAnd,
        ChcOp::BvOr => B::BvOr,
        ChcOp::BvXor => B::BvXor,
        ChcOp::BvNand => B::BvNand,
        ChcOp::BvNor => B::BvNor,
        ChcOp::BvXnor => B::BvXnor,
        ChcOp::BvShl => B::BvShl,
        ChcOp::BvLShr => B::BvLShr,
        ChcOp::BvAShr => B::BvAShr,
        ChcOp::BvNot => B::BvNot,
        ChcOp::BvNeg => B::BvNeg,
        ChcOp::BvULt => B::BvULt,
        ChcOp::BvULe => B::BvULe,
        ChcOp::BvUGt => B::BvUGt,
        ChcOp::BvUGe => B::BvUGe,
        ChcOp::BvSLt => B::BvSLt,
        ChcOp::BvSLe => B::BvSLe,
        ChcOp::BvSGt => B::BvSGt,
        ChcOp::BvSGe => B::BvSGe,
        ChcOp::BvComp => B::BvComp,
        ChcOp::BvConcat => B::BvConcat,
        ChcOp::BvExtract(high, low) => B::BvExtract(high, low),
        ChcOp::BvZeroExtend(extra) => B::BvZeroExtend(extra),
        ChcOp::BvSignExtend(extra) => B::BvSignExtend(extra),
        ChcOp::BvRotateLeft(count) => B::BvRotateLeft(count),
        ChcOp::BvRotateRight(count) => B::BvRotateRight(count),
        ChcOp::BvRepeat(count) => B::BvRepeat(count),
        _ => return Err(Error::Unsupported),
    })
}
