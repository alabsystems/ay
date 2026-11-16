// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Closed builtin vocabulary: caller text cannot impersonate an operator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CountedBuiltin {
    /// Boolean negation.
    Not,
    /// Boolean conjunction.
    And,
    /// Boolean disjunction.
    Or,
    /// Boolean implication.
    Implies,
    /// Boolean exclusive disjunction.
    Xor,
    /// Boolean equivalence.
    Iff,
    /// Equality of operands with the same sort.
    Eq,
    /// Disequality of operands with the same sort.
    Distinct,
    /// Conditional selection between equally sorted branches.
    Ite,
    /// Array element lookup.
    Select,
    /// Array update.
    Store,
    /// Modular bit-vector addition.
    BvAdd,
    /// Modular bit-vector subtraction.
    BvSub,
    /// Modular bit-vector multiplication.
    BvMul,
    /// Unsigned bit-vector division.
    BvUDiv,
    /// Unsigned bit-vector remainder.
    BvURem,
    /// Signed bit-vector division.
    BvSDiv,
    /// Signed bit-vector remainder.
    BvSRem,
    /// Signed bit-vector modulo.
    BvSMod,
    /// Bitwise conjunction.
    BvAnd,
    /// Bitwise disjunction.
    BvOr,
    /// Bitwise exclusive disjunction.
    BvXor,
    /// Bitwise negated conjunction.
    BvNand,
    /// Bitwise negated disjunction.
    BvNor,
    /// Bitwise negated exclusive disjunction.
    BvXnor,
    /// Bit-vector shift left.
    BvShl,
    /// Logical bit-vector shift right.
    BvLShr,
    /// Arithmetic bit-vector shift right.
    BvAShr,
    /// Bitwise complement.
    BvNot,
    /// Modular bit-vector negation.
    BvNeg,
    /// Unsigned less-than comparison.
    BvULt,
    /// Unsigned less-than-or-equal comparison.
    BvULe,
    /// Unsigned greater-than comparison.
    BvUGt,
    /// Unsigned greater-than-or-equal comparison.
    BvUGe,
    /// Signed less-than comparison.
    BvSLt,
    /// Signed less-than-or-equal comparison.
    BvSLe,
    /// Signed greater-than comparison.
    BvSGt,
    /// Signed greater-than-or-equal comparison.
    BvSGe,
    /// Equality encoded as a one-bit vector.
    BvComp,
    /// Concatenation, with the first operand supplying the high bits.
    BvConcat,
    /// Inclusive high and low extraction indices.
    BvExtract(u32, u32),
    /// Zero extension by the given number of bits.
    BvZeroExtend(u32),
    /// Sign extension by the given number of bits.
    BvSignExtend(u32),
    /// Rotation left by the given number of bits.
    BvRotateLeft(u32),
    /// Rotation right by the given number of bits.
    BvRotateRight(u32),
    /// Concatenation of the given positive number of copies.
    BvRepeat(u32),
}

pub(super) fn infer(
    store: &TermStore,
    op: CountedBuiltin,
    args: &[TermId],
    owner: &dyn TermConstructionAdmission,
) -> Result<Sort> {
    if args.len() <= 3 {
        let mut sorts = [&Sort::Bool; 3];
        for (slot, id) in sorts.iter_mut().zip(args) {
            owner.admit(1, 0)?;
            let entry = store
                .terms
                .get(id.index())
                .ok_or(CountedTermError::InvalidInput)?;
            sorts::visit(&entry.sort, owner, PayloadUse::Inspect)?;
            *slot = &entry.sort;
        }
        return infer_sorts(op, &sorts[..args.len()], owner);
    }
    let mut sorts = Vec::new();
    storage::reserve(&mut sorts, args.len(), owner)?;
    for id in args {
        owner.admit(1, 0)?;
        let entry = store
            .terms
            .get(id.index())
            .ok_or(CountedTermError::InvalidInput)?;
        sorts::visit(&entry.sort, owner, PayloadUse::Inspect)?;
        sorts.push(&entry.sort);
    }
    infer_sorts(op, &sorts, owner)
}

fn infer_sorts(
    op: CountedBuiltin,
    args: &[&Sort],
    owner: &dyn TermConstructionAdmission,
) -> Result<Sort> {
    use CountedBuiltin::{And, Distinct, Eq, Iff, Implies, Ite, Not, Or, Select, Store, Xor};
    match (op, args) {
        (Not, [Sort::Bool]) | (Implies | Xor | Iff, [Sort::Bool, Sort::Bool]) => Ok(Sort::Bool),
        (And | Or, args) if args.len() >= 2 => {
            owner.admit(args.len(), 0)?;
            if args.iter().all(|sort| **sort == Sort::Bool) {
                Ok(Sort::Bool)
            } else {
                Err(CountedTermError::InvalidInput)
            }
        }
        (Eq | Distinct, [left, right]) if sorts::equal(left, right, owner)? => Ok(Sort::Bool),
        (Ite, [Sort::Bool, left, right]) if sorts::equal(left, right, owner)? => {
            sorts::copy(left, owner)
        }
        (Select, [Sort::Array(array), key]) if sorts::equal(&array.index_sort, key, owner)? => {
            sorts::copy(&array.element_sort, owner)
        }
        (Store, [array_sort @ Sort::Array(array), key, value])
            if sorts::equal(&array.index_sort, key, owner)?
                && sorts::equal(&array.element_sort, value, owner)? =>
        {
            sorts::copy(array_sort, owner)
        }
        _ => infer_bv(op, args),
    }
}

fn infer_bv(op: CountedBuiltin, args: &[&Sort]) -> Result<Sort> {
    use CountedBuiltin::{
        BvAShr, BvAdd, BvAnd, BvComp, BvConcat, BvExtract, BvLShr, BvMul, BvNand, BvNeg, BvNor,
        BvNot, BvOr, BvRepeat, BvRotateLeft, BvRotateRight, BvSDiv, BvSGe, BvSGt, BvSLe, BvSLt,
        BvSMod, BvSRem, BvShl, BvSignExtend, BvSub, BvUDiv, BvUGe, BvUGt, BvULe, BvULt, BvURem,
        BvXnor, BvXor, BvZeroExtend,
    };
    let invalid = || CountedTermError::InvalidInput;
    let width = match args {
        [Sort::BitVec(a)] => a.width,
        [Sort::BitVec(a), Sort::BitVec(b)] if a.width == b.width => a.width,
        [Sort::BitVec(a), Sort::BitVec(b)] if op == BvConcat => {
            return a
                .width
                .checked_add(b.width)
                .filter(|width| *width > 0)
                .map(Sort::bitvec)
                .ok_or_else(invalid);
        }
        _ => return Err(invalid()),
    };
    match op {
        BvAdd | BvSub | BvMul | BvUDiv | BvURem | BvSDiv | BvSRem | BvSMod | BvAnd | BvOr
        | BvXor | BvNand | BvNor | BvXnor | BvShl | BvLShr | BvAShr
            if args.len() == 2 =>
        {
            Ok(Sort::bitvec(width))
        }
        BvULt | BvULe | BvUGt | BvUGe | BvSLt | BvSLe | BvSGt | BvSGe if args.len() == 2 => {
            Ok(Sort::Bool)
        }
        BvComp if args.len() == 2 => Ok(Sort::bitvec(1)),
        BvConcat if args.len() == 2 => width.checked_mul(2).map(Sort::bitvec).ok_or_else(invalid),
        BvNot | BvNeg | BvRotateLeft(_) | BvRotateRight(_) if args.len() == 1 => {
            Ok(Sort::bitvec(width))
        }
        BvExtract(high, low) if args.len() == 1 && high >= low && high < width => {
            Ok(Sort::bitvec(high - low + 1))
        }
        BvZeroExtend(extra) | BvSignExtend(extra) if args.len() == 1 => width
            .checked_add(extra)
            .map(Sort::bitvec)
            .ok_or_else(invalid),
        BvRepeat(count) if args.len() == 1 && count > 0 => width
            .checked_mul(count)
            .map(Sort::bitvec)
            .ok_or_else(invalid),
        _ => Err(invalid()),
    }
}

pub(super) fn term(
    op: CountedBuiltin,
    args: &[TermId],
    owner: &dyn TermConstructionAdmission,
) -> Result<TermData> {
    match (op, args) {
        (CountedBuiltin::Not, [arg]) => return Ok(TermData::Not(*arg)),
        (CountedBuiltin::Ite, [c, t, e]) => return Ok(TermData::Ite(*c, *t, *e)),
        _ => {}
    }
    let (name, indices) = symbol(op);
    owner.admit(
        name.len()
            .checked_add(1)
            .ok_or_else(|| storage::work(owner))?,
        128,
    )?;
    let name = storage::text(name, owner)?;
    let symbol = if let Some((count, values)) = indices {
        let mut copied = Vec::new();
        storage::reserve(&mut copied, count, owner)?;
        owner.admit(count, 0)?;
        copied.extend_from_slice(&values[..count]);
        Symbol::indexed(name, copied)
    } else {
        Symbol::named(name)
    };
    payload::application(symbol, args, owner)
}

fn symbol(op: CountedBuiltin) -> (&'static str, Option<(usize, [u32; 2])>) {
    use CountedBuiltin::{
        And, BvAShr, BvAdd, BvAnd, BvComp, BvConcat, BvExtract, BvLShr, BvMul, BvNand, BvNeg,
        BvNor, BvNot, BvOr, BvRepeat, BvRotateLeft, BvRotateRight, BvSDiv, BvSGe, BvSGt, BvSLe,
        BvSLt, BvSMod, BvSRem, BvShl, BvSignExtend, BvSub, BvUDiv, BvUGe, BvUGt, BvULe, BvULt,
        BvURem, BvXnor, BvXor, BvZeroExtend, Distinct, Eq, Iff, Implies, Ite, Not, Or, Select,
        Store, Xor,
    };
    let name = match op {
        Not => "not",
        And => "and",
        Or => "or",
        Implies => "=>",
        Xor => "xor",
        Iff | Eq => "=",
        Distinct => "distinct",
        Ite => "ite",
        Select => "select",
        Store => "store",
        BvAdd => "bvadd",
        BvSub => "bvsub",
        BvMul => "bvmul",
        BvUDiv => "bvudiv",
        BvURem => "bvurem",
        BvSDiv => "bvsdiv",
        BvSRem => "bvsrem",
        BvSMod => "bvsmod",
        BvAnd => "bvand",
        BvOr => "bvor",
        BvXor => "bvxor",
        BvNand => "bvnand",
        BvNor => "bvnor",
        BvXnor => "bvxnor",
        BvShl => "bvshl",
        BvLShr => "bvlshr",
        BvAShr => "bvashr",
        BvNot => "bvnot",
        BvNeg => "bvneg",
        BvULt => "bvult",
        BvULe => "bvule",
        BvUGt => "bvugt",
        BvUGe => "bvuge",
        BvSLt => "bvslt",
        BvSLe => "bvsle",
        BvSGt => "bvsgt",
        BvSGe => "bvsge",
        BvComp => "bvcomp",
        BvConcat => "concat",
        BvExtract(high, low) => return ("extract", Some((2, [high, low]))),
        BvZeroExtend(n) => return ("zero_extend", Some((1, [n, 0]))),
        BvSignExtend(n) => return ("sign_extend", Some((1, [n, 0]))),
        BvRotateLeft(n) => return ("rotate_left", Some((1, [n, 0]))),
        BvRotateRight(n) => return ("rotate_right", Some((1, [n, 0]))),
        BvRepeat(n) => return ("repeat", Some((1, [n, 0]))),
    };
    (name, None)
}

/// Typed field assembly, separate from the public builtin enum so existing
/// clients' exhaustive matches retain their supported vocabulary.
pub(super) fn fp_fields(
    store: &TermStore,
    args: &[TermId; 3],
    owner: &dyn TermConstructionAdmission,
) -> Result<Sort> {
    let mut widths = [0u32; 3];
    for (width, arg) in widths.iter_mut().zip(args) {
        owner.admit(1, 0)?;
        let entry = store
            .terms
            .get(arg.index())
            .ok_or(CountedTermError::InvalidInput)?;
        sorts::visit(&entry.sort, owner, PayloadUse::Inspect)?;
        let Sort::BitVec(bv) = &entry.sort else {
            return Err(CountedTermError::InvalidInput);
        };
        *width = bv.width;
    }
    let [sign, exponent, fraction] = widths;
    if sign != 1 || exponent < 2 || fraction == 0 {
        return Err(CountedTermError::InvalidInput);
    }
    let precision = fraction
        .checked_add(1)
        .ok_or(CountedTermError::InvalidInput)?;
    exponent
        .checked_add(precision)
        .ok_or(CountedTermError::InvalidInput)?;
    Ok(Sort::FloatingPoint(exponent, precision))
}
