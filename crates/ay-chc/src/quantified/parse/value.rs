// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Raw, typed QF syntax only. Scope and source budgets belong to the parser.
//! Child expressions and their sorts have already been authenticated there;
//! this layer checks operator signatures without rewriting any expression.

use super::{invalid, Budget};
use crate::{ChcExpr, ChcOp, ChcResult, ChcSort};
use ay_frontend::SExpr;
use std::sync::Arc;

mod literals;
#[cfg(test)]
mod tests;

fn natural(expr: &SExpr) -> ChcResult<u32> {
    let Some(text) = expr.as_numeral() else {
        return Err(invalid("expected an unsigned index numeral"));
    };
    if text.is_empty()
        || text.len() > 10
        || !text.bytes().all(|byte| byte.is_ascii_digit())
        || (text.len() > 1 && text.starts_with('0'))
    {
        return Err(invalid("invalid unsigned index numeral"));
    }
    text.parse().map_err(|_| invalid("index exceeds u32"))
}

fn width(expr: &SExpr) -> ChcResult<u32> {
    let width = natural(expr)?;
    if !(1..=crate::MAX_BITVECTOR_WIDTH).contains(&width) {
        return Err(invalid("bitvector width exceeds the supported range"));
    }
    Ok(width)
}

fn scalar(expr: &SExpr) -> ChcResult<ChcSort> {
    if expr.is_symbol("Bool") {
        return Ok(ChcSort::Bool);
    }
    if let Some([marker, name, size]) = expr.as_list() {
        if marker.is_symbol("_") && name.is_symbol("BitVec") {
            return Ok(ChcSort::BitVec(width(size)?));
        }
    }
    Err(invalid("expected Bool or a bitvector sort"))
}

pub(super) fn sort(expr: &SExpr) -> ChcResult<ChcSort> {
    if let Some([name, key, value]) = expr.as_list() {
        if name.is_symbol("Array") {
            let key = scalar(key)?;
            if !matches!(key, ChcSort::BitVec(_)) {
                return Err(invalid("array index must be a bitvector"));
            }
            return Ok(ChcSort::Array(Box::new(key), Box::new(scalar(value)?)));
        }
    }
    scalar(expr)
}

fn is_scalar(sort: &ChcSort) -> bool {
    matches!(
        sort,
        ChcSort::Bool | ChcSort::BitVec(1..=crate::MAX_BITVECTOR_WIDTH)
    )
}

// Deliberately shallow: reject arbitrary recursive metadata before equality,
// cloning or the general signature validator can traverse it.
fn supported(sort: &ChcSort) -> bool {
    match sort {
        ChcSort::Array(key, value) => {
            matches!(
                key.as_ref(),
                ChcSort::BitVec(1..=crate::MAX_BITVECTOR_WIDTH)
            ) && is_scalar(value)
        }
        _ => is_scalar(sort),
    }
}

pub(super) fn literal(expr: &SExpr, budget: &mut Budget) -> ChcResult<Option<Arc<ChcExpr>>> {
    literals::literal(expr, budget)
}

fn regular(name: &str) -> ChcResult<ChcOp> {
    Ok(match name {
        "not" => ChcOp::Not,
        "and" => ChcOp::And,
        "or" => ChcOp::Or,
        "=>" => ChcOp::Implies,
        "=" => ChcOp::Eq,
        "distinct" | "xor" => ChcOp::Ne,
        "ite" => ChcOp::Ite,
        "select" => ChcOp::Select,
        "store" => ChcOp::Store,
        "bvadd" => ChcOp::BvAdd,
        "bvsub" => ChcOp::BvSub,
        "bvmul" => ChcOp::BvMul,
        "bvudiv" => ChcOp::BvUDiv,
        "bvurem" => ChcOp::BvURem,
        "bvsdiv" => ChcOp::BvSDiv,
        "bvsrem" => ChcOp::BvSRem,
        "bvsmod" => ChcOp::BvSMod,
        "bvand" => ChcOp::BvAnd,
        "bvor" => ChcOp::BvOr,
        "bvxor" => ChcOp::BvXor,
        "bvnand" => ChcOp::BvNand,
        "bvnor" => ChcOp::BvNor,
        "bvxnor" => ChcOp::BvXnor,
        "bvnot" => ChcOp::BvNot,
        "bvneg" => ChcOp::BvNeg,
        "bvshl" => ChcOp::BvShl,
        "bvlshr" => ChcOp::BvLShr,
        "bvashr" => ChcOp::BvAShr,
        "bvult" => ChcOp::BvULt,
        "bvule" => ChcOp::BvULe,
        "bvugt" => ChcOp::BvUGt,
        "bvuge" => ChcOp::BvUGe,
        "bvslt" => ChcOp::BvSLt,
        "bvsle" => ChcOp::BvSLe,
        "bvsgt" => ChcOp::BvSGt,
        "bvsge" => ChcOp::BvSGe,
        "bvcomp" => ChcOp::BvComp,
        "concat" => ChcOp::BvConcat,
        _ => return Err(invalid("unsupported QF operator")),
    })
}

fn indexed(head: &SExpr) -> ChcResult<ChcOp> {
    let Some(items) = head.as_list() else {
        return Err(invalid("expected an operator identifier"));
    };
    match items {
        [marker, name, high, low] if marker.is_symbol("_") && name.is_symbol("extract") => {
            Ok(ChcOp::BvExtract(natural(high)?, natural(low)?))
        }
        [marker, name, count] if marker.is_symbol("_") => {
            let count = natural(count)?;
            match name.as_symbol() {
                Some("zero_extend") => Ok(ChcOp::BvZeroExtend(count)),
                Some("sign_extend") => Ok(ChcOp::BvSignExtend(count)),
                Some("rotate_left") => Ok(ChcOp::BvRotateLeft(count)),
                Some("rotate_right") => Ok(ChcOp::BvRotateRight(count)),
                Some("repeat") => Ok(ChcOp::BvRepeat(count)),
                _ => Err(invalid("unsupported indexed QF operator")),
            }
        }
        _ => Err(invalid("unsupported indexed operator or index arity")),
    }
}

fn const_array(
    declaration: &SExpr,
    mut args: Vec<Arc<ChcExpr>>,
    sorts: &[ChcSort],
) -> ChcResult<(Arc<ChcExpr>, ChcSort)> {
    let declared = sort(declaration)?;
    let ChcSort::Array(key, element) = &declared else {
        return Err(invalid("constant array requires an array sort"));
    };
    if !matches!(sorts, [actual] if actual == element.as_ref()) {
        return Err(invalid("constant array value has the wrong sort or arity"));
    }
    let Some(value) = args.pop() else {
        return Err(invalid("constant array requires one value"));
    };
    Ok((
        Arc::new(ChcExpr::ConstArray(key.as_ref().clone(), value)),
        declared,
    ))
}

pub(super) fn application(
    head: &SExpr,
    args: Vec<Arc<ChcExpr>>,
    sorts: &[ChcSort],
) -> ChcResult<(Arc<ChcExpr>, ChcSort)> {
    if args.len() != sorts.len() || !sorts.iter().all(supported) {
        return Err(invalid("unsupported or inconsistent operand sorts"));
    }
    if let Some([qualifier, name, declaration]) = head.as_list() {
        if qualifier.is_symbol("as") && name.is_symbol("const") {
            return const_array(declaration, args, sorts);
        }
    }
    // Binary Boolean XOR is disequality, not the similarly named BV operator.
    if head.is_symbol("xor") && sorts != [ChcSort::Bool, ChcSort::Bool] {
        return Err(invalid("xor requires two Bool operands"));
    }
    let op = match head.as_symbol() {
        Some(name) => regular(name)?,
        None => indexed(head)?,
    };
    let result = crate::pdr::validate_qf_operation(op, sorts)?;
    if !supported(&result) {
        return Err(invalid("operator result leaves the scalar-array fragment"));
    }
    Ok((Arc::new(ChcExpr::Op(op, args)), result))
}
