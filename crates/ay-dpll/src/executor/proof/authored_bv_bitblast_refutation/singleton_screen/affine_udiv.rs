// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! SINGLETON search advice from a concrete modular-offset witness, no evidence.
//!
//! SMT-LIB FixedSizeBitVectors: bvadd/sub are modulo 2^w and nonzero bvudiv
//! is unsigned integer quotient. https://smt-lib.org/theories-FixedSizeBitVectors.shtml
//! If n1=x+k1 and n2=x+k2, x=-k1 makes n1=0 and n2=delta.
//! delta<d makes both quotients zero; the symmetric witness handles -delta.
//! Every original root stays in the unchanged joint/strict/export attempt.

use super::*;
use num_bigint::{BigInt, BigUint, Sign};

#[cfg(test)]
mod tests;

const MAX_AFFINE_NODES: usize = 128;

/// Charge BEFORE bounded bigint allocation/copy/comparison/add/sub. Logical
/// word work, not an allocator/RSS/CPU promise; arithmetic remains opaque.
fn arithmetic(screen: &mut Screen<'_>, width: u32) -> Option<()> {
    let units = usize::try_from(width)
        .ok()?
        .checked_mul(32)?
        .checked_add(256)?;
    screen.charge(units).then_some(())
}

pub(super) fn singleton_witness(
    screen: &mut Screen<'_>,
    left: TermId,
    right: TermId,
) -> Option<()> {
    let (left_numerator, left_divisor, width) = division(screen, left)?;
    let (right_numerator, right_divisor, other_width) = division(screen, right)?;
    arithmetic(screen, width)?;
    if width != other_width || left_divisor != right_divisor {
        return None;
    }
    // Both canonical literals are nonzero and below 2^width.
    arithmetic(screen, width)?;
    let divisor = left_divisor.to_biguint()?;
    let modulus = BigUint::from(1u8) << width;
    let (left_variable, left_offset) = affine(screen, left_numerator, width, &modulus)?;
    let (right_variable, right_offset) = affine(screen, right_numerator, width, &modulus)?;
    if left_variable != right_variable {
        return None;
    }
    arithmetic(screen, width)?;
    let delta = if right_offset >= left_offset {
        &right_offset - &left_offset
    } else {
        &modulus - (&left_offset - &right_offset)
    };
    arithmetic(screen, width)?;
    if delta < divisor {
        return Some(());
    }
    // delta is nonzero here since divisor is strictly positive.
    let reverse_delta = &modulus - &delta;
    arithmetic(screen, width)?;
    (reverse_delta < divisor).then_some(())
}

fn division<'a>(screen: &mut Screen<'a>, term: TermId) -> Option<(TermId, &'a BigInt, u32)> {
    if !screen.charge(1) {
        return None;
    }
    let ctx = screen.ctx;
    ctx.terms.entry_stamp(term)?;
    let TermData::App(Symbol::Named(name), arguments) = ctx.terms.get(term) else {
        return None;
    };
    let [numerator, denominator] = arguments.as_slice() else {
        return None;
    };
    if name != "bvudiv" || !screen.charge(name.len().checked_add(2)?) {
        return None;
    }
    let typing::Scalar::Word(width) = typing::scalar(ctx, term)? else {
        return None;
    };
    typing::children(ctx, term)?;
    let divisor = literal(screen, *denominator, width)?;
    if divisor.sign() == Sign::NoSign {
        return None;
    }
    Some((*numerator, divisor, width))
}

fn literal<'a>(screen: &mut Screen<'a>, term: TermId, width: u32) -> Option<&'a BigInt> {
    arithmetic(screen, width)?;
    let ctx = screen.ctx;
    ctx.terms.entry_stamp(term)?;
    if typing::scalar(ctx, term)? != typing::Scalar::Word(width) {
        return None;
    }
    let TermData::Const(Constant::BitVec {
        value,
        width: literal_width,
    }) = ctx.terms.get(term)
    else {
        return None;
    };
    if *literal_width != width || value.sign() == Sign::Minus || value.bits() > u64::from(width) {
        return None;
    }
    Some(value)
}

/// Complete grammar: one exact source variable under binary add/sub literal
/// offsets. No hidden operands, indexed operators, UF, second variable,
/// literal-minus-variable or unchosen branch is assigned invented meaning.
/// A cycle cannot reach a variable within MAX_AFFINE_NODES and is refused.
fn affine(
    screen: &mut Screen<'_>,
    mut term: TermId,
    width: u32,
    modulus: &BigUint,
) -> Option<(TermId, BigUint)> {
    arithmetic(screen, width)?;
    let mut offset = BigUint::from(0u8);
    for _ in 0..MAX_AFFINE_NODES {
        if !screen.charge(1) {
            return None;
        }
        let ctx = screen.ctx;
        ctx.terms.entry_stamp(term)?;
        if typing::scalar(ctx, term)? != typing::Scalar::Word(width) {
            return None;
        }
        if matches!(ctx.terms.get(term), TermData::Var(..)) {
            screen.free_variable(term)?;
            return Some((term, offset));
        }
        let TermData::App(Symbol::Named(name), arguments) = ctx.terms.get(term) else {
            return None;
        };
        let [left, right] = arguments.as_slice() else {
            return None;
        };
        if !matches!(name.as_str(), "bvadd" | "bvsub") || !screen.charge(name.len().checked_add(2)?)
        {
            return None;
        }
        typing::children(ctx, term)?;
        let (next, constant, subtract) = if matches!(
            ctx.terms.get(*right),
            TermData::Const(Constant::BitVec { .. })
        ) {
            (*left, literal(screen, *right, width)?, name == "bvsub")
        } else if name == "bvadd"
            && matches!(
                ctx.terms.get(*left),
                TermData::Const(Constant::BitVec { .. })
            )
        {
            (*right, literal(screen, *left, width)?, false)
        } else {
            return None;
        };
        arithmetic(screen, width)?;
        let constant = constant.to_biguint()?;
        arithmetic(screen, width)?;
        offset = if subtract {
            if offset >= constant {
                offset - constant
            } else {
                modulus - (constant - offset)
            }
        } else {
            let sum = offset + constant;
            if &sum >= modulus {
                sum - modulus
            } else {
                sum
            }
        };
        term = next;
    }
    None
}
