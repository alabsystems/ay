// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{Arena, Classes, Key, Owner, Result};
use crate::ChcOp;

pub(super) fn apply(
    id: usize,
    yes: usize,
    no: usize,
    arena: &mut Arena,
    classes: &mut Classes,
    owner: &mut Owner,
) -> Result<bool> {
    let Key::Op(op, args) = &arena.node(id).key else {
        return Ok(false);
    };
    let replacement = match (*op, args.as_slice()) {
        (ChcOp::Eq | ChcOp::Ne, [a, b]) => {
            let equal = if classes.same(*a, *b, owner)? {
                Some(true)
            } else {
                literal_equal(*a, *b, arena, classes, owner)?
            };
            equal.map(|equal| if equal == (*op == ChcOp::Eq) { yes } else { no })
        }
        (ChcOp::Not, [arg]) => match literal(*arg, arena, classes, owner)? {
            Some(Key::Bool(value)) => Some(if *value { no } else { yes }),
            _ => None,
        },
        (ChcOp::Ite, [condition, then_value, else_value]) => {
            match literal(*condition, arena, classes, owner)? {
                // This condition is an original-proved class member. Reading
                // the arena already checked BOTH complete branch expressions.
                Some(Key::Bool(value)) => Some(if *value { *then_value } else { *else_value }),
                _ => None,
            }
        }
        (ChcOp::Store, [array, index, value]) => {
            read_is_value(*array, *index, *value, arena, classes, owner)?.then_some(*array)
        }
        _ => None,
    };
    if let Some(replacement) = replacement {
        return classes.union(id, replacement, arena, owner);
    }
    let folded = fold(*op, args, arena, classes, owner)?;
    if let Some((value, width)) = folded {
        let value = arena.bitvector(value, width, owner)?;
        classes.extend(arena, owner)?;
        return classes.union(id, value, arena, owner);
    }
    Ok(false)
}

/// A store of the value already read at its index leaves its base unchanged.
/// Complete input typing precedes this walk. Read-over-write skips a store
/// only for proved distinct literal indices; unrelated classes are not a
/// disequality. Every step retains the same original owner.
fn read_is_value(
    mut array: usize,
    index: usize,
    value: usize,
    arena: &Arena,
    classes: &mut Classes,
    owner: &mut Owner,
) -> Result<bool> {
    loop {
        owner.admit(1, 0)?;
        if let Some(constant) = classes.array(array, owner)? {
            if let Key::ConstArray(_, default) = &arena.node(constant).key {
                return classes.same(*default, value, owner);
            }
        }
        let Key::Op(ChcOp::Store, args) = &arena.node(array).key else {
            return Ok(false);
        };
        let [base, stored_index, stored_value] = args.as_slice() else {
            return Ok(false);
        };
        if classes.same(*stored_index, index, owner)? {
            return classes.same(*stored_value, value, owner);
        }
        if literal_equal(*stored_index, index, arena, classes, owner)? != Some(false) {
            return Ok(false);
        }
        array = *base;
    }
}

fn literal<'a, 's>(
    id: usize,
    arena: &'s Arena<'a>,
    classes: &mut Classes,
    owner: &mut Owner,
) -> Result<Option<&'s Key<'a>>> {
    Ok(classes.literal(id, owner)?.map(|id| &arena.node(id).key))
}

fn bits(
    id: usize,
    arena: &Arena,
    classes: &mut Classes,
    owner: &mut Owner,
) -> Result<Option<(u128, u32)>> {
    Ok(match literal(id, arena, classes, owner)? {
        Some(Key::BitVec(value, width)) if *width <= 128 => Some((*value, *width)),
        _ => None,
    })
}

fn literal_equal(
    a: usize,
    b: usize,
    arena: &Arena,
    classes: &mut Classes,
    owner: &mut Owner,
) -> Result<Option<bool>> {
    // Different e-classes do NOT prove disequality. Only exact, fully typed
    // concrete values do; wide bitvectors and other scalar theories decline.
    Ok(
        match (
            literal(a, arena, classes, owner)?,
            literal(b, arena, classes, owner)?,
        ) {
            (Some(Key::Bool(a)), Some(Key::Bool(b))) => Some(a == b),
            (Some(Key::BitVec(a, aw)), Some(Key::BitVec(b, bw))) if aw == bw && *aw <= 128 => {
                Some(a == b)
            }
            _ => None,
        },
    )
}

fn fold(
    op: ChcOp,
    args: &[usize],
    arena: &Arena,
    classes: &mut Classes,
    owner: &mut Owner,
) -> Result<Option<(u128, u32)>> {
    owner.admit(1, 0)?;
    match (op, args) {
        (ChcOp::BvMul, [a, b]) => {
            let (Some((a, aw)), Some((b, bw))) = (
                bits(*a, arena, classes, owner)?,
                bits(*b, arena, classes, owner)?,
            ) else {
                return Ok(None);
            };
            if aw != bw {
                return Ok(None);
            }
            // SMT fixed-width multiplication is modulo 2^w. Taking the low
            // 128 product bits first is exact for every supported w <=128,
            // including overflow; this never narrows an unsupported width.
            let mask = if aw == 128 {
                u128::MAX
            } else {
                (1u128 << aw) - 1
            };
            Ok(Some((a.wrapping_mul(b) & mask, aw)))
        }
        (ChcOp::BvConcat, [hi, lo]) => {
            let (Some((hi, hw)), Some((lo, lw))) = (
                bits(*hi, arena, classes, owner)?,
                bits(*lo, arena, classes, owner)?,
            ) else {
                return Ok(None);
            };
            let Some(width) = hw.checked_add(lw).filter(|w| *w <= 128) else {
                return Ok(None);
            };
            // Both operands were fully range-checked. A <=128-bit result and
            // nonzero high width imply lw <128; no truncating cast or shift.
            let Some(high) = hi.checked_shl(lw) else {
                return Ok(None);
            };
            Ok(Some((high | lo, width)))
        }
        (ChcOp::BvExtract(hi, lo), [arg]) => {
            let Some((value, source_width)) = bits(*arg, arena, classes, owner)? else {
                return Ok(None);
            };
            let Some(width) = hi.checked_sub(lo).and_then(|w| w.checked_add(1)) else {
                return Ok(None);
            };
            if hi >= source_width || width > 128 {
                return Ok(None);
            }
            let Some(value) = value.checked_shr(lo) else {
                return Ok(None);
            };
            let mask = if width == 128 {
                u128::MAX
            } else {
                (1u128 << width) - 1
            };
            Ok(Some((value & mask, width)))
        }
        _ => Ok(None),
    }
}
