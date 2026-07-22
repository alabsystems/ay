// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::{ChcExpr, ChcSort, ChcVar};

const INT_CHUNK_BASE: i64 = 1i64 << 32;

pub(super) fn xor(a: ChcExpr, b: ChcExpr) -> ChcExpr {
    match (&a, &b) {
        (ChcExpr::Bool(false), _) => return b,
        (_, ChcExpr::Bool(false)) => return a,
        (ChcExpr::Bool(true), _) => return ChcExpr::not(b),
        (_, ChcExpr::Bool(true)) => return ChcExpr::not(a),
        _ => {}
    }
    ChcExpr::or(
        ChcExpr::and(a.clone(), ChcExpr::not(b.clone())),
        ChcExpr::and(ChcExpr::not(a), b),
    )
}

pub(super) fn ripple_carry_add(a: &[ChcExpr], b: &[ChcExpr]) -> Vec<ChcExpr> {
    ripple_carry_add_with_carry(a, b, ChcExpr::Bool(false))
}

pub(super) fn ripple_carry_add_with_carry(
    a: &[ChcExpr],
    b: &[ChcExpr],
    initial_carry: ChcExpr,
) -> Vec<ChcExpr> {
    let mut result = Vec::with_capacity(a.len());
    let mut carry = initial_carry;

    for (ai, bi) in a.iter().zip(b.iter()) {
        let ab_xor = xor(ai.clone(), bi.clone());
        let sum = xor(ab_xor.clone(), carry.clone());
        let new_carry = ChcExpr::or(
            ChcExpr::and(ai.clone(), bi.clone()),
            ChcExpr::and(carry, ab_xor),
        );
        result.push(sum);
        carry = new_carry;
    }

    result
}

pub(super) fn shift_add_multiply(a: &[ChcExpr], b: &[ChcExpr], width: u32) -> Vec<ChcExpr> {
    let target = width as usize;
    let mut result = vec![ChcExpr::Bool(false); target];

    for (shift, control) in b.iter().enumerate() {
        let partial = partial_product(a, control, shift, target);
        result = ripple_carry_add(&result, &partial);
    }

    result
}

fn partial_product(
    a: &[ChcExpr],
    control: &ChcExpr,
    shift: usize,
    target_len: usize,
) -> Vec<ChcExpr> {
    (0..target_len)
        .map(|out_idx| match out_idx.checked_sub(shift) {
            Some(src_idx) if src_idx < a.len() => ChcExpr::and(control.clone(), a[src_idx].clone()),
            _ => ChcExpr::Bool(false),
        })
        .collect()
}

pub(super) fn barrel_shift_left(a: &[ChcExpr], b: &[ChcExpr], width: u32) -> Vec<ChcExpr> {
    barrel_shift(a, b, width, ShiftFill::Zero, ShiftDirection::Left)
}

pub(super) fn barrel_shift_right_logical(a: &[ChcExpr], b: &[ChcExpr], width: u32) -> Vec<ChcExpr> {
    barrel_shift(a, b, width, ShiftFill::Zero, ShiftDirection::Right)
}

pub(super) fn barrel_shift_right_arithmetic(
    a: &[ChcExpr],
    b: &[ChcExpr],
    width: u32,
) -> Vec<ChcExpr> {
    let sign_bit = a.last().cloned().unwrap_or(ChcExpr::Bool(false));
    barrel_shift(
        a,
        b,
        width,
        ShiftFill::Sign(sign_bit),
        ShiftDirection::Right,
    )
}

enum ShiftDirection {
    Left,
    Right,
}

enum ShiftFill {
    Zero,
    Sign(ChcExpr),
}

fn barrel_shift(
    a: &[ChcExpr],
    b: &[ChcExpr],
    width: u32,
    fill: ShiftFill,
    direction: ShiftDirection,
) -> Vec<ChcExpr> {
    let target = width as usize;
    let mut current = a.to_vec();

    for (stage, selector) in b.iter().take(32).enumerate() {
        let shift = 1usize << stage;
        if shift >= target {
            current = current
                .iter()
                .map(|bit| match &fill {
                    ShiftFill::Zero => ChcExpr::and(bit.clone(), ChcExpr::not(selector.clone())),
                    ShiftFill::Sign(sign) => {
                        ChcExpr::ite(selector.clone(), sign.clone(), ChcExpr::Bool(false))
                    }
                })
                .collect();
            break;
        }

        let mut shifted = Vec::with_capacity(target);
        for idx in 0..target {
            let replacement = shifted_bit(&current, idx, shift, &fill, &direction);
            shifted.push(ChcExpr::ite(
                selector.clone(),
                replacement,
                current[idx].clone(),
            ));
        }
        current = shifted;
    }

    current
}

fn shifted_bit(
    current: &[ChcExpr],
    idx: usize,
    shift: usize,
    fill: &ShiftFill,
    direction: &ShiftDirection,
) -> ChcExpr {
    match direction {
        ShiftDirection::Left => idx
            .checked_sub(shift)
            .and_then(|src| current.get(src).cloned())
            .unwrap_or_else(|| fill_value(fill)),
        ShiftDirection::Right => current
            .get(idx + shift)
            .cloned()
            .unwrap_or_else(|| fill_value(fill)),
    }
}

fn fill_value(fill: &ShiftFill) -> ChcExpr {
    match fill {
        ShiftFill::Zero => ChcExpr::Bool(false),
        ShiftFill::Sign(sign) => sign.clone(),
    }
}

pub(super) fn unsigned_less_than(a: &[ChcExpr], b: &[ChcExpr]) -> ChcExpr {
    let mut result = ChcExpr::Bool(false);
    for (ai, bi) in a.iter().zip(b.iter()) {
        result = ChcExpr::ite(
            xor(ai.clone(), bi.clone()),
            ChcExpr::not(ai.clone()),
            result,
        );
    }
    result
}

pub(super) fn signed_less_than(a: &[ChcExpr], b: &[ChcExpr]) -> ChcExpr {
    if a.is_empty() {
        return ChcExpr::Bool(false);
    }

    let mut a_flipped = a.to_vec();
    let mut b_flipped = b.to_vec();
    let msb = a.len() - 1;
    a_flipped[msb] = ChcExpr::not(a[msb].clone());
    b_flipped[msb] = ChcExpr::not(b[msb].clone());
    unsigned_less_than(&a_flipped, &b_flipped)
}

pub(super) fn bits_to_int_expr(var_name: &str, width: u32) -> ChcExpr {
    bits_vec_to_int_expr(
        &(0..width)
            .map(|i| ChcExpr::var(ChcVar::new(format!("{var_name}_b{i}"), ChcSort::Bool)))
            .collect::<Vec<_>>(),
    )
}

pub(super) fn bitvec_const_to_int_expr(value: u128) -> ChcExpr {
    let mut limbs = Vec::new();
    let mut remaining = value;
    while remaining != 0 {
        limbs.push((remaining & u128::from(u32::MAX)) as i64);
        remaining >>= 32;
    }

    limbs.into_iter().rev().fold(ChcExpr::int(0), |acc, limb| {
        let limb_expr = ChcExpr::int(limb);
        if acc == ChcExpr::int(0) {
            limb_expr
        } else if limb == 0 {
            ChcExpr::mul(ChcExpr::int(INT_CHUNK_BASE), acc)
        } else {
            ChcExpr::add(limb_expr, ChcExpr::mul(ChcExpr::int(INT_CHUNK_BASE), acc))
        }
    })
}

pub(super) fn bits_vec_to_int_expr(bits: &[ChcExpr]) -> ChcExpr {
    bits.iter().rev().fold(ChcExpr::int(0), |acc, bit| {
        let bit_expr = match bit {
            ChcExpr::Bool(true) => ChcExpr::int(1),
            ChcExpr::Bool(false) => ChcExpr::int(0),
            _ => ChcExpr::ite(bit.clone(), ChcExpr::int(1), ChcExpr::int(0)),
        };
        if acc == ChcExpr::int(0) {
            bit_expr
        } else if bit_expr == ChcExpr::int(0) {
            ChcExpr::mul(ChcExpr::int(2), acc)
        } else {
            ChcExpr::add(bit_expr, ChcExpr::mul(ChcExpr::int(2), acc))
        }
    })
}
