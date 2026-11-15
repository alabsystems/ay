// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

//! Freeze the cb14b9487 full adder and its arithmetic callers. Using the
//! production divider with the new full adder would not be a base oracle.

use super::*;

pub(super) fn full_adder(
    solver: &mut BvSolver<'_>,
    a: CnfLit,
    b: CnfLit,
    cin: CnfLit,
) -> (CnfLit, CnfLit) {
    let partial = solver.mk_xor(a, b);
    let first_carry = solver.mk_and(a, b);
    let sum = solver.mk_xor(partial, cin);
    let second_carry = solver.mk_and(partial, cin);
    (sum, solver.mk_or(first_carry, second_carry))
}

pub(super) fn add(solver: &mut BvSolver<'_>, a: &BvBits, b: &BvBits) -> BvBits {
    assert_eq!(a.len(), b.len());
    let width = a.len();
    let mut result = Vec::with_capacity(width);
    if width == 0 {
        return result;
    }
    if width == 1 {
        result.push(solver.mk_xor(a[0], b[0]));
        return result;
    }
    result.push(solver.mk_xor(a[0], b[0]));
    let mut carry = solver.mk_and(a[0], b[0]);
    for i in 1..width - 1 {
        let (sum, next) = full_adder(solver, a[i], b[i], carry);
        result.push(sum);
        carry = next;
    }
    let partial = solver.mk_xor(a[width - 1], b[width - 1]);
    result.push(solver.mk_xor(partial, carry));
    result
}

pub(super) fn subtract(solver: &mut BvSolver<'_>, a: &BvBits, b: &BvBits) -> BvBits {
    assert_eq!(a.len(), b.len());
    let mut carry = solver.fresh_true();
    let mut result = Vec::with_capacity(a.len());
    for (i, (&ai, &bi)) in a.iter().zip(b).enumerate() {
        if i + 1 == a.len() {
            let partial = solver.mk_xor(ai, -bi);
            result.push(solver.mk_xor(partial, carry));
        } else {
            let (sum, next) = full_adder(solver, ai, -bi, carry);
            result.push(sum);
            carry = next;
        }
    }
    result
}

fn subtract_with_carry(solver: &mut BvSolver<'_>, a: &BvBits, b: &BvBits) -> (BvBits, CnfLit) {
    assert_eq!(a.len(), b.len());
    let mut carry = solver.fresh_true();
    let mut result = Vec::with_capacity(a.len());
    for (&ai, &bi) in a.iter().zip(b) {
        let (sum, next) = full_adder(solver, ai, -bi, carry);
        result.push(sum);
        carry = next;
    }
    (result, carry)
}

pub(super) fn divide(solver: &mut BvSolver<'_>, a: &BvBits, b: &BvBits) -> (BvBits, BvBits) {
    assert_eq!(a.len(), b.len());
    let width = a.len();
    if width == 0 {
        return (Vec::new(), Vec::new());
    }
    let mut rem = solver.const_bits(0, width);
    let mut quotient = Vec::with_capacity(width);
    for i in (0..width).rev() {
        let mut shifted = Vec::with_capacity(width);
        shifted.push(a[i]);
        shifted.extend_from_slice(&rem[..width - 1]);
        rem = shifted;
        let (difference, no_borrow) = subtract_with_carry(solver, &rem, b);
        rem = solver.bitwise_mux(&difference, &rem, no_borrow);
        quotient.push(no_borrow);
    }
    quotient.reverse();
    (quotient, rem)
}

pub(super) fn multiply(solver: &mut BvSolver<'_>, a: &BvBits, b: &BvBits) -> BvBits {
    assert_eq!(a.len(), b.len());
    let width = a.len();
    for (constant, word) in [(b, a), (a, b)] {
        if let Some(shift) = solver.try_bits_power_of_2(constant) {
            return if shift >= width {
                solver.const_bits(0, width)
            } else {
                solver.shift_left_const(word, shift)
            };
        }
    }
    // This unchanged fast path only uses MUX/constant leaves, not full adders.
    if let Some(result) = solver.try_const_case_mul(a, b) {
        return result;
    }
    let (word, selector) = if solver.mul_selector_score(a) < solver.mul_selector_score(b) {
        (b, a)
    } else {
        (a, b)
    };
    multiply_shift_add(solver, word, selector)
}

pub(super) fn multiply_shift_add(solver: &mut BvSolver<'_>, a: &BvBits, b: &BvBits) -> BvBits {
    let width = a.len();
    assert_eq!(width, b.len());
    if width == 0 {
        return Vec::new();
    }
    let mut result = solver.const_bits(0, width);
    for (i, &selector) in b.iter().enumerate() {
        if solver.is_known_false(selector) {
            continue;
        }
        let shifted = solver.shift_left_const(a, i);
        let masked = if solver.is_known_true(selector) {
            shifted
        } else {
            shifted
                .iter()
                .map(|&bit| solver.mk_and(bit, selector))
                .collect()
        };
        result = add(solver, &result, &masked);
    }
    result
}
