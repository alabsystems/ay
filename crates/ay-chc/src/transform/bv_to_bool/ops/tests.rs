// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::unwrap_used)]

use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use num_bigint::BigInt;

use super::{
    circuits::{
        bits_vec_to_int_expr, bitvec_const_to_int_expr, ripple_carry_add,
        ripple_carry_add_with_carry, shift_add_multiply, signed_less_than, unsigned_less_than, xor,
    },
    expr_to_bits,
};

#[test]
fn constant_to_bits() {
    let bits = expr_to_bits(&ChcExpr::BitVec(0b1010, 4), 4);
    assert_eq!(bits.len(), 4);
    assert_eq!(bits[0], ChcExpr::Bool(false));
    assert_eq!(bits[1], ChcExpr::Bool(true));
    assert_eq!(bits[2], ChcExpr::Bool(false));
    assert_eq!(bits[3], ChcExpr::Bool(true));
}

#[test]
fn variable_to_bits() {
    let value = ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(4)));
    let bits = expr_to_bits(&value, 4);
    assert_eq!(bits.len(), 4);
    for (idx, bit) in bits.iter().enumerate() {
        match bit {
            ChcExpr::Var(var) => assert_eq!(var.name, format!("x_b{idx}")),
            _ => panic!("Expected Var, got: {bit}"),
        }
    }
}

#[test]
fn xor_constants() {
    assert_eq!(
        xor(ChcExpr::Bool(false), ChcExpr::Bool(false)),
        ChcExpr::Bool(false)
    );
    assert_eq!(
        xor(ChcExpr::Bool(true), ChcExpr::Bool(false)),
        ChcExpr::Bool(true)
    );
    assert_eq!(
        xor(ChcExpr::Bool(false), ChcExpr::Bool(true)),
        ChcExpr::Bool(true)
    );
}

#[test]
fn add_constants_4bit() {
    let a = expr_to_bits(&ChcExpr::BitVec(3, 4), 4);
    let b = expr_to_bits(&ChcExpr::BitVec(5, 4), 4);
    assert_eq!(bits_to_u32(&ripple_carry_add(&a, &b)), 8);
}

#[test]
fn add_overflow_4bit() {
    let a = expr_to_bits(&ChcExpr::BitVec(15, 4), 4);
    let b = expr_to_bits(&ChcExpr::BitVec(1, 4), 4);
    assert_eq!(bits_to_u32(&ripple_carry_add(&a, &b)), 0);
}

#[test]
fn sub_constants_4bit() {
    let a = expr_to_bits(&ChcExpr::BitVec(5, 4), 4);
    let b = expr_to_bits(&ChcExpr::BitVec(3, 4), 4);
    let not_b: Vec<ChcExpr> = b.into_iter().map(ChcExpr::not).collect();
    let diff = ripple_carry_add_with_carry(&a, &not_b, ChcExpr::Bool(true));
    assert_eq!(bits_to_u32(&diff), 2);
}

#[test]
fn mul_constants_4bit() {
    let a = expr_to_bits(&ChcExpr::BitVec(3, 4), 4);
    let b = expr_to_bits(&ChcExpr::BitVec(5, 4), 4);
    assert_eq!(bits_to_u32(&shift_add_multiply(&a, &b, 4)), 15);
}

#[test]
fn unsigned_lt_constants() {
    let a = expr_to_bits(&ChcExpr::BitVec(3, 4), 4);
    let b = expr_to_bits(&ChcExpr::BitVec(5, 4), 4);
    assert!(eval_bool(&unsigned_less_than(&a, &b)));
    assert!(!eval_bool(&unsigned_less_than(&b, &a)));
    assert!(!eval_bool(&unsigned_less_than(&a, &a)));
}

#[test]
fn signed_lt_constants() {
    let neg1 = expr_to_bits(&ChcExpr::BitVec(15, 4), 4);
    let zero = expr_to_bits(&ChcExpr::BitVec(0, 4), 4);
    let three = expr_to_bits(&ChcExpr::BitVec(3, 4), 4);
    assert!(eval_bool(&signed_less_than(&neg1, &zero)));
    assert!(eval_bool(&signed_less_than(&neg1, &three)));
    assert!(!eval_bool(&signed_less_than(&three, &neg1)));
}

#[test]
fn bits_vec_to_int_expr_handles_wide_bit_positions_7897() {
    let mut bits = vec![ChcExpr::Bool(false); 80];
    bits[0] = ChcExpr::Bool(true);
    bits[63] = ChcExpr::Bool(true);
    bits[79] = ChcExpr::Bool(true);

    let expr = bits_vec_to_int_expr(&bits);
    let expected = (BigInt::from(1u8) << 79) + (BigInt::from(1u8) << 63) + BigInt::from(1u8);
    assert_eq!(eval_int(&expr), expected);
}

#[test]
fn bitvec_const_to_int_expr_preserves_wide_literals_7897() {
    let value = (1u128 << 100) | (1u128 << 63) | 7u128;
    let expr = bitvec_const_to_int_expr(value);
    assert_eq!(eval_int(&expr), BigInt::from(value));
}

fn eval_bool(expr: &ChcExpr) -> bool {
    match expr {
        ChcExpr::Bool(value) => *value,
        ChcExpr::Op(ChcOp::Not, args) => !eval_bool(&args[0]),
        ChcExpr::Op(ChcOp::And, args) => args.iter().all(|arg| eval_bool(arg)),
        ChcExpr::Op(ChcOp::Or, args) => args.iter().any(|arg| eval_bool(arg)),
        ChcExpr::Op(ChcOp::Ite, args) => {
            if eval_bool(&args[0]) {
                eval_bool(&args[1])
            } else {
                eval_bool(&args[2])
            }
        }
        _ => panic!("Cannot evaluate: {expr}"),
    }
}

fn bits_to_u32(bits: &[ChcExpr]) -> u32 {
    let mut value = 0u32;
    for (idx, bit) in bits.iter().enumerate() {
        if eval_bool(bit) {
            value |= 1u32 << idx;
        }
    }
    value
}

fn eval_int(expr: &ChcExpr) -> BigInt {
    match expr {
        ChcExpr::Int(value) => BigInt::from(*value),
        ChcExpr::Op(ChcOp::Add, args) => eval_int(&args[0]) + eval_int(&args[1]),
        ChcExpr::Op(ChcOp::Mul, args) => eval_int(&args[0]) * eval_int(&args[1]),
        ChcExpr::Op(ChcOp::Ite, args) => {
            if eval_bool(&args[0]) {
                eval_int(&args[1])
            } else {
                eval_int(&args[2])
            }
        }
        _ => panic!("Cannot evaluate int expr: {expr}"),
    }
}

/// Regression test for #6536: comparison lowering with unknown-width operands
/// should return None (preserving the original expression) instead of
/// fabricating a 32-bit encoding.
#[test]
fn comparison_unknown_width_returns_none_6536() {
    use std::sync::Arc;
    // Int-sorted variable — width inference should fail
    let int_var = Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::Int)));
    let args = vec![int_var.clone(), int_var];
    assert!(
        super::bitblast_comparison_op(&ChcOp::BvULt, &args).is_none(),
        "comparison on Int operands should return None, not fabricate a 32-bit encoding"
    );
}

/// Regression test for #6536: equality lowering with unknown-width operands
/// should return None instead of fabricating a 32-bit encoding.
#[test]
fn equality_unknown_width_returns_none_6536() {
    use std::sync::Arc;
    let int_var = Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::Int)));
    let args = vec![int_var.clone(), int_var];
    assert!(
        super::bitblast_bv_equality_op(&ChcOp::Eq, &args).is_none(),
        "equality on Int operands should return None, not fabricate a 32-bit encoding"
    );
}

/// Regression test for #8739: BV-arithmetic lowering with a `Select` subterm
/// must return `None` instead of silently bit-blasting the `select` into
/// unconstrained bits.
#[test]
fn bv_value_op_with_select_child_returns_none_8739() {
    use std::sync::Arc;

    let arr_sort = ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::BitVec(32)));
    let arr = Arc::new(ChcExpr::Var(ChcVar::new("arr", arr_sort)));
    let i = Arc::new(ChcExpr::Var(ChcVar::new("i", ChcSort::BitVec(32))));
    let sel = Arc::new(ChcExpr::Op(ChcOp::Select, vec![arr, i]));
    let one = Arc::new(ChcExpr::BitVec(1, 32));

    assert!(
        super::bitblast_bv_value_op(&ChcOp::BvAdd, &[sel, one]).is_none(),
        "BvAdd with Select child must bail out so later transforms preserve the array read"
    );
}

/// Regression test for #8739: `bv2nat(select(arr, i))` must also preserve the
/// opaque `select` node for later BV-to-Int abstraction.
#[test]
fn bv2nat_with_select_child_returns_none_8739() {
    use std::sync::Arc;

    let arr_sort = ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::BitVec(32)));
    let arr = Arc::new(ChcExpr::Var(ChcVar::new("arr", arr_sort)));
    let i = Arc::new(ChcExpr::Var(ChcVar::new("i", ChcSort::BitVec(32))));
    let sel = Arc::new(ChcExpr::Op(ChcOp::Select, vec![arr, i]));

    assert!(
        super::bitblast_bv_value_op(&ChcOp::Bv2Nat, &[sel]).is_none(),
        "Bv2Nat with Select operand must bail out so the array-read value is not lost"
    );
}

/// Regression test for #8739: the new guard must not block ordinary BV
/// arithmetic over directly bit-blastable operands.
#[test]
fn bv_value_op_without_select_still_works_8739() {
    use std::sync::Arc;

    let x = Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(32))));
    let one = Arc::new(ChcExpr::BitVec(1, 32));

    assert!(
        super::bitblast_bv_value_op(&ChcOp::BvAdd, &[x, one]).is_some(),
        "BvAdd on plain BV operands should still use the bit-blasting fast path"
    );
}
