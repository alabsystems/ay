// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Bitvector operation tests (#875).

use super::*;

#[test]
fn test_bv_bitwise_and() {
    let mut program = AYProgram::new();
    program.set_logic("QF_BV");
    let a = program.declare_const("a", Sort::bv32());
    let b = program.declare_const("b", Sort::bv32());

    // (a AND b) = (b AND a) - commutativity via UNSAT of inequality
    let lhs = a.clone().bvand(b.clone());
    let rhs = b.bvand(a);
    program.assert(lhs.eq(rhs).not());
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(matches!(result, ExecuteResult::Verified));
}

#[test]
fn test_bv_bitwise_or() {
    let mut program = AYProgram::new();
    program.set_logic("QF_BV");
    let a = program.declare_const("a", Sort::bv32());
    let b = program.declare_const("b", Sort::bv32());

    // (a OR b) = (b OR a) - commutativity
    let lhs = a.clone().bvor(b.clone());
    let rhs = b.bvor(a);
    program.assert(lhs.eq(rhs).not());
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(matches!(result, ExecuteResult::Verified));
}

#[test]
fn test_bv_bitwise_xor() {
    let mut program = AYProgram::new();
    program.set_logic("QF_BV");
    let a = program.declare_const("a", Sort::bv32());

    // a XOR a = 0 (self-inverse)
    let zero = Expr::bitvec_const(0u64, 32);
    let xor_self = a.clone().bvxor(a);
    program.assert(xor_self.eq(zero).not());
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(matches!(result, ExecuteResult::Verified));
}

#[test]
fn test_bv_not_involution() {
    let mut program = AYProgram::new();
    program.set_logic("QF_BV");
    let a = program.declare_const("a", Sort::bv32());

    // NOT(NOT(a)) = a (involution)
    let double_not = a.clone().bvnot().bvnot();
    program.assert(double_not.eq(a).not());
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(matches!(result, ExecuteResult::Verified));
}

#[test]
fn test_bv_neg_self_cancel() {
    let mut program = AYProgram::new();
    program.set_logic("QF_BV");
    let a = program.declare_const("a", Sort::bv32());

    // -(-a) = a (negation cancels)
    let double_neg = a.clone().bvneg().bvneg();
    program.assert(double_neg.eq(a).not());
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(matches!(result, ExecuteResult::Verified));
}

#[test]
fn test_bv_shift_left() {
    let mut program = AYProgram::new();
    program.set_logic("QF_BV");

    // 1 << 3 = 8
    let one = Expr::bitvec_const(1u64, 32);
    let three = Expr::bitvec_const(3u64, 32);
    let eight = Expr::bitvec_const(8u64, 32);
    let shifted = one.bvshl(three);
    program.assert(shifted.eq(eight).not());
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(matches!(result, ExecuteResult::Verified));
}

#[test]
fn test_bv_logical_shift_right() {
    let mut program = AYProgram::new();
    program.set_logic("QF_BV");

    // 16 >> 2 = 4 (logical)
    let sixteen = Expr::bitvec_const(16u64, 32);
    let two = Expr::bitvec_const(2u64, 32);
    let four = Expr::bitvec_const(4u64, 32);
    let shifted = sixteen.bvlshr(two);
    program.assert(shifted.eq(four).not());
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(matches!(result, ExecuteResult::Verified));
}

#[test]
fn test_bv_arithmetic_shift_right() {
    let mut program = AYProgram::new();
    program.set_logic("QF_BV");

    // -8 >> 1 = -4 (arithmetic, preserves sign)
    // In 2's complement 32-bit: -8 = 0xFFFFFFF8, -4 = 0xFFFFFFFC
    let neg_eight = Expr::bitvec_const(0xFFFFFFF8u64, 32);
    let one = Expr::bitvec_const(1u64, 32);
    let neg_four = Expr::bitvec_const(0xFFFFFFFCu64, 32);
    let shifted = neg_eight.bvashr(one);
    program.assert(shifted.eq(neg_four).not());
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(matches!(result, ExecuteResult::Verified));
}

#[test]
fn test_bv_unsigned_comparison() {
    let mut program = AYProgram::new();
    program.set_logic("QF_BV");
    let a = program.declare_const("a", Sort::bv32());
    let b = program.declare_const("b", Sort::bv32());

    // (a <= b) XOR (a > b) should always be true
    // i.e., NOT((a <= b) XOR (a > b)) is UNSAT
    let le = a.clone().bvule(b.clone());
    let gt = a.bvugt(b);
    let xor_expr = le.xor(gt);
    program.assert(xor_expr.not());
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(matches!(result, ExecuteResult::Verified));
}

#[test]
fn test_bv_signed_comparison() {
    let mut program = AYProgram::new();
    program.set_logic("QF_BV");
    let a = program.declare_const("a", Sort::bv32());
    let b = program.declare_const("b", Sort::bv32());

    // (a <= b) XOR (a > b) should always be true (signed)
    let le = a.clone().bvsle(b.clone());
    let gt = a.bvsgt(b);
    let xor_expr = le.xor(gt);
    program.assert(xor_expr.not());
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(matches!(result, ExecuteResult::Verified));
}

#[test]
fn test_bv_zero_extend() {
    let mut program = AYProgram::new();
    program.set_logic("QF_BV");

    // zero_extend(8-bit 0xFF, 8) = 16-bit 0x00FF
    let val_8 = Expr::bitvec_const(0xFFu64, 8);
    let expected_16 = Expr::bitvec_const(0x00FFu64, 16);
    let extended = val_8.zero_extend(8);
    program.assert(extended.eq(expected_16).not());
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(matches!(result, ExecuteResult::Verified));
}

#[test]
fn test_bv_sign_extend() {
    let mut program = AYProgram::new();
    program.set_logic("QF_BV");

    // sign_extend(8-bit 0xFF (-1), 8) = 16-bit 0xFFFF (-1)
    let val_8 = Expr::bitvec_const(0xFFu64, 8);
    let expected_16 = Expr::bitvec_const(0xFFFFu64, 16);
    let extended = val_8.sign_extend(8);
    program.assert(extended.eq(expected_16).not());
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(matches!(result, ExecuteResult::Verified));
}

#[test]
fn test_bv_extract() {
    let mut program = AYProgram::new();
    program.set_logic("QF_BV");

    // extract[15:8](0xABCD) = 0xAB
    let val = Expr::bitvec_const(0xABCDu64, 16);
    let expected = Expr::bitvec_const(0xABu64, 8);
    let extracted = val.extract(15, 8);
    program.assert(extracted.eq(expected).not());
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(matches!(result, ExecuteResult::Verified));
}

#[test]
fn test_bv_concat() {
    let mut program = AYProgram::new();
    program.set_logic("QF_BV");

    // concat(0xAB, 0xCD) = 0xABCD
    let high = Expr::bitvec_const(0xABu64, 8);
    let low = Expr::bitvec_const(0xCDu64, 8);
    let expected = Expr::bitvec_const(0xABCDu64, 16);
    let concatenated = high.concat(low);
    program.assert(concatenated.eq(expected).not());
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(matches!(result, ExecuteResult::Verified));
}

#[test]
fn test_bv_add_no_overflow_unsigned_sat() {
    let mut program = AYProgram::new();
    program.set_logic("QF_BV");

    // 0xFFFFFFFF + 1 overflows (unsigned)
    let max = Expr::bitvec_const(0xFFFFFFFFu64, 32);
    let one = Expr::bitvec_const(1u64, 32);
    // bvadd_no_overflow returns true if no overflow, false if overflow
    // So for max + 1, overflow occurs, predicate is false
    let no_overflow = max.bvadd_no_overflow_unsigned(one);
    program.assert(no_overflow); // assert no overflow - should be SAT=false
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(matches!(result, ExecuteResult::Verified));
}

#[test]
fn test_bv_add_no_overflow_signed_sat() {
    let mut program = AYProgram::new();
    program.set_logic("QF_BV");

    // 0x7FFFFFFF (max signed i32) + 1 overflows (signed)
    let max_signed = Expr::bitvec_const(0x7FFFFFFFu64, 32);
    let one = Expr::bitvec_const(1u64, 32);
    let no_overflow = max_signed.bvadd_no_overflow_signed(one);
    program.assert(no_overflow); // assert no overflow - should be SAT=false
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(matches!(result, ExecuteResult::Verified));
}

// Regression: signed overflow must catch BOTH directions (#3884)
// Before the fix, BvAddNoOverflowSigned only checked positive overflow
// (positive+positive=negative) but missed negative underflow
// (negative+negative=positive).

#[test]
fn test_bv_add_no_overflow_signed_catches_underflow() {
    // -128 + (-1) = 127 on i8 — this is signed underflow (neg+neg=pos)
    let mut program = AYProgram::new();
    program.set_logic("QF_BV");

    let min_i8 = Expr::bitvec_const(0x80u64, 8); // -128
    let neg_one = Expr::bitvec_const(0xFFu64, 8); // -1
    let no_overflow = min_i8.bvadd_no_overflow_signed(neg_one);
    program.assert(no_overflow); // assert no overflow — should be UNSAT
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(
        matches!(result, ExecuteResult::Verified),
        "BvAddNoOverflowSigned must catch negative underflow: -128 + -1 wraps to 127"
    );
}

#[test]
fn test_bv_sub_no_overflow_signed_catches_underflow() {
    // -128 - 1 = 127 on i8 — signed subtraction underflow (neg-pos=pos)
    let mut program = AYProgram::new();
    program.set_logic("QF_BV");

    let min_i8 = Expr::bitvec_const(0x80u64, 8); // -128
    let one = Expr::bitvec_const(1u64, 8);
    let no_overflow = min_i8.bvsub_no_overflow_signed(one);
    program.assert(no_overflow); // assert no overflow — should be UNSAT
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(
        matches!(result, ExecuteResult::Verified),
        "BvSubNoOverflowSigned must catch negative underflow: -128 - 1 wraps to 127"
    );
}

#[test]
fn test_bv_mul_no_overflow_signed_catches_underflow() {
    // 127 * (-2) = -254 on i8, which wraps to 2 — signed mul underflow
    let mut program = AYProgram::new();
    program.set_logic("QF_BV");

    let pos = Expr::bitvec_const(0x7Fu64, 8); // 127
    let neg_two = Expr::bitvec_const(0xFEu64, 8); // -2
    let no_overflow = pos.bvmul_no_overflow_signed(neg_two);
    program.assert(no_overflow); // assert no overflow — should be UNSAT
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(
        matches!(result, ExecuteResult::Verified),
        "BvMulNoOverflowSigned must catch signed mul underflow: 127 * -2 wraps"
    );
}

#[test]
fn test_bv_neg_no_overflow_catches_min_value() {
    let mut program = AYProgram::new();
    program.set_logic("QF_BV");

    // Negating the signed minimum overflows: -(-128) wraps to 128 on i8.
    let min_i8 = Expr::bitvec_const(0x80u64, 8); // -128
    let no_overflow = min_i8.bvneg_no_overflow();
    program.assert(no_overflow);
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(
        matches!(result, ExecuteResult::Verified),
        "BvNegNoOverflow must reject negating the signed minimum"
    );
}

#[test]
fn test_bv_sdiv_no_overflow_catches_min_div_neg_one() {
    let mut program = AYProgram::new();
    program.set_logic("QF_BV");

    // Signed division overflows only for MIN / -1 on fixed-width bitvectors.
    let min_i8 = Expr::bitvec_const(0x80u64, 8); // -128
    let neg_one = Expr::bitvec_const(0xFFu64, 8); // -1
    let no_overflow = min_i8.bvsdiv_no_overflow(neg_one);
    program.assert(no_overflow);
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(
        matches!(result, ExecuteResult::Verified),
        "BvSdivNoOverflow must reject MIN / -1 on signed bitvectors"
    );
}

#[test]
fn test_large_bv_const_no_fallback() {
    use num_bigint::BigInt;

    let mut program = AYProgram::new();
    program.set_logic("QF_BV");
    // 128-bit constant exceeding i64 range — previously triggered fallback.
    // 2^100 is well beyond i64::MAX but fits in 128 bits.
    let large_val = BigInt::from(1u64) << 100;
    let x = program.declare_const("x", Sort::bitvec(128));
    let c = Expr::bitvec_const(large_val, 128);
    program.assert(x.eq(c));
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(
        !matches!(result, ExecuteResult::NeedsFallback(_)),
        "128-bit BV constant should not trigger fallback, got: {:?}",
        result
    );
    assert!(
        matches!(result, ExecuteResult::Counterexample { .. }),
        "expected SAT with model for equality constraint, got: {:?}",
        result
    );
}
