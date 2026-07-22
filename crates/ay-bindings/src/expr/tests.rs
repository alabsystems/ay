// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Tests for AY expression module.

use super::*;
use crate::memory::POINTER_WIDTH;
use crate::sort::Sort;
use crate::test_fixtures::{option_i32_sort, point_sort};

// ===== Helper Function Tests =====

#[test]
fn test_all_ones_literal_multiples_of_4() {
    // Multiples of 4 use hex format
    assert_eq!(all_ones_literal(4), "#xf");
    assert_eq!(all_ones_literal(8), "#xff");
    assert_eq!(all_ones_literal(16), "#xffff");
    assert_eq!(all_ones_literal(32), "#xffffffff");
}

#[test]
fn test_all_ones_literal_non_multiples_of_4() {
    // Non-multiples of 4 use binary format (#b...)
    assert_eq!(all_ones_literal(1), "#b1");
    assert_eq!(all_ones_literal(2), "#b11");
    assert_eq!(all_ones_literal(3), "#b111");
    assert_eq!(all_ones_literal(5), "#b11111");
    assert_eq!(all_ones_literal(9), "#b111111111");
}

#[test]
fn test_all_ones_literal_128bit() {
    assert_eq!(all_ones_literal(128), "#xffffffffffffffffffffffffffffffff");
}

#[test]
fn test_all_ones_literal_129bit() {
    // 129 bits is not multiple of 4, uses binary format
    let result = all_ones_literal(129);
    assert!(result.starts_with("#b"));
    assert_eq!(result.len(), 2 + 129);
    assert!(result[2..].chars().all(|c| c == '1'));
}

#[test]
fn test_all_ones_literal_256bit() {
    let result = all_ones_literal(256);
    assert_eq!(result.len(), 2 + 64); // "#x" + 64 hex digits
                                      // All f's
    for c in result[2..].chars() {
        assert_eq!(c, 'f');
    }
}

#[test]
fn test_int_min_literal_multiples_of_4() {
    // Multiples of 4 use hex format
    assert_eq!(int_min_literal(4), "#x8");
    assert_eq!(int_min_literal(8), "#x80");
    assert_eq!(int_min_literal(16), "#x8000");
    assert_eq!(int_min_literal(32), "#x80000000");
}

#[test]
fn test_int_min_literal_non_multiples_of_4() {
    // Non-multiples of 4 use binary format (#b...)
    assert_eq!(int_min_literal(1), "#b1");
    assert_eq!(int_min_literal(2), "#b10");
    assert_eq!(int_min_literal(3), "#b100");
    assert_eq!(int_min_literal(5), "#b10000");
}

#[test]
fn test_int_min_literal_128bit() {
    assert_eq!(int_min_literal(128), "#x80000000000000000000000000000000");
}

#[test]
fn test_int_min_literal_256bit() {
    let result = int_min_literal(256);
    assert_eq!(result.len(), 2 + 64); // "#x" + 64 hex digits
    assert!(result.starts_with("#x8"));
    // Rest should be zeros
    for c in result[3..].chars() {
        assert_eq!(c, '0');
    }
}

#[test]
fn test_zero_literal_multiples_of_4() {
    // Multiples of 4 use hex format
    assert_eq!(zero_literal(4), "#x0");
    assert_eq!(zero_literal(8), "#x00");
    assert_eq!(zero_literal(16), "#x0000");
    assert_eq!(zero_literal(32), "#x00000000");
}

#[test]
fn test_zero_literal_non_multiples_of_4() {
    // Non-multiples of 4 use binary format (#b...)
    assert_eq!(zero_literal(1), "#b0");
    assert_eq!(zero_literal(2), "#b00");
    assert_eq!(zero_literal(3), "#b000");
    assert_eq!(zero_literal(5), "#b00000");
    assert_eq!(zero_literal(9), "#b000000000");
}

// ===== Expression Tests =====

#[test]
fn test_bool_constants() {
    assert!(Expr::true_().sort().is_bool());
    assert!(Expr::false_().sort().is_bool());
    assert_eq!(Expr::true_().to_string(), "true");
    assert_eq!(Expr::false_().to_string(), "false");
}

#[test]
fn test_bitvec_constants() {
    let x = Expr::bitvec_const(42i32, 32);
    assert!(x.sort().is_bitvec());
    assert_eq!(x.sort().bitvec_width(), Some(32));
    assert_eq!(x.to_string(), "#x0000002a");
}

#[test]
fn test_bitvec_constants_normalize_negative_and_out_of_range() {
    // Negative values are interpreted modulo 2^width.
    assert_eq!(Expr::bitvec_const(-1i32, 8).to_string(), "#xff");
    assert_eq!(Expr::bitvec_const(-1i32, 3).to_string(), "#b111");

    // Values that don't fit are truncated modulo 2^width.
    assert_eq!(Expr::bitvec_const(0x1ffu32, 8).to_string(), "#xff");
    assert_eq!(Expr::bitvec_const(0x1ffu32, 3).to_string(), "#b111");
}

/// Test Issue #197: bool-to-u8 cast pattern
/// This is the exact pattern that was failing: (ite bool 1-bit 1-bit) then zero_extend
#[test]
fn test_bool_to_u8_cast_pattern() {
    // Pattern: (ite bool_cond (1-bit true) (1-bit false)) -> zero_extend to u8
    let bool_cond = Expr::var("b", Sort::bool());

    // 1-bit bitvectors for true/false - these must be 1-bit, not 4-bit
    let one_bit = Expr::bitvec_const(1i32, 1);
    let zero_bit = Expr::bitvec_const(0i32, 1);

    // Verify 1-bit constants use binary format
    assert_eq!(one_bit.to_string(), "#b1");
    assert_eq!(zero_bit.to_string(), "#b0");

    // Create ite expression: if b then 1 else 0 (1-bit result)
    let ite_expr = Expr::ite(bool_cond, one_bit, zero_bit);
    assert_eq!(ite_expr.to_string(), "(ite b #b1 #b0)");
    assert_eq!(ite_expr.sort().bitvec_width(), Some(1));

    // Zero extend by 7 bits to get u8
    let extended = ite_expr.zero_extend(7);
    assert_eq!(extended.sort().bitvec_width(), Some(8));
    // The result should be a valid 8-bit bitvector
    assert!(extended.to_string().contains("zero_extend 7"));
}

#[test]
fn test_variables() {
    let x = Expr::var("x", Sort::bv32());
    assert!(x.sort().is_bitvec());
    assert_eq!(x.to_string(), "x");
}

#[test]
fn test_variable_with_colons() {
    // Rust identifiers with :: must be quoted for SMT-LIB2
    let var = Expr::var("test_function::local_1_0", Sort::bv32());
    assert_eq!(var.to_string(), "|test_function::local_1_0|");
}

#[test]
fn test_variable_with_colons_in_expression() {
    // Verify quoting works within larger expressions
    let x = Expr::var("module::x", Sort::bv32());
    let y = Expr::var("module::y", Sort::bv32());
    let sum = x.bvadd(y);
    assert_eq!(sum.to_string(), "(bvadd |module::x| |module::y|)");
}

#[test]
fn test_boolean_ops() {
    let a = Expr::var("a", Sort::bool());
    let b = Expr::var("b", Sort::bool());

    assert_eq!(a.clone().not().to_string(), "(not a)");
    assert_eq!(a.clone().and(b.clone()).to_string(), "(and a b)");
    assert_eq!(a.clone().or(b.clone()).to_string(), "(or a b)");
    assert_eq!(a.implies(b).to_string(), "(=> a b)");
}

#[test]
fn test_bitvec_ops() {
    let x = Expr::var("x", Sort::bv32());
    let y = Expr::var("y", Sort::bv32());

    assert_eq!(x.clone().bvadd(y.clone()).to_string(), "(bvadd x y)");
    assert_eq!(x.clone().bvsub(y.clone()).to_string(), "(bvsub x y)");
    assert_eq!(x.bvult(y).to_string(), "(bvult x y)");
}

#[test]
fn test_ite() {
    let c = Expr::var("c", Sort::bool());
    let x = Expr::var("x", Sort::bv32());
    let y = Expr::var("y", Sort::bv32());

    let ite = Expr::ite(c, x, y);
    assert!(ite.sort().is_bitvec());
    assert_eq!(ite.to_string(), "(ite c x y)");
}

#[test]
fn test_extract() {
    let x = Expr::var("x", Sort::bv32());
    let low_byte = x.extract(7, 0);
    assert_eq!(low_byte.sort().bitvec_width(), Some(8));
    assert_eq!(low_byte.to_string(), "((_ extract 7 0) x)");
}

#[test]
fn test_array_ops() {
    let mem = Expr::var("mem", Sort::memory());
    let addr = Expr::var("addr", Sort::bv64());
    let val = Expr::var("val", Sort::bv8());

    assert_eq!(
        mem.clone().select(addr.clone()).to_string(),
        "(select mem addr)"
    );
    assert_eq!(mem.store(addr, val).to_string(), "(store mem addr val)");
}

/// Test: pointer-width BitVec → Vec auto-coercion in array store.
/// When storing a pointer-width bitvec into an Array<_, Vec>, coerce to Vec{ptr, 0, 0}.
#[test]
fn test_array_store_vec_coercion() {
    let ptr_sort = Sort::bitvec(POINTER_WIDTH);
    // Use consistent field names with production code (fld_ptr/fld_len/fld_cap)
    let vec_sort = Sort::struct_type(
        "Vec",
        vec![
            ("fld_ptr".to_string(), ptr_sort.clone()),
            ("fld_len".to_string(), ptr_sort.clone()),
            ("fld_cap".to_string(), ptr_sort.clone()),
        ],
    );
    let arr_sort = Sort::array(ptr_sort.clone(), vec_sort);
    let arr = Expr::var("arr", arr_sort);
    let idx = Expr::var("idx", ptr_sort.clone());
    let ptr = Expr::var("ptr", ptr_sort);

    let stored = arr.store(idx, ptr).to_string();
    // Verify Vec_mk constructor is used
    assert!(stored.contains("Vec_mk"), "should use Vec_mk constructor");
    // Verify the pointer var is included
    assert!(stored.contains("ptr"), "should contain ptr variable");
    // Verify zero constants for len/cap (0x0000000000000000)
    assert!(
        stored.contains("#x0000000000000000"),
        "should have zero len/cap"
    );
}

/// Test: pointer-width BitVec → String auto-coercion in array store.
/// When storing a pointer-width bitvec into an Array<_, String>, coerce to String{ptr, 0, 0}.
#[test]
fn test_array_store_string_coercion() {
    let ptr_sort = Sort::bitvec(POINTER_WIDTH);
    // Use consistent field names with production code (fld_ptr/fld_len/fld_cap)
    let string_sort = Sort::struct_type(
        "String",
        vec![
            ("fld_ptr".to_string(), ptr_sort.clone()),
            ("fld_len".to_string(), ptr_sort.clone()),
            ("fld_cap".to_string(), ptr_sort.clone()),
        ],
    );
    let arr_sort = Sort::array(ptr_sort.clone(), string_sort);
    let arr = Expr::var("arr", arr_sort);
    let idx = Expr::var("idx", ptr_sort.clone());
    let ptr = Expr::var("ptr", ptr_sort);

    let stored = arr.store(idx, ptr).to_string();
    // Verify String_mk constructor is used
    assert!(
        stored.contains("String_mk"),
        "should use String_mk constructor"
    );
    // Verify the pointer var is included
    assert!(stored.contains("ptr"), "should contain ptr variable");
    // Verify zero constants for len/cap
    assert!(
        stored.contains("#x0000000000000000"),
        "should have zero len/cap"
    );
}

/// Test: Vec → BitVec auto-coercion in array store.
/// When storing a Vec into an Array<_, BitVec(ptr)>, coerce to fld_ptr selector.
#[test]
fn test_array_store_vec_to_bitvec_coercion() {
    let ptr_sort = Sort::bitvec(POINTER_WIDTH);
    let vec_sort = Sort::struct_type(
        "Vec",
        vec![
            ("fld_ptr".to_string(), ptr_sort.clone()),
            ("fld_len".to_string(), ptr_sort.clone()),
            ("fld_cap".to_string(), ptr_sort.clone()),
        ],
    );
    let arr_sort = Sort::array(ptr_sort.clone(), ptr_sort.clone());
    let arr = Expr::var("arr", arr_sort);
    let idx = Expr::var("idx", ptr_sort);
    let vec_val = Expr::var("vec_val", vec_sort);

    let stored = arr.store(idx, vec_val).to_string();
    assert!(stored.contains("fld_ptr"), "should select fld_ptr");
    assert!(stored.contains("vec_val"), "should select from vec_val");
    assert!(!stored.contains("Vec_mk"), "should not reconstruct Vec");
}

/// Test: String → BitVec auto-coercion in array store.
/// When storing a String into an Array<_, BitVec(ptr)>, coerce to fld_ptr selector.
#[test]
fn test_array_store_string_to_bitvec_coercion() {
    let ptr_sort = Sort::bitvec(POINTER_WIDTH);
    let string_sort = Sort::struct_type(
        "String",
        vec![
            ("fld_ptr".to_string(), ptr_sort.clone()),
            ("fld_len".to_string(), ptr_sort.clone()),
            ("fld_cap".to_string(), ptr_sort.clone()),
        ],
    );
    let arr_sort = Sort::array(ptr_sort.clone(), ptr_sort.clone());
    let arr = Expr::var("arr", arr_sort);
    let idx = Expr::var("idx", ptr_sort);
    let string_val = Expr::var("string_val", string_sort);

    let stored = arr.store(idx, string_val).to_string();
    assert!(stored.contains("fld_ptr"), "should select fld_ptr");
    assert!(
        stored.contains("string_val"),
        "should select from string_val"
    );
    assert!(
        !stored.contains("String_mk"),
        "should not reconstruct String"
    );
}

/// Test: non-pointer-width bitvec is NOT coerced to Vec (only pointer-width allowed).
#[test]
#[should_panic(expected = "matching element sort")]
fn test_array_store_vec_coercion_rejects_bv32() {
    let ptr_sort = Sort::bitvec(POINTER_WIDTH);
    let vec_sort = Sort::struct_type(
        "Vec",
        vec![
            ("fld_ptr".to_string(), ptr_sort.clone()),
            ("fld_len".to_string(), ptr_sort.clone()),
            ("fld_cap".to_string(), ptr_sort.clone()),
        ],
    );
    let arr_sort = Sort::array(ptr_sort.clone(), vec_sort);
    let arr = Expr::var("arr", arr_sort);
    let idx = Expr::var("idx", ptr_sort);
    let ptr32 = Expr::var("ptr32", Sort::bv32());

    // This should panic - only 64-bit bitvecs can be coerced to Vec
    let _ = arr.store(idx, ptr32);
}

/// Test: Non-Vec/String datatypes do NOT get auto-coercion.
/// A custom datatype with same structure should reject bitvec values.
#[test]
#[should_panic(expected = "matching element sort")]
fn test_array_store_no_coercion_for_custom_datatype() {
    let ptr_sort = Sort::bitvec(POINTER_WIDTH);
    // "MyStruct" is not Vec or String, so no coercion should happen
    let my_struct_sort = Sort::struct_type(
        "MyStruct",
        vec![
            ("fld_ptr".to_string(), ptr_sort.clone()),
            ("fld_len".to_string(), ptr_sort.clone()),
            ("fld_cap".to_string(), ptr_sort.clone()),
        ],
    );
    let arr_sort = Sort::array(ptr_sort.clone(), my_struct_sort);
    let arr = Expr::var("arr", arr_sort);
    let idx = Expr::var("idx", ptr_sort.clone());
    let ptr = Expr::var("ptr", ptr_sort);

    // This should panic - MyStruct doesn't get Vec/String coercion
    let _ = arr.store(idx, ptr);
}

/// Test: BitVec → Int auto-coercion in array store.
/// When storing a BitVec into an Array<_, Int>, coerce with bv2int.
#[test]
fn test_array_store_bitvec_to_int_coercion() {
    let idx_sort = Sort::bv32();
    let arr_sort = Sort::array(idx_sort.clone(), Sort::int());
    let arr = Expr::var("arr", arr_sort);
    let idx = Expr::var("idx", idx_sort);
    let bv_val = Expr::var("bv_val", Sort::bv32());

    let stored = arr.store(idx, bv_val).to_string();
    assert!(stored.contains("bv2int"), "should use bv2int coercion");
}

/// Test: Int → BitVec auto-coercion in array store.
/// When storing an Int into an Array<_, BitVec>, coerce with int2bv.
#[test]
fn test_array_store_int_to_bitvec_coercion() {
    let idx_sort = Sort::bv32();
    let elem_sort = Sort::bv32();
    let arr_sort = Sort::array(idx_sort.clone(), elem_sort);
    let arr = Expr::var("arr", arr_sort);
    let idx = Expr::var("idx", idx_sort);
    let int_val = Expr::var("int_val", Sort::int());

    let stored = arr.store(idx, int_val).to_string();
    assert!(stored.contains("int2bv"), "should use int2bv coercion");
}

#[test]
fn test_const_array_sort_and_display() {
    let value = Expr::bitvec_const(0u8, 8);
    let array = Expr::const_array(Sort::bv32(), value.clone());

    assert!(array.sort().is_array());
    let arr_sort = array.sort().array_sort().expect("const_array sort");
    assert_eq!(arr_sort.index_sort, Sort::bv32());
    assert_eq!(arr_sort.element_sort, value.sort().clone());
    assert_eq!(
        array.to_string(),
        "((as const (Array (_ BitVec 32) (_ BitVec 8))) #x00)"
    );
}

// ===== Overflow Check Tests =====

#[test]
fn test_unsigned_add_no_overflow() {
    let x = Expr::var("x", Sort::bv32());
    let y = Expr::var("y", Sort::bv32());

    let check = x.bvadd_no_overflow_unsigned(y);
    assert!(check.sort().is_bool());
    // Should expand to: (bvuge (bvadd x y) x)
    assert!(check.to_string().contains("bvuge"));
    assert!(check.to_string().contains("bvadd"));
}

#[test]
fn test_signed_add_no_overflow() {
    let x = Expr::var("x", Sort::bv32());
    let y = Expr::var("y", Sort::bv32());

    let check = x.bvadd_no_overflow_signed(y);
    assert!(check.sort().is_bool());
    // Should expand to complex signed overflow check
    assert!(check.to_string().contains("not"));
    assert!(check.to_string().contains("bvsge"));
    assert!(check.to_string().contains("bvslt"));
}

#[test]
fn test_unsigned_sub_no_underflow() {
    let x = Expr::var("x", Sort::bv32());
    let y = Expr::var("y", Sort::bv32());

    let check = x.bvsub_no_underflow_unsigned(y);
    assert!(check.sort().is_bool());
    // Should expand to: (bvuge x y)
    assert_eq!(check.to_string(), "(bvuge x y)");
}

#[test]
fn test_signed_sub_no_overflow() {
    let x = Expr::var("x", Sort::bv32());
    let y = Expr::var("y", Sort::bv32());

    let check = x.bvsub_no_overflow_signed(y);
    assert!(check.sort().is_bool());
    // Should contain signed comparison and subtraction
    assert!(check.to_string().contains("bvsub"));
}

#[test]
fn test_unsigned_mul_no_overflow() {
    let x = Expr::var("x", Sort::bv32());
    let y = Expr::var("y", Sort::bv32());

    let check = x.bvmul_no_overflow_unsigned(y);
    assert!(check.sort().is_bool());
    // Should use zero_extend and extract
    assert!(check.to_string().contains("zero_extend"));
    assert!(check.to_string().contains("extract"));
}

#[test]
fn test_signed_mul_no_overflow() {
    let x = Expr::var("x", Sort::bv32());
    let y = Expr::var("y", Sort::bv32());

    let check = x.bvmul_no_overflow_signed(y);
    assert!(check.sort().is_bool());
    // Should use sign_extend
    assert!(check.to_string().contains("sign_extend"));
}

#[test]
fn test_neg_no_overflow() {
    let x = Expr::var("x", Sort::bitvec(8));

    let check = x.bvneg_no_overflow();
    assert!(check.sort().is_bool());
    // Should check x != INT_MIN (0x80 for 8-bit)
    let output = check.to_string();
    safe_eprintln!("neg_no_overflow output: {}", output);
    assert!(output.contains("not"));
    // The hex value should be 80 (which is INT_MIN for 8-bit)
    assert!(
        output.contains("80") || output.contains("0x80"),
        "Expected INT_MIN check, got: {output}"
    );
}

#[test]
fn test_overflow_check_8bit() {
    // Test with different bit widths
    let x = Expr::var("x", Sort::bitvec(8));
    let y = Expr::var("y", Sort::bitvec(8));

    let check = x.bvadd_no_overflow_unsigned(y);
    assert!(check.sort().is_bool());
}

#[test]
fn test_overflow_check_64bit() {
    let x = Expr::var("x", Sort::bv64());
    let y = Expr::var("y", Sort::bv64());

    let check = x.bvmul_no_overflow_unsigned(y);
    assert!(check.sort().is_bool());
    // Should handle 64-bit properly with 128-bit intermediate
    assert!(check.to_string().contains("zero_extend 64"));
}

/// Test 128-bit signed mul overflow - this was previously broken due to u128 overflow.
/// See issue #75.
#[test]
fn test_signed_mul_no_overflow_128bit() {
    let x = Expr::var("x", Sort::bitvec(128));
    let y = Expr::var("y", Sort::bitvec(128));

    // This should not panic - previously would overflow on (1u128 << 129) - 1
    let check = x.bvmul_no_overflow_signed(y);
    assert!(check.sort().is_bool());

    let output = check.to_string();
    // Should contain sign_extend 128 (extending 128-bit to 256-bit)
    assert!(
        output.contains("sign_extend 128"),
        "Expected sign_extend 128, got: {output}"
    );
    // Should contain the all-ones constant for 129 bits using binary format.
    let all_ones_129 = all_ones_literal(129);
    assert!(
        output.contains(&all_ones_129),
        "Expected 129-bit all-ones literal, got: {output}"
    );
}

/// Test 128-bit negation overflow - ensure INT_MIN is correctly generated.
#[test]
fn test_neg_no_overflow_128bit() {
    let x = Expr::var("x", Sort::bitvec(128));

    let check = x.bvneg_no_overflow();
    assert!(check.sort().is_bool());

    let output = check.to_string();
    // INT_MIN for 128-bit: 0x80000000000000000000000000000000 (32 hex digits)
    assert!(
        output.contains("80000000000000000000000000000000"),
        "Expected 128-bit INT_MIN, got: {output}"
    );
}

// ===== bv2int_signed Tests (Part of #911) =====

#[test]
fn test_bv2int_signed_sort() {
    // bv2int_signed should produce Int sort
    let x = Expr::var("x", Sort::bv32());
    let as_int = x.bv2int_signed();
    assert!(
        as_int.sort().is_int(),
        "bv2int_signed should produce Int sort"
    );
}

#[test]
fn test_bv2int_signed_encoding() {
    // bv2int_signed uses ITE on MSB
    let x = Expr::var("x", Sort::bitvec(8));
    let as_int = x.bv2int_signed();
    let output = as_int.to_string();

    // Should contain ITE (if-then-else), extract (for MSB), and bv2int
    assert!(
        output.contains("ite"),
        "Expected ITE in bv2int_signed, got: {output}"
    );
    assert!(
        output.contains("extract"),
        "Expected extract for MSB, got: {output}"
    );
    assert!(output.contains("bv2int"), "Expected bv2int, got: {output}");
}

#[test]
fn test_bv2int_signed_128bit() {
    // Test 128-bit conversion - should use BigInt for 2^128
    let x = Expr::var("x", Sort::bitvec(128));
    let as_int = x.bv2int_signed();
    assert!(as_int.sort().is_int());

    let output = as_int.to_string();
    // Should contain the large constant for 2^128
    assert!(
        output.contains("ite"),
        "Expected ITE in 128-bit conversion, got: {output}"
    );
}

// ===== int2bv conversion tests (#1137) =====

#[test]
fn test_int2bv_sort() {
    // int2bv should produce BitVec sort of specified width
    let x = Expr::var("x", Sort::int());
    let as_bv = x.int2bv(32);
    assert!(
        as_bv.sort().is_bitvec(),
        "int2bv should produce BitVec sort"
    );
    assert_eq!(
        as_bv.sort().bitvec_width(),
        Some(32),
        "int2bv(32) should produce 32-bit BV"
    );
}

#[test]
fn test_int2bv_encoding() {
    // int2bv should produce correct SMT-LIB2 encoding: ((_ int2bv w) expr)
    let x = Expr::var("x", Sort::int());
    let as_bv = x.int2bv(32);
    let output = as_bv.to_string();

    // Verify exact SMT-LIB format
    assert_eq!(
        output, "((_ int2bv 32) x)",
        "Expected exact SMT-LIB format, got: {output}"
    );
}

#[test]
fn test_int2bv_with_constant() {
    // Test int2bv with an integer constant
    let int_val = Expr::int_const(1000);
    let as_bv = int_val.int2bv(16);
    let output = as_bv.to_string();

    // Should encode as ((_ int2bv 16) 1000)
    assert!(
        output.contains("int2bv 16"),
        "Expected int2bv 16 in output, got: {output}"
    );
    assert!(
        output.contains("1000"),
        "Expected constant 1000 in output, got: {output}"
    );
}

#[test]
fn test_int2bv_with_negative_constant() {
    // Test int2bv with a negative integer constant
    // In SMT-LIB, ((_ int2bv 8) -1) produces #xFF (all ones)
    let neg_val = Expr::int_const(-1);
    let as_bv = neg_val.int2bv(8);
    let output = as_bv.to_string();

    // Should encode the negative value - SMT solver handles modular arithmetic
    assert!(
        output.contains("int2bv 8"),
        "Expected int2bv 8, got: {output}"
    );
    assert!(
        output.contains("-1") || output.contains("(- 1)"),
        "Expected -1 in output, got: {output}"
    );
}

#[test]
fn test_int2bv_different_widths() {
    // Test various widths
    let x = Expr::var("x", Sort::int());

    let bv8 = x.clone().int2bv(8);
    assert_eq!(bv8.sort().bitvec_width(), Some(8));

    let bv64 = x.clone().int2bv(64);
    assert_eq!(bv64.sort().bitvec_width(), Some(64));

    let bv128 = x.int2bv(128);
    assert_eq!(bv128.sort().bitvec_width(), Some(128));
}

#[test]
fn test_int2bv_round_trip_format() {
    // Test that bv2int and int2bv compose correctly in SMT-LIB format
    let bv = Expr::var("bv", Sort::bv32());
    let as_int = bv.bv2int();
    let back_to_bv = as_int.int2bv(32);

    let output = back_to_bv.to_string();
    assert!(output.contains("int2bv"), "Expected int2bv, got: {output}");
    assert!(output.contains("bv2int"), "Expected bv2int, got: {output}");
}

/// Test wider than 128-bit (e.g., 256-bit) to ensure string-based generation works.
#[test]
fn test_signed_mul_no_overflow_256bit() {
    let x = Expr::var("x", Sort::bitvec(256));
    let y = Expr::var("y", Sort::bitvec(256));

    // Should not panic even for very wide bitvectors
    let check = x.bvmul_no_overflow_signed(y);
    assert!(check.sort().is_bool());

    let output = check.to_string();
    // Should contain sign_extend 256
    assert!(
        output.contains("sign_extend 256"),
        "Expected sign_extend 256, got: {output}"
    );
}

/// Test 256-bit negation overflow.
#[test]
fn test_neg_no_overflow_256bit() {
    let x = Expr::var("x", Sort::bitvec(256));

    // Should not panic
    let check = x.bvneg_no_overflow();
    assert!(check.sort().is_bool());

    let output = check.to_string();
    // INT_MIN for 256-bit starts with 8 and has 63 zeros (64 hex digits total)
    // The high nibble is 8, followed by 63 zeros
    assert!(output.contains("#x8"), "Expected INT_MIN to start with 8");
    // Count that it's the right length (64 hex digits for 256 bits)
    let hex_start = output.find("#x").unwrap();
    let hex_end = output[hex_start..].find(')').unwrap() + hex_start;
    let hex_literal = &output[hex_start..hex_end];
    // #x + 64 hex digits = 66 chars
    assert_eq!(
        hex_literal.len(),
        66,
        "Expected 64 hex digits for 256-bit, got: {hex_literal}"
    );
}

/// Test signed division overflow check.
/// The only case where signed division can overflow is INT_MIN / -1.
#[test]
fn test_signed_div_no_overflow() {
    let x = Expr::var("x", Sort::bv32());
    let y = Expr::var("y", Sort::bv32());

    let check = x.bvsdiv_no_overflow(y);
    assert!(check.sort().is_bool());

    let output = check.to_string();
    // Should check: !(x == INT_MIN && y == -1)
    // INT_MIN for 32-bit is 0x80000000, -1 is 0xFFFFFFFF
    assert!(output.contains("not"), "Expected 'not' in output: {output}");
    assert!(output.contains("and"), "Expected 'and' in output: {output}");
    assert!(
        output.contains("80000000"),
        "Expected INT_MIN check in output: {output}"
    );
    assert!(
        output.contains("ffffffff"),
        "Expected -1 check in output: {output}"
    );
}

/// Test signed division overflow check with 8-bit values.
#[test]
fn test_signed_div_no_overflow_8bit() {
    let x = Expr::var("x", Sort::bitvec(8));
    let y = Expr::var("y", Sort::bitvec(8));

    let check = x.bvsdiv_no_overflow(y);
    assert!(check.sort().is_bool());

    let output = check.to_string();
    // INT_MIN for 8-bit is 0x80, -1 is 0xFF
    assert!(
        output.contains("#x80"),
        "Expected 8-bit INT_MIN in output: {output}"
    );
    assert!(
        output.contains("#xff"),
        "Expected 8-bit -1 in output: {output}"
    );
}

/// Test signed division overflow check with 128-bit values.
/// Ensures no overflow in literal generation for large bit widths.
#[test]
fn test_signed_div_no_overflow_128bit() {
    let x = Expr::var("x", Sort::bitvec(128));
    let y = Expr::var("y", Sort::bitvec(128));

    // Should not panic
    let check = x.bvsdiv_no_overflow(y);
    assert!(check.sort().is_bool());

    let output = check.to_string();
    // INT_MIN for 128-bit: 0x80000000000000000000000000000000 (32 hex digits)
    assert!(
        output.contains("80000000000000000000000000000000"),
        "Expected 128-bit INT_MIN in output: {output}"
    );
    // -1 for 128-bit: 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF (32 hex digits, all f's)
    assert!(
        output.contains("ffffffffffffffffffffffffffffffff"),
        "Expected 128-bit -1 in output: {output}"
    );
}

/// Test signed division overflow check with 256-bit values.
#[test]
fn test_signed_div_no_overflow_256bit() {
    let x = Expr::var("x", Sort::bitvec(256));
    let y = Expr::var("y", Sort::bitvec(256));

    // Should not panic even for very wide bitvectors
    let check = x.bvsdiv_no_overflow(y);
    assert!(check.sort().is_bool());

    let output = check.to_string();
    // INT_MIN for 256-bit starts with 8 followed by 63 zeros
    assert!(
        output.contains("#x8"),
        "Expected INT_MIN to start with 8 in output: {output}"
    );
    // -1 for 256-bit: all f's (64 hex digits)
    // Count f's to verify length
    let f_count = output.matches('f').count();
    assert!(
        f_count >= 64,
        "Expected at least 64 f's for 256-bit -1, got {f_count}"
    );
}

/// Test signed division overflow with non-multiple-of-4 bit width (7-bit).
/// Uses binary format for literals.
#[test]
fn test_signed_div_no_overflow_7bit() {
    let x = Expr::var("x", Sort::bitvec(7));
    let y = Expr::var("y", Sort::bitvec(7));

    let check = x.bvsdiv_no_overflow(y);
    assert!(check.sort().is_bool());

    let output = check.to_string();
    // INT_MIN for 7-bit in binary: #b1000000 (sign bit = 1, rest = 0)
    assert!(
        output.contains("#b1000000"),
        "Expected 7-bit INT_MIN in output: {output}"
    );
    // -1 for 7-bit in binary: #b1111111 (all 1s)
    assert!(
        output.contains("#b1111111"),
        "Expected 7-bit -1 in output: {output}"
    );
}

// ===== Datatype Operation Tests =====

#[test]
fn test_datatype_constructor_struct() {
    // Use shared Point fixture (#1144)
    let ps = point_sort();

    // Construct a Point: (Point_mk 1 2)
    // Note: Sort::struct_type uses "{name}_mk" as the constructor name
    let point = Expr::datatype_constructor(
        "Point",
        "Point_mk",
        vec![Expr::bitvec_const(1, 32), Expr::bitvec_const(2, 32)],
        ps,
    );

    assert!(point.sort().is_datatype());
    assert_eq!(point.to_string(), "(Point_mk #x00000001 #x00000002)");
}

#[test]
fn test_datatype_constructor_no_args() {
    // Unit-like struct: qualified form even for nullary constructors (#3362)
    // Note: Sort::struct_type uses "{name}_mk" as the constructor name
    let unit_sort = Sort::struct_type("Unit", Vec::<(&str, Sort)>::new());
    let unit = Expr::datatype_constructor("Unit", "Unit_mk", vec![], unit_sort);

    assert!(unit.sort().is_datatype());
    assert_eq!(unit.to_string(), "(as Unit_mk Unit)");
}

#[test]
fn test_datatype_field_select() {
    // Use shared Point fixture (#1144)
    let p = Expr::var("p", point_sort());

    // Select x field: (x p)
    // Note: Selector names match field names declared in datatype ("x", not "get-x")
    let x = p.field_select("Point", "x", Sort::bv32());

    assert!(x.sort().is_bitvec());
    assert_eq!(x.to_string(), "(x p)");
}

#[test]
fn test_datatype_is_constructor() {
    // Use shared Option fixture (#1144)
    let opt = Expr::var("opt", option_i32_sort());

    // Test if it's Some: Z3's (_ is ...) tester uses bare constructor name.
    let is_some = opt.is_constructor("Option", "Some");

    assert!(is_some.sort().is_bool());
    assert_eq!(is_some.to_string(), "((_ is Some) opt)");
}

#[test]
fn test_datatype_enum_variant() {
    // Use shared Option fixture (#1144)
    let some_42 = Expr::datatype_constructor(
        "Option",
        "Some",
        vec![Expr::bitvec_const(42, 32)],
        option_i32_sort(),
    );

    assert!(some_42.sort().is_datatype());
    assert_eq!(some_42.to_string(), "(Some #x0000002a)");
}

#[test]
fn test_datatype_nullary_constructor_qualified() {
    // Nullary constructors also use qualified form (#3362)
    let none = Expr::datatype_constructor("Option", "None", vec![], option_i32_sort());
    assert_eq!(none.to_string(), "(as None Option)");
}

// ===== Integer Operation Tests =====

#[test]
fn test_int_constants() {
    let x = Expr::int_const(42);
    assert!(x.sort().is_int());
    assert_eq!(x.to_string(), "42");

    let shorthand = Expr::int(7);
    assert!(shorthand.sort().is_int());
    assert_eq!(shorthand.to_string(), "7");

    let neg = Expr::int_const(-123);
    assert_eq!(neg.to_string(), "-123");
}

#[test]
fn test_int_arithmetic() {
    let x = Expr::var("x", Sort::int());
    let y = Expr::var("y", Sort::int());

    assert_eq!(x.clone().int_add(y.clone()).to_string(), "(+ x y)");
    assert_eq!(x.clone().int_sub(y.clone()).to_string(), "(- x y)");
    assert_eq!(x.clone().int_mul(y.clone()).to_string(), "(* x y)");
    assert_eq!(x.clone().int_div(y.clone()).to_string(), "(div x y)");
    assert_eq!(x.clone().int_mod(y).to_string(), "(mod x y)");
    assert_eq!(x.int_neg().to_string(), "(- x)");
}

#[test]
fn test_int_comparisons() {
    let x = Expr::var("x", Sort::int());
    let y = Expr::var("y", Sort::int());

    let lt = x.clone().int_lt(y.clone());
    assert!(lt.sort().is_bool());
    assert_eq!(lt.to_string(), "(< x y)");

    assert_eq!(x.clone().int_le(y.clone()).to_string(), "(<= x y)");
    assert_eq!(x.clone().int_gt(y.clone()).to_string(), "(> x y)");
    assert_eq!(x.int_ge(y).to_string(), "(>= x y)");
}

// ===== Real Conversion Tests =====

#[test]
fn test_real_to_int_display_and_sort() {
    let r = Expr::var("r", Sort::real());
    let i = r.real_to_int();
    assert!(i.sort().is_int());
    assert_eq!(i.to_string(), "(to_int r)");
}

#[test]
fn test_is_int_display_and_sort() {
    let r = Expr::var("r", Sort::real());
    let p = r.is_int();
    assert!(p.sort().is_bool());
    assert_eq!(p.to_string(), "(is_int r)");
}

// ===== Quantifier Tests =====

#[test]
fn test_forall() {
    let body = Expr::var("x", Sort::int()).int_ge(Expr::int_const(0));
    let forall = Expr::forall(vec![("x".into(), Sort::int())], body);

    assert!(forall.sort().is_bool());
    assert_eq!(forall.to_string(), "(forall ((x Int) ) (>= x 0))");
}

#[test]
fn test_exists() {
    let body = Expr::var("x", Sort::bv32()).eq(Expr::bitvec_const(42, 32));
    let exists = Expr::exists(vec![("x".into(), Sort::bv32())], body);

    assert!(exists.sort().is_bool());
    assert!(exists.to_string().contains("exists"));
    assert!(exists.to_string().contains("(_ BitVec 32)"));
}

#[test]
fn test_forall_multiple_vars() {
    let x = Expr::var("x", Sort::int());
    let y = Expr::var("y", Sort::int());
    let body = x.int_lt(y);
    let forall = Expr::forall(
        vec![("x".into(), Sort::int()), ("y".into(), Sort::int())],
        body,
    );

    assert!(forall.sort().is_bool());
    let output = forall.to_string();
    assert!(output.contains("forall"));
    assert!(output.contains("(x Int)"));
    assert!(output.contains("(y Int)"));
}

#[test]
fn test_forall_with_triggers() {
    let x = Expr::var("x", Sort::int());
    let fx = Expr::func_app_with_sort("f", vec![x], Sort::int());
    let trigger = vec![fx.clone()];
    let body = fx.int_gt(Expr::int_const(0));
    let q = Expr::forall_with_triggers(vec![("x".to_string(), Sort::int())], body, vec![trigger]);
    assert!(q.sort().is_bool());
    assert_eq!(
        q.to_string(),
        "(forall ((x Int) ) (! (> (f x) 0) :pattern ((f x))))"
    );
}

#[test]
fn test_forall_multi_trigger_groups() {
    // Multiple :pattern groups (disjunctive triggers)
    let x = Expr::var("x", Sort::int());
    let fx = Expr::func_app_with_sort("f", vec![x.clone()], Sort::int());
    let gx = Expr::func_app_with_sort("g", vec![x], Sort::int());
    let body = fx.clone().int_gt(gx.clone());
    let q = Expr::forall_with_triggers(
        vec![("x".to_string(), Sort::int())],
        body,
        vec![vec![fx], vec![gx]],
    );
    assert_eq!(
        q.to_string(),
        "(forall ((x Int) ) (! (> (f x) (g x)) :pattern ((f x)) :pattern ((g x))))"
    );
}

#[test]
fn test_forall_multi_term_trigger() {
    // Single :pattern with multiple terms (conjunctive multi-trigger)
    let x = Expr::var("x", Sort::int());
    let fx = Expr::func_app_with_sort("f", vec![x.clone()], Sort::int());
    let gx = Expr::func_app_with_sort("g", vec![x], Sort::int());
    let body = fx.clone().int_gt(gx.clone());
    let q = Expr::forall_with_triggers(
        vec![("x".to_string(), Sort::int())],
        body,
        vec![vec![fx, gx]],
    );
    assert_eq!(
        q.to_string(),
        "(forall ((x Int) ) (! (> (f x) (g x)) :pattern ((f x) (g x))))"
    );
}

#[test]
fn test_exists_with_triggers() {
    let x = Expr::var("x", Sort::int());
    let gx = Expr::func_app_with_sort("g", vec![x], Sort::int());
    let trigger = vec![gx.clone()];
    let body = gx.eq(Expr::int_const(42));
    let q = Expr::exists_with_triggers(vec![("x".to_string(), Sort::int())], body, vec![trigger]);
    assert!(q.sort().is_bool());
    let s = q.to_string();
    assert_eq!(s, "(exists ((x Int) ) (! (= (g x) 42) :pattern ((g x))))");
}

#[test]
fn test_forall_no_triggers_unchanged() {
    // Verify that forall without triggers produces the same output as before
    let body = Expr::var("x", Sort::int()).int_ge(Expr::int_const(0));
    let q = Expr::forall_with_triggers(vec![("x".into(), Sort::int())], body, vec![]);
    let s = q.to_string();
    assert!(
        !s.contains(":pattern"),
        "empty triggers should not emit :pattern: {s}"
    );
    assert_eq!(s, "(forall ((x Int) ) (>= x 0))");
}

// ===== Function Application Tests (CHC support) =====

#[test]
fn test_func_app_nullary() {
    // Nullary function application should output just the name
    let app = Expr::func_app("error", vec![]);
    assert!(app.sort().is_bool());
    assert_eq!(app.to_string(), "error");
}

#[test]
fn test_func_app_unary() {
    // Unary function application: (state x)
    let x = Expr::var("x", Sort::int());
    let app = Expr::func_app("state", vec![x]);
    assert!(app.sort().is_bool());
    assert_eq!(app.to_string(), "(state x)");
}

#[test]
fn test_func_app_binary() {
    // Binary function application: (trans x y)
    let x = Expr::var("x", Sort::int());
    let y = Expr::var("y", Sort::int());
    let app = Expr::func_app("trans", vec![x, y]);
    assert!(app.sort().is_bool());
    assert_eq!(app.to_string(), "(trans x y)");
}

#[test]
fn test_func_app_with_sort() {
    // Function application with custom sort (non-Bool)
    let x = Expr::var("x", Sort::int());
    let app = Expr::func_app_with_sort("get_value", vec![x], Sort::int());
    assert!(app.sort().is_int());
    assert_eq!(app.to_string(), "(get_value x)");
}

// ===== Fallible (try_) API Tests =====

#[test]
fn test_try_bvadd_success() {
    let a = Expr::bitvec_const(1i32, 32);
    let b = Expr::bitvec_const(2i32, 32);
    let result = a.try_bvadd(b);
    assert!(result.is_ok());
    let sum = result.unwrap();
    assert!(sum.sort().is_bitvec());
    assert_eq!(sum.to_string(), "(bvadd #x00000001 #x00000002)");
}

#[test]
fn test_try_bvadd_sort_mismatch() {
    let a = Expr::bitvec_const(1i32, 32);
    let b = Expr::bitvec_const(2i32, 16);
    let result = a.try_bvadd(b);
    assert!(result.is_err());
    let err = result.unwrap_err();
    let msg = err.to_string();
    assert!(
        msg.contains("bvadd"),
        "error message should name the operation: {msg}"
    );
}

#[test]
fn test_try_bvadd_wrong_sort_type() {
    let a = Expr::int_const(1);
    let b = Expr::int_const(2);
    let result = a.try_bvadd(b);
    assert!(result.is_err());
}

#[test]
fn test_try_and_success() {
    let a = Expr::var("a", Sort::bool());
    let b = Expr::var("b", Sort::bool());
    let result = a.try_and(b);
    assert!(result.is_ok());
}

#[test]
fn test_try_and_wrong_sort() {
    let a = Expr::var("a", Sort::bool());
    let b = Expr::var("b", Sort::int());
    let result = a.try_and(b);
    assert!(result.is_err());
}

#[test]
fn test_try_eq_success() {
    let a = Expr::bitvec_const(1i32, 32);
    let b = Expr::bitvec_const(2i32, 32);
    let result = a.try_eq(b);
    assert!(result.is_ok());
    assert!(result.unwrap().sort().is_bool());
}

#[test]
fn test_try_eq_sort_mismatch() {
    let a = Expr::bitvec_const(1i32, 32);
    let b = Expr::int_const(1);
    let result = a.try_eq(b);
    assert!(result.is_err());
}

#[test]
fn test_try_ite_success() {
    let cond = Expr::var("c", Sort::bool());
    let t = Expr::bitvec_const(1i32, 32);
    let e = Expr::bitvec_const(0i32, 32);
    let result = Expr::try_ite(cond, t, e);
    assert!(result.is_ok());
    assert!(result.unwrap().sort().is_bitvec());
}

#[test]
fn test_try_ite_non_bool_condition() {
    let cond = Expr::var("c", Sort::int());
    let t = Expr::bitvec_const(1i32, 32);
    let e = Expr::bitvec_const(0i32, 32);
    let result = Expr::try_ite(cond, t, e);
    assert!(result.is_err());
}

#[test]
fn test_try_ite_branch_mismatch() {
    let cond = Expr::var("c", Sort::bool());
    let t = Expr::bitvec_const(1i32, 32);
    let e = Expr::int_const(0);
    let result = Expr::try_ite(cond, t, e);
    assert!(result.is_err());
}

#[test]
fn test_try_extract_success() {
    let bv = Expr::bitvec_const(0xFFu32, 32);
    let result = bv.try_extract(7, 0);
    assert!(result.is_ok());
    let extracted = result.unwrap();
    assert_eq!(extracted.sort().bitvec_width(), Some(8));
}

#[test]
fn test_try_extract_out_of_range() {
    let bv = Expr::bitvec_const(0xFFu32, 32);
    let result = bv.try_extract(32, 0); // high >= width
    assert!(result.is_err());
}

#[test]
fn test_try_extract_inverted_range() {
    let bv = Expr::bitvec_const(0xFFu32, 32);
    let result = bv.try_extract(0, 7); // high < low
    assert!(result.is_err());
}

/// development verifier census failure regression pin: a BitVec `extract` built over an
/// INT-sorted term must surface a `SortError` the embedder can fail closed on
/// (obligation -> Unknown/Unchecked) — NOT a process panic. The panicking
/// `Expr::extract` wrapper fed exactly this shape (an Int-modeled f128 bit
/// pattern, `extract(126, 0)`) aborted an entire whole-crate compiler_consumer compile
/// (exit 101). `try_extract` is the fallible builder embedders must use for
/// externally-sourced sorts; this pins its non-BV-sort error path.
#[test]
fn test_try_extract_int_sorted_term_errors_fail_closed_not_panic() {
    let int_term = Expr::int_const(42);
    match int_term.try_extract(126, 0) {
        Err(crate::SortError::Mismatch {
            operation,
            expected,
            actual,
        }) => {
            assert_eq!(operation, "extract");
            assert_eq!(expected, "BitVec");
            assert!(
                actual.contains("Int"),
                "actual sort should be Int, got {actual}"
            );
        }
        other => panic!("expected SortError::Mismatch for Int-sorted extract, got {other:?}"),
    }
}

/// Companion control for the census pin above: the SAME magnitude-bits shape
/// (`extract(126, 0)` — drop the sign bit of an IEEE-754 quad) over a
/// correctly BV(128)-sorted term succeeds with the exact result width.
#[test]
fn test_try_extract_bv128_magnitude_census_shape_ok() {
    let bv = Expr::var("f128_bits", Sort::bitvec(128));
    let magnitude = bv
        .try_extract(126, 0)
        .expect("extract on BitVec(128) must succeed");
    assert_eq!(magnitude.sort().bitvec_width(), Some(127));
}

/// The non-BV-sort error path of the remaining hand-written fallible BV
/// builders (same panic family as `extract`'s infallible wrapper): each must
/// return `Err`, never panic, on an Int-sorted operand.
#[test]
fn test_try_bv_builders_int_sorted_term_errors_not_panics() {
    assert!(Expr::int_const(1).try_zero_extend(8).is_err());
    assert!(Expr::int_const(1).try_sign_extend(8).is_err());
    assert!(Expr::int_const(1)
        .try_concat(Expr::bitvec_const(0u32, 8))
        .is_err());
    assert!(Expr::bitvec_const(0u32, 8)
        .try_concat(Expr::int_const(1))
        .is_err());
    assert!(Expr::int_const(1).try_bv2int_signed().is_err());
    // ...and the dual: int2bv on a BITVEC-sorted operand.
    assert!(Expr::bitvec_const(0u32, 8).try_int2bv(8).is_err());
}

#[test]
fn test_try_int_add_success() {
    let a = Expr::int_const(1);
    let b = Expr::int_const(2);
    let result = a.try_int_add(b);
    assert!(result.is_ok());
    assert!(result.unwrap().sort().is_int());
}

#[test]
fn test_try_int_add_wrong_sort() {
    let a = Expr::int_const(1);
    let b = Expr::bitvec_const(2i32, 32);
    let result = a.try_int_add(b);
    assert!(result.is_err());
}

#[test]
fn test_try_constraint_assert_success() {
    use crate::constraint::Constraint;
    let cond = Expr::var("x", Sort::bool());
    let result = Constraint::try_assert(cond);
    assert!(result.is_ok());
}

#[test]
fn test_try_constraint_assert_wrong_sort() {
    use crate::constraint::Constraint;
    let val = Expr::int_const(42);
    let result = Constraint::try_assert(val);
    assert!(result.is_err());
    let msg = result.unwrap_err().to_string();
    assert!(
        msg.contains("assert"),
        "error should name the operation: {msg}"
    );
    assert!(
        msg.contains("Bool"),
        "error should mention expected sort: {msg}"
    );
}

// ===== try_select tests =====

#[test]
fn test_try_select_success() {
    let arr = Expr::const_array(Sort::int(), Expr::bitvec_const(0, 32));
    let idx = Expr::int_const(5);
    let result = arr.try_select(idx);
    assert!(result.is_ok());
    assert!(result.unwrap().sort().is_bitvec());
}

#[test]
fn test_try_select_not_array() {
    let val = Expr::int_const(42);
    let idx = Expr::int_const(0);
    let result = val.try_select(idx);
    assert!(result.is_err());
    let msg = result.unwrap_err().to_string();
    assert!(
        msg.contains("select"),
        "error should name the operation: {msg}"
    );
    assert!(
        msg.contains("Array"),
        "error should mention expected sort: {msg}"
    );
}

#[test]
fn test_try_select_index_sort_mismatch() {
    let arr = Expr::const_array(Sort::int(), Expr::bitvec_const(0, 32));
    let bad_idx = Expr::bitvec_const(1, 8);
    let result = arr.try_select(bad_idx);
    assert!(result.is_err());
    let msg = result.unwrap_err().to_string();
    assert!(
        msg.contains("select"),
        "error should name the operation: {msg}"
    );
}

// ===== try_store tests =====

#[test]
fn test_try_store_success() {
    let arr = Expr::const_array(Sort::int(), Expr::bitvec_const(0, 32));
    let idx = Expr::int_const(5);
    let val = Expr::bitvec_const(99, 32);
    let result = arr.try_store(idx, val);
    assert!(result.is_ok());
    assert!(result.unwrap().sort().is_array());
}

#[test]
fn test_try_store_not_array() {
    let val = Expr::int_const(42);
    let idx = Expr::int_const(0);
    let elem = Expr::int_const(1);
    let result = val.try_store(idx, elem);
    assert!(result.is_err());
    let msg = result.unwrap_err().to_string();
    assert!(
        msg.contains("store"),
        "error should name the operation: {msg}"
    );
    assert!(
        msg.contains("Array"),
        "error should mention expected sort: {msg}"
    );
}

#[test]
fn test_try_store_index_sort_mismatch() {
    let arr = Expr::const_array(Sort::int(), Expr::bitvec_const(0, 32));
    let bad_idx = Expr::bitvec_const(1, 8);
    let val = Expr::bitvec_const(99, 32);
    let result = arr.try_store(bad_idx, val);
    assert!(result.is_err());
    let msg = result.unwrap_err().to_string();
    assert!(
        msg.contains("store"),
        "error should name the operation: {msg}"
    );
}

#[test]
fn test_try_store_value_sort_mismatch() {
    let arr = Expr::const_array(Sort::int(), Expr::bitvec_const(0, 32));
    let idx = Expr::int_const(0);
    let bad_val = Expr::var("b", Sort::bool());
    let result = arr.try_store(idx, bad_val);
    assert!(result.is_err());
    let msg = result.unwrap_err().to_string();
    assert!(
        msg.contains("store"),
        "error should name the operation: {msg}"
    );
}

// ===== try_const_array tests (#5786) =====

#[test]
fn test_try_const_array_success() {
    let val = Expr::bitvec_const(0, 32);
    let result = Expr::try_const_array(Sort::int(), val);
    assert!(result.is_ok());
    let arr = result.unwrap();
    assert!(arr.sort().is_array());
}

// ===== try_assert_labeled tests =====

#[test]
fn test_try_assert_labeled_success() {
    use crate::constraint::Constraint;
    let cond = Expr::var("x", Sort::bool());
    let result = Constraint::try_assert_labeled(cond, "label1");
    assert!(result.is_ok());
}

#[test]
fn test_try_assert_labeled_wrong_sort() {
    use crate::constraint::Constraint;
    let val = Expr::int_const(42);
    let result = Constraint::try_assert_labeled(val, "label1");
    assert!(result.is_err());
    let msg = result.unwrap_err().to_string();
    assert!(
        msg.contains("assert_labeled"),
        "error should name the operation: {msg}"
    );
    assert!(
        msg.contains("Bool"),
        "error should mention expected sort: {msg}"
    );
}
