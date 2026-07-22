// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV, conversion, sort, model, and regression tests for AY Solver API.

use num_bigint::BigInt;
use num_rational::BigRational;

use crate::api::model_parse::parse_model_str;
use crate::api::*;

// =========================================================================
// Bitvector overflow predicate tests (#1301)
// =========================================================================

#[test]
fn test_bvadd_no_overflow_unsigned() {
    // Unsigned: 0xFF + 0x01 overflows (wraps to 0x00)
    let mut solver = Solver::new(Logic::QfBv);

    let a = solver.declare_const("a", Sort::bitvec(8));
    let b = solver.declare_const("b", Sort::bitvec(8));

    // a = 0xFF, b = 0x01
    let ff = solver.bv_const(0xFF, 8);
    let one = solver.bv_const(1, 8);
    let a_eq = solver.eq(a, ff);
    solver.assert_term(a_eq);
    let b_eq = solver.eq(b, one);
    solver.assert_term(b_eq);

    // Assert no overflow - should be UNSAT since 0xFF + 1 = 0x100 overflows
    let no_ovfl = solver.bvadd_no_overflow(a, b, false);
    solver.assert_term(no_ovfl);

    assert!(solver.check_sat().is_unsat());
}

#[test]
fn test_bvadd_no_overflow_signed() {
    // Signed: 0x7F + 0x01 = 0x80 (127 + 1 = -128, overflow!)
    let mut solver = Solver::new(Logic::QfBv);

    let a = solver.declare_const("a", Sort::bitvec(8));
    let b = solver.declare_const("b", Sort::bitvec(8));

    // a = 0x7F (127), b = 0x01
    let max_pos = solver.bv_const(0x7F, 8);
    let one = solver.bv_const(1, 8);
    let a_eq = solver.eq(a, max_pos);
    solver.assert_term(a_eq);
    let b_eq = solver.eq(b, one);
    solver.assert_term(b_eq);

    // Assert no overflow - should be UNSAT since 127 + 1 overflows
    let no_ovfl = solver.bvadd_no_overflow(a, b, true);
    solver.assert_term(no_ovfl);

    assert!(solver.check_sat().is_unsat());
}

#[test]
fn test_bvadd_no_underflow_signed() {
    // Signed: 0x80 + 0xFF = 0x7F (-128 + -1 = 127, underflow!)
    let mut solver = Solver::new(Logic::QfBv);

    let a = solver.declare_const("a", Sort::bitvec(8));
    let b = solver.declare_const("b", Sort::bitvec(8));

    // a = 0x80 (-128), b = 0xFF (-1)
    let min_neg = solver.bv_const(-128i64, 8);
    let neg_one = solver.bv_const(-1i64, 8);
    let a_eq = solver.eq(a, min_neg);
    solver.assert_term(a_eq);
    let b_eq = solver.eq(b, neg_one);
    solver.assert_term(b_eq);

    // Assert no underflow - should be UNSAT since -128 + -1 underflows
    let no_udfl = solver.bvadd_no_underflow(a, b);
    solver.assert_term(no_udfl);

    assert!(solver.check_sat().is_unsat());
}

#[test]
fn test_bvadd_no_overflow_signed_combined() {
    // Combined check: bvadd_no_overflow_signed catches both directions.
    // Test 1: positive overflow (127 + 1)
    {
        let mut solver = Solver::new(Logic::QfBv);
        let a = solver.declare_const("a", Sort::bitvec(8));
        let b = solver.declare_const("b", Sort::bitvec(8));
        let max_pos = solver.bv_const(0x7F, 8);
        let one = solver.bv_const(1, 8);
        let a_eq = solver.eq(a, max_pos);
        let b_eq = solver.eq(b, one);
        solver.assert_term(a_eq);
        solver.assert_term(b_eq);
        let safe = solver.bvadd_no_overflow_signed(a, b);
        solver.assert_term(safe);
        assert!(solver.check_sat().is_unsat());
    }
    // Test 2: negative underflow (-128 + -1)
    {
        let mut solver = Solver::new(Logic::QfBv);
        let a = solver.declare_const("a", Sort::bitvec(8));
        let b = solver.declare_const("b", Sort::bitvec(8));
        let min_neg = solver.bv_const(-128i64, 8);
        let neg_one = solver.bv_const(-1i64, 8);
        let a_eq = solver.eq(a, min_neg);
        let b_eq = solver.eq(b, neg_one);
        solver.assert_term(a_eq);
        solver.assert_term(b_eq);
        let safe = solver.bvadd_no_overflow_signed(a, b);
        solver.assert_term(safe);
        assert!(solver.check_sat().is_unsat());
    }
    // Test 3: safe addition (1 + 1)
    {
        let mut solver = Solver::new(Logic::QfBv);
        let a = solver.declare_const("a", Sort::bitvec(8));
        let b = solver.declare_const("b", Sort::bitvec(8));
        let val_one = solver.bv_const(1, 8);
        let val_one2 = solver.bv_const(1, 8);
        let a_eq = solver.eq(a, val_one);
        let b_eq = solver.eq(b, val_one2);
        solver.assert_term(a_eq);
        solver.assert_term(b_eq);
        let safe = solver.bvadd_no_overflow_signed(a, b);
        solver.assert_term(safe);
        assert_eq!(solver.check_sat(), SolveResult::Sat);
    }
}

#[test]
fn test_bvsub_no_underflow_unsigned() {
    // Unsigned: 0x00 - 0x01 underflows (wraps to 0xFF)
    let mut solver = Solver::new(Logic::QfBv);

    let a = solver.declare_const("a", Sort::bitvec(8));
    let b = solver.declare_const("b", Sort::bitvec(8));

    // a = 0x00, b = 0x01
    let zero = solver.bv_const(0, 8);
    let one = solver.bv_const(1, 8);
    let a_eq = solver.eq(a, zero);
    solver.assert_term(a_eq);
    let b_eq = solver.eq(b, one);
    solver.assert_term(b_eq);

    // Assert no underflow - should be UNSAT since 0 - 1 underflows
    let no_udfl = solver.bvsub_no_underflow(a, b, false);
    solver.assert_term(no_udfl);

    assert!(solver.check_sat().is_unsat());
}

#[test]
fn test_bvneg_no_overflow() {
    // Negating MIN overflows: -(-128) = 128, but max is 127
    let mut solver = Solver::new(Logic::QfBv);

    let a = solver.declare_const("a", Sort::bitvec(8));

    // a = 0x80 (-128, MIN)
    let min = solver.bv_const(-128i64, 8);
    let a_eq = solver.eq(a, min);
    solver.assert_term(a_eq);

    // Assert no overflow - should be UNSAT since -MIN overflows
    let no_ovfl = solver.bvneg_no_overflow(a);
    solver.assert_term(no_ovfl);

    assert!(solver.check_sat().is_unsat());
}

#[test]
fn test_bvsdiv_no_overflow() {
    // MIN / -1 overflows: -128 / -1 = 128, but max is 127
    let mut solver = Solver::new(Logic::QfBv);

    let a = solver.declare_const("a", Sort::bitvec(8));
    let b = solver.declare_const("b", Sort::bitvec(8));

    // a = 0x80 (-128, MIN), b = 0xFF (-1)
    let min = solver.bv_const(-128i64, 8);
    let neg_one = solver.bv_const(-1i64, 8);
    let a_eq = solver.eq(a, min);
    solver.assert_term(a_eq);
    let b_eq = solver.eq(b, neg_one);
    solver.assert_term(b_eq);

    // Assert no overflow - should be UNSAT since MIN / -1 overflows
    let no_ovfl = solver.bvsdiv_no_overflow(a, b);
    solver.assert_term(no_ovfl);

    assert!(solver.check_sat().is_unsat());
}

#[test]
fn test_bvmul_no_overflow_unsigned() {
    // Unsigned: 0x10 * 0x10 = 0x100, overflows 8-bit
    let mut solver = Solver::new(Logic::QfBv);

    let a = solver.declare_const("a", Sort::bitvec(8));
    let b = solver.declare_const("b", Sort::bitvec(8));

    // a = 0x10 (16), b = 0x10 (16)
    let sixteen = solver.bv_const(16, 8);
    let a_eq = solver.eq(a, sixteen);
    solver.assert_term(a_eq);
    let b_eq = solver.eq(b, sixteen);
    solver.assert_term(b_eq);

    // Assert no overflow - should be UNSAT since 16 * 16 = 256 > 255
    let no_ovfl = solver.bvmul_no_overflow(a, b, false);
    solver.assert_term(no_ovfl);

    assert!(solver.check_sat().is_unsat());
}

#[test]
fn test_bvmul_signed_positive_overflow_vs_underflow() {
    // -1 * MIN = +128 for i8: this is signed overflow, not underflow.
    let mut overflow_solver = Solver::new(Logic::QfBv);
    let a = overflow_solver.declare_const("a", Sort::bitvec(8));
    let b = overflow_solver.declare_const("b", Sort::bitvec(8));
    let neg_one = overflow_solver.bv_const(-1i64, 8);
    let min = overflow_solver.bv_const(-128i64, 8);
    let a_eq = overflow_solver.eq(a, neg_one);
    overflow_solver.assert_term(a_eq);
    let b_eq = overflow_solver.eq(b, min);
    overflow_solver.assert_term(b_eq);
    let no_overflow = overflow_solver.bvmul_no_overflow(a, b, true);
    overflow_solver.assert_term(no_overflow);
    assert!(overflow_solver.check_sat().is_unsat());

    let mut underflow_solver = Solver::new(Logic::QfBv);
    let a = underflow_solver.declare_const("a", Sort::bitvec(8));
    let b = underflow_solver.declare_const("b", Sort::bitvec(8));
    let neg_one = underflow_solver.bv_const(-1i64, 8);
    let min = underflow_solver.bv_const(-128i64, 8);
    let a_eq = underflow_solver.eq(a, neg_one);
    underflow_solver.assert_term(a_eq);
    let b_eq = underflow_solver.eq(b, min);
    underflow_solver.assert_term(b_eq);
    let no_underflow = underflow_solver.bvmul_no_underflow(a, b);
    underflow_solver.assert_term(no_underflow);
    assert_eq!(underflow_solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_bvmul_signed_negative_underflow_vs_overflow() {
    // 2 * MIN = -256 for i8: this is signed underflow, not overflow.
    let mut underflow_solver = Solver::new(Logic::QfBv);
    let a = underflow_solver.declare_const("a", Sort::bitvec(8));
    let b = underflow_solver.declare_const("b", Sort::bitvec(8));
    let two = underflow_solver.bv_const(2, 8);
    let min = underflow_solver.bv_const(-128i64, 8);
    let a_eq = underflow_solver.eq(a, two);
    underflow_solver.assert_term(a_eq);
    let b_eq = underflow_solver.eq(b, min);
    underflow_solver.assert_term(b_eq);
    let no_underflow = underflow_solver.bvmul_no_underflow(a, b);
    underflow_solver.assert_term(no_underflow);
    assert!(underflow_solver.check_sat().is_unsat());

    let mut overflow_solver = Solver::new(Logic::QfBv);
    let a = overflow_solver.declare_const("a", Sort::bitvec(8));
    let b = overflow_solver.declare_const("b", Sort::bitvec(8));
    let two = overflow_solver.bv_const(2, 8);
    let min = overflow_solver.bv_const(-128i64, 8);
    let a_eq = overflow_solver.eq(a, two);
    overflow_solver.assert_term(a_eq);
    let b_eq = overflow_solver.eq(b, min);
    overflow_solver.assert_term(b_eq);
    let no_overflow = overflow_solver.bvmul_no_overflow(a, b, true);
    overflow_solver.assert_term(no_overflow);
    assert_eq!(overflow_solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_overflow_predicates_sat_cases() {
    // Test that non-overflowing operations return SAT
    let mut solver = Solver::new(Logic::QfBv);

    let a = solver.declare_const("a", Sort::bitvec(8));
    let b = solver.declare_const("b", Sort::bitvec(8));

    // Small positive values that don't overflow
    let five = solver.bv_const(5, 8);
    let three = solver.bv_const(3, 8);
    let a_eq = solver.eq(a, five);
    solver.assert_term(a_eq);
    let b_eq = solver.eq(b, three);
    solver.assert_term(b_eq);

    // All these should be SAT (no overflow/underflow)
    let add_no_ovfl = solver.bvadd_no_overflow(a, b, false);
    solver.assert_term(add_no_ovfl);
    let add_no_ovfl_s = solver.bvadd_no_overflow(a, b, true);
    solver.assert_term(add_no_ovfl_s);
    let sub_no_udfl = solver.bvsub_no_underflow(a, b, false);
    solver.assert_term(sub_no_udfl);
    let mul_no_ovfl = solver.bvmul_no_overflow(a, b, false);
    solver.assert_term(mul_no_ovfl);
    let neg_no_ovfl = solver.bvneg_no_overflow(a);
    solver.assert_term(neg_no_ovfl);
    let div_no_ovfl = solver.bvsdiv_no_overflow(a, b);
    solver.assert_term(div_no_ovfl);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

/// Test that Sort implements Hash and can be used in HashSet (#1438)
#[test]
fn test_sort_hash() {
    use ay_core::kani_compat::DetHashSet as HashSet;

    let mut sorts: HashSet<Sort> = HashSet::default();
    sorts.insert(Sort::Bool);
    sorts.insert(Sort::Int);
    sorts.insert(Sort::Real);
    sorts.insert(Sort::bitvec(32));
    sorts.insert(Sort::array(Sort::Int, Sort::Bool));
    sorts.insert(Sort::Uninterpreted("MySort".to_string()));
    sorts.insert(Sort::Datatype(DatatypeSort::new(
        "MyDatatype",
        vec![DatatypeConstructor::new(
            "Cons",
            vec![DatatypeField::new("head", Sort::Int)],
        )],
    )));

    assert_eq!(sorts.len(), 7);
    assert!(sorts.contains(&Sort::Bool));
    assert!(sorts.contains(&Sort::Int));
    assert!(sorts.contains(&Sort::bitvec(32)));
    assert!(!sorts.contains(&Sort::bitvec(64)));
}

// =========================================================================
// bv2int / int2bv tests
// =========================================================================

#[test]
fn test_bv2int_unsigned() {
    let mut solver = Solver::new(Logic::QfAufbv);

    // Create 8-bit bitvector 255 (0xFF)
    let bv = solver.bv_const(255, 8);
    let int_val = solver.bv2int(bv);

    // bv2int(0xFF) = 255
    let expected = solver.int_const(255);
    let eq = solver.eq(int_val, expected);
    solver.assert_term(eq);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_bv2int_signed_positive() {
    let mut solver = Solver::new(Logic::QfAufbv);

    // 8-bit bitvector 127 (0x7F) - max positive signed value
    let bv = solver.bv_const(127, 8);
    let int_val = solver.bv2int_signed(bv);

    // bv2int_signed(0x7F) = 127
    let expected = solver.int_const(127);
    let eq = solver.eq(int_val, expected);
    solver.assert_term(eq);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_bv2int_signed_negative() {
    let mut solver = Solver::new(Logic::QfAufbv);

    // 8-bit bitvector 255 (0xFF) interpreted as signed = -1
    let bv = solver.bv_const(-1i64, 8); // This creates 0xFF
    let int_val = solver.bv2int_signed(bv);

    // bv2int_signed(0xFF) = -1
    let expected = solver.int_const(-1);
    let eq = solver.eq(int_val, expected);
    solver.assert_term(eq);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_int2bv_positive() {
    let mut solver = Solver::new(Logic::QfAufbv);

    let int_val = solver.int_const(255);
    let bv = solver.int2bv(int_val, 8);

    // int2bv(255, 8) = 0xFF
    let expected = solver.bv_const(255, 8);
    let eq = solver.eq(bv, expected);
    solver.assert_term(eq);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_int2bv_negative_wraps() {
    let mut solver = Solver::new(Logic::QfAufbv);

    // int2bv(-1, 8) should wrap to 255 (0xFF) since -1 mod 256 = 255
    let int_val = solver.int_const(-1);
    let bv = solver.int2bv(int_val, 8);

    let expected = solver.bv_const(255, 8);
    let eq = solver.eq(bv, expected);
    solver.assert_term(eq);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_bv2int_int2bv_roundtrip() {
    let mut solver = Solver::new(Logic::QfAufbv);

    // For unsigned interpretation: int2bv(bv2int(x), w) = x (when x has width w)
    let x = solver.declare_const("x", Sort::bitvec(8));
    let as_int = solver.bv2int(x);
    let back = solver.int2bv(as_int, 8);

    // x == int2bv(bv2int(x), 8)
    let roundtrip_eq = solver.eq(x, back);
    solver.assert_term(roundtrip_eq);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_try_bv2int_rejects_non_bitvec() {
    let mut solver = Solver::new(Logic::QfLia);
    let int_val = solver.int_const(42);

    let result = solver.try_bv2int(int_val);
    assert!(matches!(result, Err(SolverError::SortMismatch { .. })));
}

#[test]
fn test_try_int2bv_rejects_non_int() {
    let mut solver = Solver::new(Logic::QfAufbv);
    let bv = solver.bv_const(42, 8);

    let result = solver.try_int2bv(bv, 8);
    assert!(matches!(result, Err(SolverError::SortMismatch { .. })));
}

// =========================================================================
// Int/Real conversion tests
// =========================================================================

#[test]
fn test_int_to_real() {
    let mut solver = Solver::new(Logic::QfLira);
    let i = solver.int_const(42);
    let r = solver.int_to_real(i);
    assert_eq!(solver.terms().sort(r.0), &Sort::Real);
}

#[test]
fn test_real_to_int() {
    let mut solver = Solver::new(Logic::QfLira);
    let r = solver.real_const(3.7);
    let i = solver.real_to_int(r);
    assert_eq!(solver.terms().sort(i.0), &Sort::Int);
}

#[test]
fn test_is_int() {
    let mut solver = Solver::new(Logic::QfLira);
    let r = solver.real_const(3.0);
    let b = solver.is_int(r);
    assert_eq!(solver.terms().sort(b.0), &Sort::Bool);
}

#[test]
fn test_try_int_to_real_rejects_non_int() {
    let mut solver = Solver::new(Logic::QfLira);
    let r = solver.real_var("r");

    let result = solver.try_int_to_real(r);
    assert!(matches!(result, Err(SolverError::SortMismatch { .. })));
}

#[test]
fn test_try_real_to_int_rejects_non_real() {
    let mut solver = Solver::new(Logic::QfLira);
    let i = solver.int_const(42);

    let result = solver.try_real_to_int(i);
    assert!(matches!(result, Err(SolverError::SortMismatch { .. })));
}

#[test]
fn test_try_is_int_rejects_non_real() {
    let mut solver = Solver::new(Logic::QfLira);
    let i = solver.int_const(42);

    let result = solver.try_is_int(i);
    assert!(matches!(result, Err(SolverError::SortMismatch { .. })));
}

/// Real comparison operations: `x > y ∧ y > x` must be UNSAT (#5405).
#[test]
fn test_real_comparison_gt_contradiction_not_sat_issue_1654() {
    let mut solver = Solver::new(Logic::QfLra);
    let x = solver.declare_const("x", Sort::Real);
    let y = solver.declare_const("y", Sort::Real);

    // x > y AND y > x is unsatisfiable
    let x_gt_y = solver.gt(x, y);
    let y_gt_x = solver.gt(y, x);
    solver.assert_term(x_gt_y);
    solver.assert_term(y_gt_x);

    let result = solver.check_sat();
    if result == SolveResult::Unknown {
        eprintln!(
            "BUG #5405: LRA returns Unknown for x>y ∧ y>x. Reason: {:?}, error: {:?}",
            solver.unknown_reason(),
            solver.executor_error()
        );
    }
    assert_eq!(
        result,
        SolveResult::unsat(),
        "x > y AND y > x must be UNSAT (#5405)"
    );
}

/// Test Real comparison with satisfying model (Issue #1654)
#[test]
fn test_real_comparison_gt_sat_issue_1654() {
    let mut solver = Solver::new(Logic::QfLra);
    let x = solver.declare_const("x", Sort::Real);
    let y = solver.declare_const("y", Sort::Real);

    // x > y with x = 5, y = 3 should be SAT
    let x_gt_y = solver.gt(x, y);
    let five = solver.real_const(5.0);
    let three = solver.real_const(3.0);
    let x_eq_5 = solver.eq(x, five);
    let y_eq_3 = solver.eq(y, three);

    solver.assert_term(x_gt_y);
    solver.assert_term(x_eq_5);
    solver.assert_term(y_eq_3);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let model = solver.model().expect("Expected model").into_inner();
    assert_eq!(model.real_val_f64("x"), Some(5.0));
    assert_eq!(model.real_val_f64("y"), Some(3.0));
}

#[test]
fn test_solve_result_convenience_methods() {
    // Test is_sat/is_unsat/is_unknown convenience methods
    assert!(SolveResult::Sat.is_sat());
    assert!(!SolveResult::Sat.is_unsat());
    assert!(!SolveResult::Sat.is_unknown());

    assert!(!SolveResult::unsat().is_sat());
    assert!(SolveResult::unsat().is_unsat());
    assert!(!SolveResult::unsat().is_unknown());

    assert!(!SolveResult::Unknown.is_sat());
    assert!(!SolveResult::Unknown.is_unsat());
    assert!(SolveResult::Unknown.is_unknown());
}

#[test]
fn test_solve_result_display() {
    // Test Display impl matches SMT-LIB output format
    assert_eq!(format!("{}", SolveResult::Sat), "sat");
    assert_eq!(format!("{}", SolveResult::unsat()), "unsat");
    assert_eq!(format!("{}", SolveResult::Unknown), "unknown");
}

#[test]
fn test_bvrotl_constant() {
    // Test bvrotl with constant input: rotate 0xa5 (10100101) left by 2 -> 0x96 (10010110)
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.bv_const(0xa5, 8);
    let rotated = solver.bvrotl(x, 2);
    let expected = solver.bv_const(0x96, 8);
    let eq = solver.eq(rotated, expected);
    solver.assert_term(eq);
    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_bvrotr_constant() {
    // Test bvrotr with constant input: rotate 0xa5 (10100101) right by 2 -> 0x69 (01101001)
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.bv_const(0xa5, 8);
    let rotated = solver.bvrotr(x, 2);
    let expected = solver.bv_const(0x69, 8);
    let eq = solver.eq(rotated, expected);
    solver.assert_term(eq);
    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_bvrotate_inverse() {
    // Rotating left then right by the same amount should be identity
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(16));
    let rotl3 = solver.bvrotl(x, 3);
    let rotr3 = solver.bvrotr(rotl3, 3);
    let eq = solver.eq(x, rotr3);
    solver.assert_term(eq);
    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_bvrotate_symbolic() {
    // Symbolic test: find x such that rotate_left(x, 1) = 0x02 (8-bit)
    // x = 0x01 is the solution (00000001 -> 00000010)
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(8));
    let rotated = solver.bvrotl(x, 1);
    let target = solver.bv_const(0x02, 8);
    let eq = solver.eq(rotated, target);
    solver.assert_term(eq);
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let model = solver.model().expect("Expected model").into_inner();
    let x_val = model.bv_val("x").expect("x should be in model");
    assert_eq!(x_val.0, BigInt::from(0x01));
}

#[test]
fn test_try_bvrotl_type_error() {
    // try_bvrotl should return error for non-bitvector input
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let result = solver.try_bvrotl(x, 2);
    assert!(result.is_err());
    if let Err(SolverError::SortMismatch { operation, .. }) = result {
        assert_eq!(operation, "bvrotl");
    } else {
        panic!("Expected SortMismatch error");
    }
}

#[test]
fn test_try_bvrotr_type_error() {
    // try_bvrotr should return error for non-bitvector input
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let result = solver.try_bvrotr(x, 2);
    assert!(result.is_err());
    if let Err(SolverError::SortMismatch { operation, .. }) = result {
        assert_eq!(operation, "bvrotr");
    } else {
        panic!("Expected SortMismatch error");
    }
}

#[test]
fn test_bvrotate_by_zero_is_identity() {
    // Rotating by 0 should be identity: rotl(x, 0) = x, rotr(x, 0) = x
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(16));

    // rotl(x, 0) = x
    let rotl0 = solver.bvrotl(x, 0);
    let eq_left = solver.eq(x, rotl0);
    solver.assert_term(eq_left);

    // rotr(x, 0) = x
    let rotr0 = solver.bvrotr(x, 0);
    let eq_right = solver.eq(x, rotr0);
    solver.assert_term(eq_right);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_bvrotate_by_width_is_identity() {
    // Rotating by full width should be identity: rotl(x, w) = x, rotr(x, w) = x
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(8));

    // rotl(x, 8) = x for 8-bit bitvector
    let rotl8 = solver.bvrotl(x, 8);
    let eq_left = solver.eq(x, rotl8);
    solver.assert_term(eq_left);

    // rotr(x, 8) = x for 8-bit bitvector
    let rotr8 = solver.bvrotr(x, 8);
    let eq_right = solver.eq(x, rotr8);
    solver.assert_term(eq_right);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_try_push_pop_success() {
    // Basic try_push and try_pop should succeed
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let gt_zero = solver.gt(x, zero);
    solver.assert_term(gt_zero);

    // Push should succeed
    assert!(solver.try_push().is_ok());

    // Assert contradiction in new scope
    let lt_zero = solver.lt(x, zero);
    solver.assert_term(lt_zero);
    assert!(solver.check_sat().is_unsat());

    // Pop should succeed
    assert!(solver.try_pop().is_ok());

    // After pop, should be satisfiable again
    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_try_reset_success() {
    // try_reset should clear all assertions
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let gt_zero = solver.gt(x, zero);
    let lt_zero = solver.lt(x, zero);

    // Assert contradiction
    solver.assert_term(gt_zero);
    solver.assert_term(lt_zero);
    assert!(solver.check_sat().is_unsat());

    // Reset should succeed
    assert!(solver.try_reset().is_ok());

    // After reset, need to re-declare and should be satisfiable
    let y = solver.declare_const("y", Sort::Int);
    let one = solver.int_const(1);
    let eq_one = solver.eq(y, one);
    solver.assert_term(eq_one);
    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_try_reset_clears_unknown_reason() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);

    // Non-Boolean assumptions degrade to Unknown with an explicit reason.
    assert_eq!(solver.check_sat_assuming(&[x]), SolveResult::Unknown);
    assert!(solver.unknown_reason().is_some());

    assert!(solver.try_reset().is_ok());
    assert_eq!(solver.unknown_reason(), None);
}

/// Regression test for #6740: try_reset must reset scope_level to 0.
#[test]
fn test_try_reset_clears_scope_level_6740() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let gt = solver.gt(x, zero);

    solver.try_push().unwrap();
    solver.try_push().unwrap();
    assert_eq!(solver.num_scopes(), 2);

    solver.assert_term(gt);
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    solver.try_reset().unwrap();
    assert_eq!(solver.num_scopes(), 0, "scope_level must be 0 after reset");
}

#[test]
fn test_try_declare_fun_success() {
    // try_declare_fun should succeed for valid declarations
    let mut solver = Solver::new(Logic::QfUflia);

    // Declare a unary function f: Int -> Int
    let result = solver.try_declare_fun("f", &[Sort::Int], Sort::Int);
    assert!(result.is_ok());

    let f = result.unwrap();
    assert_eq!(f.name, "f");
    assert_eq!(f.domain, vec![Sort::Int]);
    assert_eq!(f.range, Sort::Int);

    // Use the declared function
    let x = solver.declare_const("x", Sort::Int);
    let fx = solver.apply(&f, &[x]);
    let zero = solver.int_const(0);
    let eq = solver.eq(fx, zero);
    solver.assert_term(eq);
    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_model_iteration_methods() {
    let mut solver = Solver::new(Logic::QfLia);

    // Create multiple variables
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);

    let five = solver.int_const(5);
    let ten = solver.int_const(10);

    let eq_x = solver.eq(x, five);
    let eq_y = solver.eq(y, ten);
    solver.assert_term(eq_x);
    solver.assert_term(eq_y);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let model = solver.model().expect("Expected model").into_inner();

    // Test len and is_empty
    assert!(!model.is_empty());
    assert_eq!(model.len(), 2);

    // Test iter_ints
    let ints: Vec<_> = model.iter_ints().collect();
    assert_eq!(ints.len(), 2);
    assert!(ints
        .iter()
        .any(|(name, val)| *name == "x" && **val == BigInt::from(5)));
    assert!(ints
        .iter()
        .any(|(name, val)| *name == "y" && **val == BigInt::from(10)));
}

#[test]
fn test_get_model_str() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    // get_model_str should return the raw SMT-LIB model
    let model_str = solver.model_str().expect("Expected model string");
    assert!(model_str.contains("define-fun"));
    assert!(model_str.contains('x'));
}

#[test]
fn test_parse_model_str_handles_multiline_define_fun() {
    let model_str = r#"(model
  (define-fun x () Int
42)
)"#;

    let model = parse_model_str(model_str);
    assert_eq!(model.int_val_i64("x"), Some(42));
}

#[test]
fn test_parse_model_str_unquotes_define_fun_names() {
    let model_str = r#"(model
  (define-fun |foo::bar| () Int 7)
)"#;

    let model = parse_model_str(model_str);
    assert_eq!(model.int_val_i64("foo::bar"), Some(7));
    assert_eq!(model.int_val_i64("|foo::bar|"), None);
}

#[test]
fn test_parse_model_str_handles_nested_values() {
    let model_str = r#"(model
  (define-fun i () Int (- 5))
  (define-fun r () Real (/ (- 1) 3))
  (define-fun b () Bool true)
  (define-fun bv () (_ BitVec 8) (_ bv10 8))
)"#;

    let model = parse_model_str(model_str);
    assert_eq!(model.int_val_i64("i"), Some(-5));

    let r = model.real_val_f64("r").expect("expected r in model");
    assert!((r + (1.0 / 3.0)).abs() < 1e-9, "expected -1/3, got {r}");

    assert_eq!(model.bool_val("b"), Some(true));

    let bv = model.bv_val("bv").expect("expected bv in model");
    assert_eq!(bv.0, BigInt::from(10));
    assert_eq!(bv.1, 8);
}

#[test]
fn test_get_model_none_after_unsat() {
    let mut solver = Solver::new(Logic::QfUf);
    let a = solver.declare_const("a", Sort::Bool);
    let not_a = solver.not(a);
    solver.assert_term(a);
    solver.assert_term(not_a);

    assert!(solver.check_sat().is_unsat());
    assert!(solver.model().is_none());
    assert!(solver.model_str().is_none());
}

// =========================================================================
// Sort tests (#1437 - Sort type consolidation)
// =========================================================================

/// Test that Sort::as_term_sort() correctly canonicalizes Datatype to Uninterpreted.
///
/// For UF-only datatypes, as_term_sort() maps Datatype(dt) to Uninterpreted(dt.name)
/// to match the SMT-LIB elaborator behavior.
#[test]
fn test_sort_as_term_sort_datatype() {
    let dt = DatatypeSort::new(
        "Option",
        vec![
            DatatypeConstructor::unit("None"),
            DatatypeConstructor::new("Some", vec![DatatypeField::new("value", Sort::Int)]),
        ],
    );
    let sort = Sort::Datatype(dt);
    let term_sort = sort.as_term_sort();

    // Should convert to Uninterpreted for term store
    assert!(matches!(&term_sort, Sort::Uninterpreted(name) if name == "Option"));
}

/// Test Sort helper methods work correctly (#1437).
#[test]
fn test_sort_helpers() {
    // Test bitvec helper
    let bv = Sort::bitvec(32);
    assert_eq!(bv.bitvec_width(), Some(32));
    assert!(bv.is_bitvec());

    // Test array helper
    let arr = Sort::array(Sort::Int, Sort::Bool);
    assert!(arr.is_array());
    assert_eq!(arr.array_index(), Some(&Sort::Int));
    assert_eq!(arr.array_element(), Some(&Sort::Bool));

    // Test struct_type helper
    let s = Sort::struct_type("Point", [("x", Sort::Int), ("y", Sort::Int)]);
    assert!(s.is_datatype());
    if let Sort::Datatype(dt) = &s {
        assert_eq!(dt.name, "Point");
        assert_eq!(dt.constructors.len(), 1);
        assert_eq!(dt.constructors[0].fields.len(), 2);
    }

    // Test enum_type helper
    let e = Sort::enum_type("Color", ["Red", "Green", "Blue"]);
    assert!(e.is_datatype());
    if let Sort::Datatype(dt) = &e {
        assert_eq!(dt.name, "Color");
        assert_eq!(dt.constructors.len(), 3);
    }
}

#[test]
fn test_bv_const_bigint_large_value() {
    // Test a 128-bit bitvector with value 2^100
    let mut solver = Solver::new(Logic::QfBv);

    let large_val = BigInt::from(1) << 100;
    let bv128 = solver.bv_const_bigint(&large_val, 128);
    let x = solver.declare_const("x", Sort::bitvec(128));

    // x == 2^100 should be satisfiable
    let eq = solver.eq(x, bv128);
    solver.assert_term(eq);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_bv_const_bigint_vs_bv_const() {
    // Ensure bv_const_bigint produces the same result as bv_const for i64 values
    let mut solver = Solver::new(Logic::QfBv);

    let val = 42i64;
    let bv1 = solver.bv_const(val, 32);
    let bv2 = solver.bv_const_bigint(&BigInt::from(val), 32);

    // Both should be equal
    let eq = solver.eq(bv1, bv2);
    solver.assert_term(eq);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_rational_const_bigint_large_numerator() {
    // Test a rational with numerator exceeding i64
    let mut solver = Solver::new(Logic::QfLra);

    let big_numer = BigInt::from(i64::MAX) * 2;
    let denom = BigInt::from(1);
    let rat = solver.rational_const_bigint(&big_numer, &denom);
    let x = solver.declare_const("x", Sort::Real);

    // x == big_numer should be satisfiable
    let eq = solver.eq(x, rat);
    solver.assert_term(eq);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_rational_const_ratio() {
    // Test creating a rational from BigRational directly
    let mut solver = Solver::new(Logic::QfLra);

    let ratio = BigRational::new(BigInt::from(3), BigInt::from(4));
    let rat = solver.rational_const_ratio(&ratio);
    let x = solver.declare_const("x", Sort::Real);

    // x == 3/4 should be satisfiable
    let eq = solver.eq(x, rat);
    solver.assert_term(eq);

    // x > 0.5 should also hold
    let half = solver.rational_const(1, 2);
    let gt = solver.gt(x, half);
    solver.assert_term(gt);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_get_value_int() {
    // Test get_value returns correct Int values
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let val = solver.value(x);
    assert!(val.is_some(), "get_value should return value after SAT");
    let val = val.unwrap();
    assert_eq!(val, ModelValue::Int(BigInt::from(5)));
}

#[test]
fn test_get_value_bool() {
    // Test get_value returns correct Bool values
    let mut solver = Solver::new(Logic::QfUf);

    let p = solver.declare_const("p", Sort::Bool);
    solver.assert_term(p);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let val = solver.value(p);
    assert!(val.is_some());
    assert_eq!(val.unwrap(), ModelValue::Bool(true));
}

#[test]
fn test_get_value_bv() {
    // Test get_value returns correct BitVec values
    let mut solver = Solver::new(Logic::QfBv);

    let x = solver.declare_const("x", Sort::bitvec(8));
    let fortytwo = solver.bv_const(42, 8);
    let eq = solver.eq(x, fortytwo);
    solver.assert_term(eq);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let val = solver.value(x);
    assert!(val.is_some());
    assert_eq!(
        val.unwrap(),
        ModelValue::BitVec {
            value: BigInt::from(42),
            width: 8
        }
    );
}

#[test]
fn test_get_values_batch() {
    // Test batch evaluation of multiple terms
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let three = solver.int_const(3);
    let seven = solver.int_const(7);

    let eq1 = solver.eq(x, three);
    solver.assert_term(eq1);
    let eq2 = solver.eq(y, seven);
    solver.assert_term(eq2);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let vals = solver.values(&[x, y]);
    assert!(vals.is_some());
    let vals = vals.unwrap();
    assert_eq!(vals.len(), 2);
    assert_eq!(vals[0], ModelValue::Int(BigInt::from(3)));
    assert_eq!(vals[1], ModelValue::Int(BigInt::from(7)));
}

#[test]
fn test_model_value_display() {
    // Test Display impl for ModelValue
    assert_eq!(format!("{}", ModelValue::Bool(true)), "true");
    assert_eq!(format!("{}", ModelValue::Bool(false)), "false");

    // Int values - SMT-LIB format
    assert_eq!(format!("{}", ModelValue::Int(BigInt::from(42))), "42");
    assert_eq!(format!("{}", ModelValue::Int(BigInt::from(-7))), "(- 7)");
    assert_eq!(format!("{}", ModelValue::Int(BigInt::from(0))), "0");

    // Real values - SMT-LIB format
    // Zero real: 0.0
    assert_eq!(
        format!(
            "{}",
            ModelValue::Real(BigRational::from_integer(BigInt::from(0)))
        ),
        "0.0"
    );
    // Integer reals: n.0
    assert_eq!(
        format!(
            "{}",
            ModelValue::Real(BigRational::from_integer(BigInt::from(5)))
        ),
        "5.0"
    );
    // Negative integer reals: (- n.0)
    assert_eq!(
        format!(
            "{}",
            ModelValue::Real(BigRational::from_integer(BigInt::from(-3)))
        ),
        "(- 3.0)"
    );
    // Fractional reals: (/ num denom)
    assert_eq!(
        format!(
            "{}",
            ModelValue::Real(BigRational::new(BigInt::from(3), BigInt::from(2)))
        ),
        "(/ 3 2)"
    );
    // Negative fractional reals: (- (/ num denom))
    assert_eq!(
        format!(
            "{}",
            ModelValue::Real(BigRational::new(BigInt::from(-7), BigInt::from(4)))
        ),
        "(- (/ 7 4))"
    );

    // BitVec should display as hex with proper width
    assert_eq!(
        format!(
            "{}",
            ModelValue::BitVec {
                value: BigInt::from(255),
                width: 8
            }
        ),
        "#xff"
    );
    assert_eq!(
        format!(
            "{}",
            ModelValue::BitVec {
                value: BigInt::from(15),
                width: 8
            }
        ),
        "#x0f"
    );
    // Negative bitvec should be converted to unsigned
    assert_eq!(
        format!(
            "{}",
            ModelValue::BitVec {
                value: BigInt::from(-1),
                width: 8
            }
        ),
        "#xff"
    );

    // String escaping
    assert_eq!(
        format!("{}", ModelValue::String("hello".to_string())),
        "\"hello\""
    );
    assert_eq!(
        format!("{}", ModelValue::String("a\"b".to_string())),
        "\"a\"\"b\""
    );
    // Backslash is printable ASCII and prints LITERALLY (z3-compatible
    // SMT-LIB 2.6 convention, commit c10ab547); non-ASCII/control code
    // points print as \u{X} with lowercase minimal-digit hex.
    assert_eq!(
        format!("{}", ModelValue::String("a\\b".to_string())),
        "\"a\\b\""
    );
    assert_eq!(
        format!("{}", ModelValue::String("\u{3b1}\t".to_string())),
        "\"\\u{3b1}\\u{9}\""
    );

    // Uninterpreted sort values - pass through
    assert_eq!(
        format!("{}", ModelValue::Uninterpreted("@Color!0".to_string())),
        "@Color!0"
    );

    // Array values - pass through SMT-LIB format
    assert_eq!(
        format!(
            "{}",
            ModelValue::ArraySmtlib("((as const (Array Int Int)) 0)".to_string())
        ),
        "((as const (Array Int Int)) 0)"
    );

    assert_eq!(format!("{}", ModelValue::Unknown), "unknown");
}

// =========================================================================
// Array try_* method tests
// =========================================================================

#[test]
fn test_try_select_success() {
    let mut solver = Solver::new(Logic::QfAuflia);
    let arr = solver.declare_const("arr", Sort::array(Sort::Int, Sort::Int));
    let idx = solver.int_const(0);
    let result = solver.try_select(arr, idx);
    assert!(result.is_ok());
}

#[test]
fn test_try_select_non_array() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let idx = solver.int_const(0);
    let err = solver.try_select(x, idx).unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "select",
            expected: "Array",
            ..
        }
    ));
}

#[test]
fn test_try_select_wrong_index_sort() {
    let mut solver = Solver::new(Logic::QfAuflia);
    let arr = solver.declare_const("arr", Sort::array(Sort::Int, Sort::Int));
    let idx = solver.bool_const(true);
    let err = solver.try_select(arr, idx).unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "select",
            expected: "index sort matching array index sort",
            ..
        }
    ));
}

#[test]
fn test_try_store_success() {
    let mut solver = Solver::new(Logic::QfAuflia);
    let arr = solver.declare_const("arr", Sort::array(Sort::Int, Sort::Int));
    let idx = solver.int_const(0);
    let val = solver.int_const(42);
    let result = solver.try_store(arr, idx, val);
    assert!(result.is_ok());
}

#[test]
fn test_try_store_non_array() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let idx = solver.int_const(0);
    let val = solver.int_const(42);
    let err = solver.try_store(x, idx, val).unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "store",
            expected: "Array",
            ..
        }
    ));
}

#[test]
fn test_try_store_wrong_index_sort() {
    let mut solver = Solver::new(Logic::QfAuflia);
    let arr = solver.declare_const("arr", Sort::array(Sort::Int, Sort::Int));
    let idx = solver.bool_const(true);
    let val = solver.int_const(42);
    let err = solver.try_store(arr, idx, val).unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "store",
            expected: "index sort matching array index sort",
            ..
        }
    ));
}

#[test]
fn test_try_store_wrong_value_sort() {
    let mut solver = Solver::new(Logic::QfAuflia);
    let arr = solver.declare_const("arr", Sort::array(Sort::Int, Sort::Int));
    let idx = solver.int_const(0);
    let val = solver.bool_const(true);
    let err = solver.try_store(arr, idx, val).unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "store",
            expected: "value sort matching array element sort",
            ..
        }
    ));
}

#[test]
fn test_try_const_array_success() {
    let mut solver = Solver::new(Logic::QfAuflia);
    let val = solver.int_const(0);
    let result = solver.try_const_array(Sort::Int, val);
    assert!(result.is_ok());
}

#[test]
#[should_panic(expected = "sort mismatch in select: expected Array")]
fn test_select_panics_on_non_array() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let idx = solver.int_const(0);
    solver.select(x, idx);
}

#[test]
#[should_panic(expected = "sort mismatch in store: expected Array")]
fn test_store_panics_on_non_array() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let idx = solver.int_const(0);
    let val = solver.int_const(42);
    solver.store(x, idx, val);
}

// =========================================================================
// Datatype try_* method tests
// =========================================================================

#[test]
fn test_try_datatype_constructor_success() {
    let mut solver = Solver::new(Logic::QfUflia);
    let pair_dt = DatatypeSort {
        name: "Pair".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "pair".to_string(),
            fields: vec![
                DatatypeField {
                    name: "fst".to_string(),
                    sort: Sort::Int,
                },
                DatatypeField {
                    name: "snd".to_string(),
                    sort: Sort::Int,
                },
            ],
        }],
    };
    solver.declare_datatype(&pair_dt);

    let one = solver.int_const(1);
    let two = solver.int_const(2);
    let result = solver.try_datatype_constructor(&pair_dt, "pair", &[one, two]);
    assert!(result.is_ok());
}

#[test]
fn test_try_datatype_constructor_undeclared_datatype() {
    let mut solver = Solver::new(Logic::QfUflia);
    let pair_dt = DatatypeSort {
        name: "Pair".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "pair".to_string(),
            fields: vec![
                DatatypeField {
                    name: "fst".to_string(),
                    sort: Sort::Int,
                },
                DatatypeField {
                    name: "snd".to_string(),
                    sort: Sort::Int,
                },
            ],
        }],
    };

    // Intentionally do not call declare_datatype.
    let one = solver.int_const(1);
    let two = solver.int_const(2);
    let err = solver
        .try_datatype_constructor(&pair_dt, "pair", &[one, two])
        .unwrap_err();
    assert!(matches!(
        err,
        SolverError::InvalidArgument {
            operation: "datatype_constructor",
            ..
        }
    ));
}

#[test]
fn test_try_datatype_constructor_unknown_ctor() {
    let mut solver = Solver::new(Logic::QfUflia);
    let pair_dt = DatatypeSort {
        name: "Pair".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "pair".to_string(),
            fields: vec![],
        }],
    };
    solver.declare_datatype(&pair_dt);

    let err = solver
        .try_datatype_constructor(&pair_dt, "unknown", &[])
        .unwrap_err();
    assert!(matches!(
        err,
        SolverError::InvalidArgument {
            operation: "datatype_constructor",
            ..
        }
    ));
}

#[test]
fn test_try_datatype_constructor_wrong_arity() {
    let mut solver = Solver::new(Logic::QfUflia);
    let pair_dt = DatatypeSort {
        name: "Pair".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "pair".to_string(),
            fields: vec![
                DatatypeField {
                    name: "fst".to_string(),
                    sort: Sort::Int,
                },
                DatatypeField {
                    name: "snd".to_string(),
                    sort: Sort::Int,
                },
            ],
        }],
    };
    solver.declare_datatype(&pair_dt);

    let one = solver.int_const(1);
    let err = solver
        .try_datatype_constructor(&pair_dt, "pair", &[one])
        .unwrap_err();
    assert!(matches!(
        err,
        SolverError::InvalidArgument {
            operation: "datatype_constructor",
            ..
        }
    ));
}

#[test]
fn test_try_datatype_constructor_wrong_arg_sort() {
    let mut solver = Solver::new(Logic::QfUflia);
    let pair_dt = DatatypeSort {
        name: "Pair".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "pair".to_string(),
            fields: vec![
                DatatypeField {
                    name: "fst".to_string(),
                    sort: Sort::Int,
                },
                DatatypeField {
                    name: "snd".to_string(),
                    sort: Sort::Int,
                },
            ],
        }],
    };
    solver.declare_datatype(&pair_dt);

    let one = solver.int_const(1);
    let b = solver.bool_const(true);
    let err = solver
        .try_datatype_constructor(&pair_dt, "pair", &[one, b])
        .unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "datatype_constructor",
            ..
        }
    ));
}

#[test]
fn test_try_datatype_selector_success() {
    let mut solver = Solver::new(Logic::QfUflia);
    let pair_dt = DatatypeSort {
        name: "Pair".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "pair".to_string(),
            fields: vec![
                DatatypeField {
                    name: "fst".to_string(),
                    sort: Sort::Int,
                },
                DatatypeField {
                    name: "snd".to_string(),
                    sort: Sort::Int,
                },
            ],
        }],
    };
    solver.declare_datatype(&pair_dt);

    let one = solver.int_const(1);
    let two = solver.int_const(2);
    let p = solver.datatype_constructor(&pair_dt, "pair", &[one, two]);
    let result = solver.try_datatype_selector("fst", p, Sort::Int);
    assert!(result.is_ok());
}

#[test]
fn test_try_datatype_selector_undeclared() {
    let mut solver = Solver::new(Logic::QfUflia);
    // Don't declare any datatype
    let x = solver.declare_const("x", Sort::Int);
    let err = solver
        .try_datatype_selector("unknown_selector", x, Sort::Int)
        .unwrap_err();
    assert!(matches!(
        err,
        SolverError::InvalidArgument {
            operation: "datatype_selector",
            ..
        }
    ));
}

#[test]
fn test_try_datatype_tester_success() {
    let mut solver = Solver::new(Logic::QfUf);
    let option_bool = DatatypeSort {
        name: "OptionBool".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "none".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "some".to_string(),
                fields: vec![DatatypeField {
                    name: "value".to_string(),
                    sort: Sort::Bool,
                }],
            },
        ],
    };
    solver.declare_datatype(&option_bool);

    let t = solver.bool_const(true);
    let some_true = solver.datatype_constructor(&option_bool, "some", &[t]);
    let result = solver.try_datatype_tester("some", some_true);
    assert!(result.is_ok());
}

#[test]
fn test_try_datatype_tester_unknown_ctor() {
    let mut solver = Solver::new(Logic::QfUf);
    let option_bool = DatatypeSort {
        name: "OptionBool".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "none".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "some".to_string(),
                fields: vec![DatatypeField {
                    name: "value".to_string(),
                    sort: Sort::Bool,
                }],
            },
        ],
    };
    solver.declare_datatype(&option_bool);

    let t = solver.bool_const(true);
    let some_true = solver.datatype_constructor(&option_bool, "some", &[t]);
    let err = solver
        .try_datatype_tester("unknown", some_true)
        .unwrap_err();
    assert!(matches!(
        err,
        SolverError::InvalidArgument {
            operation: "datatype_tester",
            ..
        }
    ));
}

#[test]
fn test_try_datatype_tester_undeclared() {
    let mut solver = Solver::new(Logic::QfUf);
    let x = solver.declare_const("x", Sort::Bool);
    let err = solver.try_datatype_tester("unknown", x).unwrap_err();
    assert!(matches!(
        err,
        SolverError::InvalidArgument {
            operation: "datatype_tester",
            ..
        }
    ));
}

#[test]
#[should_panic(expected = "invalid argument to datatype_constructor")]
fn test_datatype_constructor_panics_on_unknown_ctor() {
    let mut solver = Solver::new(Logic::QfUflia);
    let pair_dt = DatatypeSort {
        name: "Pair".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "pair".to_string(),
            fields: vec![],
        }],
    };
    solver.declare_datatype(&pair_dt);
    solver.datatype_constructor(&pair_dt, "unknown", &[]);
}

#[test]
#[should_panic(expected = "invalid argument to datatype_constructor")]
fn test_datatype_constructor_panics_on_undeclared_datatype() {
    let mut solver = Solver::new(Logic::QfUflia);
    let pair_dt = DatatypeSort {
        name: "Pair".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "pair".to_string(),
            fields: vec![],
        }],
    };
    // Intentionally do NOT call declare_datatype
    solver.datatype_constructor(&pair_dt, "pair", &[]);
}

#[test]
#[should_panic(expected = "invalid argument to datatype_tester")]
fn test_datatype_tester_panics_on_undeclared() {
    let mut solver = Solver::new(Logic::QfUf);
    let x = solver.declare_const("x", Sort::Bool);
    solver.datatype_tester("unknown", x);
}

#[test]
#[should_panic(expected = "sort mismatch in datatype_tester")]
fn test_datatype_tester_panics_on_expr_sort_mismatch() {
    let mut solver = Solver::new(Logic::QfUflia);
    let option_int = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "none".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "some".to_string(),
                fields: vec![DatatypeField {
                    name: "value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    solver.declare_datatype(&option_int);
    // Pass an Int instead of OptionInt
    let x = solver.declare_const("x", Sort::Int);
    solver.datatype_tester("some", x);
}

#[test]
#[should_panic(expected = "sort mismatch in datatype_selector")]
fn test_datatype_selector_panics_on_result_sort_mismatch() {
    let mut solver = Solver::new(Logic::QfUflia);
    let pair_dt = DatatypeSort {
        name: "Pair".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "pair".to_string(),
            fields: vec![DatatypeField {
                name: "fst".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    solver.declare_datatype(&pair_dt);
    let one = solver.int_const(1);
    let p = solver.datatype_constructor(&pair_dt, "pair", &[one]);
    // Wrong result sort: Bool instead of Int
    solver.datatype_selector("fst", p, Sort::Bool);
}

#[test]
#[should_panic(expected = "sort mismatch in datatype_selector")]
fn test_datatype_selector_panics_on_expr_sort_mismatch() {
    let mut solver = Solver::new(Logic::QfUflia);
    let pair_dt = DatatypeSort {
        name: "Pair".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "pair".to_string(),
            fields: vec![DatatypeField {
                name: "fst".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    solver.declare_datatype(&pair_dt);
    // Pass an Int instead of Pair
    let x = solver.declare_const("x", Sort::Int);
    solver.datatype_selector("fst", x, Sort::Int);
}

#[test]
fn test_try_datatype_selector_result_sort_mismatch() {
    let mut solver = Solver::new(Logic::QfUflia);
    let pair_dt = DatatypeSort {
        name: "Pair".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "pair".to_string(),
            fields: vec![DatatypeField {
                name: "fst".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    solver.declare_datatype(&pair_dt);

    let one = solver.int_const(1);
    let p = solver.datatype_constructor(&pair_dt, "pair", &[one]);
    // Try to select with wrong result sort (Bool instead of Int)
    let err = solver
        .try_datatype_selector("fst", p, Sort::Bool)
        .unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "datatype_selector",
            expected: "result_sort matching selector's return sort",
            ..
        }
    ));
}

#[test]
fn test_try_datatype_selector_expr_sort_mismatch() {
    let mut solver = Solver::new(Logic::QfUflia);
    let pair_dt = DatatypeSort {
        name: "Pair".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "pair".to_string(),
            fields: vec![DatatypeField {
                name: "fst".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    solver.declare_datatype(&pair_dt);

    // Try to select from an Int (not a Pair)
    let x = solver.declare_const("x", Sort::Int);
    let err = solver
        .try_datatype_selector("fst", x, Sort::Int)
        .unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "datatype_selector",
            expected: "expr sort matching selector's argument sort",
            ..
        }
    ));
}

#[test]
fn test_try_datatype_tester_expr_sort_mismatch() {
    let mut solver = Solver::new(Logic::QfUflia);
    let option_int = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "none".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "some".to_string(),
                fields: vec![DatatypeField {
                    name: "value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    solver.declare_datatype(&option_int);

    // Try to test an Int (not an OptionInt)
    let x = solver.declare_const("x", Sort::Int);
    let err = solver.try_datatype_tester("some", x).unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "datatype_tester",
            expected: "expr sort matching tester's argument sort",
            ..
        }
    ));
}

// =========================================================================
// Display impl tests
// =========================================================================

#[test]
fn test_logic_display() {
    assert_eq!(format!("{}", Logic::QfLia), "QF_LIA");
    assert_eq!(format!("{}", Logic::QfLra), "QF_LRA");
    assert_eq!(format!("{}", Logic::QfUf), "QF_UF");
    assert_eq!(format!("{}", Logic::QfBv), "QF_BV");
    assert_eq!(format!("{}", Logic::QfAuflia), "QF_AUFLIA");
    assert_eq!(format!("{}", Logic::Lia), "LIA");
    assert_eq!(format!("{}", Logic::Auflia), "AUFLIA");
}

#[test]
fn test_funcdecl_display() {
    let mut solver = Solver::new(Logic::QfUflia);

    // 0-arity function (constant)
    let f0 = FuncDecl {
        name: "c".to_string(),
        domain: vec![],
        range: Sort::Int,
    };
    assert_eq!(format!("{f0}"), "c : Int");

    // Unary function
    let f = solver.declare_fun("f", &[Sort::Int], Sort::Int);
    assert_eq!(format!("{f}"), "f : (Int) -> Int");

    // Binary function
    let g = solver.declare_fun("g", &[Sort::Int, Sort::Bool], Sort::Int);
    assert_eq!(format!("{g}"), "g : (Int, Bool) -> Int");
}

#[test]
fn test_proxy_variable_in_implication_negative_integers_issue_2671() {
    // Regression test for #2671: verification-consumer reports false UNSAT when a proxy
    // variable (proxy = i + 1) is used inside an implication body with
    // negative integer counterexamples.
    //
    // Formula (SAT at i = n = -1, proxy = 0):
    //   i <= n
    //   proxy = i + 1
    //   (i >= 0) => (proxy <= n)
    //   NOT(i + 1 <= n)
    let mut solver = Solver::new(Logic::QfLia);
    let i = solver.declare_const("i", Sort::Int);
    let n = solver.declare_const("n", Sort::Int);
    let proxy = solver.declare_const("proxy", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);

    // i <= n
    let c1 = solver.le(i, n);
    solver.assert_term(c1);

    // proxy = i + 1
    let i_plus_1 = solver.add(i, one);
    let c2 = solver.eq(proxy, i_plus_1);
    solver.assert_term(c2);

    // (i >= 0) => (proxy <= n)
    let guard = solver.ge(i, zero);
    let body = solver.le(proxy, n);
    let c3 = solver.implies(guard, body);
    solver.assert_term(c3);

    // NOT(i + 1 <= n)
    let i_plus_1_again = solver.add(i, one);
    let le_term = solver.le(i_plus_1_again, n);
    let c4 = solver.not(le_term);
    solver.assert_term(c4);

    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "BUG #2671: Formula is SAT (model: i=-1, n=-1, proxy=0) but solver returned UNSAT"
    );

    // Verify model consistency: proxy must equal i + 1
    let model = solver.model().expect("model for SAT result").into_inner();
    let i_val = model.int_val_i64("i").expect("i in model");
    let n_val = model.int_val_i64("n").expect("n in model");
    let proxy_val = model.int_val_i64("proxy").expect("proxy in model");

    assert_eq!(proxy_val, i_val + 1, "proxy must equal i + 1");
    assert!(i_val <= n_val, "i <= n must hold");
    assert!(i_val >= n_val, "NOT(i + 1 <= n) must hold");
    if i_val >= 0 {
        assert!(proxy_val <= n_val, "(i >= 0) => (proxy <= n) must hold");
    }
}

#[test]
fn test_lt_gt_strict_inequality_unsat_issue_2665() {
    // Regression test for #2665: lt()/gt() with compound arithmetic
    // returned Unknown instead of Unsat.

    // Case 1: lt(i,n) ∧ lt(n,i) is contradictory
    {
        let mut solver = Solver::new(Logic::QfLia);
        let i = solver.declare_const("i", Sort::Int);
        let n = solver.declare_const("n", Sort::Int);
        let c1 = solver.lt(i, n);
        solver.assert_term(c1);
        let c2 = solver.lt(n, i);
        solver.assert_term(c2);
        assert_eq!(
            solver.check_sat(),
            SolveResult::unsat(),
            "BUG #2665 case 1: i < n ∧ n < i must be Unsat"
        );
    }

    // Case 2: i >= 0 ∧ i <= n ∧ i < n ∧ (i+1) > n is contradictory
    {
        let mut solver = Solver::new(Logic::QfLia);
        let i = solver.declare_const("i", Sort::Int);
        let n = solver.declare_const("n", Sort::Int);
        let zero = solver.int_const(0);
        let one = solver.int_const(1);

        let c1 = solver.ge(i, zero);
        solver.assert_term(c1);
        let c2 = solver.le(i, n);
        solver.assert_term(c2);
        let c3 = solver.lt(i, n);
        solver.assert_term(c3);
        let i_plus_1 = solver.add(i, one);
        let c4 = solver.gt(i_plus_1, n);
        solver.assert_term(c4);
        assert_eq!(
            solver.check_sat(),
            SolveResult::unsat(),
            "BUG #2665 case 2: i >= 0 ∧ i <= n ∧ i < n ∧ i+1 > n must be Unsat"
        );
    }

    // Case 3: i >= 0 ∧ i <= n ∧ i < n ∧ (n-i) < 0 is contradictory
    {
        let mut solver = Solver::new(Logic::QfLia);
        let i = solver.declare_const("i", Sort::Int);
        let n = solver.declare_const("n", Sort::Int);
        let zero = solver.int_const(0);

        let c1 = solver.ge(i, zero);
        solver.assert_term(c1);
        let c2 = solver.le(i, n);
        solver.assert_term(c2);
        let c3 = solver.lt(i, n);
        solver.assert_term(c3);
        let n_minus_i = solver.sub(n, i);
        let c4 = solver.lt(n_minus_i, zero);
        solver.assert_term(c4);
        assert_eq!(
            solver.check_sat(),
            SolveResult::unsat(),
            "BUG #2665 case 3: i >= 0 ∧ i <= n ∧ i < n ∧ (n-i) < 0 must be Unsat"
        );
    }
}

// =========================================================================
// API-path constant folding regression tests (#4087)
//
// These tests verify that BV operations performed via the Solver API
// (try_bvadd, try_bvsub, etc.) use simplifying constructors and thus
// produce the same interned TermId as directly-created constants.
// Prior to #4087, the API used generic mk_app() which bypassed constant
// folding, creating un-normalized terms that broke congruence closure.
// =========================================================================

#[test]
fn test_api_bvadd_constant_folding_4087() {
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.bv_const(1, 8);
    let b = solver.bv_const(2, 8);
    let expected = solver.bv_const(3, 8);
    let result = solver.bvadd(a, b);
    assert_eq!(result, expected, "bvadd(1, 2) should constant-fold to 3");
}

#[test]
fn test_api_bvsub_constant_folding_4087() {
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.bv_const(10, 8);
    let b = solver.bv_const(3, 8);
    let expected = solver.bv_const(7, 8);
    let result = solver.bvsub(a, b);
    assert_eq!(result, expected, "bvsub(10, 3) should constant-fold to 7");
}

#[test]
fn test_api_bvmul_constant_folding_4087() {
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.bv_const(6, 8);
    let b = solver.bv_const(7, 8);
    let expected = solver.bv_const(42, 8);
    let result = solver.bvmul(a, b);
    assert_eq!(result, expected, "bvmul(6, 7) should constant-fold to 42");
}

#[test]
fn test_api_bvand_constant_folding_4087() {
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.bv_const(0xF0, 8);
    let b = solver.bv_const(0x3C, 8);
    let expected = solver.bv_const(0x30, 8);
    let result = solver.bvand(a, b);
    assert_eq!(
        result, expected,
        "bvand(0xF0, 0x3C) should constant-fold to 0x30"
    );
}

#[test]
fn test_api_bvor_constant_folding_4087() {
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.bv_const(0xF0, 8);
    let b = solver.bv_const(0x0F, 8);
    let expected = solver.bv_const(0xFF, 8);
    let result = solver.bvor(a, b);
    assert_eq!(
        result, expected,
        "bvor(0xF0, 0x0F) should constant-fold to 0xFF"
    );
}

#[test]
fn test_api_bvnot_constant_folding_4087() {
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.bv_const(0xA5, 8);
    let expected = solver.bv_const(0x5A, 8);
    let result = solver.bvnot(a);
    assert_eq!(result, expected, "bvnot(0xA5) should constant-fold to 0x5A");
}

#[test]
fn test_api_bvneg_constant_folding_4087() {
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.bv_const(1, 8);
    let expected = solver.bv_const(0xFF, 8);
    let result = solver.bvneg(a);
    assert_eq!(
        result, expected,
        "bvneg(1) should constant-fold to 0xFF (two's complement)"
    );
}

#[test]
fn test_api_bvzero_extend_constant_folding_4087() {
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.bv_const(0x42, 8);
    let expected = solver.bv_const(0x0042, 16);
    let result = solver.bvzeroext(a, 8);
    assert_eq!(
        result, expected,
        "bvzeroext(0x42, 8) should constant-fold to 0x0042"
    );
}

#[test]
fn test_api_bvshl_constant_folding_4087() {
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.bv_const(1, 8);
    let b = solver.bv_const(4, 8);
    let expected = solver.bv_const(16, 8);
    let result = solver.bvshl(a, b);
    assert_eq!(result, expected, "bvshl(1, 4) should constant-fold to 16");
}

#[test]
fn test_api_bvextract_constant_folding_4087() {
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.bv_const(0xABCD, 16);
    let expected = solver.bv_const(0xBC, 8);
    let result = solver.bvextract(a, 11, 4);
    assert_eq!(
        result, expected,
        "bvextract(0xABCD, 11, 4) should constant-fold to 0xBC"
    );
}

#[test]
fn test_api_bvconcat_constant_folding_4087() {
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.bv_const(0xAB, 8);
    let b = solver.bv_const(0xCD, 8);
    let expected = solver.bv_const(0xABCD, 16);
    let result = solver.bvconcat(a, b);
    assert_eq!(
        result, expected,
        "bvconcat(0xAB, 0xCD) should constant-fold to 0xABCD"
    );
}

#[test]
fn test_api_bvult_constant_folding_4087() {
    // bvult(1, 2) should constant-fold to true
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.bv_const(1, 8);
    let b = solver.bv_const(2, 8);
    let result = solver.bvult(a, b);
    let expected = solver.bool_const(true);
    assert_eq!(result, expected, "bvult(1, 2) should constant-fold to true");
}

#[test]
fn test_api_constant_folding_matches_parser_path_4087() {
    // End-to-end: verify that a term created via API produces the same
    // result as the parser path for the same expression.
    // This is the actual bug from #4087: store(a, bvadd(idx, 0), v)
    // via API should match store(a, idx, v) if bvadd(idx, 0) normalizes.
    let mut solver = Solver::new(Logic::QfAufbv);
    let arr = solver.declare_const("a", Sort::array(Sort::bitvec(8), Sort::bitvec(8)));
    let idx = solver.declare_const("idx", Sort::bitvec(8));
    let v = solver.bv_const(42, 8);
    let zero = solver.bv_const(0, 8);

    // bvadd(idx, 0) should simplify to idx (identity reduction)
    let idx_plus_zero = solver.bvadd(idx, zero);
    assert_eq!(
        idx_plus_zero, idx,
        "bvadd(idx, 0) should simplify to idx via identity reduction"
    );

    // Therefore store(a, bvadd(idx, 0), v) == store(a, idx, v)
    let store1 = solver.store(arr, idx_plus_zero, v);
    let store2 = solver.store(arr, idx, v);
    assert_eq!(
        store1, store2,
        "store with identity-reduced index should produce identical term"
    );
}

#[test]
fn test_api_bvsign_extend_negative_constant_folding_4087() {
    // Sign-extend a negative 8-bit value (-1 = 0xFF) to 16 bits (0xFFFF)
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.bv_const(-1i64, 8); // 0xFF
    let expected = solver.bv_const(-1i64, 16); // 0xFFFF
    let result = solver.bvsignext(a, 8);
    assert_eq!(
        result, expected,
        "bvsignext(0xFF_8bit, 8) should constant-fold to 0xFFFF_16bit"
    );
}

#[test]
fn test_api_bvxor_constant_folding_4087() {
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.bv_const(0xAA, 8);
    let b = solver.bv_const(0x55, 8);
    let expected = solver.bv_const(0xFF, 8);
    let result = solver.bvxor(a, b);
    assert_eq!(
        result, expected,
        "bvxor(0xAA, 0x55) should constant-fold to 0xFF"
    );
}

/// BV+Int formulas (via bv2nat) can prove UNSAT through the conservative
/// unsigned BV-to-Int bridge (#9065).
#[test]
fn test_bv2nat_symbolic_bridge_proves_unsat_under_auto_detection() {
    let mut solver = Solver::new(Logic::All);
    let x = solver.declare_const("x", Sort::bitvec(8));
    let bv2nat_x = solver.bv2int(x);
    let five = solver.int_const(5);
    let gt = solver.gt(bv2nat_x, five);
    solver.assert_term(gt);

    let three_bv = solver.bv_const(3, 8);
    let bvult = solver.bvult(x, three_bv);
    solver.assert_term(bvult);

    // bv2nat(x) > 5 AND x < 3 is UNSAT.
    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "BV+Int bridge should prove this formula UNSAT, got {result:?}"
    );
}

/// BV<->LIA residue-congruence routing fix: a mixed Int/BV obligation whose Int
/// domain (`0 <= x < 2^32`) blows the BV/LIA enumeration limit and which has no
/// `bvult`-constant atom for the old conservative bridge. It is UNSAT *only*
/// once the tight residue congruence `bv2nat(int2bv(32, x)) = x` (valid because
/// `0 <= x < 2^32`) reaches the deciding AUFLIA solver. Before the fix the
/// congruence lived only inside the bitblast/enumeration probes (which give up
/// past `2^16`), so this stayed Unknown.
#[test]
fn test_bv_lia_residue_congruence_routed_to_auflia() {
    let mut solver = Solver::new(Logic::All);
    let x = solver.declare_const("x", Sort::Int);

    let zero = solver.int_const(0);
    let two_pow_32 = solver.int_const(1i64 << 32);
    let x_nonneg = solver.ge(x, zero);
    let x_below = solver.lt(x, two_pow_32);
    solver.assert_term(x_nonneg);
    solver.assert_term(x_below);

    // bv = int2bv(32, x); nat = bv2nat(bv). For x in [0, 2^32) we have nat = x,
    // so nat > x is UNSAT — but only via the residue congruence.
    let bv = solver.int2bv(x, 32);
    let nat = solver.bv2int(bv);
    let nat_gt_x = solver.gt(nat, x);
    solver.assert_term(nat_gt_x);

    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "BV/LIA residue congruence should reach AUFLIA and prove UNSAT, got {result:?}"
    );
}

/// Euclidean-form residue routing: with no provable `e < 2^W` upper bound, the
/// bridge emits `e = bv2nat(int2bv(W, e)) + 2^W * k` plus the unsigned range
/// `0 <= bv2nat(int2bv(W, e)) < 2^W`. Asserting `bv2nat(int2bv(8, e)) > 255`
/// must be UNSAT regardless of `e`, since the residue is always in `[0, 256)`.
#[test]
fn test_bv_lia_residue_euclidean_range_routed_to_auflia() {
    let mut solver = Solver::new(Logic::All);
    let e = solver.declare_const("e", Sort::Int);

    let bv = solver.int2bv(e, 8);
    let nat = solver.bv2int(bv);
    let two_55 = solver.int_const(255);
    let nat_gt_255 = solver.gt(nat, two_55);
    solver.assert_term(nat_gt_255);

    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "Euclidean residue range should reach AUFLIA and prove UNSAT, got {result:?}"
    );
}

/// verification-consumer's `count8` popcount VC uses a very small finite input domain. The
/// BV/LIA bridge should exhaust that range directly instead of sending a
/// 64-bit SWAR expression to the general BV solver (#8961).
#[test]
fn test_verification_consumer_popcount8_bv2nat_bound_under_uflia_8961() {
    let mut solver = Solver::new(Logic::Uflia);
    let n_view = solver.declare_const("n_view", Sort::Int);
    let n = solver.declare_const("n", Sort::Int);
    let result_view = solver.declare_const("result_view", Sort::Int);

    let zero = solver.int_const(0);
    let max_u8 = solver.int_const(255);
    let width_bound = solver.int_const(8);
    let n_view_eq_n = solver.eq(n_view, n);
    let n_view_nonneg = solver.le(zero, n_view);
    let n_view_u8 = solver.le(n_view, max_u8);
    solver.assert_term(n_view_eq_n);
    solver.assert_term(n_view_nonneg);
    solver.assert_term(n_view_u8);

    let n_bv = solver.int2bv(n, 64);
    let shr1 = {
        let extracted = solver.bvextract(n_bv, 63, 1);
        solver.bvzeroext(extracted, 1)
    };
    let mask_55 = solver.bv_const(0x55, 64);
    let shr1_masked = solver.bvand(shr1, mask_55);
    let shr1_masked_nat = solver.bv2int(shr1_masked);
    let x1_int = solver.sub(n, shr1_masked_nat);
    let x1_bv = solver.int2bv(x1_int, 64);

    let mask_33 = solver.bv_const(0x33, 64);
    let x1_low = solver.bvand(x1_bv, mask_33);
    let x1_low_nat = solver.bv2int(x1_low);
    let x1_shr2 = {
        let extracted = solver.bvextract(x1_bv, 63, 2);
        solver.bvzeroext(extracted, 2)
    };
    let x1_high = solver.bvand(x1_shr2, mask_33);
    let x1_high_nat = solver.bv2int(x1_high);
    let x2_int = solver.add(x1_low_nat, x1_high_nat);
    let x2_bv = solver.int2bv(x2_int, 64);

    let x2_shr4_nat = {
        let extracted = solver.bvextract(x2_bv, 63, 4);
        let extended = solver.bvzeroext(extracted, 4);
        solver.bv2int(extended)
    };
    let x3_sum = solver.add(x2_int, x2_shr4_nat);
    let x3_sum_bv = solver.int2bv(x3_sum, 64);
    let mask_0f = solver.bv_const(0x0f, 64);
    let final_bv = solver.bvand(x3_sum_bv, mask_0f);
    let final_nat = solver.bv2int(final_bv);

    let result_eq = solver.eq(final_nat, result_view);
    let bound = solver.le(result_view, width_bound);
    let violates_bound = solver.not(bound);
    let result = solver.check_sat_assuming(&[result_eq, violates_bound]);
    assert!(
        result.is_unsat(),
        "verification-consumer popcount8 BV/LIA finite-domain bound should be UNSAT, got {result:?}"
    );
}

/// The same verification-consumer lane also checks the SWAR result against the logical
/// bit-test sum. The bridge proves the negated equality UNSAT by enumerating
/// the finite `u8` input range and evaluating the asserted ITE auxiliaries.
#[test]
fn test_verification_consumer_popcount8_bv2nat_equals_bit_sum_under_uflia_8961() {
    let mut solver = Solver::new(Logic::Uflia);
    let n_view = solver.declare_const("n_view", Sort::Int);
    let n = solver.declare_const("n", Sort::Int);
    let result_view = solver.declare_const("result_view", Sort::Int);

    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let max_u8 = solver.int_const(255);
    let n_view_eq_n = solver.eq(n_view, n);
    let n_view_nonneg = solver.le(zero, n_view);
    let n_view_u8 = solver.le(n_view, max_u8);
    solver.assert_term(n_view_eq_n);
    solver.assert_term(n_view_nonneg);
    solver.assert_term(n_view_u8);

    let n_bv = solver.int2bv(n, 64);
    let shr1 = {
        let extracted = solver.bvextract(n_bv, 63, 1);
        solver.bvzeroext(extracted, 1)
    };
    let mask_55 = solver.bv_const(0x55, 64);
    let shr1_masked = solver.bvand(shr1, mask_55);
    let shr1_masked_nat = solver.bv2int(shr1_masked);
    let x1_int = solver.sub(n, shr1_masked_nat);
    let x1_bv = solver.int2bv(x1_int, 64);

    let mask_33 = solver.bv_const(0x33, 64);
    let x1_low = solver.bvand(x1_bv, mask_33);
    let x1_low_nat = solver.bv2int(x1_low);
    let x1_shr2 = {
        let extracted = solver.bvextract(x1_bv, 63, 2);
        solver.bvzeroext(extracted, 2)
    };
    let x1_high = solver.bvand(x1_shr2, mask_33);
    let x1_high_nat = solver.bv2int(x1_high);
    let x2_int = solver.add(x1_low_nat, x1_high_nat);
    let x2_bv = solver.int2bv(x2_int, 64);

    let x2_shr4_nat = {
        let extracted = solver.bvextract(x2_bv, 63, 4);
        let extended = solver.bvzeroext(extracted, 4);
        solver.bv2int(extended)
    };
    let x3_sum = solver.add(x2_int, x2_shr4_nat);
    let x3_sum_bv = solver.int2bv(x3_sum, 64);
    let mask_0f = solver.bv_const(0x0f, 64);
    let final_bv = solver.bvand(x3_sum_bv, mask_0f);
    let final_nat = solver.bv2int(final_bv);
    let result_eq = solver.eq(final_nat, result_view);
    solver.assert_term(result_eq);

    let mut bit_terms = Vec::new();
    for bit in 0..8 {
        let modulus = solver.int_const(1 << (bit + 1));
        let threshold = solver.int_const(1 << bit);
        let rem = solver.modulo(n, modulus);
        let cond = solver.lt(rem, threshold);
        let aux = solver.declare_const(&format!("bit_{bit}"), Sort::Int);
        let aux_zero = solver.eq(zero, aux);
        let aux_one = solver.eq(one, aux);
        let cond_implies_zero = {
            let not_cond = solver.not(cond);
            solver.or(not_cond, aux_zero)
        };
        let not_cond_implies_one = solver.or(cond, aux_one);
        solver.assert_term(cond_implies_zero);
        solver.assert_term(not_cond_implies_one);
        bit_terms.push(aux);
    }

    let logical_count = solver.add_many(&bit_terms);
    let equality = solver.eq(result_view, logical_count);
    let violates_equality = solver.not(equality);
    solver.assert_term(violates_equality);

    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "verification-consumer popcount8 BV/LIA equality should be UNSAT, got {result:?}"
    );
}

/// verification-consumer's `bitvectors/popcount.rs::count16` VC is declared as UFLIA but
/// contains an unsigned BV-to-Int SWAR bound. The BV/LIA bridge must prove the
/// counterexample query impossible instead of leaving AUFLIA to learn an
/// unverifiable mixed-theory conflict (#8961).
#[test]
fn test_verification_consumer_popcount16_bv2nat_bound_under_uflia_8961() {
    let mut solver = Solver::new(Logic::Uflia);
    let n_view = solver.declare_const("n_view", Sort::Int);
    let n = solver.declare_const("n", Sort::Int);
    let result_view = solver.declare_const("result_view", Sort::Int);

    let zero = solver.int_const(0);
    let max_u16 = solver.int_const(65_535);
    let width_bound = solver.int_const(16);
    let n_view_eq_n = solver.eq(n_view, n);
    let n_view_nonneg = solver.le(zero, n_view);
    let n_view_u16 = solver.le(n_view, max_u16);
    solver.assert_term(n_view_eq_n);
    solver.assert_term(n_view_nonneg);
    solver.assert_term(n_view_u16);

    let n_bv = solver.int2bv(n, 64);
    let shr1 = {
        let extracted = solver.bvextract(n_bv, 63, 1);
        solver.bvzeroext(extracted, 1)
    };
    let mask_5555 = solver.bv_const(0x5555, 64);
    let shr1_masked = solver.bvand(shr1, mask_5555);
    let shr1_masked_nat = solver.bv2int(shr1_masked);
    let x1_int = solver.sub(n, shr1_masked_nat);
    let x1_bv = solver.int2bv(x1_int, 64);

    let mask_3333 = solver.bv_const(0x3333, 64);
    let x1_low = solver.bvand(x1_bv, mask_3333);
    let x1_low_nat = solver.bv2int(x1_low);
    let x1_shr2 = {
        let extracted = solver.bvextract(x1_bv, 63, 2);
        solver.bvzeroext(extracted, 2)
    };
    let x1_high = solver.bvand(x1_shr2, mask_3333);
    let x1_high_nat = solver.bv2int(x1_high);
    let x2_int = solver.add(x1_low_nat, x1_high_nat);
    let x2_bv = solver.int2bv(x2_int, 64);

    let x2_shr4_nat = {
        let extracted = solver.bvextract(x2_bv, 63, 4);
        let extended = solver.bvzeroext(extracted, 4);
        solver.bv2int(extended)
    };
    let x3_sum = solver.add(x2_int, x2_shr4_nat);
    let x3_sum_bv = solver.int2bv(x3_sum, 64);
    let mask_0f0f = solver.bv_const(0x0f0f, 64);
    let x3_bv = solver.bvand(x3_sum_bv, mask_0f0f);
    let x3_nat = solver.bv2int(x3_bv);

    let x3_shr8_nat = {
        let extracted = solver.bvextract(x3_bv, 63, 8);
        let extended = solver.bvzeroext(extracted, 8);
        solver.bv2int(extended)
    };
    let x4_int = solver.add(x3_nat, x3_shr8_nat);
    let x4_bv = solver.int2bv(x4_int, 64);
    let mask_1f = solver.bv_const(0x1f, 64);
    let final_bv = solver.bvand(x4_bv, mask_1f);
    let final_nat = solver.bv2int(final_bv);

    let result_eq = solver.eq(final_nat, result_view);
    let bound = solver.le(result_view, width_bound);
    let violates_bound = solver.not(bound);
    let result = solver.check_sat_assuming(&[result_eq, violates_bound]);
    assert!(
        result.is_unsat(),
        "verification-consumer popcount16 BV/LIA bound should be UNSAT, got {result:?}"
    );
}

/// Mixed Int/BV formula without cross-theory conversion functions should
/// be solvable. BV terms are treated as uninterpreted in AUFLIA. (#5356)
#[test]
fn test_mixed_int_bv_independent_returns_sat() {
    use std::time::Duration;

    let mut solver = Solver::new(Logic::All);
    solver.set_timeout(Some(Duration::from_secs(5)));

    let x = solver.declare_const("x", Sort::Int);
    let s = solver.declare_const("S", Sort::bitvec(2));

    // x >= 0 AND x <= 1
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let ge0 = solver.ge(x, zero);
    let le1 = solver.le(x, one);
    solver.assert_term(ge0);
    solver.assert_term(le1);

    // (or (and (= x 0) (= (extract 0 0 S) #b1))
    //     (and (= x 1) (= (extract 1 1 S) #b1)))
    let eq_x_0 = solver.eq(x, zero);
    let eq_x_1 = solver.eq(x, one);
    let ext_0 = solver.bvextract(s, 0, 0);
    let ext_1 = solver.bvextract(s, 1, 1);
    let b1 = solver.bv_const(1, 1);
    let eq_ext0 = solver.eq(ext_0, b1);
    let eq_ext1 = solver.eq(ext_1, b1);
    let branch0 = solver.and(eq_x_0, eq_ext0);
    let branch1 = solver.and(eq_x_1, eq_ext1);
    let disjunction = solver.or(branch0, branch1);
    solver.assert_term(disjunction);

    let result = solver.check_sat();
    // (#5356) BV-first solver (solve_bv_lia_indep) now handles mixed Int/BV
    // formulas correctly: BV solver evaluates extract/concat semantics, then
    // model validation confirms all assertions (including Int) hold.
    // Previously returned Unknown because AUFLIA routing treated BV as
    // uninterpreted. Now correctly returns Sat (z3 also finds x=0, S=#b01).
    assert_eq!(
        result,
        SolveResult::Sat,
        "Mixed Int/BV with independent constraints should be SAT via BV-first solver (#5356)"
    );
}

// =========================================================================
// BV timeout/interrupt tests (#3381)
// =========================================================================

/// BV solver must respect set_timeout(Duration::ZERO) and return Unknown.
///
/// Before #3381, the BV solver called solver.solve() (non-interruptible),
/// ignoring the executor's deadline entirely. This test verifies that
/// solve_interruptible is used instead.
#[test]
fn test_bv_zero_timeout_returns_unknown_3381() {
    use std::time::Duration;
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(8));
    let y = solver.declare_const("y", Sort::bitvec(8));
    let eq = solver.eq(x, y);
    solver.assert_term(eq);
    solver.set_timeout(Some(Duration::ZERO));
    let result = solver.check_sat();
    assert_eq!(
        result,
        SolveResult::Unknown,
        "BV solver must return Unknown when timeout is zero (#3381)"
    );
    assert_eq!(solver.get_reason_unknown(), Some("timeout".to_string()));
}

/// BV solver must respect interrupt flag and return Unknown.
#[test]
fn test_bv_interrupt_returns_unknown_3381() {
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(8));
    let y = solver.declare_const("y", Sort::bitvec(8));
    let eq = solver.eq(x, y);
    solver.assert_term(eq);
    solver.interrupt();
    let result = solver.check_sat();
    assert_eq!(
        result,
        SolveResult::Unknown,
        "BV solver must return Unknown when interrupted (#3381)"
    );
    assert_eq!(solver.get_reason_unknown(), Some("interrupted".to_string()));
}

/// ABV (Array+BV) solver must respect set_timeout.
#[test]
fn test_abv_zero_timeout_returns_unknown_3381() {
    use std::time::Duration;
    let mut solver = Solver::new(Logic::QfAbv);
    let arr = solver.declare_const("arr", Sort::array(Sort::bitvec(8), Sort::bitvec(8)));
    let idx = solver.declare_const("idx", Sort::bitvec(8));
    let val = solver.bv_const(42, 8);
    let stored = solver.store(arr, idx, val);
    let read = solver.select(stored, idx);
    let eq = solver.eq(read, val);
    solver.assert_term(eq);
    solver.set_timeout(Some(Duration::ZERO));
    let result = solver.check_sat();
    assert_eq!(
        result,
        SolveResult::Unknown,
        "ABV solver must return Unknown when timeout is zero (#3381)"
    );
    assert_eq!(solver.get_reason_unknown(), Some("timeout".to_string()));
}

/// Wide BV formula must abort during encoding phases, not hang (#3070).
///
/// Before the #3070 fix, encoding phases (Tseitin, bitblasting, axiom
/// generation) for wide bitvectors ran without interrupt/timeout checks.
/// A 64-bit multiply generates ~128K gates; with a short timeout the
/// solver must return Unknown rather than completing encoding.
#[test]
fn test_bv_wide_formula_timeout_during_encoding_3070() {
    use std::time::Duration;
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(64));
    let y = solver.declare_const("y", Sort::bitvec(64));
    let z = solver.declare_const("z", Sort::bitvec(64));
    // Build a chain of wide BV operations to stress the encoding phase:
    // (x * y) + (y * z) = (x * z) — generates substantial bitblasting work.
    let xy = solver.bvmul(x, y);
    let yz = solver.bvmul(y, z);
    let xz = solver.bvmul(x, z);
    let sum = solver.bvadd(xy, yz);
    let eq = solver.eq(sum, xz);
    solver.assert_term(eq);
    // Use Duration::ZERO to guarantee the encoding-phase abort checks fire.
    solver.set_timeout(Some(Duration::ZERO));
    let start = ay_core::time::Instant::now();
    let result = solver.check_sat();
    let elapsed = start.elapsed();
    assert_eq!(
        result,
        SolveResult::Unknown,
        "Wide BV formula must return Unknown when timeout is zero (#3070)"
    );
    assert_eq!(solver.get_reason_unknown(), Some("timeout".to_string()));
    // Encoding a 64-bit multiply chain without abort checks takes 100ms+.
    // With abort checks, this should return almost immediately.
    assert!(
        elapsed < Duration::from_secs(5),
        "BV encoding should abort quickly, took {elapsed:?}"
    );
}

/// BV bitblasting loop must respect interrupt flag during encoding (#8609).
///
/// Creates many BV assertions to exercise the bitblasting loop in
/// bitblast_all(). With the interrupt flag set before check_sat(),
/// the solver must return Unknown quickly rather than completing all
/// bitblasting work. Before #8609, the interrupt was only checked between
/// phases, not within the bitblasting loop.
#[test]
fn test_bv_interrupt_during_bitblasting_8609() {
    let mut solver = Solver::new(Logic::QfBv);
    // Create 500 BV equality assertions to stress the bitblasting loop.
    let mut vars = Vec::new();
    for i in 0..501 {
        vars.push(solver.declare_const(&format!("v{i}"), Sort::bitvec(32)));
    }
    for pair in vars.windows(2) {
        let eq = solver.eq(pair[0], pair[1]);
        solver.assert_term(eq);
    }
    // Set interrupt before solving — the bitblasting loop must check this.
    solver.interrupt();
    let result = solver.check_sat();
    assert_eq!(
        result,
        SolveResult::Unknown,
        "BV solver must return Unknown when interrupted during bitblasting (#8609)"
    );
}

/// BV solver must respect a short timeout during bitblasting of many assertions (#8609).
#[test]
fn test_bv_timeout_during_bitblasting_8609() {
    use std::time::Duration;
    let mut solver = Solver::new(Logic::QfBv);
    // Create many BV multiplication assertions (expensive bitblasting).
    for i in 0..200 {
        let x = solver.declare_const(&format!("x{i}"), Sort::bitvec(32));
        let y = solver.declare_const(&format!("y{i}"), Sort::bitvec(32));
        let z = solver.declare_const(&format!("z{i}"), Sort::bitvec(32));
        let product = solver.bvmul(x, y);
        let eq = solver.eq(product, z);
        solver.assert_term(eq);
    }
    solver.set_timeout(Some(Duration::ZERO));
    let result = solver.check_sat();
    assert_eq!(
        result,
        SolveResult::Unknown,
        "BV solver must return Unknown when timeout fires during bitblasting (#8609)"
    );
    assert_eq!(solver.get_reason_unknown(), Some("timeout".to_string()));
}

// =========================================================================
// Derived BV operations: bvnand, bvnor, bvxnor, bvcomp (#8298)
// =========================================================================

#[test]
fn test_bvnand_constant_folding() {
    // bvnand(0xF0, 0x3C) = bvnot(bvand(0xF0, 0x3C)) = bvnot(0x30) = 0xCF
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.bv_const(0xF0, 8);
    let b = solver.bv_const(0x3C, 8);
    let expected = solver.bv_const(0xCF, 8);
    let result = solver.bvnand(a, b);
    assert_eq!(
        result, expected,
        "bvnand(0xF0, 0x3C) should constant-fold to 0xCF"
    );
}

#[test]
fn test_bvnor_constant_folding() {
    // bvnor(0xF0, 0x0F) = bvnot(bvor(0xF0, 0x0F)) = bvnot(0xFF) = 0x00
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.bv_const(0xF0, 8);
    let b = solver.bv_const(0x0F, 8);
    let expected = solver.bv_const(0x00, 8);
    let result = solver.bvnor(a, b);
    assert_eq!(
        result, expected,
        "bvnor(0xF0, 0x0F) should constant-fold to 0x00"
    );
}

#[test]
fn test_bvxnor_constant_folding() {
    // bvxnor(0xAA, 0x55) = bvnot(bvxor(0xAA, 0x55)) = bvnot(0xFF) = 0x00
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.bv_const(0xAA, 8);
    let b = solver.bv_const(0x55, 8);
    let expected = solver.bv_const(0x00, 8);
    let result = solver.bvxnor(a, b);
    assert_eq!(
        result, expected,
        "bvxnor(0xAA, 0x55) should constant-fold to 0x00"
    );
}

#[test]
fn test_bvxnor_same_args() {
    // bvxnor(x, x) = bvnot(bvxor(x, x)) = bvnot(0) = all_ones
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.bv_const(0x42, 8);
    let expected = solver.bv_const(0xFF, 8);
    let result = solver.bvxnor(a, a);
    assert_eq!(
        result, expected,
        "bvxnor(x, x) should constant-fold to all-ones"
    );
}

#[test]
fn test_bvcomp_equal_constants() {
    // bvcomp(0x42, 0x42) = #b1
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.bv_const(0x42, 8);
    let b = solver.bv_const(0x42, 8);
    let expected = solver.bv_const(1, 1);
    let result = solver.bvcomp(a, b);
    assert_eq!(result, expected, "bvcomp(0x42, 0x42) should be #b1");
}

#[test]
fn test_bvcomp_unequal_constants() {
    // bvcomp(0x42, 0x43) = #b0
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.bv_const(0x42, 8);
    let b = solver.bv_const(0x43, 8);
    let expected = solver.bv_const(0, 1);
    let result = solver.bvcomp(a, b);
    assert_eq!(result, expected, "bvcomp(0x42, 0x43) should be #b0");
}

#[test]
fn test_bvcomp_symbolic() {
    // Find x such that bvcomp(x, 0x42) = #b1 => x = 0x42
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(8));
    let target = solver.bv_const(0x42, 8);
    let cmp = solver.bvcomp(x, target);
    let one = solver.bv_const(1, 1);
    let eq = solver.eq(cmp, one);
    solver.assert_term(eq);
    assert_eq!(solver.check_sat(), SolveResult::Sat);
    let model = solver.model().expect("Expected model").into_inner();
    let x_val = model.bv_val("x").expect("x should be in model");
    assert_eq!(x_val.0, BigInt::from(0x42));
}

#[test]
fn test_bvnand_symbolic() {
    // Verify bvnand(x, y) = bvnot(bvand(x, y)) symbolically
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(8));
    let y = solver.declare_const("y", Sort::bitvec(8));
    let nand_result = solver.bvnand(x, y);
    let and_result = solver.bvand(x, y);
    let not_and = solver.bvnot(and_result);
    // Assert nand(x,y) != not(and(x,y)) -- should be UNSAT (they are equal)
    let neq = solver.distinct(&[nand_result, not_and]);
    solver.assert_term(neq);
    assert!(
        solver.check_sat().is_unsat(),
        "bvnand(x,y) must equal bvnot(bvand(x,y))"
    );
}

#[test]
fn test_bvnor_symbolic() {
    // Verify bvnor(x, y) = bvnot(bvor(x, y)) symbolically
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(8));
    let y = solver.declare_const("y", Sort::bitvec(8));
    let nor_result = solver.bvnor(x, y);
    let or_result = solver.bvor(x, y);
    let not_or = solver.bvnot(or_result);
    let neq = solver.distinct(&[nor_result, not_or]);
    solver.assert_term(neq);
    assert!(
        solver.check_sat().is_unsat(),
        "bvnor(x,y) must equal bvnot(bvor(x,y))"
    );
}

#[test]
fn test_bvxnor_symbolic() {
    // Verify bvxnor(x, y) = bvnot(bvxor(x, y)) symbolically
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(8));
    let y = solver.declare_const("y", Sort::bitvec(8));
    let xnor_result = solver.bvxnor(x, y);
    let xor_result = solver.bvxor(x, y);
    let not_xor = solver.bvnot(xor_result);
    let neq = solver.distinct(&[xnor_result, not_xor]);
    solver.assert_term(neq);
    assert!(
        solver.check_sat().is_unsat(),
        "bvxnor(x,y) must equal bvnot(bvxor(x,y))"
    );
}

#[test]
fn test_try_bvnand_type_error() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let result = solver.try_bvnand(x, y);
    assert!(matches!(result, Err(SolverError::SortMismatch { .. })));
}

#[test]
fn test_try_bvnor_type_error() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let result = solver.try_bvnor(x, y);
    assert!(matches!(result, Err(SolverError::SortMismatch { .. })));
}

#[test]
fn test_try_bvxnor_type_error() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let result = solver.try_bvxnor(x, y);
    assert!(matches!(result, Err(SolverError::SortMismatch { .. })));
}

#[test]
fn test_try_bvcomp_type_error() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let result = solver.try_bvcomp(x, y);
    assert!(matches!(result, Err(SolverError::SortMismatch { .. })));
}

#[test]
fn test_try_bvcomp_width_mismatch() {
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(8));
    let y = solver.declare_const("y", Sort::bitvec(16));
    let result = solver.try_bvcomp(x, y);
    assert!(matches!(result, Err(SolverError::SortMismatch { .. })));
}

// ---------------------------------------------------------------------------
// BV↔Int symbolic modular congruence for the QfBvLia bridge (fix#7).
//
// These canaries pin the soundness of the new exact congruence
// `bv2nat(int2bv(s,w)) = s - 2^w * k` (k fresh, unconstrained), plus the
// `0 <= . < 2^w` bound. The dominant hazard is FALSE-UNSAT, so the
// SAT-preservation canaries are load-bearing: a satisfiable BV↔Int formula
// must stay SAT after the congruence is added.
// ---------------------------------------------------------------------------

/// SAT-PRESERVATION canary: `bv2nat(int2bv(x,8)) = 5` AND `x = 5` is SAT.
/// The residue of 5 mod 256 is 5, so the congruence (k=0) must admit this.
#[test]
fn test_bv_lia_congruence_preserves_sat_no_wrap_fix7() {
    let mut solver = Solver::new(Logic::Uflia);
    let x = solver.declare_const("x", Sort::Int);
    let residue = solver.int2bv(x, 8);
    let residue_nat = solver.bv2int(residue);
    let five = solver.int_const(5);
    let eq_residue = solver.eq(residue_nat, five);
    let eq_x = solver.eq(x, five);
    solver.assert_term(eq_residue);
    solver.assert_term(eq_x);
    let result = solver.check_sat();
    assert!(
        !result.is_unsat(),
        "bv2nat(int2bv(x,8))=5 AND x=5 must NOT be UNSAT (residue of 5 is 5), got {result:?}"
    );
}

/// SAT-PRESERVATION canary (wrap case): `bv2nat(int2bv(x,8)) = 5` AND `x = 261`
/// is SAT because 261 = 5 + 256, so the residue is 5 with slack k=1. If the
/// `2^w*k` slack were dropped, this would wrongly become UNSAT.
#[test]
fn test_bv_lia_congruence_preserves_sat_with_wrap_fix7() {
    let mut solver = Solver::new(Logic::Uflia);
    let x = solver.declare_const("x", Sort::Int);
    let residue = solver.int2bv(x, 8);
    let residue_nat = solver.bv2int(residue);
    let five = solver.int_const(5);
    let n261 = solver.int_const(261);
    let eq_residue = solver.eq(residue_nat, five);
    let eq_x = solver.eq(x, n261);
    solver.assert_term(eq_residue);
    solver.assert_term(eq_x);
    let result = solver.check_sat();
    assert!(
        !result.is_unsat(),
        "bv2nat(int2bv(x,8))=5 AND x=261 must NOT be UNSAT (261 mod 256 = 5, slack k=1), got {result:?}"
    );
}

/// WIDE-WIDTH UNSAT that enumeration (cap 2^16) cannot reach: width 32,
/// `bv2nat(int2bv(x,32)) = 7` AND `x = 3`. Since 0 <= 3 < 2^32, the source does
/// not wrap, so the exact congruence forces the residue to equal 3, which
/// contradicts 7. The general LIA solver derives this; enumeration over 2^32
/// values cannot. Returns UNSAT only thanks to the new congruence.
#[test]
fn test_bv_lia_congruence_wide_width_unsat_fix7() {
    let mut solver = Solver::new(Logic::Uflia);
    let x = solver.declare_const("x", Sort::Int);
    let residue = solver.int2bv(x, 32);
    let residue_nat = solver.bv2int(residue);
    let seven = solver.int_const(7);
    let three = solver.int_const(3);
    let eq_residue = solver.eq(residue_nat, seven);
    let eq_x = solver.eq(x, three);
    solver.assert_term(eq_residue);
    solver.assert_term(eq_x);
    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "bv2nat(int2bv(x,32))=7 AND x=3 must be UNSAT (residue of 3 is 3, not 7), got {result:?}"
    );
}

/// WIDE-WIDTH SAT-preservation companion: the same width-32 formula with a
/// consistent residue (`= 3`, `x = 3`) must stay SAT — guarding against the
/// congruence over-constraining at wide widths.
#[test]
fn test_bv_lia_congruence_wide_width_sat_fix7() {
    let mut solver = Solver::new(Logic::Uflia);
    let x = solver.declare_const("x", Sort::Int);
    let residue = solver.int2bv(x, 32);
    let residue_nat = solver.bv2int(residue);
    let three = solver.int_const(3);
    let eq_residue = solver.eq(residue_nat, three);
    let eq_x = solver.eq(x, three);
    solver.assert_term(eq_residue);
    solver.assert_term(eq_x);
    let result = solver.check_sat();
    assert!(
        !result.is_unsat(),
        "bv2nat(int2bv(x,32))=3 AND x=3 must NOT be UNSAT, got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Native dense-BV solve-boundary resource envelope.
// ---------------------------------------------------------------------------

const FIRST_UNSUPPORTED_NATIVE_BV_WIDTH: u32 = (1 << 20) + 1;

#[test]
fn native_bv_boundary_rejects_unused_nested_declaration_sort() {
    // `declare_const` accepts native Sort values directly. The nested BV never
    // appears below an assertion, but SAT model completion still enumerates
    // declarations, so the symbol-signature scan must catch it.
    let mut solver = Solver::new(Logic::All);
    let nested = Sort::array(
        Sort::Int,
        Sort::seq(Sort::bitvec(FIRST_UNSUPPORTED_NATIVE_BV_WIDTH)),
    );
    let _array = solver.declare_const("oversized_nested_array", nested);

    let result = solver.check_sat();
    assert!(result.is_unknown());
    assert_eq!(solver.unknown_reason(), Some(UnknownReason::Incomplete));
}

#[test]
fn native_bv_boundary_scans_derived_assumption_dag() {
    // Extension can amplify individually-supported one-bit variables past the
    // dense-BV envelope. Only the temporary assumption reaches these terms.
    let mut solver = Solver::new(Logic::All);
    let x = solver.bv_var("small_x", 1);
    let y = solver.bv_var("small_y", 1);
    let wide_x = solver.bvzeroext(x, 1 << 20);
    let wide_y = solver.bvzeroext(y, 1 << 20);
    let assumption = solver.eq(wide_x, wide_y);

    let result = solver.check_sat_assuming(&[assumption]);
    assert!(result.is_unknown());
    assert_eq!(solver.unknown_reason(), Some(UnknownReason::Incomplete));
}

#[test]
fn native_bv_boundary_scans_unused_quantifier_binder_sort() {
    // The bound variable is deliberately absent from the body. Its width lives
    // only in `TermData::Forall` metadata, not in the Bool term/body sorts.
    let mut solver = Solver::new(Logic::All);
    let bound = solver.fresh_var(
        "oversized_bound",
        Sort::bitvec(FIRST_UNSUPPORTED_NATIVE_BV_WIDTH),
    );
    let truth = solver.bool_const(true);
    let quantified = solver.forall(&[bound], truth);
    solver.assert_term(quantified);

    assert!(solver.check_sat().is_unknown());
}

#[test]
fn native_bv_boundary_scans_optimization_objective_dag() {
    // Objective solving bypasses `check_sat_guarded`, and `int2bv` historically
    // accepted an arbitrary native width. The objective DAG needs the same
    // preflight before finite-domain binary search computes 2^width.
    let mut solver = Solver::new(Logic::All);
    let x = solver.int_var("objective_source");
    let oversized = solver.int2bv(x, FIRST_UNSUPPORTED_NATIVE_BV_WIDTH);
    solver.maximize(oversized);

    assert!(solver.optimize_check().is_unknown());
}

#[test]
fn native_bv_boundary_scans_maxsmt_soft_dag_before_scaffolding() {
    // Native soft terms are installed only for `check_sat_max`; preflight them
    // before relaxation/cardinality scaffolding rather than waiting for a later
    // feasibility probe to rediscover the unsupported width.
    let mut solver = Solver::new(Logic::All);
    let x = solver.int_var("soft_source_x");
    let y = solver.int_var("soft_source_y");
    let oversized_x = solver.int2bv(x, FIRST_UNSUPPORTED_NATIVE_BV_WIDTH);
    let oversized_y = solver.int2bv(y, FIRST_UNSUPPORTED_NATIVE_BV_WIDTH);
    let soft = solver.eq(oversized_x, oversized_y);
    solver.assert_soft(soft, 1, None).unwrap();

    let result = solver.check_sat_max().unwrap();
    assert_eq!(result.status, MaxSmtStatus::Unknown);
}
