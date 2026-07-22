// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! VerifierConsumer consumer parity tests (#8291).
//!
//! This module exercises every AY Solver API surface that VerifierConsumer uses,
//! ensuring that future API changes do not silently break the consumer.
//! VerifierConsumer uses AY for verification condition checking with bitvectors,
//! arrays, integer arithmetic, and incremental solving.
//!
//! API surfaces covered:
//! - BV sort creation (8, 16, 32, 64 widths)
//! - BV arithmetic: bvadd, bvsub, bvmul
//! - BV bitwise: bvand, bvor, bvxor, bvnot
//! - BV shifts: bvshl, bvlshr, bvashr
//! - BV division: bvudiv, bvsdiv, bvurem, bvsrem
//! - BV comparisons: bvult, bvslt, bvule, bvuge, bvugt, bvsle, bvsgt, bvsge
//! - Extract/concat/extend: bvextract, bvconcat, bvzeroext, bvsignext
//! - BV overflow predicates
//! - Array(BV64, BV8): select, store
//! - Incremental push/pop with BV assertions
//! - check_sat, check_sat_assuming with BV
//! - Model generation: model_map() with BV values, ModelValue::BitVec
//! - Unsat core extraction with named BV assertions
//! - accept_for_consumer() on SAT/UNSAT results
//! - SolveResult pattern matching (Sat, Unsat, Unknown)

use num_bigint::BigInt;

use crate::api::*;

// =========================================================================
// BV sort creation
// =========================================================================

#[test]
fn test_trust_bv_sort_creation_multiple_widths() {
    for width in [8u32, 16, 32, 64] {
        let sort = Sort::bitvec(width);
        assert!(
            sort.is_bitvec(),
            "Sort::bitvec({width}) must report is_bitvec() = true"
        );
        assert_eq!(
            sort.bitvec_width(),
            Some(width),
            "Sort::bitvec({width}) must have width {width}"
        );
    }
}

// =========================================================================
// BV arithmetic
// =========================================================================

#[test]
fn test_trust_bv_arithmetic_add() {
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(32));
    let y = solver.declare_const("y", Sort::bitvec(32));
    let sum = solver.bvadd(x, y);
    let ten = solver.bv_const(10, 32);
    let eq = solver.eq(sum, ten);
    solver.assert_term(eq);
    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "bvadd(x, y) = 10 must be satisfiable"
    );
}

#[test]
fn test_trust_bv_arithmetic_sub_identity() {
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(32));
    let diff = solver.bvsub(x, x);
    let zero = solver.bv_const(0, 32);
    let eq = solver.eq(diff, zero);
    solver.assert_term(eq);
    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "bvsub(x, x) = 0 must be satisfiable"
    );
}

#[test]
fn test_trust_bv_arithmetic_mul_identity() {
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(32));
    let one = solver.bv_const(1, 32);
    let prod = solver.bvmul(x, one);
    let eq = solver.eq(prod, x);
    solver.assert_term(eq);
    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "bvmul(x, 1) = x must be satisfiable"
    );
}

// =========================================================================
// BV bitwise operations
// =========================================================================

#[test]
fn test_trust_bv_bitwise_and_or_xor_not() {
    let mut solver = Solver::new(Logic::QfBv);

    // bvand(0xF0, 0x3C) = 0x30
    let a = solver.bv_const(0xF0, 8);
    let b = solver.bv_const(0x3C, 8);
    let result_and = solver.bvand(a, b);
    let expected_and = solver.bv_const(0x30, 8);
    assert_eq!(result_and, expected_and, "bvand constant folding");

    // bvor(0xF0, 0x0F) = 0xFF
    let c = solver.bv_const(0x0F, 8);
    let result_or = solver.bvor(a, c);
    let expected_or = solver.bv_const(0xFF, 8);
    assert_eq!(result_or, expected_or, "bvor constant folding");

    // bvxor(0xAA, 0x55) = 0xFF
    let d = solver.bv_const(0xAA, 8);
    let e = solver.bv_const(0x55, 8);
    let result_xor = solver.bvxor(d, e);
    let expected_xor = solver.bv_const(0xFF, 8);
    assert_eq!(result_xor, expected_xor, "bvxor constant folding");

    // bvnot(0xA5) = 0x5A
    let f = solver.bv_const(0xA5, 8);
    let result_not = solver.bvnot(f);
    let expected_not = solver.bv_const(0x5A, 8);
    assert_eq!(result_not, expected_not, "bvnot constant folding");
}

#[test]
fn test_trust_bv_bitwise_demorgan() {
    // De Morgan: ~(a & b) = (~a) | (~b) for all 8-bit a, b
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.declare_const("a", Sort::bitvec(8));
    let b = solver.declare_const("b", Sort::bitvec(8));

    let a_and_b = solver.bvand(a, b);
    let not_a_and_b = solver.bvnot(a_and_b);

    let not_a = solver.bvnot(a);
    let not_b = solver.bvnot(b);
    let not_a_or_not_b = solver.bvor(not_a, not_b);

    let eq = solver.eq(not_a_and_b, not_a_or_not_b);
    solver.assert_term(eq);

    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "De Morgan's law for BV must be satisfiable"
    );
}

// =========================================================================
// BV shifts
// =========================================================================

#[test]
fn test_trust_bv_shifts_all() {
    let mut solver = Solver::new(Logic::QfBv);

    // bvshl(1, 4) = 16
    let a = solver.bv_const(1, 8);
    let b = solver.bv_const(4, 8);
    let shl_result = solver.bvshl(a, b);
    let expected_shl = solver.bv_const(16, 8);
    assert_eq!(shl_result, expected_shl, "bvshl(1, 4) = 16");

    // bvlshr(0x80, 4) = 0x08
    let c = solver.bv_const(0x80, 8);
    let lshr_result = solver.bvlshr(c, b);
    let expected_lshr = solver.bv_const(0x08, 8);
    assert_eq!(lshr_result, expected_lshr, "bvlshr(0x80, 4) = 0x08");

    // bvashr(0x80, 4) = 0xF8 (sign-extended: -128 >> 4 = -8)
    let ashr_result = solver.bvashr(c, b);
    let expected_ashr = solver.bv_const(0xF8u64 as i64, 8);
    assert_eq!(
        ashr_result, expected_ashr,
        "bvashr(0x80, 4) = 0xF8 (arithmetic shift preserves sign)"
    );
}

// =========================================================================
// BV division
// =========================================================================

#[test]
fn test_trust_bv_division_all() {
    let mut solver = Solver::new(Logic::QfBv);

    // bvudiv(100, 10) = 10
    let a = solver.bv_const(100, 8);
    let b = solver.bv_const(10, 8);
    let udiv = solver.bvudiv(a, b);
    let expected_udiv = solver.bv_const(10, 8);
    assert_eq!(udiv, expected_udiv, "bvudiv(100, 10) = 10");

    // bvurem(100, 10) = 0
    let urem = solver.bvurem(a, b);
    let expected_urem = solver.bv_const(0, 8);
    assert_eq!(urem, expected_urem, "bvurem(100, 10) = 0");

    // Symbolic sdiv/srem: -6 / 3 = -2
    let neg6 = solver.bv_const(-6i64, 8);
    let three = solver.bv_const(3, 8);
    let sdiv = solver.bvsdiv(neg6, three);
    let expected_sdiv = solver.bv_const(-2i64, 8);
    assert_eq!(sdiv, expected_sdiv, "bvsdiv(-6, 3) = -2");

    // bvsrem(-7, 3) = -1
    let neg7 = solver.bv_const(-7i64, 8);
    let srem = solver.bvsrem(neg7, three);
    let expected_srem = solver.bv_const(-1i64, 8);
    assert_eq!(srem, expected_srem, "bvsrem(-7, 3) = -1");
}

// =========================================================================
// BV comparisons (unsigned)
// =========================================================================

#[test]
fn test_trust_bv_comparisons_unsigned() {
    let mut solver = Solver::new(Logic::QfBv);

    let one = solver.bv_const(1, 8);
    let two = solver.bv_const(2, 8);
    let t = solver.bool_const(true);
    let f = solver.bool_const(false);

    // bvult(1, 2) = true
    let ult = solver.bvult(one, two);
    assert_eq!(ult, t, "bvult(1, 2) = true");

    // bvule(1, 2) = true
    let ule = solver.bvule(one, two);
    assert_eq!(ule, t, "bvule(1, 2) = true");

    // bvugt(1, 2) = false
    let ugt = solver.bvugt(one, two);
    assert_eq!(ugt, f, "bvugt(1, 2) = false");

    // bvuge(2, 1) = true
    let uge = solver.bvuge(two, one);
    assert_eq!(uge, t, "bvuge(2, 1) = true");
}

// =========================================================================
// BV comparisons (signed)
// =========================================================================

#[test]
fn test_trust_bv_comparisons_signed() {
    let mut solver = Solver::new(Logic::QfBv);

    // -1 (0xFF as signed) < 0 (signed)
    let neg1 = solver.bv_const(-1i64, 8);
    let zero = solver.bv_const(0, 8);
    let one = solver.bv_const(1, 8);
    let t = solver.bool_const(true);
    let f = solver.bool_const(false);

    // bvslt(-1, 0) = true
    let slt = solver.bvslt(neg1, zero);
    assert_eq!(slt, t, "bvslt(-1, 0) = true");

    // bvsle(-1, 0) = true
    let sle = solver.bvsle(neg1, zero);
    assert_eq!(sle, t, "bvsle(-1, 0) = true");

    // bvsgt(1, -1) = true
    let sgt = solver.bvsgt(one, neg1);
    assert_eq!(sgt, t, "bvsgt(1, -1) = true");

    // bvsge(0, -1) = true
    let sge = solver.bvsge(zero, neg1);
    assert_eq!(sge, t, "bvsge(0, -1) = true");

    // bvslt(0, -1) = false (0 > -1 signed)
    let slt2 = solver.bvslt(zero, neg1);
    assert_eq!(slt2, f, "bvslt(0, -1) = false");
}

// =========================================================================
// Extract / Concat / Extend
// =========================================================================

#[test]
fn test_trust_bv_extract_concat_extend() {
    let mut solver = Solver::new(Logic::QfBv);

    // Extract: bvextract(0xABCD_16bit, 11, 4) = 0xBC_8bit
    let val16 = solver.bv_const(0xABCD, 16);
    let extracted = solver.bvextract(val16, 11, 4);
    let expected_extract = solver.bv_const(0xBC, 8);
    assert_eq!(
        extracted, expected_extract,
        "bvextract(0xABCD, 11, 4) = 0xBC"
    );

    // Concat: bvconcat(0xAB_8bit, 0xCD_8bit) = 0xABCD_16bit
    let hi = solver.bv_const(0xAB, 8);
    let lo = solver.bv_const(0xCD, 8);
    let concatenated = solver.bvconcat(hi, lo);
    let expected_concat = solver.bv_const(0xABCD, 16);
    assert_eq!(
        concatenated, expected_concat,
        "bvconcat(0xAB, 0xCD) = 0xABCD"
    );

    // Zero-extend: bvzeroext(0x42_8bit, 8) = 0x0042_16bit
    let val8 = solver.bv_const(0x42, 8);
    let zero_ext = solver.bvzeroext(val8, 8);
    let expected_zext = solver.bv_const(0x0042, 16);
    assert_eq!(zero_ext, expected_zext, "bvzeroext(0x42, 8) = 0x0042");

    // Sign-extend: bvsignext(0xFF_8bit, 8) = 0xFFFF_16bit
    let neg1_8 = solver.bv_const(-1i64, 8);
    let sign_ext = solver.bvsignext(neg1_8, 8);
    let expected_sext = solver.bv_const(-1i64, 16);
    assert_eq!(sign_ext, expected_sext, "bvsignext(0xFF, 8) = 0xFFFF");
}

// =========================================================================
// BV overflow predicates
// =========================================================================

#[test]
fn test_trust_bv_overflow_predicates_safe() {
    // Safe additions (no overflow/underflow) should be SAT
    let mut solver = Solver::new(Logic::QfBv);
    let five = solver.bv_const(5, 8);
    let three = solver.bv_const(3, 8);

    let a = solver.declare_const("a", Sort::bitvec(8));
    let b = solver.declare_const("b", Sort::bitvec(8));
    let ea = solver.eq(a, five);
    let eb = solver.eq(b, three);
    solver.assert_term(ea);
    solver.assert_term(eb);

    let add_safe = solver.bvadd_no_overflow(a, b, false);
    solver.assert_term(add_safe);
    let sub_safe = solver.bvsub_no_underflow(a, b, false);
    solver.assert_term(sub_safe);
    let mul_safe = solver.bvmul_no_overflow(a, b, false);
    solver.assert_term(mul_safe);
    let neg_safe = solver.bvneg_no_overflow(a);
    solver.assert_term(neg_safe);
    let div_safe = solver.bvsdiv_no_overflow(a, b);
    solver.assert_term(div_safe);

    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "small values must not overflow"
    );
}

#[test]
fn test_trust_bv_overflow_predicates_overflow() {
    // 0xFF + 0x01 unsigned overflows
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.declare_const("a", Sort::bitvec(8));
    let b = solver.declare_const("b", Sort::bitvec(8));
    let ff = solver.bv_const(0xFF, 8);
    let one = solver.bv_const(1, 8);
    let ea = solver.eq(a, ff);
    let eb = solver.eq(b, one);
    solver.assert_term(ea);
    solver.assert_term(eb);

    let no_overflow = solver.bvadd_no_overflow(a, b, false);
    solver.assert_term(no_overflow);

    assert!(
        solver.check_sat().is_unsat(),
        "0xFF + 0x01 unsigned must overflow (UNSAT)"
    );
}

// =========================================================================
// Array(BV64, BV8) select/store
// =========================================================================

#[test]
fn test_trust_array_bv_select_store() {
    let mut solver = Solver::new(Logic::QfAbv);
    let arr = solver.declare_const("mem", Sort::array(Sort::bitvec(64), Sort::bitvec(8)));
    let addr = solver.bv_const(0x1000, 64);
    let val = solver.bv_const(42, 8);

    // store(mem, 0x1000, 42)
    let updated = solver.store(arr, addr, val);
    // select(store(mem, 0x1000, 42), 0x1000) = 42
    let read_back = solver.select(updated, addr);
    let eq = solver.eq(read_back, val);
    solver.assert_term(eq);

    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "select(store(mem, addr, v), addr) = v must be SAT"
    );
}

// =========================================================================
// Incremental push/pop with BV
// =========================================================================

#[test]
fn test_trust_incremental_push_pop_bv() {
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(8));
    let ten = solver.bv_const(10, 8);
    let eq = solver.eq(x, ten);
    solver.assert_term(eq);

    // SAT: x = 10
    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "x = 10 must be SAT before push"
    );

    // Push and add contradiction
    solver.try_push().unwrap();
    let twenty = solver.bv_const(20, 8);
    let eq2 = solver.eq(x, twenty);
    solver.assert_term(eq2);

    assert!(
        solver.check_sat().is_unsat(),
        "x = 10 AND x = 20 must be UNSAT inside push scope"
    );

    // Pop removes the contradiction
    solver.try_pop().unwrap();
    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "x = 10 must be SAT after pop"
    );
}

// =========================================================================
// check_sat and check_sat_assuming
// =========================================================================

#[test]
fn test_trust_check_sat_basic_bv() {
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(16));
    let y = solver.declare_const("y", Sort::bitvec(16));
    let sum = solver.bvadd(x, y);
    let hundred = solver.bv_const(100, 16);
    let eq = solver.eq(sum, hundred);
    solver.assert_term(eq);
    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_trust_check_sat_assuming_bv() {
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(8));
    let five = solver.bv_const(5, 8);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);

    // Assumption: x < 3 contradicts x = 5
    let three = solver.bv_const(3, 8);
    let x_lt_3 = solver.bvult(x, three);
    let result = solver.check_sat_assuming(&[x_lt_3]);
    assert!(
        result.is_unsat(),
        "x = 5 AND x < 3 must be UNSAT via check_sat_assuming"
    );
}

// =========================================================================
// Model generation with BV values
// =========================================================================

#[test]
fn test_trust_model_generation_bv() {
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(8));
    let forty_two = solver.bv_const(42, 8);
    let eq = solver.eq(x, forty_two);
    solver.assert_term(eq);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    // model_map() must return x -> BitVec { value: 42, width: 8 }
    let map = solver
        .model_map()
        .expect("model_map must be Some after SAT");
    let x_val = map.get("x").expect("x must be present in model_map");
    assert_eq!(
        *x_val,
        ModelValue::BitVec {
            value: BigInt::from(42),
            width: 8
        },
        "model_map must contain BitVec variant for x"
    );
}

#[test]
fn test_trust_model_generation_bv_via_get_model() {
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(32));
    let val = solver.bv_const(0xDEAD_BEEF_u64 as i64, 32);
    let eq = solver.eq(x, val);
    solver.assert_term(eq);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let model = solver.model().expect("model after SAT").into_inner();
    let (bv_val, bv_width) = model.bv_val("x").expect("x must be in model as BV");
    // 0xDEAD_BEEF as unsigned 32-bit = 3735928559
    assert_eq!(bv_val, BigInt::from(0xDEAD_BEEFu64), "BV value mismatch");
    assert_eq!(bv_width, 32, "BV width mismatch");
}

// =========================================================================
// Unsat core with named BV assertions
// =========================================================================

#[test]
fn test_trust_unsat_core_bv() {
    let mut solver = Solver::new(Logic::QfBv);
    solver.set_produce_unsat_cores(true);

    let x = solver.declare_const("x", Sort::bitvec(8));
    let ten = solver.bv_const(10, 8);
    let twenty = solver.bv_const(20, 8);

    let x_eq_10 = solver.eq(x, ten);
    solver.try_assert_named(x_eq_10, "x_is_10").unwrap();

    let x_eq_20 = solver.eq(x, twenty);
    solver.try_assert_named(x_eq_20, "x_is_20").unwrap();

    assert!(solver.check_sat().is_unsat());
    let core = solver.try_get_unsat_core().unwrap();
    assert!(
        core.contains(&"x_is_10".to_string()),
        "unsat core must contain 'x_is_10': {core:?}"
    );
    assert!(
        core.contains(&"x_is_20".to_string()),
        "unsat core must contain 'x_is_20': {core:?}"
    );
}

// =========================================================================
// accept_for_consumer
// =========================================================================

#[test]
fn test_trust_accept_for_consumer_sat() {
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(8));
    let five = solver.bv_const(5, 8);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);

    let details = solver.check_sat_with_details();
    assert_eq!(details.result, SolveResult::Sat);
    assert!(
        details.accept_for_consumer().is_ok(),
        "SAT with model validation must be accepted for consumer"
    );
}

#[test]
fn test_trust_accept_for_consumer_unsat() {
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(8));
    let five = solver.bv_const(5, 8);
    let ten = solver.bv_const(10, 8);
    let eq1 = solver.eq(x, five);
    let eq2 = solver.eq(x, ten);
    solver.assert_term(eq1);
    solver.assert_term(eq2);

    let details = solver.check_sat_with_details();
    assert_eq!(details.result, SolveResult::unsat());
    let accepted = details.accept_for_consumer();
    assert!(
        accepted.is_ok(),
        "UNSAT must always be accepted for consumer"
    );
    assert!(
        accepted.unwrap().is_unsat(),
        "accepted UNSAT must report is_unsat()"
    );
}

// =========================================================================
// SolveResult pattern matching
// =========================================================================

#[test]
fn test_trust_solve_result_pattern_matching() {
    // Sat
    let sat = SolveResult::Sat;
    assert!(sat.is_sat());
    assert!(!sat.is_unsat());
    assert!(!sat.is_unknown());
    match sat {
        SolveResult::Sat => {} // expected
        _ => panic!("expected Sat variant"),
    }

    // Unsat (with certificate)
    let unsat = SolveResult::unsat();
    assert!(!unsat.is_sat());
    assert!(unsat.is_unsat());
    assert!(!unsat.is_unknown());
    match unsat {
        SolveResult::Unsat(_cert) => {} // expected: Unsat carries a certificate
        _ => panic!("expected Unsat variant"),
    }

    // Unknown
    let unknown = SolveResult::Unknown;
    assert!(!unknown.is_sat());
    assert!(!unknown.is_unsat());
    assert!(unknown.is_unknown());
    match unknown {
        SolveResult::Unknown => {} // expected
        _ => panic!("expected Unknown variant"),
    }

    // Display
    assert_eq!(format!("{}", SolveResult::Sat), "sat");
    assert_eq!(format!("{}", SolveResult::unsat()), "unsat");
    assert_eq!(format!("{}", SolveResult::Unknown), "unknown");
}

// =========================================================================
// Multi-width BV solving (VerifierConsumer uses 8, 16, 32, 64)
// =========================================================================

#[test]
fn test_trust_bv_multi_width_solving() {
    for width in [8u32, 16, 32, 64] {
        let mut solver = Solver::new(Logic::QfBv);
        let x = solver.declare_const("x", Sort::bitvec(width));
        let y = solver.declare_const("y", Sort::bitvec(width));

        // x + y = x (i.e., y = 0) — verify basic arithmetic at each width
        let sum = solver.bvadd(x, y);
        let eq = solver.eq(sum, x);
        solver.assert_term(eq);

        assert_eq!(
            solver.check_sat(),
            SolveResult::Sat,
            "BV{width}: x + y = x must be SAT (y = 0 is a model)"
        );
    }
}

// =========================================================================
// BV bvneg constant folding
// =========================================================================

#[test]
fn test_trust_bv_neg() {
    let mut solver = Solver::new(Logic::QfBv);
    // bvneg(1) = 0xFF (two's complement -1)
    let one = solver.bv_const(1, 8);
    let neg_one = solver.bvneg(one);
    let expected = solver.bv_const(0xFF, 8);
    assert_eq!(neg_one, expected, "bvneg(1) = 0xFF");
}

// =========================================================================
// Executor-based SMT-LIB text interface (VerifierConsumer's actual usage path)
// =========================================================================

#[test]
fn test_trust_executor_text_interface() {
    // VerifierConsumer's actual integration uses Executor + parse (text-based SMT-LIB2)
    use crate::Executor;
    use ay_frontend::parse;

    let script = "\
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(assert (< x 10))
(check-sat)
";
    let commands = parse(script).expect("parse must succeed");
    let mut executor = Executor::new();
    let outputs = executor
        .execute_all(&commands)
        .expect("execute_all must succeed");

    assert!(
        outputs.iter().any(|o| o == "sat"),
        "Executor must return sat for x > 0 AND x < 10: {outputs:?}"
    );
}

#[test]
fn test_trust_executor_unsat() {
    use crate::Executor;
    use ay_frontend::parse;

    let script = "\
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(assert (< x 0))
(check-sat)
";
    let commands = parse(script).expect("parse must succeed");
    let mut executor = Executor::new();
    let outputs = executor
        .execute_all(&commands)
        .expect("execute_all must succeed");

    assert!(
        outputs.iter().any(|o| o == "unsat"),
        "Executor must return unsat for x > 0 AND x < 0: {outputs:?}"
    );
}

// Repro for the aterm base64::encode false-overflow bug, Int/LIA framing.
//
// This is the abstraction VerifierConsumer hands to AY: usize is a bounded Int,
// bvudiv len 3 becomes integer (div len 3). The verifier asks whether the
// derived full_chunks `fc` can reach usize::MAX (overflow witness for fc+1).
//
//   len : Int, 0 <= len <= isize::MAX (0x7FFF_FFFF_FFFF_FFFF = 9223372036854775807)
//   fc  : Int, fc = (div len 3)
//   assert fc = usize::MAX (18446744073709551615)
//
// Correct: UNSAT, since fc = len/3 <= 9223372036854775807/3 = 3074457345618258602.
// Bug: extension bound-propagation only asserts the trivial type bound
// (fc <= 18446744073709551615) and never derives fc <= isize::MAX/3 from the
// div relation, so it returns SAT with fc = usize::MAX.
#[test]
fn test_trust_executor_udiv_overflow_witness_int_unsat() {
    use crate::Executor;
    use ay_frontend::parse;

    let script = "\
(set-logic QF_LIA)
(declare-const len Int)
(declare-const fc Int)
(assert (<= 0 len))
(assert (<= len 9223372036854775807))
(assert (= fc (div len 3)))
(assert (= fc 18446744073709551615))
(check-sat)
";
    let commands = parse(script).expect("parse must succeed");
    let mut executor = Executor::new();
    let outputs = executor
        .execute_all(&commands)
        .expect("execute_all must succeed");

    assert!(
        outputs.iter().any(|o| o == "unsat"),
        "fc = len/3 <= isize::MAX/3 cannot reach usize::MAX, must be unsat: {outputs:?}"
    );
}

// =========================================================================
// BV with arrays: store-select identity across widths
// =========================================================================

#[test]
fn test_trust_array_bv64_bv8_store_select_identity() {
    // Array(BV64, BV8) is the canonical memory model for VerifierConsumer
    let mut solver = Solver::new(Logic::QfAbv);
    let mem = solver.declare_const("mem", Sort::array(Sort::bitvec(64), Sort::bitvec(8)));

    // Store at two different addresses
    let addr1 = solver.bv_const(0x100, 64);
    let addr2 = solver.bv_const(0x200, 64);
    let val1 = solver.bv_const(0xAA, 8);
    let val2 = solver.bv_const(0x55, 8);

    let mem1 = solver.store(mem, addr1, val1);
    let mem2 = solver.store(mem1, addr2, val2);

    // Read back: select(mem2, addr1) = 0xAA, select(mem2, addr2) = 0x55
    let read1 = solver.select(mem2, addr1);
    let read2 = solver.select(mem2, addr2);
    let eq1 = solver.eq(read1, val1);
    let eq2 = solver.eq(read2, val2);
    solver.assert_term(eq1);
    solver.assert_term(eq2);

    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "multi-address store-select identity must be SAT"
    );
}

// =========================================================================
// get_value for BV terms
// =========================================================================

#[test]
fn test_trust_get_value_bv() {
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(16));
    let val = solver.bv_const(1234, 16);
    let eq = solver.eq(x, val);
    solver.assert_term(eq);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let model_val = solver.value(x);
    assert!(model_val.is_some(), "get_value must return Some after SAT");
    assert_eq!(
        model_val.unwrap(),
        ModelValue::BitVec {
            value: BigInt::from(1234),
            width: 16
        },
        "get_value must return correct BV value"
    );
}
