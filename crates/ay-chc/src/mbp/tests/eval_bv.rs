// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_eval_bv_arithmetic_operations() {
    let mbp = Mbp::new();
    let model = FxHashMap::default();

    // BV literal evaluation
    let bv5 = ChcExpr::BitVec(5, 8);
    let bv3 = ChcExpr::BitVec(3, 8);

    // bvadd(5, 3) = 8
    let add = ChcExpr::Op(
        ChcOp::BvAdd,
        vec![Arc::new(bv5.clone()), Arc::new(bv3.clone())],
    );
    assert_eq!(mbp.eval_bv(&add, &model), Some((8, 8)));

    // bvsub(5, 3) = 2
    let sub = ChcExpr::Op(
        ChcOp::BvSub,
        vec![Arc::new(bv5.clone()), Arc::new(bv3.clone())],
    );
    assert_eq!(mbp.eval_bv(&sub, &model), Some((2, 8)));

    // bvmul(5, 3) = 15
    let mul = ChcExpr::Op(
        ChcOp::BvMul,
        vec![Arc::new(bv5.clone()), Arc::new(bv3.clone())],
    );
    assert_eq!(mbp.eval_bv(&mul, &model), Some((15, 8)));

    // bvand(5, 3) = 1 (0b0101 & 0b0011 = 0b0001)
    let and = ChcExpr::Op(
        ChcOp::BvAnd,
        vec![Arc::new(bv5.clone()), Arc::new(bv3.clone())],
    );
    assert_eq!(mbp.eval_bv(&and, &model), Some((1, 8)));

    // bvor(5, 3) = 7 (0b0101 | 0b0011 = 0b0111)
    let or = ChcExpr::Op(ChcOp::BvOr, vec![Arc::new(bv5), Arc::new(bv3)]);
    assert_eq!(mbp.eval_bv(&or, &model), Some((7, 8)));
}

#[test]
fn test_eval_bv_wrapping_and_masking() {
    let mbp = Mbp::new();
    let model = FxHashMap::default();

    // 8-bit overflow: 255 + 1 = 0 (wraps)
    let bv255 = ChcExpr::BitVec(255, 8);
    let bv1 = ChcExpr::BitVec(1, 8);
    let add = ChcExpr::Op(ChcOp::BvAdd, vec![Arc::new(bv255), Arc::new(bv1)]);
    assert_eq!(mbp.eval_bv(&add, &model), Some((0, 8)));

    // bvneg(5) in 8-bit = 251 (two's complement)
    let bv5 = ChcExpr::BitVec(5, 8);
    let neg = ChcExpr::Op(ChcOp::BvNeg, vec![Arc::new(bv5)]);
    assert_eq!(mbp.eval_bv(&neg, &model), Some((251, 8)));
}

#[test]
fn test_eval_bv_variable_lookup() {
    let mbp = Mbp::new();
    let mut model = FxHashMap::default();
    model.insert("bv_idx".to_string(), SmtValue::BitVec(42, 32));

    let bv_var = ChcExpr::Var(ChcVar::new("bv_idx", ChcSort::BitVec(32)));
    assert_eq!(mbp.eval_bv(&bv_var, &model), Some((42, 32)));
}

#[test]
fn test_eval_bv_comparisons_in_eval_bool() {
    let mbp = Mbp::new();
    let model = FxHashMap::default();

    let bv5 = ChcExpr::BitVec(5, 8);
    let bv10 = ChcExpr::BitVec(10, 8);

    // bvult(5, 10) = true
    let ult = ChcExpr::Op(
        ChcOp::BvULt,
        vec![Arc::new(bv5.clone()), Arc::new(bv10.clone())],
    );
    assert_eq!(mbp.eval_bool(&ult, &model), Some(true));

    // bvult(10, 5) = false
    let ult2 = ChcExpr::Op(
        ChcOp::BvULt,
        vec![Arc::new(bv10.clone()), Arc::new(bv5.clone())],
    );
    assert_eq!(mbp.eval_bool(&ult2, &model), Some(false));

    // eq(bv5, bv5) = true via BV eval path
    let eq = ChcExpr::eq(bv5.clone(), bv5.clone());
    assert_eq!(mbp.eval_bool(&eq, &model), Some(true));

    // ne(bv5, bv10) = true via BV eval path
    let ne = ChcExpr::ne(bv5, bv10);
    assert_eq!(mbp.eval_bool(&ne, &model), Some(true));
}

#[test]
fn test_eval_bv_operations_via_eval_bool_eq() {
    let mbp = Mbp::new();
    let mut model = FxHashMap::default();
    model.insert("bv_x".to_string(), SmtValue::BitVec(7, 32));
    model.insert("bv_y".to_string(), SmtValue::BitVec(3, 32));

    // Test BV arithmetic through the eval_bool(Eq) path.
    // bvadd(bv_x, bv_y) == #x0000000A should be true (7+3=10)
    let bv_x = ChcExpr::Var(ChcVar::new("bv_x", ChcSort::BitVec(32)));
    let bv_y = ChcExpr::Var(ChcVar::new("bv_y", ChcSort::BitVec(32)));
    let add = ChcExpr::Op(ChcOp::BvAdd, vec![Arc::new(bv_x), Arc::new(bv_y)]);
    let eq = ChcExpr::eq(add, ChcExpr::BitVec(10, 32));
    assert_eq!(mbp.eval_bool(&eq, &model), Some(true));
}

/// eval_bv: BV unsigned division by zero returns all-ones (SMT-LIB spec).
#[test]
fn test_eval_bv_udiv_by_zero_returns_all_ones() {
    let mbp = Mbp::new();
    let model = FxHashMap::default();

    let bv5 = ChcExpr::BitVec(5, 8);
    let bv0 = ChcExpr::BitVec(0, 8);
    let udiv = ChcExpr::Op(ChcOp::BvUDiv, vec![Arc::new(bv5), Arc::new(bv0)]);
    // SMT-LIB: bvudiv(x, 0) = all-ones = 0xFF for 8-bit
    assert_eq!(mbp.eval_bv(&udiv, &model), Some((0xFF, 8)));
}

/// eval_bv: BV unsigned remainder by zero returns dividend (SMT-LIB spec).
#[test]
fn test_eval_bv_urem_by_zero_returns_dividend() {
    let mbp = Mbp::new();
    let model = FxHashMap::default();

    let bv5 = ChcExpr::BitVec(5, 8);
    let bv0 = ChcExpr::BitVec(0, 8);
    let urem = ChcExpr::Op(ChcOp::BvURem, vec![Arc::new(bv5), Arc::new(bv0)]);
    assert_eq!(mbp.eval_bv(&urem, &model), Some((5, 8)));
}

/// eval_bv: BV signed division by zero:
/// SMT-LIB bvsdiv(s, 0) = if s < 0 then 1 else all-ones (-1).
#[test]
fn test_eval_bv_sdiv_by_zero() {
    let mbp = Mbp::new();
    let model = FxHashMap::default();

    // Positive dividend: bvsdiv(5, 0) = -1 = 0xFF in 8-bit
    let bv5 = ChcExpr::BitVec(5, 8);
    let bv0 = ChcExpr::BitVec(0, 8);
    let sdiv_pos = ChcExpr::Op(ChcOp::BvSDiv, vec![Arc::new(bv5), Arc::new(bv0.clone())]);
    assert_eq!(mbp.eval_bv(&sdiv_pos, &model), Some((0xFF, 8)));

    // Negative dividend (-5 = 0xFB in 8-bit): bvsdiv(-5, 0) = 1
    let bv_neg5 = ChcExpr::BitVec(0xFB, 8); // -5 in two's complement
    let sdiv_neg = ChcExpr::Op(ChcOp::BvSDiv, vec![Arc::new(bv_neg5), Arc::new(bv0)]);
    assert_eq!(mbp.eval_bv(&sdiv_neg, &model), Some((1, 8)));
}

/// eval_bv: signed comparison via eval_bool.
/// 0xFE is -2 in 8-bit signed, 0x01 is 1. So bvslt(0xFE, 0x01) = true.
#[test]
fn test_eval_bv_signed_comparisons() {
    let mbp = Mbp::new();
    let model = FxHashMap::default();

    let bv_neg2 = ChcExpr::BitVec(0xFE, 8); // -2 signed
    let bv_1 = ChcExpr::BitVec(0x01, 8); // +1 signed

    // bvslt(-2, 1) = true
    let slt = ChcExpr::Op(
        ChcOp::BvSLt,
        vec![Arc::new(bv_neg2.clone()), Arc::new(bv_1.clone())],
    );
    assert_eq!(mbp.eval_bool(&slt, &model), Some(true));

    // bvslt(1, -2) = false
    let slt2 = ChcExpr::Op(
        ChcOp::BvSLt,
        vec![Arc::new(bv_1.clone()), Arc::new(bv_neg2.clone())],
    );
    assert_eq!(mbp.eval_bool(&slt2, &model), Some(false));

    // bvsge(1, -2) = true
    let sge = ChcExpr::Op(ChcOp::BvSGe, vec![Arc::new(bv_1), Arc::new(bv_neg2)]);
    assert_eq!(mbp.eval_bool(&sge, &model), Some(true));
}

/// eval_bv: extract, concat, sign-extend operations.
#[test]
fn test_eval_bv_extract_concat_sign_extend() {
    let mbp = Mbp::new();
    let model = FxHashMap::default();

    // Extract bits [3:0] from 0xAB (8-bit) = 0x0B = 11
    let bv_ab = ChcExpr::BitVec(0xAB, 8);
    let extract = ChcExpr::Op(ChcOp::BvExtract(3, 0), vec![Arc::new(bv_ab.clone())]);
    assert_eq!(mbp.eval_bv(&extract, &model), Some((0x0B, 4)));

    // Extract bits [7:4] from 0xAB = 0x0A = 10
    let extract_hi = ChcExpr::Op(ChcOp::BvExtract(7, 4), vec![Arc::new(bv_ab)]);
    assert_eq!(mbp.eval_bv(&extract_hi, &model), Some((0x0A, 4)));

    // Concat 0x0A (4-bit) with 0x0B (4-bit) = 0xAB (8-bit)
    let bv_a = ChcExpr::BitVec(0x0A, 4);
    let bv_b = ChcExpr::BitVec(0x0B, 4);
    let concat = ChcExpr::Op(ChcOp::BvConcat, vec![Arc::new(bv_a), Arc::new(bv_b)]);
    assert_eq!(mbp.eval_bv(&concat, &model), Some((0xAB, 8)));

    // Sign-extend 0xFE (8-bit, = -2 signed) by 8 bits → 0xFFFE (16-bit, = -2 signed)
    let bv_fe = ChcExpr::BitVec(0xFE, 8);
    let sext = ChcExpr::Op(ChcOp::BvSignExtend(8), vec![Arc::new(bv_fe)]);
    assert_eq!(mbp.eval_bv(&sext, &model), Some((0xFFFE, 16)));

    // Zero-extend 0xFE (8-bit) by 8 bits → 0x00FE (16-bit)
    let bv_fe2 = ChcExpr::BitVec(0xFE, 8);
    let zext = ChcExpr::Op(ChcOp::BvZeroExtend(8), vec![Arc::new(bv_fe2)]);
    assert_eq!(mbp.eval_bv(&zext, &model), Some((0xFE, 16)));
}

/// eval_bv: signed division with mixed signs and overflow edge cases.
/// SMT-LIB bvsdiv follows truncation-toward-zero semantics per the
/// four-branch definition in the BV theory spec.
#[test]
fn test_eval_bv_sdiv_mixed_signs_and_overflow() {
    let mbp = Mbp::new();
    let model = FxHashMap::default();

    // bvsdiv(5, -3) in 8-bit: positive / negative → result = -(5/3) = -1 = 0xFF
    // SMT-LIB: msb_s=0, msb_t=1 → bvneg(bvudiv(5, bvneg(0xFD))) = bvneg(bvudiv(5,3)) = bvneg(1) = 0xFF
    let bv5 = ChcExpr::BitVec(5, 8);
    let bv_neg3 = ChcExpr::BitVec(0xFD, 8); // -3 in 8-bit two's complement
    let sdiv = ChcExpr::Op(ChcOp::BvSDiv, vec![Arc::new(bv5), Arc::new(bv_neg3)]);
    assert_eq!(mbp.eval_bv(&sdiv, &model), Some((0xFF, 8))); // -1

    // bvsdiv(-5, 3) in 8-bit: negative / positive → result = -(5/3) = -1 = 0xFF
    // SMT-LIB: msb_s=1, msb_t=0 → bvneg(bvudiv(bvneg(0xFB), 3)) = bvneg(bvudiv(5,3)) = bvneg(1) = 0xFF
    let bv_neg5 = ChcExpr::BitVec(0xFB, 8); // -5 in 8-bit
    let bv3 = ChcExpr::BitVec(3, 8);
    let sdiv2 = ChcExpr::Op(ChcOp::BvSDiv, vec![Arc::new(bv_neg5), Arc::new(bv3)]);
    assert_eq!(mbp.eval_bv(&sdiv2, &model), Some((0xFF, 8))); // -1

    // bvsdiv(-128, -1) in 8-bit: signed overflow case.
    // SMT-LIB: both negative → bvudiv(bvneg(-128), bvneg(-1)) = bvudiv(128, 1) = 128 = 0x80
    let bv_min = ChcExpr::BitVec(0x80, 8); // -128 in 8-bit
    let bv_neg1 = ChcExpr::BitVec(0xFF, 8); // -1 in 8-bit
    let sdiv3 = ChcExpr::Op(ChcOp::BvSDiv, vec![Arc::new(bv_min), Arc::new(bv_neg1)]);
    assert_eq!(mbp.eval_bv(&sdiv3, &model), Some((0x80, 8))); // 128 = -128 (overflow wraps)
}

/// eval_bv: bvsmod sign follows divisor (not dividend, unlike bvsrem).
#[test]
fn test_eval_bv_smod_sign_follows_divisor() {
    let mbp = Mbp::new();
    let model = FxHashMap::default();

    // bvsmod(7, 3) = 1 (both positive, normal modulo)
    let bv7 = ChcExpr::BitVec(7, 8);
    let bv3 = ChcExpr::BitVec(3, 8);
    let smod = ChcExpr::Op(
        ChcOp::BvSMod,
        vec![Arc::new(bv7.clone()), Arc::new(bv3.clone())],
    );
    assert_eq!(mbp.eval_bv(&smod, &model), Some((1, 8)));

    // bvsmod(-7, 3) in 8-bit: dividend=-7, divisor=3 (positive).
    // rem = (-7) % 3 = -1. Since rem < 0 and divisor > 0: result = -1 + 3 = 2
    let bv_neg7 = ChcExpr::BitVec(0xF9, 8); // -7 in 8-bit
    let smod2 = ChcExpr::Op(ChcOp::BvSMod, vec![Arc::new(bv_neg7), Arc::new(bv3)]);
    assert_eq!(mbp.eval_bv(&smod2, &model), Some((2, 8))); // positive (follows divisor sign)

    // bvsmod(7, -3) in 8-bit: dividend=7, divisor=-3 (negative).
    // rem = 7 % (-3) = 1. Since rem > 0 and divisor < 0: result = 1 + (-3) = -2 = 0xFE
    let bv_neg3 = ChcExpr::BitVec(0xFD, 8); // -3 in 8-bit
    let smod3 = ChcExpr::Op(ChcOp::BvSMod, vec![Arc::new(bv7), Arc::new(bv_neg3)]);
    assert_eq!(mbp.eval_bv(&smod3, &model), Some((0xFE, 8))); // negative (follows divisor sign)
}

/// eval_bv: arithmetic shift right preserves sign bit.
#[test]
fn test_eval_bv_ashr_sign_extension() {
    let mbp = Mbp::new();
    let model = FxHashMap::default();

    // bvashr(0x80, 1) in 8-bit = -128 >> 1 = -64 = 0xC0 (sign-extended)
    let bv_min = ChcExpr::BitVec(0x80, 8);
    let bv1 = ChcExpr::BitVec(1, 8);
    let ashr = ChcExpr::Op(ChcOp::BvAShr, vec![Arc::new(bv_min.clone()), Arc::new(bv1)]);
    assert_eq!(mbp.eval_bv(&ashr, &model), Some((0xC0, 8)));

    // bvashr(0x80, 7) in 8-bit = -128 >> 7 = -1 = 0xFF (all ones from sign fill)
    let bv7 = ChcExpr::BitVec(7, 8);
    let ashr7 = ChcExpr::Op(ChcOp::BvAShr, vec![Arc::new(bv_min.clone()), Arc::new(bv7)]);
    assert_eq!(mbp.eval_bv(&ashr7, &model), Some((0xFF, 8)));

    // bvashr(0x80, 8) in 8-bit: shift >= width → all sign bits = 0xFF
    let bv8 = ChcExpr::BitVec(8, 8);
    let ashr_overflow = ChcExpr::Op(ChcOp::BvAShr, vec![Arc::new(bv_min), Arc::new(bv8)]);
    assert_eq!(mbp.eval_bv(&ashr_overflow, &model), Some((0xFF, 8)));

    // bvashr(0x40, 1) in 8-bit: positive (MSB=0) >> 1 = 0x20 (no sign extension)
    let bv_pos = ChcExpr::BitVec(0x40, 8);
    let bv1 = ChcExpr::BitVec(1, 8);
    let ashr_pos = ChcExpr::Op(ChcOp::BvAShr, vec![Arc::new(bv_pos), Arc::new(bv1)]);
    assert_eq!(mbp.eval_bv(&ashr_pos, &model), Some((0x20, 8)));
}

/// Packet 1 test: store(store(a, 0, v1), 0, v2) = b — aliased indices.
///
/// The inner store writes to index 0, then the outer store overwrites index 0.
/// With partial equality tracking, only the OUTER store's constraint should
/// be emitted: `select(b, 0) = v2`. The inner `select(b, 0) = v1` must be
/// collapsed because index 0 is already in the exception set.
///
/// Before this fix, both constraints were emitted, producing a contradiction
/// when v1 != v2.
#[test]
fn test_invert_store_equality_aliased_index_collapse() {
    let mbp = Mbp::new();

    let idx_sort = ChcSort::Int;
    let val_sort = ChcSort::Int;
    let arr_sort = ChcSort::Array(Box::new(idx_sort), Box::new(val_sort));

    let a = ChcVar::new("a", arr_sort);
    let b = ChcVar::new("b", a.sort.clone());

    // store(store(a, 0, 10), 0, 20) = b
    // Inner store: a[0] = 10, outer store overwrites: a[0] = 20
    let inner_store = ChcExpr::store(ChcExpr::var(a.clone()), ChcExpr::Int(0), ChcExpr::Int(10));
    let outer_store = ChcExpr::store(inner_store, ChcExpr::Int(0), ChcExpr::Int(20));
    let eq = ChcExpr::eq(outer_store, ChcExpr::var(b));

    // Model must have values for the indices so aliasing is detected.
    // Index 0 evaluates to 0 on both stores — they alias.
    let model = FxHashMap::default(); // Int(0) is a literal, eval_generic returns Some(Int(0))

    let result = mbp.project(&eq, std::slice::from_ref(&a), &model);
    let result_str = format!("{result:?}");

    // The result should contain a constraint with value 20 (the outer store's value).
    assert!(
        result_str.contains("20"),
        "Result must contain the outer store value 20. Got: {result_str}"
    );

    // Count how many `select` constraints mention the constant 0 as index.
    // With aliasing collapse, there should be only ONE select constraint for index 0,
    // not two (which would produce both select(b,0)=10 and select(b,0)=20).
    let select_count = result_str.matches("Select").count();
    assert!(
        select_count <= 1,
        "Aliased stores should produce at most 1 select constraint (collapsed). \
         Got {select_count} Select occurrences in: {result_str}"
    );
}

/// Packet 1 test: store(store(a, 0, v1), 1, v2) = b — distinct indices.
///
/// When indices are different (0 and 1), BOTH store constraints must be emitted:
/// `select(b, 1) = v2` and `select(..., 0) = v1`. No collapsing should occur.
#[test]
fn test_invert_store_equality_distinct_indices_no_collapse() {
    let mbp = Mbp::new();

    let idx_sort = ChcSort::Int;
    let val_sort = ChcSort::Int;
    let arr_sort = ChcSort::Array(Box::new(idx_sort), Box::new(val_sort));

    let a = ChcVar::new("a", arr_sort);
    let b = ChcVar::new("b", a.sort.clone());

    // store(store(a, 0, 10), 1, 20) = b
    let inner_store = ChcExpr::store(ChcExpr::var(a.clone()), ChcExpr::Int(0), ChcExpr::Int(10));
    let outer_store = ChcExpr::store(inner_store, ChcExpr::Int(1), ChcExpr::Int(20));
    let eq = ChcExpr::eq(outer_store, ChcExpr::var(b));

    let model = FxHashMap::default();

    let result = mbp.project(&eq, std::slice::from_ref(&a), &model);
    let result_str = format!("{result:?}");

    // Both values must appear in the result (both stores produce constraints).
    assert!(
        result_str.contains("10") && result_str.contains("20"),
        "Distinct indices should produce constraints for both values 10 and 20. Got: {result_str}"
    );
}

/// Packet 1 test: `store(a, i, 10) = store(b, j, 10)` with `M(i) = M(j)`.
///
/// This exercises the both-side store-chain case from the active #6047 design.
/// Projecting `a` should keep the shared-index fact `i = j` and should not
/// leave behind `a`, `b`, or fresh `__mbp_*` helper variables.
#[test]
fn test_invert_store_equality_both_side_shared_index_reduces_to_index_equality() {
    let mbp = Mbp::new();

    let arr_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let a = ChcVar::new("a", arr_sort.clone());
    let b = ChcVar::new("b", arr_sort);
    let i = ChcVar::new("i", ChcSort::Int);
    let j = ChcVar::new("j", ChcSort::Int);

    let lhs = ChcExpr::store(
        ChcExpr::var(a.clone()),
        ChcExpr::var(i.clone()),
        ChcExpr::Int(10),
    );
    let rhs = ChcExpr::store(ChcExpr::var(b), ChcExpr::var(j.clone()), ChcExpr::Int(10));
    let formula = ChcExpr::eq(lhs, rhs);

    let mut model = FxHashMap::default();
    model.insert(
        "a".to_string(),
        SmtValue::ConstArray(Box::new(SmtValue::Int(0))),
    );
    model.insert(
        "b".to_string(),
        SmtValue::ConstArray(Box::new(SmtValue::Int(0))),
    );
    model.insert("i".to_string(), SmtValue::Int(5));
    model.insert("j".to_string(), SmtValue::Int(5));

    let result = mbp.project(&formula, std::slice::from_ref(&a), &model);
    let result_vars = result.vars();
    let i_expr = ChcExpr::var(i);
    let j_expr = ChcExpr::var(j);

    assert!(
        matches!(
            &result,
            ChcExpr::Op(ChcOp::Eq, args)
                if args.len() == 2
                    && ((args[0].as_ref() == &i_expr && args[1].as_ref() == &j_expr)
                        || (args[0].as_ref() == &j_expr && args[1].as_ref() == &i_expr))
        ),
        "Both-side store-chain projection should keep only the shared-index equality. Got: {result:?}"
    );
    assert!(
        !result_vars
            .iter()
            .any(|v| v.name == "a" || v.name == "b" || v.name.starts_with("__mbp_")),
        "Projection should eliminate array/fresh helper variables. Got: {result_vars:?}"
    );
}

/// Packet 1 regression: both-side store chains with distinct model indices
/// must normalize the generated `select(store(...), i) = v` side literal into
/// a base-array read plus the miss guard `i != j`.
///
/// This is the combined path used by consumer-style heap updates:
/// equality inversion emits a store-side literal, then `push_normalized_*`
/// must run the select-store reducer and keep the resulting guard.
#[test]
fn test_invert_store_equality_both_side_distinct_indices_normalizes_side_literal() {
    let mbp = Mbp::new();

    let arr_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let a = ChcVar::new("a", arr_sort.clone());
    let b = ChcVar::new("b", arr_sort);
    let i = ChcVar::new("i", ChcSort::Int);
    let j = ChcVar::new("j", ChcSort::Int);

    let lhs = ChcExpr::store(
        ChcExpr::var(a.clone()),
        ChcExpr::var(i.clone()),
        ChcExpr::Int(10),
    );
    let rhs = ChcExpr::store(
        ChcExpr::var(b.clone()),
        ChcExpr::var(j.clone()),
        ChcExpr::Int(20),
    );
    let formula = ChcExpr::eq(lhs, rhs);

    // Model:
    //   a = store(const(0), 7, 20)
    //   b = store(const(0), 5, 10)
    // so store(a, 5, 10) = store(b, 7, 20) = {5 -> 10, 7 -> 20}.
    let mut model = FxHashMap::default();
    model.insert(
        "a".to_string(),
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(0)),
            entries: vec![(SmtValue::Int(7), SmtValue::Int(20))],
        },
    );
    model.insert(
        "b".to_string(),
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(0)),
            entries: vec![(SmtValue::Int(5), SmtValue::Int(10))],
        },
    );
    model.insert("i".to_string(), SmtValue::Int(5));
    model.insert("j".to_string(), SmtValue::Int(7));

    let result = mbp.project(&formula, std::slice::from_ref(&a), &model);
    let conjuncts = result.collect_conjuncts();
    let result_vars = result.vars();
    let expected_guard = ChcExpr::ne(ChcExpr::var(i.clone()), ChcExpr::var(j));
    let expected_read = ChcExpr::eq(
        ChcExpr::select(ChcExpr::var(b), ChcExpr::var(i)),
        ChcExpr::Int(10),
    );

    assert!(
        conjuncts.contains(&expected_guard),
        "Projection must keep the distinct-index guard i != j. Got: {result:?}"
    );
    assert!(
        conjuncts.contains(&expected_read),
        "Projection must normalize the side literal to select(b, i) = 10. Got: {result:?}"
    );
    assert_eq!(
        conjuncts.len(),
        2,
        "Projection should reduce to exactly the guard plus base-array read. Got: {result:?}"
    );
    assert!(
        !result_vars
            .iter()
            .any(|v| v.name == "a" || v.name.starts_with("__mbp_")),
        "Projection should eliminate array/fresh helper variables. Got: {result_vars:?}"
    );
}

/// Regression: two-layer store chains on both sides must preserve the
/// shared-index equalities and at least one cross-layer miss guard after
/// normalization. This is the nested heap-update shape behind several
/// remaining #6047 mem-track residuals.
#[test]
fn test_invert_store_equality_both_side_two_layer_chain_keeps_index_relations() {
    let mbp = Mbp::new();

    let arr_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let a = ChcVar::new("a", arr_sort.clone());
    let b = ChcVar::new("b", arr_sort);
    let i = ChcVar::new("i", ChcSort::Int);
    let j = ChcVar::new("j", ChcSort::Int);
    let k = ChcVar::new("k", ChcSort::Int);
    let l = ChcVar::new("l", ChcSort::Int);

    let lhs = ChcExpr::store(
        ChcExpr::store(
            ChcExpr::var(a.clone()),
            ChcExpr::var(i.clone()),
            ChcExpr::Int(10),
        ),
        ChcExpr::var(j.clone()),
        ChcExpr::Int(20),
    );
    let rhs = ChcExpr::store(
        ChcExpr::store(ChcExpr::var(b), ChcExpr::var(k.clone()), ChcExpr::Int(10)),
        ChcExpr::var(l.clone()),
        ChcExpr::Int(20),
    );
    let formula = ChcExpr::eq(lhs, rhs);

    let mut model = FxHashMap::default();
    model.insert(
        "a".to_string(),
        SmtValue::ConstArray(Box::new(SmtValue::Int(0))),
    );
    model.insert(
        "b".to_string(),
        SmtValue::ConstArray(Box::new(SmtValue::Int(0))),
    );
    model.insert("i".to_string(), SmtValue::Int(5));
    model.insert("j".to_string(), SmtValue::Int(7));
    model.insert("k".to_string(), SmtValue::Int(5));
    model.insert("l".to_string(), SmtValue::Int(7));

    let result = mbp.project(&formula, std::slice::from_ref(&a), &model);
    let conjuncts = result.collect_conjuncts();
    let result_vars = result.vars();
    let outer_eq = ChcExpr::eq(ChcExpr::var(j.clone()), ChcExpr::var(l.clone()));
    let inner_eq = ChcExpr::eq(ChcExpr::var(i.clone()), ChcExpr::var(k));
    let miss_guard_j = ChcExpr::ne(ChcExpr::var(i.clone()), ChcExpr::var(j));
    let miss_guard_l = ChcExpr::ne(ChcExpr::var(i), ChcExpr::var(l));

    assert!(
        conjuncts.contains(&outer_eq),
        "Projection must preserve the outer shared-index equality j = l. Got: {result:?}"
    );
    assert!(
        conjuncts.contains(&inner_eq),
        "Projection must preserve the inner shared-index equality i = k. Got: {result:?}"
    );
    assert!(
        conjuncts.contains(&miss_guard_j) || conjuncts.contains(&miss_guard_l),
        "Projection must keep a cross-layer miss guard from the nested store normalization. Got: {result:?}"
    );
    assert!(
        !result_vars
            .iter()
            .any(|v| v.name == "a" || v.name.starts_with("__mbp_")),
        "Projection should eliminate array/fresh helper variables. Got: {result_vars:?}"
    );
}

/// Packet 0 test: select(store(a, i, v), j) with M(i)=M(j) should produce
/// an index equality condition `i = j` (the value 42 is consumed by tautology
/// elimination since `42 > 0` folds to `true`).
///
/// Without this fix, the reduction `select(store(a, i, v), j) → v` was
/// applied without emitting `i = j`, making the MBP unsound (the reduction
/// is only valid when the indices are equal).
#[test]
fn test_reduce_select_store_emits_index_equality_condition() {
    let mbp = Mbp::new();

    let idx_sort = ChcSort::Int;
    let val_sort = ChcSort::Int;
    let arr_sort = ChcSort::Array(Box::new(idx_sort), Box::new(val_sort));

    let a = ChcVar::new("a", arr_sort);
    let i = ChcVar::new("i", ChcSort::Int);
    let j = ChcVar::new("j", ChcSort::Int);

    // select(store(a, i, 42), j) > 0  AND  a = a (dummy to force array projection)
    let stored = ChcExpr::store(ChcExpr::var(a.clone()), ChcExpr::var(i), ChcExpr::Int(42));
    let sel = ChcExpr::select(stored, ChcExpr::var(j));
    let formula = ChcExpr::gt(sel, ChcExpr::Int(0));

    // Model: i=5, j=5 (equal indices → select hits the store)
    let mut model = FxHashMap::default();
    model.insert("i".to_string(), SmtValue::Int(5));
    model.insert("j".to_string(), SmtValue::Int(5));

    let result = mbp.project(&formula, std::slice::from_ref(&a), &model);
    let result_str = format!("{result:?}");

    // After reduction: select(store(a, i, 42), j) → 42 with side condition i=j.
    // Then gt(42, 0) simplifies to true (tautology, dropped).
    // The final result should contain the index equality condition i=j.
    assert!(
        result_str.contains("Eq"),
        "MBP must emit index equality condition (i = j) for the select-store hit. Got: {result_str}"
    );

    // The value 42 is consumed during constant folding of gt(42, 0) → true,
    // so it does not appear in the final projected result.
    assert!(
        !result_str.contains("42"),
        "Value 42 should be consumed by tautology elimination (42 > 0 → true). Got: {result_str}"
    );
}

/// Packet 0 test: select(store(a, i, v), j) with M(i)!=M(j) should produce
/// the pass-through `select(a, j)` AND an index disequality condition `i != j`.
#[test]
fn test_reduce_select_store_emits_index_disequality_condition() {
    let mbp = Mbp::new();

    let idx_sort = ChcSort::Int;
    let val_sort = ChcSort::Int;
    let arr_sort = ChcSort::Array(Box::new(idx_sort), Box::new(val_sort));

    let a = ChcVar::new("a", arr_sort);
    let i = ChcVar::new("i", ChcSort::Int);
    let j = ChcVar::new("j", ChcSort::Int);

    // select(store(a, i, 42), j) > 0
    let stored = ChcExpr::store(ChcExpr::var(a.clone()), ChcExpr::var(i), ChcExpr::Int(42));
    let sel = ChcExpr::select(stored, ChcExpr::var(j));
    let formula = ChcExpr::gt(sel, ChcExpr::Int(0));

    // Model: i=5, j=7 (different indices → select misses the store)
    let mut model = FxHashMap::default();
    model.insert("i".to_string(), SmtValue::Int(5));
    model.insert("j".to_string(), SmtValue::Int(7));

    let result = mbp.project(&formula, std::slice::from_ref(&a), &model);
    let result_str = format!("{result:?}");

    // The result should contain a disequality condition between i and j.
    assert!(
        result_str.contains("Ne"),
        "MBP must emit index disequality condition (i != j) for the select-store miss. Got: {result_str}"
    );
}
