// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fold infrastructure consistency tests.
//!
//! Verifies that `ExprValue::children()` and `rebuild_with_children()` agree
//! on the number of children for every constructible compound variant.
//! A mismatch causes a runtime panic in the fold infrastructure
//! (`rebuild_with_children` calls `unwrap()` on the child iterator).
//!
//! These two functions are defined in separate locations (`children()` in
//! `expr/mod.rs`, `rebuild_with_children` in `expr/fold.rs`) and maintained
//! independently. This test is the only guard against count divergence.
//!
//! Part of #3150.

#![allow(clippy::unwrap_used)]

use ay_bindings::expr::fold::{fold_expr, rebuild_with_children, ExprFold};
use ay_bindings::expr::{Expr, RoundingMode};
use ay_bindings::sort::Sort;

/// Substitution fold: replaces variable "x" with constant 42.
struct SubstFold;
impl ExprFold for SubstFold {
    fn fold_var(&mut self, name: &str, sort: &Sort) -> Expr {
        if name == "x" && sort.is_int() {
            Expr::int_const(42)
        } else {
            Expr::var(name.to_string(), sort.clone())
        }
    }
}

/// Critical consistency test: for every constructible compound variant,
/// `children().count()` matches what `rebuild_with_children` consumes.
/// The roundtrip (collect children, rebuild) must produce an equal expression.
#[test]
fn test_children_rebuild_consistency_all_categories() {
    fn assert_roundtrip(label: &str, expr: &Expr) {
        let children: Vec<Expr> = expr.value().children().cloned().collect();
        let rebuilt = rebuild_with_children(expr, children);
        assert_eq!(
            &rebuilt, expr,
            "rebuild_with_children roundtrip failed for {label}"
        );
    }

    let x_bool = Expr::var("x", Sort::bool());
    let y_bool = Expr::var("y", Sort::bool());
    let z_bool = Expr::var("z", Sort::bool());
    let x_int = Expr::var("x", Sort::int());
    let y_int = Expr::var("y", Sort::int());
    let x_real = Expr::var("x", Sort::real());
    let y_real = Expr::var("y", Sort::real());
    let x_bv = Expr::var("x", Sort::bv32());
    let y_bv = Expr::var("y", Sort::bv32());
    let arr = Expr::var("arr", Sort::array(Sort::int(), Sort::int()));
    let idx = Expr::var("idx", Sort::int());
    let val = Expr::var("val", Sort::int());

    // --- Unary Bool ---
    assert_roundtrip("Not", &x_bool.clone().not());

    // --- Binary Bool ---
    assert_roundtrip("Xor", &x_bool.clone().xor(y_bool.clone()));
    assert_roundtrip("Implies", &x_bool.clone().implies(y_bool.clone()));
    assert_roundtrip("Eq(bool)", &x_bool.clone().eq(y_bool.clone()));

    // --- N-ary Bool ---
    assert_roundtrip(
        "And",
        &Expr::and_many(vec![x_bool.clone(), y_bool.clone(), z_bool]),
    );
    assert_roundtrip("Or", &Expr::or_many(vec![x_bool.clone(), y_bool]));
    assert_roundtrip(
        "Distinct",
        &Expr::distinct(vec![x_int.clone(), y_int.clone()]),
    );

    // --- Ternary ---
    assert_roundtrip(
        "Ite",
        &Expr::ite(x_bool, Expr::int_const(1), Expr::int_const(0)),
    );

    // --- Int operations ---
    assert_roundtrip("IntAdd", &x_int.clone().int_add(y_int.clone()));
    assert_roundtrip("IntSub", &x_int.clone().int_sub(y_int.clone()));
    assert_roundtrip("IntMul", &x_int.clone().int_mul(y_int.clone()));
    assert_roundtrip("IntDiv", &x_int.clone().int_div(y_int.clone()));
    assert_roundtrip("IntMod", &x_int.clone().int_mod(y_int.clone()));
    assert_roundtrip("IntLt", &x_int.clone().int_lt(y_int.clone()));
    assert_roundtrip("IntLe", &x_int.clone().int_le(y_int.clone()));
    assert_roundtrip("IntGt", &x_int.clone().int_gt(y_int.clone()));
    assert_roundtrip("IntGe", &x_int.clone().int_ge(y_int.clone()));
    assert_roundtrip("IntNeg", &x_int.clone().int_neg());
    assert_roundtrip("IntToReal", &x_int.clone().int_to_real());
    assert_roundtrip("IsInt", &x_real.clone().is_int());

    // --- Real operations ---
    assert_roundtrip("RealAdd", &x_real.clone().real_add(y_real.clone()));
    assert_roundtrip("RealSub", &x_real.clone().real_sub(y_real.clone()));
    assert_roundtrip("RealMul", &x_real.clone().real_mul(y_real.clone()));
    assert_roundtrip("RealDiv", &x_real.clone().real_div(y_real.clone()));
    assert_roundtrip("RealLt", &x_real.clone().real_lt(y_real.clone()));
    assert_roundtrip("RealLe", &x_real.clone().real_le(y_real.clone()));
    assert_roundtrip("RealGt", &x_real.clone().real_gt(y_real.clone()));
    assert_roundtrip("RealGe", &x_real.clone().real_ge(y_real));
    assert_roundtrip("RealNeg", &x_real.clone().real_neg());
    assert_roundtrip("RealToInt", &x_real.real_to_int());

    // --- BV operations ---
    assert_roundtrip("BvAdd", &x_bv.clone().bvadd(y_bv.clone()));
    assert_roundtrip("BvSub", &x_bv.clone().bvsub(y_bv.clone()));
    assert_roundtrip("BvMul", &x_bv.clone().bvmul(y_bv.clone()));
    assert_roundtrip("BvUDiv", &x_bv.clone().bvudiv(y_bv.clone()));
    assert_roundtrip("BvSDiv", &x_bv.clone().bvsdiv(y_bv.clone()));
    assert_roundtrip("BvURem", &x_bv.clone().bvurem(y_bv.clone()));
    assert_roundtrip("BvSRem", &x_bv.clone().bvsrem(y_bv.clone()));
    assert_roundtrip("BvAnd", &x_bv.clone().bvand(y_bv.clone()));
    assert_roundtrip("BvOr", &x_bv.clone().bvor(y_bv.clone()));
    assert_roundtrip("BvXor", &x_bv.clone().bvxor(y_bv.clone()));
    assert_roundtrip("BvShl", &x_bv.clone().bvshl(y_bv.clone()));
    assert_roundtrip("BvLShr", &x_bv.clone().bvlshr(y_bv.clone()));
    assert_roundtrip("BvAShr", &x_bv.clone().bvashr(y_bv.clone()));
    assert_roundtrip("BvULt", &x_bv.clone().bvult(y_bv.clone()));
    assert_roundtrip("BvULe", &x_bv.clone().bvule(y_bv.clone()));
    assert_roundtrip("BvUGt", &x_bv.clone().bvugt(y_bv.clone()));
    assert_roundtrip("BvUGe", &x_bv.clone().bvuge(y_bv.clone()));
    assert_roundtrip("BvSLt", &x_bv.clone().bvslt(y_bv.clone()));
    assert_roundtrip("BvSLe", &x_bv.clone().bvsle(y_bv.clone()));
    assert_roundtrip("BvSGt", &x_bv.clone().bvsgt(y_bv.clone()));
    assert_roundtrip("BvSGe", &x_bv.clone().bvsge(y_bv.clone()));
    assert_roundtrip("BvConcat", &x_bv.clone().concat(y_bv.clone()));
    assert_roundtrip("BvNeg", &x_bv.clone().bvneg());
    assert_roundtrip("BvNot", &x_bv.clone().bvnot());
    assert_roundtrip("BvExtract", &x_bv.clone().extract(15, 0));
    assert_roundtrip("BvZeroExtend", &x_bv.clone().zero_extend(32));
    assert_roundtrip("BvSignExtend", &x_bv.clone().sign_extend(32));
    assert_roundtrip("Bv2Int", &x_bv.clone().bv2int());

    // --- Array operations ---
    assert_roundtrip("Select", &arr.clone().select(idx.clone()));
    assert_roundtrip("Store", &arr.store(idx, val));
    assert_roundtrip(
        "ConstArray",
        &Expr::const_array(Sort::int(), Expr::int_const(0)),
    );

    // --- FuncApp ---
    assert_roundtrip("FuncApp(0)", &Expr::func_app("f", vec![]));
    assert_roundtrip("FuncApp(1)", &Expr::func_app("f", vec![x_int.clone()]));
    assert_roundtrip(
        "FuncApp(3)",
        &Expr::func_app("f", vec![x_int.clone(), y_int, Expr::int_const(1)]),
    );

    // --- Quantifiers ---
    let body = x_int.clone().int_ge(Expr::int_const(0));
    assert_roundtrip(
        "Forall(no triggers)",
        &Expr::forall(vec![("x".into(), Sort::int())], body.clone()),
    );
    assert_roundtrip(
        "Exists(no triggers)",
        &Expr::exists(vec![("x".into(), Sort::int())], body.clone()),
    );

    // Forall with single trigger group
    let trigger = x_int.clone().int_add(Expr::int_const(1));
    let with_triggers = Expr::forall_with_triggers(
        vec![("x".into(), Sort::int())],
        body.clone(),
        vec![vec![trigger.clone()]],
    );
    assert_roundtrip("Forall(1 trigger group, 1 term)", &with_triggers);

    // Forall with multi-term trigger
    let trigger2 = x_int.clone().int_mul(Expr::int_const(2));
    let multi_trigger = Expr::forall_with_triggers(
        vec![("x".into(), Sort::int())],
        body.clone(),
        vec![vec![trigger.clone(), trigger2]],
    );
    assert_roundtrip("Forall(1 trigger group, 2 terms)", &multi_trigger);

    // Forall with multiple trigger groups
    let multi_groups = Expr::forall_with_triggers(
        vec![("x".into(), Sort::int())],
        body,
        vec![vec![trigger], vec![x_int]],
    );
    assert_roundtrip("Forall(2 trigger groups)", &multi_groups);

    // --- FP operations (rounding mode variants) ---
    let fp_sort = Sort::fp32();
    let x_fp = Expr::var("xf", fp_sort.clone());
    let y_fp = Expr::var("yf", fp_sort.clone());
    let rm = RoundingMode::RNE;
    assert_roundtrip("FpAdd", &x_fp.clone().fp_add(rm, y_fp.clone()));
    assert_roundtrip("FpSub", &x_fp.clone().fp_sub(rm, y_fp.clone()));
    assert_roundtrip("FpMul", &x_fp.clone().fp_mul(rm, y_fp.clone()));
    assert_roundtrip("FpDiv", &x_fp.clone().fp_div(rm, y_fp.clone()));
    assert_roundtrip("FpAbs", &x_fp.clone().fp_abs());
    assert_roundtrip("FpNeg", &x_fp.clone().fp_neg());
    assert_roundtrip("FpEq", &x_fp.clone().fp_eq(y_fp.clone()));
    assert_roundtrip("FpLt", &x_fp.clone().fp_lt(y_fp.clone()));
    assert_roundtrip("FpLe", &x_fp.clone().fp_le(y_fp.clone()));
    assert_roundtrip("FpGt", &x_fp.clone().fp_gt(y_fp.clone()));
    assert_roundtrip("FpGe", &x_fp.clone().fp_ge(y_fp.clone()));
    assert_roundtrip("FpRem", &x_fp.clone().fp_rem(y_fp.clone()));
    assert_roundtrip("FpMin", &x_fp.clone().fp_min(y_fp.clone()));
    assert_roundtrip("FpMax", &x_fp.clone().fp_max(y_fp));
    assert_roundtrip("FpSqrt", &x_fp.clone().fp_sqrt(rm));
    assert_roundtrip("FpRoundToIntegral", &x_fp.clone().fp_round_to_integral(rm));
    assert_roundtrip("FpIsNaN", &x_fp.clone().fp_is_nan());
    assert_roundtrip("FpIsInfinite", &x_fp.clone().fp_is_infinite());
    assert_roundtrip("FpIsZero", &x_fp.clone().fp_is_zero());
    assert_roundtrip("FpIsNormal", &x_fp.clone().fp_is_normal());
    assert_roundtrip("FpIsSubnormal", &x_fp.clone().fp_is_subnormal());
    assert_roundtrip("FpIsPositive", &x_fp.clone().fp_is_positive());
    assert_roundtrip("FpIsNegative", &x_fp.clone().fp_is_negative());
    assert_roundtrip("FpToReal", &x_fp.fp_to_real());

    // --- FP leaf constants ---
    assert_roundtrip("FpPlusInfinity", &Expr::fp_plus_infinity(&fp_sort));
    assert_roundtrip("FpMinusInfinity", &Expr::fp_minus_infinity(&fp_sort));
    assert_roundtrip("FpNaN", &Expr::fp_nan(&fp_sort));
    assert_roundtrip("FpPlusZero", &Expr::fp_plus_zero(&fp_sort));
    assert_roundtrip("FpMinusZero", &Expr::fp_minus_zero(&fp_sort));

    // --- BV overflow checks ---
    assert_roundtrip(
        "BvAddNoOverflowUnsigned",
        &x_bv.clone().bvadd_no_overflow_unsigned(y_bv.clone()),
    );
    assert_roundtrip(
        "BvAddNoOverflowSigned",
        &x_bv.clone().bvadd_no_overflow_signed(y_bv.clone()),
    );
    assert_roundtrip(
        "BvSubNoUnderflowUnsigned",
        &x_bv.clone().bvsub_no_underflow_unsigned(y_bv.clone()),
    );
    assert_roundtrip(
        "BvSubNoOverflowSigned",
        &x_bv.clone().bvsub_no_overflow_signed(y_bv.clone()),
    );
    assert_roundtrip(
        "BvMulNoOverflowUnsigned",
        &x_bv.clone().bvmul_no_overflow_unsigned(y_bv.clone()),
    );
    assert_roundtrip(
        "BvMulNoOverflowSigned",
        &x_bv.clone().bvmul_no_overflow_signed(y_bv.clone()),
    );
    assert_roundtrip("BvSdivNoOverflow", &x_bv.clone().bvsdiv_no_overflow(y_bv));
    assert_roundtrip("BvNegNoOverflow", &x_bv.bvneg_no_overflow());
}

/// Test that a non-identity fold correctly propagates through 3 levels of
/// compound nodes (not just 2-level operator+leaf).
#[test]
fn test_fold_substitute_deep_tree() {
    // (+ (+ x y) 1) — 3 levels: outer IntAdd -> inner IntAdd -> Var("x")
    let x = Expr::var("x", Sort::int());
    let y = Expr::var("y", Sort::int());
    let one = Expr::int_const(1);
    let inner = x.int_add(y.clone());
    let outer = inner.int_add(one.clone());

    let mut f = SubstFold; // replaces "x" with 42
    let result = fold_expr(&mut f, &outer);

    // Expected: (+ (+ 42 y) 1)
    let expected = Expr::int_const(42).int_add(y).int_add(one);
    assert_eq!(
        result, expected,
        "3-level deep substitution should propagate"
    );
}
