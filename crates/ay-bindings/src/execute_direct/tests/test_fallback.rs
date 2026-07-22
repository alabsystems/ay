// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Fallback behavior tests — unsupported expressions trigger NeedsFallback (#876).

use super::*;

#[test]
fn test_fallback_for_chc() {
    let mut program = AYProgram::horn();
    program.declare_rel("Inv", vec![Sort::int()]);

    let result = execute(&program).unwrap();
    assert!(matches!(result, ExecuteResult::NeedsFallback(_)));
}

#[test]
fn test_fallback_for_bv2int() {
    let mut program = AYProgram::new();
    // Z3 requires a logic including both BV and Int for bv2int.
    program.set_logic("ALL");
    let bv = program.declare_const("bv", Sort::bitvec(8));
    program.assert(bv.clone().eq(Expr::bitvec_const(255u64, 8)));

    let as_int = bv.bv2int();
    program.assert(as_int.eq(Expr::int(1)));
    program.check_sat();

    // #5406: bv2int now wired to direct execution — should not fall back.
    let result = execute(&program).unwrap();
    assert!(
        !matches!(result, ExecuteResult::NeedsFallback(_)),
        "bv2int should not trigger fallback after #5406, got: {:?}",
        result
    );
}

#[test]
fn test_fallback_for_int_to_real() {
    let mut program = AYProgram::new();
    // QF_LIRA supports linear integer and real arithmetic
    program.set_logic("QF_LIRA");
    let x = program.declare_const("x", Sort::int());
    let y = program.declare_const("y", Sort::real());
    let as_real = x.int_to_real();
    program.assert(as_real.real_ge(y));
    program.check_sat();

    // #5406: IntToReal now wired to direct execution — should not fall back.
    let result = execute(&program).unwrap();
    assert!(
        !matches!(result, ExecuteResult::NeedsFallback(_)),
        "IntToReal should not trigger fallback after #5406, got: {:?}",
        result
    );
}

#[test]
fn test_fallback_for_real_to_int() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LIRA");

    // floor(3/2) = 1, so (to_int (/ 3 2)) = 2 is UNSAT.
    let r = Expr::real(3).real_div(Expr::real(2));
    let i = r.real_to_int();
    program.assert(i.eq(Expr::int(2)));
    program.check_sat();

    // #5406: RealToInt now wired to direct execution — should not fall back.
    let result = execute(&program).unwrap();
    assert!(
        !matches!(result, ExecuteResult::NeedsFallback(_)),
        "RealToInt should not trigger fallback after #5406, got: {:?}",
        result
    );
}

#[test]
fn test_fallback_for_is_int() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LIRA");

    // (is_int (/ 3 2)) is false, so asserting it is UNSAT.
    let r = Expr::real(3).real_div(Expr::real(2));
    program.assert(r.is_int());
    program.check_sat();

    // #5406: IsInt now wired to direct execution — should not fall back.
    let result = execute(&program).unwrap();
    assert!(
        !matches!(result, ExecuteResult::NeedsFallback(_)),
        "IsInt should not trigger fallback after #5406, got: {:?}",
        result
    );
}

#[test]
fn test_fallback_for_func_app() {
    let mut program = AYProgram::new();
    // QF_UFLIA supports uninterpreted functions + linear integer arithmetic
    program.set_logic("QF_UFLIA");
    let x = program.declare_const("x", Sort::int());
    // #5406: Declare f before using it so the direct path can look it up.
    program.declare_fun("f", vec![Sort::int()], Sort::int());
    let f_x = Expr::func_app_with_sort("f", vec![x.clone()], Sort::int());
    program.assert(f_x.eq(x));
    program.check_sat();

    // #5406: FuncApp now wired to direct execution — should not fall back.
    let result = execute(&program).unwrap();
    assert!(
        !matches!(result, ExecuteResult::NeedsFallback(_)),
        "FuncApp should not trigger fallback after #5406, got: {:?}",
        result
    );
}

#[test]
fn test_fallback_for_forall() {
    let mut program = AYProgram::new();
    program.set_logic("LIA");
    // forall x. x >= 0 is NOT valid (x can be negative)
    let x = Expr::var("x", Sort::int());
    let zero = Expr::int(0);
    let body = x.clone().int_ge(zero);
    let forall_expr = Expr::forall(vec![("x".to_string(), Sort::int())], body);
    program.assert(forall_expr);
    program.check_sat();

    // #5406: Quantifiers now wired to direct execution — should not fall back.
    let result = execute(&program).unwrap();
    assert!(
        !matches!(result, ExecuteResult::NeedsFallback(_)),
        "Forall should not trigger fallback after #5406, got: {:?}",
        result
    );
}

#[test]
fn test_fallback_for_exists() {
    let mut program = AYProgram::new();
    program.set_logic("LIA");
    // exists x. x > x (false — no integer is greater than itself)
    let x = Expr::var("x", Sort::int());
    let body = x.clone().int_gt(x.clone());
    let exists_expr = Expr::exists(vec![("x".to_string(), Sort::int())], body);
    program.assert(exists_expr);
    program.check_sat();

    // #5406: Quantifiers now wired to direct execution — should not fall back.
    let result = execute(&program).unwrap();
    assert!(
        !matches!(result, ExecuteResult::NeedsFallback(_)),
        "Exists should not trigger fallback after #5406, got: {:?}",
        result
    );
}

#[test]
fn test_str_regex_no_fallback() {
    let mut program = AYProgram::new();
    program.set_logic("QF_SLIA");
    let s = program.declare_const("s", Sort::string());
    let suffix = Expr::string_const("b");
    let regex = Expr::string_const("a")
        .str_to_re()
        .re_star()
        .re_concat(suffix.clone().str_to_re());
    program.assert(s.str_concat(suffix).str_in_re(regex));
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(
        !matches!(result, ExecuteResult::NeedsFallback(_)),
        "string/regex bridge should not trigger fallback after #5168, got: {:?}",
        result
    );
}

#[test]
fn test_seq_contains_no_fallback() {
    let mut program = AYProgram::new();
    program.set_logic("QF_SEQLIA");
    let seq = program.declare_const("seq", Sort::seq(Sort::int()));
    let needle = Expr::int(5).seq_unit();
    program.assert(seq.seq_concat(needle.clone()).seq_contains(needle));
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(
        !matches!(result, ExecuteResult::NeedsFallback(_)),
        "sequence bridge should not trigger fallback after #5168, got: {:?}",
        result
    );
}

// --- FP fallback tests (#5774) ---

use crate::expr::RoundingMode;

#[test]
fn test_fp_comparison_no_fallback() {
    // FP comparisons are fully bit-blasted and should execute directly (#5774).
    let mut program = AYProgram::new();
    program.set_logic("QF_FP");
    let fp_sort = Sort::fp(8, 24); // Float32
    let x = program.declare_const("x", fp_sort.clone());
    let y = program.declare_const("y", fp_sort);
    program.assert(x.fp_lt(y));
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(
        !matches!(result, ExecuteResult::NeedsFallback(_)),
        "FP comparison (fp.lt) should not trigger fallback (#5774), got: {:?}",
        result
    );
}

#[test]
fn test_fp_classification_no_fallback() {
    // FP classification predicates are fully bit-blasted (#5774).
    let mut program = AYProgram::new();
    program.set_logic("QF_FP");
    let x = program.declare_const("x", Sort::fp(8, 24));
    program.assert(x.fp_is_nan());
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(
        !matches!(result, ExecuteResult::NeedsFallback(_)),
        "FP classification (fp.isNaN) should not trigger fallback (#5774), got: {:?}",
        result
    );
}

#[test]
fn test_fp_constant_no_fallback() {
    // FP constants (infinity, NaN, zero) are leaf nodes, no fallback needed (#5774).
    let mut program = AYProgram::new();
    program.set_logic("QF_FP");
    let fp_sort = Sort::fp(8, 24);
    let x = program.declare_const("x", fp_sort.clone());
    let inf = Expr::fp_plus_infinity(&fp_sort);
    program.assert(x.fp_eq(inf));
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(
        !matches!(result, ExecuteResult::NeedsFallback(_)),
        "FP constant (fp.plusInfinity) should not trigger fallback (#5774), got: {:?}",
        result
    );
}

#[test]
fn test_fp_neg_abs_no_fallback() {
    // FP negation and abs are sign-bit operations, fully implemented (#5774).
    let mut program = AYProgram::new();
    program.set_logic("QF_FP");
    let fp_sort = Sort::fp(8, 24);
    let x = program.declare_const("x", fp_sort.clone());
    let y = program.declare_const("y", fp_sort);
    program.assert(x.clone().fp_neg().fp_abs().fp_eq(y));
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(
        !matches!(result, ExecuteResult::NeedsFallback(_)),
        "FP neg/abs should not trigger fallback (#5774), got: {:?}",
        result
    );
}

#[test]
fn test_fp_arithmetic_no_fallback() {
    // FP arithmetic is fully bit-blasted (#6128) — no fallback needed.
    let mut program = AYProgram::new();
    program.set_logic("QF_FP");
    let fp_sort = Sort::fp(8, 24);
    let x = program.declare_const("x", fp_sort.clone());
    let y = program.declare_const("y", fp_sort);
    program.assert(x.fp_add(RoundingMode::RNE, y).fp_is_nan());
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(
        !matches!(result, ExecuteResult::NeedsFallback(_)),
        "FP arithmetic (fp.add) should not trigger fallback (#6128), got: {:?}",
        result
    );
}

#[test]
fn test_fp_comparison_with_arithmetic_subexpr_no_fallback() {
    // FP comparison on arithmetic subexpressions should execute directly (#6128).
    let mut program = AYProgram::new();
    program.set_logic("QF_FP");
    let fp_sort = Sort::fp(8, 24);
    let x = program.declare_const("x", fp_sort.clone());
    let y = program.declare_const("y", fp_sort.clone());
    let z = program.declare_const("z", fp_sort);
    // fp.lt(fp.add(x, y), z) — both comparison and arithmetic execute directly.
    program.assert(x.fp_add(RoundingMode::RNE, y).fp_lt(z));
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(
        !matches!(result, ExecuteResult::NeedsFallback(_)),
        "FP comparison with arithmetic subexpr should not trigger fallback (#6128), got: {:?}",
        result
    );
}

/// Helper: build a QF_FP program with FP16 variables and assert an FP expression.
fn fp16_program(build: impl FnOnce(&mut AYProgram, Sort, RoundingMode)) -> AYProgram {
    let mut p = AYProgram::new();
    p.set_logic("QF_FP");
    let fp_sort = Sort::fp(5, 11); // Float16 — small for fast bit-blasting
    build(&mut p, fp_sort, RoundingMode::RNE);
    p.check_sat();
    p
}

fn assert_no_fallback(program: &AYProgram, op: &str) {
    let result = execute(program).unwrap();
    assert!(
        !matches!(result, ExecuteResult::NeedsFallback(_)),
        "FP op {} should execute directly (#6128), got: {:?}",
        op,
        result
    );
}

#[test]
fn test_fp_add_sub_no_fallback() {
    let p = fp16_program(|p, s, rm| {
        let x = p.declare_const("x", s.clone());
        let y = p.declare_const("y", s);
        p.assert(x.fp_add(rm, y).fp_is_nan());
    });
    assert_no_fallback(&p, "fp.add");

    let p = fp16_program(|p, s, rm| {
        let x = p.declare_const("x", s.clone());
        let y = p.declare_const("y", s);
        p.assert(x.fp_sub(rm, y).fp_is_nan());
    });
    assert_no_fallback(&p, "fp.sub");
}

#[test]
fn test_fp_mul_div_no_fallback() {
    let p = fp16_program(|p, s, rm| {
        let x = p.declare_const("x", s.clone());
        let y = p.declare_const("y", s);
        p.assert(x.fp_mul(rm, y).fp_is_nan());
    });
    assert_no_fallback(&p, "fp.mul");

    let p = fp16_program(|p, s, rm| {
        let x = p.declare_const("x", s.clone());
        let y = p.declare_const("y", s);
        p.assert(x.fp_div(rm, y).fp_is_nan());
    });
    assert_no_fallback(&p, "fp.div");
}

#[test]
fn test_fp_fma_sqrt_no_fallback() {
    let p = fp16_program(|p, s, rm| {
        let x = p.declare_const("x", s.clone());
        let y = p.declare_const("y", s.clone());
        let z = p.declare_const("z", s);
        p.assert(x.fp_fma(rm, y, z).fp_is_nan());
    });
    assert_no_fallback(&p, "fp.fma");

    let p = fp16_program(|p, s, rm| {
        let x = p.declare_const("x", s);
        p.assert(x.fp_sqrt(rm).fp_is_nan());
    });
    assert_no_fallback(&p, "fp.sqrt");
}

#[test]
fn test_fp_rem_round_no_fallback() {
    let p = fp16_program(|p, s, _| {
        let x = p.declare_const("x", s.clone());
        let y = p.declare_const("y", s);
        p.assert(x.fp_rem(y).fp_is_nan());
    });
    assert_no_fallback(&p, "fp.rem");

    let p = fp16_program(|p, s, rm| {
        let x = p.declare_const("x", s);
        p.assert(x.fp_round_to_integral(rm).fp_is_nan());
    });
    assert_no_fallback(&p, "fp.roundToIntegral");
}
