// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! evaluate_term tests: bitvector theory predicates, BV shift/div/concat/extend,
//! and model validation tests (validate_model, validate_sat_assumptions).

use super::*;

// ==========================================================================
// evaluate_term: theory predicates
// ==========================================================================

#[test]
fn test_evaluate_term_bv_predicates_evaluate_concretely() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(8));
    let bvult = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvult"), vec![x, y], Sort::Bool);
    let bvslt = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvslt"), vec![x, y], Sort::Bool);

    let mut bv_values = HashMap::default();
    bv_values.insert(x, BigInt::from(0xFFu8)); // -1 signed, 255 unsigned
    bv_values.insert(y, BigInt::from(1u8));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    // Unsigned: 255 < 1 is false
    assert_eq!(
        executor.evaluate_term(&model, bvult),
        EvalValue::Bool(false)
    );
    // Signed: -1 < 1 is true
    assert_eq!(executor.evaluate_term(&model, bvslt), EvalValue::Bool(true));
}

#[test]
fn test_evaluate_term_bv_ite_keeps_array_condition_unknown_11936() {
    let mut executor = Executor::new();
    let array_sort = Sort::array(Sort::bitvec(32), Sort::bitvec(8));
    let mem0 = executor.ctx.terms.mk_var("mem0", array_sort.clone());
    let mem1 = executor.ctx.terms.mk_var("mem1", array_sort);
    let idx = executor.ctx.terms.mk_bitvec(BigInt::from(3u8), 32);
    let value = executor.ctx.terms.mk_bitvec(BigInt::from(0xaau8), 8);
    let store = executor.ctx.terms.mk_store(mem0, idx, value);
    let array_eq = executor.ctx.terms.mk_eq_coerce_no_ite_expand(mem1, store);
    let one = executor.ctx.terms.mk_bitvec(BigInt::one(), 1);
    let zero = executor.ctx.terms.mk_bitvec(BigInt::zero(), 1);
    let ite = executor.ctx.terms.mk_ite(array_eq, one, zero);

    let mut values = HashMap::default();
    values.insert(ite, BigInt::one());
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    assert_eq!(
        executor.evaluate_term(&model, ite),
        EvalValue::Unknown,
        "array-conditioned BV ITE must not become independent evidence via BV cache"
    );
}

#[test]
fn test_validate_model_rejects_false_bv_predicate_assertion() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(8));
    let bvult = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvult"), vec![x, y], Sort::Bool);
    executor.ctx.assertions.push(bvult);

    let mut bv_values = HashMap::default();
    bv_values.insert(x, BigInt::from(0u8));
    bv_values.insert(y, BigInt::from(0u8));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    let err = executor
        .validate_model()
        .expect_err("Expected false bvult assertion to be rejected");
    assert!(
        err.contains("Assertion 0 violated"),
        "Unexpected error: {err}"
    );
}

#[test]
fn test_validate_model_rejects_unknown_bv_with_uf_subterms() {
    // (#3903) Fail closed: if bvult(f(u), g(u)) is Unknown, model
    // validation must reject and the SAT path must degrade to Unknown.
    let mut executor = Executor::new();
    let u = executor
        .ctx
        .terms
        .mk_var("u", Sort::Uninterpreted("U".to_string()));
    let f_u = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![u], Sort::bitvec(8));
    let g_u = executor
        .ctx
        .terms
        .mk_app(Symbol::named("g"), vec![u], Sort::bitvec(8));
    let bvult = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvult"), vec![f_u, g_u], Sort::Bool);
    executor.ctx.assertions.push(bvult);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_model()
        .expect_err("UF-containing BV assertion Unknown should be rejected");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
}

#[test]
fn test_evaluate_bv_shift_operations() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(8));
    let shl = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvshl"), vec![x, y], Sort::bitvec(8));
    let lshr = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvlshr"), vec![x, y], Sort::bitvec(8));
    let ashr = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvashr"), vec![x, y], Sort::bitvec(8));

    let mut bv_values = HashMap::default();
    bv_values.insert(x, BigInt::from(0b1100_0011u8)); // 195 unsigned, -61 signed
    bv_values.insert(y, BigInt::from(2u8));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    // shl: 0b1100_0011 << 2 = 0b0000_1100 (mod 256)
    assert_eq!(
        executor.evaluate_term(&model, shl),
        EvalValue::BitVec {
            value: BigInt::from(0b0000_1100u8),
            width: 8,
        }
    );
    // lshr (logical): 0b1100_0011 >> 2 = 0b0011_0000
    assert_eq!(
        executor.evaluate_term(&model, lshr),
        EvalValue::BitVec {
            value: BigInt::from(0b0011_0000u8),
            width: 8,
        }
    );
    // ashr (arithmetic): -61 >> 2 = -16 = 0b1111_0000 (240 unsigned)
    assert_eq!(
        executor.evaluate_term(&model, ashr),
        EvalValue::BitVec {
            value: BigInt::from(0b1111_0000u8),
            width: 8,
        }
    );
}

#[test]
fn test_evaluate_bv_div_rem() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(8));
    let udiv = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvudiv"), vec![x, y], Sort::bitvec(8));
    let urem = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvurem"), vec![x, y], Sort::bitvec(8));

    let mut bv_values = HashMap::default();
    bv_values.insert(x, BigInt::from(200u8));
    bv_values.insert(y, BigInt::from(7u8));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    // 200 / 7 = 28
    assert_eq!(
        executor.evaluate_term(&model, udiv),
        EvalValue::BitVec {
            value: BigInt::from(28u8),
            width: 8,
        }
    );
    // 200 % 7 = 4
    assert_eq!(
        executor.evaluate_term(&model, urem),
        EvalValue::BitVec {
            value: BigInt::from(4u8),
            width: 8,
        }
    );
}

#[test]
fn test_evaluate_bv_concat_extend() {
    let mut executor = Executor::new();
    let hi = executor.ctx.terms.mk_var("hi", Sort::bitvec(4));
    let lo = executor.ctx.terms.mk_var("lo", Sort::bitvec(4));
    let concat = executor
        .ctx
        .terms
        .mk_app(Symbol::named("concat"), vec![hi, lo], Sort::bitvec(8));

    let narrow = executor.ctx.terms.mk_var("narrow", Sort::bitvec(4));
    let zext =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("zero_extend"), vec![narrow], Sort::bitvec(8));
    let sext =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("sign_extend"), vec![narrow], Sort::bitvec(8));

    let mut bv_values = HashMap::default();
    bv_values.insert(hi, BigInt::from(0b1010u8));
    bv_values.insert(lo, BigInt::from(0b0101u8));
    bv_values.insert(narrow, BigInt::from(0b1100u8)); // -4 in 4-bit signed
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    // concat(0b1010, 0b0101) = 0b10100101 = 165
    assert_eq!(
        executor.evaluate_term(&model, concat),
        EvalValue::BitVec {
            value: BigInt::from(0b10100101u8),
            width: 8,
        }
    );
    // zero_extend(0b1100) = 0b00001100 = 12
    assert_eq!(
        executor.evaluate_term(&model, zext),
        EvalValue::BitVec {
            value: BigInt::from(0b00001100u8),
            width: 8,
        }
    );
    // sign_extend(0b1100) = 0b11111100 = 252 (sign bit propagated)
    assert_eq!(
        executor.evaluate_term(&model, sext),
        EvalValue::BitVec {
            value: BigInt::from(0b11111100u8),
            width: 8,
        }
    );
}

/// Regression test for #5627: when a sign_extend child variable is missing from
/// the BV model (e.g., eliminated by BVE and not recovered), the evaluator should
/// fall back to the BV model cache for the application term instead of returning
/// Unknown.
#[test]
fn test_bv_model_cache_fallback_sign_extend_5627() {
    let mut executor = Executor::new();
    // Create a variable "x" (4-bit) and sign_extend to 8-bit.
    // Do NOT put "x" in the BV model — simulates BVE eliminating it.
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(4));
    let sext = executor
        .ctx
        .terms
        .mk_app(Symbol::named("sign_extend"), vec![x], Sort::bitvec(8));

    // Only the application term is in the BV model (from bit-blasting),
    // NOT the child variable. This simulates BVE eliminating "x".
    let mut bv_values = HashMap::default();
    // sign_extend(0b1100) = 0b11111100 = 252
    bv_values.insert(sext, BigInt::from(252u16));

    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    // Without the fallback, this would return Unknown (child "x" evaluates to
    // default 0, then sign_extend(0) = 0, which is wrong).
    // Actually, child "x" is in the BV model as default 0 (line 555), so
    // sign_extend(0) = 0. But 0 != 252 from the cache. The fallback only
    // fires when the child returns non-BitVec (Unknown).
    //
    // Revised scenario: child "x" is NOT a BV var but returns Unknown.
    // Use an Int-sorted var to make the child return a non-BitVec value.
    // Actually, x IS BV-sorted, so it defaults to 0. The sign_extend
    // of 0 is 0, which is semantically correct for a missing variable.
    //
    // The real fallback triggers when evaluate_term returns non-BitVec for
    // the child — which happens for more complex terms, not simple vars.
    // Let's test with a non-trivial child (e.g., a UF application).
    let f_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], Sort::bitvec(4));
    let sext2 = executor
        .ctx
        .terms
        .mk_app(Symbol::named("sign_extend"), vec![f_x], Sort::bitvec(8));

    let mut bv_values2 = HashMap::default();
    // sign_extend(f(x)) = 252 in the BV model cache
    bv_values2.insert(sext2, BigInt::from(252u16));

    let mut model2 = empty_model();
    model2.bv_model = Some(BvModel {
        values: bv_values2,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    // f(x) is an uninterpreted function — with no EUF model, it returns Unknown.
    // sign_extend should fall back to BV model cache and return 252.
    assert_eq!(
        executor.evaluate_term(&model2, sext2),
        EvalValue::BitVec {
            value: BigInt::from(252u16),
            width: 8,
        }
    );
}

/// Regression test for #5627: zero_extend BV model cache fallback.
#[test]
fn test_bv_model_cache_fallback_zero_extend_5627() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(4));
    // f(x) returns Unknown (no EUF model)
    let f_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], Sort::bitvec(4));
    let zext = executor
        .ctx
        .terms
        .mk_app(Symbol::named("zero_extend"), vec![f_x], Sort::bitvec(8));

    let mut bv_values = HashMap::default();
    bv_values.insert(zext, BigInt::from(12u8)); // 0b00001100

    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    assert_eq!(
        executor.evaluate_term(&model, zext),
        EvalValue::BitVec {
            value: BigInt::from(12u8),
            width: 8,
        }
    );
}

/// Regression test for #5627: concat BV model cache fallback.
#[test]
fn test_bv_model_cache_fallback_concat_5627() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(4));
    let f_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], Sort::bitvec(4));
    let concat = executor
        .ctx
        .terms
        .mk_app(Symbol::named("concat"), vec![x, f_x], Sort::bitvec(8));

    let mut bv_values = HashMap::default();
    bv_values.insert(x, BigInt::from(0b1010u8));
    // f(x) is Unknown, but concat application has a cached value
    bv_values.insert(concat, BigInt::from(0b10100101u8));

    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    // One child (f(x)) returns Unknown, so concat falls back to cache
    assert_eq!(
        executor.evaluate_term(&model, concat),
        EvalValue::BitVec {
            value: BigInt::from(0b10100101u8),
            width: 8,
        }
    );
}

/// Regression test for #5627 audit: bvcomp BV model cache fallback.
/// bvcomp was missed in the original fix — it returns (_ BitVec 1) and
/// should also fall back to the cache when children return Unknown.
#[test]
fn test_bv_model_cache_fallback_bvcomp_5627() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    // f(x) returns Unknown (no EUF model)
    let f_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], Sort::bitvec(8));
    // bvcomp(x, f(x)) -> (_ BitVec 1), result 1 means equal, 0 means not equal
    let bvcomp = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvcomp"), vec![x, f_x], Sort::bitvec(1));

    let mut bv_values = HashMap::default();
    bv_values.insert(x, BigInt::from(42u8));
    // f(x) is Unknown, but bvcomp application has a cached value of 1 (equal)
    bv_values.insert(bvcomp, BigInt::one());

    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    // One child (f(x)) returns Unknown, so bvcomp falls back to cache
    assert_eq!(
        executor.evaluate_term(&model, bvcomp),
        EvalValue::BitVec {
            value: BigInt::one(),
            width: 1,
        }
    );
}

/// Regression test for #5461: when a BV UF application is missing from the BV
/// model cache, evaluation should reuse a congruent application with the same
/// function symbol and argument values.
#[test]
fn test_bv_uf_congruence_fallback_5461() {
    let mut executor = Executor::new();
    let sort_u = Sort::Uninterpreted("U".to_string());
    let x = executor.ctx.terms.mk_var("x", sort_u.clone());
    let y = executor.ctx.terms.mk_var("y", sort_u);
    let f_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], Sort::bitvec(8));
    let f_y = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![y], Sort::bitvec(8));

    let mut bv_values = HashMap::default();
    bv_values.insert(f_x, BigInt::from(0x2Au8));

    let mut term_values = HashMap::default();
    term_values.insert(x, "@U!0".to_string());
    term_values.insert(y, "@U!0".to_string());

    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    model.euf_model = Some(EufModel {
        term_values,
        ..Default::default()
    });

    assert_eq!(
        executor.evaluate_term(&model, f_y),
        EvalValue::BitVec {
            value: BigInt::from(0x2Au8),
            width: 8,
        }
    );
}

/// Regression test for #5627: sign_extend with a BV variable child that is
/// MISSING from the BV model (eliminated by preprocessing, not recovered).
/// Without the is_bv_child_missing_from_model check, evaluate_term returns
/// BitVec(0) for the missing child, then sign_extend(0) = 0, which may
/// differ from the correct cached value. With the fix, the sign_extend
/// handler detects the missing child and falls back to the BV model cache.
#[test]
fn test_sign_extend_missing_child_var_uses_cache_5627() {
    let mut executor = Executor::new();
    // Child "x" is a 32-bit BV variable, NOT in the BV model (simulates
    // preprocessing elimination with failed recovery).
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(32));
    // sign_extend from 32-bit to 64-bit
    let sext = executor
        .ctx
        .terms
        .mk_app(Symbol::named("sign_extend"), vec![x], Sort::bitvec(64));

    // Only the sign_extend APPLICATION term is in the BV model cache
    // (from bit-blasting). The child "x" is NOT — it was eliminated.
    // The correct value is 0xFFFFFFFF_FFFF0000 (sign_extend of 0xFFFF0000).
    let expected_val = BigInt::from(0xFFFF_FFFF_FFFF_0000u64);
    let mut bv_values = HashMap::default();
    bv_values.insert(sext, expected_val.clone());
    // x is deliberately NOT in bv_values

    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    // Without the fix: evaluate_term(x) -> BitVec(0, 32) (default)
    //   sign_extend(0) -> BitVec(0, 64) (WRONG)
    // With the fix: detect x is missing -> fall back to cache -> BitVec(0xFFFFFFFFFFFF0000, 64) (CORRECT)
    assert_eq!(
        executor.evaluate_term(&model, sext),
        EvalValue::BitVec {
            value: expected_val,
            width: 64,
        }
    );
}

/// Same as above but for zero_extend with a missing child variable.
#[test]
fn test_zero_extend_missing_child_var_uses_cache_5627() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(32));
    let zext = executor
        .ctx
        .terms
        .mk_app(Symbol::named("zero_extend"), vec![x], Sort::bitvec(64));

    let expected_val = BigInt::from(0x0000_0000_FFFF_0000u64);
    let mut bv_values = HashMap::default();
    bv_values.insert(zext, expected_val.clone());
    // x is deliberately NOT in bv_values

    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    assert_eq!(
        executor.evaluate_term(&model, zext),
        EvalValue::BitVec {
            value: expected_val,
            width: 64,
        }
    );
}

#[test]
fn test_validate_model_rejects_unknown_non_bv_comparison() {
    // (#3903) Non-BV-comparison assertions that evaluate to Unknown are rejected.
    // Unknown means the evaluator cannot verify the model satisfies the assertion.
    // Use an uninterpreted function (UF) application: the evaluator cannot resolve
    // UF applications without a UF model, so it returns Unknown and is rejected.
    let mut executor = Executor::new();
    let hello = executor.ctx.terms.mk_string("hello".to_string());
    let uf_app =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("my_uf_predicate"), vec![hello], Sort::Bool);
    executor.ctx.assertions.push(uf_app);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_model()
        .expect_err("Unknown UF application should be rejected by validate_model");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
}

#[test]
fn test_validate_model_rejects_unknown_string_var_assertion() {
    // (#3903) Fail closed for String assertions that evaluate to Unknown.
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::String);
    let pattern = executor.ctx.terms.mk_string("hello".to_string());
    let contains =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("str.contains"), vec![x, pattern], Sort::Bool);
    executor.ctx.assertions.push(contains);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_model()
        .expect_err("Unknown String assertion should be rejected");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
}

#[test]
fn test_validate_model_accepts_quantified_assertion_skipped_before_evaluation() {
    // Quantified assertions are skipped before evaluation —
    // validate_model returns Ok because the solver already verified
    // them via E-matching/CEGQI during solving.
    let mut executor = Executor::new();
    let body = executor.ctx.terms.mk_var("x", Sort::Bool);
    let forall = executor
        .ctx
        .terms
        .mk_forall(vec![("x".to_string(), Sort::Bool)], body);
    executor.ctx.assertions.push(forall);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    executor
        .validate_model()
        .expect("Quantified assertion should be accepted (skipped before evaluation)");
}

#[test]
fn test_validate_model_rejects_unknown_bv_comparison_with_uf_arguments() {
    // (#3903) Fail closed even when the Unknown originates from UF args.
    let mut executor = Executor::new();
    let x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bv_x"), vec![], Sort::bitvec(8));
    let y = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bv_y"), vec![], Sort::bitvec(8));
    let comparison = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvult"), vec![x, y], Sort::Bool);
    executor.ctx.assertions.push(comparison);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_model()
        .expect_err("Unknown BV comparison should be rejected");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
}

#[test]
fn test_validate_model_accepts_unknown_quantified_assertion() {
    // Quantified assertions cannot be model-checked; Unknown is acceptable.
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));
    let body = executor
        .ctx
        .terms
        .mk_app(Symbol::named(">="), vec![x, zero], Sort::Bool);
    let forall = executor
        .ctx
        .terms
        .mk_forall(vec![("x".to_string(), Sort::Int)], body);
    executor.ctx.assertions.push(forall);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    executor
        .validate_model()
        .expect("Quantified assertion Unknown should be accepted");
}

#[test]
fn test_validate_model_rejects_unknown_uf_assertion() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let p_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("P"), vec![x], Sort::Bool);
    executor.ctx.assertions.push(p_x);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_model()
        .expect_err("Unknown UF predicate assertion must be rejected");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
}

#[test]
fn test_validate_model_rejects_unknown_array_assertion() {
    // Unknown array assertions return Incomplete so
    // finalize_sat_model_validation can return Unknown instead of
    // silently accepting a potentially wrong SAT answer (#5116).
    let mut executor = Executor::new();
    let a = executor
        .ctx
        .terms
        .mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let i = executor.ctx.terms.mk_var("i", Sort::Int);
    let v = executor.ctx.terms.mk_var("v", Sort::Int);
    let sel = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![a, i], Sort::Int);
    let eq = executor.ctx.terms.mk_eq(sel, v);
    executor.ctx.assertions.push(eq);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_model()
        .expect_err("Unknown array assertion should now be rejected");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
}

#[test]
fn test_finalize_sat_model_validation_degrades_array_false_with_sat_assignment() {
    let mut executor = Executor::new();
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));
    let one = executor.ctx.terms.mk_int(BigInt::from(1));
    let const_array = executor.ctx.terms.mk_app(
        Symbol::named("const-array"),
        vec![zero],
        Sort::array(Sort::Int, Sort::Int),
    );
    let stored = executor.ctx.terms.mk_app(
        Symbol::named("store"),
        vec![const_array, zero, one],
        Sort::array(Sort::Int, Sort::Int),
    );
    let selected =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), vec![stored, zero], Sort::Int);
    let assertion = executor
        .ctx
        .terms
        .mk_app(Symbol::named("<"), vec![selected, zero], Sort::Bool);
    assert!(
        executor.contains_array_term(assertion),
        "assertion must retain array structure"
    );
    executor.ctx.assertions.push(assertion);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model_with_sat_assignments(&[(assertion, true)]));

    let result = executor
        .finalize_sat_model_validation()
        .expect("array false assertion should degrade to Unknown");

    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(executor.last_result, Some(SolveResult::Unknown));
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::Incomplete)
    );
}

#[test]
fn test_finalize_sat_model_validation_degrades_bv_backed_array_false_11929() {
    let mut executor = Executor::new();
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));
    let one = executor.ctx.terms.mk_int(BigInt::from(1));
    let const_array = executor.ctx.terms.mk_app(
        Symbol::named("const-array"),
        vec![zero],
        Sort::array(Sort::Int, Sort::Int),
    );
    let stored = executor.ctx.terms.mk_app(
        Symbol::named("store"),
        vec![const_array, zero, one],
        Sort::array(Sort::Int, Sort::Int),
    );
    let selected =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), vec![stored, zero], Sort::Int);
    let assertion = executor
        .ctx
        .terms
        .mk_app(Symbol::named("<"), vec![selected, zero], Sort::Bool);
    executor.ctx.assertions.push(assertion);
    executor.last_result = Some(SolveResult::Sat);
    let mut model = model_with_sat_assignments(&[(assertion, true)]);
    model.bv_model = Some(BvModel {
        values: HashMap::default(),
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    executor.last_model = Some(model);

    let result = executor
        .finalize_sat_model_validation()
        .expect("BV-backed array false assertion must fail closed");

    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(executor.last_result, Some(SolveResult::Unknown));
    assert_eq!(
        executor.statistics().get_int("model_validation_failures"),
        Some(1)
    );
    assert_eq!(
        executor.statistics().get_string("unknown.phase"),
        Some("model-validation")
    );
    assert_eq!(
        executor.statistics().get_string("unknown.cost_center"),
        Some("smt-model-validation")
    );
    assert!(
        executor
            .statistics()
            .get_string("unknown.detail")
            .is_some_and(|detail| detail.contains("BV-backed array assertion evaluates to false")),
        "missing model-validation detail: {:?}",
        executor.statistics().get_string("unknown.detail")
    );
}

#[test]
fn test_finalize_sat_model_validation_resolves_bv_backed_array_select_via_asserted_equality_11936()
{
    let mut executor = Executor::new();
    let arr = executor
        .ctx
        .terms
        .mk_var("arr", Sort::array(Sort::bitvec(8), Sort::bitvec(8)));
    let idx = executor.ctx.terms.mk_var("idx", Sort::bitvec(8));
    let selected =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), vec![arr, idx], Sort::bitvec(8));
    let expected = executor.ctx.terms.mk_bitvec(BigInt::from(0x42u8), 8);
    let assertion = executor.ctx.terms.mk_eq(selected, expected);
    executor.ctx.assertions.push(assertion);
    executor.last_result = Some(SolveResult::Sat);

    let mut model = model_with_sat_assignments(&[(assertion, true)]);
    model.bv_model = Some(BvModel {
        values: HashMap::default(),
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    executor.last_model = Some(model);

    let result = executor
        .finalize_sat_model_validation()
        .expect("BV-backed array select resolved via asserted equality");

    // #aufbv-nonbv-elem completeness improvement: `select(arr,idx) == 0x42` is an
    // ASSERTED equality (true in every model), so the validator resolves the
    // otherwise-unvalued select to 0x42 — a genuine satisfying model — and the
    // full-model re-validation confirms it, yielding Sat instead of a conservative
    // Unknown. (Sound: the resolved value comes from the solver's own committed
    // interpretation; a mis-resolution would fail re-validation and degrade.)
    assert_eq!(result, SolveResult::Sat);
    assert_eq!(executor.last_result, Some(SolveResult::Sat));
}

#[test]
fn test_finalize_sat_model_validation_resolves_covered_direct_bv_backed_array_select_11936() {
    let mut executor = Executor::new();
    let arr = executor
        .ctx
        .terms
        .mk_var("arr", Sort::array(Sort::bitvec(8), Sort::bitvec(8)));
    let idx = executor.ctx.terms.mk_var("idx", Sort::bitvec(8));
    let selected =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), vec![arr, idx], Sort::bitvec(8));
    let expected = executor.ctx.terms.mk_bitvec(BigInt::from(0x42u8), 8);
    let assertion = executor.ctx.terms.mk_eq(selected, expected);
    executor.ctx.assertions.push(assertion);
    executor
        .model_validation_delegated_assertions
        .insert(assertion);
    executor.last_result = Some(SolveResult::Sat);

    let mut model = model_with_sat_assignments(&[(assertion, true)]);
    model.bv_model = Some(BvModel {
        values: HashMap::default(),
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    executor.last_model = Some(model);

    let result = executor
        .finalize_sat_model_validation()
        .expect("covered direct BV-backed array select resolved via asserted equality");

    // Same #aufbv-nonbv-elem completeness improvement as the direct case: the
    // asserted `select(arr,idx) == 0x42` resolves the select to a genuine value,
    // re-validation confirms it, so the covered/delegated path returns Sat (not a
    // conservative Unknown).
    assert_eq!(result, SolveResult::Sat);
    assert_eq!(executor.last_result, Some(SolveResult::Sat));
}

#[test]
fn test_finalize_sat_model_validation_delegates_bv_backed_array_wrapper_unknown_11936() {
    let mut executor = Executor::new();
    let arr = executor
        .ctx
        .terms
        .mk_var("arr", Sort::array(Sort::bitvec(8), Sort::bitvec(8)));
    let idx = executor.ctx.terms.mk_var("idx", Sort::bitvec(8));
    let selected =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), vec![arr, idx], Sort::bitvec(8));
    let expected = executor.ctx.terms.mk_bitvec(BigInt::from(0x42u8), 8);
    let array_eq = executor.ctx.terms.mk_eq(selected, expected);
    let one = executor.ctx.terms.mk_bitvec(BigInt::one(), 1);
    let zero = executor.ctx.terms.mk_bitvec(BigInt::zero(), 1);
    let wrapper = executor.ctx.terms.mk_ite(array_eq, one, zero);
    let assertion = executor.ctx.terms.mk_eq_coerce_no_ite_expand(one, wrapper);
    executor.ctx.assertions.push(assertion);
    executor
        .model_validation_delegated_assertions
        .insert(assertion);
    executor.last_result = Some(SolveResult::Sat);

    let mut model = model_with_sat_assignments(&[(assertion, true)]);
    model.bv_model = Some(BvModel {
        values: HashMap::default(),
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    executor.last_model = Some(model);

    let result = executor
        .finalize_sat_model_validation()
        .expect("explicitly covered BV-backed array wrapper should delegate");

    assert_eq!(result, SolveResult::Sat);
    assert_eq!(executor.last_result, Some(SolveResult::Sat));
    assert_eq!(
        executor.statistics().get_int("model_validation_failures"),
        Some(0)
    );
    assert_eq!(
        executor
            .statistics()
            .get_int("model_validation.array_delegated"),
        Some(1)
    );
}

#[test]
fn test_finalize_sat_model_validation_degrades_uncovered_bv_backed_array_wrapper_11936() {
    let mut executor = Executor::new();
    let arr = executor
        .ctx
        .terms
        .mk_var("arr", Sort::array(Sort::bitvec(8), Sort::bitvec(8)));
    let idx = executor.ctx.terms.mk_var("idx", Sort::bitvec(8));
    let selected =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), vec![arr, idx], Sort::bitvec(8));
    let expected = executor.ctx.terms.mk_bitvec(BigInt::from(0x42u8), 8);
    let array_eq = executor.ctx.terms.mk_eq(selected, expected);
    let one = executor.ctx.terms.mk_bitvec(BigInt::one(), 1);
    let zero = executor.ctx.terms.mk_bitvec(BigInt::zero(), 1);
    let wrapper = executor.ctx.terms.mk_ite(array_eq, one, zero);
    let assertion = executor.ctx.terms.mk_eq_coerce_no_ite_expand(one, wrapper);
    executor.ctx.assertions.push(assertion);
    executor.last_result = Some(SolveResult::Sat);

    let mut model = model_with_sat_assignments(&[(assertion, true)]);
    model.bv_model = Some(BvModel {
        values: HashMap::default(),
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    executor.last_model = Some(model);

    let result = executor
        .finalize_sat_model_validation()
        .expect("uncovered SAT-assigned BV-backed array wrapper should degrade to Unknown");

    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(executor.last_result, Some(SolveResult::Unknown));
    assert_eq!(
        executor
            .statistics()
            .get_int("model_validation.array_delegated")
            .unwrap_or(0),
        0
    );
}

#[test]
fn test_finalize_sat_model_validation_degrades_uncovered_bv_backed_array_wrapper_false_11936() {
    use ay_arrays::ArrayInterpretation;

    let mut executor = Executor::new();
    let arr = executor
        .ctx
        .terms
        .mk_var("arr", Sort::array(Sort::bitvec(8), Sort::bitvec(8)));
    let idx = executor.ctx.terms.mk_var("idx", Sort::bitvec(8));
    let selected =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), vec![arr, idx], Sort::bitvec(8));
    let expected = executor.ctx.terms.mk_bitvec(BigInt::from(0x42u8), 8);
    let array_eq = executor.ctx.terms.mk_eq(selected, expected);
    let cond = executor.ctx.terms.mk_var("cond", Sort::Bool);
    let true_term = executor.ctx.terms.mk_bool(true);
    let assertion = executor.ctx.terms.mk_ite(cond, array_eq, true_term);
    executor.ctx.assertions.push(assertion);
    executor.last_result = Some(SolveResult::Sat);

    let mut model = model_with_sat_assignments(&[(assertion, true), (cond, true)]);
    model.array_model = Some(ArrayModel {
        array_values: HashMap::from_iter([(
            arr,
            ArrayInterpretation {
                index_sort: Some(Sort::bitvec(8)),
                element_sort: Some(Sort::bitvec(8)),
                default: Some("#x00".to_string()),
                stores: vec![],
            },
        )]),
        ..Default::default()
    });
    model.bv_model = Some(BvModel {
        values: HashMap::default(),
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    executor.last_model = Some(model);

    let result = executor
        .finalize_sat_model_validation()
        .expect("uncovered BV-backed array wrapper false should degrade to Unknown");

    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(
        executor
            .statistics()
            .get_int("model_validation.array_delegated"),
        Some(0)
    );
}

#[test]
fn test_finalize_sat_model_validation_delegates_covered_bv_backed_array_wrapper_false_11936() {
    use ay_arrays::ArrayInterpretation;

    let mut executor = Executor::new();
    let arr = executor
        .ctx
        .terms
        .mk_var("arr", Sort::array(Sort::bitvec(8), Sort::bitvec(8)));
    let idx = executor.ctx.terms.mk_var("idx", Sort::bitvec(8));
    let selected =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), vec![arr, idx], Sort::bitvec(8));
    let expected = executor.ctx.terms.mk_bitvec(BigInt::from(0x42u8), 8);
    let array_eq = executor.ctx.terms.mk_eq(selected, expected);
    let cond = executor.ctx.terms.mk_var("cond", Sort::Bool);
    let true_term = executor.ctx.terms.mk_bool(true);
    let assertion = executor.ctx.terms.mk_ite(cond, array_eq, true_term);
    executor.ctx.assertions.push(assertion);
    executor
        .model_validation_delegated_assertions
        .insert(assertion);
    executor.last_result = Some(SolveResult::Sat);

    let mut model = model_with_sat_assignments(&[(assertion, true), (cond, true)]);
    model.array_model = Some(ArrayModel {
        array_values: HashMap::from_iter([(
            arr,
            ArrayInterpretation {
                index_sort: Some(Sort::bitvec(8)),
                element_sort: Some(Sort::bitvec(8)),
                default: Some("#x00".to_string()),
                stores: vec![],
            },
        )]),
        ..Default::default()
    });
    model.bv_model = Some(BvModel {
        values: HashMap::default(),
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    executor.last_model = Some(model);

    let result = executor
        .finalize_sat_model_validation()
        .expect("explicitly covered BV-backed array wrapper false should delegate");

    assert_eq!(result, SolveResult::Sat);
    assert_eq!(
        executor
            .statistics()
            .get_int("model_validation.array_delegated"),
        Some(1)
    );
}

#[test]
fn test_finalize_sat_model_validation_degrades_uncovered_bv_ite_false_11936() {
    let mut executor = Executor::new();
    let cond = executor.ctx.terms.mk_var("cond", Sort::Bool);
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    let zero = executor.ctx.terms.mk_bitvec(BigInt::zero(), 8);
    let one = executor.ctx.terms.mk_bitvec(BigInt::one(), 8);
    let selected = executor.ctx.terms.mk_ite(cond, zero, one);
    let assertion = executor.ctx.terms.mk_eq_coerce_no_ite_expand(x, selected);
    executor.ctx.assertions.push(assertion);
    executor.last_result = Some(SolveResult::Sat);

    let mut model = model_with_sat_assignments(&[(assertion, true)]);
    model.bv_model = Some(BvModel {
        values: HashMap::from_iter([(x, BigInt::one())]),
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::from_iter([(cond, true)]),
    });
    executor.last_model = Some(model);

    let result = executor
        .finalize_sat_model_validation()
        .expect("uncovered BV ITE false should degrade to Unknown");

    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(executor.last_result, Some(SolveResult::Unknown));
    assert_eq!(
        executor
            .statistics()
            .get_int("model_validation.delegated")
            .unwrap_or(0),
        0
    );
}

#[test]
fn test_finalize_sat_model_validation_degrades_covered_restored_bv_ite_false_11936() {
    // (#bv-ite-bool-model) This test originally asserted the OPPOSITE
    // behavior: that delegation coverage lets a covered BV ITE assertion pass
    // as Sat even though the emitted model CONCRETELY evaluates it to false
    // (cond=true selects the zero branch, but x=1: `(= x (ite cond 0 1))` is
    // refuted). Bit-blast coverage certifies the SAT solver's internal
    // assignment, NOT the reconstructed model, so that delegation masked
    // genuinely invalid models (qf_bv fuzzer seeds 5/432/439). A concrete
    // evaluator refutation is now final regardless of coverage: the covered
    // case must degrade to Unknown exactly like the uncovered sibling above.
    let mut executor = Executor::new();
    let cond = executor.ctx.terms.mk_var("cond", Sort::Bool);
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(8));
    let zero = executor.ctx.terms.mk_bitvec(BigInt::zero(), 8);
    let one = executor.ctx.terms.mk_bitvec(BigInt::one(), 8);
    let selected = executor.ctx.terms.mk_ite(cond, zero, one);
    let assertion = executor.ctx.terms.mk_eq_coerce_no_ite_expand(x, selected);
    executor.ctx.assertions.push(assertion);
    executor
        .model_validation_delegated_assertions
        .insert(assertion);
    executor.last_result = Some(SolveResult::Sat);

    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: HashMap::from_iter([(x, BigInt::one()), (y, BigInt::one())]),
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::from_iter([(cond, true)]),
    });
    executor.last_model = Some(model);

    let result = executor
        .finalize_sat_model_validation()
        .expect("covered but concretely-refuted BV ITE model must degrade to Unknown");

    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(executor.last_result, Some(SolveResult::Unknown));
    assert_eq!(
        executor
            .statistics()
            .get_int("model_validation.delegated")
            .unwrap_or(0),
        0
    );
}

#[test]
fn test_validate_model_equality_sat_fallback() {
    // (#5499) When both operands of an equality evaluate to Unknown
    // (e.g., string variables with no string model), the equality
    // returns Unknown (no SAT-model fallback — that would be circular).
    // If the SAT variable is true, validate_model tracks this as
    // sat_fallback_count. With only one assertion and no independent
    // evidence, the zero-check guard rejects the model.
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("a", Sort::String);
    let b = executor.ctx.terms.mk_var("b", Sort::String);
    let eq_ab = executor.ctx.terms.mk_eq(a, b);
    executor.ctx.assertions.push(eq_ab);

    // Build a model where the equality term has SAT variable = true
    let model = model_with_sat_assignments(&[(eq_ab, true)]);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    let err = executor
        .validate_model()
        .expect_err("SAT-fallback-only model should be rejected (#5499)");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
}

#[test]
fn test_validate_model_equality_sat_fallback_false_rejects() {
    // (#5499) SAT-fallback false → reject. UF sort, not String (#4057 handler).
    let mut executor = Executor::new();
    let uf = Sort::Uninterpreted("UFSort".into());
    let a = executor.ctx.terms.mk_var("a", uf.clone());
    let b = executor.ctx.terms.mk_var("b", uf);
    let eq_ab = executor.ctx.terms.mk_eq(a, b);
    executor.ctx.assertions.push(eq_ab);

    let model = model_with_sat_assignments(&[(eq_ab, false)]);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    let err = executor
        .validate_model()
        .expect_err("SAT fallback false should reject");
    assert!(
        err.contains("evaluates to Unknown"),
        "Expected 'evaluates to Unknown' error, got: {err}"
    );
}

#[test]
fn test_validate_model_string_equality_uses_string_model() {
    // Validate leaf string equality without SAT-literal fallback by
    // providing a concrete string model assignment.
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::String);
    let abc = executor.ctx.terms.mk_string("abc".to_string());
    let eq_x_abc = executor.ctx.terms.mk_eq(x, abc);
    executor.ctx.assertions.push(eq_x_abc);

    let mut string_values = HashMap::default();
    string_values.insert(x, "abc".to_string());
    let mut model = empty_model();
    model.string_model = Some(StringModel {
        values: string_values,
    });
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    executor
        .validate_model()
        .expect("String equality should validate from string model");
}

#[test]
fn test_validate_model_rejects_unknown_extf_string_equality() {
    // (#3903) Unsupported extf terms evaluating to Unknown are rejected.
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::String);
    let lower_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("str.to_lower"), vec![x], Sort::String);
    let abc = executor.ctx.terms.mk_string("abc".to_string());
    let eq_term = executor.ctx.terms.mk_eq(lower_x, abc);
    executor.ctx.assertions.push(eq_term);

    let model = model_with_sat_assignments(&[(eq_term, true)]);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    let err = executor
        .validate_model()
        .expect_err("Unknown extf equality should be rejected");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
}

#[test]
fn test_finalize_sat_model_validation_returns_unknown_for_unevaluable_string_term() {
    // (#3903) Unknown validation must degrade SAT to Unknown.
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::String);
    let pattern = executor.ctx.terms.mk_string("hello".to_string());
    let contains =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("str.contains"), vec![x, pattern], Sort::Bool);
    executor.ctx.assertions.push(contains);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let result = executor.finalize_sat_model_validation();
    assert!(
        matches!(result, Ok(SolveResult::Unknown)),
        "Expected Unknown for unevaluable string term, got: {result:?}"
    );
}

#[test]
fn test_finalize_sat_assumption_validation_accepts_true_assumption() {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("a", Sort::Bool);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model_with_sat_assignments(&[(a, true)]));

    let result = executor
        .finalize_sat_assumption_validation(&[a])
        .expect("true assumption should pass assumption validation");

    assert_eq!(result, SolveResult::Sat);
}

#[test]
fn test_finalize_sat_assumption_validation_degrades_unknown_assumption() {
    // Use an uninterpreted function — the evaluator cannot resolve it without
    // a UF model, so the assumption evaluates to Unknown and degrades to Unknown.
    let mut executor = Executor::new();
    let hello = executor.ctx.terms.mk_string("hello".to_string());
    let uf_app =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("my_uf_predicate"), vec![hello], Sort::Bool);

    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let result = executor
        .finalize_sat_assumption_validation(&[uf_app])
        .expect("unknown assumption evaluability should degrade to Unknown");

    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(executor.last_result, Some(SolveResult::Unknown));
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::Incomplete)
    );
}

#[test]
fn test_finalize_sat_assumption_validation_degrades_unknown_bv_with_uf_subterms() {
    // Keep fail-closed behavior consistent with assertion validation:
    // bv comparison assumptions with UF arguments must not be skipped.
    let mut executor = Executor::new();
    let u = executor
        .ctx
        .terms
        .mk_var("u", Sort::Uninterpreted("U".to_string()));
    let f_u = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![u], Sort::bitvec(8));
    let g_u = executor
        .ctx
        .terms
        .mk_app(Symbol::named("g"), vec![u], Sort::bitvec(8));
    let bvult = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvult"), vec![f_u, g_u], Sort::Bool);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let result = executor
        .finalize_sat_assumption_validation(&[bvult])
        .expect("UF-containing BV assumption should degrade to Unknown");

    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(executor.last_result, Some(SolveResult::Unknown));
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::Incomplete)
    );
}

#[test]
fn test_finalize_sat_assumption_validation_degrades_array_false_assumption() {
    let mut executor = Executor::new();
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));
    let one = executor.ctx.terms.mk_int(BigInt::from(1));
    let const_array = executor.ctx.terms.mk_app(
        Symbol::named("const-array"),
        vec![zero],
        Sort::array(Sort::Int, Sort::Int),
    );
    let stored = executor.ctx.terms.mk_app(
        Symbol::named("store"),
        vec![const_array, zero, one],
        Sort::array(Sort::Int, Sort::Int),
    );
    let selected =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), vec![stored, zero], Sort::Int);
    let assumption =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("<"), vec![selected, zero], Sort::Bool);
    assert!(
        executor.contains_array_term(assumption),
        "assumption must retain array structure"
    );

    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model_with_sat_assignments(&[(assumption, true)]));

    let result = executor
        .finalize_sat_assumption_validation(&[assumption])
        .expect("array false assumption should degrade to Unknown");

    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(executor.last_result, Some(SolveResult::Unknown));
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::Incomplete)
    );
}

// ==========================================================================
// Cross-type equality: Rational vs BitVec (#5356)
// ==========================================================================

#[test]
fn test_evaluate_equality_rational_vs_bitvec_matching_values() {
    // (#5356) When the evaluator produces Rational for one side and BitVec
    // for the other (e.g., DT+BV combined theories, int2bv boundaries),
    // the equality should compare numerically instead of returning Unknown.
    let mut executor = Executor::new();
    // Use mk_app to create a raw equality that bypasses sort checks.
    // In practice, this arises when internal terms have mismatched
    // evaluator types (e.g., LIA model provides Int value for a term
    // that appears in a BV equality context).
    let int_const = executor.ctx.terms.mk_int(BigInt::from(42));
    let bv_const = executor.ctx.terms.mk_bitvec(BigInt::from(42), 32);
    let eq = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![int_const, bv_const], Sort::Bool);

    let model = empty_model();
    // Int constant evaluates to Rational(42), BV constant evaluates to BitVec(42, 32).
    // The cross-type handler should compare numerically: 42 == 42 → true.
    assert_eq!(
        executor.evaluate_term(&model, eq),
        EvalValue::Bool(true),
        "Rational(42) == BitVec(42, 32) should be true"
    );
}

#[test]
fn test_evaluate_equality_rational_vs_bitvec_different_values() {
    let mut executor = Executor::new();
    let int_const = executor.ctx.terms.mk_int(BigInt::from(7));
    let bv_const = executor.ctx.terms.mk_bitvec(BigInt::from(8), 8);
    let eq = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![int_const, bv_const], Sort::Bool);

    let model = empty_model();
    assert_eq!(
        executor.evaluate_term(&model, eq),
        EvalValue::Bool(false),
        "Rational(7) == BitVec(8, 8) should be false"
    );
}

#[test]
fn test_evaluate_equality_bitvec_vs_rational_symmetric() {
    // Same as above but reversed order — (BitVec, Rational) should also work.
    let mut executor = Executor::new();
    let bv_const = executor.ctx.terms.mk_bitvec(BigInt::from(100), 16);
    let int_const = executor.ctx.terms.mk_int(BigInt::from(100));
    let eq = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![bv_const, int_const], Sort::Bool);

    let model = empty_model();
    assert_eq!(
        executor.evaluate_term(&model, eq),
        EvalValue::Bool(true),
        "BitVec(100, 16) == Rational(100) should be true"
    );
}

// ==========================================================================
// BV select fallback: store chain with UF indices (#8510)
// ==========================================================================

/// Test that evaluate_select falls back to the BV model when the array model
/// has no entry for a base array + index combination, but a matching
/// `select(base_array, idx)` term exists in the BV model.
#[test]
fn test_bv_select_fallback_resolves_missing_array_model_entry_8510() {
    use ay_arrays::ArrayInterpretation;

    let mut executor = Executor::new();
    let arr_sort = Sort::array(Sort::bitvec(8), Sort::bitvec(8));
    let arr = executor.ctx.terms.mk_var("arr", arr_sort);
    let idx = executor.ctx.terms.mk_var("idx", Sort::bitvec(8));

    // Create select(arr, idx)
    let sel = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![arr, idx], Sort::bitvec(8));

    // BV model has values for idx and sel
    let mut bv_values = HashMap::default();
    bv_values.insert(idx, BigInt::from(0x05u8));
    bv_values.insert(sel, BigInt::from(0x42u8)); // select(arr, #x05) = #x42

    // Array model exists but has NO entry for arr at index #x05.
    // This simulates the case where extract_array_model_from_bv_model
    // didn't populate the entry (e.g., because the select was through a store chain).
    let mut array_values = HashMap::default();
    array_values.insert(
        arr,
        ArrayInterpretation {
            index_sort: Some(Sort::bitvec(8)),
            element_sort: Some(Sort::bitvec(8)),
            default: None,
            stores: vec![], // Empty: no known index-value pairs
        },
    );

    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    model.array_model = Some(ArrayModel {
        array_values,
        ..Default::default()
    });

    // Without the BV select fallback, this would return Unknown
    // because lookup_array_model finds no entry for arr at index #x05.
    // With the fallback, it finds select(arr, idx) in the BV model
    // where idx evaluates to #x05, and returns #x42.
    assert_eq!(
        executor.evaluate_term(&model, sel),
        EvalValue::BitVec {
            value: BigInt::from(0x42u8),
            width: 8,
        },
        "BV select fallback should resolve select(arr, #x05) = #x42"
    );
}

/// Test that contradictory exact bit-blasted select terms and array-model
/// completion defaults fail closed, while explicit store entries stay
/// authoritative.
#[test]
fn test_bv_exact_select_conflicting_default_is_unknown_11936() {
    use ay_arrays::ArrayInterpretation;

    let mut executor = Executor::new();
    let arr_sort = Sort::array(Sort::bitvec(8), Sort::bitvec(8));
    let arr = executor.ctx.terms.mk_var("arr", arr_sort);
    let idx = executor.ctx.terms.mk_var("idx", Sort::bitvec(8));
    let sel = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![arr, idx], Sort::bitvec(8));

    let mut bv_values = HashMap::default();
    bv_values.insert(idx, BigInt::from(0x05u8));
    bv_values.insert(sel, BigInt::from(0x42u8));

    let mut array_values = HashMap::default();
    array_values.insert(
        arr,
        ArrayInterpretation {
            index_sort: Some(Sort::bitvec(8)),
            element_sort: Some(Sort::bitvec(8)),
            default: Some("#x00".to_string()),
            stores: vec![],
        },
    );

    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    model.array_model = Some(ArrayModel {
        array_values,
        ..Default::default()
    });

    assert_eq!(
        executor.evaluate_term(&model, sel),
        EvalValue::Unknown,
        "conflicting exact select and array completion default must fail closed"
    );

    model
        .array_model
        .as_mut()
        .unwrap()
        .array_values
        .get_mut(&arr)
        .unwrap()
        .stores
        .push(("#x05".to_string(), "#xAA".to_string()));

    assert_eq!(
        executor.evaluate_term(&model, sel),
        EvalValue::BitVec {
            value: BigInt::from(0xAAu8),
            width: 8,
        },
        "explicit array-model store entries remain authoritative"
    );
}

#[test]
fn test_bv_backed_array_equality_partial_mismatch_is_unknown() {
    use ay_arrays::ArrayInterpretation;

    let mut executor = Executor::new();
    let arr_sort = Sort::array(Sort::bitvec(32), Sort::bitvec(8));
    let array_q3 = executor.ctx.terms.mk_var("array_Q_3", arr_sort.clone());
    let array_q4 = executor.ctx.terms.mk_var("array_Q_4", arr_sort.clone());
    let index = executor.ctx.terms.mk_bitvec(BigInt::from(3u8), 32);
    let value = executor.ctx.terms.mk_bitvec(BigInt::from(0x12u8), 8);
    let stored = executor.ctx.terms.mk_app(
        Symbol::named("store"),
        vec![array_q3, index, value],
        arr_sort,
    );
    let eq = executor.ctx.terms.mk_eq(array_q4, stored);

    let mut array_values = HashMap::default();
    array_values.insert(
        array_q3,
        ArrayInterpretation {
            index_sort: Some(Sort::bitvec(32)),
            element_sort: Some(Sort::bitvec(8)),
            default: Some("#x00".to_string()),
            stores: vec![],
        },
    );
    array_values.insert(
        array_q4,
        ArrayInterpretation {
            index_sort: Some(Sort::bitvec(32)),
            element_sort: Some(Sort::bitvec(8)),
            default: Some("#x00".to_string()),
            stores: vec![],
        },
    );

    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: HashMap::default(),
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    model.array_model = Some(ArrayModel {
        array_values,
        ..Default::default()
    });

    assert_eq!(executor.evaluate_term(&model, eq), EvalValue::Unknown);
}

#[test]
fn test_array_equality_partial_mismatch_without_bv_model_is_false() {
    use ay_arrays::ArrayInterpretation;

    let mut executor = Executor::new();
    let arr_sort = Sort::array(Sort::bitvec(32), Sort::bitvec(8));
    let array_q3 = executor.ctx.terms.mk_var("array_Q_3", arr_sort.clone());
    let array_q4 = executor.ctx.terms.mk_var("array_Q_4", arr_sort.clone());
    let index = executor.ctx.terms.mk_bitvec(BigInt::from(3u8), 32);
    let value = executor.ctx.terms.mk_bitvec(BigInt::from(0x12u8), 8);
    let stored = executor.ctx.terms.mk_app(
        Symbol::named("store"),
        vec![array_q3, index, value],
        arr_sort,
    );
    let eq = executor.ctx.terms.mk_eq(array_q4, stored);

    let mut array_values = HashMap::default();
    array_values.insert(
        array_q3,
        ArrayInterpretation {
            index_sort: Some(Sort::bitvec(32)),
            element_sort: Some(Sort::bitvec(8)),
            default: Some("#x00".to_string()),
            stores: vec![],
        },
    );
    array_values.insert(
        array_q4,
        ArrayInterpretation {
            index_sort: Some(Sort::bitvec(32)),
            element_sort: Some(Sort::bitvec(8)),
            default: Some("#x00".to_string()),
            stores: vec![],
        },
    );

    let mut model = empty_model();
    model.array_model = Some(ArrayModel {
        array_values,
        ..Default::default()
    });

    assert_eq!(executor.evaluate_term(&model, eq), EvalValue::Bool(false));
}

/// Test that evaluate_select with a store chain plus BV fallback
/// correctly handles: select(store(arr, (f x), v), (g y)) where
/// (f x) != (g y), requiring fallback to the base array via BV model.
#[test]
fn test_bv_select_fallback_through_store_chain_uf_indices_8510() {
    use ay_arrays::ArrayInterpretation;

    let mut executor = Executor::new();
    let arr_sort = Sort::array(Sort::bitvec(8), Sort::bitvec(8));
    let arr = executor.ctx.terms.mk_var("arr", arr_sort.clone());
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(8));

    // UF applications: f(x) and g(y)
    let f_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], Sort::bitvec(8));
    let g_y = executor
        .ctx
        .terms
        .mk_app(Symbol::named("g"), vec![y], Sort::bitvec(8));

    // Build store(arr, f(x), #xAA)
    let store_val_term = executor.ctx.terms.mk_bitvec(BigInt::from(0xAAu8), 8);
    let store_term = executor.ctx.terms.mk_app(
        Symbol::named("store"),
        vec![arr, f_x, store_val_term],
        arr_sort,
    );

    // Build select(store(arr, f(x), #xAA), g(y))
    let sel = executor.ctx.terms.mk_app(
        Symbol::named("select"),
        vec![store_term, g_y],
        Sort::bitvec(8),
    );

    // Also create a direct select(arr, g_y) term in the BV model
    let direct_sel =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), vec![arr, g_y], Sort::bitvec(8));

    // BV model: f(x) = #x05, g(y) = #x03 (different indices)
    // select(arr, g(y)) = #xBB in BV model
    let mut bv_values = HashMap::default();
    bv_values.insert(x, BigInt::from(0x01u8));
    bv_values.insert(y, BigInt::from(0x02u8));
    bv_values.insert(f_x, BigInt::from(0x05u8));
    bv_values.insert(g_y, BigInt::from(0x03u8));
    bv_values.insert(direct_sel, BigInt::from(0xBBu8)); // select(arr, #x03) = #xBB

    // Array model with NO entry for arr (empty stores)
    let mut array_values = HashMap::default();
    array_values.insert(
        arr,
        ArrayInterpretation {
            index_sort: Some(Sort::bitvec(8)),
            element_sort: Some(Sort::bitvec(8)),
            default: None,
            stores: vec![],
        },
    );

    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    model.array_model = Some(ArrayModel {
        array_values,
        ..Default::default()
    });

    // Evaluation: select(store(arr, f(x), #xAA), g(y))
    // 1. Walk store chain: f(x) = #x05, g(y) = #x03 -> different indices
    // 2. Peel store, reach base array arr
    // 3. lookup_array_model(arr, #x03) -> Unknown (empty stores)
    // 4. BV select fallback: find select(arr, g(y)) where g(y) = #x03 -> #xBB
    assert_eq!(
        executor.evaluate_term(&model, sel),
        EvalValue::BitVec {
            value: BigInt::from(0xBBu8),
            width: 8,
        },
        "Store chain with different UF indices should fall back to BV model for base array"
    );
}

/// Test that the BV select fallback does NOT override a store-chain hit.
/// When the store index matches the select index, the store value should
/// be returned, NOT the BV fallback value.
#[test]
fn test_bv_select_fallback_does_not_override_store_hit_8510() {
    use ay_arrays::ArrayInterpretation;

    let mut executor = Executor::new();
    let arr_sort = Sort::array(Sort::bitvec(8), Sort::bitvec(8));
    let arr = executor.ctx.terms.mk_var("arr", arr_sort.clone());
    let idx = executor.ctx.terms.mk_var("idx", Sort::bitvec(8));

    let store_val = executor.ctx.terms.mk_bitvec(BigInt::from(0xAAu8), 8);

    // Build store(arr, idx, #xAA)
    let store_term =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("store"), vec![arr, idx, store_val], arr_sort);

    // Build select(store(arr, idx, #xAA), idx) -- same index, should return #xAA
    let sel = executor.ctx.terms.mk_app(
        Symbol::named("select"),
        vec![store_term, idx],
        Sort::bitvec(8),
    );

    // BV model: idx = #x05, sel (in BV model) = #xBB (hypothetically different)
    // But the store-chain hit should take precedence.
    let mut bv_values = HashMap::default();
    bv_values.insert(idx, BigInt::from(0x05u8));
    bv_values.insert(sel, BigInt::from(0xBBu8));

    let mut array_values = HashMap::default();
    array_values.insert(
        arr,
        ArrayInterpretation {
            index_sort: Some(Sort::bitvec(8)),
            element_sort: Some(Sort::bitvec(8)),
            default: None,
            stores: vec![],
        },
    );

    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    model.array_model = Some(ArrayModel {
        array_values,
        ..Default::default()
    });

    // Store-chain hit: idx = idx, so return store value #xAA
    assert_eq!(
        executor.evaluate_term(&model, sel),
        EvalValue::BitVec {
            value: BigInt::from(0xAAu8),
            width: 8,
        },
        "Store-chain index match should return store value, not BV fallback"
    );
}

/// Test that evaluation of an assertion involving select through store
/// with UF index evaluates to Bool(true) when the model is correct,
/// instead of Unknown that triggers delegated verification.
#[test]
fn test_bv_array_assertion_evaluates_true_not_unknown_8510() {
    let mut executor = Executor::new();
    let arr_sort = Sort::array(Sort::bitvec(8), Sort::bitvec(8));
    let arr = executor.ctx.terms.mk_var("arr", arr_sort.clone());
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));

    // UF application f(x)
    let f_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], Sort::bitvec(8));

    let store_val = executor.ctx.terms.mk_bitvec(BigInt::from(0x42u8), 8);
    let expected_val = executor.ctx.terms.mk_bitvec(BigInt::from(0x42u8), 8);

    // store(arr, f(x), #x42)
    let store_term =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("store"), vec![arr, f_x, store_val], arr_sort);

    // select(store(arr, f(x), #x42), f(x))
    let sel = executor.ctx.terms.mk_app(
        Symbol::named("select"),
        vec![store_term, f_x],
        Sort::bitvec(8),
    );

    // (= (select (store arr (f x) #x42) (f x)) #x42)
    let assertion = executor.ctx.terms.mk_eq(sel, expected_val);

    // BV model: x = #x01, f(x) = #x05
    let mut bv_values = HashMap::default();
    bv_values.insert(x, BigInt::from(0x01u8));
    bv_values.insert(f_x, BigInt::from(0x05u8));

    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    // No array model needed -- the store chain walk resolves directly.

    // The evaluator should:
    // 1. Evaluate select(store(arr, f(x), #x42), f(x))
    // 2. Walk store chain: f(x) = #x05 as store index, f(x) = #x05 as select index -> match!
    // 3. Return #x42
    // 4. Compare #x42 == #x42 -> true
    assert_eq!(
        executor.evaluate_term(&model, assertion),
        EvalValue::Bool(true),
        "Assertion (= (select (store arr (f x) #x42) (f x)) #x42) should evaluate to true"
    );
}

/// Test BV select fallback with Bool-sorted array element (#6047).
#[test]
fn test_bv_select_fallback_bool_element_8510() {
    use ay_arrays::ArrayInterpretation;

    let mut executor = Executor::new();
    let arr_sort = Sort::array(Sort::bitvec(8), Sort::Bool);
    let arr = executor.ctx.terms.mk_var("arr", arr_sort);
    let idx = executor.ctx.terms.mk_var("idx", Sort::bitvec(8));

    // select(arr, idx) -> Bool
    let sel = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![arr, idx], Sort::Bool);

    // BV model: idx = #x03
    let mut bv_values = HashMap::default();
    bv_values.insert(idx, BigInt::from(0x03u8));

    // Bool override: select(arr, idx) = true
    let mut bool_overrides = HashMap::default();
    bool_overrides.insert(sel, true);

    // Array model with no entries for arr
    let mut array_values = HashMap::default();
    array_values.insert(
        arr,
        ArrayInterpretation {
            index_sort: Some(Sort::bitvec(8)),
            element_sort: Some(Sort::Bool),
            default: None,
            stores: vec![],
        },
    );

    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides,
    });
    model.array_model = Some(ArrayModel {
        array_values,
        ..Default::default()
    });

    // Without BV fallback: lookup_array_model returns Unknown (no stores).
    // With BV fallback: finds select(arr, idx) in bool_overrides -> true.
    assert_eq!(
        executor.evaluate_term(&model, sel),
        EvalValue::Bool(true),
        "BV select fallback should resolve Bool-sorted array element"
    );
}

// ==========================================================================
// bv2nat companion-bridge evaluation (#B2)
//
// `(= L (bv2nat k))` is the Route-A array-length companion: `L` an Int var,
// `k` a BitVec. When `k` occurs only inside `bv2nat(k)` the BV theory never
// produces a value for it (no `bv_model`), so the arithmetic solver treats the
// Int-sorted `(bv2nat k)` term as opaque and assigns it directly. These tests
// pin the SOUND behaviour: definite evaluation from the recoverable value with
// an exact unsigned-nat semantics and a `[0, 2^w)` realizability guard.
// ==========================================================================

// (c) Concrete bv2nat of a literal bitvector computes the exact unsigned value.
#[test]
fn test_bv2nat_concrete_unsigned_value() {
    let mut ex = Executor::new();
    let c05 = ex.ctx.terms.mk_bitvec(BigInt::from(5), 8);
    let cff = ex.ctx.terms.mk_bitvec(BigInt::from(255), 8);
    let b05 = ex.ctx.terms.mk_bv2nat(c05);
    let bff = ex.ctx.terms.mk_bv2nat(cff);
    let model = empty_model();
    assert_eq!(
        ex.evaluate_term(&model, b05),
        EvalValue::Rational(BigRational::from(BigInt::from(5))),
        "bv2nat(#x05:BV8) must be 5"
    );
    assert_eq!(
        ex.evaluate_term(&model, bff),
        EvalValue::Rational(BigRational::from(BigInt::from(255))),
        "bv2nat(#xff:BV8) must be 255 (unsigned, no sign error)"
    );
}

// bv2nat of a BV variable resolved through a BV model computes the exact value.
#[test]
fn test_bv2nat_from_bv_model_value() {
    let mut ex = Executor::new();
    let k = ex.ctx.terms.mk_var("k", Sort::bitvec(8));
    let b2n = ex.ctx.terms.mk_bv2nat(k);
    let mut bv = HashMap::default();
    bv.insert(k, BigInt::from(0xFF)); // 255 unsigned, -1 signed: must be 255
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    assert_eq!(
        ex.evaluate_term(&model, b2n),
        EvalValue::Rational(BigRational::from(BigInt::from(255))),
        "bv2nat(k) with k=0xFF must be the UNSIGNED value 255"
    );
}

// (b) DECISIVE: genuine SAT companion with NO bv_model. `k` is unconstrained
// except through `(bv2nat k)`, which the arithmetic solver assigned as an
// opaque Int. The evaluator must recover that assignment (range-checked) so the
// companion evaluates DEFINITELY — closing the Option-A over-rejection that
// dropped this genuine SAT model.
#[test]
fn test_bv2nat_companion_genuine_sat_validates_no_bv_model() {
    let mut ex = Executor::new();
    let k = ex.ctx.terms.mk_var("k", Sort::bitvec(8));
    let l = ex.ctx.terms.mk_var("L", Sort::Int);
    let b2n = ex.ctx.terms.mk_bv2nat(k);
    let eq = ex.ctx.terms.mk_eq_coerce_no_ite_expand(l, b2n);
    ex.ctx.assertions.push(eq);

    let mut lia = HashMap::default();
    lia.insert(l, BigInt::from(5));
    lia.insert(b2n, BigInt::from(5)); // opaque Int assignment for (bv2nat k)
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia });

    // Eval is DEFINITE (not Unknown) and equal to the opaque assignment.
    assert_eq!(
        ex.evaluate_term(&model, b2n),
        EvalValue::Rational(BigRational::from(BigInt::from(5))),
        "bv2nat(k) must recover the in-range opaque Int assignment (5)"
    );
    assert_eq!(
        ex.evaluate_term(&model, eq),
        EvalValue::Bool(true),
        "companion (= L (bv2nat k)) with L == 5 == bv2nat(k) must be true"
    );

    ex.last_result = Some(SolveResult::Sat);
    ex.last_model = Some(model);
    let stats = ex
        .validate_model()
        .expect("genuine SAT companion must validate (no over-rejection)");
    assert!(
        stats.checked >= 1,
        "companion must be independently checked"
    );
}

// (b') Genuine SAT companion WITH a bv_model holding k's value — the computed
// path. Must also validate.
#[test]
fn test_bv2nat_companion_genuine_sat_validates_with_bv_model() {
    let mut ex = Executor::new();
    let k = ex.ctx.terms.mk_var("k", Sort::bitvec(8));
    let l = ex.ctx.terms.mk_var("L", Sort::Int);
    let b2n = ex.ctx.terms.mk_bv2nat(k);
    let eq = ex.ctx.terms.mk_eq_coerce_no_ite_expand(l, b2n);
    ex.ctx.assertions.push(eq);

    let mut bv = HashMap::default();
    bv.insert(k, BigInt::from(5));
    let mut lia = HashMap::default();
    lia.insert(l, BigInt::from(5));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    model.lia_model = Some(LiaModel { values: lia });

    ex.last_result = Some(SolveResult::Sat);
    ex.last_model = Some(model);
    ex.validate_model()
        .expect("genuine SAT companion (computed from bv_model) must validate");
}

// (a) B2 INVALID: L decoupled from k's computed value (bv_model present).
// `(= L (bv2nat k))` evaluates DEFINITELY false -> validation rejects.
#[test]
fn test_bv2nat_companion_decoupled_rejected_with_bv_model() {
    let mut ex = Executor::new();
    let k = ex.ctx.terms.mk_var("k", Sort::bitvec(8));
    let l = ex.ctx.terms.mk_var("L", Sort::Int);
    let b2n = ex.ctx.terms.mk_bv2nat(k);
    let eq = ex.ctx.terms.mk_eq_coerce_no_ite_expand(l, b2n);
    ex.ctx.assertions.push(eq);

    let mut bv = HashMap::default();
    bv.insert(k, BigInt::from(5));
    let mut lia = HashMap::default();
    lia.insert(l, BigInt::from(7)); // decoupled: L != bv2nat(k)=5
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    model.lia_model = Some(LiaModel { values: lia });

    ex.last_result = Some(SolveResult::Sat);
    ex.last_model = Some(model);
    let err = ex
        .validate_model()
        .expect_err("decoupled companion must be rejected");
    assert!(
        format!("{err}").contains("violated") || format!("{err}").contains("false"),
        "expected a violation, got: {err}"
    );
}

// (d) Model violating the companion in the NO-bv_model path: L is decoupled
// from the opaque (bv2nat k) Int assignment. The companion evaluates to a
// definite Bool(false) -> rejected (never a spurious accept).
#[test]
fn test_bv2nat_companion_decoupled_rejected_no_bv_model() {
    let mut ex = Executor::new();
    let k = ex.ctx.terms.mk_var("k", Sort::bitvec(8));
    let l = ex.ctx.terms.mk_var("L", Sort::Int);
    let b2n = ex.ctx.terms.mk_bv2nat(k);
    let eq = ex.ctx.terms.mk_eq_coerce_no_ite_expand(l, b2n);
    ex.ctx.assertions.push(eq);

    let mut lia = HashMap::default();
    lia.insert(l, BigInt::from(7));
    lia.insert(b2n, BigInt::from(5)); // L=7 != bv2nat(k)=5
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia });

    assert_eq!(
        ex.evaluate_term(&model, eq),
        EvalValue::Bool(false),
        "decoupled companion must evaluate to a definite false"
    );
    ex.last_result = Some(SolveResult::Sat);
    ex.last_model = Some(model);
    ex.validate_model()
        .expect_err("decoupled no-bv_model companion must be rejected");
}

// SOUNDNESS GUARD: an (impossible) out-of-range opaque assignment for
// (bv2nat k) — v >= 2^w — is NOT used (it is not realizable by any width-w
// bitvector). Evaluation stays Unknown rather than fabricating an invalid value.
#[test]
fn test_bv2nat_out_of_range_opaque_value_rejected() {
    let mut ex = Executor::new();
    let k = ex.ctx.terms.mk_var("k", Sort::bitvec(8));
    let b2n = ex.ctx.terms.mk_bv2nat(k);
    let mut lia = HashMap::default();
    lia.insert(b2n, BigInt::from(300)); // 300 >= 2^8 = 256: not a valid bv2nat
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia });
    assert_eq!(
        ex.evaluate_term(&model, b2n),
        EvalValue::Unknown,
        "out-of-range opaque bv2nat assignment must not be accepted"
    );
}

// SOUNDNESS GATE: the opaque-Int fallback fires ONLY when there is no bv_model.
// With a bv_model present (even if `k` is absent and defaults to 0), the
// computed path is authoritative and the LIA opaque value is NOT consulted.
#[test]
fn test_bv2nat_lia_fallback_gated_on_absent_bv_model() {
    let mut ex = Executor::new();
    let k = ex.ctx.terms.mk_var("k", Sort::bitvec(8));
    let b2n = ex.ctx.terms.mk_bv2nat(k);
    // bv_model present but missing `k` -> evaluate_var(k) defaults to BitVec(0).
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: HashMap::default(),
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    // A (would-be) opaque LIA assignment that must be IGNORED because a BV model exists.
    let mut lia = HashMap::default();
    lia.insert(b2n, BigInt::from(9));
    model.lia_model = Some(LiaModel { values: lia });
    assert_eq!(
        ex.evaluate_term(&model, b2n),
        EvalValue::Rational(BigRational::from(BigInt::zero())),
        "with a bv_model present, bv2nat uses the computed BV value (0 default), not the LIA opaque value"
    );
}
