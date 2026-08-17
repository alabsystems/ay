// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! evaluate_term tests: basic boolean variables, constants, and variable lookup
//! from theory models (LIA, LRA, BV, strings, EUF).

use super::*;

#[test]
fn test_evaluate_term_bool_var_from_sat_model() {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("a", Sort::Bool);

    let model = model_with_sat_assignments(&[(a, true)]);
    assert_eq!(executor.evaluate_term(&model, a), EvalValue::Bool(true));
}

#[test]
fn test_evaluate_term_bool_var_unknown_when_unassigned() {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("a", Sort::Bool);

    let model = empty_model();
    assert_eq!(executor.evaluate_term(&model, a), EvalValue::Unknown);
}

#[test]
fn test_evaluate_term_unknown_bool_app_is_unknown_unless_in_sat_model() {
    let mut executor = Executor::new();
    let p = executor
        .ctx
        .terms
        .mk_app(Symbol::named("p"), vec![], Sort::Bool);

    let model = empty_model();
    assert_eq!(executor.evaluate_term(&model, p), EvalValue::Unknown);

    let model = model_with_sat_assignments(&[(p, true)]);
    assert_eq!(executor.evaluate_term(&model, p), EvalValue::Bool(true));
}

#[test]
fn test_evaluate_term_bool_connectives_and_ite() {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("a", Sort::Bool);
    let b = executor.ctx.terms.mk_var("b", Sort::Bool);
    let c = executor.ctx.terms.mk_var("c", Sort::Bool);

    let not_b = executor.ctx.terms.mk_not(b);
    let a_and_not_b = executor.ctx.terms.mk_and(vec![a, not_b]);
    let ite = executor.ctx.terms.mk_ite(c, a, b);

    let model = model_with_sat_assignments(&[(a, true), (b, false), (c, true)]);
    assert_eq!(
        executor.evaluate_term(&model, a_and_not_b),
        EvalValue::Bool(true)
    );
    assert_eq!(executor.evaluate_term(&model, ite), EvalValue::Bool(true));

    let model = model_with_sat_assignments(&[(a, false), (b, true), (c, false)]);
    assert_eq!(
        executor.evaluate_term(&model, a_and_not_b),
        EvalValue::Bool(false)
    );
    assert_eq!(executor.evaluate_term(&model, ite), EvalValue::Bool(true));
}

#[test]
fn test_evaluate_term_int_arithmetic_comparison_and_division_by_zero() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let y = executor.ctx.terms.mk_var("y", Sort::Int);

    let one_int = executor.ctx.terms.mk_int(BigInt::from(1));
    let sum = executor.ctx.terms.mk_add(vec![x, y, one_int]);
    let lt = executor.ctx.terms.mk_lt(x, y);

    let one_real = executor
        .ctx
        .terms
        .mk_rational(BigRational::from(BigInt::from(1)));
    let zero_real = executor.ctx.terms.mk_rational(BigRational::zero());
    let div_by_zero = executor.ctx.terms.mk_div(one_real, zero_real);

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(3));
    lia_values.insert(y, BigInt::from(4));

    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });

    assert_eq!(
        executor.evaluate_term(&model, sum),
        EvalValue::Rational(BigRational::from(BigInt::from(8)))
    );
    assert_eq!(executor.evaluate_term(&model, lt), EvalValue::Bool(true));
    assert_eq!(
        executor.evaluate_term(&model, div_by_zero),
        EvalValue::Unknown
    );
}

// ==========================================================================
// evaluate_term: constant evaluation tests
// ==========================================================================

#[test]
fn test_evaluate_term_const_bool() {
    let mut executor = Executor::new();
    let t = executor.ctx.terms.mk_bool(true);
    let f = executor.ctx.terms.mk_bool(false);

    let model = empty_model();
    assert_eq!(executor.evaluate_term(&model, t), EvalValue::Bool(true));
    assert_eq!(executor.evaluate_term(&model, f), EvalValue::Bool(false));
}

#[test]
fn test_evaluate_term_const_int() {
    let mut executor = Executor::new();
    let pos = executor.ctx.terms.mk_int(BigInt::from(42));
    let neg = executor.ctx.terms.mk_int(BigInt::from(-100));
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));

    let model = empty_model();
    assert_eq!(
        executor.evaluate_term(&model, pos),
        EvalValue::Rational(BigRational::from(BigInt::from(42)))
    );
    assert_eq!(
        executor.evaluate_term(&model, neg),
        EvalValue::Rational(BigRational::from(BigInt::from(-100)))
    );
    assert_eq!(
        executor.evaluate_term(&model, zero),
        EvalValue::Rational(BigRational::zero())
    );
}

#[test]
fn test_evaluate_term_const_rational() {
    let mut executor = Executor::new();
    let half = BigRational::new(BigInt::from(1), BigInt::from(2));
    let neg_third = BigRational::new(BigInt::from(-1), BigInt::from(3));
    let rat1 = executor.ctx.terms.mk_rational(half.clone());
    let rat2 = executor.ctx.terms.mk_rational(neg_third.clone());

    let model = empty_model();
    assert_eq!(
        executor.evaluate_term(&model, rat1),
        EvalValue::Rational(half)
    );
    assert_eq!(
        executor.evaluate_term(&model, rat2),
        EvalValue::Rational(neg_third)
    );
}

#[test]
fn test_evaluate_term_const_bitvec() {
    let mut executor = Executor::new();
    let bv8 = executor.ctx.terms.mk_bitvec(BigInt::from(0xFF), 8);
    let bv32 = executor
        .ctx
        .terms
        .mk_bitvec(BigInt::from(0xDEADBEEFu32), 32);
    let bv1 = executor.ctx.terms.mk_bitvec(BigInt::from(1), 1);

    let model = empty_model();
    assert_eq!(
        executor.evaluate_term(&model, bv8),
        EvalValue::BitVec {
            value: BigInt::from(0xFF),
            width: 8
        }
    );
    assert_eq!(
        executor.evaluate_term(&model, bv32),
        EvalValue::BitVec {
            value: BigInt::from(0xDEADBEEFu32),
            width: 32
        }
    );
    assert_eq!(
        executor.evaluate_term(&model, bv1),
        EvalValue::BitVec {
            value: BigInt::from(1),
            width: 1
        }
    );
}

#[test]
fn test_evaluate_term_const_string() {
    let mut executor = Executor::new();
    let s1 = executor.ctx.terms.mk_string("hello world".to_string());
    let s2 = executor.ctx.terms.mk_string(String::new());
    let s3 = executor.ctx.terms.mk_string("with\nnewline".to_string());

    let model = empty_model();
    assert_eq!(
        executor.evaluate_term(&model, s1),
        EvalValue::String("hello world".to_string())
    );
    assert_eq!(
        executor.evaluate_term(&model, s2),
        EvalValue::String(String::new())
    );
    assert_eq!(
        executor.evaluate_term(&model, s3),
        EvalValue::String("with\nnewline".to_string())
    );
}

// ==========================================================================
// evaluate_term: variable lookup from theory models
// ==========================================================================

#[test]
fn test_evaluate_term_var_string_from_string_model() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::String);

    let mut string_values = HashMap::default();
    string_values.insert(x, "abc".to_string());

    let mut model = empty_model();
    model.string_model = Some(StringModel {
        values: string_values,
    });

    assert_eq!(
        executor.evaluate_term(&model, x),
        EvalValue::String("abc".to_string())
    );
}

#[test]
fn test_evaluate_term_var_string_without_assignment_is_unknown() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::String);

    let mut model = empty_model();
    model.string_model = Some(StringModel::default());

    assert_eq!(executor.evaluate_term(&model, x), EvalValue::Unknown);
}

#[test]
fn test_evaluate_term_var_int_from_lia_model() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let y = executor.ctx.terms.mk_var("y", Sort::Int);

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(42));
    lia_values.insert(y, BigInt::from(-17));

    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });

    assert_eq!(
        executor.evaluate_term(&model, x),
        EvalValue::Rational(BigRational::from(BigInt::from(42)))
    );
    assert_eq!(
        executor.evaluate_term(&model, y),
        EvalValue::Rational(BigRational::from(BigInt::from(-17)))
    );
}

#[test]
fn test_evaluate_term_var_int_fallback_to_lra_model() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);

    // No LIA model, but value exists in LRA model
    let mut lra_values = HashMap::default();
    lra_values.insert(x, BigRational::from(BigInt::from(100)));

    let mut model = empty_model();
    model.lra_model = Some(LraModel { values: lra_values });

    assert_eq!(
        executor.evaluate_term(&model, x),
        EvalValue::Rational(BigRational::from(BigInt::from(100)))
    );
}

#[test]
fn test_evaluate_term_var_int_defaults_to_zero() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);

    let model = empty_model();
    assert_eq!(
        executor.evaluate_term(&model, x),
        EvalValue::Rational(BigRational::zero())
    );
}

#[test]
fn test_evaluate_term_var_int_uses_merged_euf_value_when_arith_model_missing_term() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);

    let mut model = empty_model();
    model.lia_model = Some(LiaModel {
        values: HashMap::default(),
    });

    let mut term_values = HashMap::default();
    term_values.insert(x, "7".to_string());
    model.euf_model = Some(EufModel {
        term_values,
        ..Default::default()
    });

    assert_eq!(
        executor.evaluate_term(&model, x),
        EvalValue::Rational(BigRational::from(BigInt::from(7)))
    );
}

#[test]
fn test_evaluate_term_var_real_from_lra_model() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Real);

    let half = BigRational::new(BigInt::from(1), BigInt::from(2));
    let mut lra_values = HashMap::default();
    lra_values.insert(x, half.clone());

    let mut model = empty_model();
    model.lra_model = Some(LraModel { values: lra_values });

    assert_eq!(executor.evaluate_term(&model, x), EvalValue::Rational(half));
}

#[test]
fn test_evaluate_term_var_real_defaults_to_zero() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Real);

    let model = empty_model();
    assert_eq!(
        executor.evaluate_term(&model, x),
        EvalValue::Rational(BigRational::zero())
    );
}

#[test]
fn test_evaluate_term_var_bitvec_from_bv_model() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(32));

    let mut bv_values = HashMap::default();
    bv_values.insert(x, BigInt::from(0xAB));
    bv_values.insert(y, BigInt::from(0x12345678u32));

    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    assert_eq!(
        executor.evaluate_term(&model, x),
        EvalValue::BitVec {
            value: BigInt::from(0xAB),
            width: 8
        }
    );
    assert_eq!(
        executor.evaluate_term(&model, y),
        EvalValue::BitVec {
            value: BigInt::from(0x12345678u32),
            width: 32
        }
    );
}

#[test]
fn test_evaluate_term_var_bitvec_missing_from_model_returns_unknown() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(16));

    // An existing BV model does not prove an absent variable is free. It may
    // be a substitution key that completion still needs to recover.
    let model = bv_model(&[]);
    assert_eq!(executor.evaluate_term(&model, x), EvalValue::Unknown);
}

#[test]
fn test_evaluate_term_var_bitvec_no_bv_model_returns_unknown() {
    // When no BV model exists (AUFLIA routing), BV variables return Unknown (#5356).
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(16));

    let model = empty_model();
    assert_eq!(executor.evaluate_term(&model, x), EvalValue::Unknown);
}

#[test]
fn test_evaluate_term_var_uninterpreted_from_euf_model() {
    let mut executor = Executor::new();
    let sort = Sort::Uninterpreted("U".to_string());
    let x = executor.ctx.terms.mk_var("x", sort);

    let mut term_values = HashMap::default();
    term_values.insert(x, "@U!0".to_string());

    let euf_model = EufModel {
        term_values,
        ..Default::default()
    };

    let mut model = empty_model();
    model.euf_model = Some(euf_model);

    assert_eq!(
        executor.evaluate_term(&model, x),
        EvalValue::Element("@U!0".to_string())
    );
}

#[test]
fn test_evaluate_term_var_uninterpreted_unknown_when_not_in_model() {
    let mut executor = Executor::new();
    let sort = Sort::Uninterpreted("U".to_string());
    let x = executor.ctx.terms.mk_var("x", sort);

    let model = empty_model();
    assert_eq!(executor.evaluate_term(&model, x), EvalValue::Unknown);
}
