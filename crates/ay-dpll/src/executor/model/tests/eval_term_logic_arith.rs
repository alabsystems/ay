// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! evaluate_term tests: Boolean logic operations, equality, arithmetic,
//! integer division/modulo, and comparison operations.

use super::*;

// ==========================================================================
// evaluate_term: Boolean logic operations
// ==========================================================================

#[test]
fn test_evaluate_term_not() {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("a", Sort::Bool);
    let not_a = executor.ctx.terms.mk_not(a);

    let model_true = model_with_sat_assignments(&[(a, true)]);
    assert_eq!(
        executor.evaluate_term(&model_true, not_a),
        EvalValue::Bool(false)
    );

    let model_false = model_with_sat_assignments(&[(a, false)]);
    assert_eq!(
        executor.evaluate_term(&model_false, not_a),
        EvalValue::Bool(true)
    );
}

#[test]
fn test_evaluate_term_and_short_circuit() {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("a", Sort::Bool);
    let b = executor.ctx.terms.mk_var("b", Sort::Bool);
    let c = executor.ctx.terms.mk_var("c", Sort::Bool);
    let and_abc = executor.ctx.terms.mk_and(vec![a, b, c]);

    // All true
    let model = model_with_sat_assignments(&[(a, true), (b, true), (c, true)]);
    assert_eq!(
        executor.evaluate_term(&model, and_abc),
        EvalValue::Bool(true)
    );

    // First false - short circuits
    let model = model_with_sat_assignments(&[(a, false), (b, true), (c, true)]);
    assert_eq!(
        executor.evaluate_term(&model, and_abc),
        EvalValue::Bool(false)
    );

    // Middle false
    let model = model_with_sat_assignments(&[(a, true), (b, false), (c, true)]);
    assert_eq!(
        executor.evaluate_term(&model, and_abc),
        EvalValue::Bool(false)
    );

    // Last false
    let model = model_with_sat_assignments(&[(a, true), (b, true), (c, false)]);
    assert_eq!(
        executor.evaluate_term(&model, and_abc),
        EvalValue::Bool(false)
    );
}

#[test]
fn test_evaluate_term_or_short_circuit() {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("a", Sort::Bool);
    let b = executor.ctx.terms.mk_var("b", Sort::Bool);
    let c = executor.ctx.terms.mk_var("c", Sort::Bool);
    let or_abc = executor.ctx.terms.mk_or(vec![a, b, c]);

    // All false
    let model = model_with_sat_assignments(&[(a, false), (b, false), (c, false)]);
    assert_eq!(
        executor.evaluate_term(&model, or_abc),
        EvalValue::Bool(false)
    );

    // First true - short circuits
    let model = model_with_sat_assignments(&[(a, true), (b, false), (c, false)]);
    assert_eq!(
        executor.evaluate_term(&model, or_abc),
        EvalValue::Bool(true)
    );

    // Middle true
    let model = model_with_sat_assignments(&[(a, false), (b, true), (c, false)]);
    assert_eq!(
        executor.evaluate_term(&model, or_abc),
        EvalValue::Bool(true)
    );

    // Last true
    let model = model_with_sat_assignments(&[(a, false), (b, false), (c, true)]);
    assert_eq!(
        executor.evaluate_term(&model, or_abc),
        EvalValue::Bool(true)
    );
}

#[test]
fn test_evaluate_term_implication() {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("a", Sort::Bool);
    let b = executor.ctx.terms.mk_var("b", Sort::Bool);
    let implies = executor.ctx.terms.mk_implies(a, b);

    // false => _ is true
    let model = model_with_sat_assignments(&[(a, false), (b, false)]);
    assert_eq!(
        executor.evaluate_term(&model, implies),
        EvalValue::Bool(true)
    );

    let model = model_with_sat_assignments(&[(a, false), (b, true)]);
    assert_eq!(
        executor.evaluate_term(&model, implies),
        EvalValue::Bool(true)
    );

    // true => false is false
    let model = model_with_sat_assignments(&[(a, true), (b, false)]);
    assert_eq!(
        executor.evaluate_term(&model, implies),
        EvalValue::Bool(false)
    );

    // true => true is true
    let model = model_with_sat_assignments(&[(a, true), (b, true)]);
    assert_eq!(
        executor.evaluate_term(&model, implies),
        EvalValue::Bool(true)
    );
}

#[test]
fn test_evaluate_term_xor() {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("a", Sort::Bool);
    let b = executor.ctx.terms.mk_var("b", Sort::Bool);
    let xor = executor.ctx.terms.mk_xor(a, b);

    let model = model_with_sat_assignments(&[(a, false), (b, false)]);
    assert_eq!(executor.evaluate_term(&model, xor), EvalValue::Bool(false));

    let model = model_with_sat_assignments(&[(a, false), (b, true)]);
    assert_eq!(executor.evaluate_term(&model, xor), EvalValue::Bool(true));

    let model = model_with_sat_assignments(&[(a, true), (b, false)]);
    assert_eq!(executor.evaluate_term(&model, xor), EvalValue::Bool(true));

    let model = model_with_sat_assignments(&[(a, true), (b, true)]);
    assert_eq!(executor.evaluate_term(&model, xor), EvalValue::Bool(false));
}

#[test]
fn test_evaluate_term_ite() {
    let mut executor = Executor::new();
    let cond = executor.ctx.terms.mk_var("c", Sort::Bool);
    let then_val = executor.ctx.terms.mk_int(BigInt::from(42));
    let else_val = executor.ctx.terms.mk_int(BigInt::from(100));
    let ite = executor.ctx.terms.mk_ite(cond, then_val, else_val);

    let model_true = model_with_sat_assignments(&[(cond, true)]);
    assert_eq!(
        executor.evaluate_term(&model_true, ite),
        EvalValue::Rational(BigRational::from(BigInt::from(42)))
    );

    let model_false = model_with_sat_assignments(&[(cond, false)]);
    assert_eq!(
        executor.evaluate_term(&model_false, ite),
        EvalValue::Rational(BigRational::from(BigInt::from(100)))
    );
}

// ==========================================================================
// evaluate_term: equality and distinct
// ==========================================================================

#[test]
fn test_evaluate_term_equality_bool() {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("a", Sort::Bool);
    let b = executor.ctx.terms.mk_var("b", Sort::Bool);
    let eq = executor.ctx.terms.mk_eq(a, b);

    let model = model_with_sat_assignments(&[(a, true), (b, true)]);
    assert_eq!(executor.evaluate_term(&model, eq), EvalValue::Bool(true));

    let model = model_with_sat_assignments(&[(a, false), (b, false)]);
    assert_eq!(executor.evaluate_term(&model, eq), EvalValue::Bool(true));

    let model = model_with_sat_assignments(&[(a, true), (b, false)]);
    assert_eq!(executor.evaluate_term(&model, eq), EvalValue::Bool(false));
}

#[test]
fn test_evaluate_term_equality_int() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let y = executor.ctx.terms.mk_var("y", Sort::Int);
    let eq = executor.ctx.terms.mk_eq(x, y);

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(42));
    lia_values.insert(y, BigInt::from(42));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });
    assert_eq!(executor.evaluate_term(&model, eq), EvalValue::Bool(true));

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(42));
    lia_values.insert(y, BigInt::from(43));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });
    assert_eq!(executor.evaluate_term(&model, eq), EvalValue::Bool(false));
}

#[test]
fn test_evaluate_term_equality_bitvec() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(8));
    let eq = executor.ctx.terms.mk_eq(x, y);

    let mut bv_values = HashMap::default();
    bv_values.insert(x, BigInt::from(0xFF));
    bv_values.insert(y, BigInt::from(0xFF));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    assert_eq!(executor.evaluate_term(&model, eq), EvalValue::Bool(true));

    let mut bv_values = HashMap::default();
    bv_values.insert(x, BigInt::from(0xFF));
    bv_values.insert(y, BigInt::from(0xFE));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    assert_eq!(executor.evaluate_term(&model, eq), EvalValue::Bool(false));
}

#[test]
fn test_evaluate_term_distinct() {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("a", Sort::Int);
    let b = executor.ctx.terms.mk_var("b", Sort::Int);
    let c = executor.ctx.terms.mk_var("c", Sort::Int);
    let distinct = executor.ctx.terms.mk_distinct(vec![a, b, c]);

    // All different
    let mut lia_values = HashMap::default();
    lia_values.insert(a, BigInt::from(1));
    lia_values.insert(b, BigInt::from(2));
    lia_values.insert(c, BigInt::from(3));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });
    assert_eq!(
        executor.evaluate_term(&model, distinct),
        EvalValue::Bool(true)
    );

    // Two equal
    let mut lia_values = HashMap::default();
    lia_values.insert(a, BigInt::from(1));
    lia_values.insert(b, BigInt::from(1));
    lia_values.insert(c, BigInt::from(3));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });
    assert_eq!(
        executor.evaluate_term(&model, distinct),
        EvalValue::Bool(false)
    );
}

// ==========================================================================
// evaluate_term: arithmetic operations
// ==========================================================================

#[test]
fn test_evaluate_term_addition() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let y = executor.ctx.terms.mk_var("y", Sort::Int);
    let sum = executor.ctx.terms.mk_add(vec![x, y]);

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(10));
    lia_values.insert(y, BigInt::from(32));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });

    assert_eq!(
        executor.evaluate_term(&model, sum),
        EvalValue::Rational(BigRational::from(BigInt::from(42)))
    );
}

#[test]
fn test_evaluate_term_subtraction_binary() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let y = executor.ctx.terms.mk_var("y", Sort::Int);
    let diff = executor.ctx.terms.mk_sub(vec![x, y]);

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(100));
    lia_values.insert(y, BigInt::from(58));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });

    assert_eq!(
        executor.evaluate_term(&model, diff),
        EvalValue::Rational(BigRational::from(BigInt::from(42)))
    );
}

#[test]
fn test_evaluate_term_subtraction_unary() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let neg_x = executor.ctx.terms.mk_sub(vec![x]);

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(42));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });

    assert_eq!(
        executor.evaluate_term(&model, neg_x),
        EvalValue::Rational(BigRational::from(BigInt::from(-42)))
    );
}

#[test]
fn test_evaluate_term_multiplication() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let y = executor.ctx.terms.mk_var("y", Sort::Int);
    let prod = executor.ctx.terms.mk_mul(vec![x, y]);

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(6));
    lia_values.insert(y, BigInt::from(7));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });

    assert_eq!(
        executor.evaluate_term(&model, prod),
        EvalValue::Rational(BigRational::from(BigInt::from(42)))
    );
}

#[test]
fn test_evaluate_term_division() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Real);
    let y = executor.ctx.terms.mk_var("y", Sort::Real);
    let quot = executor.ctx.terms.mk_div(x, y);

    let mut lra_values = HashMap::default();
    lra_values.insert(x, BigRational::from(BigInt::from(84)));
    lra_values.insert(y, BigRational::from(BigInt::from(2)));
    let mut model = empty_model();
    model.lra_model = Some(LraModel { values: lra_values });

    assert_eq!(
        executor.evaluate_term(&model, quot),
        EvalValue::Rational(BigRational::from(BigInt::from(42)))
    );
}

// ==========================================================================
// evaluate_term: integer div, mod, abs
// ==========================================================================

#[test]
fn test_evaluate_term_int_div_positive() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let y = executor.ctx.terms.mk_var("y", Sort::Int);
    let div = executor
        .ctx
        .terms
        .mk_app(Symbol::named("div"), vec![x, y], Sort::Int);

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(7));
    lia_values.insert(y, BigInt::from(3));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });

    // 7 div 3 = 2 (floor(7/3) = 2)
    assert_eq!(
        executor.evaluate_term(&model, div),
        EvalValue::Rational(BigRational::from(BigInt::from(2)))
    );
}

#[test]
fn test_evaluate_term_int_div_negative_dividend() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let y = executor.ctx.terms.mk_var("y", Sort::Int);
    let div = executor
        .ctx
        .terms
        .mk_app(Symbol::named("div"), vec![x, y], Sort::Int);

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(-7));
    lia_values.insert(y, BigInt::from(3));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });

    // SMT-LIB: (-7) div 3 = -3 (floor(-7/3) = -3, NOT -2)
    // Because mod must be non-negative: -7 = (-3)*3 + 2, so 0 <= 2 < 3 ✓
    assert_eq!(
        executor.evaluate_term(&model, div),
        EvalValue::Rational(BigRational::from(BigInt::from(-3)))
    );
}

#[test]
fn test_evaluate_term_int_mod_positive() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let y = executor.ctx.terms.mk_var("y", Sort::Int);
    let modop = executor
        .ctx
        .terms
        .mk_app(Symbol::named("mod"), vec![x, y], Sort::Int);

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(7));
    lia_values.insert(y, BigInt::from(3));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });

    // 7 mod 3 = 1
    assert_eq!(
        executor.evaluate_term(&model, modop),
        EvalValue::Rational(BigRational::from(BigInt::from(1)))
    );
}

#[test]
fn test_evaluate_term_int_mod_negative_dividend() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let y = executor.ctx.terms.mk_var("y", Sort::Int);
    let modop = executor
        .ctx
        .terms
        .mk_app(Symbol::named("mod"), vec![x, y], Sort::Int);

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(-7));
    lia_values.insert(y, BigInt::from(3));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });

    // SMT-LIB: (-7) mod 3 = 2 (always non-negative)
    // -7 = (-3)*3 + 2
    assert_eq!(
        executor.evaluate_term(&model, modop),
        EvalValue::Rational(BigRational::from(BigInt::from(2)))
    );
}

#[test]
fn test_evaluate_term_int_abs() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let absop = executor
        .ctx
        .terms
        .mk_app(Symbol::named("abs"), vec![x], Sort::Int);

    // abs(-5) = 5
    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(-5));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });
    assert_eq!(
        executor.evaluate_term(&model, absop),
        EvalValue::Rational(BigRational::from(BigInt::from(5)))
    );

    // abs(3) = 3
    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(3));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });
    assert_eq!(
        executor.evaluate_term(&model, absop),
        EvalValue::Rational(BigRational::from(BigInt::from(3)))
    );

    // abs(0) = 0
    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(0));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });
    assert_eq!(
        executor.evaluate_term(&model, absop),
        EvalValue::Rational(BigRational::from(BigInt::from(0)))
    );
}

#[test]
fn test_evaluate_term_int_div_by_zero_is_unknown() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let y = executor.ctx.terms.mk_var("y", Sort::Int);
    let div = executor
        .ctx
        .terms
        .mk_app(Symbol::named("div"), vec![x, y], Sort::Int);

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(7));
    lia_values.insert(y, BigInt::from(0));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });

    assert_eq!(executor.evaluate_term(&model, div), EvalValue::Unknown);
}

// ==========================================================================
// evaluate_term: comparison operations
// ==========================================================================

#[test]
fn test_evaluate_term_less_than() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let y = executor.ctx.terms.mk_var("y", Sort::Int);
    let lt = executor.ctx.terms.mk_lt(x, y);

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(1));
    lia_values.insert(y, BigInt::from(2));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });
    assert_eq!(executor.evaluate_term(&model, lt), EvalValue::Bool(true));

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(2));
    lia_values.insert(y, BigInt::from(2));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });
    assert_eq!(executor.evaluate_term(&model, lt), EvalValue::Bool(false));

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(3));
    lia_values.insert(y, BigInt::from(2));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });
    assert_eq!(executor.evaluate_term(&model, lt), EvalValue::Bool(false));
}

#[test]
fn test_evaluate_term_less_than_or_equal() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let y = executor.ctx.terms.mk_var("y", Sort::Int);
    let le = executor.ctx.terms.mk_le(x, y);

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(1));
    lia_values.insert(y, BigInt::from(2));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });
    assert_eq!(executor.evaluate_term(&model, le), EvalValue::Bool(true));

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(2));
    lia_values.insert(y, BigInt::from(2));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });
    assert_eq!(executor.evaluate_term(&model, le), EvalValue::Bool(true));

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(3));
    lia_values.insert(y, BigInt::from(2));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });
    assert_eq!(executor.evaluate_term(&model, le), EvalValue::Bool(false));
}

#[test]
fn test_evaluate_term_greater_than() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let y = executor.ctx.terms.mk_var("y", Sort::Int);
    let gt = executor.ctx.terms.mk_gt(x, y);

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(3));
    lia_values.insert(y, BigInt::from(2));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });
    assert_eq!(executor.evaluate_term(&model, gt), EvalValue::Bool(true));

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(2));
    lia_values.insert(y, BigInt::from(2));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });
    assert_eq!(executor.evaluate_term(&model, gt), EvalValue::Bool(false));
}

#[test]
fn test_evaluate_term_greater_than_or_equal() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let y = executor.ctx.terms.mk_var("y", Sort::Int);
    let ge = executor.ctx.terms.mk_ge(x, y);

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(3));
    lia_values.insert(y, BigInt::from(2));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });
    assert_eq!(executor.evaluate_term(&model, ge), EvalValue::Bool(true));

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(2));
    lia_values.insert(y, BigInt::from(2));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });
    assert_eq!(executor.evaluate_term(&model, ge), EvalValue::Bool(true));

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(1));
    lia_values.insert(y, BigInt::from(2));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });
    assert_eq!(executor.evaluate_term(&model, ge), EvalValue::Bool(false));
}
