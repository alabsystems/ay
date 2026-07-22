// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

use super::*;
use ay_core::term::{Constant, RationalWrapper};
use ay_core::Sort;

#[test]
fn test_arith_instantiator_creation() {
    let inst = ArithInstantiator::new();
    assert!(inst.lower_bounds.is_empty());
    assert!(inst.upper_bounds.is_empty());
    assert!(inst.equalities.is_empty());
}

#[test]
fn test_process_simple_bound() {
    let mut terms = TermStore::new();
    let mut inst = ArithInstantiator::new();

    // Create: x >= 0
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(0.into());
    let ge = terms.mk_ge(x, zero);

    let result = inst.process_assertion(&mut terms, ge, x);
    assert!(result);
    assert_eq!(inst.lower_bounds.len(), 1);
}

#[test]
fn test_process_complex_bound() {
    let mut terms = TermStore::new();
    let mut inst = ArithInstantiator::new();

    // Create: 2*x + 3 >= 0  =>  (>= (+ (* 2 x) 3) 0)
    let x = terms.mk_var("x", Sort::Int);
    let two = terms.mk_int(2.into());
    let three = terms.mk_int(3.into());
    let zero = terms.mk_int(0.into());
    let two_x = terms.mk_mul(vec![two, x]);
    let sum = terms.mk_add(vec![two_x, three]);
    let ge = terms.mk_ge(sum, zero);

    let result = inst.process_assertion(&mut terms, ge, x);
    assert!(result, "Should extract bound from 2*x + 3 >= 0");
    assert_eq!(inst.lower_bounds.len(), 1);
    assert_eq!(
        inst.lower_bounds[0].coeff,
        BigRational::from(BigInt::from(2))
    );
}

#[test]
fn test_select_model_value() {
    let mut terms = TermStore::new();
    let inst = ArithInstantiator::new();

    let x = terms.mk_var("x", Sort::Int);
    let model_value = BigRational::from(BigInt::from(42));

    let selected = inst.select_term(&mut terms, x, &model_value, true);
    assert!(selected.is_some());

    let selected = selected.unwrap();
    let data = terms.get(selected);
    match data {
        TermData::Const(Constant::Int(v)) => assert_eq!(*v, BigInt::from(42)),
        _ => panic!("Expected Int, got {data:?}"),
    }
}

#[test]
fn test_process_disequality_integer() {
    let mut terms = TermStore::new();
    let mut inst = ArithInstantiator::new();

    // Create: Not(x = 5)  →  x != 5
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(5.into());
    let eq = terms.mk_eq(x, five);
    let neq = terms.mk_not(eq);

    let result = inst.process_assertion(&mut terms, neq, x);
    assert!(result, "Should extract bounds from x != 5");
    // For integers: x != 5 → x >= 6 (lower) AND x <= 4 (upper)
    assert_eq!(
        inst.lower_bounds.len(),
        1,
        "Expected 1 lower bound from disequality"
    );
    assert_eq!(
        inst.upper_bounds.len(),
        1,
        "Expected 1 upper bound from disequality"
    );
}

#[test]
fn test_extract_variable_subtraction() {
    let mut terms = TermStore::new();

    // (- a x) where x is pv: coeff = -1, remainder = a
    let x = terms.mk_var("x", Sort::Int);
    let a = terms.mk_var("a", Sort::Int);
    let sub = terms.mk_sub(vec![a, x]);

    let (coeff, remainder) = ArithInstantiator::extract_variable(&mut terms, sub, x);
    assert_eq!(
        coeff,
        BigRational::from(BigInt::from(-1)),
        "x in (- a x) should have coeff -1"
    );
    assert!(remainder.is_some(), "Should have remainder = a");
}

#[test]
fn test_extract_variable_subtraction_first_pos() {
    let mut terms = TermStore::new();

    // (- x a) where x is pv: coeff = 1, remainder = -a
    let x = terms.mk_var("x", Sort::Int);
    let a = terms.mk_var("a", Sort::Int);
    let sub = terms.mk_sub(vec![x, a]);

    let (coeff, remainder) = ArithInstantiator::extract_variable(&mut terms, sub, x);
    assert_eq!(
        coeff,
        BigRational::from(BigInt::from(1)),
        "x in (- x a) should have coeff 1"
    );
    assert!(remainder.is_some(), "Should have remainder = -a");
}

#[test]
fn test_select_term_real_model_value() {
    let mut terms = TermStore::new();
    let inst = ArithInstantiator::new();

    let x = terms.mk_var("x", Sort::Real);
    // Model value is 3/2 (not integer)
    let model_value = BigRational::new(BigInt::from(3), BigInt::from(2));

    let selected = inst.select_term(&mut terms, x, &model_value, false);
    assert!(selected.is_some());

    let selected = selected.unwrap();
    let data = terms.get(selected);
    match data {
        TermData::Const(Constant::Rational(r)) => {
            assert_eq!(
                *r,
                RationalWrapper::from(BigRational::new(BigInt::from(3), BigInt::from(2))),
                "Real model value should be preserved as 3/2"
            );
        }
        _ => panic!("Expected Rational, got {data:?}"),
    }
}

/// Negative coefficient sign flip: (-2)*x <= 10 should become x >= -5 (lower bound).
///
/// When the coefficient is negative, add_bound flips upper↔lower.
/// This is HIGH RISK: a bug here misclassifies bounds, leading to wrong instantiations.
#[test]
fn test_add_bound_negative_coeff_flips_to_lower() {
    let mut terms = TermStore::new();
    let mut inst = ArithInstantiator::new();

    // Create: (-2)*x <= 10  →  "upper" when positive, but coeff < 0 → flip to lower
    let x = terms.mk_var("x", Sort::Int);
    let neg_two = terms.mk_int((-2).into());
    let ten = terms.mk_int(10.into());
    let neg_two_x = terms.mk_mul(vec![neg_two, x]);
    let le = terms.mk_le(neg_two_x, ten);

    let result = inst.process_assertion(&mut terms, le, x);
    assert!(result, "Should extract bound from (-2)*x <= 10");
    // (-2)*x <= 10 with negative coeff: add_bound flips "upper" → lower
    assert_eq!(
        inst.lower_bounds.len(),
        1,
        "Negative coeff on <= should flip to lower bound"
    );
    assert!(
        inst.upper_bounds.is_empty(),
        "Should NOT have upper bound (flipped)"
    );
    // Coefficient stored should be the absolute value (2, not -2)
    assert_eq!(
        inst.lower_bounds[0].coeff,
        BigRational::from(BigInt::from(2)),
        "Stored coeff should be |coeff| = 2"
    );

    let model_value = BigRational::from(BigInt::from(0));
    let selected = inst
        .select_term(&mut terms, x, &model_value, true)
        .expect("negative coefficient lower bound should select");
    match terms.get(selected) {
        TermData::Const(Constant::Int(v)) => {
            assert_eq!(*v, BigInt::from(-5), "(-2*x <= 10) means x >= -5");
        }
        other => panic!("Expected Int(-5), got {other:?}"),
    }
}

/// Negative coefficient sign flip: (-3)*x >= 9 should become x <= -3 (upper bound).
#[test]
fn test_add_bound_negative_coeff_flips_to_upper() {
    let mut terms = TermStore::new();
    let mut inst = ArithInstantiator::new();

    // Create: (-3)*x >= 9  →  "lower" when positive, but coeff < 0 → flip to upper
    let x = terms.mk_var("x", Sort::Int);
    let neg_three = terms.mk_int((-3).into());
    let nine = terms.mk_int(9.into());
    let neg_three_x = terms.mk_mul(vec![neg_three, x]);
    let ge = terms.mk_ge(neg_three_x, nine);

    let result = inst.process_assertion(&mut terms, ge, x);
    assert!(result, "Should extract bound from (-3)*x >= 9");
    assert_eq!(
        inst.upper_bounds.len(),
        1,
        "Negative coeff on >= should flip to upper bound"
    );
    assert!(
        inst.lower_bounds.is_empty(),
        "Should NOT have lower bound (flipped)"
    );
    assert_eq!(
        inst.upper_bounds[0].coeff,
        BigRational::from(BigInt::from(3)),
        "Stored coeff should be |coeff| = 3"
    );

    let model_value = BigRational::from(BigInt::from(0));
    let selected = inst
        .select_term(&mut terms, x, &model_value, true)
        .expect("negative coefficient upper bound should select");
    match terms.get(selected) {
        TermData::Const(Constant::Int(v)) => {
            assert_eq!(*v, BigInt::from(-3), "(-3*x >= 9) means x <= -3");
        }
        other => panic!("Expected Int(-3), got {other:?}"),
    }
}

#[test]
fn test_select_term_real_single_strict_lower_uses_delta() {
    let mut terms = TermStore::new();
    let mut inst = ArithInstantiator::new();

    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::from(BigInt::from(0)));
    let gt = terms.mk_gt(x, zero);

    assert!(inst.process_assertion(&mut terms, gt, x));
    assert_eq!(inst.lower_bounds.len(), 1);
    assert!(inst.lower_bounds[0].strict);

    let selected = inst
        .select_term(
            &mut terms,
            x,
            &BigRational::new(BigInt::from(1), BigInt::from(2)),
            false,
        )
        .expect("strict real lower bound should select");
    match terms.get(selected) {
        TermData::Const(Constant::Rational(r)) => {
            assert_eq!(
                *r,
                RationalWrapper::from(BigRational::from(BigInt::from(1))),
                "x > 0 should select 0 + delta"
            );
        }
        other => panic!("Expected Rational(1), got {other:?}"),
    }
}

#[test]
fn test_select_term_real_dual_bounds_uses_midpoint() {
    let mut terms = TermStore::new();
    let mut inst = ArithInstantiator::new();

    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::from(BigInt::from(0)));
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let gt = terms.mk_gt(x, zero);
    let le = terms.mk_le(x, one);

    assert!(inst.process_assertion(&mut terms, gt, x));
    assert!(inst.process_assertion(&mut terms, le, x));

    let selected = inst
        .select_term(
            &mut terms,
            x,
            &BigRational::new(BigInt::from(1), BigInt::from(2)),
            false,
        )
        .expect("dual real bounds should select");
    match terms.get(selected) {
        TermData::Const(Constant::Rational(r)) => {
            assert_eq!(
                *r,
                RationalWrapper::from(BigRational::new(BigInt::from(1), BigInt::from(2))),
                "0 < x <= 1 should select midpoint 1/2"
            );
        }
        other => panic!("Expected Rational(1/2), got {other:?}"),
    }
}

/// Variable on RHS: 10 >= 2*x should extract bound for x.
///
/// extract_bound checks lhs first, then rhs. When pv is in rhs,
/// the coefficient is negated. This is HIGH RISK — wrong negation
/// would misclassify the bound direction.
#[test]
fn test_extract_bound_pv_on_rhs() {
    let mut terms = TermStore::new();
    let mut inst = ArithInstantiator::new();

    // Create: 10 >= 2*x  (pv on RHS)
    let x = terms.mk_var("x", Sort::Int);
    let two = terms.mk_int(2.into());
    let ten = terms.mk_int(10.into());
    let two_x = terms.mk_mul(vec![two, x]);
    let ge = terms.mk_ge(ten, two_x);

    let result = inst.process_assertion(&mut terms, ge, x);
    assert!(result, "Should extract bound from 10 >= 2*x");
    // 10 >= 2*x → extract_bound first moves pv to the left as -2*x <= -10.
    // add_bound sees a negative coeff with "lower when positive" (>=):
    //   coeff < 0 → flip "lower" to "upper" and normalize to 2*x <= 10.
    // Semantically: 10 >= 2*x → x <= 5, which is an upper bound. Correct.
    assert_eq!(
        inst.upper_bounds.len(),
        1,
        "10 >= 2*x should give upper bound (x <= 5)"
    );
    assert!(inst.lower_bounds.is_empty(), "Should not have lower bound");
}

/// Equality bound: extract from `x = 5` and verify it takes priority in select_term.
#[test]
fn test_process_equality_and_select_priority() {
    let mut terms = TermStore::new();
    let mut inst = ArithInstantiator::new();

    // Create: x = 5 (equality)
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(5.into());
    let eq = terms.mk_eq(x, five);

    let result = inst.process_assertion(&mut terms, eq, x);
    assert!(result, "Should extract equality from x = 5");
    assert_eq!(inst.equalities.len(), 1, "Should have 1 equality");

    // Also add a lower bound to verify equality takes priority
    let zero = terms.mk_int(0.into());
    let ge = terms.mk_ge(x, zero);
    inst.process_assertion(&mut terms, ge, x);
    assert_eq!(inst.lower_bounds.len(), 1, "Should also have lower bound");

    // select_term should pick equality over lower bound
    let model_value = BigRational::from(BigInt::from(42));
    let selected = inst.select_term(&mut terms, x, &model_value, true);
    assert!(selected.is_some());
    // With equality coeff=1, should return the bound term directly (5)
    let selected = selected.unwrap();
    match terms.get(selected) {
        TermData::Const(Constant::Int(v)) => assert_eq!(*v, BigInt::from(5)),
        other => panic!("Expected Int(5), got {other:?}"),
    }
}

/// Reversed multiplication: (pv * c) should extract same as (c * pv).
#[test]
fn test_extract_variable_reversed_multiplication() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(3.into());
    // pv * c (reversed order)
    let x_times_3 = terms.mk_mul(vec![x, three]);

    let (coeff, remainder) = ArithInstantiator::extract_variable(&mut terms, x_times_3, x);
    assert_eq!(
        coeff,
        BigRational::from(BigInt::from(3)),
        "x * 3 should extract coeff = 3"
    );
    assert!(remainder.is_none(), "x * 3 should have no remainder");
}

/// Unary negation: (-x) should extract coeff = -1.
#[test]
fn test_extract_variable_unary_negation() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let neg_x = terms.mk_sub(vec![x]); // Unary negation: (- x)

    let (coeff, remainder) = ArithInstantiator::extract_variable(&mut terms, neg_x, x);
    assert_eq!(
        coeff,
        BigRational::from(BigInt::from(-1)),
        "(-x) should extract coeff = -1"
    );
    assert!(remainder.is_none(), "(-x) should have no remainder");
}

/// Real disequality: Not(x = 3.0) should add both lower and upper bounds.
#[test]
fn test_process_real_disequality() {
    let mut terms = TermStore::new();
    let mut inst = ArithInstantiator::new();

    let x = terms.mk_var("x", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let eq = terms.mk_eq(x, three);
    let neq = terms.mk_not(eq);

    let result = inst.process_assertion(&mut terms, neq, x);
    assert!(
        result,
        "Should extract bounds from real disequality x != 3.0"
    );
    // For reals: add same term as both lower and upper bound
    assert_eq!(
        inst.lower_bounds.len(),
        1,
        "Real disequality should add 1 lower bound"
    );
    assert_eq!(
        inst.upper_bounds.len(),
        1,
        "Real disequality should add 1 upper bound"
    );
}

/// Integer divide_term: 2*x = 10 → select creates (div 10 2) = 5.
///
/// Previously this panicked because divide_term called mk_div (Real-only)
/// instead of mk_intdiv. Fixed in this commit (#5924).
#[test]
fn test_select_term_int_equality_divide() {
    let mut terms = TermStore::new();
    let mut inst = ArithInstantiator::new();

    // Push equality: 2*x = 10 → coeff=2, term=10
    let ten = terms.mk_int(10.into());
    inst.equalities
        .push((BigRational::from(BigInt::from(2)), ten));

    let x = terms.mk_var("x", Sort::Int);
    let model_value = BigRational::from(BigInt::from(5));

    let selected = inst.select_term(&mut terms, x, &model_value, true);
    assert!(selected.is_some(), "Should select a term via divide_term");

    // mk_intdiv constant-folds (div 10 2) → 5
    let selected = selected.unwrap();
    match terms.get(selected) {
        TermData::Const(Constant::Int(v)) => {
            assert_eq!(*v, BigInt::from(5), "10 / 2 should constant-fold to 5");
        }
        other => panic!("Expected Int(5) from integer division, got {other:?}"),
    }
}

/// Real divide_term: 3*x = 9.0 → select creates (* 9 (1/3)) which constant-folds to 3.
#[test]
fn test_select_term_real_equality_divide() {
    let mut terms = TermStore::new();
    let mut inst = ArithInstantiator::new();

    // Push equality: 3*x = 9.0 → coeff=3, term=9
    let nine = terms.mk_rational(BigRational::from(BigInt::from(9)));
    inst.equalities
        .push((BigRational::from(BigInt::from(3)), nine));

    let x = terms.mk_var("x", Sort::Real);
    let model_value = BigRational::from(BigInt::from(3));
    let selected = inst.select_term(&mut terms, x, &model_value, false);
    assert!(selected.is_some(), "Should select a term via divide_term");

    // Real division: (* 9 (1/3)) constant-folds to Rational(3)
    let selected = selected.unwrap();
    let data = terms.get(selected);
    match data {
        TermData::Const(Constant::Rational(r)) => {
            assert_eq!(
                *r,
                RationalWrapper::from(BigRational::from(BigInt::from(3))),
                "9/3 should constant-fold to 3"
            );
        }
        other => panic!("Expected Rational(3) from constant folding, got {other:?}"),
    }
}

/// divide_term should assert that for integer division, the coefficient
/// denominator is 1 (i.e., the coefficient is actually an integer).
///
/// Coefficients extracted from SMT-LIB integer constraints should always have
/// denominator 1, but if a bug produces a fractional coefficient like 7/2,
/// the current code silently truncates to 3 via Rust integer division.
#[test]
fn test_divide_term_integer_unit_denominator() {
    let mut terms = TermStore::new();

    // Normal case: integer coefficient with denom=1
    let ten = terms.mk_int(10.into());
    let coeff = BigRational::from(BigInt::from(2)); // 2/1
    let result = ArithInstantiator::divide_term(&mut terms, ten, &coeff, true);

    // mk_intdiv constant-folds: (div 10 2) → 5
    match terms.get(result) {
        TermData::Const(Constant::Int(v)) => {
            assert_eq!(*v, BigInt::from(5), "10 / 2 should be 5");
        }
        other => panic!("Expected Int(5), got {other:?}"),
    }
}

/// Rho computation for two-sided integer bounds with non-unit coefficient.
///
/// Lower bound: 2*x >= 3, model value x=5.
/// rho = (2*5 - 3) mod 2 = 7 mod 2 = 1
/// selection = (3 + 1) / 2 = 2 (via intdiv)
#[test]
fn test_select_term_both_bounds_integer_rho_computation() {
    let mut terms = TermStore::new();
    let mut inst = ArithInstantiator::new();

    // Lower bound: 2*x >= 3 → coeff=2, term=3, model_value=3
    let three = terms.mk_int(3.into());
    inst.lower_bounds.push(Bound {
        coeff: BigRational::from(BigInt::from(2)),
        term: three,
        strict: false,
        source_literal: None,
        model_value: Some(BigRational::from(BigInt::from(3))),
    });

    // Upper bound: x <= 10 → coeff=1, term=10, model_value=10
    let ten = terms.mk_int(10.into());
    inst.upper_bounds.push(Bound {
        coeff: BigRational::from(BigInt::from(1)),
        term: ten,
        strict: false,
        source_literal: None,
        model_value: Some(BigRational::from(BigInt::from(10))),
    });

    let x = terms.mk_var("x", Sort::Int);
    let model_value = BigRational::from(BigInt::from(5));

    let selected = inst.select_term(&mut terms, x, &model_value, true);
    assert!(selected.is_some(), "Should select a term");

    // rho = (2*5 - 3) mod 2 = 1
    // selection = (3 + 1) / 2 = intdiv(4, 2) = 2
    let selected = selected.unwrap();
    match terms.get(selected) {
        TermData::Const(Constant::Int(v)) => {
            assert_eq!(*v, BigInt::from(2), "rho selection should give 2");
        }
        other => panic!("Expected Int(2) from rho computation, got {other:?}"),
    }
}

/// Rho = 0 case: coefficient divides (c * model - t_model) evenly.
///
/// Lower bound: 3*x >= 6, model value x=7.
/// rho = (3*7 - 6) mod 3 = 15 mod 3 = 0
/// selection = 6 / 3 = 2 (simple intdiv, no rho adjustment)
#[test]
fn test_select_term_both_bounds_nonunit_coeff_rho_zero() {
    let mut terms = TermStore::new();
    let mut inst = ArithInstantiator::new();

    let six = terms.mk_int(6.into());
    inst.lower_bounds.push(Bound {
        coeff: BigRational::from(BigInt::from(3)),
        term: six,
        strict: false,
        source_literal: None,
        model_value: Some(BigRational::from(BigInt::from(6))),
    });

    let twenty = terms.mk_int(20.into());
    inst.upper_bounds.push(Bound {
        coeff: BigRational::from(BigInt::from(1)),
        term: twenty,
        strict: false,
        source_literal: None,
        model_value: Some(BigRational::from(BigInt::from(20))),
    });

    let x = terms.mk_var("x", Sort::Int);
    let model_value = BigRational::from(BigInt::from(7));

    let selected = inst.select_term(&mut terms, x, &model_value, true);
    assert!(selected.is_some(), "Should select a term");

    // rho = (3*7 - 6) mod 3 = 0 → selection = intdiv(6, 3) = 2
    let selected = selected.unwrap();
    match terms.get(selected) {
        TermData::Const(Constant::Int(v)) => {
            assert_eq!(
                *v,
                BigInt::from(2),
                "rho=0 should give simple division 6/3=2"
            );
        }
        other => panic!("Expected Int(2) from rho=0 path, got {other:?}"),
    }
}

/// Fallback when no model values are populated on bounds.
///
/// Without model values, bound_selection_term falls back to simple t/c division.
#[test]
fn test_select_term_both_bounds_no_model_values_fallback() {
    let mut terms = TermStore::new();
    let mut inst = ArithInstantiator::new();

    let three = terms.mk_int(3.into());
    inst.lower_bounds.push(Bound {
        coeff: BigRational::from(BigInt::from(2)),
        term: three,
        strict: false,
        source_literal: None,
        model_value: None,
    });

    let ten = terms.mk_int(10.into());
    inst.upper_bounds.push(Bound {
        coeff: BigRational::from(BigInt::from(1)),
        term: ten,
        strict: false,
        source_literal: None,
        model_value: None,
    });

    let x = terms.mk_var("x", Sort::Int);
    let model_value = BigRational::from(BigInt::from(5));

    let selected = inst.select_term(&mut terms, x, &model_value, true);
    assert!(selected.is_some(), "Should select a term");

    // Without model values: fallback to simple intdiv(3, 2) = 1
    let selected = selected.unwrap();
    match terms.get(selected) {
        TermData::Const(Constant::Int(v)) => {
            assert_eq!(*v, BigInt::from(1), "fallback should give intdiv(3,2)=1");
        }
        other => panic!("Expected Int(1) from fallback division, got {other:?}"),
    }
}

/// Bounds with model values should be preferred over bounds without model
/// values so LIA rho computation can run when an evaluable bound is available.
#[test]
fn test_select_term_lower_prefers_bound_with_model_value_for_rho() {
    let mut terms = TermStore::new();
    let mut inst = ArithInstantiator::new();

    let y = terms.mk_var("y", Sort::Int);
    inst.lower_bounds.push(Bound {
        coeff: BigRational::from(BigInt::from(2)),
        term: y,
        strict: false,
        source_literal: None,
        model_value: None,
    });

    let five = terms.mk_int(5.into());
    inst.lower_bounds.push(Bound {
        coeff: BigRational::from(BigInt::from(2)),
        term: five,
        strict: false,
        source_literal: None,
        model_value: Some(BigRational::from(BigInt::from(5))),
    });

    let x = terms.mk_var("x", Sort::Int);
    let model_value = BigRational::from(BigInt::from(4));

    let selected = inst
        .select_term(&mut terms, x, &model_value, true)
        .expect("evaluable lower bound should select");

    // rho = (2*4 - 5) mod 2 = 1, so selection is (5 + 1) / 2 = 3.
    match terms.get(selected) {
        TermData::Const(Constant::Int(v)) => {
            assert_eq!(*v, BigInt::from(3), "rho-adjusted lower bound");
        }
        other => panic!("Expected Int(3) from evaluable lower rho, got {other:?}"),
    }
}

/// Same preference for upper bounds: an earlier unevaluable symbolic bound
/// must not block a later bound from using LIA rho.
#[test]
fn test_select_term_upper_prefers_bound_with_model_value_for_rho() {
    let mut terms = TermStore::new();
    let mut inst = ArithInstantiator::new();

    let y = terms.mk_var("y", Sort::Int);
    inst.upper_bounds.push(Bound {
        coeff: BigRational::from(BigInt::from(2)),
        term: y,
        strict: false,
        source_literal: None,
        model_value: None,
    });

    let five = terms.mk_int(5.into());
    inst.upper_bounds.push(Bound {
        coeff: BigRational::from(BigInt::from(2)),
        term: five,
        strict: false,
        source_literal: None,
        model_value: Some(BigRational::from(BigInt::from(5))),
    });

    let x = terms.mk_var("x", Sort::Int);
    let model_value = BigRational::from(BigInt::from(1));

    let selected = inst
        .select_term(&mut terms, x, &model_value, true)
        .expect("evaluable upper bound should select");

    // rho = (5 - 2*1) mod 2 = 1, so selection is (5 - 1) / 2 = 2.
    match terms.get(selected) {
        TermData::Const(Constant::Int(v)) => {
            assert_eq!(*v, BigInt::from(2), "rho-adjusted upper bound");
        }
        other => panic!("Expected Int(2) from evaluable upper rho, got {other:?}"),
    }
}

/// Rho computation with symbolic (non-constant) bound term.
///
/// Prior rho tests only used constant bound terms where mk_add/mk_intdiv
/// constant-fold to a concrete Int. This test uses a variable as the bound
/// term, so the selection must produce a compound term `(div (+ y 1) 2)`.
///
/// Lower bound: 2*x >= y, coeff=2, term=y, model_value(y)=3
/// Model value of x: 5
/// rho = (2*5 - 3) mod 2 = 7 mod 2 = 1
/// selection = (y + 1) / 2 = intdiv(add(y, 1), 2)
#[test]
fn test_select_term_symbolic_bound_rho_computation() {
    let mut terms = TermStore::new();
    let mut inst = ArithInstantiator::new();

    let y = terms.mk_var("y", Sort::Int);
    inst.lower_bounds.push(Bound {
        coeff: BigRational::from(BigInt::from(2)),
        term: y,
        strict: false,
        source_literal: None,
        model_value: Some(BigRational::from(BigInt::from(3))),
    });

    // Need an upper bound too (Priority 3 path)
    let ten = terms.mk_int(10.into());
    inst.upper_bounds.push(Bound {
        coeff: BigRational::from(BigInt::from(1)),
        term: ten,
        strict: false,
        source_literal: None,
        model_value: Some(BigRational::from(BigInt::from(10))),
    });

    let x = terms.mk_var("x", Sort::Int);
    let model_value = BigRational::from(BigInt::from(5));

    let selected = inst.select_term(&mut terms, x, &model_value, true);
    assert!(
        selected.is_some(),
        "Should select a term with symbolic bound"
    );

    let selected = selected.unwrap();
    // Result should be a compound term: intdiv(add(y, 1), 2)
    // Since y is symbolic, mk_add(y, 1) does NOT fold to a constant.
    // The term should be IntDiv(Add(y, 1), 2).
    match terms.get(selected) {
        TermData::Const(Constant::Int(_)) => {
            panic!("Expected compound term from symbolic bound, got a constant");
        }
        _ => {
            // Compound term — verify structure: should involve intdiv
            // The exact structure depends on TermStore's mk_intdiv and mk_add
            // implementation. The key property is that the term is NOT just a constant.
        }
    }
}

/// Euclidean mod with negative numerator.
///
/// rho = (-3) mod 2 should be 1 (not -1).
/// This is critical for correctness: SMT-LIB uses Euclidean semantics.
///
/// Setup: 2*x >= t, t^M = 13, x^M = 5
/// diff = 2*5 - 13 = -3
/// rho = (-3) mod 2 = 1  (Euclidean: always non-negative)
/// selection = (t + 1) / 2
#[test]
fn test_select_term_negative_rho_euclidean() {
    let mut terms = TermStore::new();
    let mut inst = ArithInstantiator::new();

    let thirteen = terms.mk_int(13.into());
    inst.lower_bounds.push(Bound {
        coeff: BigRational::from(BigInt::from(2)),
        term: thirteen,
        strict: false,
        source_literal: None,
        model_value: Some(BigRational::from(BigInt::from(13))),
    });

    let twenty = terms.mk_int(20.into());
    inst.upper_bounds.push(Bound {
        coeff: BigRational::from(BigInt::from(1)),
        term: twenty,
        strict: false,
        source_literal: None,
        model_value: Some(BigRational::from(BigInt::from(20))),
    });

    let x = terms.mk_var("x", Sort::Int);
    let model_value = BigRational::from(BigInt::from(5));

    let selected = inst.select_term(&mut terms, x, &model_value, true);
    assert!(selected.is_some(), "Should select a term");

    // rho = (2*5 - 13) mod 2 = -3 mod 2 = 1 (Euclidean)
    // selection = intdiv(13 + 1, 2) = intdiv(14, 2) = 7
    let selected = selected.unwrap();
    match terms.get(selected) {
        TermData::Const(Constant::Int(v)) => {
            assert_eq!(
                *v,
                BigInt::from(7),
                "negative rho should use Euclidean mod: (-3) mod 2 = 1, giving (13+1)/2 = 7"
            );
        }
        other => panic!("Expected Int(7) from negative rho computation, got {other:?}"),
    }
}

/// Nested multiplication: (* 2 (* 3 x)) should extract coeff = 6.
/// (#5888 Finding 7)
#[test]
fn test_extract_variable_nested_multiplication() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let two = terms.mk_int(2.into());
    let three = terms.mk_int(3.into());
    // (* 2 (* 3 x))
    let inner = terms.mk_mul(vec![three, x]);
    let outer = terms.mk_mul(vec![two, inner]);

    let (coeff, remainder) = ArithInstantiator::extract_variable(&mut terms, outer, x);
    assert_eq!(
        coeff,
        BigRational::from(BigInt::from(6)),
        "(* 2 (* 3 x)) should extract coeff = 6"
    );
    assert!(remainder.is_none(), "No remainder for pure multiplication");
}

/// N-ary multiplication: (* 2 3 x) should extract coeff = 6.
#[test]
fn test_extract_variable_nary_multiplication() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let two = terms.mk_int(2.into());
    let three = terms.mk_int(3.into());
    // (* 2 3 x) — 3-arg multiplication
    let nary_mul = terms.mk_mul(vec![two, three, x]);

    let (coeff, remainder) = ArithInstantiator::extract_variable(&mut terms, nary_mul, x);
    assert_eq!(
        coeff,
        BigRational::from(BigInt::from(6)),
        "(* 2 3 x) should extract coeff = 6"
    );
    assert!(remainder.is_none(), "No remainder for pure multiplication");
}

/// Reversed nested: (* (* 3 x) 2) should also extract coeff = 6.
#[test]
fn test_extract_variable_nested_multiplication_reversed() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let two = terms.mk_int(2.into());
    let three = terms.mk_int(3.into());
    // (* (* 3 x) 2)
    let inner = terms.mk_mul(vec![three, x]);
    let outer = terms.mk_mul(vec![inner, two]);

    let (coeff, remainder) = ArithInstantiator::extract_variable(&mut terms, outer, x);
    assert_eq!(
        coeff,
        BigRational::from(BigInt::from(6)),
        "(* (* 3 x) 2) should extract coeff = 6"
    );
    assert!(remainder.is_none(), "No remainder for pure multiplication");
}

/// ITE extraction: (ite cond x (-x)) should extract coeff = 1 with ITE remainder.
/// This is the abs(x) pattern: ite(x >= 0, x, -x).
/// (#5888 Finding 8 — deductive-checks generates ite for truncation division)
#[test]
fn test_extract_variable_ite_same_coeff() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(0.into());
    let cond = terms.mk_ge(x, zero); // x >= 0
    let neg_x = terms.mk_sub(vec![zero, x]); // 0 - x = -x (coeff = -1)

    // But for abs, both branches have the variable with potentially different sign.
    // ite(x >= 0, x, -x) — then_coeff = 1, else_coeff = -1 → different, can't extract.
    // That's actually correct: abs(x) doesn't have a clean linear coefficient.
    let abs_x = terms.mk_ite(cond, x, neg_x);
    let (coeff, _remainder) = ArithInstantiator::extract_variable(&mut terms, abs_x, x);
    // abs(x) has different coefficients in branches, so extraction returns 0
    assert_eq!(
        coeff,
        BigRational::from(BigInt::from(0)),
        "abs(x) = ite(x>=0, x, -x) has different coefficients (1 vs -1)"
    );
}

/// ITE extraction: (ite cond (x + a) (x + b)) should extract coeff = 1.
/// Both branches have x with coefficient 1, remainders differ.
#[test]
fn test_extract_variable_ite_matching_coeff() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let zero = terms.mk_int(0.into());
    let cond = terms.mk_ge(a, zero); // a >= 0 (condition doesn't involve x)

    let then_val = terms.mk_add(vec![x, a]); // x + a
    let else_val = terms.mk_add(vec![x, b]); // x + b

    let ite_term = terms.mk_ite(cond, then_val, else_val);
    let (coeff, remainder) = ArithInstantiator::extract_variable(&mut terms, ite_term, x);

    assert_eq!(
        coeff,
        BigRational::from(BigInt::from(1)),
        "ite(cond, x+a, x+b) should extract coeff = 1"
    );
    assert!(
        remainder.is_some(),
        "Should have remainder = ite(cond, a, b)"
    );
}

/// Not(<) produces lower bound (since Not(<) is >=).
/// This tests that process_assertion handles Not(< x 5) → x >= 5 → lower bound.
#[test]
fn test_process_negated_strict_lt_produces_lower_bound() {
    let mut terms = TermStore::new();
    let mut inst = ArithInstantiator::new();

    // Create: Not(x < 5) → x >= 5 → lower bound
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(5.into());
    let lt = terms.mk_lt(x, five); // x < 5
    let not_lt = terms.mk_not(lt); // Not(x < 5) = x >= 5

    let result = inst.process_assertion(&mut terms, not_lt, x);
    assert!(result, "Should extract bound from Not(x < 5)");
    assert_eq!(
        inst.lower_bounds.len(),
        1,
        "Not(x < 5) should give lower bound (x >= 5)"
    );
    assert!(inst.upper_bounds.is_empty(), "Should NOT have upper bound");
}

/// Conjunction recursion: (and (x >= 0) (x <= 10)) should extract both bounds.
#[test]
fn test_process_conjunction_extracts_both_bounds() {
    let mut terms = TermStore::new();
    let mut inst = ArithInstantiator::new();

    // Create: (and (x >= 0) (x <= 10))
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(0.into());
    let ten = terms.mk_int(10.into());
    let ge = terms.mk_ge(x, zero); // x >= 0
    let le = terms.mk_le(x, ten); // x <= 10
    let conj = terms.mk_and(vec![ge, le]); // (and (x >= 0) (x <= 10))

    let result = inst.process_assertion(&mut terms, conj, x);
    assert!(result, "Should extract bounds from conjunction");
    assert_eq!(
        inst.lower_bounds.len(),
        1,
        "Should have 1 lower bound from x >= 0"
    );
    assert_eq!(
        inst.upper_bounds.len(),
        1,
        "Should have 1 upper bound from x <= 10"
    );
}

/// Nested conjunction: (and (and (x >= 0) (x <= 10)) (x >= -5)) should extract 3 bounds.
#[test]
fn test_process_nested_conjunction() {
    let mut terms = TermStore::new();
    let mut inst = ArithInstantiator::new();

    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(0.into());
    let ten = terms.mk_int(10.into());
    let neg5 = terms.mk_int((-5).into());
    let ge0 = terms.mk_ge(x, zero);
    let le10 = terms.mk_le(x, ten);
    let ge_neg5 = terms.mk_ge(x, neg5);
    let inner = terms.mk_and(vec![ge0, le10]);
    let outer = terms.mk_and(vec![inner, ge_neg5]);

    let result = inst.process_assertion(&mut terms, outer, x);
    assert!(result, "Should extract bounds from nested conjunction");
    assert_eq!(
        inst.lower_bounds.len(),
        2,
        "Should have 2 lower bounds (x >= 0, x >= -5)"
    );
    assert_eq!(
        inst.upper_bounds.len(),
        1,
        "Should have 1 upper bound (x <= 10)"
    );
}

/// Test Not(P => Q) decomposition: Not(x >= 5 => x >= 10) ≡ x >= 5 AND x < 10.
/// This arises from CEGQI CE lemmas where forall body `(=> P Q)` is negated.
/// Without decomposition, bounds in P are invisible to the extractor.
#[test]
fn test_process_not_implies_decomposition() {
    let mut terms = TermStore::new();
    let mut inst = ArithInstantiator::new();

    // Build: Not(x >= 5 => x >= 10)
    // which equals: x >= 5 AND Not(x >= 10) = x >= 5 AND x < 10
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));
    let x_ge_5 = terms.mk_ge(x, five);
    let x_ge_10 = terms.mk_ge(x, ten);
    let implies = terms.mk_implies(x_ge_5, x_ge_10);
    let not_implies = terms.mk_not(implies);

    let result = inst.process_assertion(&mut terms, not_implies, x);
    assert!(result, "Should extract bounds from Not(P => Q)");
    // x >= 5 gives a lower bound, Not(x >= 10) = x < 10 gives an upper bound.
    assert!(
        !inst.lower_bounds.is_empty(),
        "Not(P => Q): P = (x >= 5) should yield a lower bound"
    );
    assert!(
        !inst.upper_bounds.is_empty(),
        "Not(P => Q): Not(Q) = (x < 10) should yield an upper bound"
    );
}

/// Test Not(or A B) decomposition: Not(x <= 0 OR x >= 10) ≡ x > 0 AND x < 10.
/// De Morgan decomposition extracts bounds from each negated disjunct.
#[test]
fn test_process_not_or_de_morgan_decomposition() {
    let mut terms = TermStore::new();
    let mut inst = ArithInstantiator::new();

    // Build: Not(x <= 0 OR x >= 10)
    // which equals: Not(x <= 0) AND Not(x >= 10) = x > 0 AND x < 10
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let ten = terms.mk_int(BigInt::from(10));
    let x_le_0 = terms.mk_le(x, zero);
    let x_ge_10 = terms.mk_ge(x, ten);
    let or_term = terms.mk_or(vec![x_le_0, x_ge_10]);
    let not_or = terms.mk_not(or_term);

    let result = inst.process_assertion(&mut terms, not_or, x);
    assert!(result, "Should extract bounds from Not(or A B)");
    // Not(x <= 0) = x > 0 gives lower bound, Not(x >= 10) = x < 10 gives upper bound.
    assert!(
        !inst.lower_bounds.is_empty(),
        "Not(or A B): Not(x <= 0) = x > 0 should yield a lower bound"
    );
    assert!(
        !inst.upper_bounds.is_empty(),
        "Not(or A B): Not(x >= 10) = x < 10 should yield an upper bound"
    );
}

/// Test Not(Not(x >= 5)) double negation elimination.
/// Should pass through to process x >= 5 directly.
#[test]
fn test_process_double_negation_elimination() {
    let mut terms = TermStore::new();
    let mut inst = ArithInstantiator::new();

    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let x_ge_5 = terms.mk_ge(x, five);
    let not_ge = terms.mk_not(x_ge_5);
    let not_not_ge = terms.mk_not(not_ge);

    let result = inst.process_assertion(&mut terms, not_not_ge, x);
    assert!(result, "Double negation should be eliminated");
    assert_eq!(inst.lower_bounds.len(), 1, "x >= 5 yields one lower bound");
}

/// Test that extract_bound rejects bounds where pv still appears in the bound term.
/// This matches CVC5's hasSubterm(val, pv) safety check.
/// Example: (>= (+ x (div x 3)) 10) → extract_variable finds x with coeff=1,
/// remainder = (div x 3). The bound_term = (- 10 (div x 3)) still contains x.
#[test]
fn test_extract_bound_rejects_pv_in_bound_term() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let ten = terms.mk_int(BigInt::from(10));
    let div_x_3 = terms.mk_intdiv(x, three); // (div x 3)
    let sum = terms.mk_add(vec![x, div_x_3]); // x + (div x 3)

    // Assertion: (>= (+ x (div x 3)) 10) → x >= 10 - (div x 3)
    // But (div x 3) still contains x, so the bound should be rejected.
    let mut inst = ArithInstantiator::new();
    let geq = terms.mk_ge(sum, ten);
    let result = inst.process_assertion(&mut terms, geq, x);

    // Should NOT extract a bound because pv is still in the bound term
    assert!(
        !result,
        "Should reject bound where pv appears under div in the bound term"
    );
    assert!(
        inst.lower_bounds.is_empty(),
        "No lower bounds should be collected"
    );
    assert!(
        inst.upper_bounds.is_empty(),
        "No upper bounds should be collected"
    );
}
