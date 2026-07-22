// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_int_constants() {
    let mut store = TermStore::new();

    let i1 = store.mk_int(BigInt::from(42));
    let i2 = store.mk_int(BigInt::from(42));
    let i3 = store.mk_int(BigInt::from(43));

    assert_eq!(i1, i2);
    assert_ne!(i1, i3);
}

#[test]
fn test_int_addition_constant_folding() {
    let mut store = TermStore::new();

    let a = store.mk_int(BigInt::from(2));
    let b = store.mk_int(BigInt::from(3));
    let c = store.mk_int(BigInt::from(5));

    // 2 + 3 = 5
    let sum = store.mk_add(vec![a, b]);
    assert_eq!(sum, c);

    // 1 + 2 + 3 = 6
    let one = store.mk_int(BigInt::from(1));
    let two = store.mk_int(BigInt::from(2));
    let three = store.mk_int(BigInt::from(3));
    let six = store.mk_int(BigInt::from(6));
    let sum3 = store.mk_add(vec![one, two, three]);
    assert_eq!(sum3, six);
}

#[test]
fn test_int_addition_identity() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Int);
    let zero = store.mk_int(BigInt::from(0));

    // x + 0 = x
    assert_eq!(store.mk_add(vec![x, zero]), x);
    // 0 + x = x
    assert_eq!(store.mk_add(vec![zero, x]), x);
}

#[test]
fn test_int_subtraction_constant_folding() {
    let mut store = TermStore::new();

    let five = store.mk_int(BigInt::from(5));
    let three = store.mk_int(BigInt::from(3));
    let two = store.mk_int(BigInt::from(2));

    // 5 - 3 = 2
    assert_eq!(store.mk_sub(vec![five, three]), two);
}

#[test]
fn test_int_subtraction_identity() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Int);
    let zero = store.mk_int(BigInt::from(0));

    // x - 0 = x
    assert_eq!(store.mk_sub(vec![x, zero]), x);

    // x - x = 0
    assert_eq!(store.mk_sub(vec![x, x]), zero);
}

#[test]
fn test_int_multiplication_constant_folding() {
    let mut store = TermStore::new();

    let three = store.mk_int(BigInt::from(3));
    let four = store.mk_int(BigInt::from(4));
    let twelve = store.mk_int(BigInt::from(12));

    // 3 * 4 = 12
    assert_eq!(store.mk_mul(vec![three, four]), twelve);

    // 2 * 3 * 4 = 24
    let two = store.mk_int(BigInt::from(2));
    let twenty_four = store.mk_int(BigInt::from(24));
    assert_eq!(store.mk_mul(vec![two, three, four]), twenty_four);
}

#[test]
fn test_int_multiplication_identity_annihilation() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Int);
    let zero = store.mk_int(BigInt::from(0));
    let one = store.mk_int(BigInt::from(1));

    // x * 1 = x
    assert_eq!(store.mk_mul(vec![x, one]), x);

    // x * 0 = 0
    assert_eq!(store.mk_mul(vec![x, zero]), zero);
}

#[test]
fn test_int_constant_distribution_over_add() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    let two = store.mk_int(BigInt::from(2));

    let sum = store.mk_add(vec![x, y]);
    let result = store.mk_mul(vec![two, sum]);

    let two_x = store.mk_mul(vec![two, x]);
    let two_y = store.mk_mul(vec![two, y]);
    let expected = store.mk_add(vec![two_x, two_y]);
    assert_eq!(result, expected);
}

#[test]
fn test_int_constant_distribution_over_add_with_folding() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    let two = store.mk_int(BigInt::from(2));
    let three = store.mk_int(BigInt::from(3));

    let sum = store.mk_add(vec![x, y]);
    let result = store.mk_mul(vec![two, three, sum]);

    let six_x = store.mk_mul(vec![two, three, x]);
    let six_y = store.mk_mul(vec![two, three, y]);
    let expected = store.mk_add(vec![six_x, six_y]);
    assert_eq!(result, expected);
}

#[test]
fn test_int_negation() {
    let mut store = TermStore::new();

    let five = store.mk_int(BigInt::from(5));
    let neg_five = store.mk_int(BigInt::from(-5));

    // -5
    assert_eq!(store.mk_neg(five), neg_five);
    // -(-5) = 5
    assert_eq!(store.mk_neg(neg_five), five);
}

#[test]
fn test_neg_distribute_over_add_int() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);
    let sum = store.mk_add(vec![a, b]);

    // -(a + b) → (-a) + (-b)
    let result = store.mk_neg(sum);
    let neg_a = store.mk_neg(a);
    let neg_b = store.mk_neg(b);
    let expected = store.mk_add(vec![neg_a, neg_b]);

    assert_eq!(result, expected);
}

#[test]
fn test_neg_distribute_over_add_real() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Real);
    let y = store.mk_var("y", Sort::Real);
    let sum = store.mk_add(vec![x, y]);

    // -(x + y) → (-x) + (-y)
    let result = store.mk_neg(sum);
    let neg_x = store.mk_neg(x);
    let neg_y = store.mk_neg(y);
    let expected = store.mk_add(vec![neg_x, neg_y]);

    assert_eq!(result, expected);
}

#[test]
fn test_neg_distribute_with_coefficients() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let two = store.mk_int(BigInt::from(2));
    let three = store.mk_int(BigInt::from(3));

    // -(2a + 3a) → -5a via distribution and coefficient collection
    let two_a = store.mk_mul(vec![two, a]);
    let three_a = store.mk_mul(vec![three, a]);
    let sum = store.mk_add(vec![two_a, three_a]);
    let result = store.mk_neg(sum);

    // Expected: -5a (single term with coefficient -5)
    let neg_five = store.mk_int(BigInt::from(-5));
    let expected = store.mk_mul(vec![neg_five, a]);

    assert_eq!(result, expected);
}

#[test]
fn test_neg_factor_into_mul_int() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let three = store.mk_int(BigInt::from(3));
    let neg_three = store.mk_int(BigInt::from(-3));

    // -(3 * a) → (-3) * a
    let three_a = store.mk_mul(vec![three, a]);
    let result = store.mk_neg(three_a);

    let expected = store.mk_mul(vec![neg_three, a]);

    assert_eq!(result, expected);
}

#[test]
fn test_neg_factor_into_mul_real() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Real);
    let half = store.mk_rational(BigRational::new(BigInt::from(1), BigInt::from(2)));
    let neg_half = store.mk_rational(BigRational::new(BigInt::from(-1), BigInt::from(2)));

    // -(1/2 * x) → (-1/2) * x
    let half_x = store.mk_mul(vec![half, x]);
    let result = store.mk_neg(half_x);

    let expected = store.mk_mul(vec![neg_half, x]);

    assert_eq!(result, expected);
}

#[test]
fn test_neg_chain_simplification() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);
    let two = store.mk_int(BigInt::from(2));

    // -(2a + b) → -2a + (-b) → (-2)*a + (-b)
    let two_a = store.mk_mul(vec![two, a]);
    let sum = store.mk_add(vec![two_a, b]);
    let result = store.mk_neg(sum);

    let neg_two = store.mk_int(BigInt::from(-2));
    let neg_two_a = store.mk_mul(vec![neg_two, a]);
    let neg_b = store.mk_neg(b);
    let expected = store.mk_add(vec![neg_two_a, neg_b]);

    assert_eq!(result, expected);
}

#[test]
fn test_int_div_mod() {
    let mut store = TermStore::new();

    let seven = store.mk_int(BigInt::from(7));
    let three = store.mk_int(BigInt::from(3));
    let two = store.mk_int(BigInt::from(2));
    let one = store.mk_int(BigInt::from(1));

    // 7 div 3 = 2
    assert_eq!(store.mk_intdiv(seven, three), two);

    // 7 mod 3 = 1
    assert_eq!(store.mk_mod(seven, three), one);

    // SMT-LIB Euclidean division for negative dividend (#2781):
    // (div -7 2) = -4, NOT -3 (Rust truncation toward zero)
    let neg_seven = store.mk_int(BigInt::from(-7));
    let two_term = store.mk_int(BigInt::from(2));
    let neg_four = store.mk_int(BigInt::from(-4));
    assert_eq!(store.mk_intdiv(neg_seven, two_term), neg_four);

    // (mod -7 2) = 1 (always non-negative in SMT-LIB)
    assert_eq!(store.mk_mod(neg_seven, two_term), one);

    // (div 7 -2) = -3 (Euclidean: 7 = (-2)*(-3) + 1, remainder 1 >= 0)
    let neg_two = store.mk_int(BigInt::from(-2));
    let neg_three = store.mk_int(BigInt::from(-3));
    assert_eq!(store.mk_intdiv(seven, neg_two), neg_three);

    // (mod 7 -2) = 1 (always non-negative in SMT-LIB)
    assert_eq!(store.mk_mod(seven, neg_two), one);

    // (div -7 -2) = 4 (Euclidean: -7 = (-2)*4 + 1, remainder 1 >= 0)
    let four = store.mk_int(BigInt::from(4));
    assert_eq!(store.mk_intdiv(neg_seven, neg_two), four);

    // (mod -7 -2) = 1 (always non-negative in SMT-LIB)
    assert_eq!(store.mk_mod(neg_seven, neg_two), one);
}

#[test]
fn test_int_rem_constant_folding() {
    // Z3 semantics (#8730): `rem` takes the sign of the divisor.
    // Reference: z3/src/ast/arith_decl_plugin.cpp OP_REM,
    // z3/src/tactic/arith/purify_arith_tactic.cpp:47
    //   (rem t1 t2) --> ite(t2 >= 0, (mod t1 t2), -(mod t1 t2))
    let mut store = TermStore::new();
    let seven = store.mk_int(BigInt::from(7));
    let neg_seven = store.mk_int(BigInt::from(-7));
    let three = store.mk_int(BigInt::from(3));
    let neg_three = store.mk_int(BigInt::from(-3));
    let one = store.mk_int(BigInt::from(1));
    let two = store.mk_int(BigInt::from(2));
    let neg_one = store.mk_int(BigInt::from(-1));
    let neg_two = store.mk_int(BigInt::from(-2));

    // Positive divisor: rem == mod.
    //   rem 7 3 = 1, rem -7 3 = 2.
    assert_eq!(store.mk_rem(seven, three), one);
    assert_eq!(store.mk_rem(neg_seven, three), two);

    // Negative divisor: rem = -(mod ..).
    //   rem 7 -3 = -(mod 7 -3) = -1.
    //   rem -7 -3 = -(mod -7 -3) = -2.
    assert_eq!(store.mk_rem(seven, neg_three), neg_one);
    assert_eq!(store.mk_rem(neg_seven, neg_three), neg_two);

    // rem x 1 = 0, rem x -1 = 0.
    let x = store.mk_var("x", Sort::Int);
    let zero = store.mk_int(BigInt::from(0));
    assert_eq!(store.mk_rem(x, one), zero);
    assert_eq!(store.mk_rem(x, neg_one), zero);

    // 0 rem y = 0 (when y is a constant NON-ZERO divisor).
    assert_eq!(store.mk_rem(zero, three), zero);

    // `0 rem y` with a SYMBOLIC divisor must NOT fold to 0: when y = 0,
    // `(rem 0 0)` is UNCONSTRAINED under SMT-LIB / Z3 (#9140), so folding it
    // wrongly refutes y = 0 models (#div0).
    let y = store.mk_var("y", Sort::Int);
    let zero_rem_y = store.mk_rem(zero, y);
    assert!(matches!(
        store.get(zero_rem_y),
        TermData::App(sym, args) if sym.name() == "rem" && args.len() == 2
    ));

    // `rem x x` must NOT fold to 0: when x = 0, `(rem 0 0)` is unconstrained.
    let rem_x_x = store.mk_rem(x, x);
    assert_ne!(rem_x_x, zero);
    assert!(matches!(
        store.get(rem_x_x),
        TermData::App(sym, args) if sym.name() == "rem" && args.len() == 2
    ));
}

#[test]
fn test_rational_addition() {
    let mut store = TermStore::new();

    let half = store.mk_rational(BigRational::new(BigInt::from(1), BigInt::from(2)));
    let quarter = store.mk_rational(BigRational::new(BigInt::from(1), BigInt::from(4)));
    let three_quarters = store.mk_rational(BigRational::new(BigInt::from(3), BigInt::from(4)));

    // 1/2 + 1/4 = 3/4
    assert_eq!(store.mk_add(vec![half, quarter]), three_quarters);
}

#[test]
fn test_real_constant_distribution_over_add() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Real);
    let y = store.mk_var("y", Sort::Real);
    let three_halves = store.mk_rational(BigRational::new(BigInt::from(3), BigInt::from(2)));

    let sum = store.mk_add(vec![x, y]);
    let result = store.mk_mul(vec![three_halves, sum]);

    let c_x = store.mk_mul(vec![three_halves, x]);
    let c_y = store.mk_mul(vec![three_halves, y]);
    let expected = store.mk_add(vec![c_x, c_y]);
    assert_eq!(result, expected);
}

#[test]
fn test_rational_division() {
    let mut store = TermStore::new();

    let two = store.mk_rational(BigRational::from(BigInt::from(2)));
    let half = store.mk_rational(BigRational::new(BigInt::from(1), BigInt::from(2)));
    let four = store.mk_rational(BigRational::from(BigInt::from(4)));

    // 2 / 0.5 = 4
    assert_eq!(store.mk_div(two, half), four);
}

#[test]
fn test_real_self_division_not_folded() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Real);
    let one = store.mk_rational(BigRational::from(BigInt::from(1)));

    // `x / x` must NOT fold to 1: when x = 0, `(/ 0 0)` is UNCONSTRAINED under
    // SMT-LIB Reals (a single consistent but unspecified value, not 1), so the
    // identity is unsound (#div0-soundness). The term is kept symbolic so the
    // real-arithmetic theory reasons about (and fails closed on) the zero case.
    // This mirrors `test_int_self_division_not_folded` for integer `div`.
    let result = store.mk_div(x, x);
    assert_ne!(result, one);
    assert!(matches!(
        store.get(result),
        TermData::App(sym, args) if sym.name() == "/" && args.len() == 2
    ));
}

#[test]
fn test_real_zero_numerator_symbolic_divisor_not_folded() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Real);
    let zero = store.mk_rational(BigRational::zero());

    // `0 / x` must NOT fold to 0 when the divisor `x` may be zero: under
    // SMT-LIB Reals `(/ 0 0)` is UNCONSTRAINED, so folding wrongly refutes
    // models with x = 0 (#div0-soundness). Kept symbolic.
    let result = store.mk_div(zero, x);
    assert_ne!(result, zero);
    assert!(matches!(
        store.get(result),
        TermData::App(sym, args) if sym.name() == "/" && args.len() == 2
    ));
}

#[test]
fn test_real_zero_numerator_nonzero_const_divisor_folds() {
    let mut store = TermStore::new();

    let zero = store.mk_rational(BigRational::zero());
    let two = store.mk_rational(BigRational::from(BigInt::from(2)));

    // `0 / 2 = 0` is sound: the divisor is a known non-zero constant.
    assert_eq!(store.mk_div(zero, two), zero);
}

#[test]
fn test_int_self_division_not_folded() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Int);
    let one = store.mk_int(BigInt::from(1));

    // `x div x` must NOT fold to 1: when x = 0, `(div 0 0)` is UNCONSTRAINED
    // under SMT-LIB Ints (not 1), so the identity is unsound (#div0). The term
    // is kept symbolic so the LIA theory reasons about the zero case.
    let result = store.mk_intdiv(x, x);
    assert_ne!(result, one);
    assert!(matches!(
        store.get(result),
        TermData::App(sym, args) if sym.name() == "div" && args.len() == 2
    ));
}

#[test]
fn test_self_division_complex_term_not_folded() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);
    let sum = store.mk_add(vec![a, b]);
    let one = store.mk_int(BigInt::from(1));

    // `(a + b) div (a + b)` must NOT fold to 1 for the same reason: the divisor
    // may be zero, leaving the quotient unconstrained (#div0).
    let result = store.mk_intdiv(sum, sum);
    assert_ne!(result, one);
    assert!(matches!(
        store.get(result),
        TermData::App(sym, args) if sym.name() == "div" && args.len() == 2
    ));
}

#[test]
fn test_real_coefficient_collection_basic() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Real);
    let two = store.mk_rational(BigRational::from(BigInt::from(2)));
    let three = store.mk_rational(BigRational::from(BigInt::from(3)));
    let five = store.mk_rational(BigRational::from(BigInt::from(5)));

    // Create (* 2.0 a) and (* 3.0 a)
    let two_a = store.mk_mul(vec![two, a]);
    let three_a = store.mk_mul(vec![three, a]);

    // (* 2.0 a) + (* 3.0 a) = (* 5.0 a)
    let result = store.mk_add(vec![two_a, three_a]);
    let expected = store.mk_mul(vec![five, a]);
    assert_eq!(result, expected);
}

#[test]
fn test_real_coefficient_collection_with_negation() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Real);
    let three = store.mk_rational(BigRational::from(BigInt::from(3)));

    // Create (* 3.0 a) and (- a)
    let three_a = store.mk_mul(vec![three, a]);
    let neg_a = store.mk_neg(a);

    // (* 3.0 a) + (- a) = (* 2.0 a)
    let result = store.mk_add(vec![three_a, neg_a]);
    let two = store.mk_rational(BigRational::from(BigInt::from(2)));
    let expected = store.mk_mul(vec![two, a]);
    assert_eq!(result, expected);
}

#[test]
fn test_real_coefficient_collection_to_zero() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Real);
    let two = store.mk_rational(BigRational::from(BigInt::from(2)));
    let neg_two = store.mk_rational(BigRational::from(BigInt::from(-2)));
    let zero = store.mk_rational(BigRational::from(BigInt::from(0)));

    // Create (* 2.0 a) and (* -2.0 a)
    let two_a = store.mk_mul(vec![two, a]);
    let neg_two_a = store.mk_mul(vec![neg_two, a]);

    // (* 2.0 a) + (* -2.0 a) = 0
    let result = store.mk_add(vec![two_a, neg_two_a]);
    assert_eq!(result, zero);
}

#[test]
fn test_real_coefficient_collection_to_single() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Real);
    let two = store.mk_rational(BigRational::from(BigInt::from(2)));
    let neg_one = store.mk_rational(BigRational::from(BigInt::from(-1)));

    // Create (* 2.0 a) and (* -1.0 a)
    let two_a = store.mk_mul(vec![two, a]);
    let neg_one_a = store.mk_mul(vec![neg_one, a]);

    // (* 2.0 a) + (* -1.0 a) = a
    let result = store.mk_add(vec![two_a, neg_one_a]);
    assert_eq!(result, a);
}

#[test]
fn test_real_coefficient_collection_to_neg() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Real);
    let two = store.mk_rational(BigRational::from(BigInt::from(2)));
    let neg_three = store.mk_rational(BigRational::from(BigInt::from(-3)));

    // Create (* 2.0 a) and (* -3.0 a)
    let two_a = store.mk_mul(vec![two, a]);
    let neg_three_a = store.mk_mul(vec![neg_three, a]);

    // (* 2.0 a) + (* -3.0 a) = (- a)
    let result = store.mk_add(vec![two_a, neg_three_a]);
    let expected = store.mk_neg(a);
    assert_eq!(result, expected);
}

#[test]
fn test_real_coefficient_collection_fractional() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Real);
    // Create 1/2 and 3/2
    let half = store.mk_rational(BigRational::new(BigInt::from(1), BigInt::from(2)));
    let three_halves = store.mk_rational(BigRational::new(BigInt::from(3), BigInt::from(2)));
    let two = store.mk_rational(BigRational::from(BigInt::from(2)));

    // Create (* 1/2 a) and (* 3/2 a)
    let half_a = store.mk_mul(vec![half, a]);
    let three_halves_a = store.mk_mul(vec![three_halves, a]);

    // (* 1/2 a) + (* 3/2 a) = (* 2 a)
    let result = store.mk_add(vec![half_a, three_halves_a]);
    let expected = store.mk_mul(vec![two, a]);
    assert_eq!(result, expected);
}

#[test]
fn test_real_coefficient_collection_mixed() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Real);
    let b = store.mk_var("b", Sort::Real);
    let two = store.mk_rational(BigRational::from(BigInt::from(2)));
    let three = store.mk_rational(BigRational::from(BigInt::from(3)));

    // Create (* 2 a), a, and (* 3 b)
    let two_a = store.mk_mul(vec![two, a]);
    let three_b = store.mk_mul(vec![three, b]);

    // (* 2 a) + a + (* 3 b) should combine 2a + 1a = 3a
    let result = store.mk_add(vec![two_a, a, three_b]);

    // Result should be (+ (* 3 a) (* 3 b)) - though order may vary
    if let TermData::App(Symbol::Named(name), args) = store.get(result) {
        assert_eq!(name, "+");
        assert_eq!(args.len(), 2);
        // Both should be multiplications with coefficient 3
        for &arg in args {
            if let TermData::App(Symbol::Named(op), factors) = store.get(arg) {
                assert_eq!(op, "*");
                assert_eq!(factors.len(), 2);
                let has_coeff_3 = factors
                    .iter()
                    .any(|&f| store.get_rational(f) == Some(&BigRational::from(BigInt::from(3))));
                assert!(has_coeff_3, "Expected coefficient 3 in multiplication");
            } else {
                panic!("Expected multiplication");
            }
        }
    } else {
        panic!("Expected + App term");
    }
}

#[test]
fn test_int_less_than() {
    let mut store = TermStore::new();

    let two = store.mk_int(BigInt::from(2));
    let three = store.mk_int(BigInt::from(3));

    // 2 < 3 = true
    assert_eq!(store.mk_lt(two, three), store.true_term());
    // 3 < 2 = false
    assert_eq!(store.mk_lt(three, two), store.false_term());
    // 2 < 2 = false
    assert_eq!(store.mk_lt(two, two), store.false_term());
}

#[test]
fn test_int_less_equal() {
    let mut store = TermStore::new();

    let two = store.mk_int(BigInt::from(2));
    let three = store.mk_int(BigInt::from(3));

    // 2 <= 3 = true
    assert_eq!(store.mk_le(two, three), store.true_term());
    // 3 <= 2 = false
    assert_eq!(store.mk_le(three, two), store.false_term());
    // 2 <= 2 = true
    assert_eq!(store.mk_le(two, two), store.true_term());
}

#[test]
fn test_int_greater_than() {
    let mut store = TermStore::new();

    let two = store.mk_int(BigInt::from(2));
    let three = store.mk_int(BigInt::from(3));

    // 3 > 2 = true
    assert_eq!(store.mk_gt(three, two), store.true_term());
    // 2 > 3 = false
    assert_eq!(store.mk_gt(two, three), store.false_term());
    // 2 > 2 = false
    assert_eq!(store.mk_gt(two, two), store.false_term());
}

#[test]
fn test_int_greater_equal() {
    let mut store = TermStore::new();

    let two = store.mk_int(BigInt::from(2));
    let three = store.mk_int(BigInt::from(3));

    // 3 >= 2 = true
    assert_eq!(store.mk_ge(three, two), store.true_term());
    // 2 >= 3 = false
    assert_eq!(store.mk_ge(two, three), store.false_term());
    // 2 >= 2 = true
    assert_eq!(store.mk_ge(two, two), store.true_term());
}

#[test]
fn test_rational_comparisons() {
    let mut store = TermStore::new();

    let half = store.mk_rational(BigRational::new(BigInt::from(1), BigInt::from(2)));
    let third = store.mk_rational(BigRational::new(BigInt::from(1), BigInt::from(3)));

    // 1/3 < 1/2 = true
    assert_eq!(store.mk_lt(third, half), store.true_term());
    // 1/2 < 1/3 = false
    assert_eq!(store.mk_lt(half, third), store.false_term());

    // 1/3 <= 1/2 = true
    assert_eq!(store.mk_le(third, half), store.true_term());
    // 1/2 <= 1/2 = true
    assert_eq!(store.mk_le(half, half), store.true_term());

    // 1/2 > 1/3 = true
    assert_eq!(store.mk_gt(half, third), store.true_term());

    // 1/2 >= 1/3 = true
    assert_eq!(store.mk_ge(half, third), store.true_term());
}

// Regression tests for additive-inverse cancellation that MUST respect
// multiplicity. A prior `mk_add` implementation cancelled `a + (-a)` using a
// deduplicating hash set + `retain`, which dropped EVERY copy of a base term
// equal to a cancelled one. For sums like `a + (-a) + a` it collapsed the
// whole sum to 0 instead of `a`, corrupting linear constraints at the
// simplification level and producing wrong sat/unsat verdicts in both
// directions. Cancellation is now handled by per-base coefficient summation,
// which preserves multiplicity. See crates/ay-core/src/term/arithmetic.rs.

#[test]
fn test_add_cancel_multiplicity_int() {
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::Int);
    let two = store.mk_int(BigInt::from(2));

    // a + (-a) + a == a  (net coefficient +1)
    let neg_a = store.mk_neg(a);
    assert_eq!(store.mk_add(vec![a, neg_a, a]), a);

    // a + a + (-a) == a  (order independence)
    assert_eq!(store.mk_add(vec![a, a, neg_a]), a);

    // a + (-a) + (-a) == -a  (net coefficient -1)
    let expected_neg = store.mk_neg(a);
    assert_eq!(store.mk_add(vec![a, neg_a, neg_a]), expected_neg);

    // a + (-a) + a + a == 2a  (net coefficient +2)
    let two_a = store.mk_mul(vec![two, a]);
    assert_eq!(store.mk_add(vec![a, neg_a, a, a]), two_a);

    // a + (-a) == 0  (true cancellation still collapses)
    let zero = store.mk_int(BigInt::zero());
    assert_eq!(store.mk_add(vec![a, neg_a]), zero);
}

#[test]
fn test_add_cancel_multiplicity_preserves_other_terms_int() {
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);

    // a + b + a + (-a) == a + b  (b must survive; net coeff of a is +1)
    let neg_a = store.mk_neg(a);
    let expected = store.mk_add(vec![a, b]);
    assert_eq!(store.mk_add(vec![a, b, a, neg_a]), expected);

    // a + b + (-a) == b  (a fully cancels, b survives)
    assert_eq!(store.mk_add(vec![a, b, neg_a]), b);
}

#[test]
fn test_add_cancel_multiplicity_real() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Real);

    // x + (-x) + x == x  (net coefficient +1) — Real path must be sound too
    let neg_x = store.mk_neg(x);
    assert_eq!(store.mk_add(vec![x, neg_x, x]), x);

    // x + x + (-x) == x
    assert_eq!(store.mk_add(vec![x, x, neg_x]), x);

    // x + (-x) + (-x) == -x
    let expected_neg = store.mk_neg(x);
    assert_eq!(store.mk_add(vec![x, neg_x, neg_x]), expected_neg);

    // x + (-x) == 0
    let zero = store.mk_rational(BigRational::zero());
    assert_eq!(store.mk_add(vec![x, neg_x]), zero);
}

#[test]
fn test_mul_commutative_canonical_monomial() {
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);
    // (* a b) and (* b a) must canonicalize to the same term (sorted factors).
    let ab = store.mk_mul(vec![a, b]);
    let ba = store.mk_mul(vec![b, a]);
    assert_eq!(
        ab, ba,
        "mk_mul must produce a canonical (commutative) monomial"
    );

    // 3-factor commutativity: (* a b a) and (* a a b) must agree.
    let aba = store.mk_mul(vec![a, b, a]);
    let aab = store.mk_mul(vec![a, a, b]);
    assert_eq!(aba, aab, "mk_mul must canonicalize repeated factors");

    // Constant coefficient + canonical factors: (* 2 b a) == (* 2 a b) == (* a 2 b)
    let two = store.mk_int(BigInt::from(2));
    let m1 = store.mk_mul(vec![two, b, a]);
    let m2 = store.mk_mul(vec![two, a, b]);
    let m3 = store.mk_mul(vec![a, two, b]);
    assert_eq!(m1, m2);
    assert_eq!(m2, m3);
}
