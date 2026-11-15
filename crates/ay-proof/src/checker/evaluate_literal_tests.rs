// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::Sort;

fn ratio(numerator: i64, denominator: i64) -> BigRational {
    BigRational::new(BigInt::from(numerator), BigInt::from(denominator))
}

#[test]
fn every_integer_and_every_finite_decimal_has_a_literal() {
    for (value, integral, literal) in [
        (ratio(-4, 1), true, "-4"),
        (ratio(4, 1), true, "4"),
        (ratio(0, 1), true, "0"),
        (ratio(-4, 1), false, "-4.0"),
        (ratio(4, 1), false, "4.0"),
        (ratio(0, 1), false, "0.0"),
        (ratio(5, 2), false, "2.5"),
        (ratio(-5, 2), false, "-2.5"),
        (ratio(-1, 8), false, "-0.125"),
        (ratio(1, 20), false, "0.05"),
        (ratio(-1001, 1000), false, "-1.001"),
    ] {
        assert_eq!(
            carcara_numeric_literal(&value, integral).as_deref(),
            Some(literal),
            "{value}"
        );
    }
}

#[test]
fn a_value_without_a_finite_decimal_has_no_literal() {
    for value in [ratio(1, 3), ratio(-1, 3), ratio(5, 6), ratio(1, 7)] {
        assert_eq!(carcara_numeric_literal(&value, false), None, "{value}");
    }
}

/// `(= (* (- 1.0) (/ 1.0 3.0)) (- (/ 1.0 3.0)))` is a true ground equality
/// AY's evaluator accepts, but no literal spells `-1/3`, so pinned Carcara's
/// `evaluate` cannot conclude it in any spelling: the printer-facing validator
/// refuses it, and the `-4` and `-2.5` results it keeps.
#[test]
fn the_printer_facing_validator_refuses_exactly_the_unspellable_values() {
    let mut terms = TermStore::new();
    let minus_one = terms.mk_rational(ratio(-1, 1));
    let third = terms.mk_rational(ratio(1, 3));
    let product = terms.mk_app(Symbol::named("*"), [minus_one, third], Sort::Real);
    let minus_third = terms.mk_rational(ratio(-1, 3));
    let unspellable = terms.mk_app(Symbol::named("="), [product, minus_third], Sort::Bool);
    assert!(validate_ground_evaluate(&terms, ProofId(1), &[unspellable], 0, &[]).is_ok());
    assert!(
        validate_ground_evaluate_for_printer(&terms, ProofId(1), &[unspellable], 0, &[]).is_err()
    );

    let minus_two = terms.mk_int(BigInt::from(-2));
    let sum = terms.mk_app(Symbol::named("+"), [minus_two, minus_two], Sort::Int);
    let minus_four = terms.mk_int(BigInt::from(-4));
    let negative = terms.mk_app(Symbol::named("="), [sum, minus_four], Sort::Bool);
    assert!(validate_ground_evaluate_for_printer(&terms, ProofId(2), &[negative], 0, &[]).is_ok());

    let half = terms.mk_rational(ratio(1, 2));
    let five = terms.mk_rational(ratio(-5, 1));
    let scaled = terms.mk_app(Symbol::named("*"), [five, half], Sort::Real);
    let minus_two_and_a_half = terms.mk_rational(ratio(-5, 2));
    let decimal = terms.mk_app(
        Symbol::named("="),
        [scaled, minus_two_and_a_half],
        Sort::Bool,
    );
    assert!(validate_ground_evaluate_for_printer(&terms, ProofId(3), &[decimal], 0, &[]).is_ok());
}

/// Pinned Carcara's `evaluate` divides by truncation (MEASURED: `(= (div (- 7)
/// 2) -4)` fails with "'-3' and '-4'"), so a true SMT-LIB `div` / `mod` over a
/// negative dividend is refused for the printer, and the non-negative
/// dividend, where truncation and SMT-LIB agree, is kept.
#[test]
fn integer_division_over_a_negative_dividend_is_refused_for_the_printer() {
    let mut terms = TermStore::new();
    let equality = |terms: &mut TermStore, op: &str, dividend: i64, divisor: i64, value: i64| {
        let dividend = terms.mk_int(BigInt::from(dividend));
        let divisor = terms.mk_int(BigInt::from(divisor));
        let applied = terms.mk_app(Symbol::named(op), [dividend, divisor], Sort::Int);
        let value = terms.mk_int(BigInt::from(value));
        terms.mk_app(Symbol::named("="), [applied, value], Sort::Bool)
    };
    for (op, dividend, divisor, value, printable) in [
        ("div", -7, 2, -4, false),
        ("mod", -7, 2, 1, false),
        ("div", 7, -2, -3, true),
        ("mod", 7, -2, 1, true),
        ("div", 7, 2, 3, true),
    ] {
        let step = equality(&mut terms, op, dividend, divisor, value);
        assert!(
            validate_ground_evaluate(&terms, ProofId(1), &[step], 0, &[]).is_ok(),
            "({op} {dividend} {divisor}) = {value} is SMT-LIB-true"
        );
        assert_eq!(
            validate_ground_evaluate_for_printer(&terms, ProofId(1), &[step], 0, &[]).is_ok(),
            printable,
            "({op} {dividend} {divisor})"
        );
    }
}
