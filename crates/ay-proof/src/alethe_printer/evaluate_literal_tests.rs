// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{Sort, TermStore};
use num_bigint::BigInt;

fn printed(terms: &TermStore, equality: TermId) -> String {
    let printer = AlethePrinter::new(terms);
    let clause_str = printer.format_clause(&[equality]);
    printer.format_evaluate_step(ProofId(7), &[equality], &clause_str)
}

/// The step f07/f08 reached: `(= (+ (- 2) (- 2)) (- 4))`. Pinned Carcara
/// rejects it as `evaluate` and checks the printed bridge `valid` (measured
/// with carcara 1.1.0, git 9a352ee).
#[test]
fn a_negative_integer_result_is_evaluated_to_its_literal_and_bridged_by_refl() {
    let mut terms = TermStore::new();
    let minus_two = terms.mk_int(BigInt::from(-2));
    let sum = terms.mk_app(Symbol::named("+"), [minus_two, minus_two], Sort::Int);
    let minus_four = terms.mk_int(BigInt::from(-4));
    let equality = terms.mk_app(Symbol::named("="), [sum, minus_four], Sort::Bool);
    assert_eq!(
        printed(&terms, equality),
        "(step t7.lit (cl (= (+ (- 2) (- 2)) -4)) :rule evaluate)\n\
         (step t7.sp (cl (= -4 (- 4))) :rule refl)\n\
         (step t7 (cl (= (+ (- 2) (- 2)) (- 4))) :rule trans :premises (t7.lit t7.sp))"
    );
}

#[test]
fn a_real_result_with_a_finite_decimal_is_bridged_and_one_without_is_a_hole() {
    let mut terms = TermStore::new();
    let five = terms.mk_rational(BigRational::from_integer(BigInt::from(-5)));
    let half = terms.mk_rational(BigRational::new(BigInt::from(1), BigInt::from(2)));
    let product = terms.mk_app(Symbol::named("*"), [five, half], Sort::Real);
    let value = terms.mk_rational(BigRational::new(BigInt::from(-5), BigInt::from(2)));
    let equality = terms.mk_app(Symbol::named("="), [product, value], Sort::Bool);
    assert_eq!(
        printed(&terms, equality),
        "(step t7.lit (cl (= (* (- 5.0) (/ 1.0 2.0)) -2.5)) :rule evaluate)\n\
         (step t7.sp (cl (= -2.5 (- (/ 5.0 2.0)))) :rule refl)\n\
         (step t7 (cl (= (* (- 5.0) (/ 1.0 2.0)) (- (/ 5.0 2.0)))) :rule trans \
         :premises (t7.lit t7.sp))"
    );

    let three = terms.mk_rational(BigRational::from_integer(BigInt::from(3)));
    let one = terms.mk_rational(BigRational::from_integer(BigInt::from(1)));
    let quotient = terms.mk_app(Symbol::named("/"), [one, three], Sort::Real);
    let third = terms.mk_rational(BigRational::new(BigInt::from(1), BigInt::from(3)));
    let unspellable = terms.mk_app(Symbol::named("="), [quotient, third], Sort::Bool);
    assert_eq!(
        printed(&terms, unspellable),
        format!(
            "(step t7 (cl (= (/ 1.0 3.0) (/ 1.0 3.0))) :rule {})",
            ay_core::UNPROVED_STEP_RULE
        )
    );
}

#[test]
fn a_literal_value_prints_the_step_unchanged() {
    let mut terms = TermStore::new();
    let two = terms.mk_int(BigInt::from(2));
    let sum = terms.mk_app(Symbol::named("+"), [two, two], Sort::Int);
    let four = terms.mk_int(BigInt::from(4));
    let equality = terms.mk_app(Symbol::named("="), [sum, four], Sort::Bool);
    assert_eq!(
        printed(&terms, equality),
        "(step t7 (cl (= (+ 2 2) 4)) :rule evaluate)"
    );
    let truth = terms.mk_bool(true);
    let less = terms.mk_app(Symbol::named("<"), [two, four], Sort::Bool);
    let comparison = terms.mk_app(Symbol::named("="), [less, truth], Sort::Bool);
    assert_eq!(
        printed(&terms, comparison),
        "(step t7 (cl (= (< 2 4) true)) :rule evaluate)"
    );
}
