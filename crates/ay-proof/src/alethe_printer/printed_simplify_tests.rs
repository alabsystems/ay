// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Every row was MEASURED as a one-step document against pinned Carcara
/// 1.1.0 (git 9a352ee) on 2026-10-02.
#[test]
fn comp_simplify_is_judged_as_pinned_carcara_checks_it() {
    for (conclusion, carcara_accepts) in [
        ("(= (< x 5) (not (<= 5 x)))", true),
        ("(= (not (<= 5 x)) (< x 5))", true),
        ("(= (> x x) (not (<= x x)))", true),
        ("(= (not (<= x x)) (> x x))", true),
        ("(= (> 5 x) (< x 5))", false),
        ("(= (>= x 5) (<= 5 x))", true),
        ("(= (<= 5 x) (>= x 5))", true),
        ("(= (< 2 3) true)", true),
        ("(= (< (- 2) 3) true)", true),
        ("(= (< -2 3) true)", true),
        ("(= (< (- 2) x) (not (<= x (- 2))))", true),
        ("(= (not (< x 5)) (not (not (<= 5 x))))", false),
        ("(= (>= x x) true)", true),
        ("(= (>= x x) (<= x x))", true),
        ("(= (<= x x) true)", true),
        ("(= (< x x) false)", true),
        ("(= (> x 5) (not (<= x 5)))", true),
        ("(= (>= 5 x) (<= x 5))", true),
        ("(= (> x y) (< y x))", false),
        ("(= (< y x) (> x y))", false),
        ("(= (>= (+ x 1) x) (<= x (+ x 1)))", true),
        ("(= (< x 5) (< x 5))", false),
        ("(= (<= (- 2) (- 3)) false)", true),
        ("(= (<= 2.0 3) true)", true),
        ("(= (> (- 2) (- 3)) true)", false),
        ("(= (< x (- 3)) (not (<= (- 3) x)))", true),
        // The comparison-reversal chain step d0e349259b retired.
        ("(= (not (<= x x)) (< x x))", false),
    ] {
        assert_eq!(
            printed_comp_simplify_holds(&[conclusion], &StepDefinitions::NONE),
            carcara_accepts,
            "{conclusion}"
        );
    }
}

#[test]
fn comp_simplify_declines_what_it_cannot_read_exactly() {
    for conclusion in [
        // Closed operands that are not both plain numbers.
        "(= (< (/ 1.0 2.0) 1.0) (not (<= 1.0 (/ 1.0 2.0))))",
        // Two spellings that may be one Carcara term.
        "(= (< -2 (- 2)) (not (<= (- 2) -2)))",
        // Not a unit equality.
        "(< x 5)",
    ] {
        assert!(
            !printed_comp_simplify_holds(&[conclusion], &StepDefinitions::NONE),
            "{conclusion}"
        );
    }
    assert!(!printed_comp_simplify_holds(
        &["(= (< x 5) (not (<= 5 x)))", "(= (< x 5) (not (<= 5 x)))"],
        &StepDefinitions::NONE
    ));
}

/// MEASURED: `evaluate` compares the evaluated left side with the printed
/// right side as a term, so only a literal value passes.
#[test]
fn an_evaluate_value_must_be_a_literal() {
    for (conclusion, literal) in [
        ("(= (+ (- 2) (- 2)) -4)", true),
        ("(= (+ (- 2) (- 2)) (- 4))", false),
        ("(= (+ 2 2) 4)", true),
        ("(= (+ (- 2.0) (- 2.0)) -4.0)", true),
        ("(= (+ (- 2.0) (- 2.0)) (- 4.0))", false),
        ("(= (* 5.0 (/ 1.0 2.0)) 2.5)", true),
        ("(= (* 1.0 (/ 1.0 3.0)) (/ 1.0 3.0))", false),
        ("(= (< (- 2) 0) true)", true),
        ("(= (= (- 2) (- 3)) false)", true),
        ("(= (bvadd #b01 #b01) #b10)", true),
        ("(= (concat #x1 #x2) (_ bv18 8))", true),
        ("(= (str.++ \"a\" \"b\") \"ab\")", true),
        ("(not (= (- 2) (- 3)))", false),
        ("(= 4 (+ 2 2))", false),
        // Truncating `div` / `mod` (pinned Carcara) agree with SMT-LIB only
        // over a non-negative dividend.
        ("(= (div 7 2) 3)", true),
        ("(= (div 7 (- 2)) -3)", true),
        ("(= (mod 7 (- 2)) 1)", true),
        ("(= (div (- 7) 2) -4)", false),
        ("(= (+ 1 (mod (- 7) 2)) 2)", false),
        ("(= (div -7 2) -4)", false),
        ("(= (div (+ 1 6) 2) 3)", false),
        ("(= (rem 7 2) 1)", false),
    ] {
        assert_eq!(
            printed_evaluate_value_is_literal(&[conclusion], &StepDefinitions::NONE),
            literal,
            "{conclusion}"
        );
    }
}

/// A lowering that names its compound terms (`mul_overflow_cert` binds every
/// long subterm, equalities included, to a step-local `define-fun`) ships
/// `(cl e3) :rule evaluate`; the checker inlines `e3`, and so does the judge.
#[test]
fn step_defined_names_are_read_as_the_terms_they_name() {
    let rendered = "(define-fun e3 () Bool (= (bvadd #x1 #x1) #x2))\n\
                    (define-fun c4 () Bool (= (> x y) (not (<= x y))))\n\
                    (define-fun e5 () Bool (= (bvadd #x1 #x1) w9))";
    let definitions = printed_step_definitions(rendered);
    assert!(printed_evaluate_value_is_literal(&["e3"], &definitions));
    assert!(!printed_evaluate_value_is_literal(&["e5"], &definitions));
    assert!(printed_comp_simplify_holds(&["c4"], &definitions));
    assert!(!printed_evaluate_value_is_literal(
        &["e3"],
        &StepDefinitions::NONE
    ));
}
