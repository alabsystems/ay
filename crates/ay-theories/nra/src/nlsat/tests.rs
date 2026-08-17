// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use num_rational::BigRational;

fn rat(n: i64) -> BigRational {
    BigRational::from_integer(n.into())
}

#[test]
fn test_flip_cmp() {
    assert_eq!(flip_cmp(">="), "<=");
    assert_eq!(flip_cmp(">"), "<");
    assert_eq!(flip_cmp("<="), ">=");
    assert_eq!(flip_cmp("<"), ">");
    assert_eq!(flip_cmp("="), "=");
}

#[test]
fn test_negate_cmp() {
    assert_eq!(negate_cmp(">="), "<");
    assert_eq!(negate_cmp(">"), "<=");
    assert_eq!(negate_cmp("<="), ">");
    assert_eq!(negate_cmp("<"), ">=");
    assert_eq!(negate_cmp("="), "distinct");
    assert_eq!(negate_cmp("distinct"), "=");
}

#[test]
fn test_eval_constant_cmp() {
    assert!(eval_constant_cmp(">=", &rat(5), &rat(3)));
    assert!(eval_constant_cmp(">=", &rat(3), &rat(3)));
    assert!(!eval_constant_cmp(">=", &rat(2), &rat(3)));
    assert!(eval_constant_cmp("=", &rat(3), &rat(3)));
    assert!(!eval_constant_cmp("=", &rat(2), &rat(3)));
}

#[test]
fn test_feasible_set_from_linear_ge() {
    // x >= 5 => [5, +inf)
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear(">=", true, &rat(1), &rat(5));
    assert!(fs.contains_point(&rat(5)));
    assert!(fs.contains_point(&rat(10)));
    assert!(!fs.contains_point(&rat(4)));
}

#[test]
fn test_feasible_set_from_linear_lt() {
    // x < 3 => (-inf, 3)
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear("<", true, &rat(1), &rat(3));
    assert!(fs.contains_point(&rat(2)));
    assert!(!fs.contains_point(&rat(3)));
    assert!(!fs.contains_point(&rat(4)));
}

#[test]
fn test_feasible_set_from_linear_negative_coeff() {
    // -2*x >= 6 => x <= -3 => (-inf, -3]
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear(">=", true, &rat(-2), &rat(6));
    assert!(fs.contains_point(&rat(-3)));
    assert!(fs.contains_point(&rat(-10)));
    assert!(!fs.contains_point(&rat(-2)));
}

#[test]
fn test_feasible_set_from_linear_negated() {
    // NOT(x >= 5) => x < 5 => (-inf, 5)
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear(">=", false, &rat(1), &rat(5));
    assert!(fs.contains_point(&rat(4)));
    assert!(!fs.contains_point(&rat(5)));
}

#[test]
fn test_feasible_set_from_linear_equality() {
    // x = 7 => {7}
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear("=", true, &rat(1), &rat(7));
    assert!(fs.contains_point(&rat(7)));
    assert!(!fs.contains_point(&rat(6)));
    assert_eq!(fs.is_singleton(), Some(rat(7)));
}

#[test]
fn test_feasible_set_from_linear_disequality() {
    // x != 3 => (-inf, 3) U (3, +inf)
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear("distinct", true, &rat(1), &rat(3));
    assert!(!fs.contains_point(&rat(3)));
    assert!(fs.contains_point(&rat(2)));
    assert!(fs.contains_point(&rat(4)));
}

// ====== Additional NLSAT tests (#8460) ======

/// Zero coefficient: 0*x >= 5 => 0 >= 5 is false => empty set.
#[test]
fn test_feasible_set_from_linear_zero_coeff_false() {
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear(">=", true, &rat(0), &rat(5));
    assert!(
        fs.is_empty(),
        "0 >= 5 is false, so feasible set should be empty"
    );
}

/// Zero coefficient: 0*x >= 0 => 0 >= 0 is true => full set.
#[test]
fn test_feasible_set_from_linear_zero_coeff_true() {
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear(">=", true, &rat(0), &rat(0));
    assert!(
        !fs.is_empty(),
        "0 >= 0 is true, so feasible set should be full"
    );
    assert!(fs.contains_point(&rat(42)));
    assert!(fs.contains_point(&rat(-42)));
}

/// Zero coefficient: 0*x > 0 => false => empty.
#[test]
fn test_feasible_set_from_linear_zero_coeff_strict_gt_false() {
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear(">", true, &rat(0), &rat(0));
    assert!(
        fs.is_empty(),
        "0 > 0 is false, so feasible set should be empty"
    );
}

/// Zero coefficient: 0*x = 0 => true => full.
#[test]
fn test_feasible_set_from_linear_zero_coeff_eq_true() {
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear("=", true, &rat(0), &rat(0));
    assert!(
        !fs.is_empty(),
        "0 = 0 is true, so feasible set should be full"
    );
}

/// Negated equality: NOT(x = 5) => x != 5 => (-inf,5) U (5,+inf).
#[test]
fn test_feasible_set_from_linear_negated_equality() {
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear("=", false, &rat(1), &rat(5));
    assert!(!fs.contains_point(&rat(5)));
    assert!(fs.contains_point(&rat(4)));
    assert!(fs.contains_point(&rat(6)));
}

/// Negated disequality: NOT(x != 3) => x = 3 => {3}.
#[test]
fn test_feasible_set_from_linear_negated_disequality() {
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear("distinct", false, &rat(1), &rat(3));
    assert!(fs.contains_point(&rat(3)));
    assert!(!fs.contains_point(&rat(2)));
    assert!(!fs.contains_point(&rat(4)));
    assert_eq!(fs.is_singleton(), Some(rat(3)));
}

/// Unknown comparator should conservatively return full set.
#[test]
fn test_feasible_set_from_linear_unknown_cmp() {
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear("???", true, &rat(1), &rat(5));
    assert!(!fs.is_empty(), "unknown comparator should produce full set");
    assert!(fs.contains_point(&rat(0)));
}

/// flip_cmp is its own inverse: flip(flip(x)) == x.
#[test]
fn test_flip_cmp_involution() {
    for cmp in &[">=", ">", "<=", "<", "=", "distinct"] {
        assert_eq!(
            flip_cmp(flip_cmp(cmp)),
            *cmp,
            "flip_cmp should be an involution for {cmp}"
        );
    }
}

/// negate_cmp is its own inverse: negate(negate(x)) == x.
#[test]
fn test_negate_cmp_involution() {
    for cmp in &[">=", ">", "<=", "<", "=", "distinct"] {
        assert_eq!(
            negate_cmp(negate_cmp(cmp)),
            *cmp,
            "negate_cmp should be an involution for {cmp}"
        );
    }
}

/// eval_constant_cmp covers all six operators.
#[test]
fn test_eval_constant_cmp_all_operators() {
    assert!(eval_constant_cmp(">", &rat(5), &rat(3)));
    assert!(!eval_constant_cmp(">", &rat(3), &rat(3)));
    assert!(eval_constant_cmp("<=", &rat(3), &rat(3)));
    assert!(eval_constant_cmp("<=", &rat(2), &rat(3)));
    assert!(!eval_constant_cmp("<=", &rat(4), &rat(3)));
    assert!(eval_constant_cmp("<", &rat(2), &rat(3)));
    assert!(!eval_constant_cmp("<", &rat(3), &rat(3)));
    assert!(eval_constant_cmp("distinct", &rat(1), &rat(2)));
    assert!(!eval_constant_cmp("distinct", &rat(2), &rat(2)));
    assert!(eval_constant_cmp("!=", &rat(1), &rat(2)));
}

/// Negative coefficient with negated literal:
/// NOT(-3*x >= 6) => NOT(x <= -2) => x > -2 => (-2, +inf).
#[test]
fn test_feasible_set_from_linear_negative_coeff_negated() {
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear(">=", false, &rat(-3), &rat(6));
    // -3*x >= 6 => x <= -2, negation => x > -2
    assert!(!fs.contains_point(&rat(-2)));
    assert!(fs.contains_point(&rat(-1)));
    assert!(fs.contains_point(&rat(0)));
}

/// Fractional coefficient: (1/2)*x >= 3 => x >= 6.
#[test]
fn test_feasible_set_from_linear_fractional_coeff() {
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let half = BigRational::new(1.into(), 2.into());
    let fs = solver.feasible_set_from_linear(">=", true, &half, &rat(3));
    assert!(fs.contains_point(&rat(6)));
    assert!(fs.contains_point(&rat(100)));
    assert!(!fs.contains_point(&rat(5)));
}

/// x <= -10 => (-inf, -10].
#[test]
fn test_feasible_set_from_linear_le_negative() {
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear("<=", true, &rat(1), &rat(-10));
    assert!(fs.contains_point(&rat(-10)));
    assert!(fs.contains_point(&rat(-100)));
    assert!(!fs.contains_point(&rat(-9)));
}
