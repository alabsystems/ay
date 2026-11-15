// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Workstream D sort fix (DESIGN_lra_interp_tpa.md §4.1, WP-D1-M).

use super::*;

fn row(var: &str, coeff: i64, bound: i64, strict: bool, sort: ChcSort) -> LinearConstraint {
    let mut coeffs = FxHashMap::default();
    coeffs.insert(var.to_owned(), Rational64::from_integer(coeff));
    LinearConstraint {
        coeffs,
        bound: Rational64::from_integer(bound),
        strict,
        var_sort: sort,
    }
}

#[test]
fn real_strict_rows_are_never_tightened() {
    // x < 5 over the reals admits x = 4.5; x <= 4 does not.
    let real = strengthen_strict_lia_constraint(row("x", 1, 5, true, ChcSort::Real));
    assert!(real.strict);
    assert_eq!(real.bound, Rational64::from_integer(5));
    let int = strengthen_strict_lia_constraint(row("x", 1, 5, true, ChcSort::Int));
    assert!(!int.strict);
    assert_eq!(int.bound, Rational64::from_integer(4));
}

#[test]
fn combinations_are_emitted_in_the_rows_sort() {
    let real_row = row("x", 2, 3, true, ChcSort::Real);
    let int_row = row("x", 2, 3, true, ChcSort::Int);
    assert_eq!(combined_row_sort([&int_row, &real_row]), ChcSort::Real);
    assert_eq!(combined_row_sort([&int_row]), ChcSort::Int);
    let mut coeffs = FxHashMap::default();
    coeffs.insert("x".to_owned(), Rational64::new(1, 2));
    let real =
        build_linear_inequality_in_sort(&coeffs, Rational64::new(3, 4), true, &ChcSort::Real)
            .unwrap();
    assert!(
        real.vars().iter().all(|v| v.sort == ChcSort::Real),
        "{real}"
    );
    // (1/2)·x < 3/4 over the reals, never an integer-rounded atom.
    assert_eq!(
        real,
        ChcExpr::lt(
            ChcExpr::mul(
                ChcExpr::Real(1, 2),
                ChcExpr::var(ChcVar::new("x", ChcSort::Real))
            ),
            ChcExpr::Real(3, 4)
        )
    );
    // Int keeps the historical emission byte for byte.
    let int = build_linear_inequality_in_sort(&coeffs, Rational64::new(3, 4), true, &ChcSort::Int);
    assert_eq!(
        int,
        build_linear_inequality(&coeffs, Rational64::new(3, 4), true)
    );
}
