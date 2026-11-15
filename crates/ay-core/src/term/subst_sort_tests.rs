// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rebuilding `/` preserves Real division even when its children are Int numerals.

use super::*;

#[test]
fn real_division_rebuild_promotes_integer_numerals() {
    let mut terms = TermStore::new();
    let seven = terms.mk_int(7.into());
    let two = terms.mk_int(2.into());
    let real_division = terms.mk_app(Symbol::named("/"), [seven, two], Sort::Real);
    let rebuilt =
        terms.rebuild_arith_app("/", &Symbol::named("/"), vec![seven, two], real_division);
    let expected = terms.mk_rational(BigRational::new(7.into(), 2.into()));
    assert_eq!(rebuilt, expected);
    assert_eq!(terms.sort(real_division), &Sort::Real);
    let integer_division = terms.rebuild_arith_app(
        "div",
        &Symbol::named("div"),
        vec![seven, two],
        real_division,
    );
    assert_eq!(integer_division, terms.mk_int(3.into()));
    assert_eq!(terms.sort(integer_division), &Sort::Int);
}

#[test]
fn real_division_substitution_preserves_result_sort() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let two = terms.mk_rational(BigRational::from_integer(2.into()));
    let division = terms.mk_div(x, two);
    let three = terms.mk_int(3.into());
    let rebuilt = terms.substitute(division, &[x], &[three]);
    let expected = terms.mk_rational(BigRational::new(3.into(), 2.into()));
    assert_eq!(rebuilt, expected);
    assert_eq!(terms.sort(rebuilt), &Sort::Real);
}

#[test]
fn division_by_zero_stays_an_unspecified_real_application() {
    let mut terms = TermStore::new();
    let zero = terms.mk_int(0.into());
    let original = terms.mk_app(Symbol::named("/"), [zero, zero], Sort::Real);
    let rebuilt = terms.rebuild_arith_app("/", &Symbol::named("/"), vec![zero, zero], original);
    assert_eq!(terms.sort(rebuilt), &Sort::Real);
    assert!(matches!(terms.get(rebuilt), TermData::App(symbol, _) if symbol.name() == "/"));
}
