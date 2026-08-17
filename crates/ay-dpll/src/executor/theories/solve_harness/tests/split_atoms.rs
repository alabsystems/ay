// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::{create_disequality_split_atoms, create_int_split_atoms, DisequalitySplitAtoms};
use super::rat;
use ay_core::{Sort, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;

#[test]
fn test_create_disequality_split_atoms_skips_non_numeric_variables() {
    let mut terms = TermStore::new();
    let b = terms.mk_var("b", Sort::Bool);
    let split = ay_core::DisequalitySplitRequest {
        variable: b,
        excluded_value: rat(1),
        disequality_term: None,
        is_distinct: false,
    };

    assert!(matches!(
        create_disequality_split_atoms(&mut terms, &split),
        DisequalitySplitAtoms::Skip
    ));
}

#[test]
fn test_create_disequality_split_atoms_int_fractional_uses_floor_ceil_bounds() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let split = ay_core::DisequalitySplitRequest {
        variable: x,
        excluded_value: BigRational::new(BigInt::from(7), BigInt::from(2)),
        disequality_term: None,
        is_distinct: false,
    };

    let three = terms.mk_int(BigInt::from(3));
    let four = terms.mk_int(BigInt::from(4));
    let expected_le = terms.mk_le(x, three);
    let expected_ge = terms.mk_ge(x, four);

    match create_disequality_split_atoms(&mut terms, &split) {
        DisequalitySplitAtoms::IntFractional { le, ge } => {
            assert_eq!(le, expected_le);
            assert_eq!(ge, expected_ge);
        }
        _ => panic!("expected IntFractional split atoms"),
    }
}

#[test]
fn test_create_disequality_split_atoms_int_exact_preserves_context() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let eq = terms.mk_eq(x, five);
    let diseq = terms.mk_not(eq);
    let split = ay_core::DisequalitySplitRequest {
        variable: x,
        excluded_value: rat(5),
        disequality_term: Some(diseq),
        is_distinct: true,
    };

    let four = terms.mk_int(BigInt::from(4));
    let six = terms.mk_int(BigInt::from(6));
    let expected_le = terms.mk_le(x, four);
    let expected_ge = terms.mk_ge(x, six);

    match create_disequality_split_atoms(&mut terms, &split) {
        DisequalitySplitAtoms::IntExact {
            le,
            ge,
            disequality_term,
            is_distinct,
        } => {
            assert_eq!(le, expected_le);
            assert_eq!(ge, expected_ge);
            assert_eq!(disequality_term, Some(diseq));
            assert!(is_distinct);
        }
        _ => panic!("expected IntExact split atoms"),
    }
}

#[test]
fn test_create_disequality_split_atoms_real_uses_strict_inequalities() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let excluded_term_for_eq =
        terms.mk_rational(BigRational::new(BigInt::from(9), BigInt::from(4)));
    let eq = terms.mk_eq(x, excluded_term_for_eq);
    let excluded = BigRational::new(BigInt::from(9), BigInt::from(4));
    let split = ay_core::DisequalitySplitRequest {
        variable: x,
        excluded_value: excluded.clone(),
        disequality_term: Some(eq),
        is_distinct: false,
    };

    let excluded_term = terms.mk_rational(excluded);
    let expected_lt = terms.mk_lt(x, excluded_term);
    let expected_gt = terms.mk_gt(x, excluded_term);

    match create_disequality_split_atoms(&mut terms, &split) {
        DisequalitySplitAtoms::Real {
            lt,
            gt,
            disequality_term,
            is_distinct,
        } => {
            assert_eq!(lt, expected_lt);
            assert_eq!(gt, expected_gt);
            assert_eq!(disequality_term, Some(eq));
            assert!(!is_distinct);
        }
        _ => panic!("expected Real split atoms"),
    }
}

#[test]
fn test_create_int_split_atoms_real_sort_uses_rational_constants_and_prefer_ceil() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let split = ay_core::SplitRequest {
        variable: x,
        value: BigRational::new(BigInt::from(7), BigInt::from(4)),
        floor: BigInt::from(1),
        ceil: BigInt::from(2),
    };

    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let two = terms.mk_rational(BigRational::from(BigInt::from(2)));
    let expected_le = terms.mk_le(x, one);
    let expected_ge = terms.mk_ge(x, two);

    let (le, ge, prefer_ceil) = create_int_split_atoms(&mut terms, &split);
    assert_eq!(le, expected_le);
    assert_eq!(ge, expected_ge);
    assert_eq!(prefer_ceil, Some(true));
}

#[test]
fn test_create_int_split_atoms_exact_half_prefers_floor_first() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let split = ay_core::SplitRequest {
        variable: x,
        value: BigRational::new(BigInt::from(3), BigInt::from(2)),
        floor: BigInt::from(1),
        ceil: BigInt::from(2),
    };

    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let expected_le = terms.mk_le(x, one);
    let expected_ge = terms.mk_ge(x, two);

    let (le, ge, prefer_ceil) = create_int_split_atoms(&mut terms, &split);
    assert_eq!(le, expected_le);
    assert_eq!(ge, expected_ge);
    assert_eq!(prefer_ceil, Some(false));
}
