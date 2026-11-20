// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use num_bigint::BigInt;
use num_rational::BigRational;

use super::*;
use crate::parse_mps_exact;

fn int(v: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(v))
}

fn big(text: &str) -> BigRational {
    decimal::parse_decimal(text).expect("number")
}

/// AY-N11 `cancel-bad`: 9007199254740993 X - 9007199254740992 Y = 0 at
/// X = Y = 1 has activity 1. Through `f64` both coefficients are ...992 and
/// the point looks feasible; exactly it is not. (The checker's relative
/// tolerance, `tol * 9e15` here, does accept it, as the organizers' checker
/// did on the reviewers' file: only the exact test sees the model is
/// infeasible.)
#[test]
fn a_point_that_only_f64_finds_feasible_is_refused() {
    let p = parse_mps_exact(
        "NAME EXACT\nROWS\n N OBJ\n E MATCH\nCOLUMNS\n    X OBJ 1 MATCH 9007199254740993\n    \
         Y MATCH -9007199254740992\nRHS\n    RHS1 MATCH 0\nBOUNDS\n FX BND1 X 1\n FX BND1 Y 1\nENDATA\n",
    )
    .expect("parse");
    let point = [int(1), int(1)];
    assert!(p.check_point(&point, &BigRational::zero()).is_err());
    assert!(p.check_point(&point, &write_tolerance()).is_ok());
    // The rounded copy the dense simplex sees accepts it: the reason a
    // verdict of that copy is never printed unconfirmed.
    assert!(crate::check_point(&p.to_problem(), &[1.0, 1.0]).is_ok());
}

#[test]
fn check_point_follows_the_checker_test_and_open_sides_are_1e20() {
    let p = parse_mps_exact(
        "NAME T\nROWS\n N OBJ\n G R\nCOLUMNS\n    X OBJ 2 R 1\nRHS\n    RHS OBJ -3 R 0.1\nENDATA\n",
    )
    .expect("parse");
    // Objective 2x + 3 (the RHS of the objective row is the negated constant).
    assert_eq!(
        p.check_point(&[big("0.1")], &BigRational::zero()),
        Ok(big("3.2"))
    );
    assert!(p.check_point(&[big("0.09")], &BigRational::zero()).is_err());
    // Open upper side of the column and of the G row: 1e20 for the checker.
    assert!(p.check_point(&[big("1e20")], &BigRational::zero()).is_ok());
    assert!(p
        .check_point(&[big("1.0000000001e20")], &BigRational::zero())
        .is_err());
}

#[test]
fn check_written_reads_the_texts_back_and_tests_the_objective() {
    let p = parse_mps_exact(
        "NAME T\nROWS\n N OBJ\n E R\nCOLUMNS\n    X OBJ 1 R 3\nRHS\n    RHS R 1\nENDATA\n",
    )
    .expect("parse");
    // x = 1/3 exactly; written as the nearest f64's text it is within 1e-9.
    let text =
        decimal::write_value(&BigRational::new(BigInt::from(1), BigInt::from(3))).expect("text");
    assert!(p.check_written(&text, std::slice::from_ref(&text)).is_ok());
    // A written objective that is off is refused, as the checker would.
    assert!(p.check_written("0.5", &[text.clone()]).is_err());
    // So is a value the checker cannot read.
    assert!(p.check_written(&text, &["1/3".to_string()]).is_err());
}

#[test]
fn empty_domains_are_exact_infeasibility_arguments() {
    let p = parse_mps_exact(
        "NAME T\nROWS\n N OBJ\n L R\nCOLUMNS\n    M 'MARKER' 'INTORG'\n    X OBJ 1 R 1\n    \
         M 'MARKER' 'INTEND'\nRHS\n    RHS R 4\nBOUNDS\n LO BND X 0.2\n UP BND X 0.7\nENDATA\n",
    )
    .expect("parse");
    assert!(p
        .empty_domain()
        .expect("empty")
        .contains("holds no integer"));
    let p = parse_mps_exact(
        "NAME T\nROWS\n N OBJ\n G R\n L S\nCOLUMNS\n    X OBJ 1 S 1\nRHS\n    RHS R 1\nENDATA\n",
    )
    .expect("parse");
    assert!(p.empty_domain().expect("empty").contains("row 'R'"));
}
