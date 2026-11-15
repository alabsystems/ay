// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Safe snapshot-to-term tests: no FFI pointers or solver search are involved.

use super::*;
use ay_dpll::api::Logic;

fn wide(sign: bool, exponent: u64, significand: u128, eb: u32, sb: u32) -> ModelValue {
    ModelValue::FloatingPointWide {
        sign,
        exponent,
        significand,
        eb,
        sb,
    }
}

#[test]
fn exact_199_bit_snapshot_dispatch_preserves_every_field_in_the_model_ast() {
    let mut solver = Solver::new(Logic::QfFp);
    let sort = Sort::FloatingPoint(8, 200);
    let literal = format!("(fp #b1 #b01111111 #b1{}1)", "0".repeat(197));
    let mut values = ModelValue::decode_typed_literals(&[(&literal, &sort)]).unwrap();
    let value = values.remove(0);
    assert_eq!(scalar_value_sort(&value), Some(sort.clone()));
    let term = super::super::model_value_to_term(&mut solver, &value, &sort).unwrap();
    assert_eq!(solver.term_sort(term), sort);
    let children = solver.term_children(term);
    assert_eq!(children.len(), 3);
    let expected = [
        (BigInt::from(1), 1),
        (BigInt::from(127), 8),
        ((BigInt::from(1) << 198usize) | BigInt::from(1), 199),
    ];
    for (child, (value, width)) in children.into_iter().zip(expected) {
        assert_eq!(solver.term_sort(child), Sort::bitvec(width));
        assert_eq!(
            solver
                .numeral_string(child)
                .unwrap()
                .parse::<BigInt>()
                .unwrap(),
            value
        );
    }
    assert!(value_to_term(&mut solver, &value, &Sort::FloatingPoint(8, 201)).is_none());
}

fn assert_fields(solver: &Solver, term: Term, fields: (bool, u64, u128, u32, u32)) {
    let (sign, exponent, significand, eb, sb) = fields;
    assert_eq!(solver.term_sort(term), Sort::FloatingPoint(eb, sb));
    assert_eq!(
        solver.term_kind(term),
        TermKind::App {
            name: "fp".into(),
            num_args: 3
        }
    );
    let children = solver.term_children(term);
    assert_eq!(children.len(), 3);
    for (child, (value, width)) in children.into_iter().zip([
        (BigInt::from(u8::from(sign)), 1),
        (BigInt::from(exponent), eb),
        (BigInt::from(significand), sb - 1),
    ]) {
        assert_eq!(solver.term_kind(child), TermKind::Const);
        assert_eq!(solver.term_sort(child), Sort::bitvec(width));
        let actual: BigInt = solver.numeral_string(child).unwrap().parse().unwrap();
        assert_eq!(
            actual, value,
            "every unsigned field bit must survive BigInt transfer"
        );
    }
}

#[test]
fn binary128_snapshot_dispatch_preserves_high_and_low_fraction_bits() {
    let mut solver = Solver::new(Logic::QfFp);
    let fraction = (1u128 << 111) | (1u128 << 64) | (1u128 << 63) | 1;
    for (sign, exponent, significand) in [
        (false, 0x3fff, fraction),
        (true, 0x3fff, fraction),
        (true, 0, 0),
        (false, 0, 1),
        (true, 0x7fff, fraction),
    ] {
        let value = wide(sign, exponent, significand, 15, 113);
        let sort = Sort::FloatingPoint(15, 113);
        let term = super::super::model_value_to_term(&mut solver, &value, &sort).unwrap();
        assert_eq!(Some(term), value_to_term(&mut solver, &value, &sort));
        assert_fields(&solver, term, (sign, exponent, significand, 15, 113));
    }
}

#[test]
fn snapshot_transfer_preserves_unsigned_carriers_without_widening_api_admission() {
    let mut solver = Solver::new(Logic::QfFp);
    // These checks concern term construction only, not arithmetic admission.
    let maximum = wide(true, (1u64 << 31) - 1, u128::MAX, 31, 129);
    let term = value_to_term(&mut solver, &maximum, &Sort::FloatingPoint(31, 129)).unwrap();
    assert_fields(&solver, term, (true, (1u64 << 31) - 1, u128::MAX, 31, 129));
    // A lossless value carrier does not override the existing API eb<=31 bound.
    let outside_api = wide(true, u64::MAX, u128::MAX, 64, 129);
    assert!(value_to_term(&mut solver, &outside_api, &Sort::FloatingPoint(64, 129)).is_none());
    // The old variant must take the same unsigned path, even above i64::MAX.
    let narrow = ModelValue::FloatingPoint {
        sign: false,
        exponent: 123,
        significand: u64::MAX,
        eb: 15,
        sb: 65,
    };
    let term =
        super::super::model_value_to_term(&mut solver, &narrow, &Sort::FloatingPoint(15, 65))
            .unwrap();
    assert_fields(&solver, term, (false, 123, u128::from(u64::MAX), 15, 65));
}

#[test]
fn snapshot_transfer_rejects_malformed_fields_and_declared_sorts() {
    let mut solver = Solver::new(Logic::QfFp);
    for (value, sort) in [
        (
            wide(false, 1 << 15, 0, 15, 113),
            Sort::FloatingPoint(15, 113),
        ),
        (
            wide(false, 0, 1u128 << 112, 15, 113),
            Sort::FloatingPoint(15, 113),
        ),
        (wide(false, 0, 1, 15, 113), Sort::FloatingPoint(15, 114)),
        (wide(false, 0, 1, 15, 113), Sort::bitvec(128)),
        (wide(false, 0, 1, 15, 113), Sort::Bool),
        (wide(false, 0, 0, 1, 113), Sort::FloatingPoint(1, 113)),
        (wide(false, 0, 0, 15, 1), Sort::FloatingPoint(15, 1)),
        (wide(false, 0, 0, 65, 113), Sort::FloatingPoint(65, 113)),
        (wide(false, 0, 0, 15, 130), Sort::FloatingPoint(15, 130)),
        (
            wide(false, 0, 1u128 << 64, 15, 65),
            Sort::FloatingPoint(15, 65),
        ),
    ] {
        assert!(
            value_to_term(&mut solver, &value, &sort).is_none(),
            "{value:?} at {sort:?}"
        );
        assert!(super::super::model_value_to_term(&mut solver, &value, &sort).is_none());
    }
    assert!(value_to_term(
        &mut solver,
        &ModelValue::Bool(false),
        &Sort::FloatingPoint(15, 113)
    )
    .is_none());
    let fresh = wide(false, 0x3fff, 1u128 << 111, 15, 113);
    let term = value_to_term(&mut solver, &fresh, &Sort::FloatingPoint(15, 113)).unwrap();
    assert_fields(&solver, term, (false, 0x3fff, 1u128 << 111, 15, 113));
}
