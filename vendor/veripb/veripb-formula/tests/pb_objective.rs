use malachite_bigint::BigInt;
use veripb_formula::prelude::*;

#[test]
fn init_objective() {
    let terms = vec![
        GeneralPBTerm::new(BigInt::from(17), Lit::from_var(0, false)),
        GeneralPBTerm::new(BigInt::from(42), Lit::from_var(1, true)),
        GeneralPBTerm::new(BigInt::from(75), Lit::from_var(2, false)),
    ];

    let objective = PBObjective::from_terms(terms, BigInt::from(0), false);

    assert_eq!(objective.constant, BigInt::from(0));
    let mut values = objective.terms.values();
    assert_eq!(values.next().unwrap().coeff, BigInt::from(17));
    assert_eq!(values.next().unwrap().coeff, BigInt::from(42));
    assert_eq!(values.next().unwrap().coeff, BigInt::from(75));
}

#[test]
fn init_objective_duplicate_literal() {
    let terms = vec![
        GeneralPBTerm::new(BigInt::from(17), Lit::from_var(0, false)),
        GeneralPBTerm::new(BigInt::from(42), Lit::from_var(1, true)),
        GeneralPBTerm::new(BigInt::from(75), Lit::from_var(2, false)),
        GeneralPBTerm::new(BigInt::from(33), Lit::from_var(0, false)),
    ];

    let objective = PBObjective::from_terms(terms, BigInt::from(0), false);

    assert_eq!(objective.constant, BigInt::from(0));
    let mut values = objective.terms.values();
    assert_eq!(values.next().unwrap().coeff, BigInt::from(50));
    assert_eq!(values.next().unwrap().coeff, BigInt::from(42));
    assert_eq!(values.next().unwrap().coeff, BigInt::from(75));
}

#[test]
fn init_objective_opposing_literals() {
    let terms = vec![
        GeneralPBTerm::new(BigInt::from(17), Lit::from_var(0, false)),
        GeneralPBTerm::new(BigInt::from(42), Lit::from_var(1, true)),
        GeneralPBTerm::new(BigInt::from(75), Lit::from_var(2, false)),
        GeneralPBTerm::new(BigInt::from(33), Lit::from_var(0, true)),
    ];

    let objective = PBObjective::from_terms(terms, BigInt::from(0), false);

    assert_eq!(objective.constant, BigInt::from(17));
    let mut values = objective.terms.values();
    assert_eq!(
        *values.next().unwrap(),
        GeneralPBTerm::new(BigInt::from(16), Lit::from_var(0, true))
    );
    assert_eq!(values.next().unwrap().coeff, BigInt::from(42));
    assert_eq!(values.next().unwrap().coeff, BigInt::from(75));
}

#[test]
fn init_objective_negative_coeff() {
    let terms = vec![
        GeneralPBTerm::new(BigInt::from(-17), Lit::from_var(0, false)),
        GeneralPBTerm::new(BigInt::from(42), Lit::from_var(1, true)),
        GeneralPBTerm::new(BigInt::from(-75), Lit::from_var(2, false)),
        GeneralPBTerm::new(BigInt::from(33), Lit::from_var(0, true)),
    ];

    let objective = PBObjective::from_terms(terms, BigInt::from(0), false);

    assert_eq!(objective.constant, BigInt::from(-92));
    let mut values = objective.terms.values();
    assert_eq!(
        *values.next().unwrap(),
        GeneralPBTerm::new(BigInt::from(50), Lit::from_var(0, true))
    );
    assert_eq!(values.next().unwrap().coeff, BigInt::from(42));
    assert_eq!(values.next().unwrap().coeff, BigInt::from(75));
}

#[test]
fn init_objective_negative_coeff_opposing_lit() {
    let terms = vec![
        GeneralPBTerm::new(BigInt::from(-17), Lit::from_var(0, true)),
        GeneralPBTerm::new(BigInt::from(42), Lit::from_var(1, true)),
        GeneralPBTerm::new(BigInt::from(-75), Lit::from_var(2, false)),
        GeneralPBTerm::new(BigInt::from(33), Lit::from_var(0, true)),
    ];

    let objective = PBObjective::from_terms(terms, BigInt::from(0), false);

    assert_eq!(objective.constant, BigInt::from(-75));
    let mut values = objective.terms.values();
    assert_eq!(
        *values.next().unwrap(),
        GeneralPBTerm::new(BigInt::from(16), Lit::from_var(0, true))
    );
    assert_eq!(values.next().unwrap().coeff, BigInt::from(42));
    assert_eq!(values.next().unwrap().coeff, BigInt::from(75));
}

#[test]
fn compute_objective_value_complete_assignment() {
    let terms = vec![
        GeneralPBTerm::new(BigInt::from(17), Lit::from_var(0, false)),
        GeneralPBTerm::new(BigInt::from(42), Lit::from_var(1, true)),
        GeneralPBTerm::new(BigInt::from(75), Lit::from_var(2, false)),
        GeneralPBTerm::new(BigInt::from(33), Lit::from_var(3, true)),
        GeneralPBTerm::new(BigInt::from(42), Lit::from_var(4, true)),
    ];
    let objective = PBObjective::from_terms(terms, BigInt::from(0), false);
    let mut assignment = Assignment::<BooleanVar>::with_size(5);

    assignment.set_value(0, BoolValue::Assigned(true));
    assignment.set_value(1, BoolValue::Assigned(true));
    assignment.set_value(2, BoolValue::Assigned(false));
    assignment.set_value(3, BoolValue::Assigned(false));
    assignment.set_value(4, BoolValue::Assigned(false));

    assert_eq!(
        objective.evaluate(&assignment),
        Some(BigInt::from(17 + 33 + 42))
    );
}
