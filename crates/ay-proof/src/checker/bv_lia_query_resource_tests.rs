// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Resource-accounting regressions for the bounded BV/LIA interpreter.

use std::collections::HashMap;

use ay_core::{Sort, TermStore};
use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::*;

fn assert_resource(error: BvLiaUnsatAuthenticationError, expected: &'static str) {
    assert!(matches!(
        error,
        BvLiaUnsatAuthenticationError::ResourceLimit { resource } if resource == expected
    ));
}

#[test]
fn bulk_meter_charge_checks_every_crossed_deadline_boundary() {
    let mut meter = Meter {
        work: 1,
        deadline: Some(Instant::now()),
    };
    let error = meter
        .charge(1 << 14)
        .expect_err("a bulk charge crossing a checkpoint must observe the deadline");
    assert_resource(error, "caller deadline");
}

#[test]
fn dimension_member_work_is_charged_before_environment_mutation() {
    let mut terms = TermStore::new();
    let members: Vec<_> = (0..3)
        .map(|index| terms.mk_var(format!("dimension_member_{index}"), Sort::Int))
        .collect();
    let dimension = Dimension::IntClass {
        members,
        lower: BigInt::zero(),
        count: 1,
    };
    let mut checker = QueryChecker::new(&terms, None);
    checker.meter.work = MAX_WORK - 1;
    let mut env = Environment::default();

    let error = checker
        .assign_dimension(&dimension, 0, &mut env)
        .expect_err("member preflight must exhaust the remaining work before inserts");
    assert_resource(error, "deterministic work budget");
    assert!(env.ints.is_empty());
    assert_eq!(env.int_limbs, 0);
}

#[test]
fn propagated_class_work_is_charged_before_environment_mutation() {
    let mut terms = TermStore::new();
    let members: Vec<_> = (0..3)
        .map(|index| terms.mk_var(format!("propagated_member_{index}"), Sort::Int))
        .collect();
    let class_of = members.iter().copied().map(|term| (term, 0)).collect();
    let classes = IntClasses {
        class_of,
        members: vec![members.clone()],
        bounds: vec![ClassBounds::default()],
    };
    let mut checker = QueryChecker::new(&terms, None);
    checker.meter.work = MAX_WORK - 2;
    let mut env = Environment::default();

    let error = checker
        .assign_value(members[0], Value::Int(BigInt::zero()), &mut env, &classes)
        .expect_err("propagation must meter the complete equality class before inserts");
    assert_resource(error, "deterministic work budget");
    assert!(env.ints.is_empty());
    assert_eq!(env.int_limbs, 0);
}

#[test]
fn integer_clone_payload_is_charged_before_environment_mutation() {
    let mut terms = TermStore::new();
    let members: Vec<_> = (0..2)
        .map(|index| terms.mk_var(format!("cloned_member_{index}"), Sort::Int))
        .collect();
    let value = BigInt::one() << 511_u32;
    let mut checker = QueryChecker::new(&terms, None);
    checker.meter.work = MAX_WORK - 10;
    let mut env = Environment::default();

    let error = checker
        .assign_int_members(&members, &value, &mut env)
        .expect_err("the complete clone payload must be charged before inserts");
    assert_resource(error, "deterministic work budget");
    assert!(env.ints.is_empty());
    assert_eq!(env.int_limbs, 0);
}

#[test]
fn integer_environment_storage_is_atomic_bounded_and_resettable() {
    let mut terms = TermStore::new();
    let small_members: Vec<_> = (0..2)
        .map(|index| terms.mk_var(format!("stored_member_{index}"), Sort::Int))
        .collect();
    let mut checker = QueryChecker::new(&terms, None);
    let mut env = Environment::default();
    let seven = BigInt::from(7_u8);

    assert_eq!(
        checker
            .assign_int_members(&small_members, &seven, &mut env)
            .expect("small assignment fits"),
        EnforceOutcome::Changed
    );
    assert_eq!(env.int_limbs, 2);
    assert_eq!(
        checker
            .assign_int_members(&small_members, &seven, &mut env)
            .expect("idempotent assignment fits"),
        EnforceOutcome::Stable
    );
    assert_eq!(env.int_limbs, 2);
    assert_eq!(
        checker
            .assign_int_members(&small_members, &BigInt::from(8_u8), &mut env)
            .expect("a logical conflict is not a resource failure"),
        EnforceOutcome::Conflict
    );
    assert_eq!(env.int_limbs, 2);
    env.clear_ints();
    assert!(env.ints.is_empty());
    assert_eq!(env.int_limbs, 0);

    let repeated = [small_members[0], small_members[0]];
    assert_eq!(
        checker
            .assign_int_members(&repeated, &seven, &mut env)
            .expect("duplicate internal members are counted exactly once"),
        EnforceOutcome::Changed
    );
    assert_eq!(env.ints.len(), 1);
    assert_eq!(env.int_limbs, 1);
}

#[test]
fn integer_environment_rejects_aggregate_payload_before_cloning() {
    let mut terms = TermStore::new();
    let members: Vec<_> = (0..=MAX_LIVE_INTEGER_LIMBS / 1024)
        .map(|index| terms.mk_var(format!("wide_member_{index}"), Sort::Int))
        .collect();
    let wide = BigInt::one() << (MAX_INTEGER_BITS - 1);
    let mut checker = QueryChecker::new(&terms, None);
    let mut env = Environment::default();

    let error = checker
        .assign_int_members(&members, &wide, &mut env)
        .expect_err("aggregate wide values must exceed the live payload cap");
    assert_resource(error, "live integer storage");
    assert!(env.ints.is_empty());
    assert_eq!(env.int_limbs, 0);
}

#[test]
fn persistent_integer_payload_bounds_classes_and_dimensions() {
    let mut terms = TermStore::new();
    let wide = BigInt::one() << (MAX_INTEGER_BITS - 1);
    let wide_limbs = integer_evaluation::integer_limb_units(&wide);
    let class_count = usize::try_from(MAX_LIVE_INTEGER_LIMBS / (2 * wide_limbs))
        .expect("the static payload cap fits usize");
    let wide_term = terms.mk_int(wide.clone());
    let mut variables = Vec::with_capacity(class_count);
    let mut assertions = Vec::with_capacity(class_count);
    for index in 0..class_count {
        let variable = terms.mk_var(format!("persistent_member_{index}"), Sort::Int);
        variables.push(variable);
        assertions.push(terms.mk_eq(variable, wide_term));
    }

    let mut checker = QueryChecker::new(&terms, None);
    let classes = checker
        .build_int_classes(&variables, &assertions)
        .expect("the exact persistent payload cap is admitted");
    assert_eq!(checker.retained_int_limbs, MAX_LIVE_INTEGER_LIMBS);

    let mut additional = ClassBounds::default();
    let error = checker
        .tighten_lower_bound_from_ref(&mut additional, &wide)
        .expect_err("another class bound must be rejected before its clone is retained");
    assert_resource(error, "live integer storage");
    assert!(additional.lower.is_none());
    assert_eq!(checker.retained_int_limbs, MAX_LIVE_INTEGER_LIMBS);

    let error = checker
        .build_dimensions(&classes, &[], &[], &Environment::default())
        .expect_err("dimension lower clones share the persistent payload cap");
    assert_resource(error, "live integer storage");
    assert_eq!(checker.retained_int_limbs, MAX_LIVE_INTEGER_LIMBS);
}

#[test]
fn owned_integer_arithmetic_preflights_magnitude_and_limb_work() {
    let terms = TermStore::new();
    let mut checker = QueryChecker::new(&terms, None);
    let max_bits = BigInt::one() << (MAX_INTEGER_BITS - 1);
    let error = checker
        .add_bounded_ints(&max_bits, &max_bits)
        .expect_err("addition may not create a value above the integer cap");
    assert_resource(error, "integer magnitude");
    let error = checker
        .subtract_bounded_ints(&max_bits, &(-&max_bits))
        .expect_err("subtraction may not create a value above the integer cap");
    assert_resource(error, "integer magnitude");

    let oversized = BigInt::one() << MAX_INTEGER_BITS;
    let error = checker
        .subtract_bounded_ints(&oversized, &BigInt::zero())
        .expect_err("subtraction must reject an oversized operand before arithmetic");
    assert_resource(error, "integer magnitude");
    let error = checker
        .abs_bounded_int(-oversized)
        .expect_err("abs must reject an oversized operand before arithmetic");
    assert_resource(error, "integer magnitude");

    let dividend = (BigInt::one() << 1023_u32) + BigInt::one();
    let divisor = (BigInt::one() << 1022_u32) + BigInt::one();
    checker.meter.work = MAX_WORK - 200;
    let error = checker
        .modulo_bounded_ints(&dividend, &divisor)
        .expect_err("division work must be charged before computing the residue");
    assert_resource(error, "deterministic work budget");

    checker.meter.work = MAX_WORK - 8;
    let error = checker
        .residue_bounded_int(&dividend, 8)
        .expect_err("int2bv residue work must scale with the source magnitude");
    assert_resource(error, "deterministic work budget");
}

#[test]
fn integer_values_are_never_retained_in_the_evaluation_memo() {
    let mut terms = TermStore::new();
    let integer = terms.mk_int(BigInt::from(42_u8));
    let boolean = terms.mk_bool(true);
    let mut checker = QueryChecker::new(&terms, None);
    let env = Environment::default();
    let mut memo = HashMap::new();

    assert_eq!(
        checker
            .eval_value(integer, &env, &mut memo, 0)
            .expect("integer evaluation fits"),
        Some(Value::Int(BigInt::from(42_u8)))
    );
    assert!(!memo.contains_key(&integer));
    assert_eq!(
        checker
            .eval_value(boolean, &env, &mut memo, 0)
            .expect("Boolean evaluation fits"),
        Some(Value::Bool(true))
    );
    assert_eq!(memo.get(&boolean), Some(&Value::Bool(true)));
}
