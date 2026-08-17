// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::mem::size_of;

use num_bigint::BigInt;
use num_rational::BigRational;

use super::*;
use crate::proof_validation::verify_farkas_conflict_lits_full;
use crate::{Sort, Symbol, TermId};

fn twenty_two_row_fixture() -> (TermStore, Vec<TheoryLit>, FarkasAnnotation) {
    let mut terms = TermStore::new();
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let mut conflict = Vec::new();
    for index in 0..11 {
        let variable = terms.mk_var(format!("metered_farkas_{index}"), Sort::Int);
        let mut expression = variable;
        for _ in 0..4 {
            expression = terms.mk_app(Symbol::named("+"), [expression, zero], Sort::Int);
        }
        conflict.push(TheoryLit::new(terms.mk_le(expression, zero), true));
        conflict.push(TheoryLit::new(terms.mk_ge(expression, one), true));
    }
    let farkas = FarkasAnnotation::from_ints(&[1_i64; 22]);
    (terms, conflict, farkas)
}

fn parser_surface_terms(terms: &mut TermStore) -> (Vec<TermId>, TermId, TermId) {
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let half = terms.mk_rational(BigRational::new(BigInt::from(1), BigInt::from(2)));
    let x = terms.mk_var("metered_diff_x", Sort::Int);
    let y = terms.mk_var("metered_diff_y", Sort::Int);
    let real = terms.mk_var("metered_diff_real", Sort::Real);
    let guard = terms.mk_var("metered_diff_guard", Sort::Bool);

    let empty_sum = terms.mk_app(Symbol::named("+"), Vec::<TermId>::new(), Sort::Int);
    let sum = terms.mk_app(Symbol::named("+"), [x, one, y], Sort::Int);
    let repeated_sum = terms.mk_app(Symbol::named("+"), [x, x], Sort::Int);
    let reversed_sum = terms.mk_app(Symbol::named("+"), [y, x], Sort::Int);
    let negated = terms.mk_app(Symbol::named("-"), [x], Sort::Int);
    let cancelling_sum = terms.mk_app(Symbol::named("+"), [x, negated], Sort::Int);
    let difference = terms.mk_app(Symbol::named("-"), [x, y, one], Sort::Int);
    let empty_subtract = terms.mk_app(Symbol::named("-"), Vec::<TermId>::new(), Sort::Int);
    let empty_product = terms.mk_app(Symbol::named("*"), Vec::<TermId>::new(), Sort::Int);
    let constant_product = terms.mk_app(Symbol::named("*"), [two, one], Sort::Int);
    let scaled = terms.mk_app(Symbol::named("*"), [two, x], Sort::Int);
    let zero_scaled = terms.mk_app(Symbol::named("*"), [zero, x], Sort::Int);
    let nonlinear = terms.mk_app(Symbol::named("*"), [x, y], Sort::Int);
    let quotient = terms.mk_app(Symbol::named("/"), [x, two], Sort::Int);
    let zero_divisor = terms.mk_app(Symbol::named("/"), [x, zero], Sort::Int);
    let symbolic_divisor = terms.mk_app(Symbol::named("/"), [x, y], Sort::Int);
    let short_quotient = terms.mk_app(Symbol::named("/"), [x], Sort::Int);
    let opaque_named = terms.mk_app(Symbol::named("metered_opaque"), [x], Sort::Int);
    let opaque_indexed = terms.mk_app(Symbol::indexed("metered_indexed", vec![3]), [x], Sort::Int);
    let ite = terms.mk_ite_raw(guard, x, y);
    let truth = terms.mk_bool(true);

    (
        vec![
            zero,
            one,
            half,
            x,
            real,
            empty_sum,
            sum,
            repeated_sum,
            reversed_sum,
            negated,
            cancelling_sum,
            difference,
            empty_subtract,
            empty_product,
            constant_product,
            scaled,
            zero_scaled,
            nonlinear,
            quotient,
            zero_divisor,
            symbolic_divisor,
            short_quotient,
            opaque_named,
            opaque_indexed,
            ite,
            truth,
        ],
        zero,
        real,
    )
}

fn assert_matches_full_validator(terms: &TermStore, conflict: &[TheoryLit], coefficients: &[i64]) {
    let farkas = FarkasAnnotation::from_ints(coefficients);
    let expected = verify_farkas_conflict_lits_full(terms, conflict, &farkas);
    let mut progress = |_: usize, _: usize| true;
    let actual =
        verify_pure_inequality_farkas_with_progress(terms, conflict, &farkas, &mut progress);
    assert_eq!(
        actual, expected,
        "conflict={conflict:?}, coefficients={coefficients:?}"
    );
}

#[test]
fn vector_reserve_charges_each_actual_target_capacity_and_polls() {
    let (mut charged_bytes, mut polls) = (0usize, 0usize);
    let mut values = Vec::<u64>::new();
    let (first_capacity, second_capacity);
    {
        let mut progress = |_: usize, bytes: usize| {
            charged_bytes = charged_bytes.checked_add(bytes).expect("test charge fits");
            polls += 1;
            true
        };
        let mut meter = ProgressMeter::new(&mut progress);
        meter
            .reserve_vec(&mut values, 1)
            .expect("first reserve succeeds");
        first_capacity = values.capacity();
        values.resize(first_capacity, 0);
        meter
            .reserve_vec(&mut values, 1)
            .expect("growth reserve succeeds");
        second_capacity = values.capacity();
        meter
            .reserve_vec(&mut values, 0)
            .expect("no-op reserve polls");
    }
    assert_eq!(
        charged_bytes,
        first_capacity
            .checked_add(second_capacity)
            .and_then(|slots| slots.checked_mul(size_of::<u64>()))
            .expect("test capacities fit")
    );
    assert!(polls >= 5, "both allocations and the no-op must poll");
}

#[test]
fn metered_parser_and_normalization_match_full_validator_on_admitted_surface() {
    let mut terms = TermStore::new();
    let (expressions, zero, real) = parser_surface_terms(&mut terms);
    let mut first_atom = None;
    for expression in expressions {
        for predicate in ["<", "<=", ">", ">="] {
            let atom = terms.mk_app(Symbol::named(predicate), [expression, zero], Sort::Bool);
            first_atom.get_or_insert(atom);
            let negated = terms.mk_not_raw(atom);
            let double_negated = terms.mk_not_raw(negated);
            for literal in [
                TheoryLit::new(atom, true),
                TheoryLit::new(atom, false),
                TheoryLit::new(negated, true),
                TheoryLit::new(negated, false),
                TheoryLit::new(double_negated, true),
            ] {
                assert_matches_full_validator(&terms, &[literal], &[1]);
            }
        }
    }

    let atom = first_atom.expect("the parser surface is non-empty");
    assert_matches_full_validator(&terms, &[TheoryLit::new(atom, true)], &[]);
    assert_matches_full_validator(&terms, &[TheoryLit::new(atom, true)], &[0]);
    assert_matches_full_validator(&terms, &[TheoryLit::new(atom, true)], &[-1]);

    for variable in [terms.mk_var("metered_diff_strict_int", Sort::Int), real] {
        let lt = terms.mk_app(Symbol::named("<"), [variable, zero], Sort::Bool);
        let ge = terms.mk_app(Symbol::named(">="), [variable, zero], Sort::Bool);
        assert_matches_full_validator(
            &terms,
            &[TheoryLit::new(lt, true), TheoryLit::new(ge, true)],
            &[1, 1],
        );
    }
}

#[test]
fn twenty_two_row_meter_is_accepting_and_exactly_replayable() {
    let (terms, conflict, farkas) = twenty_two_row_fixture();
    verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect("baseline full validator accepts the 22-row contradiction");

    let (mut total_work, mut total_bytes) = (0usize, 0usize);
    verify_pure_inequality_farkas_with_progress(&terms, &conflict, &farkas, &mut |work, bytes| {
        total_work = total_work
            .checked_add(work)
            .expect("fixture work fits usize");
        total_bytes = total_bytes
            .checked_add(bytes)
            .expect("fixture bytes fit usize");
        true
    })
    .expect("the progress-metered validator preserves acceptance");
    assert!(total_work > conflict.len());
    assert!(total_bytes > conflict.len() * size_of::<TheoryLit>());

    let (mut work_left, mut bytes_left) = (total_work, total_bytes);
    verify_pure_inequality_farkas_with_progress(&terms, &conflict, &farkas, &mut |work, bytes| {
        let (Some(next_work), Some(next_bytes)) =
            (work_left.checked_sub(work), bytes_left.checked_sub(bytes))
        else {
            return false;
        };
        work_left = next_work;
        bytes_left = next_bytes;
        true
    })
    .expect("the exactly measured envelope must accept the same certificate");
    assert_eq!((work_left, bytes_left), (0, 0));

    let mut used = 0usize;
    let error =
        verify_pure_inequality_farkas_with_progress(&terms, &conflict, &farkas, &mut |work, _| {
            let Some(next) = used.checked_add(work) else {
                return false;
            };
            if next >= total_work {
                return false;
            }
            used = next;
            true
        })
        .expect_err("one work unit below the measured total must refuse");
    assert_eq!(error, FarkasValidationError::ResourceLimit);

    let mut used = 0usize;
    let error =
        verify_pure_inequality_farkas_with_progress(&terms, &conflict, &farkas, &mut |_, bytes| {
            let Some(next) = used.checked_add(bytes) else {
                return false;
            };
            if next >= total_bytes {
                return false;
            }
            used = next;
            true
        })
        .expect_err("one byte below the measured total must refuse");
    assert_eq!(error, FarkasValidationError::ResourceLimit);
}
