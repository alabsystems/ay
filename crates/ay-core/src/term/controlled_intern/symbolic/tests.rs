// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::term::RationalWrapper;
use num_bigint::BigInt;
use num_rational::BigRational;

#[test]
fn symbolic_intern_real_rational_retains_arbitrary_precision_and_actual_hash_work() {
    let mut terms = TermStore::new();
    let value = BigRational::new((BigInt::from(1) << 200) + BigInt::from(1), BigInt::from(3));
    let node = TermData::Const(Constant::Rational(RationalWrapper(value.clone())));
    let mut work = 0usize;
    let mut bytes = 0usize;
    let id = terms
        .try_intern_symbolic_with_progress(&node, &Sort::Real, &mut |w, b| {
            work += w;
            bytes += b;
            true
        })
        .unwrap();
    assert_eq!(terms.get(id), &node);
    assert_eq!(terms.sort(id), &Sort::Real);
    assert!(work > 200 && bytes > 200);
    let again = terms
        .try_intern_symbolic_with_progress(&node, &Sort::Real, &mut |_, _| true)
        .unwrap();
    assert_eq!(id, again);
}

#[test]
fn symbolic_intern_nested_array_and_wide_application_use_structural_typed_handles() {
    let mut terms = TermStore::new();
    let no = terms.mk_bool(false);
    let inner = Sort::array(Sort::Int, Sort::Bool);
    let outer = Sort::array(Sort::Real, inner.clone());
    let inner_value = terms
        .try_intern_symbolic_with_progress(
            &TermData::App(Symbol::named("const-array"), vec![no]),
            &inner,
            &mut |_, _| true,
        )
        .unwrap();
    let outer_value = terms
        .try_intern_symbolic_with_progress(
            &TermData::App(Symbol::named("const-array"), vec![inner_value]),
            &outer,
            &mut |_, _| true,
        )
        .unwrap();
    assert_eq!(terms.sort(outer_value), &outer);
    let args = vec![no; 256];
    assert!(terms
        .try_intern_symbolic_with_progress(
            &TermData::App(Symbol::named("and"), args),
            &Sort::Bool,
            &mut |_, _| true
        )
        .is_ok());
    assert_eq!(
        terms.try_intern_symbolic_with_progress(
            &TermData::App(Symbol::named("and"), vec![no; 257]),
            &Sort::Bool,
            &mut |_, _| true
        ),
        Err(ControlledTermInternError::UnsupportedFragment)
    );
    assert!(
        terms
            .try_intern_with_progress(
                &TermData::Const(Constant::Rational(RationalWrapper(
                    BigRational::from_integer(1.into())
                ))),
                &Sort::Real,
                &mut |_, _| true
            )
            .is_err(),
        "the ordinary fragment was not widened"
    );
}

#[test]
fn symbolic_intern_bad_child_variable_or_binder_never_acquires_a_handle() {
    let mut terms = TermStore::new();
    let before = terms.snapshot_stamp();
    for node in [
        TermData::App(Symbol::named("+"), vec![TermId(u32::MAX)]),
        TermData::Var("forged".to_owned(), 55),
        TermData::Forall(
            vec![("forged".to_owned(), Sort::Int)],
            terms.true_term(),
            vec![],
        ),
    ] {
        assert!(terms
            .try_intern_symbolic_with_progress(&node, &Sort::Bool, &mut |_, _| true)
            .is_err());
    }
    assert_eq!(before, terms.snapshot_stamp());
}

#[test]
fn symbolic_intern_ratio_comparison_depth_and_zero_denominator_refuse_before_arena_publication() {
    let mut terms = TermStore::new();
    let before = terms.snapshot_stamp();
    let mut a = BigInt::from(1);
    let mut b = BigInt::from(1);
    for _ in 0..300 {
        let next = &a + &b;
        a = b;
        b = next;
    }
    for value in [
        BigRational::new_raw(b, a),
        BigRational::new_raw(1.into(), 0.into()),
    ] {
        assert!(terms
            .try_intern_symbolic_with_progress(
                &TermData::Const(Constant::Rational(RationalWrapper(value))),
                &Sort::Real,
                &mut |_, _| true
            )
            .is_err());
    }
    assert_eq!(before, terms.snapshot_stamp());
}

#[test]
fn symbolic_intern_refused_external_owner_stays_refused_across_retry() {
    let mut terms = TermStore::new();
    let before = terms.snapshot_stamp();
    let node = TermData::Const(Constant::Rational(RationalWrapper(BigRational::new(
        1.into(),
        3.into(),
    ))));
    let mut left = 10usize;
    let mut progress = |work: usize, bytes: usize| {
        let next = work
            .checked_add(bytes)
            .and_then(|amount| left.checked_sub(amount));
        match next {
            Some(next) => {
                left = next;
                true
            }
            None => {
                left = 0;
                false
            }
        }
    };
    for _ in 0..2 {
        assert_eq!(
            terms.try_intern_symbolic_with_progress(&node, &Sort::Real, &mut progress),
            Err(ControlledTermInternError::ResourceLimit)
        );
    }
    assert_eq!(before, terms.snapshot_stamp());
}
