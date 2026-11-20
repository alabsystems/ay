// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_core::{Sort, Symbol, TermId, TermStore};
use num_bigint::BigInt;
use num_traits::One;

use super::super::{
    authenticate_bv_lia_unsat_query, BvLiaUnsatAuthenticationError, QueryChecker, MAX_WORK,
};

fn or(terms: &mut TermStore, args: &[TermId]) -> TermId {
    terms.mk_app(Symbol::named("or"), args.to_vec(), Sort::Bool)
}

fn point(terms: &mut TermStore, var: TermId, value: i64) -> TermId {
    let value = terms.mk_int(value.into());
    terms.mk_eq(var, value)
}

fn block(terms: &mut TermStore, var: TermId, value: i64) -> TermId {
    let point = point(terms, var, value);
    terms.mk_not(point)
}

#[test]
fn finite_choice_hull_keeps_gaps_and_checks_every_original_alternative() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("choice", Sort::Int);
    let choices: Vec<_> = [-3, -1, 1, 3]
        .into_iter()
        .map(|value| point(&mut terms, x, value))
        .collect();
    let nested = or(&mut terms, &choices[..2]);
    let domain = or(&mut terms, &[nested, choices[2], choices[3]]);
    let mut roots = vec![domain];
    roots.extend(
        [-3, -1, 1, 3]
            .into_iter()
            .map(|value| block(&mut terms, x, value)),
    );
    let evidence = authenticate_bv_lia_unsat_query(&terms, &roots, None)
        .expect("the original OR rejects all gaps, including zero");
    assert!(evidence.is_current_for(&terms, &roots));
}

#[test]
fn finite_choice_missing_last_alternative_is_satisfiable() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("choice", Sort::Int);
    let minus_two = point(&mut terms, x, -2);
    let one = point(&mut terms, x, 1);
    let four = terms.mk_int(4.into());
    // Preserve original operand order; mk_eq canonicalizes it by TermId.
    let reversed = terms.mk_app(Symbol::named("="), vec![four, x], Sort::Bool);
    let domain = or(&mut terms, &[minus_two, one, reversed]);
    let roots = [domain, block(&mut terms, x, -2), block(&mut terms, x, 1)];
    assert!(matches!(
        authenticate_bv_lia_unsat_query(&terms, &roots, None),
        Err(BvLiaUnsatAuthenticationError::Satisfiable)
    ));
}

#[test]
fn finite_choice_mixed_variables_or_non_equality_cannot_narrow_a_prefix() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let p = terms.mk_var("p", Sort::Bool);
    let x_one = point(&mut terms, x, 1);
    let y_two = point(&mut terms, y, 2);
    let x_zero = point(&mut terms, x, 0);
    // DFS sees x=1 first. Neither later branch permits committing that bound.
    let mixed = or(&mut terms, &[y_two, x_one]);
    let roots = [mixed, x_zero, y_two];
    assert!(matches!(
        authenticate_bv_lia_unsat_query(&terms, &roots, None),
        Err(BvLiaUnsatAuthenticationError::Satisfiable)
    ));
    let non_equality = or(&mut terms, &[p, x_one]);
    let roots = [non_equality, x_zero, y_two, p];
    assert!(matches!(
        authenticate_bv_lia_unsat_query(&terms, &roots, None),
        Err(BvLiaUnsatAuthenticationError::Satisfiable)
    ));
}

#[test]
fn negated_choice_does_not_bound_an_original_integer() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let minus_one = point(&mut terms, x, -1);
    let one = point(&mut terms, x, 1);
    let domain = or(&mut terms, &[minus_one, one]);
    let outside = terms.mk_not(domain);
    let three = point(&mut terms, x, 3);
    assert!(matches!(
        authenticate_bv_lia_unsat_query(&terms, &[outside, three], None),
        Err(BvLiaUnsatAuthenticationError::Satisfiable)
    ));
}

#[test]
fn finite_choice_zero_gap_is_rejected_by_original_source_even_after_division() {
    let mut terms = TermStore::new();
    let divisor = terms.mk_var("divisor", Sort::Int);
    let minus_one = point(&mut terms, divisor, -1);
    let one_choice = point(&mut terms, divisor, 1);
    let domain = or(&mut terms, &[minus_one, one_choice]);
    let one = terms.mk_int(1.into());
    let quotient = terms.mk_intdiv(one, divisor);
    let zero = terms.mk_int(0.into());
    let impossible = terms.mk_eq(quotient, zero);
    // The conservative hull includes zero. A zero-divisor interpretation
    // cannot satisfy the complete original OR, even when that root is last.
    authenticate_bv_lia_unsat_query(&terms, &[impossible, domain], None)
        .expect("no original nonzero divisor gives quotient zero");
}

#[test]
fn finite_choice_wide_sparse_hull_keeps_existing_assignment_limit() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("wide_choice", Sort::Int);
    let wide = BigInt::one() << 140_u32;
    let lo = terms.mk_int(-wide.clone());
    let hi = terms.mk_int(wide);
    let lo_choice = terms.mk_eq(x, lo);
    let hi_choice = terms.mk_eq(x, hi);
    let domain = or(&mut terms, &[lo_choice, hi_choice]);
    let no_lo = terms.mk_not(lo_choice);
    let no_hi = terms.mk_not(hi_choice);
    assert!(matches!(
        authenticate_bv_lia_unsat_query(&terms, &[domain, no_lo, no_hi], None),
        Err(BvLiaUnsatAuthenticationError::UnsupportedFragment { .. })
            | Err(BvLiaUnsatAuthenticationError::ResourceLimit { .. })
    ));
}

#[test]
fn finite_choice_original_work_refusal_precedes_bounds_and_scratch() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("choice", Sort::Int);
    let one = point(&mut terms, x, 1);
    let two = point(&mut terms, x, 2);
    let domain = or(&mut terms, &[one, two]);
    let mut checker = QueryChecker::new(&terms, None);
    let mut classes = checker.build_int_classes(&[x], &[]).unwrap();
    checker.meter.work = MAX_WORK;
    assert!(matches!(
        checker.record_int_choice_bound(domain, &mut classes),
        Err(BvLiaUnsatAuthenticationError::ResourceLimit { .. })
    ));
    let class = classes.class_of.get(&x).copied().unwrap();
    assert!(classes.bounds[class].lower.is_none());
    assert!(classes.bounds[class].upper.is_none());
}
