// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{Sort, Symbol, TermId, TermStore};

use super::{guard_bound_seeds, seedable};

fn app(terms: &mut TermStore, name: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(name), args, sort)
}

/// `(=> (and (<= 0 s) (<= s t)) (<= (+ s v) 1))` with `s` the binder.
#[test]
fn interval_guard_names_both_end_points_in_order() {
    let mut terms = TermStore::new();
    let s = terms.mk_var("s", Sort::Real);
    let t = terms.mk_var("t", Sort::Real);
    let v = terms.mk_var("v", Sort::Real);
    let zero = terms.mk_rational(num_rational::BigRational::from_integer(0.into()));
    let one = terms.mk_rational(num_rational::BigRational::from_integer(1.into()));
    let lo = app(&mut terms, "<=", &[zero, s], Sort::Bool);
    let hi = app(&mut terms, "<=", &[s, t], Sort::Bool);
    let guard = app(&mut terms, "and", &[lo, hi], Sort::Bool);
    let sum = app(&mut terms, "+", &[s, v], Sort::Real);
    let goal = app(&mut terms, "<=", &[sum, one], Sort::Bool);
    let body = app(&mut terms, "=>", &[guard, goal], Sort::Bool);
    assert_eq!(
        guard_bound_seeds(&terms, body, "s", &Sort::Real),
        vec![zero, t]
    );
}

/// A comparison whose other side mentions the binder is no bound, and a
/// comparison that does not mention the binder bounds nothing.
#[test]
fn binder_dependent_and_binder_free_comparisons_are_not_seeds() {
    let mut terms = TermStore::new();
    let s = terms.mk_var("s", Sort::Real);
    let t = terms.mk_var("t", Sort::Real);
    let twice = app(&mut terms, "+", &[s, s], Sort::Real);
    let self_bound = app(&mut terms, "<=", &[s, twice], Sort::Bool);
    let ground = app(&mut terms, "<=", &[t, t], Sort::Bool);
    let product = app(&mut terms, "*", &[s, t], Sort::Real);
    let nonlinear = app(&mut terms, "<=", &[product, t], Sort::Bool);
    let body = app(
        &mut terms,
        "and",
        &[self_bound, ground, nonlinear],
        Sort::Bool,
    );
    assert!(guard_bound_seeds(&terms, body, "s", &Sort::Real).is_empty());
}

/// The scan reads the Boolean skeleton under `not` and `or` and never enters
/// a nested binder, whose atoms bound a different variable.
#[test]
fn seeds_are_found_under_negation_and_never_under_a_nested_binder() {
    let mut terms = TermStore::new();
    let s = terms.mk_var("s", Sort::Real);
    let t = terms.mk_var("t", Sort::Real);
    let u = terms.mk_var("u", Sort::Real);
    let lt = app(&mut terms, "<", &[t, s], Sort::Bool);
    let negated = terms.mk_not(lt);
    let inner_atom = app(&mut terms, "<=", &[s, u], Sort::Bool);
    let nested = terms.mk_forall(vec![("w".to_string(), Sort::Real)], inner_atom);
    let body = app(&mut terms, "or", &[negated, nested], Sort::Bool);
    assert_eq!(guard_bound_seeds(&terms, body, "s", &Sort::Real), vec![t]);
}

/// Only a universal over nonlinear arithmetic is seeded: the linear interval
/// universal is left to the quantified-LRA lanes.
#[test]
fn only_nonlinear_single_real_binder_bodies_are_seedable() {
    let mut terms = TermStore::new();
    let s = terms.mk_var("s", Sort::Real);
    let t = terms.mk_var("t", Sort::Real);
    let v = terms.mk_var("v", Sort::Real);
    let zero = terms.mk_rational(num_rational::BigRational::from_integer(0.into()));
    let lo = app(&mut terms, "<=", &[zero, s], Sort::Bool);
    let hi = app(&mut terms, "<=", &[s, t], Sort::Bool);
    let guard = app(&mut terms, "and", &[lo, hi], Sort::Bool);
    let vars = vec![("s".to_string(), Sort::Real)];

    let sum = app(&mut terms, "+", &[s, v], Sort::Real);
    let linear_goal = app(&mut terms, "<=", &[sum, t], Sort::Bool);
    let linear = app(&mut terms, "=>", &[guard, linear_goal], Sort::Bool);
    assert!(seedable(&terms, &vars, linear).is_empty());

    let two = terms.mk_rational(num_rational::BigRational::from_integer(2.into()));
    let scaled = app(&mut terms, "*", &[two, s], Sort::Real);
    let scaled_goal = app(&mut terms, "<=", &[scaled, t], Sort::Bool);
    let scaled_body = app(&mut terms, "=>", &[guard, scaled_goal], Sort::Bool);
    assert!(seedable(&terms, &vars, scaled_body).is_empty());

    let product = app(&mut terms, "*", &[s, v], Sort::Real);
    let nonlinear_goal = app(&mut terms, "<=", &[product, t], Sort::Bool);
    let nonlinear = app(&mut terms, "=>", &[guard, nonlinear_goal], Sort::Bool);
    assert_eq!(seedable(&terms, &vars, nonlinear), vec![zero, t]);

    let int_vars = vec![("s".to_string(), Sort::Int)];
    assert!(seedable(&terms, &int_vars, nonlinear).is_empty());
    let two_vars = vec![("s".to_string(), Sort::Real), ("r".to_string(), Sort::Real)];
    assert!(seedable(&terms, &two_vars, nonlinear).is_empty());
}
