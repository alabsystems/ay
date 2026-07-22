// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::Symbol;
use ay_core::{Sort, TheoryLit};
use num_bigint::BigInt;

#[test]
fn length_bound_concat_has_nonzero_lower_bound() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let a = terms.mk_string("a".to_string());
    let concat = terms.mk_app(Symbol::named("str.++"), vec![x, a], Sort::String);

    let mut state = SolverState::new();
    state.register_term(&terms, concat);

    let ae = ArithEntail::new(&terms, &state);
    assert_eq!(ae.get_length_bound(concat, true), Some(1));
    assert_eq!(ae.get_length_bound(concat, false), None);
}

#[test]
fn constant_bounds_cover_add_and_sub() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let len_x = terms.mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let three = terms.mk_int(BigInt::from(3));
    let add = terms.mk_add(vec![len_x, two, three]);
    let sub = terms.mk_sub(vec![add, three]);

    let mut state = SolverState::new();
    state.register_term(&terms, len_x);

    let ae = ArithEntail::new(&terms, &state);
    assert_eq!(ae.get_constant_bound(add, true), Some(5));
    assert_eq!(ae.get_constant_bound(add, false), None);
    assert_eq!(ae.get_constant_bound(sub, true), Some(2));
}

#[test]
fn check_eq_uses_int_equalities_from_state() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let len_x = terms.mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let len_y = terms.mk_app(Symbol::named("str.len"), vec![y], Sort::Int);
    let len_x_eq_y = terms.mk_eq(len_x, len_y);

    let mut state = SolverState::new();
    state.assert_literal(&terms, len_x_eq_y, true);

    let ae = ArithEntail::new(&terms, &state);
    assert!(ae.check_eq(len_x, len_y));
    assert!(ae.check(len_x, len_y, false));
    assert!(!ae.check(len_x, len_y, true));
}

#[test]
fn infer_zeros_in_sum_geq_removes_redundant_summands() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let len_x = terms.mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let len_y = terms.mk_app(Symbol::named("str.len"), vec![y], Sort::Int);
    let one = terms.mk_int(BigInt::from(1));

    let mut state = SolverState::new();
    state.register_term(&terms, len_x);
    state.register_term(&terms, len_y);

    let ae = ArithEntail::new(&terms, &state);
    let mut ys = vec![len_x, len_y, one];
    let mut zero_ys = Vec::new();

    assert!(ae.infer_zeros_in_sum_geq(len_x, &mut ys, &mut zero_ys));
    assert_eq!(ys, vec![len_x]);
    assert_eq!(zero_ys.len(), 2);
    assert!(zero_ys.contains(&len_y));
    assert!(zero_ys.contains(&one));
}

#[test]
fn length_bound_cycle_returns_conservative_lower_bound() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let concat = terms.mk_app(Symbol::named("str.++"), vec![x, x], Sort::String);
    let eq = terms.mk_eq(x, concat);

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, concat);
    let _ = state.merge(x, concat, TheoryLit::new(eq, true));

    let ae = ArithEntail::new(&terms, &state);
    assert_eq!(ae.get_length_bound(x, true), Some(0));
    assert_eq!(ae.get_length_bound(concat, true), Some(0));
    assert_eq!(ae.get_length_bound(x, false), None);
}
