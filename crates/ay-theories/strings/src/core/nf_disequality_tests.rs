// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;

/// check_normal_forms_deq integrates the deq reducer and emits a component
/// LengthSplit after trimming equal suffix components.
#[test]
fn check_normal_forms_deq_component_length_split_after_suffix_reduction() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let a = terms.mk_string("a".to_string());
    let len_x = terms.mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let len_y = terms.mk_app(Symbol::named("str.len"), vec![y], Sort::Int);
    let xa = terms.mk_app(Symbol::named("str.++"), vec![x, a], Sort::String);
    let ya = terms.mk_app(Symbol::named("str.++"), vec![y, a], Sort::String);
    let eq_xa_ya = terms.mk_eq(xa, ya);

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, y);
    state.register_term(&terms, a);
    state.register_term(&terms, len_x);
    state.register_term(&terms, len_y);
    state.assert_literal(&terms, eq_xa_ya, false); // xa != ya

    let mut core = CoreSolver::new();
    core.compute_normal_forms(&terms, &state);
    let mut infer = InferenceManager::new();
    let mut skolems = SkolemCache::new();
    let result = core.check_normal_forms_deq(&terms, &state, &mut infer, &mut skolems);

    match result {
        NfCheckResult::NeedLemma(StringLemma {
            kind: StringLemmaKind::LengthSplit,
            x: lhs,
            y: rhs,
            ..
        }) => {
            assert_eq!(lhs, x, "split lhs should be reduced prefix component x");
            assert_eq!(rhs, y, "split rhs should be reduced prefix component y");
        }
        other => panic!("expected component LengthSplit from deq reducer, got {other:?}"),
    }
    assert!(!infer.has_conflict());
}

#[test]
fn is_guaranteed_nonempty_constant() {
    let mut terms = TermStore::new();
    let s = terms.mk_string("hello".to_string());
    let state = SolverState::new();
    assert!(CoreSolver::is_guaranteed_nonempty(&terms, &state, s));
}

#[test]
fn is_guaranteed_nonempty_empty_constant() {
    let mut terms = TermStore::new();
    let s = terms.mk_string(String::new());
    let state = SolverState::new();
    assert!(!CoreSolver::is_guaranteed_nonempty(&terms, &state, s));
}

#[test]
fn is_guaranteed_nonempty_concat_with_nonempty_child() {
    let mut terms = TermStore::new();
    let a = terms.mk_string("a".to_string());
    let x = terms.mk_var("x", Sort::String);
    let concat = terms.mk_app(Symbol::named("str.++"), vec![x, a], Sort::String);
    let state = SolverState::new();
    // concat has a non-empty constant child "a", so it is guaranteed non-empty.
    assert!(CoreSolver::is_guaranteed_nonempty(&terms, &state, concat));
}

#[test]
fn is_guaranteed_nonempty_variable_is_false() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let state = SolverState::new();
    assert!(!CoreSolver::is_guaranteed_nonempty(&terms, &state, x));
}
