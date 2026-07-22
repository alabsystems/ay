// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Basic core solver tests: state management, clear semantics, skolem cache.

use super::*;
use crate::normal_form::ExplainEntry;
use ay_core::term::Symbol;
use ay_core::Sort;

#[test]
fn empty_state_no_conflict() {
    let terms = TermStore::new();
    let state = SolverState::new();
    let mut infer = InferenceManager::new();
    let mut core = CoreSolver::new();
    assert!(!core.check(&terms, &state, &mut infer, &mut SkolemCache::new()));
}

#[test]
fn single_variable_eqc() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);

    let mut state = SolverState::new();
    state.register_term(&terms, x);

    let mut infer = InferenceManager::new();
    let mut core = CoreSolver::new();
    assert!(!core.check(&terms, &state, &mut infer, &mut SkolemCache::new()));

    let nf = core.get_normal_form(&x).expect("normal form exists");
    assert_eq!(nf.len(), 1);
    assert_eq!(nf.base[0], x);
}

#[test]
fn constant_eqc_normal_form() {
    let mut terms = TermStore::new();
    let c = terms.mk_string("hello".to_string());

    let mut state = SolverState::new();
    state.register_term(&terms, c);

    let mut infer = InferenceManager::new();
    let mut core = CoreSolver::new();
    assert!(!core.check(&terms, &state, &mut infer, &mut SkolemCache::new()));

    let nf = core.get_normal_form(&c).expect("normal form exists");
    assert_eq!(nf.len(), 1);
}

#[test]
fn disequality_merged_reps_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let eq_xy = terms.mk_eq(x, y);
    let eq_xy2 = terms.mk_eq(x, y);

    let mut state = SolverState::new();
    // Assert x = y (merge them).
    state.assert_literal(&terms, eq_xy, true);
    // Assert x != y (contradicts merge).
    state.assert_literal(&terms, eq_xy2, false);

    let mut infer = InferenceManager::new();
    let mut core = CoreSolver::new();
    assert!(core.check(&terms, &state, &mut infer, &mut SkolemCache::new()));
    assert!(infer.has_conflict());
    // Same-EQC disequality violations are ground conflicts (#3875).
    assert!(infer.is_ground_conflict());
}

#[test]
fn disequality_different_reps_no_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let eq = terms.mk_eq(x, y);

    let mut state = SolverState::new();
    state.assert_literal(&terms, eq, false);

    let mut infer = InferenceManager::new();
    let mut core = CoreSolver::new();
    assert!(!core.check(&terms, &state, &mut infer, &mut SkolemCache::new()));
}

#[test]
fn clear_resets_normal_forms() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);

    let mut state = SolverState::new();
    state.register_term(&terms, x);

    let mut infer = InferenceManager::new();
    let mut core = CoreSolver::new();
    core.check(&terms, &state, &mut infer, &mut SkolemCache::new());
    assert!(core.get_normal_form(&x).is_some());

    core.clear();
    assert!(core.get_normal_form(&x).is_none());
}

#[test]
fn clear_preserves_reduced_terms() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);

    let mut core = CoreSolver::new();
    core.mark_reduced(x);
    assert!(core.reduced_terms.contains(&x));

    // clear() preserves reduced_terms: DPLL-level reduction lemmas
    // persist across scope changes (push/pop calls clear()).
    core.clear();
    assert!(
        core.reduced_terms.contains(&x),
        "clear() must preserve reduced_terms (DPLL reductions persist across scopes)"
    );
}

/// SkolemCache dedup: duplicate EmptySplit on the same variable is suppressed.
///
/// Two NF pairs both need EmptySplit on x. The first call returns NeedLemma,
/// the second returns Incomplete because the SkolemCache marks the split as
/// already emitted.
#[test]
fn skolem_cache_dedup_empty_split() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let a = terms.mk_string("a".to_string());
    let b = terms.mk_string("b".to_string());
    let v1 = terms.mk_var("v1", Sort::String);
    let v2 = terms.mk_var("v2", Sort::String);
    let eq1 = terms.mk_eq(v1, x);
    let eq2 = terms.mk_eq(v2, a);

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, a);
    state.register_term(&terms, b);
    state.register_term(&terms, v1);
    state.register_term(&terms, v2);
    state.assert_literal(&terms, eq1, true);
    state.assert_literal(&terms, eq2, true);

    // NF pair 1: [x, "b"] vs ["a", "b"] → EmptySplit on x
    let nf1 = NormalForm {
        base: vec![x, b],
        rep: Some(x),
        source: Some(x),
        deps: vec![ExplainEntry { lhs: v1, rhs: x }],
    };
    let b2 = terms.mk_string("b".to_string());
    state.register_term(&terms, b2);
    let nf2 = NormalForm {
        base: vec![a, b2],
        rep: Some(a),
        source: Some(a),
        deps: vec![ExplainEntry { lhs: v2, rhs: a }],
    };

    let mut skolems = SkolemCache::new();
    let mut infer = InferenceManager::new();
    let r1 = CoreSolver::process_simple_neq(&terms, &state, &nf1, &nf2, &mut infer, &mut skolems);
    assert!(
        matches!(
            r1,
            NfCheckResult::NeedLemma(StringLemma {
                kind: StringLemmaKind::EmptySplit,
                ..
            })
        ),
        "first call should emit EmptySplit, got {r1:?}"
    );
    let c = terms.mk_string("c".to_string());
    let (v3, v4) = (
        terms.mk_var("v3", Sort::String),
        terms.mk_var("v4", Sort::String),
    );
    for &t in &[c, v3, v4] {
        state.register_term(&terms, t);
    }
    let (eq3, eq4) = (terms.mk_eq(v3, x), terms.mk_eq(v4, c));
    state.assert_literal(&terms, eq3, true);
    state.assert_literal(&terms, eq4, true);
    let nf3 = NormalForm {
        base: vec![x],
        rep: Some(x),
        source: Some(x),
        deps: vec![ExplainEntry { lhs: v3, rhs: x }],
    };
    let nf4 = NormalForm {
        base: vec![c],
        rep: Some(c),
        source: Some(c),
        deps: vec![ExplainEntry { lhs: v4, rhs: c }],
    };
    let r2 = CoreSolver::process_simple_neq(&terms, &state, &nf3, &nf4, &mut infer, &mut skolems);
    assert!(
        matches!(r2, NfCheckResult::Incomplete),
        "duplicate EmptySplit should be dedup, got {r2:?}"
    );
}

/// SkolemCache dedup: duplicate ConstSplit on the same `(x, c, offset)`.
///
/// First request emits `ConstSplit`; second equivalent request is suppressed.
#[test]
fn skolem_cache_dedup_const_split() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let a = terms.mk_string("a".to_string());
    let b = terms.mk_string("b".to_string());
    let empty = terms.mk_string(String::new());
    let eq_x_empty = terms.mk_eq(x, empty);
    let v1 = terms.mk_var("v1", Sort::String);
    let v2 = terms.mk_var("v2", Sort::String);
    let eq1 = terms.mk_eq(v1, x);
    let eq2 = terms.mk_eq(v2, a);

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, a);
    state.register_term(&terms, b);
    state.register_term(&terms, empty);
    state.register_term(&terms, v1);
    state.register_term(&terms, v2);
    state.assert_literal(&terms, eq1, true);
    state.assert_literal(&terms, eq2, true);
    state.assert_literal(&terms, eq_x_empty, false); // x != "" -> non-empty

    let nf1 = NormalForm {
        base: vec![x, b],
        rep: Some(x),
        source: Some(x),
        deps: vec![ExplainEntry { lhs: v1, rhs: x }],
    };
    let b2 = terms.mk_string("b".to_string());
    state.register_term(&terms, b2);
    let nf2 = NormalForm {
        base: vec![a, b2],
        rep: Some(a),
        source: Some(a),
        deps: vec![ExplainEntry { lhs: v2, rhs: a }],
    };

    let mut skolems = SkolemCache::new();
    let mut infer = InferenceManager::new();

    let result1 =
        CoreSolver::process_simple_neq(&terms, &state, &nf1, &nf2, &mut infer, &mut skolems);
    assert!(
        matches!(
            result1,
            NfCheckResult::NeedLemma(StringLemma {
                kind: StringLemmaKind::ConstSplit,
                ..
            })
        ),
        "first call should emit ConstSplit, got {result1:?}"
    );

    let result2 =
        CoreSolver::process_simple_neq(&terms, &state, &nf1, &nf2, &mut infer, &mut skolems);
    assert!(
        matches!(result2, NfCheckResult::Incomplete),
        "duplicate ConstSplit should return Incomplete (dedup), got {result2:?}"
    );
}

/// SkolemCache dedup: duplicate VarSplit on the same `(x, y)` pair.
#[test]
fn skolem_cache_dedup_var_split() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let len_x = terms.mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let len_y = terms.mk_app(Symbol::named("str.len"), vec![y], Sort::Int);
    let len_eq = terms.mk_eq(len_x, len_y);
    let v1 = terms.mk_var("v1", Sort::String);
    let v2 = terms.mk_var("v2", Sort::String);
    let eq1 = terms.mk_eq(v1, x);
    let eq2 = terms.mk_eq(v2, y);

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, y);
    state.register_term(&terms, len_x);
    state.register_term(&terms, len_y);
    state.register_term(&terms, v1);
    state.register_term(&terms, v2);
    state.assert_literal(&terms, eq1, true);
    state.assert_literal(&terms, eq2, true);
    state.assert_literal(&terms, len_eq, false); // len(x) != len(y)

    let nf1 = NormalForm {
        base: vec![x],
        rep: Some(x),
        source: Some(x),
        deps: vec![ExplainEntry { lhs: v1, rhs: x }],
    };
    let nf2 = NormalForm {
        base: vec![y],
        rep: Some(y),
        source: Some(y),
        deps: vec![ExplainEntry { lhs: v2, rhs: y }],
    };

    let mut skolems = SkolemCache::new();
    let mut infer = InferenceManager::new();

    let result1 =
        CoreSolver::process_simple_neq(&terms, &state, &nf1, &nf2, &mut infer, &mut skolems);
    assert!(
        matches!(
            result1,
            NfCheckResult::NeedLemma(StringLemma {
                kind: StringLemmaKind::VarSplit,
                ..
            })
        ),
        "first call should emit VarSplit, got {result1:?}"
    );

    let result2 =
        CoreSolver::process_simple_neq(&terms, &state, &nf1, &nf2, &mut infer, &mut skolems);
    assert!(
        matches!(result2, NfCheckResult::Incomplete),
        "duplicate VarSplit should return Incomplete (dedup), got {result2:?}"
    );
}

/// SkolemCache push/pop: EmptySplit dedup respects scope boundaries.
///
/// After pop, a previously-cached EmptySplit is available again.
#[test]
fn skolem_cache_push_pop_empty_split_scope() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let a = terms.mk_string("a".to_string());
    let b = terms.mk_string("b".to_string());
    let v1 = terms.mk_var("v1", Sort::String);
    let v2 = terms.mk_var("v2", Sort::String);
    let eq1 = terms.mk_eq(v1, x);
    let eq2 = terms.mk_eq(v2, a);

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, a);
    state.register_term(&terms, b);
    state.register_term(&terms, v1);
    state.register_term(&terms, v2);
    state.assert_literal(&terms, eq1, true);
    state.assert_literal(&terms, eq2, true);

    let nf1 = NormalForm {
        base: vec![x, b],
        rep: Some(x),
        source: Some(x),
        deps: vec![ExplainEntry { lhs: v1, rhs: x }],
    };
    let b2 = terms.mk_string("b".to_string());
    state.register_term(&terms, b2);
    let nf2 = NormalForm {
        base: vec![a, b2],
        rep: Some(a),
        source: Some(a),
        deps: vec![ExplainEntry { lhs: v2, rhs: a }],
    };

    let mut skolems = SkolemCache::new();
    let mut infer = InferenceManager::new();

    // Mark in scope 0.
    skolems.push();
    let result1 =
        CoreSolver::process_simple_neq(&terms, &state, &nf1, &nf2, &mut infer, &mut skolems);
    assert!(
        matches!(result1, NfCheckResult::NeedLemma(..)),
        "first call should emit lemma"
    );

    // Pop scope — the EmptySplit mark should be removed.
    skolems.pop();

    // After pop, same split should be emittable again.
    let result2 =
        CoreSolver::process_simple_neq(&terms, &state, &nf1, &nf2, &mut infer, &mut skolems);
    assert!(
        matches!(
            result2,
            NfCheckResult::NeedLemma(StringLemma {
                kind: StringLemmaKind::EmptySplit,
                ..
            })
        ),
        "after pop, EmptySplit should be emittable again, got {result2:?}"
    );
}
