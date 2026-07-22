// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::TermStore;
use ay_core::Sort;

#[test]
fn no_conflict_on_empty_state() {
    let terms = TermStore::new();
    let state = SolverState::new();
    let mut infer = InferenceManager::new();
    let base = BaseSolver::new();
    assert!(!base.check_init(&terms, &state, &mut infer));
}

#[test]
fn no_conflict_single_constant_eqc() {
    let mut terms = TermStore::new();
    let c = terms.mk_string("hello".to_string());

    let mut state = SolverState::new();
    state.register_term(&terms, c);

    let mut infer = InferenceManager::new();
    let base = BaseSolver::new();
    assert!(!base.check_init(&terms, &state, &mut infer));
}

#[test]
fn constant_merge_conflict() {
    let mut terms = TermStore::new();
    let r1 = terms.mk_string("abc".to_string());
    let r2 = terms.mk_string("def".to_string());

    let mut state = SolverState::new();
    state.register_term(&terms, r1);
    state.register_term(&terms, r2);

    let mut infer = InferenceManager::new();
    let base = BaseSolver::new();
    assert!(base.check_constant_merge(&state, &r1, &r2, &mut infer));
    assert!(infer.has_conflict());
}

#[test]
fn constant_merge_same_value_no_conflict() {
    let mut terms = TermStore::new();
    let r1 = terms.mk_string("abc".to_string());
    let r2 = terms.mk_string("abc".to_string());

    let mut state = SolverState::new();
    state.register_term(&terms, r1);
    state.register_term(&terms, r2);

    let mut infer = InferenceManager::new();
    let base = BaseSolver::new();
    assert!(!base.check_constant_merge(&state, &r1, &r2, &mut infer));
}

#[test]
fn constant_merge_one_missing_no_conflict() {
    let mut terms = TermStore::new();
    let r1 = terms.mk_string("abc".to_string());
    let r2 = terms.mk_var("x", Sort::String);

    let mut state = SolverState::new();
    state.register_term(&terms, r1);
    state.register_term(&terms, r2);

    let mut infer = InferenceManager::new();
    let base = BaseSolver::new();
    assert!(!base.check_constant_merge(&state, &r1, &r2, &mut infer));
}

#[test]
fn pending_conflict_prefers_targeted_explanation_over_unrelated_assertions() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let p = terms.mk_var("p", Sort::String);
    let q = terms.mk_var("q", Sort::String);
    let a = terms.mk_string("a".to_string());
    let b = terms.mk_string("b".to_string());

    // Two asserted literals in scope.
    let lit_xy_term = terms.mk_eq(x, y);
    let lit_pq_term = terms.mk_eq(p, q);
    let lit_xy = TheoryLit::new(lit_xy_term, true);
    let lit_pq = TheoryLit::new(lit_pq_term, true);

    let mut state = SolverState::new();
    for t in [x, y, p, q, a, b] {
        state.register_term(&terms, t);
    }
    state.assert_literal(&terms, lit_xy_term, true);
    state.assert_literal(&terms, lit_pq_term, true);

    // Simulate an internal merge chain whose explanations are lit_xy only.
    let _ = state.merge(y, a, lit_xy);
    let _ = state.merge(x, b, lit_xy);
    assert!(
        state.pending_conflict().is_some(),
        "expected pending conflict"
    );

    let base = BaseSolver::new();
    let mut infer = InferenceManager::new();
    assert!(base.check_init(&terms, &state, &mut infer));

    match infer.to_theory_result() {
        ay_core::TheoryResult::Unsat(lits) => {
            assert!(
                lits.contains(&lit_xy),
                "pending conflict explanation must include original merge reason"
            );
            assert!(
                !lits.contains(&lit_pq),
                "pending conflict explanation should not include unrelated assertions"
            );
        }
        other => panic!("expected Unsat, got {other:?}"),
    }
}

#[test]
fn pending_conflict_explanation_includes_constant_origins() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let p = terms.mk_var("p", Sort::String);
    let q = terms.mk_var("q", Sort::String);
    let a = terms.mk_string("a".to_string());
    let b = terms.mk_string("b".to_string());
    let eq_xa = terms.mk_eq(x, a);
    let eq_yb = terms.mk_eq(y, b);
    let eq_xy = terms.mk_eq(x, y);
    let eq_pq = terms.mk_eq(p, q);
    let lit_xa = TheoryLit::new(eq_xa, true);
    let lit_yb = TheoryLit::new(eq_yb, true);
    let lit_xy = TheoryLit::new(eq_xy, true);
    let lit_pq = TheoryLit::new(eq_pq, true);

    let mut state = SolverState::new();
    state.assert_literal(&terms, eq_xa, true);
    state.assert_literal(&terms, eq_yb, true);
    state.assert_literal(&terms, eq_pq, true);
    state.assert_literal(&terms, eq_xy, true);
    assert!(
        state.pending_conflict().is_some(),
        "expected pending conflict"
    );

    let base = BaseSolver::new();
    let mut infer = InferenceManager::new();
    assert!(base.check_init(&terms, &state, &mut infer));

    match infer.to_theory_result() {
        ay_core::TheoryResult::Unsat(lits) => {
            assert!(
                lits.contains(&lit_xa),
                "constant-conflict explanation must include x = \"a\""
            );
            assert!(
                lits.contains(&lit_yb),
                "constant-conflict explanation must include y = \"b\""
            );
            assert!(
                lits.contains(&lit_xy),
                "constant-conflict explanation must include x = y"
            );
            assert!(
                !lits.contains(&lit_pq),
                "unrelated assertions must not appear in pending-conflict explanation"
            );
        }
        other => panic!("expected Unsat, got {other:?}"),
    }
}
