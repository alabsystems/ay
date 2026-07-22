// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{
    build_canonical_predicate_vars, build_predicate_users, build_push_cache_deps,
    compute_push_cache_signature, compute_reachable_predicates, detect_triangular_pattern,
};
use crate::{
    ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, PredicateId,
};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

fn var(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

// --- build_canonical_predicate_vars ---

#[test]
fn canonical_vars_empty_problem() {
    let problem = ChcProblem::new();
    let vars = build_canonical_predicate_vars(&problem);
    assert!(vars.is_empty());
}

#[test]
fn canonical_vars_naming_convention() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Bool]);
    let vars = build_canonical_predicate_vars(&problem);
    let p_vars = &vars[&p];
    assert_eq!(p_vars.len(), 2);
    assert_eq!(p_vars[0].name, format!("__p{}_a0", p.index()));
    assert_eq!(p_vars[0].sort, ChcSort::Int);
    assert_eq!(p_vars[1].name, format!("__p{}_a1", p.index()));
    assert_eq!(p_vars[1].sort, ChcSort::Bool);
}

// --- build_push_cache_deps ---

#[test]
fn push_cache_deps_captures_body_predicates() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    // P(x) :- Q(x)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(q, vec![var("x")])], None),
        ClauseHead::Predicate(p, vec![var("x")]),
    ));
    let deps = build_push_cache_deps(&problem);
    assert!(deps[&p].contains(&q));
    assert!(deps[&q].is_empty());
}

#[test]
fn push_cache_deps_deduplicates() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    // Two clauses P(x) :- Q(x)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(q, vec![var("x")])], None),
        ClauseHead::Predicate(p, vec![var("x")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(q, vec![var("y")])], None),
        ClauseHead::Predicate(p, vec![var("y")]),
    ));
    let deps = build_push_cache_deps(&problem);
    // Q should appear only once in P's deps
    assert_eq!(deps[&p].len(), 1);
}

// --- build_predicate_users ---

#[test]
fn predicate_users_inverts_deps() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    // Q(x) :- P(x) (Q depends on P)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![var("x")])], None),
        ClauseHead::Predicate(q, vec![var("x")]),
    ));
    let users = build_predicate_users(&problem);
    // P is used by Q
    assert!(users[&p].contains(&q));
    // Q is not used by anyone
    assert!(users[&q].is_empty());
}

// --- compute_reachable_predicates ---

#[test]
fn reachable_from_facts_only() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    // Only P has a fact
    problem.add_clause(HornClause::fact(
        ChcExpr::eq(var("x"), ChcExpr::int(0)),
        p,
        vec![var("x")],
    ));

    let facts: FxHashSet<PredicateId> = [p].into_iter().collect();
    let reachable = compute_reachable_predicates(&problem, &facts);
    assert!(reachable.contains(&p));
    assert!(!reachable.contains(&q));
}

#[test]
fn reachable_propagates_through_transition() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    // P has a fact
    problem.add_clause(HornClause::fact(
        ChcExpr::bool_const(true),
        p,
        vec![ChcExpr::int(0)],
    ));
    // Q(x) :- P(x)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![var("x")])], None),
        ClauseHead::Predicate(q, vec![var("x")]),
    ));

    let facts: FxHashSet<PredicateId> = [p].into_iter().collect();
    let reachable = compute_reachable_predicates(&problem, &facts);
    assert!(reachable.contains(&p));
    assert!(reachable.contains(&q));
}

#[test]
fn reachable_multi_body_requires_all_premises() {
    // R(x) :- P(x), Q(x)  (both P and Q must be reachable for R)
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let r = problem.declare_predicate("R", vec![ChcSort::Int]);
    // Only P has a fact
    problem.add_clause(HornClause::fact(
        ChcExpr::bool_const(true),
        p,
        vec![ChcExpr::int(0)],
    ));
    // R needs both P and Q
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![var("x")]), (q, vec![var("y")])], None),
        ClauseHead::Predicate(r, vec![var("x")]),
    ));

    let facts: FxHashSet<PredicateId> = [p].into_iter().collect();
    let reachable = compute_reachable_predicates(&problem, &facts);
    assert!(reachable.contains(&p));
    assert!(!reachable.contains(&q)); // No fact for Q
    assert!(!reachable.contains(&r)); // R needs both P and Q
}

#[test]
fn reachable_multi_body_all_satisfied() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let r = problem.declare_predicate("R", vec![ChcSort::Int]);
    // Both P and Q have facts
    problem.add_clause(HornClause::fact(
        ChcExpr::bool_const(true),
        p,
        vec![ChcExpr::int(0)],
    ));
    problem.add_clause(HornClause::fact(
        ChcExpr::bool_const(true),
        q,
        vec![ChcExpr::int(0)],
    ));
    // R needs both P and Q
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![var("x")]), (q, vec![var("y")])], None),
        ClauseHead::Predicate(r, vec![var("x")]),
    ));

    let facts: FxHashSet<PredicateId> = [p, q].into_iter().collect();
    let reachable = compute_reachable_predicates(&problem, &facts);
    assert!(reachable.contains(&r));
}

// --- compute_push_cache_signature ---

#[test]
fn push_cache_signature_deterministic() {
    let mut counts = FxHashMap::default();
    let p = PredicateId::new(0);
    counts.insert(p, 5);
    let deps = vec![p];
    let s1 = compute_push_cache_signature(&counts, &deps);
    let s2 = compute_push_cache_signature(&counts, &deps);
    assert_eq!(s1, s2);
}

#[test]
fn push_cache_signature_changes_with_count() {
    let p = PredicateId::new(0);
    let deps = vec![p];
    let mut counts1 = FxHashMap::default();
    counts1.insert(p, 5);
    let mut counts2 = FxHashMap::default();
    counts2.insert(p, 6);
    assert_ne!(
        compute_push_cache_signature(&counts1, &deps),
        compute_push_cache_signature(&counts2, &deps),
    );
}

// --- detect_triangular_pattern ---

#[test]
fn triangular_pattern_exact_fit() {
    // k=0,c=0; k=1,c=1; k=2,c=3; k=3,c=6 => c = k*(k+1)/2, offset=0
    let data = vec![vec![0, 0], vec![1, 1], vec![2, 3], vec![3, 6]];
    let vars = vec![
        ChcVar::new("k", ChcSort::Int),
        ChcVar::new("c", ChcSort::Int),
    ];
    let result = detect_triangular_pattern(&data, 0, 1, &vars, false);
    assert!(result.is_some());
    let bounds = result.unwrap();
    assert!(!bounds.is_empty());
}

#[test]
fn triangular_pattern_with_offset() {
    // c = k*(k+1)/2 + 10
    let data = vec![vec![0, 10], vec![1, 11], vec![2, 13], vec![3, 16]];
    let vars = vec![
        ChcVar::new("k", ChcSort::Int),
        ChcVar::new("c", ChcSort::Int),
    ];
    let result = detect_triangular_pattern(&data, 0, 1, &vars, false);
    assert!(result.is_some());
}

#[test]
fn triangular_pattern_rejects_too_few_points() {
    let data = vec![vec![0, 0], vec![1, 1], vec![2, 3]];
    let vars = vec![
        ChcVar::new("k", ChcSort::Int),
        ChcVar::new("c", ChcSort::Int),
    ];
    let result = detect_triangular_pattern(&data, 0, 1, &vars, false);
    assert!(result.is_none());
}

#[test]
fn triangular_pattern_rejects_constant_c() {
    // c is constant (100), offsets diverge: [100, 99, 97, 94], range=6 > 5
    let data = vec![vec![0, 100], vec![1, 100], vec![2, 100], vec![3, 100]];
    let vars = vec![
        ChcVar::new("k", ChcSort::Int),
        ChcVar::new("c", ChcSort::Int),
    ];
    let result = detect_triangular_pattern(&data, 0, 1, &vars, false);
    assert!(result.is_none());
}

#[test]
fn triangular_pattern_rejects_negative_k() {
    let data = vec![vec![-1, 0], vec![0, 0], vec![1, 1], vec![2, 3]];
    let vars = vec![
        ChcVar::new("k", ChcSort::Int),
        ChcVar::new("c", ChcSort::Int),
    ];
    let result = detect_triangular_pattern(&data, 0, 1, &vars, false);
    assert!(result.is_none());
}
