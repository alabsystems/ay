// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{ChcExpr, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

fn var(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

#[test]
fn empty_problem_yields_empty_scc() {
    let problem = ChcProblem::new();
    let info = tarjan_scc(&problem);
    assert!(info.sccs.is_empty());
    assert!(info.predicate_to_scc.is_empty());
}

#[test]
fn single_predicate_no_self_loop_is_acyclic() {
    // P(x) :- x = 0  (fact only, no self-loop)
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    problem.add_clause(HornClause::fact(
        ChcExpr::eq(var("x"), ChcExpr::int(0)),
        p,
        vec![var("x")],
    ));

    let info = tarjan_scc(&problem);
    assert_eq!(info.sccs.len(), 1);
    assert!(!info.sccs[0].is_cyclic);
    assert_eq!(info.sccs[0].predicates, vec![p]);
    assert_eq!(info.predicate_to_scc[&p], 0);
}

#[test]
fn single_predicate_with_self_loop_is_cyclic() {
    // P(x') :- P(x), x' = x + 1  (self-loop transition)
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    // Fact
    problem.add_clause(HornClause::fact(
        ChcExpr::eq(var("x"), ChcExpr::int(0)),
        p,
        vec![var("x")],
    ));
    // Self-loop: P(x) => P(x+1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![var("x")])], None),
        ClauseHead::Predicate(p, vec![ChcExpr::add(var("x"), ChcExpr::int(1))]),
    ));

    let info = tarjan_scc(&problem);
    assert_eq!(info.sccs.len(), 1);
    assert!(info.sccs[0].is_cyclic);
    assert_eq!(info.sccs[0].predicates, vec![p]);
}

#[test]
fn two_predicates_no_cycle() {
    // P(x) :- x = 0
    // Q(x) :- P(x)   (Q depends on P, but P doesn't depend on Q)
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    // Fact for P
    problem.add_clause(HornClause::fact(
        ChcExpr::eq(var("x"), ChcExpr::int(0)),
        p,
        vec![var("x")],
    ));
    // Q depends on P: P(x) => Q(x)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![var("x")])], None),
        ClauseHead::Predicate(q, vec![var("x")]),
    ));

    let info = tarjan_scc(&problem);
    assert_eq!(info.sccs.len(), 2);
    // Both are singletons, neither is cyclic
    for scc in &info.sccs {
        assert_eq!(scc.predicates.len(), 1);
        assert!(!scc.is_cyclic);
    }
    // Each predicate maps to a different SCC
    assert_ne!(info.predicate_to_scc[&p], info.predicate_to_scc[&q]);
}

#[test]
fn two_predicates_mutual_cycle() {
    // P(x) :- Q(x)
    // Q(x) :- P(x)
    // P and Q form a single cyclic SCC
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    // P depends on Q
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(q, vec![var("x")])], None),
        ClauseHead::Predicate(p, vec![var("x")]),
    ));
    // Q depends on P
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![var("x")])], None),
        ClauseHead::Predicate(q, vec![var("x")]),
    ));

    let info = tarjan_scc(&problem);
    assert_eq!(info.sccs.len(), 1);
    assert!(info.sccs[0].is_cyclic);
    assert_eq!(info.sccs[0].predicates.len(), 2);
    // Both predicates in same SCC
    assert_eq!(info.predicate_to_scc[&p], info.predicate_to_scc[&q]);
}

#[test]
fn three_predicates_chain_no_cycles() {
    // A -> B -> C  (chain, no back edges)
    let mut problem = ChcProblem::new();
    let a = problem.declare_predicate("A", vec![ChcSort::Int]);
    let b = problem.declare_predicate("B", vec![ChcSort::Int]);
    let c = problem.declare_predicate("C", vec![ChcSort::Int]);
    // A depends on nothing (fact)
    problem.add_clause(HornClause::fact(
        ChcExpr::bool_const(true),
        a,
        vec![ChcExpr::int(0)],
    ));
    // B depends on A
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(a, vec![var("x")])], None),
        ClauseHead::Predicate(b, vec![var("x")]),
    ));
    // C depends on B
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(b, vec![var("x")])], None),
        ClauseHead::Predicate(c, vec![var("x")]),
    ));

    let info = tarjan_scc(&problem);
    assert_eq!(info.sccs.len(), 3);
    for scc in &info.sccs {
        assert_eq!(scc.predicates.len(), 1);
        assert!(!scc.is_cyclic);
    }
    // All three predicates map to different SCCs
    let scc_a = info.predicate_to_scc[&a];
    let scc_b = info.predicate_to_scc[&b];
    let scc_c = info.predicate_to_scc[&c];
    assert_ne!(scc_a, scc_b);
    assert_ne!(scc_b, scc_c);
    assert_ne!(scc_a, scc_c);
}

#[test]
fn diamond_dependency_no_cycle() {
    //   A
    //  / \
    // B   C
    //  \ /
    //   D
    let mut problem = ChcProblem::new();
    let a = problem.declare_predicate("A", vec![ChcSort::Int]);
    let b = problem.declare_predicate("B", vec![ChcSort::Int]);
    let c = problem.declare_predicate("C", vec![ChcSort::Int]);
    let d = problem.declare_predicate("D", vec![ChcSort::Int]);
    problem.add_clause(HornClause::fact(
        ChcExpr::bool_const(true),
        a,
        vec![ChcExpr::int(0)],
    ));
    // B depends on A
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(a, vec![var("x")])], None),
        ClauseHead::Predicate(b, vec![var("x")]),
    ));
    // C depends on A
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(a, vec![var("x")])], None),
        ClauseHead::Predicate(c, vec![var("x")]),
    ));
    // D depends on B and C (two body predicates)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(b, vec![var("x")]), (c, vec![var("y")])], None),
        ClauseHead::Predicate(d, vec![var("x")]),
    ));

    let info = tarjan_scc(&problem);
    assert_eq!(info.sccs.len(), 4);
    for scc in &info.sccs {
        assert!(!scc.is_cyclic);
    }
}

#[test]
fn predicate_to_scc_is_complete() {
    // All predicates should appear in predicate_to_scc
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let r = problem.declare_predicate("R", vec![ChcSort::Int]);
    // P self-loop
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![var("x")])], None),
        ClauseHead::Predicate(p, vec![var("x")]),
    ));
    // Q -> R -> Q cycle
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(r, vec![var("x")])], None),
        ClauseHead::Predicate(q, vec![var("x")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(q, vec![var("x")])], None),
        ClauseHead::Predicate(r, vec![var("x")]),
    ));

    let info = tarjan_scc(&problem);
    // All 3 predicates accounted for
    assert!(info.predicate_to_scc.contains_key(&p));
    assert!(info.predicate_to_scc.contains_key(&q));
    assert!(info.predicate_to_scc.contains_key(&r));
    // P is alone and cyclic (self-loop)
    let p_scc = &info.sccs[info.predicate_to_scc[&p]];
    assert!(p_scc.is_cyclic);
    assert_eq!(p_scc.predicates.len(), 1);
    // Q and R form a cyclic SCC together
    assert_eq!(info.predicate_to_scc[&q], info.predicate_to_scc[&r]);
    let qr_scc = &info.sccs[info.predicate_to_scc[&q]];
    assert!(qr_scc.is_cyclic);
    assert_eq!(qr_scc.predicates.len(), 2);
}
