// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Engine tests with a scripted oracle: tree shapes, the CE-free main query,
//! and the fail-closed declines.

use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;

use super::tree::TreeDecline;
use super::*;

/// Oracle answering from a script, recording every query it was asked.
struct Scripted {
    terms: TermStore,
    answers: Vec<OracleAnswer>,
    asked: Vec<Vec<TermId>>,
}

impl QlraHost for Scripted {
    fn terms(&mut self) -> &mut TermStore {
        &mut self.terms
    }
    fn check(&mut self, assertions: &[TermId], _targets: &[TermId]) -> OracleAnswer {
        self.asked.push(assertions.to_vec());
        if self.answers.is_empty() {
            OracleAnswer::Unknown
        } else {
            self.answers.remove(0)
        }
    }
    fn should_stop(&self) -> bool {
        false
    }
}

fn rat(n: i64) -> OracleValue {
    OracleValue::Rat(BigRational::from_integer(BigInt::from(n)))
}

/// `c > 0` and `(forall ((x Real)) (< x c))`.
fn simple_problem(terms: &mut TermStore) -> (Vec<TermId>, TermId) {
    let c = terms.mk_var("c", Sort::Real);
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::from_integer(0.into()));
    let ground = terms.mk_gt(c, zero);
    let body = terms.mk_lt(x, c);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Real)], body);
    (vec![ground, forall], forall)
}

#[test]
fn depth1_tree_splits_ground_nodes_and_skolems() {
    let mut terms = TermStore::new();
    let (roots, forall) = simple_problem(&mut terms);
    let y = terms.mk_var("y", Sort::Real);
    let c = terms.mk_var("c", Sort::Real);
    let gt = terms.mk_gt(y, c);
    let exists = terms.mk_exists(vec![("y".to_string(), Sort::Real)], gt);
    let conj = terms.mk_and(vec![roots[0], exists]);
    let tree = build_depth1_tree(&mut terms, &[conj, forall]).expect("depth-1 shape");
    assert_eq!(tree.nodes.len(), 1);
    assert_eq!(tree.skolems.len(), 1);
    // ground sibling + Skolem instance
    assert_eq!(tree.ground.len(), 2);
    assert!(
        matches!(tree.nodes[0].source, NodeSource::Forall { quantifier } if quantifier == forall)
    );
    let witness = tree.skolems[0].witness;
    assert!(
        terms.skolem_choices().any(|(w, _)| w == witness),
        "Skolem must be registered"
    );
}

#[test]
fn depth1_tree_declines_quantifier_under_connective_and_nesting() {
    let mut terms = TermStore::new();
    let (_, forall) = simple_problem(&mut terms);
    let p = terms.mk_var("p", Sort::Bool);
    let under_or = terms.mk_or(vec![p, forall]);
    assert_eq!(
        build_depth1_tree(&mut terms, &[under_or]).err(),
        Some(TreeDecline::QuantifierUnderConnective)
    );
    let nested = terms.mk_exists(vec![("z".to_string(), Sort::Real)], forall);
    assert_eq!(
        build_depth1_tree(&mut terms, &[nested]).err(),
        Some(TreeDecline::Nested)
    );
    let not_forall = terms.mk_not(forall);
    assert_eq!(
        build_depth1_tree(&mut terms, &[not_forall]).err(),
        Some(TreeDecline::ExistentialShape)
    );
}

/// The main query S1 never carries a counterexample formula, and the loop
/// reads UNSAT of S1 as the refutation.
#[test]
fn main_query_is_counterexample_free() {
    let mut terms = TermStore::new();
    let (roots, _) = simple_problem(&mut terms);
    let tree = build_depth1_tree(&mut terms, &roots).expect("tree");
    let e = tree.nodes[0].ce_vars[0];
    let c = terms.mk_var("c", Sort::Real);
    // Round 0: S1 sat; CE sat with c=1, e=5 (5 < 1 false); Round 1: S1 unsat.
    let mut targets_model = vec![rat(1), rat(5)];
    if c > e {
        targets_model.reverse();
    }
    let mut host = Scripted {
        terms,
        answers: vec![
            OracleAnswer::Sat(vec![]),
            OracleAnswer::Sat(targets_model.into_iter().map(Some).collect()),
            OracleAnswer::Unsat,
        ],
        asked: Vec::new(),
    };
    let (outcome, log, _) = solve_depth1(&mut host, &tree, 64);
    assert!(matches!(outcome, QlraOutcome::Unsat), "{outcome:?}");
    assert_eq!(log.len(), 1, "one instance logged");
    let ce_vars = tree.all_ce_vars();
    // Queries 0 and 2 are S1 queries: none may mention a CE constant.
    for &q in &[0usize, 2] {
        for a in host.asked[q].clone() {
            assert!(
                !free_vars(&mut host, a).iter().any(|v| ce_vars.contains(v)),
                "S1 query {q} carries a counterexample formula"
            );
        }
    }
    // The logged tuple is c + 1 (lower bound c from x >= c, no upper bound).
    let tuple = log.entries()[0].tuple[0];
    assert!(!free_vars(&mut host, tuple)
        .iter()
        .any(|v| ce_vars.contains(v)));
}

/// An oracle model contradicting Γ (the same instance re-selected) must
/// decline, never loop and never answer.
#[test]
fn repeated_selection_declines_no_progress() {
    let mut terms = TermStore::new();
    let (roots, _) = simple_problem(&mut terms);
    let tree = build_depth1_tree(&mut terms, &roots).expect("tree");
    let e = tree.nodes[0].ce_vars[0];
    let c = terms.mk_var("c", Sort::Real);
    let model = |c_first: bool| {
        let v = if c_first {
            vec![rat(1), rat(5)]
        } else {
            vec![rat(5), rat(1)]
        };
        OracleAnswer::Sat(v.into_iter().map(Some).collect())
    };
    let mut host = Scripted {
        terms,
        answers: vec![
            OracleAnswer::Sat(vec![]),
            model(c < e),
            OracleAnswer::Sat(vec![]),
            model(c < e),
        ],
        asked: Vec::new(),
    };
    let (outcome, _, _) = solve_depth1(&mut host, &tree, 64);
    assert!(
        matches!(outcome, QlraOutcome::Decline(QlraDecline::NoProgress)),
        "{outcome:?}"
    );
}

/// A cap below the log size declines instead of answering.
#[test]
fn publishable_cap_declines() {
    let mut terms = TermStore::new();
    let (roots, _) = simple_problem(&mut terms);
    let tree = build_depth1_tree(&mut terms, &roots).expect("tree");
    let e = tree.nodes[0].ce_vars[0];
    let c = terms.mk_var("c", Sort::Real);
    let v = if c < e {
        vec![rat(1), rat(5)]
    } else {
        vec![rat(5), rat(1)]
    };
    let mut host = Scripted {
        terms,
        answers: vec![
            OracleAnswer::Sat(vec![]),
            OracleAnswer::Sat(v.into_iter().map(Some).collect()),
        ],
        asked: Vec::new(),
    };
    let (outcome, _, _) = solve_depth1(&mut host, &tree, 0);
    assert!(
        matches!(outcome, QlraOutcome::Decline(QlraDecline::Cap(_))),
        "{outcome:?}"
    );
}
