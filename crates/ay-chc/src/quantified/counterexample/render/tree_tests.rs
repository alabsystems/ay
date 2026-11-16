// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent emitted-text semantics for occurrence-tree edges and scopes.

use super::*;
use crate::quantified::counterexample::render_oracle as oracle;
use crate::quantified::QuantifiedHornClause;
use crate::{CancellationToken, ChcOp, ChcProblem, ChcSort, ClauseBody};
use ay_core::time::Instant;
use std::sync::Arc;
use std::time::Duration;

fn op(operator: ChcOp, arguments: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(operator, arguments.into_iter().map(Arc::new).collect())
}

fn enabled() -> ChcExpr {
    ChcExpr::Var(ChcVar::new("enabled", ChcSort::Bool))
}

fn premise(consequent: ChcExpr) -> UniversalPremise {
    let i = ChcVar::new("i", ChcSort::BitVec(2));
    let j = ChcVar::new("j", ChcSort::BitVec(2));
    UniversalPremise::with_binders(
        vec![i.clone(), j.clone()],
        op(
            ChcOp::Implies,
            vec![
                op(ChcOp::Eq, vec![ChcExpr::Var(i), ChcExpr::Var(j)]),
                consequent,
            ],
        ),
    )
    .unwrap()
}

fn source(fact: ChcExpr, query: ChcExpr) -> QuantifiedChcProblem {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![ChcSort::BitVec(2)]);
    let x = ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(2)));
    QuantifiedChcProblem::new(
        declarations,
        vec![
            QuantifiedHornClause::new(
                HornClause::fact(ChcExpr::Bool(true), p, vec![x]),
                vec![premise(fact)],
            ),
            QuantifiedHornClause::new(
                HornClause::query(ClauseBody::predicates_only(vec![
                    (p, vec![ChcExpr::BitVec(0, 2)]),
                    (p, vec![ChcExpr::BitVec(1, 2)]),
                ])),
                vec![premise(query)],
            ),
        ],
    )
    .unwrap()
}

fn output(
    problem: &QuantifiedChcProblem,
    indices: &[usize],
    edges: &[Vec<usize>],
) -> Result<String> {
    let token = CancellationToken::new();
    let control = SourceControl::new(Instant::now() + Duration::from_secs(30), &token);
    render_derivation(problem, indices, edges, &control)
}

#[test]
fn repeated_fact_occurrences_have_independent_values_and_complete_premises() {
    let problem = source(enabled(), enabled());
    let script = output(&problem, &[0, 0, 1], &[vec![], vec![], vec![0, 1]]).unwrap();
    ay_frontend::parse(&script).expect("ordinary occurrence-tree SAT script");
    // Two occurrences of the SAME fact require x=0 and x=1. Matrix-only
    // enabled values are local to each occurrence, including the query.
    assert_eq!(oracle::models(&script), vec![vec![1, 0, 1, 1, 1]]);
    assert_eq!(
        script
            .matches("(forall ((i (_ BitVec 2))(j (_ BitVec 2)))")
            .count(),
        3
    );
    assert_eq!(script.matches("(declare-const ").count(), 5);
    assert!(!script.contains("(P "));
    assert_eq!(
        script,
        output(&problem, &[0, 0, 1], &[vec![], vec![], vec![0, 1]]).unwrap()
    );
}

#[test]
fn every_ordered_body_edge_selects_its_own_predecessor_scope() {
    let problem = source(enabled(), enabled());
    let normal = output(&problem, &[0, 0, 1], &[vec![], vec![], vec![0, 1]]).unwrap();
    let reverse = output(&problem, &[0, 0, 1], &[vec![], vec![], vec![1, 0]]).unwrap();
    assert_eq!(oracle::models(&normal), vec![vec![1, 0, 1, 1, 1]]);
    assert_eq!(oracle::models(&reverse), vec![vec![1, 1, 1, 0, 1]]);
    assert_ne!(normal, reverse);
}

#[test]
fn false_premises_on_either_facts_or_query_remain_in_the_tree_obligation() {
    for problem in [
        source(ChcExpr::Bool(false), enabled()),
        source(enabled(), ChcExpr::Bool(false)),
    ] {
        let script = output(&problem, &[0, 0, 1], &[vec![], vec![], vec![0, 1]]).unwrap();
        assert_eq!(oracle::models(&script), [] as [std::vec::Vec<u64>; 0]);
        assert_eq!(script.matches("(forall ").count(), 3);
    }
}

#[test]
fn malformed_trees_never_drop_a_premise_share_a_node_or_publish_an_orphan() {
    let problem = source(enabled(), enabled());
    for edges in [
        vec![],
        vec![vec![], vec![], vec![0]],
        vec![vec![], vec![], vec![0, 0]],
        vec![vec![], vec![], vec![0, 2]],
        vec![vec![1], vec![], vec![0, 1]],
    ] {
        assert!(output(&problem, &[0, 0, 1], &edges).is_err());
    }
    assert!(output(
        &problem,
        &[0, 0, 0, 1],
        &[vec![], vec![], vec![], vec![0, 1]]
    )
    .is_err());
    assert!(output(&problem, &[0, 1, 1], &[vec![], vec![], vec![0, 1]]).is_err());
}

#[test]
fn linear_derivation_rendering_keeps_the_original_script_bytes() {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![ChcSort::BitVec(2)]);
    let x = ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(2)));
    let problem = QuantifiedChcProblem::new(
        declarations,
        vec![
            QuantifiedHornClause::new(
                HornClause::fact(
                    op(ChcOp::Eq, vec![x.clone(), ChcExpr::BitVec(0, 2)]),
                    p,
                    vec![x.clone()],
                ),
                vec![],
            ),
            QuantifiedHornClause::new(
                HornClause::query(ClauseBody::new(
                    vec![(p, vec![x.clone()])],
                    Some(op(ChcOp::Eq, vec![x, ChcExpr::BitVec(1, 2)])),
                )),
                vec![],
            ),
        ],
    )
    .unwrap();
    let expected = "(set-logic ALL)\n\
        (declare-const ay_qcex_0 (_ BitVec 2))\n\
        (declare-const ay_qcex_1 (_ BitVec 2))\n\
        (assert true)\n\
        (assert (let ((x ay_qcex_0)) (= x (_ bv0 2))))\n\
        (assert (let ((x ay_qcex_1)) (= x (_ bv1 2))))\n\
        (assert (= (let ((x ay_qcex_1)) x) (let ((x ay_qcex_0)) x)))\n\
        (check-sat)\n";
    let script = output(&problem, &[0, 1], &[vec![], vec![0]]).unwrap();
    assert_eq!(script, expected);
    let token = CancellationToken::new();
    let control = SourceControl::new(Instant::now() + Duration::from_secs(30), &token);
    assert_eq!(render(&problem, &[0, 1], &control).unwrap(), expected);
}
