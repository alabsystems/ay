// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::{ChcOp, ClauseBody, ClauseHead, HornClause};

mod arrays;
mod fixtures;
mod grouped;
mod record_ingress;
mod refusals;
mod scopes;

fn parsed(input: &str) -> QuantifiedChcProblem {
    QuantifiedChcProblem::parse_smtlib(input).expect("supported exact source script")
}

#[test]
fn projected_resize_fixedpoint_retains_symbolic_matrix_and_query_local_probe() {
    let problem = parsed(&fixtures::resize());
    let source = problem.source_problem();
    assert_eq!(source.predicates().len(), 2);
    assert_eq!(source.predicates()[0].arg_sorts.len(), 4);
    assert_eq!(source.clauses().len(), 3);
    assert_eq!(
        problem.premises().iter().map(Vec::len).collect::<Vec<_>>(),
        vec![1, 0, 0]
    );
    assert!(!source.has_stripped_body_forall());
    assert_eq!(source.pruned_false_query_count(), 0);
    let premise = &problem.premises()[0][0];
    assert_eq!(premise.binder().sort, ChcSort::BitVec(64));
    let text = crate::InvariantModel::expr_to_smtlib(premise.matrix());
    let index = &premise.binder().name;
    assert!(text.contains(&format!("(bvult {index} old)")));
    assert!(text.contains(&format!("(bvuge {index} old)")));
    assert!(text.contains(&format!("(bvult {index} new)")));
    assert!(text.contains(&format!("(select a {index})")));
    let query_guard = source.clauses()[1].body.constraint.as_ref().unwrap();
    assert!(query_guard.vars().iter().any(|var| var.name == "j"));
    assert!(crate::InvariantModel::expr_to_smtlib(query_guard).contains("(_ bv32 64)"));
    fixtures::check_matrix(premise);
}

#[test]
fn typed_source_horn_roundtrip_retains_premises_and_original_query_order() {
    let original = fixtures::typed();
    let roundtrip = parsed(original.source_smtlib());
    assert_eq!(roundtrip.source_problem().clauses().len(), 3);
    assert_eq!(
        roundtrip
            .premises()
            .iter()
            .map(Vec::len)
            .collect::<Vec<_>>(),
        vec![1, 0, 0]
    );
    assert_eq!(
        roundtrip
            .source_problem()
            .clauses()
            .iter()
            .map(|clause| clause.source_query_ordinal)
            .collect::<Vec<_>>(),
        vec![None, Some(0), Some(1)]
    );
    assert_eq!(roundtrip.source_problem().pruned_false_query_count(), 0);
    assert_eq!(
        roundtrip.source_problem().clauses()[2]
            .body
            .constraint
            .as_ref(),
        Some(&ChcExpr::Bool(false))
    );
    assert_eq!(roundtrip.premises()[0][0].binder().sort, ChcSort::BitVec(2));
}

#[test]
fn raw_false_rules_duplicate_queries_and_guard_order_are_not_simplified() {
    let problem = parsed(
        "(set-logic HORN)
        (declare-fun P () Bool)
        (assert (=> false P))
        (assert (=> (and true false) false))
        (assert (=> false false))
        (assert (=> false false))
        (check-sat)(exit)",
    );
    let source = problem.source_problem();
    assert_eq!(source.clauses().len(), 4);
    assert_eq!(source.pruned_false_query_count(), 0);
    assert_eq!(
        source.clauses()[0].body.constraint.as_ref(),
        Some(&ChcExpr::Bool(false))
    );
    let Some(ChcExpr::Op(ChcOp::And, args)) = source.clauses()[1].body.constraint.as_ref() else {
        panic!("raw ordered conjunction")
    };
    assert_eq!(
        args.iter().map(|arg| arg.as_ref()).collect::<Vec<_>>(),
        vec![&ChcExpr::Bool(true), &ChcExpr::Bool(false)]
    );
    assert_eq!(
        source
            .clauses()
            .iter()
            .map(|clause| clause.source_query_ordinal)
            .collect::<Vec<_>>(),
        vec![None, Some(0), Some(1), Some(2)]
    );
}

#[test]
fn identity_tracks_changed_matrix_and_query_but_not_lexical_trivia() {
    let input = fixtures::resize();
    let original = parsed(&input);
    let decorated = parsed(&format!("; header\n{input}\n; trailer\n"));
    assert_eq!(original.source_smtlib(), decorated.source_smtlib());
    let changed_matrix = parsed(&input.replace("(bvult i old)", "(bvule i old)"));
    assert_ne!(original.source_smtlib(), changed_matrix.source_smtlib());
    let changed_query = parsed(&input.replace("(_ bv32 64)", "(_ bv33 64)"));
    assert_ne!(original.source_smtlib(), changed_query.source_smtlib());
    let unused = parsed(&input.replace(
        "(declare-var j",
        "(declare-var unused Bool)\n(declare-var j",
    ));
    // Identity is canonical admitted typed semantics, not lexical source bytes.
    assert_eq!(original.source_smtlib(), unused.source_smtlib());
}

#[test]
fn horn_theory_consequents_keep_the_complete_negated_property() {
    let problem = parsed(
        "(declare-fun P ((_ BitVec 8)) Bool)
        (assert (forall ((x (_ BitVec 8))) (=> (P x) (bvult x #x10))))
        (assert true)(check-sat)",
    );
    let clauses = problem.source_problem().clauses();
    assert_eq!(clauses.len(), 2);
    assert_eq!(clauses[0].body.predicates.len(), 1);
    assert!(matches!(clauses[0].head, ClauseHead::False));
    let Some(ChcExpr::Op(ChcOp::Not, negation)) = &clauses[0].body.constraint else {
        panic!("raw negated theory consequent")
    };
    let ChcExpr::Op(ChcOp::BvULt, comparison) = negation[0].as_ref() else {
        panic!("original comparison")
    };
    assert_eq!(comparison[0].as_ref(), &clauses[0].body.predicates[0].1[0]);
    assert_eq!(comparison[1].as_ref(), &ChcExpr::BitVec(16, 8));
    assert_eq!(
        clauses[1].body.constraint,
        Some(ChcExpr::Op(ChcOp::Not, vec![Arc::new(ChcExpr::Bool(true))]))
    );
    assert_eq!(clauses[1].source_query_ordinal, Some(1));
}
