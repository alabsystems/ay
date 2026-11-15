// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{ChcSort, ChcVar};
use std::time::Duration;

fn source(operator: ChcOp) -> QuantifiedChcProblem {
    let sort = ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::BitVec(8)));
    let mut declarations = ChcProblem::new();
    let predicate = declarations.declare_predicate("P", vec![sort.clone()]);
    let array = ChcExpr::var(ChcVar::new("a", sort));
    let bad = ChcExpr::Op(
        operator,
        [0, 1]
            .into_iter()
            .map(|index| {
                Arc::new(ChcExpr::ne(
                    ChcExpr::select(array.clone(), ChcExpr::BitVec(index, 64)),
                    ChcExpr::BitVec(0, 8),
                ))
            })
            .collect(),
    );
    let fact = HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(
            predicate,
            vec![ChcExpr::const_array(
                ChcSort::BitVec(64),
                ChcExpr::BitVec(0, 8),
            )],
        ),
    );
    let query = HornClause::query(ClauseBody::new(vec![(predicate, vec![array])], Some(bad)));
    QuantifiedChcProblem::new(
        declarations,
        vec![
            crate::quantified::QuantifiedHornClause::new(fact, Vec::new()),
            crate::quantified::QuantifiedHornClause::new(query, Vec::new()),
        ],
    )
    .expect("exact retained original source")
}

#[test]
fn private_raw_branch_queries_keep_both_indices_and_original_query_unchanged() {
    let end = Instant::now() + Duration::from_secs(20);
    let token = CancellationToken::new();
    let control = SourceControl::new(end, &token);
    let original = source(ChcOp::Or);
    let text = original.source_smtlib().to_owned();
    let spec = GhostPairSpec::analyze(original.source_problem(), 1);
    let raw = rewrite_source(&original, &spec, &control).expect("complete private synthesis split");
    assert_eq!(original.source_problem().clauses().len(), 2);
    assert_eq!(raw.clauses().len(), 3);
    let ChcExpr::Op(ChcOp::Or, branches) = original.source_problem().clauses()[1]
        .body
        .constraint
        .as_ref()
        .expect("whole original OR")
    else {
        panic!("original OR retained")
    };
    for (index, branch) in raw.clauses()[1..].iter().enumerate() {
        assert!(matches!(branch.head, ClauseHead::False));
        assert_eq!(
            branch.body.constraint.as_ref(),
            Some(branches[index].as_ref())
        );
        assert_eq!(branch.body.predicates.len(), 1);
        let args = &branch.body.predicates[0].1;
        assert_eq!(args.len(), 3);
        assert_eq!(args[1], ChcExpr::BitVec(index as u128, 64));
        assert_eq!(args[2], ChcExpr::select(args[0].clone(), args[1].clone()));
    }
    assert_eq!(original.source_smtlib(), text);
    assert!(control.poll().is_some());
}

#[test]
fn arbitrary_conjunction_query_is_not_distributed_or_given_extra_slots() {
    let end = Instant::now() + Duration::from_secs(20);
    let token = CancellationToken::new();
    let control = SourceControl::new(end, &token);
    let original = source(ChcOp::And);
    let spec = GhostPairSpec::analyze(original.source_problem(), 1);
    let raw = rewrite_source(&original, &spec, &control).expect("existing whole query");
    assert_eq!(raw.clauses().len(), 2);
    assert_eq!(
        raw.clauses()[1].body.constraint,
        original.source_problem().clauses()[1].body.constraint
    );
    assert_eq!(spec.n, 1);
}

#[test]
fn private_query_split_preserves_the_same_original_sticky_refusal() {
    let end = Instant::now() + Duration::from_secs(20);
    let token = CancellationToken::new();
    let control = SourceControl::new(end, &token);
    let original = source(ChcOp::Or);
    let spec = GhostPairSpec::analyze(original.source_problem(), 1);
    control.stop();
    assert!(rewrite_source(&original, &spec, &control).is_none());
    assert!(control.poll().is_none());
    assert!(rewrite_source(&original, &spec, &control).is_none());
}
