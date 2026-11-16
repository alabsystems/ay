// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{ClauseBody, HornClause};

#[test]
fn constant_key_projection_keeps_the_write_read_relation_without_source_mutation() {
    let original = source(9, false);
    let before = original.clone();
    let projected = project(&original);
    for (old, reduced) in original
        .predicates()
        .iter()
        .zip(projected.reduced.predicates())
    {
        assert_eq!((old.id, &old.name), (reduced.id, &reduced.name));
        assert_eq!(
            reduced.arg_sorts,
            [ChcSort::BitVec(32), ChcSort::BitVec(64)]
        );
    }
    let ClauseHead::Predicate(_, fact) = &projected.reduced.clauses()[0].head else {
        panic!("fact");
    };
    assert_eq!(fact, &[bv(5, 32), bv(0, 64)]);
    let ClauseHead::Predicate(_, write) = &projected.reduced.clauses()[1].head else {
        panic!("write");
    };
    assert_eq!(write[0], bv(9, 32));
    let original_query = original
        .queries()
        .next()
        .unwrap()
        .body
        .constraint
        .as_ref()
        .unwrap();
    assert!(matches!(original_query.sort(), ChcSort::Bool));
    assert!(projected
        .reduced
        .queries()
        .next()
        .unwrap()
        .body
        .constraint
        .as_ref()
        .unwrap()
        .vars()
        .iter()
        .all(|var| !matches!(var.sort, ChcSort::Array(..))));
    same_source(&before, &original);
}

#[test]
fn actions_query_occurrences_and_nullary_predicates_survive_the_candidate_transform() {
    let mut original = source(9, false);
    let action = original.declare_action("write_cell");
    original.clauses_mut()[1].action_id = Some(action);
    let error = original.declare_predicate("error", vec![]);
    original.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        error,
        vec![],
    )])));
    original.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
        false,
    ))));
    let before = original.clone();
    let projected = project(&original);
    assert_eq!(projected.reduced.action_names(), original.action_names());
    assert_eq!(
        projected.reduced.pruned_false_query_ids(),
        original.pruned_false_query_ids()
    );
    for (old, reduced) in original.clauses().iter().zip(projected.reduced.clauses()) {
        assert_eq!(old.action_id, reduced.action_id);
        assert_eq!(old.source_query_ordinal, reduced.source_query_ordinal);
    }
    let lifted = projected
        .lift(&candidate(projected.reduced()), &mut || true)
        .unwrap();
    assert_eq!(lifted.get(&error).unwrap().vars, [] as [ChcVar; 0]);
    same_source(&before, &original);
}

#[test]
fn scalar_only_symbolic_key_and_unsupported_sort_inputs_decline_unchanged() {
    let scalar = ChcParser::parse("(declare-fun p (Int) Bool) (assert (p 0)) (check-sat)").unwrap();
    assert!(Projection::new(&scalar, &mut || true).is_none());
    let mut symbolic = source(9, false);
    let query = symbolic.clauses_mut().last_mut().unwrap();
    query.body.constraint = Some(ChcExpr::eq(
        ChcExpr::select(
            variable("a", symbolic_array()),
            variable("i", ChcSort::BitVec(64)),
        ),
        bv(9, 32),
    ));
    let before = symbolic.clone();
    assert!(Projection::new(&symbolic, &mut || true).is_none());
    same_source(&before, &symbolic);
    let mut unsupported = source(9, false);
    unsupported.declare_predicate(
        "unused",
        vec![ChcSort::Array(
            Box::new(ChcSort::Int),
            Box::new(symbolic_array()),
        )],
    );
    assert!(Projection::new(&unsupported, &mut || true).is_none());
}

fn symbolic_array() -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::BitVec(32)))
}

#[test]
fn bad_ids_argument_arity_and_child_types_decline_before_scalarization() {
    for case in 0..4 {
        let mut malformed = source(9, false);
        match case {
            0 => malformed.clauses_mut()[1].body.predicates[0].0 = PredicateId::new(999),
            1 => {
                malformed.clauses_mut()[1].body.predicates[0].1.pop();
            }
            2 => malformed.clauses_mut()[1].body.predicates[0].1[0] = bv(0, 32),
            _ => {
                malformed.clauses_mut()[1].body.constraint =
                    Some(operation(ChcOp::BvULt, bv(0, 64), ChcExpr::Bool(true)))
            }
        }
        let before = malformed.clone();
        assert!(Projection::new(&malformed, &mut || true).is_none());
        same_source(&before, &malformed);
    }
}

#[test]
fn conservative_depth_fanout_occurrence_and_signature_caps_decline() {
    use super::super::admission::{Scan, MAX_ARITY, MAX_DEPTH};
    // `ChcExpr::not` eliminates double negation, so a chain built with it
    // collapses to a depth-1 constant. Nest explicitly: the leaf of
    // `nested(levels)` sits at depth `levels + 1` (the root is depth 1).
    let nested = |levels: usize| {
        let mut expr = ChcExpr::Bool(true);
        for _ in 0..levels {
            expr = ChcExpr::Op(ChcOp::Not, vec![Arc::new(expr)]);
        }
        expr
    };
    assert!(Scan::default()
        .expression(&nested(MAX_DEPTH - 1), &mut || true)
        .is_some());
    assert!(Scan::default()
        .expression(&nested(MAX_DEPTH), &mut || true)
        .is_none());
    #[expect(
        clippy::rc_clone_in_vec_init,
        reason = "the arity-cap fixture intentionally shares one immutable boolean node across every edge"
    )]
    let wide = ChcExpr::Op(
        ChcOp::And,
        vec![Arc::new(ChcExpr::Bool(true)); MAX_ARITY + 1],
    );
    assert!(Scan::default().expression(&wide, &mut || true).is_none());
    let mut shared = ChcExpr::Bool(true);
    for _ in 0..14 {
        let child = Arc::new(shared);
        shared = ChcExpr::Op(ChcOp::And, vec![child.clone(), child]);
    }
    assert!(Scan::default().expression(&shared, &mut || true).is_none());
    let mut large = source(9, false);
    large.declare_predicate("wide", vec![ChcSort::Int; MAX_ARITY + 1]);
    assert!(Projection::new(&large, &mut || true).is_none());
}

#[test]
fn excessive_text_and_array_observations_decline_before_opaque_rewrites() {
    use super::super::admission::Scan;
    let enormous = variable(&"v".repeat(1025), ChcSort::Int);
    assert!(Scan::default()
        .expression(&enormous, &mut || true)
        .is_none());
    let mut observed = source(9, false);
    let reads: Vec<_> = (0..17)
        .map(|index| {
            ChcExpr::eq(
                ChcExpr::select(variable("a", symbolic_array()), bv(index, 64)),
                bv(9, 32),
            )
        })
        .collect();
    observed.clauses_mut().last_mut().unwrap().body.constraint = Some(ChcExpr::and_all(reads));
    assert!(Projection::new(&observed, &mut || true).is_none());
}
