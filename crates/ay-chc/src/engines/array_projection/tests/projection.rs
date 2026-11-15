// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn exact_r22_constant_initializer_erases_to_the_committed_scalar_problem() {
    let original = source();
    let before = original.clone();
    let ClauseHead::Predicate(_, arguments) = &original.clauses()[0].head else {
        panic!("source fact");
    };
    assert!(matches!(
        arguments[0],
        ChcExpr::ConstArray(ChcSort::BitVec(64), _)
    ));
    let projection = project(&original);
    assert_fixed_erasure(&original, projection.reduced());
    let scalar = ChcParser::parse(R22_SCALAR).unwrap();
    assert_eq!(
        projection.reduced().normalized_input(),
        scalar.normalized_input()
    );
    assert!(Projection::new(&scalar, &mut || true).is_none());
    same_original(&before, &original);
}

#[test]
fn clause_actions_query_ordinals_and_nonpredicate_metadata_survive_unchanged() {
    let mut original = source();
    let first = original.declare_action("enter");
    let second = original.declare_action("advance");
    original.clauses_mut()[0].action_id = Some(first);
    original.clauses_mut()[3].action_id = Some(second);
    original.mark_stripped_body_forall();
    original.add_datatype_def("UnusedMetadata".into(), vec![("unit".into(), Vec::new())]);
    original.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
        false,
    ))));
    assert_eq!(original.pruned_false_query_count(), 1);
    let before = original.clone();
    let projection = project(&original);
    let reduced = projection.reduced();
    assert_fixed_erasure(&original, reduced);
    assert!(reduced.is_fixedpoint_format());
    assert!(reduced.has_stripped_body_forall());
    assert_eq!(reduced.action_names(), original.action_names());
    assert_eq!(reduced.datatype_defs(), original.datatype_defs());
    assert_eq!(
        reduced.pruned_false_query_count(),
        original.pruned_false_query_count()
    );
    assert_eq!(
        reduced.pruned_false_query_ids(),
        original.pruned_false_query_ids()
    );
    same_original(&before, &original);
}

#[test]
fn body_joins_and_observed_array_contents_are_preserved_not_declared_dead() {
    let mut original = source();
    let head = original.lookup_predicate("head").unwrap();
    let a = variable("a", array_sort());
    let b = variable("b", array_sort());
    let i = variable("i", ChcSort::BitVec(64));
    let select_a = ChcExpr::select(a.clone(), i.clone());
    let select_b = ChcExpr::select(b.clone(), i.clone());
    let constraint = ChcExpr::eq(select_a, select_b);
    let clause = &mut original.clauses_mut()[1];
    clause.body.predicates.push((head, vec![b, i]));
    clause.body.constraint = Some(ChcExpr::and(
        clause.body.constraint.take().unwrap(),
        constraint,
    ));
    assert_eq!(clause.body.predicates.len(), 2);
    let before = original.clone();
    let projection = project(&original);
    assert_fixed_erasure(&original, projection.reduced());
    assert_eq!(projection.reduced().clauses()[1].body.predicates.len(), 2);
    assert!(projection.reduced().clauses()[1]
        .body
        .constraint
        .as_ref()
        .unwrap()
        .vars()
        .iter()
        .any(|var| matches!(var.sort, ChcSort::Array(..))));
    same_original(&before, &original);
}

#[test]
fn retained_scalar_selects_and_several_interior_array_columns_keep_their_positions() {
    let mut original = signature_problem(vec![
        ChcSort::Bool,
        array_sort(),
        ChcSort::BitVec(32),
        array_sort(),
        ChcSort::Int,
    ]);
    let id = original.lookup_predicate("p").unwrap();
    let a = variable("a", array_sort());
    let b = variable("b", array_sort());
    let value = ChcExpr::select(a.clone(), ChcExpr::BitVec(0, 64));
    original.add_clause(HornClause::fact(
        ChcExpr::Bool(true),
        id,
        vec![ChcExpr::Bool(true), a, value.clone(), b, ChcExpr::Int(7)],
    ));
    let projection = project(&original);
    assert_fixed_erasure(&original, projection.reduced());
    assert_eq!(
        projection.reduced().predicates()[0].arg_sorts,
        [ChcSort::Bool, ChcSort::BitVec(32), ChcSort::Int]
    );
    let ClauseHead::Predicate(_, arguments) = &projection.reduced().clauses()[0].head else {
        panic!("fact head");
    };
    assert_eq!(arguments, &[ChcExpr::Bool(true), value, ChcExpr::Int(7)]);
}

#[test]
fn bad_predicate_ids_arities_and_argument_types_decline_without_mutating_source() {
    for case in 0..8 {
        let mut malformed = source();
        match case {
            0 => {
                malformed.clauses_mut()[0].head =
                    ClauseHead::Predicate(PredicateId::new(999), vec![])
            }
            1 => malformed.clauses_mut()[1].body.predicates[0].0 = PredicateId::new(999),
            2 => {
                let ClauseHead::Predicate(_, args) = &mut malformed.clauses_mut()[0].head else {
                    unreachable!()
                };
                args.pop();
            }
            3 => {
                malformed.clauses_mut()[1].body.predicates[0]
                    .1
                    .push(ChcExpr::Bool(true));
            }
            4 => {
                let ClauseHead::Predicate(_, args) = &mut malformed.clauses_mut()[0].head else {
                    unreachable!()
                };
                args[1] = ChcExpr::Bool(true);
            }
            5 => malformed.clauses_mut()[1].body.predicates[0].1[0] = ChcExpr::BitVec(0, 32),
            6 => {
                let ClauseHead::Predicate(_, args) = &mut malformed.clauses_mut()[0].head else {
                    unreachable!()
                };
                // The erased array has the expected result sort, but its
                // element expression is malformed. Erasure must not hide it.
                args[0] = ChcExpr::ConstArray(
                    ChcSort::BitVec(64),
                    Arc::new(ChcExpr::Op(
                        ChcOp::BvAdd,
                        vec![
                            Arc::new(ChcExpr::BitVec(0, 32)),
                            Arc::new(ChcExpr::Bool(true)),
                        ],
                    )),
                );
            }
            _ => {
                let mut query = HornClause::query(ClauseBody::constraint(ChcExpr::Bool(false)));
                query.body.predicates.push((PredicateId::new(999), vec![]));
                malformed.add_clause(query);
                assert_eq!(malformed.pruned_false_query_count(), 1);
            }
        }
        let before = format!("{malformed:?}");
        assert!(
            Projection::new(&malformed, &mut || true).is_none(),
            "case {case}"
        );
        assert_eq!(format!("{malformed:?}"), before);
    }
}

#[test]
fn nested_predicate_calls_and_unsupported_sorts_functions_or_markers_decline() {
    let mut nested_constraint = source();
    let error = nested_constraint.lookup_predicate("error").unwrap();
    nested_constraint.clauses_mut()[1].body.constraint =
        Some(ChcExpr::PredicateApp("error".into(), error, vec![]));
    assert!(Projection::new(&nested_constraint, &mut || true).is_none());

    let mut nested_argument = signature_problem(vec![array_sort(), ChcSort::Bool]);
    let p = nested_argument.lookup_predicate("p").unwrap();
    let q = nested_argument.declare_predicate("q", vec![]);
    nested_argument.add_clause(HornClause::fact(
        ChcExpr::Bool(true),
        p,
        vec![
            variable("a", array_sort()),
            ChcExpr::PredicateApp("q".into(), q, vec![]),
        ],
    ));
    assert!(Projection::new(&nested_argument, &mut || true).is_none());

    for sort in [
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(array_sort())),
        ChcSort::Uninterpreted("U".into()),
        ChcSort::Datatype {
            name: "D".into(),
            constructors: crate::ChcDtConstructors::new(vec![]),
        },
        ChcSort::BitVec(0),
    ] {
        let unsupported = signature_problem(vec![array_sort(), sort]);
        assert!(Projection::new(&unsupported, &mut || true).is_none());
    }
    for expression in [
        ChcExpr::FuncApp("f".into(), ChcSort::BitVec(64), vec![]),
        ChcExpr::ConstArrayMarker(ChcSort::BitVec(64)),
    ] {
        let mut unsupported = source();
        let ClauseHead::Predicate(_, args) = &mut unsupported.clauses_mut()[0].head else {
            unreachable!()
        };
        args[1] = expression;
        assert!(Projection::new(&unsupported, &mut || true).is_none());
    }
}
