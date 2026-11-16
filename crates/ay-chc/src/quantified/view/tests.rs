// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::quantified::records::Registry;
use crate::quantified::{QuantifiedHornClause, UniversalPremise};
use crate::{ChcDtConstructor, ChcDtSelector, ChcOp, ChcProblem, ChcVar, ClauseBody};
use std::sync::Arc;

fn record(
    declarations: &mut ChcProblem,
    name: &str,
    constructor: &str,
    fields: Vec<(&str, ChcSort)>,
) -> ChcSort {
    declarations.add_datatype_def(
        name.to_owned(),
        vec![(
            constructor.to_owned(),
            fields
                .iter()
                .map(|(name, sort)| (name.to_string(), sort.clone()))
                .collect(),
        )],
    );
    ChcSort::Datatype {
        name: name.to_owned(),
        constructors: crate::ChcDtConstructors::new(vec![ChcDtConstructor {
            name: constructor.to_owned(),
            selectors: fields
                .into_iter()
                .map(|(name, sort)| ChcDtSelector {
                    name: name.to_owned(),
                    sort,
                })
                .collect(),
        }]),
    }
}

fn declarations() -> ChcProblem {
    let mut out = ChcProblem::new();
    record(
        &mut out,
        "ZUnused",
        "mk_unused",
        vec![("unused_bits", ChcSort::BitVec(136))],
    );
    let inner = record(
        &mut out,
        "AInner",
        "mk_inner",
        vec![(
            "inner_data",
            ChcSort::Array(Box::new(ChcSort::BitVec(72)), Box::new(ChcSort::BitVec(8))),
        )],
    );
    record(&mut out, "Outer", "mk_outer", vec![("outer_inner", inner)]);
    out.declare_predicate("ZPredicate", vec![ChcSort::Bool]);
    out.declare_predicate("APredicate", vec![ChcSort::BitVec(136)]);
    out
}

fn variable(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, sort))
}

fn operation(op: ChcOp, arguments: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(op, arguments.into_iter().map(Arc::new).collect())
}

fn fixture() -> QuantifiedChcProblem {
    let predicate = PredicateId::new(0);
    let outer = variable("x", ChcSort::Bool);
    let matrix = operation(
        ChcOp::And,
        vec![
            operation(
                ChcOp::BvULt,
                vec![
                    variable("x", ChcSort::BitVec(64)),
                    variable("length", ChcSort::BitVec(64)),
                ],
            ),
            operation(
                ChcOp::Eq,
                vec![
                    variable("matrix_only", ChcSort::BitVec(8)),
                    ChcExpr::BitVec(7, 8),
                ],
            ),
        ],
    );
    let premises = vec![
        UniversalPremise::with_binders(
            vec![
                ChcVar::new("x", ChcSort::BitVec(64)),
                ChcVar::new("unused_joint", ChcSort::BitVec(32)),
            ],
            matrix,
        )
        .unwrap(),
        UniversalPremise::new(
            ChcVar::new("x", ChcSort::BitVec(1)),
            operation(
                ChcOp::Eq,
                vec![variable("x", ChcSort::BitVec(1)), ChcExpr::BitVec(1, 1)],
            ),
        ),
        UniversalPremise::new(
            ChcVar::new("unused", ChcSort::BitVec(64)),
            ChcExpr::Bool(true),
        ),
    ];
    let false_query = || {
        QuantifiedHornClause::new(
            HornClause::query(ClauseBody::constraint(ChcExpr::Bool(false))),
            vec![],
        )
    };
    QuantifiedChcProblem::new_with_functions(
        declarations(),
        vec![
            QuantifiedChcFunction::new(
                "z_unused_function".into(),
                vec![ChcSort::BitVec(136)],
                ChcSort::BitVec(1),
            ),
            QuantifiedChcFunction::new("a_nullary".into(), vec![], ChcSort::BitVec(136)),
        ],
        vec![
            QuantifiedHornClause::new(
                HornClause::fact(ChcExpr::Bool(false), predicate, vec![outer.clone()]),
                vec![],
            ),
            QuantifiedHornClause::new(
                HornClause::query(ClauseBody::new(
                    vec![(predicate, vec![outer])],
                    Some(operation(
                        ChcOp::And,
                        vec![ChcExpr::Bool(true), ChcExpr::Bool(false)],
                    )),
                )),
                premises,
            ),
            false_query(),
            false_query(),
        ],
    )
    .unwrap()
}

#[test]
fn complete_declarations_and_source_identity_are_borrowed_in_canonical_order() {
    let problem = fixture();
    let source = problem.source_view();
    assert!(std::ptr::eq(
        source.source_smtlib(),
        problem.source_smtlib()
    ));
    assert!(std::ptr::eq(
        source.predicates(),
        problem.source_problem().predicates()
    ));
    assert_eq!(
        source
            .predicates()
            .iter()
            .map(|p| p.name.as_str())
            .collect::<Vec<_>>(),
        ["ZPredicate", "APredicate"]
    );
    for predicate in source.predicates() {
        assert!(std::ptr::eq(
            predicate,
            source.predicate(predicate.id).unwrap()
        ));
    }
    assert!(source.predicate(PredicateId::new(2)).is_none());
    assert!(source.predicate(PredicateId::new(u32::MAX)).is_none());
    let datatypes = source.datatype_declarations();
    assert!(std::ptr::eq(
        datatypes,
        problem.datatype_declarations.as_slice()
    ));
    let names: Vec<_> = datatypes
        .iter()
        .map(|sort| match sort {
            ChcSort::Datatype { name, .. } => name.as_str(),
            _ => panic!("record declaration"),
        })
        .collect();
    assert_eq!(names, ["AInner", "Outer", "ZUnused"]);
    let ChcSort::Datatype { constructors, .. } = &datatypes[1] else {
        panic!("Outer");
    };
    assert_eq!(constructors[0].selectors[0].sort, datatypes[0]);
    let ChcSort::Datatype { constructors, .. } = &datatypes[2] else {
        panic!("unused record");
    };
    assert_eq!(constructors[0].selectors[0].sort, ChcSort::BitVec(136));
    let functions = source.function_declarations();
    assert!(std::ptr::eq(functions, problem.function_declarations()));
    assert_eq!(
        functions
            .iter()
            .map(QuantifiedChcFunction::name)
            .collect::<Vec<_>>(),
        ["z_unused_function", "a_nullary"]
    );
    assert_eq!(functions[0].arg_sorts(), &[ChcSort::BitVec(136)]);
    assert_eq!(functions[0].result_sort(), &ChcSort::BitVec(1));
    assert_eq!(functions[1].arg_sorts(), []);
    assert_eq!(functions[1].result_sort(), &ChcSort::BitVec(136));
}

#[test]
fn raw_clause_order_false_queries_and_all_attached_payloads_are_exact_borrows() {
    let problem = fixture();
    let source = problem.source_view();
    let raw = problem.source_problem().clauses();
    let mut clauses = source.clauses();
    assert_eq!(clauses.len(), 4);
    assert_eq!(
        clauses.clone().map(|c| c.index()).collect::<Vec<_>>(),
        [0, 1, 2, 3]
    );
    assert_eq!(clauses.next().unwrap().index(), 0);
    assert_eq!(clauses.next_back().unwrap().index(), 3);
    assert_eq!(clauses.len(), 2);
    for (index, clause) in source.clauses().enumerate() {
        assert_eq!(clause.index(), index);
        assert!(std::ptr::eq(
            clause.body_predicates(),
            raw[index].body.predicates.as_slice()
        ));
        assert!(std::ptr::eq(clause.head(), &raw const raw[index].head));
        assert!(std::ptr::eq(
            clause.premises(),
            problem.premises()[index].as_slice()
        ));
        assert!(std::ptr::eq(
            clause.constraint().unwrap(),
            raw[index].body.constraint.as_ref().unwrap()
        ));
    }
    assert_eq!(
        source
            .clauses()
            .map(|c| c.source_query_ordinal())
            .collect::<Vec<_>>(),
        [None, Some(0), Some(1), Some(2)]
    );
    assert_eq!(
        source.clause(0).unwrap().constraint(),
        Some(&ChcExpr::Bool(false))
    );
    assert!(
        matches!(source.clause(1).unwrap().constraint(), Some(ChcExpr::Op(ChcOp::And, args)) if args.len() == 2)
    );
    for index in [2, 3] {
        let clause = source.clause(index).unwrap();
        assert_eq!(clause.constraint(), Some(&ChcExpr::Bool(false)));
        assert!(matches!(clause.head(), ClauseHead::False));
        assert!(clause.premises().is_empty());
    }
    assert!(source.clause(4).is_none());
    assert!(source.clause(usize::MAX).is_none());
}

#[test]
fn complete_joint_and_sibling_scopes_preserve_matrix_only_free_variables() {
    let problem = fixture();
    // These references outlive the temporary source/clause view, not the source.
    let premises = problem.source_view().clause(1).unwrap().premises();
    let body = problem.source_view().clause(1).unwrap().body_predicates();
    assert_eq!(premises.len(), 3);
    assert_eq!(body[0].1, [variable("x", ChcSort::Bool)]);
    assert_eq!(
        premises[0].binders().cloned().collect::<Vec<_>>(),
        [
            ChcVar::new("x", ChcSort::BitVec(64)),
            ChcVar::new("unused_joint", ChcSort::BitVec(32)),
        ]
    );
    assert_eq!(premises[1].binder(), &ChcVar::new("x", ChcSort::BitVec(1)));
    assert_eq!(
        premises[2].binder(),
        &ChcVar::new("unused", ChcSort::BitVec(64))
    );
    assert_eq!(premises[2].matrix(), &ChcExpr::Bool(true));
    for (borrowed, original) in premises.iter().zip(&problem.premises()[1]) {
        assert!(std::ptr::eq(borrowed.matrix(), original.matrix()));
        for (binder, raw_binder) in borrowed.binders().zip(original.binders()) {
            assert!(std::ptr::eq(binder, raw_binder));
        }
    }
    let matrix_variables = premises[0].matrix().vars();
    assert!(matrix_variables.contains(&ChcVar::new("matrix_only", ChcSort::BitVec(8))));
    assert!(matrix_variables.contains(&ChcVar::new("length", ChcSort::BitVec(64))));
    assert!(!problem.source_problem().clauses()[1]
        .vars()
        .iter()
        .any(|v| v.name == "matrix_only"));
}

#[test]
fn empty_declarations_and_fixedpoint_flag_need_no_reconstruction() {
    assert!(matches!(
        QuantifiedChcProblem::new(ChcProblem::new(), vec![]),
        Err(crate::ChcError::NoQuery)
    ));
    let empty = QuantifiedChcProblem::new(
        ChcProblem::new(),
        vec![QuantifiedHornClause::new(
            HornClause::query(ClauseBody::empty()),
            vec![],
        )],
    )
    .unwrap();
    let view = empty.source_view();
    assert_eq!(view.clauses().len(), 1);
    assert!(view.clauses().next().unwrap().constraint().is_none());
    assert!(view.clause(1).is_none());
    assert!(view.predicates().is_empty());
    assert_eq!(view.datatype_declarations(), []);
    assert_eq!(view.function_declarations(), []);
    assert!(!view.is_fixedpoint_format());
    let fixedpoint = QuantifiedChcProblem::parse_smtlib(
        "(set-logic HORN) (declare-rel P ()) (rule P) (query P)",
    )
    .unwrap();
    assert!(fixedpoint.source_view().is_fixedpoint_format());
    assert!(fixedpoint
        .source_view()
        .source_smtlib()
        .contains("; fixedpoint=true"));
    assert_eq!(fixedpoint.source_view().clauses().len(), 2);
}

#[test]
fn registry_transfer_keeps_the_already_admitted_vector_allocation() {
    let declarations = declarations();
    let registry = Registry::new(&declarations).unwrap();
    let first = std::ptr::from_ref(registry.record_sorts().next().unwrap());
    let records = registry.into_record_sorts();
    assert_eq!(records.as_ptr(), first);
    assert_eq!(records.len(), 3);
}
