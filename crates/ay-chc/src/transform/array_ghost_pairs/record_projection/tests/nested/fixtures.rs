// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;

pub(super) fn make_sort(name: &str, constructor: &str, fields: &[(String, ChcSort)]) -> ChcSort {
    ChcSort::Datatype {
        name: name.into(),
        constructors: crate::ChcDtConstructors::new(vec![ChcDtConstructor {
            name: constructor.into(),
            selectors: fields
                .iter()
                .map(|(name, sort)| ChcDtSelector {
                    name: name.clone(),
                    sort: sort.clone(),
                })
                .collect(),
        }]),
    }
}

pub(super) fn schema(width: u32) -> (ChcProblem, ChcSort, ChcSort) {
    let index = ChcSort::BitVec(width);
    let array = ChcSort::Array(Box::new(index.clone()), Box::new(ChcSort::Bool));
    let fields = vec![
        ("fld_ptr".into(), index.clone()),
        ("fld_len".into(), index.clone()),
        ("fld_cap".into(), index.clone()),
        ("fld_data".into(), array),
    ];
    let vector = make_sort("Vec", "mk-vec", &fields);
    let mut declarations = ChcProblem::new();
    declarations.add_datatype_def("Vec".into(), vec![("mk-vec".into(), fields)]);
    let fields = vec![
        ("fld_vec".into(), vector.clone()),
        ("fld_pos".into(), index),
    ];
    let iterator = make_sort("Iter", "mk-iter", &fields);
    declarations.add_datatype_def("Iter".into(), vec![("mk-iter".into(), fields)]);
    declarations.declare_predicate("P", vec![iterator.clone()]);
    (declarations, vector, iterator)
}

pub(super) fn iterator_source(width: u32) -> QuantifiedChcProblem {
    let (declarations, vector, iterator) = schema(width);
    let it = var("iterator", iterator);
    let value = select("fld_vec", vector, it.clone());
    let array = ChcSort::Array(Box::new(ChcSort::BitVec(width)), Box::new(ChcSort::Bool));
    let binder = ChcVar::new("i", ChcSort::BitVec(width));
    let matrix = op(
        ChcOp::Implies,
        vec![
            op(
                ChcOp::BvULt,
                vec![
                    ChcExpr::Var(binder.clone()),
                    select("fld_len", ChcSort::BitVec(width), value.clone()),
                ],
            ),
            op(
                ChcOp::Select,
                vec![
                    select("fld_data", array, value),
                    ChcExpr::Var(binder.clone()),
                ],
            ),
        ],
    );
    let body = ClauseBody::new(
        vec![(PredicateId::new(0), vec![it.clone()])],
        Some(ChcExpr::Bool(true)),
    );
    let rule = HornClause::new(
        body.clone(),
        ClauseHead::Predicate(PredicateId::new(0), vec![it]),
    );
    let query = HornClause::query(ClauseBody::new(body.predicates, Some(ChcExpr::Bool(false))));
    QuantifiedChcProblem::new(
        declarations,
        vec![
            QuantifiedHornClause::new(rule, vec![UniversalPremise::new(binder, matrix)]),
            QuantifiedHornClause::new(query, vec![]),
        ],
    )
    .unwrap()
}
