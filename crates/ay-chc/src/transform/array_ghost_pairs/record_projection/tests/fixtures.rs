// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;

pub(super) fn deadline() -> ay_core::time::Instant {
    ay_core::time::Instant::now() + std::time::Duration::from_secs(600)
}

pub(super) fn no_functions(control: &SourceControl<'_>) -> RetainedFunctions {
    // A quantified source is only well formed with a query clause; an empty
    // clause list is rejected as `NoQuery` before any function is retained.
    // The clause carries no functions, so "no functions" still holds.
    let empty = QuantifiedChcProblem::new(ChcProblem::new(), empty_query()).unwrap();
    controlled::retain(&empty, control).unwrap()
}

/// The minimal well-formed clause list: a query with an empty body.
pub(super) fn empty_query() -> Vec<QuantifiedHornClause> {
    vec![QuantifiedHornClause::new(
        HornClause::query(ClauseBody::empty()),
        vec![],
    )]
}

pub(super) fn array() -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::BitVec(2)), Box::new(ChcSort::Bool))
}

pub(super) fn fields() -> Vec<(String, ChcSort)> {
    vec![
        ("flag".into(), ChcSort::Bool),
        ("len".into(), ChcSort::BitVec(2)),
        ("data".into(), array()),
    ]
}

pub(super) fn record() -> ChcSort {
    ChcSort::Datatype {
        name: "R".into(),
        constructors: crate::ChcDtConstructors::new(vec![ChcDtConstructor {
            name: "make-r".into(),
            selectors: fields()
                .into_iter()
                .map(|(name, sort)| ChcDtSelector { name, sort })
                .collect(),
        }]),
    }
}

pub(super) fn var(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, sort))
}

pub(super) fn op(op: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(op, args.into_iter().map(Arc::new).collect())
}

pub(super) fn select(name: &str, sort: ChcSort, value: ChcExpr) -> ChcExpr {
    ChcExpr::FuncApp(name.into(), sort, vec![Arc::new(value)])
}

pub(super) fn declarations() -> ChcProblem {
    let mut problem = ChcProblem::new();
    problem.add_datatype_def("R".into(), vec![("make-r".into(), fields())]);
    problem.declare_predicate("P", vec![record(), ChcSort::BitVec(2)]);
    problem.set_fixedpoint_format();
    problem
}

pub(super) fn source(record_name: &str, binder: &str, scalar: &str) -> QuantifiedChcProblem {
    let (declarations, clauses) = inputs(record_name, binder, scalar);
    QuantifiedChcProblem::new(declarations, clauses).unwrap()
}

fn inputs(
    record_name: &str,
    binder: &str,
    scalar: &str,
) -> (ChcProblem, Vec<QuantifiedHornClause>) {
    let r = var(record_name, record());
    let n = var(scalar, ChcSort::BitVec(2));
    let args = vec![r.clone(), n.clone()];
    let binder = ChcVar::new(binder, ChcSort::BitVec(2));
    let premise = UniversalPremise::new(
        binder.clone(),
        op(
            ChcOp::Select,
            vec![select("data", array(), r.clone()), ChcExpr::Var(binder)],
        ),
    );
    let body = ClauseBody::new(
        vec![(PredicateId::new(0), args.clone())],
        Some(op(ChcOp::Eq, vec![select("len", ChcSort::BitVec(2), r), n])),
    );
    let clause = HornClause::new(
        body,
        ClauseHead::Predicate(PredicateId::new(0), args.clone()),
    );
    let query = || {
        QuantifiedHornClause::new(
            HornClause::query(ClauseBody::new(
                vec![(PredicateId::new(0), args.clone())],
                Some(ChcExpr::Bool(false)),
            )),
            vec![],
        )
    };
    (
        declarations(),
        vec![
            QuantifiedHornClause::new(clause, vec![premise]),
            query(),
            query(),
        ],
    )
}

pub(super) fn with_unused_record() -> QuantifiedChcProblem {
    let (mut declarations, clauses) = inputs("r", "i", "n");
    declarations.add_datatype_def(
        "Unused".into(),
        vec![(
            "make-unused".into(),
            vec![("unused-flag".into(), ChcSort::Bool)],
        )],
    );
    QuantifiedChcProblem::new(declarations, clauses).unwrap()
}
