// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::quantified::{QuantifiedHornClause, UniversalPremise};
use crate::{ChcDtConstructor, ChcDtSelector, ChcOp, ChcProblem, ChcVar, ClauseBody, HornClause};
use std::time::Duration;

pub(super) fn bv(width: u32) -> ChcSort {
    ChcSort::BitVec(width)
}
pub(super) fn variable(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, sort))
}
fn array(value: ChcSort) -> ChcSort {
    ChcSort::Array(Box::new(bv(64)), Box::new(value))
}
fn operation(op: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(op, args.into_iter().map(Arc::new).collect())
}
pub(super) fn length(a: ChcExpr, row: ChcExpr) -> ChcExpr {
    ChcExpr::FuncApp(
        "len".into(),
        bv(64),
        vec![Arc::new(ChcExpr::select(a, row))],
    )
}
pub(super) fn read(a: ChcExpr, row: ChcExpr, column: ChcExpr) -> ChcExpr {
    ChcExpr::select(
        ChcExpr::FuncApp(
            "data".into(),
            array(bv(8)),
            vec![Arc::new(ChcExpr::select(a, row))],
        ),
        column,
    )
}
pub(super) fn control(token: &CancellationToken) -> SourceControl<'_> {
    SourceControl::new(
        Instant::now().checked_add(Duration::from_secs(60)).unwrap(),
        token,
    )
}

pub(super) fn fixture(array_name: &str, reverse: bool) -> QuantifiedChcProblem {
    let fields = vec![
        ("len".to_owned(), bv(64)),
        ("data".to_owned(), array(bv(8))),
    ];
    let record = ChcSort::Datatype {
        name: "Vec".into(),
        constructors: crate::ChcDtConstructors::new(vec![ChcDtConstructor {
            name: "mkVec".into(),
            selectors: fields
                .iter()
                .map(|(name, sort)| ChcDtSelector {
                    name: name.clone(),
                    sort: sort.clone(),
                })
                .collect(),
        }]),
    };
    let mut declarations = ChcProblem::new();
    declarations.add_datatype_def("Vec".into(), vec![("mkVec".into(), fields)]);
    let p = declarations.declare_predicate("P", vec![array(record.clone()), bv(8)]);
    let a = variable(array_name, array(record));
    let fill = variable("fill", bv(8));
    let args = vec![a.clone(), fill.clone()];
    let i = variable("i", bv(64));
    let j = variable("j", bv(64));
    let matrix = ChcExpr::implies(
        operation(ChcOp::BvULt, vec![j.clone(), length(a.clone(), i.clone())]),
        ChcExpr::eq(read(a.clone(), i, j), fill.clone()),
    );
    let premise = UniversalPremise::with_binders(
        vec![ChcVar::new("i", bv(64)), ChcVar::new("j", bv(64))],
        matrix,
    )
    .unwrap();
    let mut clauses = vec![QuantifiedHornClause::new(
        HornClause::new(ClauseBody::empty(), ClauseHead::Predicate(p, args.clone())),
        vec![premise],
    )];
    let (query_predicate, query_args) = if reverse {
        let q = declarations.declare_predicate("Q", vec![bv(8), a.sort()]);
        let reordered = vec![fill.clone(), a.clone()];
        clauses.push(QuantifiedHornClause::new(
            HornClause::new(
                ClauseBody::new(vec![(p, args.clone())], None),
                ClauseHead::Predicate(q, reordered.clone()),
            ),
            vec![],
        ));
        (q, reordered)
    } else {
        (p, args)
    };
    let r = variable("r", bv(64));
    let c = variable("c", bv(64));
    let bad = ChcExpr::and_all([
        operation(ChcOp::BvUGe, vec![r.clone(), ChcExpr::BitVec(32, 64)]),
        operation(ChcOp::BvUGe, vec![c.clone(), ChcExpr::BitVec(32, 64)]),
        operation(ChcOp::BvULt, vec![c.clone(), length(a.clone(), r.clone())]),
        ChcExpr::ne(read(a, r, c), fill),
    ]);
    clauses.push(QuantifiedHornClause::new(
        HornClause::query(ClauseBody::new(
            vec![(query_predicate, query_args)],
            Some(bad),
        )),
        vec![],
    ));
    QuantifiedChcProblem::new(declarations, clauses).unwrap()
}
