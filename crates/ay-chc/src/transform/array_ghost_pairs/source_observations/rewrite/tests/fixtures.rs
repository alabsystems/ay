// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn bv(width: u32) -> ChcSort {
    ChcSort::BitVec(width)
}
pub(super) fn array(width: u32, value: ChcSort) -> ChcSort {
    ChcSort::Array(Box::new(bv(width)), Box::new(value))
}
pub(super) fn variable(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, sort))
}
pub(super) fn control(token: &CancellationToken) -> SourceControl<'_> {
    SourceControl::new(Instant::now() + Duration::from_secs(60), token)
}
pub(super) fn record(name: &str, fields: Vec<(&str, ChcSort)>) -> ChcSort {
    ChcSort::Datatype {
        name: name.into(),
        constructors: crate::ChcDtConstructors::new(vec![ChcDtConstructor {
            name: format!("make_{name}"),
            selectors: fields
                .into_iter()
                .map(|(name, sort)| ChcDtSelector {
                    name: name.into(),
                    sort,
                })
                .collect(),
        }]),
    }
}
pub(super) fn fixture(
    body: Vec<ChcExpr>,
    head: Vec<ChcExpr>,
    records: Vec<ChcSort>,
) -> QuantifiedChcProblem {
    fixture_with_constraint(body, head, records, None)
}
pub(super) fn fixture_with_constraint(
    body: Vec<ChcExpr>,
    head: Vec<ChcExpr>,
    records: Vec<ChcSort>,
    constraint: Option<ChcExpr>,
) -> QuantifiedChcProblem {
    let mut declarations = ChcProblem::new();
    for record in records {
        let ChcSort::Datatype { name, constructors } = record else {
            panic!("record")
        };
        declarations.add_datatype_def(
            name,
            constructors
                .iter()
                .map(|ctor| {
                    (
                        ctor.name.clone(),
                        ctor.selectors
                            .iter()
                            .map(|field| (field.name.clone(), field.sort.clone()))
                            .collect(),
                    )
                })
                .collect(),
        );
    }
    let p = declarations.declare_predicate("P", body.iter().map(ChcExpr::sort).collect());
    let q = declarations.declare_predicate("Q", head.iter().map(ChcExpr::sort).collect());
    QuantifiedChcProblem::new(
        declarations,
        vec![
            QuantifiedHornClause::new(
                HornClause::new(
                    ClauseBody::new(vec![(p, body)], constraint),
                    ClauseHead::Predicate(q, head.clone()),
                ),
                vec![],
            ),
            QuantifiedHornClause::new(
                HornClause::query(ClauseBody::new(vec![(q, head)], None)),
                vec![],
            ),
        ],
    )
    .unwrap()
}
pub(super) fn try_mapping(
    source: &QuantifiedChcProblem,
    layout: &Layout,
    control: &SourceControl<'_>,
) -> Option<Vec<Option<usize>>> {
    let clause = &source.source_problem().clauses()[0];
    let (id, args) = &clause.body.predicates[0];
    transport::correspondence(*id, args, &clause.head, layout, control)
}
pub(super) fn mapping(
    source: &QuantifiedChcProblem,
    layout: &Layout,
    control: &SourceControl<'_>,
) -> Vec<Option<usize>> {
    try_mapping(source, layout, control).unwrap()
}
pub(super) fn simple() -> QuantifiedChcProblem {
    let a = variable("a", array(4, bv(8)));
    let b = variable("b", array(4, bv(8)));
    fixture(vec![a.clone(), b.clone()], vec![b, a], vec![])
}
