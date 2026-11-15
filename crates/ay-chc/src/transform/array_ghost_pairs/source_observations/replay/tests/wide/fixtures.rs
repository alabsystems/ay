// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn bits(width: u32) -> ChcSort {
    ChcSort::BitVec(width)
}
pub(super) fn array(key: u32, cell: u32) -> ChcSort {
    ChcSort::Array(Box::new(bits(key)), Box::new(bits(cell)))
}
pub(super) fn high136() -> ChcExpr {
    operation(
        ChcOp::BvConcat,
        vec![ChcExpr::BitVec(128, 8), ChcExpr::BitVec(0, 128)],
    )
}
pub(super) fn wide_source() -> QuantifiedChcProblem {
    let sorts = [array(64, 8), array(72, 32), array(136, 136), bits(136)];
    let args: Vec<_> = ["data", "table72", "table136", "fill"]
        .into_iter()
        .zip(&sorts)
        .map(|(name, sort)| variable(name, sort.clone()))
        .collect();
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", sorts.to_vec());
    let constraint = operation(
        ChcOp::Eq,
        vec![
            args[2].clone(),
            ChcExpr::ConstArray(bits(136), Arc::new(args[3].clone())),
        ],
    );
    let i = ChcVar::new("i", bits(64));
    let premise = UniversalPremise::new(
        i.clone(),
        operation(
            ChcOp::Eq,
            vec![
                operation(ChcOp::Select, vec![args[0].clone(), ChcExpr::var(i)]),
                ChcExpr::BitVec(0, 8),
            ],
        ),
    );
    let fact = HornClause::new(
        ClauseBody::new(vec![], Some(constraint)),
        ClauseHead::Predicate(p, args.clone()),
    );
    let keys = [
        variable("j", bits(64)),
        variable("key72", bits(72)),
        variable("key136", bits(136)),
    ];
    let expected = [
        ChcExpr::BitVec(0, 8),
        ChcExpr::BitVec(0, 32),
        args[3].clone(),
    ];
    let bad = operation(
        ChcOp::Or,
        (0..3)
            .map(|index| {
                operation(
                    ChcOp::Ne,
                    vec![
                        operation(
                            ChcOp::Select,
                            vec![args[index].clone(), keys[index].clone()],
                        ),
                        expected[index].clone(),
                    ],
                )
            })
            .collect(),
    );
    let guarded = operation(
        ChcOp::And,
        vec![
            operation(
                ChcOp::BvUGe,
                vec![keys[1].clone(), ChcExpr::BitVec(1_u128 << 71, 72)],
            ),
            operation(ChcOp::BvUGe, vec![keys[2].clone(), high136()]),
            bad,
        ],
    );
    let query = HornClause::query(ClauseBody::new(vec![(p, args)], Some(guarded)));
    QuantifiedChcProblem::new(
        declarations,
        vec![
            QuantifiedHornClause::new(fact, vec![premise]),
            QuantifiedHornClause::new(query, vec![]),
        ],
    )
    .unwrap()
}

pub(super) fn wide_model(
    source: &QuantifiedChcProblem,
    control: &SourceControl<'_>,
) -> ObservationModel {
    let layout = Layout::analyze(source, control).unwrap();
    let p = source.source_problem().predicates()[0].id;
    let vars = layout.canonical(p).unwrap().to_vec();
    assert_eq!(vars.len(), 10);
    let formula = operation(
        ChcOp::Eq,
        vec![ChcExpr::var(vars[9].clone()), ChcExpr::var(vars[3].clone())],
    );
    let mut model = InvariantModel::new();
    model.set(p, PredicateInterpretation::new(vars, formula));
    ObservationModel { layout, model }
}

pub(super) fn set_formula(model: &mut ObservationModel, formula: ChcExpr) {
    let p = PredicateId::new(0);
    let vars = model.layout.canonical(p).unwrap().to_vec();
    model
        .model
        .set(p, PredicateInterpretation::new(vars, formula));
}
