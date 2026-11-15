// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Unsealed data fixtures, not acquired SAT evidence. Pure tests stop before
//! native replay; native.rs separately qualifies the consuming public API.

use super::*;
use crate::quantified::{QuantifiedHornClause, UniversalPremise};
use crate::{ChcExpr, ChcProblem, ChcSort, ClauseBody, ClauseHead, HornClause};

pub(super) fn unchecked(
    source: &QuantifiedChcProblem,
    indices: Vec<usize>,
    edges: Vec<Vec<usize>>,
    values: Vec<SmtValue>,
    token: &CancellationToken,
) -> QuantifiedChcTrace {
    unchecked_with_models(source, indices, edges, values, Vec::new(), token)
}

pub(super) fn unchecked_with_models(
    source: &QuantifiedChcProblem,
    indices: Vec<usize>,
    edges: Vec<Vec<usize>>,
    values: Vec<SmtValue>,
    functions: Vec<ScalarFunctionModel>,
    token: &CancellationToken,
) -> QuantifiedChcTrace {
    let rendered = render::render_with_bindings(source, &indices, &edges, &control(token)).unwrap();
    assert_eq!(rendered.bindings.len(), values.len());
    let bindings = rendered
        .bindings
        .iter()
        .zip(values)
        .map(|(binding, value)| QuantifiedChcTraceBinding {
            occurrence: binding.occurrence,
            variable: binding.variable.clone(),
            value,
        })
        .collect::<Vec<_>>();
    let registry = registry(source, &control(token)).unwrap();
    let pinned_obligation = pins::render(
        &rendered,
        &bindings,
        &functions,
        source,
        &registry,
        &control(token),
    )
    .unwrap();
    QuantifiedChcTrace {
        base: QuantifiedChcCounterexample {
            source: Arc::from(source.source_smtlib()),
            topology_sha256: derivation::fingerprint(&indices, &edges, &control(token)).unwrap(),
            clause_indices: indices,
            premise_steps: edges,
            obligation: rendered.obligation,
            memory_budget: Some(128 * 1024 * 1024),
        },
        bindings,
        functions,
        pinned_obligation,
    }
}

pub(super) fn repin(
    source: &QuantifiedChcProblem,
    trace: &mut QuantifiedChcTrace,
    token: &CancellationToken,
) {
    let rendered = bound_render(&trace.base, source, &control(token)).unwrap();
    let registry = registry(source, &control(token)).unwrap();
    trace.pinned_obligation = pins::render(
        &rendered,
        &trace.bindings,
        &trace.functions,
        source,
        &registry,
        &control(token),
    )
    .unwrap();
}

pub(super) enum Query {
    Direct,
    Marker,
}

fn matrix() -> UniversalPremise {
    UniversalPremise::with_binders(
        vec![
            ChcVar::new("i", ChcSort::BitVec(2)),
            ChcVar::new("j", ChcSort::BitVec(2)),
        ],
        ChcExpr::Bool(true),
    )
    .unwrap()
}

fn row(
    body: ClauseBody,
    head: ClauseHead,
    premises: Vec<UniversalPremise>,
) -> QuantifiedHornClause {
    QuantifiedHornClause::new(HornClause::new(body, head), premises)
}

fn zero(name: &str) -> (ChcExpr, ChcExpr) {
    let variable = ChcExpr::Var(ChcVar::new(name, ChcSort::BitVec(2)));
    let constraint = ChcExpr::eq(variable.clone(), ChcExpr::BitVec(0, 2));
    (variable, constraint)
}

pub(super) fn scalar(kind: Query) -> QuantifiedChcProblem {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![ChcSort::BitVec(2)]);
    let error = declarations.declare_predicate("error", vec![]);
    let unused = declarations.declare_predicate("Unused", vec![]);
    let (x, x_zero) = zero("x");
    let (y, y_zero) = zero("y");
    let (_, reserved_zero) = zero("ay_qcex_0");
    let query_body = match kind {
        Query::Direct => ClauseBody::new(vec![(p, vec![y.clone()])], Some(y_zero.clone())),
        Query::Marker => ClauseBody::new(vec![(error, vec![])], None),
    };
    let mut clauses = vec![
        row(query_body, ClauseHead::False, vec![]),
        row(
            ClauseBody::new(vec![], Some(reserved_zero)),
            ClauseHead::Predicate(unused, vec![]),
            vec![],
        ),
        row(
            ClauseBody::new(vec![], Some(x_zero)),
            ClauseHead::Predicate(p, vec![x]),
            vec![matrix()],
        ),
    ];
    if matches!(kind, Query::Marker) {
        clauses.push(row(
            ClauseBody::new(vec![(p, vec![y])], Some(y_zero)),
            ClauseHead::Predicate(error, vec![]),
            vec![matrix()],
        ));
    }
    QuantifiedChcProblem::new(declarations, clauses).unwrap()
}

pub(super) fn recursive() -> QuantifiedChcProblem {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    let error = declarations.declare_predicate("error", vec![]);
    QuantifiedChcProblem::new(
        declarations,
        vec![
            row(
                ClauseBody::new(vec![], None),
                ClauseHead::Predicate(error, vec![]),
                vec![matrix()],
            ),
            row(
                ClauseBody::new(vec![(error, vec![])], None),
                ClauseHead::Predicate(p, vec![]),
                vec![],
            ),
            row(
                ClauseBody::new(vec![(p, vec![])], None),
                ClauseHead::Predicate(error, vec![]),
                vec![matrix()],
            ),
            row(
                ClauseBody::new(vec![(error, vec![])], None),
                ClauseHead::False,
                vec![],
            ),
        ],
    )
    .unwrap()
}

pub(super) fn rows(source: &QuantifiedChcProblem) -> Vec<QuantifiedChcQueryObligation> {
    source
        .query_obligations(Duration::from_secs(60), &CancellationToken::new())
        .unwrap()
}

pub(super) fn scalar_trace(
    row: &QuantifiedChcQueryObligation,
    token: &CancellationToken,
) -> QuantifiedChcTrace {
    unchecked(
        row.problem(),
        vec![1, 0],
        vec![vec![], vec![0]],
        vec![SmtValue::BitVec(0, 2), SmtValue::BitVec(0, 2)],
        token,
    )
}

pub(super) fn nested() -> QuantifiedChcProblem {
    QuantifiedChcProblem::parse_smtlib(
        "(set-logic HORN)
         (declare-datatype Inner ((mkInner (len (_ BitVec 64))
           (data (Array (_ BitVec 64) (_ BitVec 8))))))
         (declare-datatype Outer ((mkOuter (flag Bool) (inner Inner))))
         (declare-fun f ((_ BitVec 2)) (_ BitVec 2))
         (declare-fun unused () (_ BitVec 136))
         (declare-fun P (Outer) Bool)
         (declare-fun error () Bool)
         (assert (forall ((r Outer))
           (=> (and (= r r) (forall ((i (_ BitVec 2))) (= (f i) (_ bv0 2)))) (P r))))
         (assert (forall ((r Outer)) (=> (P r) error)))
         (assert (=> error false)) (check-sat)",
    )
    .unwrap()
}

pub(super) fn nested_value() -> ay_dpll::api::ModelValue {
    use ay_dpll::api::ModelValue;
    let bv = |value: u64, width| ModelValue::BitVec {
        value: value.into(),
        width,
    };
    ModelValue::Datatype {
        constructor: "mkOuter".to_owned(),
        args: vec![
            ModelValue::Bool(true),
            ModelValue::Datatype {
                constructor: "mkInner".to_owned(),
                args: vec![
                    bv(65, 64),
                    ModelValue::Array {
                        default: Box::new(bv(7, 8)),
                        stores: vec![(bv(64, 64), bv(9, 8)), (bv(64, 64), bv(7, 8))],
                    },
                ],
            },
        ],
    }
}

pub(super) fn functions() -> Vec<ScalarFunctionModel> {
    let small = ay_core::Sort::bitvec(2);
    let wide = ay_core::Sort::bitvec(136);
    let args = [small.clone()];
    ScalarFunctionModel::decode_smtlib(
        "(model (define-fun f ((i (_ BitVec 2))) (_ BitVec 2) (_ bv0 2))
         (define-fun unused () (_ BitVec 136) (_ bv0 136)))",
        &[("f", args.as_slice(), &small), ("unused", &[], &wide)],
    )
    .unwrap()
}
