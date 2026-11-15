// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) enum Change {
    None,
    UnusedRecord,
    UnusedPredicate,
    Premise,
    BinderOrder,
}

fn var(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, sort))
}

fn op(op: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(op, args.into_iter().map(Arc::new).collect())
}

pub(super) fn source(change: Change) -> QuantifiedChcProblem {
    let mut declarations = ChcProblem::new();
    declarations.add_datatype_def(
        "Unused record".into(),
        vec![(
            "mk_unused".into(),
            vec![(
                "field".into(),
                ChcSort::BitVec(if matches!(change, Change::UnusedRecord) {
                    3
                } else {
                    2
                }),
            )],
        )],
    );
    let p = declarations.declare_predicate("P", vec![ChcSort::BitVec(2)]);
    declarations.declare_predicate(
        if matches!(change, Change::UnusedPredicate) {
            "changed"
        } else {
            "unused"
        },
        vec![],
    );
    let mut binders = vec![
        ChcVar::new("i", ChcSort::BitVec(2)),
        ChcVar::new("j", ChcSort::BitVec(2)),
    ];
    if matches!(change, Change::BinderOrder) {
        binders.swap(0, 1);
    }
    let matrix = op(
        ChcOp::Implies,
        vec![
            op(
                ChcOp::Eq,
                vec![var("i", ChcSort::BitVec(2)), var("j", ChcSort::BitVec(2))],
            ),
            if matches!(change, Change::Premise) {
                ChcExpr::Bool(false)
            } else {
                var("matrix", ChcSort::Bool)
            },
        ],
    );
    let premise = UniversalPremise::with_binders(binders, matrix).unwrap();
    let x = var("x", ChcSort::BitVec(2));
    let y = var("y", ChcSort::BitVec(2));
    QuantifiedChcProblem::new(
        declarations,
        vec![
            QuantifiedHornClause::new(
                HornClause::fact(var("i", ChcSort::Bool), p, vec![x.clone()]),
                vec![premise.clone()],
            ),
            QuantifiedHornClause::new(
                HornClause::query(ClauseBody::new(
                    vec![(p, vec![x.clone()]), (p, vec![y.clone()])],
                    Some(op(
                        ChcOp::And,
                        vec![var("i", ChcSort::Bool), op(ChcOp::Ne, vec![x, y])],
                    )),
                )),
                vec![premise],
            ),
            QuantifiedHornClause::new(
                HornClause::query(ClauseBody::constraint(ChcExpr::Bool(false))),
                vec![],
            ),
        ],
    )
    .unwrap()
}

pub(super) fn control(token: &CancellationToken) -> SourceControl<'_> {
    SourceControl::new(Instant::now() + Duration::from_secs(30), token)
}

pub(super) fn unchecked_trace(
    source: &QuantifiedChcProblem,
    token: &CancellationToken,
) -> QuantifiedChcTrace {
    unchecked_tree(
        source,
        vec![0, 0, 1],
        vec![vec![], vec![], vec![0, 1]],
        token,
    )
}

// Deliberately private and unsealed: this assembles internally consistent
// metadata to test borrowed view membership, never a claimed native SAT.
pub(super) fn unchecked_tree(
    source: &QuantifiedChcProblem,
    indices: Vec<usize>,
    edges: Vec<Vec<usize>>,
    token: &CancellationToken,
) -> QuantifiedChcTrace {
    unchecked_tree_models(source, indices, edges, vec![], token)
}

pub(super) fn unchecked_tree_models(
    source: &QuantifiedChcProblem,
    indices: Vec<usize>,
    edges: Vec<Vec<usize>>,
    functions: Vec<ScalarFunctionModel>,
    token: &CancellationToken,
) -> QuantifiedChcTrace {
    let rendered = render::render_with_bindings(source, &indices, &edges, &control(token)).unwrap();
    let bindings = rendered
        .bindings
        .iter()
        .map(|binding| QuantifiedChcTraceBinding {
            occurrence: binding.occurrence,
            variable: binding.variable.clone(),
            value: match binding.variable.sort {
                ChcSort::Bool => SmtValue::Bool(true),
                ChcSort::BitVec(2) => SmtValue::BitVec(
                    u128::from(binding.occurrence == 1 || binding.variable.name == "y"),
                    2,
                ),
                _ => panic!("fixture sort"),
            },
        })
        .collect::<Vec<_>>();
    let registry = registry(source, &control(token)).unwrap();
    let pinned = pins::render(
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
        pinned_obligation: pinned,
    }
}
