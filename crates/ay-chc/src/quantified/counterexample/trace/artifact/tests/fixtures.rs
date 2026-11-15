// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private unsealed DATA fixtures. None establishes SAT; only public native
//! export/import in native.rs can seal this assignment after actual replay.

use super::*;

pub(super) fn scalar(token: &CancellationToken) -> (QuantifiedChcProblem, QuantifiedChcTrace) {
    let source = QuantifiedChcProblem::parse_smtlib(
        "(set-logic HORN)
         (declare-fun P ((_ BitVec 2)) Bool)
         (assert (forall ((x (_ BitVec 2)))
           (=> (forall ((i (_ BitVec 2))) (= x x)) (P x))))
         (assert (forall ((x (_ BitVec 2)) (y (_ BitVec 2)))
           (=> (and (P x) (P y) (distinct x y)) false)))
         (check-sat)",
    )
    .unwrap();
    let trace = unchecked(
        &source,
        vec![0, 0, 1],
        vec![vec![], vec![], vec![0, 1]],
        [0, 1, 0, 1].map(|v| SmtValue::BitVec(v, 2)).into(),
        token,
    );
    (source, trace)
}

pub(super) fn unchecked(
    source: &QuantifiedChcProblem,
    indices: Vec<usize>,
    premises: Vec<Vec<usize>>,
    values: Vec<SmtValue>,
    token: &CancellationToken,
) -> QuantifiedChcTrace {
    unchecked_with_models(source, indices, premises, values, Vec::new(), token)
}

pub(super) fn unchecked_with_models(
    source: &QuantifiedChcProblem,
    indices: Vec<usize>,
    premises: Vec<Vec<usize>>,
    values: Vec<SmtValue>,
    functions: Vec<ScalarFunctionModel>,
    token: &CancellationToken,
) -> QuantifiedChcTrace {
    let rendered =
        render::render_with_bindings(source, &indices, &premises, &control(token)).unwrap();
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
    let base = QuantifiedChcCounterexample {
        source: Arc::from(source.source_smtlib()),
        topology_sha256: derivation::fingerprint(&indices, &premises, &control(token)).unwrap(),
        clause_indices: indices,
        premise_steps: premises,
        obligation: rendered.obligation,
        memory_budget: Some(128 * 1024 * 1024),
    };
    QuantifiedChcTrace {
        base,
        bindings,
        functions,
        pinned_obligation,
    }
}

pub(super) fn wire(
    source: &QuantifiedChcProblem,
    trace: &QuantifiedChcTrace,
    token: &CancellationToken,
) -> wire::Wire {
    let registry = registry(source, &control(token)).unwrap();
    wire::export(trace, source, &registry, &control(token)).unwrap()
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
