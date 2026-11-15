// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private fixtures are DATA, not source SAT or complete-trace credentials.

use super::*;
use ay_core::Sort;
use ay_model_check::{ArrayValue, ModelValue, SnapshotKind, SnapshotNode};

mod graphs;
mod native;
mod refusal;

const MEMORY: usize = 128 * 1024 * 1024;
const WALL: Duration = Duration::from_secs(20);
const SOURCE: &str = "(set-logic HORN)
 (declare-fun P ((Array (_ BitVec 64) (_ BitVec 8))) Bool)
 (assert (forall ((a (Array (_ BitVec 64) (_ BitVec 8))))
   (=> (and (forall ((i (_ BitVec 64))) (= (select a i) (select a i)))
            (= (select a (_ bv0 64)) (_ bv9 8))) (P a))))
 (assert (forall ((a (Array (_ BitVec 64) (_ BitVec 8)))
                  (b (Array (_ BitVec 64) (_ BitVec 8))))
   (=> (and (P a) (= a b)) false))) (check-sat)";

// ModelValue intentionally has no global PartialEq; these fixtures require
// exact scalar variant, bit width, and arbitrary-precision integer identity.
fn assert_scalar_eq(actual: &ModelValue, expected: &ModelValue) {
    match (actual, expected) {
        (ModelValue::Bool(actual), ModelValue::Bool(expected)) => assert_eq!(actual, expected),
        (
            ModelValue::BitVec {
                width: actual_width,
                value: actual_value,
            },
            ModelValue::BitVec {
                width: expected_width,
                value: expected_value,
            },
        ) => {
            assert_eq!(actual_width, expected_width, "bit-vector width");
            assert_eq!(actual_value, expected_value, "bit-vector integer payload");
        }
        _ => panic!("expected matching Bool or BitVec model values"),
    }
}

fn source() -> QuantifiedChcProblem {
    QuantifiedChcProblem::parse_smtlib(SOURCE).unwrap()
}

fn control(token: &CancellationToken) -> SourceControl<'_> {
    SourceControl::new(Instant::now() + WALL, token)
}

fn bv(value: u64, width: u32) -> ModelValue {
    ModelValue::bitvec(value.into(), width)
}

fn sort() -> Sort {
    Sort::array(Sort::bitvec(64), Sort::bitvec(8))
}

fn finite(value: u64) -> Arc<ArraySnapshot> {
    ArraySnapshot::finite(
        ArrayValue {
            default: bv(value, 8),
            store: Vec::new(),
        },
        &sort(),
        &mut 100_000,
    )
    .unwrap()
}

fn range() -> Arc<ArraySnapshot> {
    ArraySnapshot::range_copy(
        finite(0),
        finite(9),
        &bv(0, 64),
        &bv(1 << 40, 64),
        &bv(0, 64),
        &mut 100_000,
    )
    .unwrap()
}

fn unchecked(
    problem: &QuantifiedChcProblem,
    array: &Arc<ArraySnapshot>,
    token: &CancellationToken,
) -> QuantifiedChcCompleteTrace {
    let indices = vec![0, 1];
    let premises = vec![vec![], vec![0]];
    let rendered = render::render_complete(problem, &indices, &premises, &control(token)).unwrap();
    let bindings: Vec<QuantifiedChcCompleteTraceBinding> = rendered
        .original
        .bindings
        .iter()
        .map(|entry| QuantifiedChcCompleteTraceBinding {
            occurrence: entry.occurrence,
            variable: entry.variable.clone(),
            value: QuantifiedChcCompleteValue::FunctionalArray(Arc::clone(array)),
        })
        .collect();
    let registry = registry(problem, &control(token)).unwrap();
    let pinned_obligation = pins::render(
        &rendered,
        &bindings,
        &[],
        problem,
        &registry,
        &control(token),
    )
    .unwrap();
    QuantifiedChcCompleteTrace {
        base: QuantifiedChcCounterexample {
            source: Arc::from(problem.source_smtlib()),
            clause_indices: indices,
            premise_steps: premises.clone(),
            topology_sha256: derivation::fingerprint(&[0, 1], &premises, &control(token)).unwrap(),
            obligation: rendered.original.obligation,
            memory_budget: Some(MEMORY),
        },
        bindings,
        functions: Vec::new(),
        pinned_obligation,
    }
}

fn wire(problem: &QuantifiedChcProblem, token: &CancellationToken) -> wire::Wire {
    let trace = unchecked(problem, &range(), token);
    let registry = registry(problem, &control(token)).unwrap();
    let mut catalog = arrays::Catalog::new(&control(token), trace.bindings.len()).unwrap();
    let steps = bindings::export(&trace, &registry, &mut catalog, &control(token)).unwrap();
    wire::Wire {
        schema: wire::SCHEMA.to_owned(),
        source: problem.source_smtlib().to_owned(),
        steps,
        graphs: catalog.graphs,
        functions: "(model)".into(),
        pinned_sha256: codec_transport::digest(
            trace.replay_obligation().as_bytes(),
            &control(token),
        )
        .unwrap(),
    }
}

fn repin(problem: &QuantifiedChcProblem, wire: &mut wire::Wire, token: &CancellationToken) {
    let indices = wire
        .steps
        .iter()
        .map(|s| s.clause_index)
        .collect::<Vec<_>>();
    let premises = wire
        .steps
        .iter()
        .map(|s| s.premises.clone())
        .collect::<Vec<_>>();
    let rendered = render::render_complete(problem, &indices, &premises, &control(token)).unwrap();
    let registry = registry(problem, &control(token)).unwrap();
    let arrays = arrays::import(&wire.graphs, &control(token)).unwrap();
    let bindings = bindings::import(wire, &rendered, &registry, &arrays, &control(token)).unwrap();
    let functions = codec_functions::import(&wire.functions, problem, &control(token)).unwrap();
    let text = pins::render(
        &rendered,
        &bindings,
        &functions,
        problem,
        &registry,
        &control(token),
    )
    .unwrap();
    wire.pinned_sha256 = codec_transport::digest(text.as_bytes(), &control(token)).unwrap();
}

fn read(array: &ArraySnapshot, index: u64) -> ModelValue {
    array
        .read_with_stop(&bv(index, 64), &mut 100_000, &mut || false)
        .unwrap()
}
