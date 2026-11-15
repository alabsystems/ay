// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::ChcSort;
use ay_core::Sort;
use ay_model_check::{ArrayValue, ModelValue, SnapshotKind, SnapshotNode};

mod native;
mod ownership;
mod topology;

fn control(token: &CancellationToken) -> SourceControl<'_> {
    SourceControl::new(Instant::now() + Duration::from_secs(20), token)
}

const SOURCE: &str = "(set-logic HORN)
         (declare-fun unused ((_ BitVec 8)) (_ BitVec 8))
         (declare-fun ay_qcex_0 ((_ BitVec 8)) Bool)
         (declare-fun P ((Array (_ BitVec 64) (_ BitVec 8))) Bool)
         (assert (forall ((a (Array (_ BitVec 64) (_ BitVec 8))))
           (=> (forall ((ay_qcex_0 (_ BitVec 64)))
                 (= (select a ay_qcex_0) (select a ay_qcex_0))) (P a))))
         (assert (forall ((a (Array (_ BitVec 64) (_ BitVec 8)))
                          (b (Array (_ BitVec 64) (_ BitVec 8))))
           (=> (and (P a) (= a b)) false)))
         (check-sat)";

fn source() -> QuantifiedChcProblem {
    QuantifiedChcProblem::parse_smtlib(SOURCE).unwrap()
}

fn render<'a>(
    source: &'a QuantifiedChcProblem,
    token: &CancellationToken,
) -> render::CompleteRendered<'a> {
    render::render_complete(source, &[0, 1], &[vec![], vec![0]], &control(token)).unwrap()
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
        finite(7),
        &bv(0, 64),
        &bv(1 << 40, 64),
        &bv(0, 64),
        &mut 100_000,
    )
    .unwrap()
}

fn bindings(
    rendered: &render::CompleteRendered<'_>,
    snapshot: &Arc<ArraySnapshot>,
) -> Vec<QuantifiedChcCompleteTraceBinding> {
    rendered
        .original
        .bindings
        .iter()
        .map(|entry| QuantifiedChcCompleteTraceBinding {
            occurrence: entry.occurrence,
            variable: entry.variable.clone(),
            value: QuantifiedChcCompleteValue::FunctionalArray(Arc::clone(snapshot)),
        })
        .collect()
}

// Pins themselves confer no credential. These DATA-only fixtures have no
// scalar functions; public acquisition tests retain the genuine full registry.
fn data_source() -> QuantifiedChcProblem {
    let input = SOURCE.replace("(declare-fun unused ((_ BitVec 8)) (_ BitVec 8))", "");
    QuantifiedChcProblem::parse_smtlib(&input).unwrap()
}

#[test]
fn complete_shared_capture_is_one_lambda_in_one_original_conjunction() {
    let token = CancellationToken::new();
    let source = data_source();
    let rendered = render(&source, &token);
    let registry = registry(&source, &control(&token)).unwrap();
    let bindings = bindings(&rendered, &range());
    let output = pins::render(
        &rendered,
        &bindings,
        &[],
        &source,
        &registry,
        &control(&token),
    )
    .unwrap();
    assert_eq!(output.matches("(assert ").count(), 1);
    assert_eq!(output.matches("(lambda ((").count(), 1);
    assert_eq!(output.matches("(check-sat)").count(), 1);
    assert_eq!(output.matches("(forall ((").count(), 1);
    for payload in &rendered.assertions {
        assert!(output.contains(&rendered.original.obligation[payload.clone()]));
    }
    let environment =
        snapshots::build(&rendered.original, &bindings, &source, &control(&token)).unwrap();
    assert!(environment
        .bindings
        .iter()
        .all(|root| root == &environment.bindings[0]));
    // The unused source declaration is reserved, not only selected-path names.
    assert!(!environment
        .definitions
        .iter()
        .any(|node| node.name == "ay_qcex_0"));
    assert!(!output.contains("(define-fun ay_qcex_"));
    ay_frontend::parse(&output).unwrap();
}

#[test]
fn complete_source_generated_ranges_match_every_legacy_original_payload() {
    let token = CancellationToken::new();
    let source = source();
    let complete = render(&source, &token);
    let legacy =
        render::render_with_bindings(&source, &[0, 1], &[vec![], vec![0]], &control(&token))
            .unwrap();
    assert_eq!(complete.original.obligation, legacy.obligation);
    assert_eq!(complete.assertions.len(), 4);
    assert_eq!(complete.original.bindings.len(), 3);
    assert!(complete
        .original
        .obligation
        .contains("(declare-fun unused "));
    for payload in &complete.assertions {
        assert_eq!(
            &complete.original.obligation[payload.start - 8..payload.start],
            "(assert "
        );
        assert_eq!(
            &complete.original.obligation[payload.end..payload.end + 2],
            ")\n"
        );
    }
    assert!(source.source_smtlib().contains("unused"));
}

#[test]
fn complete_pin_membership_refuses_wrong_occurrence_name_sort_or_order_atomically() {
    let token = CancellationToken::new();
    let source = data_source();
    let rendered = render(&source, &token);
    let registry = registry(&source, &control(&token)).unwrap();
    let mut bindings = bindings(&rendered, &range());
    for kind in 0..4 {
        let original = bindings[0].variable.clone();
        match kind {
            0 => bindings[0].occurrence = usize::MAX,
            1 => bindings[0].variable.name.push_str("_foreign"),
            2 => {
                bindings[0].variable.sort =
                    ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::Bool))
            }
            _ => bindings.swap(0, 1),
        }
        let owner = control(&token);
        assert!(pins::render(&rendered, &bindings, &[], &source, &registry, &owner).is_none());
        assert!(owner.debit(0, 0).is_none());
        if kind == 3 {
            bindings.swap(0, 1);
        }
        bindings[0].occurrence = rendered.original.bindings[0].occurrence;
        bindings[0].variable = original;
    }
}
