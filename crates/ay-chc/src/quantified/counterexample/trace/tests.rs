// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::quantified::counterexample::render_oracle as oracle;
use crate::quantified::QuantifiedChcResult;
use crate::ChcSort;
use ntest::timeout;

mod functions;
mod native;

fn control(token: &CancellationToken) -> SourceControl<'_> {
    SourceControl::new(Instant::now() + Duration::from_secs(30), token)
}

fn scalar_source() -> QuantifiedChcProblem {
    QuantifiedChcProblem::parse_smtlib(
        "(set-logic HORN)
         (declare-fun P ((_ BitVec 2)) Bool)
         (assert (forall ((x (_ BitVec 2)))
           (=> (forall ((i (_ BitVec 2))) (= x x)) (P x))))
         (assert (forall ((x (_ BitVec 2)) (y (_ BitVec 2)))
           (=> (and (P x) (P y) (distinct x y)) false)))
         (check-sat)",
    )
    .unwrap()
}

fn render_source<'a>(
    problem: &'a QuantifiedChcProblem,
    token: &CancellationToken,
) -> render::Rendered<'a> {
    render::render_with_bindings(
        problem,
        &[0, 0, 1],
        &[vec![], vec![], vec![0, 1]],
        &control(token),
    )
    .unwrap()
}

fn assignment(rendered: &render::Rendered<'_>, values: &[u128]) -> Vec<QuantifiedChcTraceBinding> {
    assert_eq!(rendered.bindings.len(), values.len());
    rendered
        .bindings
        .iter()
        .zip(values)
        .map(|(binding, value)| QuantifiedChcTraceBinding {
            occurrence: binding.occurrence,
            variable: binding.variable.clone(),
            value: SmtValue::BitVec(*value, 2),
        })
        .collect()
}

#[test]
fn independent_text_oracle_checks_complete_same_assignment_pins() {
    let token = CancellationToken::new();
    let source = scalar_source();
    let rendered = render_source(&source, &token);
    let registry = registry(&source, &control(&token)).unwrap();
    let mut bindings = assignment(&rendered, &[0, 1, 0, 1]);
    let pinned = pins::render(
        &rendered,
        &bindings,
        &[],
        &source,
        &registry,
        &control(&token),
    )
    .unwrap();
    assert_eq!(oracle::models(&pinned), vec![vec![0, 1, 0, 1]]);
    assert_eq!(pinned.matches("(forall ((").count(), 2);
    assert_eq!(pinned.matches("(check-sat)").count(), 1);
    // Changing one source occurrence cannot silently switch the query's value.
    bindings[0].value = SmtValue::BitVec(1, 2);
    let inconsistent = pins::render(
        &rendered,
        &bindings,
        &[],
        &source,
        &registry,
        &control(&token),
    )
    .unwrap();
    assert_eq!(oracle::models(&inconsistent), [] as [std::vec::Vec<u64>; 0]);
    // Another satisfying assignment is semantically valid but not the retained
    // witness: byte identity must still reject this replacement during recheck.
    let alternative = assignment(&rendered, &[2, 3, 2, 3]);
    let alternative = pins::render(
        &rendered,
        &alternative,
        &[],
        &source,
        &registry,
        &control(&token),
    )
    .unwrap();
    assert_eq!(oracle::models(&alternative), vec![vec![2, 3, 2, 3]]);
    assert_ne!(pinned, alternative);
}

#[test]
fn pin_membership_is_total_ordered_and_exactly_sorted() {
    let token = CancellationToken::new();
    let source = scalar_source();
    let rendered = render_source(&source, &token);
    let registry = registry(&source, &control(&token)).unwrap();
    let mut bindings = assignment(&rendered, &[0, 1, 0, 1]);
    assert!(pins::render(
        &rendered,
        &bindings[..3],
        &[],
        &source,
        &registry,
        &control(&token)
    )
    .is_none());
    bindings.swap(0, 1);
    assert!(pins::render(
        &rendered,
        &bindings,
        &[],
        &source,
        &registry,
        &control(&token)
    )
    .is_none());
    bindings.swap(0, 1);
    bindings[0].occurrence = usize::MAX;
    assert!(pins::render(
        &rendered,
        &bindings,
        &[],
        &source,
        &registry,
        &control(&token)
    )
    .is_none());
    bindings[0].occurrence = 0;
    bindings[0].variable.name.push_str("_foreign");
    assert!(pins::render(
        &rendered,
        &bindings,
        &[],
        &source,
        &registry,
        &control(&token)
    )
    .is_none());
    bindings[0].variable = rendered.bindings[0].variable.clone();
    bindings[0].variable.sort = ChcSort::Bool;
    assert!(pins::render(
        &rendered,
        &bindings,
        &[],
        &source,
        &registry,
        &control(&token)
    )
    .is_none());
    bindings[0].variable = rendered.bindings[0].variable.clone();
    bindings[0].value = SmtValue::BitVec(0, 3);
    assert!(pins::render(
        &rendered,
        &bindings,
        &[],
        &source,
        &registry,
        &control(&token)
    )
    .is_none());
}

#[test]
fn pin_rendering_observes_sticky_controls_and_combined_output_bound() {
    let token = CancellationToken::new();
    let source = scalar_source();
    let mut rendered = render_source(&source, &token);
    let registry = registry(&source, &control(&token)).unwrap();
    let bindings = assignment(&rendered, &[0, 1, 0, 1]);
    let stopped = control(&token);
    token.cancel();
    assert!(pins::render(&rendered, &bindings, &[], &source, &registry, &stopped).is_none());
    token.reset();
    assert!(pins::render(&rendered, &bindings, &[], &source, &registry, &stopped).is_none());
    let exhausted = control(&token);
    exhausted.bytes(64 * 1024 * 1024).unwrap();
    assert!(pins::render(&rendered, &bindings, &[], &source, &registry, &exhausted).is_none());
    rendered.obligation = format!("{}(check-sat)\n", " ".repeat(8 * 1024 * 1024));
    assert!(pins::render(
        &rendered,
        &bindings,
        &[],
        &source,
        &registry,
        &control(&token)
    )
    .is_none());
}

// The following helper assembles metadata ONLY for solver-free boundary tests.
// It is deliberately not a production evidence constructor or a claimed SAT.
fn unchecked_base(
    source: &QuantifiedChcProblem,
    token: &CancellationToken,
) -> QuantifiedChcCounterexample {
    let rendered = render_source(source, token);
    let indices = vec![0, 0, 1];
    let edges = vec![vec![], vec![], vec![0, 1]];
    QuantifiedChcCounterexample {
        source: Arc::from(source.source_smtlib()),
        topology_sha256: derivation::fingerprint(&indices, &edges, &control(token)).unwrap(),
        clause_indices: indices,
        premise_steps: edges,
        obligation: rendered.obligation,
        memory_budget: Some(128 * 1024 * 1024),
    }
}

#[test]
fn bound_manifest_refuses_source_topology_and_script_changes_before_extraction() {
    let token = CancellationToken::new();
    let source = scalar_source();
    let mut base = unchecked_base(&source, &token);
    assert!(bound_render(&base, &source, &control(&token)).is_some());
    base.source = Arc::from("foreign");
    assert!(bound_render(&base, &source, &control(&token)).is_none());
    base.source = Arc::from(source.source_smtlib());
    base.premise_steps[2].swap(0, 1);
    assert!(bound_render(&base, &source, &control(&token)).is_none());
    base.premise_steps[2].swap(0, 1);
    base.obligation.push_str("; changed");
    assert!(bound_render(&base, &source, &control(&token)).is_none());
    assert!(base
        .concrete_trace(&source, Duration::ZERO, &token)
        .is_none());
}
