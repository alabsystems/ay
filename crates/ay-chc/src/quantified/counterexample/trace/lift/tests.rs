// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Pure source/manifest tests. `prepare` is untrusted data, never a SAT seal.

use super::super::QuantifiedChcTraceBinding;
use super::*;
use crate::quantified::counterexample::render_oracle as oracle;

mod fixtures;
mod native;

pub(super) fn control(token: &CancellationToken) -> SourceControl<'_> {
    SourceControl::new(Instant::now() + Duration::from_secs(60), token)
}

fn associated(row: &QuantifiedChcQueryObligation, source: &QuantifiedChcProblem) {
    let token = CancellationToken::new();
    assert!(row
        .authenticate_aggregate(
            source,
            Instant::now() + Duration::from_secs(60),
            &token,
            &control(&token),
        )
        .is_some());
}

#[test]
fn early_direct_query_maps_original_positions_without_appending_a_marker() {
    let token = CancellationToken::new();
    let aggregate = fixtures::scalar(fixtures::Query::Direct);
    let rows = fixtures::rows(&aggregate);
    assert_eq!(rows.len(), 1);
    let row = &rows[0];
    assert_eq!(row.id().query_clause_index(), 0);
    assert_eq!(row.id().defining_clause_index(), None);
    associated(row, &aggregate);
    let trace = fixtures::scalar_trace(row, &token);
    assert!(authenticate_slice(&trace, row.problem(), &control(&token)).is_some());
    let prepared = prepare(&trace, row.id(), &aggregate, &control(&token)).unwrap();
    assert_eq!(prepared.derivation.clause_indices, [2, 0]);
    assert_eq!(prepared.derivation.premise_steps, [vec![], vec![0]]);
    assert_eq!(prepared.pinned.matches("(forall ((").count(), 1);
    assert_eq!(oracle::models(&prepared.pinned), vec![vec![0, 0]]);
    assert_eq!(trace.clause_indices(), &[1, 0]);
    assert_eq!(trace.source_smtlib(), row.problem().source_smtlib());
}

#[test]
fn unfolded_early_query_repins_fresh_names_reserved_only_by_unused_aggregate_locals() {
    let token = CancellationToken::new();
    let aggregate = fixtures::scalar(fixtures::Query::Marker);
    let rows = fixtures::rows(&aggregate);
    let row = &rows[0];
    assert_eq!(row.id().defining_clause_index(), Some(3));
    associated(row, &aggregate);
    let trace = fixtures::scalar_trace(row, &token);
    let pointer = trace.bindings().as_ptr();
    let prepared = prepare(&trace, row.id(), &aggregate, &control(&token)).unwrap();
    assert_eq!(prepared.derivation.clause_indices, [2, 3, 0]);
    assert_eq!(
        prepared.derivation.premise_steps,
        [vec![], vec![0], vec![1]]
    );
    assert_eq!(prepared.pinned.matches("(forall ((").count(), 2);
    assert!(trace
        .replay_obligation()
        .contains("(declare-const ay_qcex_0 "));
    assert!(!prepared.pinned.contains("(declare-const ay_qcex_0 "));
    assert!(prepared.pinned.contains("(declare-const ay_qcex_2 "));
    assert_ne!(prepared.pinned, trace.replay_obligation());
    assert_eq!(oracle::models(&prepared.pinned), vec![vec![0, 0]]);
    assert_eq!(oracle::models(trace.replay_obligation()), vec![vec![0, 0]]);
    assert_eq!(trace.bindings().as_ptr(), pointer);
    assert_eq!(trace.bindings()[0].variable().name, "x");
    assert_eq!(trace.bindings()[1].variable().name, "y");
    assert_eq!(trace.bindings()[0].occurrence(), 0);
    assert_eq!(trace.bindings()[1].occurrence(), 1);
}

#[test]
fn recursive_marker_definition_remains_an_ordinary_occurrence_before_the_final_unfold() {
    let token = CancellationToken::new();
    let aggregate = fixtures::recursive();
    let rows = fixtures::rows(&aggregate);
    let row = rows
        .iter()
        .find(|row| row.id().defining_clause_index() == Some(2))
        .unwrap();
    associated(row, &aggregate);
    let trace = fixtures::unchecked(
        row.problem(),
        vec![0, 1, 2, 1, 3],
        vec![vec![], vec![0], vec![1], vec![2], vec![3]],
        vec![],
        &token,
    );
    assert!(authenticate_slice(&trace, row.problem(), &control(&token)).is_some());
    let prepared = prepare(&trace, row.id(), &aggregate, &control(&token)).unwrap();
    assert_eq!(prepared.derivation.clause_indices, [0, 1, 2, 1, 2, 3]);
    assert_eq!(
        prepared.derivation.premise_steps,
        [vec![], vec![0], vec![1], vec![2], vec![3], vec![4]]
    );
    assert_eq!(prepared.pinned.matches("(forall ((").count(), 3);
    assert_eq!(oracle::models(&prepared.pinned), vec![Vec::<u64>::new()]);
    assert!(trace.bindings().is_empty());
}

#[test]
fn nested_record_values_ordered_stores_and_complete_global_functions_are_reused() {
    let token = CancellationToken::new();
    let aggregate = fixtures::nested();
    let rows = fixtures::rows(&aggregate);
    let row = &rows[0];
    associated(row, &aggregate);
    let rendered =
        render::render_with_bindings(row.problem(), &[0, 1], &[vec![], vec![0]], &control(&token))
            .unwrap();
    let registry = registry(row.problem(), &control(&token)).unwrap();
    let value = values::decode(
        &fixtures::nested_value(),
        &rendered.bindings[0].variable.sort,
        &registry,
        &control(&token),
    )
    .unwrap();
    let trace = fixtures::unchecked_with_models(
        row.problem(),
        vec![0, 1],
        vec![vec![], vec![0]],
        vec![value.clone(), value],
        fixtures::functions(),
        &token,
    );
    let bindings = trace.bindings().as_ptr();
    let functions = trace.function_models().as_ptr();
    assert!(authenticate_slice(&trace, row.problem(), &control(&token)).is_some());
    let prepared = prepare(&trace, row.id(), &aggregate, &control(&token)).unwrap();
    assert_eq!(prepared.derivation.clause_indices, [0, 1, 2]);
    assert_eq!(prepared.pinned.matches("(store ").count(), 4);
    assert_eq!(prepared.pinned.matches("(forall ((").count(), 1);
    for function in trace.function_models() {
        assert!(prepared.pinned.contains(function.definition_smtlib()));
    }
    assert_eq!(trace.bindings()[0].value(), trace.bindings()[1].value());
    assert_eq!(trace.bindings().as_ptr(), bindings);
    assert_eq!(trace.function_models().as_ptr(), functions);
}

#[test]
fn stale_pins_refuse_but_coherent_unsatisfying_pins_remain_only_prepared_data() {
    let token = CancellationToken::new();
    let aggregate = fixtures::scalar(fixtures::Query::Marker);
    let rows = fixtures::rows(&aggregate);
    let row = &rows[0];
    let mut trace = fixtures::scalar_trace(row, &token);
    trace.bindings[0].value = SmtValue::BitVec(1, 2);
    assert!(authenticate_slice(&trace, row.problem(), &control(&token)).is_none());
    fixtures::repin(row.problem(), &mut trace, &token);
    assert!(authenticate_slice(&trace, row.problem(), &control(&token)).is_some());
    let prepared = prepare(&trace, row.id(), &aggregate, &control(&token)).unwrap();
    // Exact pin reconstruction is not SAT authority. This independent tiny
    // interpreter finds no assignment; native.rs checks actual lift refusal.
    assert_eq!(
        oracle::models(&prepared.pinned),
        [] as [std::vec::Vec<u64>; 0]
    );
    assert_eq!(
        oracle::models(trace.replay_obligation()),
        [] as [std::vec::Vec<u64>; 0]
    );
    trace.bindings[0].occurrence = 1;
    assert!(prepare(&trace, row.id(), &aggregate, &control(&token)).is_none());
}

#[test]
fn shared_budget_and_observed_cancellation_refuse_preparation_without_mutating_the_trace() {
    let token = CancellationToken::new();
    let aggregate = fixtures::scalar(fixtures::Query::Marker);
    let rows = fixtures::rows(&aggregate);
    let row = &rows[0];
    let trace = fixtures::scalar_trace(row, &token);
    let pins = trace.replay_obligation().to_owned();
    let limited = control(&token);
    assert!(limited.bytes(64 * 1024 * 1024).is_some());
    assert!(prepare(&trace, row.id(), &aggregate, &limited).is_none());
    assert!(limited.poll().is_none());
    let cancelled = control(&token);
    token.cancel();
    assert!(cancelled.poll().is_none());
    token.reset();
    assert!(prepare(&trace, row.id(), &aggregate, &cancelled).is_none());
    assert!(prepare(&trace, row.id(), &aggregate, &control(&token)).is_some());
    assert_eq!(trace.replay_obligation(), pins);
}

#[test]
fn public_pre_native_refusals_return_the_original_trace_and_owned_allocations() {
    let token = CancellationToken::new();
    let aggregate = fixtures::scalar(fixtures::Query::Marker);
    let foreign = fixtures::scalar(fixtures::Query::Direct);
    let rows = fixtures::rows(&aggregate);
    let row = &rows[0];
    for refusal in 0..7 {
        let mut trace = fixtures::scalar_trace(row, &token);
        let time = match refusal {
            0 => Duration::ZERO,
            1 => Duration::MAX,
            _ => Duration::from_secs(30),
        };
        if refusal == 2 {
            trace.base.memory_budget = Some(0);
        }
        if refusal == 3 {
            token.cancel();
        }
        let original_pins = trace.replay_obligation().to_owned();
        let original_pointer = trace.bindings().as_ptr();
        let source = if refusal == 4 { &foreign } else { &aggregate };
        let parent_memory =
            (refusal == 5).then(|| SmtContext::scoped_thread_term_memory_budget(Some(0)));
        let parent_deadline =
            (refusal == 6).then(|| ScopedSmtDeadline::install_until(Instant::now()));
        // Every case fails before a solver can be invoked.
        let error = trace
            .lift_to_aggregate(row, source, time, &token)
            .unwrap_err();
        drop((parent_memory, parent_deadline));
        assert_eq!(error.trace().bindings().as_ptr(), original_pointer);
        assert_eq!(error.trace().replay_obligation(), original_pins);
        assert_eq!(error.trace().source_smtlib(), row.problem().source_smtlib());
        assert_eq!(error.trace().clause_indices(), &[1, 0]);
        assert_eq!(error.trace().premise_steps(), &[vec![], vec![0]]);
        let recovered = error.into_trace();
        token.reset();
        assert_eq!(recovered.bindings().as_ptr(), original_pointer);
        assert!(authenticate_slice(&recovered, row.problem(), &control(&token)).is_some());
    }
}
