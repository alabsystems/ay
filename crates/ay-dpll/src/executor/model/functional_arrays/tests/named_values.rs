// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private DATA fixtures do not install SAT/validation/proof authority.

use super::*;

fn current_data() -> Executor {
    let mut exec = prepared("(set-option :produce-models true)(declare-const p Bool)");
    let model = installed(&exec);
    assert!(matches!(confirm(&exec, &model), GateVerdict::ConfirmedSat));
    // This tests the private extraction seam, not the public accepted-SAT gate.
    // The public regression obtains SAT by the actual original solve pipeline.
    exec.last_model = Some(model);
    assert!(exec.last_result.is_none());
    exec
}

#[test]
fn private_complete_batch_preserves_duplicates_and_distinguishes_absent_entries() {
    let exec = current_data();
    let w = variable(&exec, "w");
    let p = variable(&exec, "p");
    let values = exec
        .functional_array_snapshots_for_named_values(&[w, p, w])
        .expect("bound native data");
    assert_eq!(values.len(), 3);
    assert!(values[1].is_none());
    assert!(Arc::ptr_eq(
        values[0].as_ref().expect("first native entry"),
        values[2].as_ref().expect("duplicate native entry"),
    ));
    assert!(exec.last_result.is_none(), "data does not publish SAT");
}

#[test]
fn private_complete_batch_refuses_missing_model_or_nonlive_term() {
    let mut exec = current_data();
    assert!(exec
        .functional_array_snapshots_for_named_values(&[TermId(u32::MAX)])
        .is_err());
    exec.last_model = None;
    assert!(exec
        .functional_array_snapshots_for_named_values(&[])
        .is_err());
}

#[test]
fn private_complete_batch_refuses_stale_query_without_literal_fallback() {
    let mut exec = current_data();
    let w = variable(&exec, "w");
    exec.execute_all(&parse("(assert false)").expect("different query"))
        .expect("original query mutation");
    assert!(exec
        .functional_array_snapshots_for_named_values(&[w])
        .is_err());
}

#[test]
fn private_complete_batch_refuses_wrong_snapshot_sort_atomically() {
    let mut exec = current_data();
    let w = variable(&exec, "w");
    let s = variable(&exec, "s");
    let finite = ay_model_check::ArrayValue {
        default: ModelValue::bitvec(0.into(), 16),
        store: Vec::new(),
    };
    let wrong = ArraySnapshot::finite(
        finite,
        &Sort::array(Sort::bitvec(64), Sort::bitvec(16)),
        &mut 1_024,
    )
    .expect("independently well-typed wrong carrier");
    let data = exec
        .last_model
        .as_mut()
        .expect("original native model")
        .functional_arrays
        .as_mut()
        .expect("original data");
    let index = data
        .entries
        .binary_search_by_key(&w, |(term, _)| *term)
        .expect("w entry");
    data.entries[index].1 = wrong;
    assert!(exec
        .functional_array_snapshots_for_named_values(&[s, w])
        .is_err());
}

#[test]
fn private_complete_batch_cannot_reuse_equal_numeric_ids_from_fresh_terms() {
    let mut exec = current_data();
    let w = variable(&exec, "w");
    let entries = exec
        .ctx
        .terms
        .entries_snapshot_with_progress(&mut |_, _| true)
        .expect("bounded original fixture");
    let (t, f) = exec.ctx.terms.boolean_constant_ids();
    exec.ctx.terms = TermStore::from_entries(entries, t, f, 0);
    assert!(exec
        .functional_array_snapshots_for_named_values(&[w])
        .is_err());
}

#[test]
fn private_complete_batch_all_entries_and_retries_share_native_original_work() {
    let exec = current_data();
    let w = variable(&exec, "w");
    let model = exec.last_model.as_ref().expect("original native model");
    let clone = model.clone();
    let data = model.functional_arrays.as_ref().expect("original data");
    let copied = clone.functional_arrays.as_ref().expect("cloned data");
    assert!(Arc::ptr_eq(&data.work_used, &copied.work_used));
    let before = data.work_used.load(Ordering::Acquire);
    exec.functional_array_snapshots_for_named_values(&[w, w])
        .expect("one owner");
    assert!(data.work_used.load(Ordering::Acquire) > before);
    data.work_used.store(MAX_FUNCTIONAL_WORK, Ordering::Release);
    assert!(exec
        .functional_array_snapshots_for_named_values(&[w])
        .is_err());
    assert!(exec
        .functional_array_snapshots_for_named_values(&[w, w])
        .is_err());
    assert_eq!(data.work_used.load(Ordering::Acquire), REFUSED);
}

#[test]
fn private_complete_batch_keeps_original_stop_latched_after_resource_refusal() {
    for origin in [
        UnknownOrigin::InterruptFlag,
        UnknownOrigin::SolveDeadline,
        UnknownOrigin::MemoryBudget,
    ] {
        let exec = current_data();
        let w = variable(&exec, "w");
        exec.record_evaluation_stop(origin);
        assert!(exec
            .functional_array_snapshots_for_named_values(&[w])
            .is_err());
        assert!(exec
            .functional_array_snapshots_for_named_values(&[w])
            .is_err());
        assert_eq!(exec.evaluation_stop_origin(), Some(origin));
        assert!(exec.last_result.is_none());
    }
}
