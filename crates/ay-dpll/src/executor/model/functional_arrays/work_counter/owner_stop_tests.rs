// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Observed-stop storage controls, not full extraction or native SAT authority.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

use ay_core::resource::{enter_check_stop, CheckStopScope};
use ay_core::time::Instant;
use ay_core::TermId;
use ay_frontend::parse;
use ay_model_check::ModelView;

use crate::executor::model::independent_gate::IndependentModelView;
use crate::executor::model::Model;
use crate::executor::Executor;
use crate::executor_types::UnknownOrigin;

use super::super::super::EvalValue;
use super::{MAX_FUNCTIONAL_WORK, REFUSED};

const SOURCE: &str = "(declare-const a (Array (_ BitVec 64) (_ BitVec 128)))
    (assert (= a ((as const (Array (_ BitVec 64) (_ BitVec 128))) (_ bv7 128))))";

fn fixture(end: Instant) -> (Executor, Model, TermId, Arc<AtomicBool>, CheckStopScope) {
    let scope = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let mut exec = Executor::new();
    exec.set_term_memory_limit(Some(128 * 1024 * 1024));
    assert_eq!(
        exec.execute_all(&parse(SOURCE).expect("bounded source"))
            .expect("elaboration only"),
        [] as [String; 0]
    );
    let raw = Arc::new(AtomicBool::new(false));
    exec.set_interrupt(Arc::clone(&raw));
    exec.begin_external_decision_query(false);
    exec.set_deadline(Some(end));
    let mut model = Model::empty();
    exec.install_functional_array_candidate(&mut model);
    assert!(
        model.functional_arrays.is_some(),
        "actual original producer"
    );
    let leaf = exec
        .ctx
        .symbol_info("a")
        .and_then(|info| info.term)
        .expect("original leaf");
    exec.last_model = Some(model.clone());
    assert!(exec.last_result.is_none(), "no solve or publication");
    (exec, model, leaf, raw, scope)
}

fn storage(model: &Model) -> usize {
    model
        .functional_arrays
        .as_ref()
        .expect("same functional MODEL")
        .work_used
        .load(Ordering::Acquire)
}

fn reset_read_refuses(exec: &mut Executor, model: &Model, raw: &AtomicBool, end: Instant) {
    raw.store(false, Ordering::Release);
    exec.set_deadline(Some(end));
    let read = exec.begin_external_evaluation_read();
    assert!(
        exec.evaluation_stop_origin().is_none(),
        "distinct frame, not a grant"
    );
    assert_eq!(
        model.charge_functional_array_work(exec, 0),
        Err("functional array original cumulative work exhausted".to_owned())
    );
    assert_eq!(storage(model), REFUSED);
    drop(read);
}

#[test]
fn early_original_raw_poll_marks_model_terminal_without_admitting_work() {
    let end = Instant::now() + Duration::from_secs(20);
    let (mut exec, model, _, raw, scope) = fixture(end);
    let copied = model.clone();
    let before = storage(&model);
    assert!(before < MAX_FUNCTIONAL_WORK);
    assert!(Arc::ptr_eq(
        &model.functional_arrays.as_ref().expect("model").work_used,
        &copied.functional_arrays.as_ref().expect("clone").work_used
    ));
    raw.store(true, Ordering::Release);
    assert_eq!(
        model.charge_functional_array_work(&exec, 0),
        Err("functional array owner interrupted".to_owned())
    );
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(UnknownOrigin::InterruptFlag)
    );
    assert_eq!(
        storage(&model),
        REFUSED,
        "terminal storage, not an admitted unit"
    );
    reset_read_refuses(&mut exec, &copied, &raw, end);
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(UnknownOrigin::InterruptFlag)
    );
    drop(copied);
    drop(model);
    drop(exec);
    drop(scope);
    assert!(Instant::now() < end);
}

#[test]
fn original_deadline_poll_keeps_precise_cause_and_same_model_refusal() {
    let end = Instant::now() + Duration::from_secs(20);
    let (mut exec, model, _, raw, scope) = fixture(end);
    exec.set_deadline(Some(Instant::now()));
    assert_eq!(
        model.validate_functional_array_source(&exec),
        Err("functional array owner interrupted".to_owned())
    );
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(UnknownOrigin::SolveDeadline)
    );
    assert_eq!(storage(&model), REFUSED);
    reset_read_refuses(&mut exec, &model, &raw, end);
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(UnknownOrigin::SolveDeadline)
    );
    drop(model);
    drop(exec);
    drop(scope);
    assert!(Instant::now() < end);
}

#[test]
fn late_zero_fence_after_complete_lookup_survives_unpublished_snapshot_cleanup() {
    let end = Instant::now() + Duration::from_secs(20);
    let (mut exec, model, leaf, raw, scope) = fixture(end);
    let selected = model
        .functional_array_value(&exec, leaf)
        .expect("healthy complete source lookup")
        .expect("whole snapshot");
    assert!(storage(&model) < MAX_FUNCTIONAL_WORK);
    raw.store(true, Ordering::Release);
    // Directly exercise the SAME zero-debit fence used after source/read/render
    // work. This is not a synthetic claim of interruption inside that work.
    assert_eq!(
        model.charge_functional_array_work(&exec, 0),
        Err("functional array owner interrupted".to_owned())
    );
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(UnknownOrigin::InterruptFlag)
    );
    drop(selected);
    reset_read_refuses(&mut exec, &model, &raw, end);
    assert!(model.functional_array_value(&exec, leaf).is_err());
    assert_eq!(storage(&model), REFUSED);
    drop(model);
    drop(exec);
    drop(scope);
    assert!(Instant::now() < end);
}

#[test]
fn direct_model_view_interruption_latches_before_evaluator_charge_hook() {
    let end = Instant::now() + Duration::from_secs(20);
    let (exec, model, _, raw, scope) = fixture(end);
    let view = IndependentModelView::new(&exec, &model);
    assert!(!view.functional_array_interrupted()); // real source inspection first
    let before = storage(&model);
    assert!(!view.functional_array_interrupted());
    assert_eq!(
        storage(&model),
        before,
        "healthy zero does not consume a unit"
    );
    raw.store(true, Ordering::Release);
    assert!(IndependentModelView::new(&exec, &model).functional_array_interrupted());
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(UnknownOrigin::InterruptFlag)
    );
    assert_eq!(storage(&model), REFUSED);
    raw.store(false, Ordering::Release);
    let read = exec.begin_external_evaluation_read();
    assert!(exec.evaluation_stop_origin().is_none());
    assert!(IndependentModelView::new(&exec, &model).functional_array_interrupted());
    assert_eq!(storage(&model), REFUSED);
    drop(read);
    drop(model);
    drop(exec);
    drop(scope);
    assert!(Instant::now() < end);
}

#[test]
fn native_read_and_render_refusals_survive_the_new_read_frame() {
    let end = Instant::now() + Duration::from_secs(20);
    let (exec, model, leaf, raw, scope) = fixture(end);
    let index = EvalValue::BitVec {
        value: 0u8.into(),
        width: 64,
    };
    assert!(matches!(exec.functional_array_read(&model, leaf, &index),
        Some(EvalValue::BitVec { value, width: 128 }) if value == 7u8.into()));
    raw.store(true, Ordering::Release);
    assert!(matches!(
        exec.functional_array_read(&model, leaf, &index),
        Some(EvalValue::Unknown)
    ));
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(UnknownOrigin::InterruptFlag)
    );
    assert_eq!(storage(&model), REFUSED);
    raw.store(false, Ordering::Release);
    let read = exec.begin_external_evaluation_read();
    assert!(exec.evaluation_stop_origin().is_none());
    assert!(matches!(
        exec.functional_array_read(&model, leaf, &index),
        Some(EvalValue::Unknown)
    ));
    assert_eq!(
        exec.functional_array_render(&model, leaf),
        Err("functional array original cumulative work exhausted".to_owned())
    );
    assert_eq!(storage(&model), REFUSED);
    drop(read);
    drop(model);
    drop(exec);
    drop(scope);
    assert!(Instant::now() < end);
}

#[test]
fn exact_limit_zero_hook_is_healthy_until_an_actual_refusal() {
    let end = Instant::now() + Duration::from_secs(20);
    let (exec, model, _, _, scope) = fixture(end);
    let view = IndependentModelView::new(&exec, &model);
    assert!(!view.functional_array_interrupted()); // validation itself is real work
    let left = model.functional_work_left();
    model
        .charge_functional_array_work(&exec, left)
        .expect("exact original remainder");
    assert_eq!(storage(&model), MAX_FUNCTIONAL_WORK);
    assert!(!view.functional_array_interrupted());
    assert_eq!(storage(&model), MAX_FUNCTIONAL_WORK);
    assert_eq!(
        model.charge_functional_array_work(&exec, 1),
        Err("functional array original cumulative work exhausted".to_owned())
    );
    assert!(view.functional_array_interrupted());
    assert_eq!(storage(&model), REFUSED);
    drop(view);
    drop(model);
    drop(exec);
    drop(scope);
    assert!(Instant::now() < end);
}

#[test]
fn repeated_source_validation_charges_the_stamp_walk_only_per_arena_change() {
    // Regression: every array read re-walked and re-charged all entry stamps,
    // so read traffic during ordinary model validation exhausted the
    // cumulative owner on multi-record quantified problems and degraded a
    // valid SAT to `resourceout`. While the validated snapshot remains an
    // append-only prefix of the store, the walk runs (and is charged) once;
    // the per-read source/roots checks and owner fence are unchanged.
    let end = Instant::now() + Duration::from_secs(20);
    let (mut exec, model, _, _, scope) = fixture(end);
    let data = model.functional_arrays.as_ref().expect("functional MODEL");
    let (roots, stamps) = (data.roots.len(), data.stamps.len());
    assert!(stamps > 0, "fixture must carry entry stamps");
    let before = storage(&model);
    model
        .validate_functional_array_source(&exec)
        .expect("first validation walks the stamps");
    let after_first = storage(&model);
    assert_eq!(after_first - before, roots + stamps + 1);
    model
        .validate_functional_array_source(&exec)
        .expect("second validation reuses the walk verdict");
    assert_eq!(storage(&model) - after_first, roots + 1);
    // Appending a fresh term keeps the validated snapshot an append-only
    // prefix, so the walk is still not re-charged.
    let _ = exec
        .ctx
        .terms
        .mk_var("appended_after_validation", ay_core::Sort::Bool);
    model
        .validate_functional_array_source(&exec)
        .expect("append-only growth keeps the walk verdict");
    assert_eq!(storage(&model) - after_first, 2 * (roots + 1));
    drop(model);
    drop(exec);
    drop(scope);
    assert!(Instant::now() < end);
}
