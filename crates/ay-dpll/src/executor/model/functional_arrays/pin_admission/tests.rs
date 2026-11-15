// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private constructor-owner controls, never accepted model/proof fixtures.

use std::sync::atomic::AtomicBool;
use std::time::Duration;

use ay_core::resource::enter_check_stop;
use ay_core::time::Instant;
use ay_frontend::parse;

use super::super::MAX_FUNCTIONAL_WORK;
use super::*;

thread_local! {
    static REENTER_PAYMENT: std::cell::RefCell<Option<PinAdmission>> = const {
        std::cell::RefCell::new(None)
    };
}

#[test]
fn counted_term_adapter_debits_and_refuses_the_original_model_owner() {
    let (exec, model) = fixture();
    let used = counter(&model);
    let capture_before = used.load(Ordering::Acquire);
    let admission = PinAdmission::capture(&exec, &model).expect("original model owner");
    let before = used.load(Ordering::Acquire);
    assert_eq!(
        before, capture_before,
        "DATA metadata does not consume the specialized construction ledger"
    );
    TermConstructionAdmission::admit(&admission, 7, 32).expect("borrowed debit");
    admission.pay(13, 0).expect("same native ledger");
    assert_eq!(used.load(Ordering::Acquire), before + 20);
    TermConstructionAdmission::refuse(&admission, CountedAdmissionError::StorageExhausted);
    assert_eq!(admission.poll(), Err(UnknownOrigin::MemoryBudget));
    assert_eq!(used.load(Ordering::Acquire), work_counter::REFUSED);
    assert_eq!(
        TermConstructionAdmission::admit(&admission, 0, 0),
        Err(CountedAdmissionError::Memory),
    );
}

#[test]
fn callback_reentry_refuses_the_original_payment_without_a_mutable_borrow() {
    let (exec, model) = fixture();
    let armed = Arc::new(AtomicBool::new(false));
    let observe = Arc::clone(&armed);
    let scope = enter_check_stop(Arc::new(move || {
        observe.load(Ordering::Acquire)
            && REENTER_PAYMENT.with(|slot| {
                slot.borrow()
                    .as_ref()
                    .is_some_and(|admission| admission.pay(1, 0).is_err())
            })
    }));
    let admission = PinAdmission::capture(&exec, &model).expect("capture before callback arms");
    REENTER_PAYMENT.with(|slot| *slot.borrow_mut() = Some(admission));
    armed.store(true, Ordering::Release);
    let result =
        REENTER_PAYMENT.with(|slot| slot.borrow().as_ref().expect("original payment").pay(1, 0));
    armed.store(false, Ordering::Release);
    let admission = REENTER_PAYMENT
        .with(|slot| slot.borrow_mut().take())
        .expect("same owner");
    assert_eq!(result, Err(UnknownOrigin::IncompleteSolverLane));
    assert_eq!(admission.poll(), Err(UnknownOrigin::IncompleteSolverLane));
    assert_eq!(
        TermConstructionAdmission::admit(&admission, 0, 0),
        Err(CountedAdmissionError::Original(
            OriginalAdmissionError::Reentrant
        )),
    );
    assert_eq!(
        counter(&model).load(Ordering::Acquire),
        work_counter::REFUSED
    );
    drop(admission);
    drop(scope);
}

#[test]
fn terminal_callback_unwind_refuses_a_later_read_of_the_same_model() {
    let (exec, model) = fixture();
    let armed = Arc::new(AtomicBool::new(false));
    let observe = Arc::clone(&armed);
    let scope = enter_check_stop(Arc::new(move || {
        assert!(!observe.load(Ordering::Acquire), "terminal callback unwind");
        false
    }));
    let admission = PinAdmission::capture(&exec, &model).expect("original owner");
    armed.store(true, Ordering::Release);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        admission.finish(exec.ctx.terms.true_memory_bytes())
    }));
    armed.store(false, Ordering::Release);
    assert!(result.is_err());
    assert_eq!(
        counter(&model).load(Ordering::Acquire),
        work_counter::REFUSED
    );
    let read = exec.begin_external_evaluation_read();
    assert!(exec.evaluation_stop_origin().is_none(), "fresh read frame");
    assert!(PinAdmission::capture(&exec, &model).is_err());
    drop(read);
    drop(scope);
}

#[test]
fn accepting_callback_cannot_cross_the_original_live_deadline() {
    for finishing in [false, true] {
        let (exec, model) = fixture();
        let end = exec.solve_deadline.clone();
        let armed = Arc::new(AtomicBool::new(false));
        let observe = Arc::clone(&armed);
        let scope = enter_check_stop(Arc::new(move || {
            if observe.load(Ordering::Acquire) {
                end.set(Some(Instant::now()));
            }
            false
        }));
        let admission = PinAdmission::capture(&exec, &model).expect("original live owner");
        armed.store(true, Ordering::Release);
        let result = if finishing {
            admission.finish(exec.ctx.terms.true_memory_bytes())
        } else {
            admission.pay(1, 0)
        };
        assert_eq!(result, Err(UnknownOrigin::SolveDeadline));
        assert_eq!(
            counter(&model).load(Ordering::Acquire),
            work_counter::REFUSED
        );
        drop(scope);
    }
}

#[test]
fn callback_unwind_cannot_leave_a_model_eligible_for_payment_retry() {
    let (exec, model) = fixture();
    let armed = Arc::new(AtomicBool::new(false));
    let observe = Arc::clone(&armed);
    let scope = enter_check_stop(Arc::new(move || {
        assert!(!observe.load(Ordering::Acquire), "test callback unwind");
        false
    }));
    let admission = PinAdmission::capture(&exec, &model).expect("capture before callback arms");
    armed.store(true, Ordering::Release);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| admission.pay(1, 0)));
    armed.store(false, Ordering::Release);
    assert!(result.is_err());
    assert_eq!(
        admission.pay(0, 0),
        Err(UnknownOrigin::IncompleteSolverLane)
    );
    assert_eq!(
        counter(&model).load(Ordering::Acquire),
        work_counter::REFUSED
    );
    drop(admission);
    drop(scope);
}

fn fixture() -> (Executor, Model) {
    let mut exec = Executor::new();
    exec.execute_all(
        &parse(
            "(declare-const a (Array (_ BitVec 64) (_ BitVec 8)))
         (assert (= a ((as const (Array (_ BitVec 64) (_ BitVec 8))) (_ bv7 8))))",
        )
        .expect("bounded original source"),
    )
    .expect("elaborate, not solve");
    let mut model = Model::empty();
    exec.install_functional_array_candidate(&mut model);
    assert!(
        model.functional_arrays.is_some(),
        "real complete data producer"
    );
    assert!(exec.last_result.is_none(), "fixture does not publish SAT");
    (exec, model)
}

fn counter(model: &Model) -> Arc<AtomicUsize> {
    Arc::clone(
        &model
            .functional_arrays
            .as_ref()
            .expect("original data")
            .work_used,
    )
}

#[test]
fn two_adapters_and_model_clone_share_the_original_cumulative_counter() {
    let (exec, model) = fixture();
    let used = counter(&model);
    let capture_before = used.load(Ordering::Acquire);
    let cloned = model.clone();
    let mut first = PinAdmission::capture(&exec, &model).expect("same original owner");
    let mut second = PinAdmission::capture(&exec, &cloned).expect("clone carries original owner");
    assert!(Arc::ptr_eq(&first.used, &second.used));
    let before = used.load(Ordering::Acquire);
    assert_eq!(
        before, capture_before,
        "source validation does not debit either adapter's FP/construction ledger"
    );
    first.pay(7, 0).expect("first debit");
    second.pay(13, 0).expect("second debit");
    assert_eq!(used.load(Ordering::Acquire), before + 20);
    first
        .finish(exec.ctx.terms.true_memory_bytes())
        .expect("first cleanup");
    second
        .finish(exec.ctx.terms.true_memory_bytes())
        .expect("second cleanup");
    assert_eq!(
        used.load(Ordering::Acquire),
        before + 20,
        "cleanup refunds no work"
    );
}

#[test]
fn exact_limit_zero_poll_succeeds_but_excess_refuses_all_followup_work() {
    let (exec, model) = fixture();
    let used = counter(&model);
    let mut admission =
        PinAdmission::capture(&exec, &model).expect("paid original source validation");
    assert!(used.load(Ordering::Acquire) < MAX_FUNCTIONAL_WORK - 5);
    used.store(MAX_FUNCTIONAL_WORK - 5, Ordering::Release);
    assert_eq!(admission.pay(5, 0), Ok(()));
    assert_eq!(admission.pay(0, 0), Ok(()));
    assert_eq!(used.load(Ordering::Acquire), MAX_FUNCTIONAL_WORK);
    assert_eq!(
        admission.pay(1, 0),
        Err(UnknownOrigin::DeterministicResourceBudget)
    );
    assert_eq!(
        admission.pay(0, 0),
        Err(UnknownOrigin::DeterministicResourceBudget)
    );
    assert_eq!(used.load(Ordering::Acquire), work_counter::REFUSED);
}

#[test]
fn typed_constructor_refusal_latches_the_model_without_an_invented_work_debit() {
    let (exec, model) = fixture();
    let used = counter(&model);
    let admission = PinAdmission::capture(&exec, &model).expect("original model");
    assert_eq!(
        admission.refuse_resource(),
        UnknownOrigin::DeterministicResourceBudget
    );
    assert_eq!(used.load(Ordering::Acquire), work_counter::REFUSED);
    assert_eq!(
        admission.poll(),
        Err(UnknownOrigin::DeterministicResourceBudget)
    );
    drop(admission);
    // A distinct native stop frame must NOT replenish the original model.
    let read = exec.begin_external_evaluation_read();
    assert!(exec.evaluation_stop_origin().is_none());
    assert!(matches!(
        PinAdmission::capture(&exec, &model),
        Err(UnknownOrigin::DeterministicResourceBudget)
    ));
    drop(read);
}

#[test]
fn a_distinct_read_frame_cannot_finish_after_another_frame_refuses_the_same_model() {
    let (exec, model) = fixture();
    let first = PinAdmission::capture(&exec, &model).expect("original model frame");
    let read = exec.begin_external_evaluation_read();
    let later = PinAdmission::capture(&exec, &model).expect("distinct healthy read frame");
    assert!(!first.attempt.is_same_attempt(&later.attempt));
    assert!(Arc::ptr_eq(&first.used, &later.used));
    assert_eq!(
        first.refuse_resource(),
        UnknownOrigin::DeterministicResourceBudget
    );
    assert!(
        exec.evaluation_stop_origin().is_none(),
        "old-frame stop is not this frame's origin"
    );
    assert_eq!(
        later.finish(exec.ctx.terms.true_memory_bytes()),
        Err(UnknownOrigin::DeterministicResourceBudget)
    );
    drop(first);
    drop(read);
}

#[test]
fn a_distinct_read_frame_zero_poll_observes_terminal_model_storage() {
    let (exec, model) = fixture();
    let first = PinAdmission::capture(&exec, &model).expect("original model frame");
    let read = exec.begin_external_evaluation_read();
    let later = PinAdmission::capture(&exec, &model).expect("distinct healthy frame");
    first.refuse_resource();
    assert_eq!(
        later.poll(),
        Err(UnknownOrigin::DeterministicResourceBudget)
    );
    drop(later);
    drop(first);
    drop(read);
}

#[test]
fn original_raw_interrupt_is_precise_and_reset_cannot_revive_construction() {
    let (mut exec, model) = fixture();
    let interrupt = Arc::new(AtomicBool::new(false));
    exec.set_interrupt(Arc::clone(&interrupt));
    let mut admission = PinAdmission::capture(&exec, &model).expect("original cancel carrier");
    interrupt.store(true, Ordering::Release);
    assert_eq!(admission.pay(1, 0), Err(UnknownOrigin::InterruptFlag));
    interrupt.store(false, Ordering::Release);
    assert_eq!(admission.pay(0, 0), Err(UnknownOrigin::InterruptFlag));
    assert_eq!(admission.refuse_resource(), UnknownOrigin::InterruptFlag);
    assert_eq!(
        counter(&model).load(Ordering::Acquire),
        work_counter::REFUSED
    );
}

#[test]
fn original_live_deadline_refusal_stays_precise_after_control_restoration() {
    let (mut exec, model) = fixture();
    let mut admission = PinAdmission::capture(&exec, &model).expect("live original end");
    exec.set_deadline(Some(Instant::now()));
    assert_eq!(admission.pay(0, 0), Err(UnknownOrigin::SolveDeadline));
    assert_eq!(
        TermConstructionAdmission::admit(&admission, 0, 0),
        Err(CountedAdmissionError::Original(
            OriginalAdmissionError::Query(QueryError::Interrupted(StopReason::Deadline),)
        )),
    );
    exec.set_deadline(None);
    assert_eq!(admission.pay(0, 0), Err(UnknownOrigin::SolveDeadline));
    assert_eq!(admission.refuse_resource(), UnknownOrigin::SolveDeadline);
}

#[test]
fn captured_original_end_cannot_be_extended_or_removed_before_its_first_poll() {
    for restore in [None, Some(Instant::now() + Duration::from_secs(60))] {
        let (mut exec, model) = fixture();
        let end = Instant::now() + Duration::from_secs(1);
        exec.set_deadline(Some(end));
        let mut admission = PinAdmission::capture(&exec, &model).expect("original end not expired");
        exec.set_deadline(restore);
        std::thread::sleep(end.saturating_duration_since(Instant::now()));
        assert_eq!(admission.pay(0, 0), Err(UnknownOrigin::SolveDeadline));
        assert_eq!(admission.refuse_resource(), UnknownOrigin::SolveDeadline);
        assert_eq!(
            counter(&model).load(Ordering::Acquire),
            work_counter::REFUSED
        );
    }
}

#[test]
fn aggregate_original_arena_limit_refuses_one_byte_over_without_refund() {
    let (mut exec, model) = fixture();
    let source = exec.ctx.terms.true_memory_bytes();
    let retained = model
        .construction_owner
        .as_ref()
        .unwrap()
        .retained_metadata_bytes_for_test();
    assert!(retained > 0);
    // The retained admission now owns a real Arc arena in addition to payload.
    let arena_owner = std::mem::size_of::<crate::executor::model::EvaluationArena>()
        + 2 * std::mem::size_of::<usize>();
    exec.set_term_memory_limit(Some(source + retained + arena_owner + 31));
    let mut admission = PinAdmission::capture(&exec, &model).expect("source fits original arena");
    assert_eq!(admission.pay(0, 16), Ok(()));
    assert_eq!(admission.pay(0, 16), Err(UnknownOrigin::MemoryBudget));
    assert_eq!(admission.pay(0, 0), Err(UnknownOrigin::MemoryBudget));
    assert_eq!(
        counter(&model).load(Ordering::Acquire),
        work_counter::REFUSED
    );
}

#[test]
fn final_post_arena_cleanup_poll_revokes_a_previously_healthy_result() {
    let (mut exec, model) = fixture();
    let interrupt = Arc::new(AtomicBool::new(false));
    exec.set_interrupt(Arc::clone(&interrupt));
    let mut admission = PinAdmission::capture(&exec, &model).expect("original admission");
    admission.pay(1, 128).expect("prepaid scratch");
    interrupt.store(true, Ordering::Release);
    assert_eq!(
        admission.finish(exec.ctx.terms.true_memory_bytes()),
        Err(UnknownOrigin::InterruptFlag)
    );
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(UnknownOrigin::InterruptFlag)
    );
    assert_eq!(
        counter(&model).load(Ordering::Acquire),
        work_counter::REFUSED
    );
}

#[test]
fn final_live_producer_memory_check_cannot_be_bypassed_by_scratch_cleanup() {
    let (mut exec, model) = fixture();
    let source = exec.ctx.terms.true_memory_bytes();
    let retained = model
        .construction_owner
        .as_ref()
        .unwrap()
        .retained_metadata_bytes_for_test();
    exec.set_term_memory_limit(Some(source + retained + 128));
    let admission = PinAdmission::capture(&exec, &model).expect("source originally fits");
    assert_eq!(
        admission.finish(source + 129),
        Err(UnknownOrigin::MemoryBudget)
    );
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(UnknownOrigin::MemoryBudget)
    );
    assert_eq!(
        counter(&model).load(Ordering::Acquire),
        work_counter::REFUSED
    );
}

fn original_callback(flag: &Arc<AtomicBool>) -> ay_core::resource::CheckStop {
    let flag = Arc::clone(flag);
    Arc::new(move || flag.load(Ordering::Acquire))
}

#[test]
fn original_callback_only_stop_refuses_capture_without_a_fabricated_precise_cause() {
    let (exec, model) = fixture();
    let flag = Arc::new(AtomicBool::new(true));
    let scope = enter_check_stop(original_callback(&flag));
    assert!(matches!(
        PinAdmission::capture(&exec, &model),
        Err(UnknownOrigin::IncompleteSolverLane)
    ));
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(UnknownOrigin::IncompleteSolverLane)
    );
    assert_eq!(
        counter(&model).load(Ordering::Acquire),
        work_counter::REFUSED
    );
    flag.store(false, Ordering::Release);
    drop(scope);
    assert!(matches!(
        PinAdmission::capture(&exec, &model),
        Err(UnknownOrigin::IncompleteSolverLane)
    ));
}

#[test]
fn original_callback_reset_cannot_revive_a_refused_construction() {
    let (exec, model) = fixture();
    let flag = Arc::new(AtomicBool::new(false));
    let scope = enter_check_stop(original_callback(&flag));
    let mut admission = PinAdmission::capture(&exec, &model).expect("original callback");
    admission
        .pay(7, 16)
        .expect("healthy debit under original callback");
    flag.store(true, Ordering::Release);
    assert_eq!(
        admission.pay(1, 0),
        Err(UnknownOrigin::IncompleteSolverLane)
    );
    flag.store(false, Ordering::Release);
    drop(scope);
    assert_eq!(
        admission.pay(0, 0),
        Err(UnknownOrigin::IncompleteSolverLane)
    );
    assert_eq!(
        admission.refuse_resource(),
        UnknownOrigin::IncompleteSolverLane
    );
    assert_eq!(
        admission.finish(exec.ctx.terms.true_memory_bytes()),
        Err(UnknownOrigin::IncompleteSolverLane)
    );
    assert_eq!(
        counter(&model).load(Ordering::Acquire),
        work_counter::REFUSED
    );
}

#[test]
fn original_callback_survives_scope_restoration_and_a_healthy_replacement() {
    let (exec, model) = fixture();
    let flag = Arc::new(AtomicBool::new(false));
    let scope = enter_check_stop(original_callback(&flag));
    let mut admission = PinAdmission::capture(&exec, &model).expect("original callback captured");
    drop(scope);
    let replacement = enter_check_stop(Arc::new(|| false));
    flag.store(true, Ordering::Release);
    assert_eq!(
        admission.pay(0, 0),
        Err(UnknownOrigin::IncompleteSolverLane)
    );
    flag.store(false, Ordering::Release);
    drop(replacement);
    assert_eq!(admission.poll(), Err(UnknownOrigin::IncompleteSolverLane));
    assert_eq!(
        counter(&model).load(Ordering::Acquire),
        work_counter::REFUSED
    );
}

#[test]
fn original_callback_final_fence_refuses_after_arena_cleanup_and_scope_drop() {
    let (exec, model) = fixture();
    let flag = Arc::new(AtomicBool::new(false));
    let scope = enter_check_stop(original_callback(&flag));
    let mut admission = PinAdmission::capture(&exec, &model).expect("original callback");
    admission
        .pay(5, 128)
        .expect("scratch prepaid under original callback");
    drop(scope);
    flag.store(true, Ordering::Release);
    assert_eq!(
        admission.finish(exec.ctx.terms.true_memory_bytes()),
        Err(UnknownOrigin::IncompleteSolverLane)
    );
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(UnknownOrigin::IncompleteSolverLane)
    );
    assert_eq!(
        counter(&model).load(Ordering::Acquire),
        work_counter::REFUSED
    );
}

#[test]
fn precise_original_raw_interrupt_precedes_an_opaque_callback_stop() {
    let (mut exec, model) = fixture();
    let raw = Arc::new(AtomicBool::new(false));
    exec.set_interrupt(Arc::clone(&raw));
    let flag = Arc::new(AtomicBool::new(false));
    let scope = enter_check_stop(original_callback(&flag));
    let mut admission = PinAdmission::capture(&exec, &model).expect("both original sources");
    raw.store(true, Ordering::Release);
    flag.store(true, Ordering::Release);
    assert_eq!(admission.pay(0, 0), Err(UnknownOrigin::InterruptFlag));
    raw.store(false, Ordering::Release);
    flag.store(false, Ordering::Release);
    drop(scope);
    assert_eq!(
        admission.finish(exec.ctx.terms.true_memory_bytes()),
        Err(UnknownOrigin::InterruptFlag)
    );
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(UnknownOrigin::InterruptFlag)
    );
}

#[test]
fn native_stop_before_capture_preserves_precise_origin_and_terminal_model() {
    for deadline in [false, true] {
        let (mut exec, model) = fixture();
        let interrupt = Arc::new(AtomicBool::new(false));
        exec.set_interrupt(Arc::clone(&interrupt));
        let expected = if deadline {
            exec.set_deadline(Some(Instant::now()));
            UnknownOrigin::SolveDeadline
        } else {
            interrupt.store(true, Ordering::Release);
            UnknownOrigin::InterruptFlag
        };
        assert!(matches!(PinAdmission::capture(&exec, &model), Err(origin) if origin == expected));
        assert_eq!(
            counter(&model).load(Ordering::Acquire),
            work_counter::REFUSED
        );
        interrupt.store(false, Ordering::Release);
        exec.set_deadline(None);
        assert!(matches!(PinAdmission::capture(&exec, &model), Err(origin) if origin == expected));
        let read = exec.begin_external_evaluation_read();
        assert!(
            PinAdmission::capture(&exec, &model).is_err(),
            "new read cannot renew original counter"
        );
        drop(read);
    }
}
