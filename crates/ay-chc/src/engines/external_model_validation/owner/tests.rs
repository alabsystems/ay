// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{ChcParser, InvariantModel, PdrConfig};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;

fn configured() -> PdrConfig {
    let mut config = PdrConfig::production(false).with_memory_budget(Some(64 * 1024 * 1024));
    config.solve_timeout = Some(Duration::from_secs(20));
    config
}

fn guard() -> ResourceGuard {
    let mut original = ResourceGuard::new();
    original.set_deadline(Some(Instant::now() + Duration::from_secs(20)));
    original
}

#[test]
fn captured_guard_tree_ancestor_deadline_is_the_immutable_worker_wall() {
    use ay_core::resource::{ChildSpec, DeadlineSource, NodeLabel};
    let wall = Instant::now() + Duration::from_secs(3);
    let parent = ResourceGuard::root_child(
        ChildSpec::new(NodeLabel::Check).with_deadline(DeadlineSource::Fixed(wall)),
    );
    let child = parent.child(ChildSpec::new(NodeLabel::Search));
    assert_eq!(child.deadline(), None);
    let owner = ExternalInvariantValidationOwner::capture(&child, &configured());
    assert_eq!(owner.deadline(), wall);
    assert_eq!(owner.check(), None);
    assert_eq!(
        std::thread::spawn(move || owner.deadline()).join().unwrap(),
        wall
    );
}

#[test]
fn captured_certify_owner_respects_cancel_only_deadline_boundary() {
    use ay_core::resource::{ChildSpec, DeadlineSource, NodeLabel};
    let parent = ResourceGuard::root_child(
        ChildSpec::new(NodeLabel::Check).with_deadline(DeadlineSource::Fixed(Instant::now())),
    );
    let wall = Instant::now() + Duration::from_secs(10);
    let certify = parent.child(
        ChildSpec::new(NodeLabel::Certify)
            .cancel_only()
            .with_deadline(DeadlineSource::Fixed(wall)),
    );
    let child = certify.child(ChildSpec::new(NodeLabel::Check));
    let owner = ExternalInvariantValidationOwner::capture(&child, &configured());
    assert_eq!(owner.deadline(), wall);
    assert_eq!(owner.check(), None);
    parent.cancel();
    assert_eq!(owner.check(), Some(Kind::Cancelled));
}

#[test]
fn cpu_exhaustion_is_a_timeout_not_an_evidence_verdict() {
    assert_eq!(from_guard(Exhausted::Cpu), Kind::Timeout);
}

fn fixture() -> (ChcProblem, InvariantModel) {
    let problem = ChcParser::parse(
        "(set-logic HORN)
         (declare-fun Inv (Int) Bool)
         (assert (forall ((x Int)) (=> (= x 0) (Inv x))))
         (assert (forall ((x Int) (y Int))
             (=> (and (Inv x) (= y (+ x 1))) (Inv y))))
         (assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
         (check-sat)",
    )
    .unwrap();
    let model =
        InvariantModel::parse_smtlib("(define-fun Inv ((x Int)) Bool (>= x 0))", &problem).unwrap();
    (problem, model)
}

#[test]
fn worker_capture_is_send_sync_and_preserves_absolute_wall_and_shared_ticks() {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<ExternalInvariantValidationOwner>();
    let original = guard();
    let config = configured();
    let owner = ExternalInvariantValidationOwner::capture(&original, &config);
    let wall = owner.deadline();
    let before = original.ticks();
    let worker_owner = owner.clone();
    let (problem, model) = fixture();
    let result = std::thread::spawn(move || {
        assert_eq!(worker_owner.deadline(), wall);
        validate_external_invariant_model_with_owner(&problem, &model, &config, &worker_owner)
    })
    .join()
    .unwrap()
    .unwrap();
    assert_eq!(result, Kind::Valid);
    assert!(original.ticks() > before);
    assert!(Arc::ptr_eq(&owner.inner, &owner.clone().inner));
    assert_eq!(owner.check(), None);
}

#[test]
fn expired_original_owner_skips_lowering_cache_and_validation_without_new_clock() {
    let mut original = guard();
    original.set_deadline(Some(Instant::now() - Duration::from_secs(1)));
    let owner = ExternalInvariantValidationOwner::capture(&original, &configured());
    let calls = AtomicUsize::new(0);
    assert_eq!(
        owner
            .with_resources(|| {
                calls.fetch_add(1, Ordering::Relaxed);
                Ok(true)
            })
            .unwrap(),
        Err(Kind::Timeout)
    );
    let (problem, model) = fixture();
    let result =
        validate_external_invariant_model_with_owner(&problem, &model, &configured(), &owner)
            .unwrap();
    assert_eq!(result, Kind::Timeout);
    assert_eq!(calls.load(Ordering::Relaxed), 0);
}

#[test]
fn descendant_observed_original_token_cannot_resume_after_caller_reset() {
    let caller = CancellationToken::new();
    let original = guard();
    let owner = ExternalInvariantValidationOwner::capture(
        &original,
        &configured().with_cancellation_token(Some(caller.clone())),
    );
    let descendant = owner.inner.cancellation.as_ref().unwrap().child();
    caller.cancel();
    assert!(std::thread::spawn(move || descendant.is_cancelled())
        .join()
        .unwrap());
    caller.reset();
    assert!(!caller.is_cancelled());
    assert_eq!(owner.check(), Some(Kind::Cancelled));
    assert_eq!(owner.clone().check(), Some(Kind::Cancelled));
}

#[test]
fn raw_guard_and_ambient_interrupts_keep_original_identity_and_sticky_reset() {
    for ambient in [false, true] {
        let flag = Arc::new(AtomicBool::new(false));
        let token = CancellationToken::new();
        let lane = ambient.then(|| {
            crate::smt::deadline::ScopedLaneCancellation::install(
                token.clone(),
                Some(Arc::clone(&flag)),
            )
        });
        let mut original = guard();
        if !ambient {
            original.set_cancel(Some(Arc::clone(&flag)));
            assert!(Arc::ptr_eq(original.cancel_flag().unwrap(), &flag));
        }
        let owner = ExternalInvariantValidationOwner::capture(&original, &configured());
        drop(lane);
        let descendant = owner.inner.cancellation.as_ref().unwrap().child();
        flag.store(true, Ordering::Relaxed);
        assert!(std::thread::spawn(move || descendant.is_cancelled())
            .join()
            .unwrap());
        flag.store(false, Ordering::Relaxed);
        assert_eq!(owner.check(), Some(Kind::Cancelled));
        assert!(!token.is_cancelled());
        assert!(!flag.load(Ordering::Relaxed));
    }
}

#[test]
fn captured_callback_survives_drop_replacement_without_inventing_a_typed_cause() {
    let stopped = Arc::new(AtomicBool::new(false));
    let observer = Arc::clone(&stopped);
    let caller_scope =
        ay_core::resource::enter_check_stop(Arc::new(move || observer.load(Ordering::Relaxed)));
    let original = guard();
    let owner = ExternalInvariantValidationOwner::capture(&original, &configured());
    drop(caller_scope);
    stopped.store(true, Ordering::Relaxed);
    let worker = owner.clone();
    assert_eq!(
        std::thread::spawn(move || {
            let _replacement = ay_core::resource::enter_check_stop(Arc::new(|| false));
            worker.with_resources(|| Ok(17))
        })
        .join()
        .unwrap()
        .unwrap(),
        Err(Kind::Inconclusive)
    );
    stopped.store(false, Ordering::Relaxed);
    assert_eq!(owner.check(), Some(Kind::Inconclusive));
}

#[test]
fn last_fence_observes_restored_term_scope_before_returning_checked_phase_data() {
    assert_eq!(
        crate::smt::SmtContext::current_thread_term_memory_budget(),
        None
    );
    let enabled = Arc::new(AtomicBool::new(false));
    let observer = Arc::clone(&enabled);
    let _scope = ay_core::resource::enter_check_stop(Arc::new(move || {
        observer.load(Ordering::Relaxed)
            && crate::smt::SmtContext::current_thread_term_memory_budget().is_none()
    }));
    let original = guard();
    let owner = ExternalInvariantValidationOwner::capture(&original, &configured());
    let result = owner
        .with_resources(|| {
            assert_eq!(
                crate::smt::SmtContext::current_thread_term_memory_budget(),
                owner.memory_budget()
            );
            enabled.store(true, Ordering::Relaxed);
            Ok(17)
        })
        .unwrap();
    assert_eq!(
        crate::smt::SmtContext::current_thread_term_memory_budget(),
        None
    );
    assert_eq!(result, Err(Kind::Inconclusive));
}

#[test]
fn reentry_and_reused_rlimit_never_create_independent_phase_allowances() {
    let original = guard();
    let owner = ExternalInvariantValidationOwner::capture(&original, &configured());
    let nested = owner.clone();
    let result = owner
        .with_resources(|| {
            assert_eq!(
                nested.with_resources(|| Ok(17)).unwrap(),
                Err(Kind::Inconclusive)
            );
            Ok(23)
        })
        .unwrap();
    assert_eq!(result, Err(Kind::Inconclusive));
    let mut limited = guard();
    limited.set_rlimit(Some(3));
    let bounded = ExternalInvariantValidationOwner::capture(&limited, &configured());
    let peer = bounded.clone();
    assert_eq!(peer.check(), None);
    assert_eq!(bounded.check(), Some(Kind::WorkLimit));
    assert_eq!(limited.ticks(), 3);
}

#[test]
fn candidate_refutation_is_not_unsafe_or_a_reset_of_the_original_owner() {
    let original = guard();
    let config = configured();
    let owner = ExternalInvariantValidationOwner::capture(&original, &config);
    let (problem, model) = fixture();
    let bad =
        InvariantModel::parse_smtlib("(define-fun Inv ((x Int)) Bool (= x 0))", &problem).unwrap();
    assert_eq!(
        validate_external_invariant_model_with_owner(&problem, &bad, &config, &owner,).unwrap(),
        Kind::Refuted
    );
    assert_eq!(owner.check(), None);
    assert_eq!(
        validate_external_invariant_model_with_owner(&problem, &model, &config, &owner,).unwrap(),
        Kind::Valid
    );
}

#[test]
fn no_raw_or_token_cancellation_stays_absent_and_none_does_not_invent_a_cap() {
    let original = guard();
    let owner = ExternalInvariantValidationOwner::capture(
        &original,
        &configured().with_memory_budget(None),
    );
    assert!(owner.inner.cancellation.is_none());
    assert_eq!(owner.memory_budget(), None);
    assert_eq!(owner.with_resources(|| Ok(17)).unwrap(), Ok(17));
}

#[test]
fn callback_panic_is_inconclusive_and_phase_panic_cannot_revive_the_owner() {
    let _scope = ay_core::resource::enter_check_stop(Arc::new(|| panic!("exact callback panic")));
    let original = guard();
    let owner = ExternalInvariantValidationOwner::capture(&original, &configured());
    assert_eq!(owner.check(), Some(Kind::Inconclusive));
    drop(_scope);
    let fresh = ExternalInvariantValidationOwner::capture(&original, &configured());
    let result = std::panic::catch_unwind(AssertUnwindSafe(|| {
        fresh.with_resources(|| -> ChcResult<()> { panic!("non-AY phase panic") })
    }));
    assert!(result.is_err());
    assert_eq!(fresh.check(), Some(Kind::Inconclusive));
}

#[test]
fn serial_phase_fence_remains_held_during_last_restored_scope_callback() {
    let enabled = Arc::new(AtomicBool::new(false));
    let saw_active = Arc::new(AtomicBool::new(false));
    let calls = Arc::new(AtomicUsize::new(0));
    let slot = Arc::new(std::sync::Mutex::new(
        None::<ExternalInvariantValidationOwner>,
    ));
    let (on, seen, count, peer) = (
        Arc::clone(&enabled),
        Arc::clone(&saw_active),
        Arc::clone(&calls),
        Arc::clone(&slot),
    );
    let _scope = ay_core::resource::enter_check_stop(Arc::new(move || {
        if on.load(Ordering::Relaxed)
            && crate::smt::SmtContext::current_thread_term_memory_budget().is_none()
        {
            let owner = peer.lock().unwrap().as_ref().unwrap().clone();
            seen.store(
                owner.inner.running.load(Ordering::Acquire),
                Ordering::Relaxed,
            );
            let _ = owner.with_resources(|| {
                count.fetch_add(1, Ordering::Relaxed);
                Ok(17)
            });
            return true;
        }
        false
    }));
    let original = guard();
    let owner = ExternalInvariantValidationOwner::capture(&original, &configured());
    *slot.lock().unwrap() = Some(owner.clone());
    let result = owner
        .with_resources(|| {
            enabled.store(true, Ordering::Relaxed);
            Ok(23)
        })
        .unwrap();
    slot.lock().unwrap().take(); // break the diagnostic callback's Arc cycle
    assert!(saw_active.load(Ordering::Relaxed));
    assert_eq!(calls.load(Ordering::Relaxed), 0);
    assert_eq!(result, Err(Kind::Inconclusive));
}

#[test]
fn tighter_worker_raw_interrupt_refuses_generic_data_with_token_still_live() {
    let original = guard();
    let owner = ExternalInvariantValidationOwner::capture(&original, &configured());
    let worker = owner.clone();
    let (result, cancelled, reset_result) = std::thread::spawn(move || {
        let token = CancellationToken::new();
        let flag = Arc::new(AtomicBool::new(true));
        let _scope = crate::smt::deadline::ScopedLaneCancellation::install(
            token.clone(),
            Some(Arc::clone(&flag)),
        );
        let result = worker.with_resources(|| Ok(17)).unwrap();
        flag.store(false, Ordering::Relaxed);
        (result, token.is_cancelled(), worker.check())
    })
    .join()
    .unwrap();
    assert_eq!(result, Err(Kind::Cancelled));
    assert!(!cancelled);
    assert_eq!(reset_result, Some(Kind::Cancelled));
    assert_eq!(owner.check(), Some(Kind::Cancelled));
}

#[test]
fn worker_only_interrupt_set_at_final_restored_scope_fence_refuses_checked_data() {
    let enabled = Arc::new(AtomicBool::new(false));
    let flag = Arc::new(AtomicBool::new(false));
    let (on, raw) = (Arc::clone(&enabled), Arc::clone(&flag));
    let _scope = ay_core::resource::enter_check_stop(Arc::new(move || {
        if on.load(Ordering::Relaxed)
            && crate::smt::SmtContext::current_thread_term_memory_budget().is_none()
        {
            raw.store(true, Ordering::Relaxed);
        }
        false
    }));
    let original = guard();
    let owner = ExternalInvariantValidationOwner::capture(&original, &configured());
    let worker = owner.clone();
    let (result, reset) = std::thread::spawn(move || {
        let token = CancellationToken::new();
        let lane =
            crate::smt::deadline::ScopedLaneCancellation::install(token, Some(Arc::clone(&flag)));
        let result = worker
            .with_resources(|| {
                enabled.store(true, Ordering::Relaxed);
                Ok(17)
            })
            .unwrap();
        drop(lane);
        flag.store(false, Ordering::Relaxed);
        (result, worker.check())
    })
    .join()
    .unwrap();
    assert_eq!(result, Err(Kind::Cancelled));
    assert_eq!(reset, Some(Kind::Cancelled));
    assert_eq!(owner.check(), Some(Kind::Cancelled));
}

mod memory;
mod work_limit;
