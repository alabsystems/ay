// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::resource_observation::ScopedResourceObservation;
use crate::smt::{ScopedSmtDeadline, SmtContext};
use std::time::Duration;

fn future() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

fn capture(guard: &ResourceGuard, config: &PdrConfig) -> Resources {
    let caller = config.effective_cancellation_token();
    let replay = ScopedReplayControl::install_until(future(), caller.as_ref());
    Resources::capture(guard, config, &replay)
}

#[test]
fn captured_none_and_finite_caps_intersect_without_erasing_zero() {
    let owner = ResourceGuard::new();
    let _cap = SmtContext::scoped_thread_term_memory_budget(Some(4096));
    let inherited = capture(&owner, &PdrConfig::production(false));
    assert_eq!(inherited.memory.term_limit(), Some(4096));
    assert_eq!(
        inherited.validation_config(future()).memory_budget(),
        Some(4096)
    );
    let tight = capture(
        &owner,
        &PdrConfig::production(false).with_memory_budget(Some(1024)),
    );
    assert_eq!(tight.memory.term_limit(), Some(1024));
    let zero = capture(
        &owner,
        &PdrConfig::production(false).with_memory_budget(Some(0)),
    );
    assert_eq!(zero.memory.term_limit(), Some(0));
    assert!(!zero.poll());
    assert!(!zero.poll());
}

#[test]
fn original_and_ambient_absolute_walls_only_tighten() {
    let mut owner = ResourceGuard::new();
    owner.set_deadline(Some(Instant::now()));
    let expired = capture(&owner, &PdrConfig::production(false));
    assert!(!expired.poll());
    let _ambient = ScopedSmtDeadline::install_until(Instant::now());
    let inherited = capture(&ResourceGuard::new(), &PdrConfig::production(false));
    assert!(!inherited.poll());
}

#[test]
fn caller_cancel_reset_revives_only_a_fresh_attempt() {
    let caller = CancellationToken::new();
    let config = PdrConfig::production(false).with_cancellation_token(Some(caller.clone()));
    let owner = ResourceGuard::new();
    let attempt = capture(&owner, &config);
    assert!(attempt.poll());
    caller.cancel();
    assert!(!attempt.poll());
    caller.reset();
    assert!(!attempt.poll());
    assert!(attempt
        .validation_config(future())
        .cancellation_token
        .unwrap()
        .is_cancelled());
    assert!(capture(&owner, &config).poll());
}

#[test]
fn raw_original_guard_and_ambient_interrupts_remain_read_only_sticky() {
    let flag = Arc::new(AtomicBool::new(false));
    let mut owner = ResourceGuard::new();
    owner.set_cancel(Some(flag.clone()));
    let resources = capture(&owner, &PdrConfig::production(false));
    flag.store(true, Ordering::Relaxed);
    assert!(!resources.poll());
    flag.store(false, Ordering::Relaxed);
    assert!(!resources.poll());
    let token = CancellationToken::new();
    let _lane = crate::smt::deadline::ScopedLaneCancellation::install(token, Some(flag.clone()));
    let resources = capture(&ResourceGuard::new(), &PdrConfig::production(false));
    flag.store(true, Ordering::Relaxed);
    assert!(!resources.poll());
    flag.store(false, Ordering::Relaxed);
    assert!(!resources.poll());
    assert!(!flag.load(Ordering::Relaxed));
}

#[test]
fn all_rungs_and_native_polls_share_original_work_ticks() {
    let mut owner = ResourceGuard::new();
    owner.set_rlimit(Some(3));
    let resources = capture(&owner, &PdrConfig::production(false));
    assert!(resources.poll());
    assert!(resources.poll());
    assert_eq!(owner.ticks(), 2);
    assert!(!resources.poll());
    assert_eq!(owner.ticks(), 3);
    assert!(!resources.poll());
    assert_eq!(owner.ticks(), 3);
    assert!(!capture(&owner, &PdrConfig::production(false)).poll());
}

#[test]
fn validator_memory_and_cancellation_survive_drop_but_local_timeout_is_not_global() {
    let owner = ResourceGuard::new();
    let config = PdrConfig::production(false);
    let live = capture(&owner, &config);
    live.observe_validation(
        Some(ResourceRefusal::Timeout),
        &Ok(ExternalInvariantValidation::Timeout),
    );
    assert!(live.poll());
    let memory = capture(&owner, &config);
    {
        let observation = ScopedResourceObservation::install();
        observation.note(ResourceRefusal::Memory);
        memory.observe_validation(
            observation.first(),
            &Err(crate::ChcError::Internal("test refusal".into())),
        );
    }
    assert!(!memory.poll());
    for reason in [
        ExternalInvariantValidation::Memory,
        ExternalInvariantValidation::Cancelled,
    ] {
        let resources = capture(&owner, &config);
        resources.observe_validation(None, &Ok(reason));
        assert!(!resources.poll());
    }
}

#[test]
fn inherited_check_stop_and_reentry_cannot_be_cleared_to_resume() {
    let stopped = Arc::new(AtomicBool::new(true));
    let flag = stopped.clone();
    let scope = ay_core::resource::enter_check_stop(Arc::new(move || flag.load(Ordering::Relaxed)));
    let resources = capture(&ResourceGuard::new(), &PdrConfig::production(false));
    assert!(!resources.poll());
    stopped.store(false, Ordering::Relaxed);
    assert!(!resources.poll());
    drop(scope);
    let resources = Arc::new(capture(
        &ResourceGuard::new(),
        &PdrConfig::production(false),
    ));
    let nested = resources.clone();
    let scope = ay_core::resource::enter_check_stop(Arc::new(move || {
        assert!(!nested.poll());
        false
    }));
    assert!(!resources.poll());
    drop(scope);
    assert!(!resources.poll());
}

#[test]
fn panic_in_original_check_stop_keeps_resources_terminal() {
    let resources = capture(&ResourceGuard::new(), &PdrConfig::production(false));
    let scope = ay_core::resource::enter_check_stop(Arc::new(|| panic!("test original stop")));
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| resources.poll()));
    assert!(result.is_err());
    drop(scope);
    assert!(!resources.poll());
}

#[test]
fn original_resource_carrier_adds_no_send_sync_or_borrowed_solver_restriction() {
    fn require_send_sync<T: Send + Sync>() {}
    require_send_sync::<Resources>();
    let resources = Arc::new(capture(
        &ResourceGuard::new(),
        &PdrConfig::production(false),
    ));
    let poll: Arc<dyn Fn() -> bool + Send + Sync> = Arc::new(move || resources.poll());
    assert!(poll());
}

#[test]
fn original_group_soft_trip_survives_scope_drop_and_raw_cancel_reset() {
    let owner = ResourceGuard::new();
    let cancel = Arc::new(AtomicBool::new(false));
    let scope = ay_sys::enter_memory_group(ay_sys::MemoryGroup::new(
        1024 * 1024,
        usize::MAX,
        cancel.clone(),
    ));
    let resources = capture(&owner, &PdrConfig::production(false));
    assert!(resources.poll());
    ay_sys::charge_current_for_testing(2 * 1024 * 1024);
    assert!(cancel.load(Ordering::Relaxed));
    drop(scope);
    cancel.store(false, Ordering::Relaxed);
    assert!(ay_sys::current_memory_group_observation().is_none());
    assert!(!owner.should_stop());
    assert!(resources.memory.open());
    assert!(
        !resources.poll(),
        "the original group trip cannot disappear with TLS"
    );
    assert!(!resources.poll());
    assert!(capture(&owner, &PdrConfig::production(false)).poll());
}

#[test]
fn original_group_shed_survives_healthy_replacement_without_registry_ownership() {
    let owner = ResourceGuard::new();
    let cancel = Arc::new(AtomicBool::new(false));
    let original = ay_sys::MemoryGroup::new(usize::MAX, usize::MAX, cancel.clone());
    let weak = Arc::downgrade(&original);
    let scope = ay_sys::enter_memory_group(original.clone());
    let resources = capture(&owner, &PdrConfig::production(false));
    assert!(resources.poll());
    assert!(original.shed());
    assert!(
        !original.soft_tripped(),
        "shed-only is still a memory refusal"
    );
    drop(scope);
    drop(original);
    assert!(
        weak.upgrade().is_none(),
        "the observation retains no group owner"
    );
    cancel.store(false, Ordering::Relaxed);
    let _replacement = ay_sys::enter_memory_group(ay_sys::MemoryGroup::new(
        usize::MAX,
        usize::MAX,
        Arc::new(AtomicBool::new(false)),
    ));
    assert!(!ay_sys::current_memory_group_observation()
        .unwrap()
        .is_tripped());
    assert!(!owner.should_stop());
    assert!(resources.memory.open());
    assert!(
        !resources.poll(),
        "a healthy replacement cannot replace the original refusal"
    );
    assert!(!resources.poll());
    assert!(capture(&owner, &PdrConfig::production(false)).poll());
}
