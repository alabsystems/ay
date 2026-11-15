// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::super::{work_counter, MAX_FUNCTIONAL_WORK};
use super::*;
use std::sync::atomic::{AtomicBool, Ordering};

#[test]
fn one_short_retained_model_work_is_terminal_across_a_new_read_frame() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let probe = loaded(end);
    let term = root(&probe);
    let data = probe
        .last_model
        .as_ref()
        .expect("model")
        .functional_arrays
        .as_ref()
        .expect("data");
    let before = data.work_used.load(Ordering::Acquire);
    assert!(confirm(&probe, term));
    let spent = data.work_used.load(Ordering::Acquire) - before;
    let exec = loaded(end);
    let term = root(&exec);
    let used = &exec
        .last_model
        .as_ref()
        .expect("model")
        .functional_arrays
        .as_ref()
        .expect("data")
        .work_used;
    used.store(MAX_FUNCTIONAL_WORK - spent + 1, Ordering::Release);
    assert!(!confirm(&exec, term));
    assert_eq!(used.load(Ordering::Acquire), work_counter::REFUSED);
    let read = exec.begin_external_evaluation_read();
    assert!(!confirm(&exec, term));
    drop(read);
    assert!(Instant::now() < end);
}

#[test]
fn original_raw_stop_and_absolute_end_refuse_after_reset_and_restoration() {
    let end = Instant::now() + Duration::from_secs(20);
    let stopped = Arc::new(AtomicBool::new(false));
    let flag = stopped.clone();
    let _owner = enter_check_stop(Arc::new(move || {
        Instant::now() >= end || flag.load(Ordering::Acquire)
    }));
    let mut exec = loaded(end);
    let term = root(&exec);
    stopped.store(true, Ordering::Release);
    assert!(!confirm(&exec, term));
    stopped.store(false, Ordering::Release);
    exec.set_deadline(Some(end));
    exec.begin_subset_evaluation_attempt();
    assert!(!confirm(&exec, term));
    let mut fresh = loaded(end);
    let term = root(&fresh);
    fresh.set_deadline(Some(Instant::now() - Duration::from_secs(1)));
    assert!(!confirm(&fresh, term));
    fresh.set_deadline(Some(end));
    fresh.begin_subset_evaluation_attempt();
    assert!(!confirm(&fresh, term));
    assert!(Instant::now() < end);
}

#[test]
fn wrapper_final_owner_callback_veto_is_terminal_after_all_capture_cleanup() {
    let end = Instant::now() + Duration::from_secs(20);
    final_veto(end, Purpose::Arm);
    final_veto(end, Purpose::Confirm);
}

fn final_veto(end: Instant, purpose: Purpose) {
    use std::sync::atomic::AtomicUsize;
    let run = |exec: &Executor| match purpose {
        Purpose::Arm => exec.complete_array_fill_restoration_candidate(root(exec)),
        Purpose::Confirm => confirm(exec, root(exec)),
    };
    let calls = Arc::new(AtomicUsize::new(0));
    let armed = Arc::new(AtomicBool::new(false));
    let refuse_at = Arc::new(AtomicUsize::new(usize::MAX));
    let (count, enabled, limit) = (calls.clone(), armed.clone(), refuse_at.clone());
    let _owner = enter_check_stop(Arc::new(move || {
        Instant::now() >= end
            || (enabled.load(Ordering::Acquire)
                && count.fetch_add(1, Ordering::AcqRel) + 1 >= limit.load(Ordering::Acquire))
    }));
    let probe = loaded(end);
    armed.store(true, Ordering::Release);
    assert!(run(&probe));
    let observed = calls.load(Ordering::Acquire);
    assert!(observed > 1);
    armed.store(false, Ordering::Release);
    let exec = loaded(end);
    calls.store(0, Ordering::Release);
    refuse_at.store(observed, Ordering::Release);
    armed.store(true, Ordering::Release);
    assert!(
        !run(&exec),
        "last original callback runs in finish after scratch drop"
    );
    assert_eq!(calls.load(Ordering::Acquire), observed);
    armed.store(false, Ordering::Release);
    let used = &exec
        .last_model
        .as_ref()
        .expect("model")
        .functional_arrays
        .as_ref()
        .expect("data")
        .work_used;
    assert_eq!(used.load(Ordering::Acquire), work_counter::REFUSED);
    let read = exec.begin_external_evaluation_read();
    assert!(!run(&exec));
    drop(read);
    assert!(Instant::now() < end);
}
