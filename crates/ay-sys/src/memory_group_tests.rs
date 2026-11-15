// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use super::*;

#[test]
fn soft_limit_sets_cancel_flag_once_and_hard_limit_is_reported() {
    let cancel = Arc::new(AtomicBool::new(false));
    let group = MemoryGroup::new(1000, 2000, Arc::clone(&cancel));
    let scope = enter_memory_group(Arc::clone(&group));
    charge_current_for_testing(900);
    assert!(!cancel.load(Ordering::Relaxed));
    assert!(!current_memory_group_over_hard_limit());
    charge_current_for_testing(200);
    assert!(
        cancel.load(Ordering::Relaxed),
        "soft limit cancels the lane"
    );
    assert!(group.soft_tripped());
    assert!(!current_memory_group_over_hard_limit());
    charge_current_for_testing(1000);
    assert!(current_memory_group_over_hard_limit());
    drop(scope);
    assert!(
        !current_memory_group_over_hard_limit(),
        "no group is current after the scope ends"
    );
    assert_eq!(group.live_bytes(), 2100);
}

#[test]
fn groups_are_per_thread() {
    let cancel = Arc::new(AtomicBool::new(false));
    let group = MemoryGroup::new(100, 100, Arc::clone(&cancel));
    let _scope = enter_memory_group(Arc::clone(&group));
    std::thread::spawn(|| charge_current_for_testing(1_000_000))
        .join()
        .expect("thread");
    assert_eq!(group.live_bytes(), 0, "another thread's bytes are not ours");
    assert!(!cancel.load(Ordering::Relaxed));
}

#[test]
fn scopes_nest_and_restore() {
    let outer = MemoryGroup::new(usize::MAX, usize::MAX, Arc::new(AtomicBool::new(false)));
    let inner = MemoryGroup::new(usize::MAX, usize::MAX, Arc::new(AtomicBool::new(false)));
    let outer_scope = enter_memory_group(Arc::clone(&outer));
    {
        let _inner_scope = enter_memory_group(Arc::clone(&inner));
        charge_current_for_testing(10);
    }
    charge_current_for_testing(5);
    drop(outer_scope);
    assert_eq!(inner.live_bytes(), 10);
    assert_eq!(outer.live_bytes(), 5);
}

#[test]
fn out_of_order_drop_never_restores_a_released_group() {
    let outer = MemoryGroup::new(usize::MAX, usize::MAX, Arc::new(AtomicBool::new(false)));
    let inner = MemoryGroup::new(usize::MAX, usize::MAX, Arc::new(AtomicBool::new(false)));
    let outer_scope = enter_memory_group(Arc::clone(&outer));
    let inner_scope = enter_memory_group(Arc::clone(&inner));
    // Drop the OUTER scope first: attribution stops (CURRENT is null) rather
    // than pointing at anything released later.
    drop(outer_scope);
    charge_current_for_testing(7);
    assert_eq!(
        inner.live_bytes(),
        0,
        "no group is current after an out-of-order drop"
    );
    drop(inner_scope);
    charge_current_for_testing(9);
    assert_eq!(
        outer.live_bytes(),
        0,
        "the released outer group is never restored"
    );
    assert_eq!(inner.live_bytes(), 0);
}

#[test]
fn soft_trip_is_visible_to_bare_stop_polls_only_while_the_scope_is_current() {
    assert!(
        !current_memory_group_soft_tripped(),
        "no group entered: one relaxed load, false"
    );
    let cancel = Arc::new(AtomicBool::new(false));
    let group = MemoryGroup::new(100, 1000, Arc::clone(&cancel));
    let scope = enter_memory_group(Arc::clone(&group));
    assert!(!current_memory_group_soft_tripped());
    charge_current_for_testing(101);
    assert!(
        current_memory_group_soft_tripped(),
        "the lane's own trip is polled"
    );
    assert!(cancel.load(Ordering::Relaxed));
    let other = std::thread::spawn(current_memory_group_soft_tripped)
        .join()
        .expect("thread");
    assert!(!other, "another thread's poll sees its own (absent) group");
    drop(scope);
    assert!(!current_memory_group_soft_tripped());
}

#[test]
fn same_group_scopes_have_distinct_lifetimes_even_after_moving() {
    let group = MemoryGroup::new(usize::MAX, usize::MAX, Arc::new(AtomicBool::new(false)));
    let mut scopes = [
        Some(enter_memory_group(Arc::clone(&group))),
        Some(enter_memory_group(Arc::clone(&group))),
    ];
    let before = group.live_bytes();
    charge_current_for_testing(7);
    assert_eq!(group.live_bytes() - before, 7);
    drop(scopes[1].take());
    let before = group.live_bytes();
    charge_current_for_testing(11);
    assert_eq!(group.live_bytes() - before, 11, "outer scope restored");
    drop(scopes[0].take());
    let before = group.live_bytes();
    charge_current_for_testing(13);
    assert_eq!(group.live_bytes(), before, "both scopes ended");
}

#[test]
fn reentering_same_group_cannot_restore_an_invalidated_predecessor() {
    // Keep these external owners so the old bug is an observable stale charge,
    // not UB in the regression. Without the outer owner, its pointer dangles.
    let outer = MemoryGroup::new(usize::MAX, usize::MAX, Arc::new(AtomicBool::new(false)));
    let group = MemoryGroup::new(usize::MAX, usize::MAX, Arc::new(AtomicBool::new(false)));
    let predecessor = enter_memory_group(Arc::clone(&outer));
    let old_scope = enter_memory_group(Arc::clone(&group));
    drop(predecessor);
    let new_scope = enter_memory_group(Arc::clone(&group));
    drop(old_scope);

    let before = (outer.live_bytes(), group.live_bytes());
    charge_current_for_testing(7);
    assert_eq!((outer.live_bytes(), group.live_bytes()), before);
    drop(new_scope);
    let before = (outer.live_bytes(), group.live_bytes());
    charge_current_for_testing(11);
    assert_eq!((outer.live_bytes(), group.live_bytes()), before);

    let fresh = enter_memory_group(Arc::clone(&group));
    let before = group.live_bytes();
    charge_current_for_testing(13);
    assert_eq!(group.live_bytes() - before, 13, "fresh scopes still work");
    drop(fresh);
}

#[test]
fn same_group_out_of_order_drop_does_not_impersonate_inner_scope() {
    let predecessor = MemoryGroup::new(usize::MAX, usize::MAX, Arc::new(AtomicBool::new(false)));
    let group = MemoryGroup::new(usize::MAX, usize::MAX, Arc::new(AtomicBool::new(false)));
    let enclosing = enter_memory_group(Arc::clone(&predecessor));
    let outer = enter_memory_group(Arc::clone(&group));
    let inner = enter_memory_group(Arc::clone(&group));
    drop(outer);
    let before = (predecessor.live_bytes(), group.live_bytes());
    charge_current_for_testing(7);
    assert_eq!((predecessor.live_bytes(), group.live_bytes()), before);
    drop(inner);
    drop(enclosing);
    let before = (predecessor.live_bytes(), group.live_bytes());
    charge_current_for_testing(11);
    assert_eq!((predecessor.live_bytes(), group.live_bytes()), before);
}

/// The governor sheds the lane holding the most live heap, which then reads
/// as cancelled and over its hard limit, and leaves the census.
#[test]
fn shedding_cancels_the_fattest_lane_and_forces_its_unwind() {
    // Charges far above anything a concurrent test group holds, so this test
    // sheds only its own groups whatever else the registry lists.
    const HUGE: usize = 1 << 50;
    let fat_cancel = Arc::new(AtomicBool::new(false));
    let fat = MemoryGroup::named("fat", usize::MAX, usize::MAX, Arc::clone(&fat_cancel));
    let thin_cancel = Arc::new(AtomicBool::new(false));
    let thin = MemoryGroup::named("thin", usize::MAX, usize::MAX, Arc::clone(&thin_cancel));
    {
        let _scope = enter_memory_group(Arc::clone(&thin));
        charge_current_for_testing(HUGE + 1);
    }
    let fat_scope = enter_memory_group(Arc::clone(&fat));
    charge_current_for_testing(HUGE + 2);
    assert!(!current_memory_group_over_hard_limit());
    assert!(memory_group_census()
        .iter()
        .any(|usage| usage.label == "fat" && usage.live_bytes > 0));

    let shed = shed_fattest_memory_group(HUGE, 1).expect("the fat lane is shed");
    assert_eq!(shed.label, "fat");
    assert!(fat_cancel.load(Ordering::Relaxed), "its lane is cancelled");
    assert!(
        !thin_cancel.load(Ordering::Relaxed),
        "the other lane runs on"
    );
    assert!(fat.was_shed());
    assert!(current_memory_group_over_hard_limit(), "it unwinds");
    assert!(current_memory_group_soft_tripped());
    assert!(!memory_group_census()
        .iter()
        .any(|usage| usage.label == "fat"));
    drop(fat_scope);

    let next = shed_fattest_memory_group(HUGE, 0).expect("then the next fattest");
    assert_eq!(next.label, "thin");
    assert!(thin_cancel.load(Ordering::Relaxed));
    assert!(
        shed_fattest_memory_group(HUGE, 0).is_none(),
        "no lane above the minimum is left"
    );
}

/// The last running lanes are kept, and lanes below the minimum are not shed.
#[test]
fn shedding_keeps_the_last_lanes_and_skips_small_ones() {
    let cancel = Arc::new(AtomicBool::new(false));
    let group = MemoryGroup::named("small", usize::MAX, usize::MAX, Arc::clone(&cancel));
    let _scope = enter_memory_group(Arc::clone(&group));
    charge_current_for_testing(10);
    assert!(
        shed_fattest_memory_group(usize::MAX, 0).is_none(),
        "a lane under the minimum is never shed"
    );
    assert!(
        shed_fattest_memory_group(0, usize::MAX).is_none(),
        "the kept lanes are never shed"
    );
    assert!(!cancel.load(Ordering::Relaxed));
    assert!(!group.was_shed());
}

/// A dropped group leaves the registry.
#[test]
fn dropped_groups_leave_the_census() {
    let group = MemoryGroup::named(
        "gone",
        usize::MAX,
        usize::MAX,
        Arc::new(AtomicBool::new(false)),
    );
    let weak = Arc::downgrade(&group);
    drop(group);
    assert!(weak.upgrade().is_none());
    assert!(!memory_group_census()
        .iter()
        .any(|usage| usage.label == "gone"));
}

/// A shed lane that keeps allocating past the slack is throttled: each
/// further charge pauses its thread.
#[test]
fn a_shed_lane_that_keeps_growing_is_throttled() {
    let group = MemoryGroup::named(
        "runaway",
        usize::MAX,
        usize::MAX,
        Arc::new(AtomicBool::new(false)),
    );
    let _scope = enter_memory_group(Arc::clone(&group));
    charge_current_for_testing(1 << 20);
    let started = std::time::Instant::now();
    charge_current_for_testing(1 << 20);
    let unthrottled = started.elapsed();
    assert!(group.shed());
    charge_current_for_testing(SHED_GROWTH_SLACK / 2);
    let started = std::time::Instant::now();
    charge_current_for_testing(SHED_GROWTH_SLACK);
    let throttled = started.elapsed();
    assert!(
        throttled >= std::time::Duration::from_millis(1),
        "growth past the slack pauses the lane ({throttled:?}, unthrottled {unthrottled:?})"
    );
    assert!(
        !group.soft_tripped(),
        "the soft limit itself was never crossed"
    );
}

#[test]
fn observation_preserves_original_group_across_nested_replacement() {
    assert!(current_memory_group_observation().is_none());
    let original_cancel = Arc::new(AtomicBool::new(false));
    let original = MemoryGroup::new(1024 * 1024, usize::MAX, Arc::clone(&original_cancel));
    let original_scope = enter_memory_group(original);
    let observed = current_memory_group_observation().expect("original group");
    let cloned = observed.clone();
    {
        let nested = MemoryGroup::new(1024 * 1024, usize::MAX, Arc::new(AtomicBool::new(false)));
        let _nested_scope = enter_memory_group(nested);
        let nested_observed = current_memory_group_observation().expect("nested group");
        charge_current_for_testing(2 * 1024 * 1024);
        assert!(nested_observed.is_tripped());
        assert!(
            !observed.is_tripped(),
            "a nested trip is not the original trip"
        );
        assert!(!cloned.is_tripped());
    }
    assert!(!observed.is_tripped());
    charge_current_for_testing(2 * 1024 * 1024);
    assert!(observed.is_tripped());
    assert!(cloned.is_tripped());
    assert!(original_cancel.load(Ordering::Relaxed));
    drop(original_scope);
    assert!(current_memory_group_observation().is_none());
    assert!(
        observed.is_tripped(),
        "owner cleanup does not erase the trip"
    );
}

#[test]
fn observation_outlives_an_untripped_owner_scope() {
    let scope = enter_memory_group(MemoryGroup::new(
        usize::MAX,
        usize::MAX,
        Arc::new(AtomicBool::new(false)),
    ));
    let observed = current_memory_group_observation().expect("entered group");
    drop(scope);
    assert!(current_memory_group_observation().is_none());
    assert!(
        !observed.is_tripped(),
        "retaining a latch cannot invent a trip"
    );
}

#[test]
fn resetting_cancel_flag_cannot_clear_retained_soft_trip() {
    let cancel = Arc::new(AtomicBool::new(false));
    let scope = enter_memory_group(MemoryGroup::new(
        1024 * 1024,
        usize::MAX,
        Arc::clone(&cancel),
    ));
    let observed = current_memory_group_observation().expect("entered group");
    charge_current_for_testing(2 * 1024 * 1024);
    assert!(observed.is_tripped());
    cancel.store(false, Ordering::Relaxed);
    assert!(!cancel.load(Ordering::Relaxed));
    assert!(
        observed.is_tripped(),
        "the retained latch has no reset authority"
    );
    assert!(current_memory_group_soft_tripped());
    drop(scope);
    assert!(observed.is_tripped());
}

#[test]
fn invalidated_tls_scope_cannot_erase_an_observed_trip() {
    let outer = enter_memory_group(MemoryGroup::new(
        1024 * 1024,
        usize::MAX,
        Arc::new(AtomicBool::new(false)),
    ));
    let observed = current_memory_group_observation().expect("outer group");
    charge_current_for_testing(2 * 1024 * 1024);
    let inner = enter_memory_group(MemoryGroup::new(
        usize::MAX,
        usize::MAX,
        Arc::new(AtomicBool::new(false)),
    ));
    drop(outer);
    assert!(current_memory_group_observation().is_none());
    assert!(observed.is_tripped());
    drop(inner);
    assert!(current_memory_group_observation().is_none());
    assert!(observed.is_tripped());
}

#[test]
fn retained_observation_keeps_original_shed_without_inventing_a_soft_trip() {
    let cancel = Arc::new(AtomicBool::new(false));
    let original = MemoryGroup::named("observed-shed", usize::MAX, usize::MAX, Arc::clone(&cancel));
    let weak = Arc::downgrade(&original);
    let scope = enter_memory_group(Arc::clone(&original));
    let observed = current_memory_group_observation().expect("original group");
    assert!(!observed.is_tripped());
    assert!(original.shed());
    assert!(!original.shed(), "shedding is terminal");
    assert!(
        !original.soft_tripped(),
        "shedding did not cross the soft limit"
    );
    assert!(observed.is_tripped());
    cancel.store(false, Ordering::Relaxed);
    assert!(
        observed.is_tripped(),
        "resetting cancellation cannot undo shedding"
    );
    {
        let _nested = enter_memory_group(MemoryGroup::new(
            usize::MAX,
            usize::MAX,
            Arc::new(AtomicBool::new(false)),
        ));
        assert!(!current_memory_group_observation()
            .expect("nested group")
            .is_tripped());
        assert!(
            observed.is_tripped(),
            "the observation belongs to the original group"
        );
    }
    drop(scope);
    drop(original);
    assert!(
        weak.upgrade().is_none(),
        "observations do not retain registry ownership"
    );
    assert!(current_memory_group_observation().is_none());
    assert!(
        observed.is_tripped(),
        "cleanup cannot erase original shedding"
    );
}
