// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exercise scope entry and destruction through the actual global allocator.
//! This is a separate target: the library's counter tests require no global
//! counting allocator and deliberately mutate its process-wide counters.

use std::alloc::System;
use std::hint::black_box;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use ay_sys::{enter_memory_group, CountingAllocator, MemoryGroup};

#[global_allocator]
static GLOBAL: CountingAllocator<System> = CountingAllocator::new(System);

const ALLOCATION_BYTES: usize = 4096;
type AllocationDelta<const N: usize> = ([isize; N], [isize; N]);

fn unlimited_group() -> Arc<MemoryGroup> {
    MemoryGroup::new(usize::MAX, usize::MAX, Arc::new(AtomicBool::new(false)))
}

/// No formatting, assertions, or harness calls occur between these samples.
/// Keep the allocation opaque and alive through the first counter read; the
/// second read observes its real deallocation, not a synthetic counter debit.
fn allocation_delta<const N: usize>(groups: [&MemoryGroup; N]) -> AllocationDelta<N> {
    let before = groups.map(MemoryGroup::live_bytes);
    let buffer = black_box(vec![0u8; ALLOCATION_BYTES]);
    black_box(buffer.as_ptr());
    let allocated = std::array::from_fn(|i| groups[i].live_bytes() - before[i]);
    drop(black_box(buffer));
    let freed = std::array::from_fn(|i| groups[i].live_bytes() - before[i]);
    (allocated, freed)
}

#[test]
fn allocator_tracks_moved_same_group_lifo_scopes_and_marker_lifetimes() {
    let group = unlimited_group();
    let outer = enter_memory_group(Arc::clone(&group));
    let before_marker = group.live_bytes();
    let inner = enter_memory_group(Arc::clone(&group));
    let marker_charge = group.live_bytes() - before_marker;
    let mut scopes = [Some(outer), Some(inner)];

    let inner_allocation = allocation_delta([group.as_ref()]);
    let before_drop = group.live_bytes();
    drop(scopes[1].take());
    let marker_credit = group.live_bytes() - before_drop;
    let outer_allocation = allocation_delta([group.as_ref()]);
    drop(scopes[0].take());
    let outside_allocation = allocation_delta([group.as_ref()]);

    // All guards are gone before an assertion can panic. The one-byte marker
    // was allocated under the outer scope and freed after restoring it.
    assert_eq!(marker_charge, 1);
    assert_eq!(marker_credit, -1);
    assert_eq!(inner_allocation, ([4096], [0]));
    assert_eq!(outer_allocation, ([4096], [0]));
    assert_eq!(outside_allocation, ([0], [0]));
}

#[test]
fn allocator_reentry_cannot_restore_an_invalidated_predecessor() {
    // External owners keep the old implementation's stale pointer live, so a
    // regression fails by misattribution without executing a use-after-free.
    let predecessor = unlimited_group();
    let group = unlimited_group();
    let enclosing = enter_memory_group(Arc::clone(&predecessor));
    let old_scope = enter_memory_group(Arc::clone(&group));
    drop(enclosing);
    let new_scope = enter_memory_group(Arc::clone(&group));
    drop(old_scope);
    let invalidated = allocation_delta([predecessor.as_ref(), group.as_ref()]);
    drop(new_scope);
    let after_cleanup = allocation_delta([predecessor.as_ref(), group.as_ref()]);

    let fresh = enter_memory_group(Arc::clone(&group));
    let fresh_allocation = allocation_delta([predecessor.as_ref(), group.as_ref()]);
    drop(fresh);
    let outside_allocation = allocation_delta([predecessor.as_ref(), group.as_ref()]);

    assert_eq!(invalidated, ([0, 0], [0, 0]));
    assert_eq!(after_cleanup, ([0, 0], [0, 0]));
    assert_eq!(fresh_allocation, ([0, 4096], [0, 0]));
    assert_eq!(outside_allocation, ([0, 0], [0, 0]));
}

#[test]
fn allocator_unwind_restores_the_enclosing_scope() {
    let outer = unlimited_group();
    let inner = unlimited_group();
    let enclosing = enter_memory_group(Arc::clone(&outer));
    let outcome: std::thread::Result<()> = std::panic::catch_unwind(|| {
        let _inner_scope = enter_memory_group(Arc::clone(&inner));
        let observed = allocation_delta([outer.as_ref(), inner.as_ref()]);
        // Carry the pre-unwind observation out without assertions or shared
        // mutable state. The guard must restore TLS while this unwinds.
        std::panic::panic_any(observed);
    });
    let restored = allocation_delta([outer.as_ref(), inner.as_ref()]);
    drop(enclosing);
    let outside_allocation = allocation_delta([outer.as_ref(), inner.as_ref()]);

    let Err(payload) = outcome else {
        panic!("the inner scope must have unwound");
    };
    let Ok(observed) = payload.downcast::<AllocationDelta<2>>() else {
        panic!("the unwind must carry the allocation observation");
    };
    assert_eq!(*observed, ([0, 4096], [0, 0]));
    assert_eq!(restored, ([4096, 0], [0, 0]));
    assert_eq!(outside_allocation, ([0, 0], [0, 0]));
}
