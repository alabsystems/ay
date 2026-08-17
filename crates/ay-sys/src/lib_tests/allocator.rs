// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_counting_allocator_tracks_live_bytes() {
    use std::alloc::{GlobalAlloc, Layout, System};

    let base = current_live_bytes();
    let alloc = CountingAllocator::new(System);
    let layout = Layout::from_size_align(8192, 8).unwrap();

    // SAFETY: `layout` is non-zero-sized and well-formed; the pointer returned
    // is freed exactly once below with the same layout.
    let ptr = unsafe { alloc.alloc(layout) };
    assert!(!ptr.is_null());
    assert_eq!(
        current_live_bytes(),
        base + 8192,
        "alloc must add layout.size() live bytes"
    );

    // SAFETY: `ptr` came from `alloc.alloc(layout)` just above with this layout.
    unsafe { alloc.dealloc(ptr, layout) };
    assert_eq!(
        current_live_bytes(),
        base,
        "dealloc must subtract layout.size() live bytes"
    );
}

#[test]
fn test_counting_allocator_realloc_grow_and_shrink() {
    use std::alloc::{GlobalAlloc, Layout, System};

    let base = current_live_bytes();
    let alloc = CountingAllocator::new(System);
    let layout = Layout::from_size_align(1024, 8).unwrap();

    // SAFETY: well-formed non-zero layout; freed once below.
    let ptr = unsafe { alloc.alloc(layout) };
    assert!(!ptr.is_null());
    assert_eq!(current_live_bytes(), base + 1024);

    // Grow 1024 -> 4096: +3072.
    // SAFETY: `ptr`/`layout` are the live block; `new_size` is non-zero.
    let ptr = unsafe { alloc.realloc(ptr, layout, 4096) };
    assert!(!ptr.is_null());
    assert_eq!(current_live_bytes(), base + 4096, "grow must add the delta");

    // Shrink 4096 -> 512: -3584. The block's current layout size is 4096.
    let grown = Layout::from_size_align(4096, 8).unwrap();
    // SAFETY: `ptr` is the live block whose current size is 4096.
    let ptr = unsafe { alloc.realloc(ptr, grown, 512) };
    assert!(!ptr.is_null());
    assert_eq!(
        current_live_bytes(),
        base + 512,
        "shrink must subtract the delta"
    );

    let shrunk = Layout::from_size_align(512, 8).unwrap();
    // SAFETY: frees the live block with its current (512-byte) layout.
    unsafe { alloc.dealloc(ptr, shrunk) };
    assert_eq!(current_live_bytes(), base);
}

/// The hard ceiling is a strict `>` comparison against an armed, non-zero
/// bound, and is inert while disarmed. The probe takes `live` as an argument,
/// so this exercises the predicate without moving the real allocator counter —
/// arming a low ceiling in-process would `_exit` the test runner.
#[test]
fn hard_memory_ceiling_is_inert_until_armed_and_then_strict() {
    // Far above anything this process will ever hold live, so no real
    // allocation can breach it while the test runs.
    const CEILING: usize = 1 << 60;

    assert!(
        !hard_memory_ceiling_breached(usize::MAX),
        "a disarmed ceiling never breaches, at any live size"
    );

    HARD_MEMORY_CEILING.store(CEILING, Ordering::SeqCst);
    assert!(
        !hard_memory_ceiling_breached(CEILING - 1),
        "below the ceiling is not a breach"
    );
    assert!(
        !hard_memory_ceiling_breached(CEILING),
        "exactly at the ceiling is not a breach"
    );
    assert!(
        hard_memory_ceiling_breached(CEILING + 1),
        "one byte past the ceiling is a breach"
    );
    HARD_MEMORY_CEILING.store(0, Ordering::SeqCst);

    assert!(
        !hard_memory_ceiling_breached(usize::MAX),
        "disarming restores the inert state"
    );
}

/// Arming publishes the action before the ceiling, so a breach can never see a
/// live ceiling with no verdict to emit.
#[test]
fn arming_the_hard_ceiling_publishes_the_action() {
    static ACTION: HardMemoryCeiling = HardMemoryCeiling {
        stdout_line: b"unknown\n",
        stderr_line: b"(:reason-unknown \"memout\")\n",
        exit_code: 124,
    };

    arm_hard_memory_ceiling(0, &ACTION);
    let published = HARD_MEMORY_CEILING_ACTION.load(Ordering::SeqCst);
    assert!(!published.is_null(), "the action must be published");
    // SAFETY: just stored from a `&'static HardMemoryCeiling`.
    let published = unsafe { &*published };
    assert_eq!(published.exit_code, 124);
    assert_eq!(published.stdout_line, b"unknown\n");
    assert_eq!(
        HARD_MEMORY_CEILING.load(Ordering::SeqCst),
        0,
        "arming with 0 leaves the ceiling disabled"
    );
}
