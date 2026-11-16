// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_counting_allocator_tracks_live_bytes() {
    use std::alloc::{GlobalAlloc, Layout, System};

    let _serial = live_bytes_test_lock();
    let base = exact_live_bytes();
    let alloc = CountingAllocator::new(System);
    let layout = Layout::from_size_align(8192, 8).unwrap();

    // SAFETY: `layout` is non-zero-sized and well-formed; the pointer returned
    // is freed exactly once below with the same layout.
    let ptr = unsafe { alloc.alloc(layout) };
    assert!(!ptr.is_null());
    assert_eq!(
        exact_live_bytes(),
        base + 8192,
        "alloc must add layout.size() live bytes"
    );

    // SAFETY: `ptr` came from `alloc.alloc(layout)` just above with this layout.
    unsafe { alloc.dealloc(ptr, layout) };
    assert_eq!(
        exact_live_bytes(),
        base,
        "dealloc must subtract layout.size() live bytes"
    );
}

#[test]
fn test_counting_allocator_realloc_grow_and_shrink() {
    use std::alloc::{GlobalAlloc, Layout, System};

    let _serial = live_bytes_test_lock();
    let base = exact_live_bytes();
    let alloc = CountingAllocator::new(System);
    let layout = Layout::from_size_align(1024, 8).unwrap();

    // SAFETY: well-formed non-zero layout; freed once below.
    let ptr = unsafe { alloc.alloc(layout) };
    assert!(!ptr.is_null());
    assert_eq!(exact_live_bytes(), base + 1024);

    // Grow 1024 -> 4096: +3072.
    // SAFETY: `ptr`/`layout` are the live block; `new_size` is non-zero.
    let ptr = unsafe { alloc.realloc(ptr, layout, 4096) };
    assert!(!ptr.is_null());
    assert_eq!(exact_live_bytes(), base + 4096, "grow must add the delta");

    // Shrink 4096 -> 512: -3584. The block's current layout size is 4096.
    let grown = Layout::from_size_align(4096, 8).unwrap();
    // SAFETY: `ptr` is the live block whose current size is 4096.
    let ptr = unsafe { alloc.realloc(ptr, grown, 512) };
    assert!(!ptr.is_null());
    assert_eq!(
        exact_live_bytes(),
        base + 512,
        "shrink must subtract the delta"
    );

    let shrunk = Layout::from_size_align(512, 8).unwrap();
    // SAFETY: frees the live block with its current (512-byte) layout.
    unsafe { alloc.dealloc(ptr, shrunk) };
    assert_eq!(exact_live_bytes(), base);
}

/// A sub-batch allocation stays off the published total: it waits on its
/// stripe, and only the exact count (every stripe summed) shows it.
///
/// Before the stripes every allocation and every free was a read-modify-write
/// of the one published atomic, from every thread. With the CHC portfolio's
/// engines running in parallel that cache line was the largest single cost in
/// the process (`PERF_vs_winners_2026-09-25.md`, row 5), and on
/// `faulty__barthe!_000` it held the 2 s BMC probe to depth 6-7 of the 12 the
/// counterexample needs (11 once striped).
#[test]
fn sub_batch_live_byte_changes_stay_off_the_published_total() {
    let _serial = live_bytes_test_lock();
    let published_before = published_live_bytes();
    let exact_before = exact_live_bytes();
    let (to_main, from_worker) = std::sync::mpsc::channel::<()>();
    let (to_worker, from_main) = std::sync::mpsc::channel::<()>();
    let worker = std::thread::spawn(move || {
        add_live_bytes(1000);
        to_main.send(()).expect("main thread is waiting");
        from_main.recv().expect("main thread releases the worker");
        sub_live_bytes(1000);
    });
    from_worker.recv().expect("worker allocated");
    let published_during = published_live_bytes();
    let exact_during = exact_live_bytes();
    to_worker.send(()).expect("worker is waiting");
    worker.join().expect("worker thread");

    assert_eq!(
        published_during, published_before,
        "a sub-batch change must stay off the published total"
    );
    assert_eq!(exact_during, exact_before + 1000, "but it is counted");
    assert_eq!(exact_live_bytes(), exact_before);
}

/// Burst detection is kept: a change of two batches is published at once,
/// where every reader (and the hard ceiling) sees it, whatever its stripe was
/// holding.
#[test]
fn a_two_batch_live_byte_change_is_published_at_once() {
    let _serial = live_bytes_test_lock();
    let before = published_live_bytes();
    std::thread::spawn(|| add_live_bytes(2 * LIVE_BYTES_BATCH))
        .join()
        .expect("allocating thread");
    let after_growth = published_live_bytes();
    std::thread::spawn(|| sub_live_bytes(2 * LIVE_BYTES_BATCH))
        .join()
        .expect("freeing thread");
    let after_release = published_live_bytes();

    // A stripe holds under one batch either way, so publishing it with the
    // change moves the total by the change give or take less than one batch.
    let signed = |bytes: usize| isize::try_from(bytes).expect("test sizes fit");
    let two_batches = signed(2 * LIVE_BYTES_BATCH);
    let growth = signed(after_growth) - signed(before);
    let release = signed(after_release) - signed(after_growth);
    assert!(
        (growth - two_batches).unsigned_abs() < LIVE_BYTES_BATCH,
        "growth must be published at once: moved {growth}"
    );
    assert!(
        (release + two_batches).unsigned_abs() < LIVE_BYTES_BATCH,
        "release must be published at once: moved {release}"
    );
}

/// Threads that run at the same time write different stripes, which is the
/// whole of the fix for row 5 of `PERF_vs_winners_2026-09-25.md`: every
/// allocation on every thread writing one cache line. Two engine-sized
/// (8 MiB) stacks alive at once lie in different 1 MiB windows, and 256
/// stripes of those windows meet again only 256 MiB apart. The sizes are
/// written out rather than read from the constants, so that sending every
/// thread to one stripe, fewer stripes or wider windows fails here.
#[test]
fn threads_alive_at_once_write_different_stripes() {
    const ENGINE_STACK: usize = 8 << 20;
    const WINDOW: usize = 1 << 20;
    const STRIPES_APART: usize = 256 << 20;
    let both_alive = std::sync::Arc::new(std::sync::Barrier::new(2));
    let spawn = || {
        let both_alive = std::sync::Arc::clone(&both_alive);
        std::thread::Builder::new()
            .stack_size(ENGINE_STACK)
            .spawn(move || {
                let marker = 0_u8;
                let at = std::ptr::addr_of!(marker).addr();
                let stripe = caller_stripe_index_for_test();
                both_alive.wait();
                (at, stripe)
            })
            .expect("spawn a thread")
    };
    let (first, second) = (spawn(), spawn());
    let (first_at, first_stripe) = first.join().expect("first thread");
    let (second_at, second_stripe) = second.join().expect("second thread");

    let apart = first_at.abs_diff(second_at);
    assert!(
        apart >= WINDOW,
        "two live 8 MiB stacks are in different windows ({apart} bytes apart)"
    );
    // Only a stack a whole cycle of stripes away, give or take the one
    // window the two markers can straddle, may share a stripe.
    let off_cycle = apart % STRIPES_APART;
    let a_cycle_apart =
        apart >= STRIPES_APART - WINDOW && !(WINDOW..=STRIPES_APART - WINDOW).contains(&off_cycle);
    assert!(
        first_stripe != second_stripe || a_cycle_apart,
        "threads {apart} bytes apart share stripe {first_stripe}"
    );
}

/// A free is often published before the allocation it pairs with, whose
/// growth still waits on the allocating thread's stripe. The published total
/// must keep that debt. Clamping it at zero instead, as the unstriped counter
/// did, is two atomic steps with a total of about 2^64 between them (a false
/// hard-ceiling breach for any growth published in that gap), and it drops
/// the debt, so once the growth is published the count stays high for good.
#[test]
fn a_release_published_before_its_growth_keeps_the_count_exact() {
    let _serial = live_bytes_test_lock();
    let batch = isize::try_from(LIVE_BYTES_BATCH).expect("a batch fits");
    let bytes = |signed: isize| usize::try_from(signed).expect("a non-negative size");
    let exact_before = exact_live_bytes();
    // A release bigger than everything published, so that it takes the total
    // below zero, and of two batches or more, so that it is published at once.
    let published = isize::try_from(published_live_bytes()).expect("the test total fits");
    let release = published + 2 * batch;
    // Its growth waits in shares of under one batch on idle stripes.
    let share = batch - 1;
    let idle: Vec<usize> = (0..STRIPES)
        .filter(|&index| stripe_balance_for_test(index) == 0)
        .collect();
    let growth_stripes = bytes((release + share - 1) / share);
    assert!(idle.len() > growth_stripes, "enough idle stripes");
    let (growth_on, rest) = idle.split_at(growth_stripes);
    let release_on = rest[0];
    let mut unplaced = release;
    for &stripe in growth_on {
        let part = unplaced.min(share);
        add_to_stripe_for_test(stripe, part);
        unplaced -= part;
    }
    assert_eq!(unplaced, 0);
    assert_eq!(exact_live_bytes(), exact_before + bytes(release));

    add_to_stripe_for_test(release_on, -release);
    assert_eq!(
        stripe_balance_for_test(release_on),
        0,
        "the release is published at once"
    );
    assert_eq!(
        published_live_bytes(),
        0,
        "a total in debt reads as zero, never as a wrapped value"
    );
    assert_eq!(
        exact_live_bytes(),
        exact_before,
        "the growth and its release cancel exactly"
    );

    // Take the pair back out: the growth leaves its stripes unpublished, and
    // the release is repaid on its own stripe.
    for &stripe in growth_on {
        add_to_stripe_for_test(stripe, -stripe_balance_for_test(stripe));
    }
    add_to_stripe_for_test(release_on, release);
    assert_eq!(stripe_balance_for_test(release_on), 0);
    assert_eq!(exact_live_bytes(), exact_before);
    assert_eq!(published_live_bytes(), bytes(published));
}

/// Small changes accumulate on a stripe until its balance reaches a batch,
/// and then the whole balance is published, in either direction.
#[test]
fn a_stripe_publishes_its_balance_when_it_reaches_a_batch() {
    let _serial = live_bytes_test_lock();
    let stripe = (0..STRIPES)
        .find(|&index| stripe_balance_for_test(index) == 0)
        .expect("an idle stripe");
    let quarter = isize::try_from(LIVE_BYTES_BATCH / 4).expect("a quarter batch fits");
    let before = published_live_bytes();

    for _ in 0..3 {
        add_to_stripe_for_test(stripe, quarter);
    }
    assert_eq!(
        published_live_bytes(),
        before,
        "three quarters stay pending"
    );
    assert_eq!(stripe_balance_for_test(stripe), 3 * quarter);

    add_to_stripe_for_test(stripe, quarter);
    assert_eq!(
        published_live_bytes(),
        before + LIVE_BYTES_BATCH,
        "the fourth quarter publishes the whole batch"
    );
    assert_eq!(stripe_balance_for_test(stripe), 0);

    for _ in 0..4 {
        add_to_stripe_for_test(stripe, -quarter);
    }
    assert_eq!(
        published_live_bytes(),
        before,
        "releases publish the same way"
    );
    assert_eq!(stripe_balance_for_test(stripe), 0);
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
        statistics: None,
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

/// The breach settlement (2026-09-13). What the registered settlement decides
/// is what a breach does, with the armed exit status as its input, and only
/// the settling thread is exempt from the ceiling. A settlement that panics
/// falls back to the armed verdict instead of unwinding out of the allocator.
/// One test, because the settlement is process-wide.
#[test]
fn a_registered_settlement_decides_how_a_breach_leaves() {
    assert!(ceiling_settlement::SETTLEMENT
        .load(Ordering::SeqCst)
        .is_null());
    assert_eq!(
        ceiling_settlement::settle(3),
        CeilingSettlement::ArmedVerdict
    );

    static SEEN: AtomicUsize = AtomicUsize::new(usize::MAX);
    fn silent_one_past_the_armed_status(armed: i32) -> CeilingSettlement {
        SEEN.store(
            usize::try_from(armed).unwrap_or(usize::MAX),
            Ordering::SeqCst,
        );
        if !ceiling_settlement::settling_here() {
            return CeilingSettlement::ArmedVerdict;
        }
        CeilingSettlement::Silent(armed + 1)
    }
    set_hard_memory_ceiling_settlement(silent_one_past_the_armed_status);
    assert_eq!(ceiling_settlement::settle(3), CeilingSettlement::Silent(4));
    assert_eq!(SEEN.load(Ordering::SeqCst), 3);
    assert!(
        !std::thread::spawn(ceiling_settlement::settling_here)
            .join()
            .expect("probe thread"),
        "only the settling thread is exempt from the ceiling"
    );

    fn panics(_: i32) -> CeilingSettlement {
        panic!("a settlement that panics")
    }
    set_hard_memory_ceiling_settlement(panics);
    assert_eq!(
        ceiling_settlement::settle(3),
        CeilingSettlement::ArmedVerdict
    );

    ceiling_settlement::SETTLEMENT.store(std::ptr::null_mut(), Ordering::SeqCst);
    let _ = ceiling_settlement::SETTLING.try_with(|settling| settling.set(false));
}
