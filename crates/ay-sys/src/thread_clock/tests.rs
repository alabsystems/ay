// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::sync::mpsc;
use std::time::Duration;

/// Spin until THIS thread has been charged `work` of CPU. Measured on the
/// thread's own clock, so a descheduled interval extends the wall time of the
/// loop but never the amount of work it proves was done.
fn spin_for_cpu(work: Duration) {
    let start = crate::thread_cpu_time().expect("per-thread CPU clock on this platform");
    let mut acc = 0u64;
    while crate::thread_cpu_time()
        .expect("clock stays readable")
        .saturating_sub(start)
        < work
    {
        for _ in 0..1_000 {
            acc = std::hint::black_box(acc.wrapping_mul(6364136223846793005).wrapping_add(1));
        }
    }
}

fn platform_clock() -> Option<ThreadCpuClock> {
    let clock = ThreadCpuClock::current();
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    assert!(clock.is_some(), "this platform has a per-thread CPU clock");
    clock
}

#[test]
fn own_clock_agrees_with_the_calling_thread_cpu_time() {
    let Some(clock) = platform_clock() else {
        return;
    };
    let before = clock.elapsed().expect("readable");
    let own = crate::thread_cpu_time().expect("readable");
    let after = clock.elapsed().expect("readable");
    // Both readings are the same kernel accounting; allow the coarser
    // microsecond granularity of the Mach reply.
    let slack = Duration::from_millis(1);
    assert!(before <= own + slack, "{before:?} vs {own:?}");
    assert!(own <= after + slack, "{own:?} vs {after:?}");
    assert!(before <= after, "monotone: {before:?} -> {after:?}");
}

/// The reader measures the CAPTURED thread: its work is charged, while the
/// reader's own spinning and the captured thread's blocking are not.
#[test]
fn another_thread_reads_the_captured_threads_work_not_its_own() {
    if platform_clock().is_none() {
        return;
    }
    let (clock_tx, clock_rx) = mpsc::channel();
    let (go_tx, go_rx) = mpsc::channel::<()>();
    let (spun_tx, spun_rx) = mpsc::channel::<()>();
    let (done_tx, done_rx) = mpsc::channel::<()>();
    let worker = std::thread::spawn(move || {
        clock_tx
            .send(ThreadCpuClock::current().expect("captured"))
            .expect("reader alive");
        go_rx.recv().expect("reader alive");
        spin_for_cpu(Duration::from_millis(30));
        spun_tx.send(()).expect("reader alive");
        // Blocked, not running, until the reader has finished measuring.
        done_rx.recv().expect("reader alive");
    });
    let clock = clock_rx.recv().expect("worker sends its clock");
    let before = clock.elapsed().expect("worker alive");
    go_tx.send(()).expect("worker alive");
    spun_rx.recv().expect("worker spun");
    let after_spin = clock.elapsed().expect("worker alive");
    assert!(
        after_spin.saturating_sub(before) >= Duration::from_millis(29),
        "30 ms of the worker's CPU must be visible to the reader: {before:?} -> {after_spin:?}"
    );
    spin_for_cpu(Duration::from_millis(20));
    let after_reader_spin = clock.elapsed().expect("worker alive");
    assert!(
        after_reader_spin.saturating_sub(after_spin) < Duration::from_millis(10),
        "the reader's own work is not the worker's: {after_spin:?} -> {after_reader_spin:?}"
    );
    done_tx.send(()).expect("worker alive");
    worker.join().expect("worker exits cleanly");
}
