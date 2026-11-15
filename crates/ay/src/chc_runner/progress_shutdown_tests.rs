// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn reporter() -> ProgressHandle {
    spawn_chc_progress_thread_rich(
        Instant::now(),
        Arc::new(ay::chc::ChcProgressSnapshot::new(0)),
    )
}

#[test]
#[ntest::timeout(2_000)]
fn stop_before_first_report_joins_without_waiting_for_the_reporting_interval() {
    let handle = reporter();
    assert!(handle.handle.is_some(), "the real reporting worker starts");
    handle.stop();
    drop(handle);
}

#[test]
#[ntest::timeout(2_000)]
fn dropping_an_active_reporter_wakes_and_joins_its_worker() {
    let handle = reporter();
    assert!(handle.handle.is_some(), "the real reporting worker starts");
    std::thread::sleep(Duration::from_millis(20));
    drop(handle);
}
