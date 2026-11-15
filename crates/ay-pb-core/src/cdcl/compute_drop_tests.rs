// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{drop_on_owned_unit, drop_with_spare_computation};
use ay_sys::compute_budget::ComputeScope;
use std::sync::mpsc;

struct ObservedDrop {
    entered: mpsc::Sender<std::thread::ThreadId>,
    release: Option<mpsc::Receiver<()>>,
    finished: mpsc::Sender<()>,
}

impl Drop for ObservedDrop {
    fn drop(&mut self) {
        self.entered
            .send(std::thread::current().id())
            .expect("drop entered");
        if let Some(release) = self.release.take() {
            release.recv().expect("drop released");
        }
        self.finished.send(()).expect("drop finished");
    }
}

#[test]
fn unavailable_capacity_keeps_destructor_on_the_original_computation() {
    if !ay_test_support::isolated_test::run_alone(
        module_path!(),
        "unavailable_capacity_keeps_destructor_on_the_original_computation",
    )
    .expect("isolated resource case")
    {
        return;
    }
    let compute = ComputeScope::enter().expect("caller");
    let mut retained = Vec::new();
    while let Some(unit) = compute.try_extra().expect("probe") {
        retained.push(unit);
    }
    let (entered_tx, entered_rx) = mpsc::channel();
    let (finished_tx, finished_rx) = mpsc::channel();
    drop_with_spare_computation(ObservedDrop {
        entered: entered_tx,
        release: None,
        finished: finished_tx,
    });
    assert_eq!(
        entered_rx.recv().expect("destructor ran"),
        std::thread::current().id()
    );
    finished_rx
        .try_recv()
        .expect("destruction completed before returning");
}

#[test]
fn deferred_destructor_retains_its_actual_unit_until_cleanup_finishes() {
    if !ay_test_support::isolated_test::run_alone(
        module_path!(),
        "deferred_destructor_retains_its_actual_unit_until_cleanup_finishes",
    )
    .expect("isolated resource case")
    {
        return;
    }
    let compute = ComputeScope::enter().expect("caller");
    let spare = compute
        .try_extra()
        .expect("probe")
        .expect("native spare capacity");
    let mut retained = Vec::new();
    while let Some(unit) = compute.try_extra().expect("probe") {
        retained.push(unit);
    }
    let (entered_tx, entered_rx) = mpsc::channel();
    let (release_tx, release_rx) = mpsc::channel();
    let (finished_tx, finished_rx) = mpsc::channel();
    drop_on_owned_unit(
        ObservedDrop {
            entered: entered_tx,
            release: Some(release_rx),
            finished: finished_tx,
        },
        spare,
    );
    assert_ne!(
        entered_rx.recv().expect("actual background destructor"),
        std::thread::current().id()
    );
    assert!(
        compute.try_extra().expect("probe").is_none(),
        "destruction still owns the only spare"
    );
    release_tx.send(()).expect("allow destruction");
    finished_rx.recv().expect("destructor completed");
    // The closure returns its unit after the destructor's final statement.
    // Retained units are original owned values, never a reset global counter.
    drop(retained);
}
