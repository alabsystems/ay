// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::fmt::Write;
use std::sync::Mutex;
use std::time::Duration;

static OBSERVED: Mutex<Option<Vec<std::thread::ThreadId>>> = Mutex::new(None);

pub(super) fn observe_worker() {
    if let Some(observed) = OBSERVED.lock().expect("observations").as_mut() {
        observed.push(std::thread::current().id());
    }
}

fn forced_zero_instance() -> PbInstance {
    let mut text = String::from("* #variable= 18 #constraint= 95\n");
    for block in 0..8 {
        writeln!(text, "+1 x{} +1 x{} = 1 ;", 2 * block + 1, 2 * block + 2).expect("format");
    }
    for first in 0..8 {
        for second in first + 1..8 {
            for (a, b) in [(0, 1), (1, 0), (1, 1)] {
                writeln!(
                    text,
                    "-1 x{} -1 x{} >= -1 ;",
                    2 * first + 1 + a,
                    2 * second + 1 + b
                )
                .expect("format");
            }
        }
    }
    text.push_str("+1 x1 +1 x3 -2 x17 >= 0 ;\n+1 x2 +1 x4 -2 x18 >= 0 ;\n+1 x17 +1 x18 >= 1 ;\n");
    crate::parse_opb(&text).expect("bounded FRB fixture")
}

#[test]
fn nested_clique_search_finishes_with_all_original_spares_retained() {
    if !ay_test_support::isolated_test::run_alone(
        module_path!(),
        "nested_clique_search_finishes_with_all_original_spares_retained",
    )
    .expect("fresh process")
    {
        return;
    }
    let compute = ay_sys::compute_budget::ComputeScope::enter().expect("caller");
    // Ownership, not inspection, exhausts the spare compute units through this scope.
    #[expect(
        clippy::collection_is_never_read,
        reason = "the owned compute units intentionally exhaust spare capacity until scope exit"
    )]
    let mut _retained_units = Vec::new();
    while let Some(unit) = compute.try_extra().expect("probe") {
        _retained_units.push(unit);
    }
    let instance = forced_zero_instance();
    assert!(clique_arm_matches(&instance));
    *OBSERVED.lock().expect("observations") = Some(Vec::new());
    let caller = std::thread::current().id();
    let answer = try_clique_witness(
        &instance,
        Some(Instant::now() + Duration::from_secs(2)),
        &AtomicBool::new(false),
        1,
    )
    .expect("inline original computational unit finds the known clique");
    let observed = OBSERVED
        .lock()
        .expect("observations")
        .take()
        .expect("active observer");
    assert!(!observed.is_empty(), "actual search did not run");
    assert!(
        observed.iter().all(|thread| *thread == caller),
        "search ran outside the sole available caller unit: {observed:?}"
    );
    assert!(verify_all_constraints(&instance.constraints, &answer));
    for block in 0..8 {
        assert!(answer[2 * block]);
        assert!(!answer[2 * block + 1]);
    }
    assert!(answer[16]);
    assert!(!answer[17]);
}

#[test]
fn original_cancellation_declines_before_clique_preparation() {
    assert!(try_clique_witness(&forced_zero_instance(), None, &AtomicBool::new(true), 1).is_none());
}
