// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::executor_adapter::new_search_executor;

/// The library posture with no CLI flags installed: proof-carrying.
fn certified_flags() -> ay_core::misc_test_override::Guard {
    ay_core::misc_test_override::set(ay_core::MiscCliFlags::default())
}

/// The scope switches the posture on and back off, and nested guards keep it
/// switched on until the outermost one drops.
#[test]
fn search_executors_shed_the_proof_cycle_only_inside_a_verdict_only_search() {
    let _flags = certified_flags();
    assert!(
        !new_search_executor().competition_mode(),
        "outside any guard a search executor stays proof-carrying"
    );
    let outer = ScopedVerdictOnlySearch::install();
    assert!(new_search_executor().competition_mode());
    let inner = ScopedVerdictOnlySearch::install();
    drop(inner);
    assert!(
        new_search_executor().competition_mode(),
        "an inner guard's drop must not end the outer scope"
    );
    drop(outer);
    assert!(!verdict_only_search_active());
    assert!(
        !new_search_executor().competition_mode(),
        "the posture must not outlive the scope"
    );
}

/// The guard is per thread: a search running on another thread, under no
/// guard of its own, keeps the proof-carrying posture.
#[test]
fn a_verdict_only_search_does_not_reach_other_threads() {
    let _flags = certified_flags();
    let _guard = ScopedVerdictOnlySearch::install();
    let elsewhere = std::thread::spawn(|| {
        let _flags = certified_flags();
        new_search_executor().competition_mode()
    })
    .join()
    .expect("the probe thread does not panic");
    assert!(
        !elsewhere,
        "another thread inherited the verdict-only scope"
    );
    assert!(new_search_executor().competition_mode());
}

/// The raw SMT-LIB script channels, whose `unsat` can be a published claim,
/// take the process posture alone: a verdict-only scope does not reach them.
#[test]
fn the_script_channels_ignore_a_verdict_only_search() {
    let _flags = certified_flags();
    let _guard = ScopedVerdictOnlySearch::install();
    assert!(
        !super::super::new_script_executor().competition_mode(),
        "the script executor stays proof-carrying under a verdict-only scope"
    );
    let built_before = shed_search_executors_built();
    let verdict = super::super::smtlib_first_verdict_via_executor_until(
        "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x x))\n(check-sat)\n",
        ay_core::time::Instant::now() + std::time::Duration::from_mins(1),
        None,
    );
    assert_eq!(verdict.as_deref(), Some("unsat"));
    assert_eq!(
        shed_search_executors_built(),
        built_before,
        "the script channel built its executor outside the verdict-only scope"
    );
}
