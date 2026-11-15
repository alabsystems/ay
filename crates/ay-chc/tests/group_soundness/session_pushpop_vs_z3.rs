// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! `HornSmt` session differential locks vs z3 (CHC-COMP 2026 Rung 1, design
//! §8 / §7.3 (i); WP-4). The z3-mandatory registration of the in-crate
//! `session/tests/{pushpop_fuzz,diff_lra}.rs`: a missing z3 is a FAILURE
//! here, not a skip. The z3 is the workspace's one oracle (`Z3_PATH`, else the
//! first z3 on `PATH` that proves it is z3, reached by path past reroute
//! stubs); each report names it. Seeded, fixed sample sizes.

use ay_chc::testing::session_harness::{run_diff_lra, run_pushpop_fuzz};
use ay_test_support::z3::require_z3;

#[test]
fn session_pushpop_scripts_agree_with_z3() {
    require_z3("ay-chc session_pushpop_vs_z3");
    let n = 500;
    let report = run_pushpop_fuzz(2026, n, true);
    eprintln!("[session_pushpop_vs_z3] {}", report.summary());
    for d in report.disagreements.iter().take(3) {
        eprintln!("[session_pushpop_vs_z3] DISAGREEMENT {d}");
    }
    assert!(report.z3_available);
    assert!(
        report.errors.is_empty(),
        "harness errors: {:?}",
        report.errors
    );
    assert!(
        report.disagreements.is_empty(),
        "{} disagreements; first: {}",
        report.disagreements.len(),
        report.disagreements[0]
    );
    assert_eq!(report.real_false_unsat, 0);
}

#[test]
fn session_random_lra_conjunctions_agree_with_z3() {
    require_z3("ay-chc session_diff_lra_vs_z3");
    let n = 1_200;
    let report = run_diff_lra(2026, n, true);
    eprintln!("[session_diff_lra_vs_z3] {}", report.summary());
    for d in report.disagreements.iter().take(3) {
        eprintln!("[session_diff_lra_vs_z3] DISAGREEMENT {d}");
    }
    assert!(report.z3_available);
    assert!(
        report.errors.is_empty(),
        "harness errors: {:?}",
        report.errors
    );
    assert!(
        report.disagreements.is_empty(),
        "{} disagreements; first: {}",
        report.disagreements.len(),
        report.disagreements[0]
    );
    assert_eq!(report.real_false_unsat, 0);
}
