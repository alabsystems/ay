// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Public consumer checks for current-thread memory-read attribution.

use ay_dpll::api::{Logic, Solver, Sort};
use ay_sys::memory_observations::Snapshot;

#[test]
fn independent_snapshots_keep_nested_observations_without_draining() {
    let before = Snapshot::capture();
    let _ = ay_sys::current_footprint_bytes();
    let middle = Snapshot::capture();
    let _ = ay_sys::current_footprint_bytes();
    let _ = ay_sys::current_footprint_bytes();
    let after = Snapshot::capture();

    let first = middle.since(&before);
    let second = after.since(&middle);
    let whole = after.since(&before);
    assert_eq!(first.attempts, 1);
    assert_eq!(second.attempts, 2);
    assert_eq!(whole.attempts, 3);
    assert_eq!(whole.elapsed, first.elapsed + second.elapsed);
    assert_eq!(after.since(&before).attempts, 3);
    let unchanged = Snapshot::capture().since(&after);
    assert_eq!(unchanged.attempts, 0);
    assert_eq!(unchanged.elapsed, std::time::Duration::ZERO);
}

#[test]
fn concurrent_threads_do_not_change_the_callers_observations() {
    let before = Snapshot::capture();
    let child = std::thread::spawn(|| {
        let before = Snapshot::capture();
        let _ = ay_sys::current_footprint_bytes();
        let _ = ay_sys::current_footprint_bytes();
        Snapshot::capture().since(&before)
    })
    .join()
    .expect("memory-read worker");
    assert_eq!(child.attempts, 2);
    let parent = Snapshot::capture().since(&before);
    assert_eq!(parent.attempts, 0);
    assert_eq!(parent.elapsed, std::time::Duration::ZERO);
}

#[test]
fn measured_native_checks_keep_strict_unsat_and_restored_sat() {
    let mut solver = Solver::try_new(Logic::All).expect("native solver");
    solver.set_produce_proofs(true);
    solver.set_produce_unsat_cores(true);
    solver.set_timeout(Some(std::time::Duration::from_millis(120_000)));
    solver.set_quantifier_deadline_backstop(false);
    solver
        .try_set_option("rlimit", "400000")
        .expect("Core conflict bound");
    let requested = 512_usize.saturating_mul(1024 * 1024);
    let memory = requested
        .max(ay_sys::default_memory_limit())
        .max(ay_sys::current_rss_bytes().saturating_add(requested));
    solver.set_memory_limit((memory > 0).then_some(memory));

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let nonnegative = solver.try_le(zero, x).expect("0 <= x");
    solver
        .try_assert_named(nonnegative, "nonnegative")
        .expect("authored premise");
    solver.try_push().expect("target scope");
    let negative = solver.try_lt(x, zero).expect("x < 0");
    solver.try_assert_term(negative).expect("negative target");

    let before = Snapshot::capture();
    let unsat = solver.check_sat_with_details();
    let measured = Snapshot::capture().since(&before);
    assert!(
        measured.attempts > 0,
        "finite native memory envelope was read"
    );
    assert!(unsat.result.is_unsat(), "{unsat:?}");
    assert!(unsat.result.was_unsat_strictly_verified(), "{unsat:?}");
    assert!(unsat
        .accept_for_consumer()
        .expect("checked contradiction")
        .is_unsat());
    assert!(solver
        .last_strict_proof_quality()
        .expect("current proof")
        .expect("strictly valid authored proof")
        .is_complete());

    solver.try_pop().expect("restore authored premise");
    let restored = solver.check_sat_with_details();
    assert!(restored.result.is_sat(), "{restored:?}");
    assert!(restored
        .accept_for_consumer()
        .expect("validated restored model")
        .is_sat());
    assert!(solver.last_strict_proof_quality().is_none());
}
