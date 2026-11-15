// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{
    keep_proof_inprocessing_after_exhaustion, proof_inprocessing_kept_after_exhaustion, Solver,
    KEEP_PROOF_INPROCESSING_DEPTH,
};

#[test]
fn ordinary_scopes_can_drop_in_either_order_without_losing_the_live_scope() {
    assert!(!proof_inprocessing_kept_after_exhaustion());
    let first = keep_proof_inprocessing_after_exhaustion();
    let second = keep_proof_inprocessing_after_exhaustion();
    drop(first);
    assert!(proof_inprocessing_kept_after_exhaustion());
    drop(second);
    assert!(!proof_inprocessing_kept_after_exhaustion());
}

#[test]
fn nesting_overflow_cannot_release_a_still_live_proof_clamp() {
    // Seed the representable boundary directly, instead of opening 2^32
    // guards. A dedicated thread keeps this deliberately sticky state local.
    std::thread::spawn(|| {
        KEEP_PROOF_INPROCESSING_DEPTH.with(|depth| depth.set(Some(u32::MAX)));
        let overflow = keep_proof_inprocessing_after_exhaustion();
        assert_eq!(
            KEEP_PROOF_INPROCESSING_DEPTH.with(|depth| depth.get()),
            None
        );
        drop(overflow);
        assert_eq!(
            KEEP_PROOF_INPROCESSING_DEPTH.with(|depth| depth.get()),
            None
        );
        drop(keep_proof_inprocessing_after_exhaustion());
        assert!(proof_inprocessing_kept_after_exhaustion());

        let mut solver = Solver::new(2);
        solver.enable_clause_trace();
        solver.set_proof_bookkeeping_budget(Some(0));
        assert!(solver.keeps_proof_inprocessing_after_exhaustion());
        if let Some(trace) = solver.cold.clause_trace.as_mut() {
            trace.mark_proof_work_exhausted();
        }
        solver.degrade_proof_bookkeeping_after_exhaustion();
        assert!(!solver.cold.lrat_enabled);
        let controls = &solver.inproc_ctrl;
        assert!(!controls.bve.enabled);
        assert!(!controls.decompose.enabled);
        assert!(!controls.factor.enabled);
        assert!(!controls.sbva.enabled);
        assert!(!controls.congruence.enabled);
        assert!(!controls.sweep.enabled);
    })
    .join()
    .expect("overflow fixture thread completes");
    assert!(!proof_inprocessing_kept_after_exhaustion());
}

#[test]
fn the_largest_representable_depth_does_not_overflow_early() {
    std::thread::spawn(|| {
        KEEP_PROOF_INPROCESSING_DEPTH.with(|depth| depth.set(Some(u32::MAX - 1)));
        let last = keep_proof_inprocessing_after_exhaustion();
        assert_eq!(
            KEEP_PROOF_INPROCESSING_DEPTH.with(|depth| depth.get()),
            Some(u32::MAX)
        );
        drop(last);
        assert_eq!(
            KEEP_PROOF_INPROCESSING_DEPTH.with(|depth| depth.get()),
            Some(u32::MAX - 1)
        );
    })
    .join()
    .expect("exact-boundary fixture thread completes");
    assert!(!proof_inprocessing_kept_after_exhaustion());
}
