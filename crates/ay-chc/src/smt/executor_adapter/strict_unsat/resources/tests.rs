// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::{checked_certificate, parse_plain_query, solver_config};
use super::*;
use crate::smt::executor_adapter::replay_cancellation::ReplayCancellation;
use ay_core::time::Instant;
use ay_dpll::api::Solver;
use std::time::Duration;

const UNSAT: &str =
    "(set-logic QF_LIA) (declare-const x Int) (assert (> x 5)) (assert (< x 3)) (check-sat)";

#[test]
fn accounted_bytes_have_exact_cap_and_overflow_refusal_is_sticky() {
    let mut progress = ProofProgress::new(ReplayLimit::Legacy, ReplayMemory::capture(Some(13)));
    assert!(progress.charge(1, 6));
    assert!(progress.charge(1, 7));
    assert!(!progress.charge(0, 1));
    assert!(!progress.charge(0, 0));
    for byte_overflow in [false, true] {
        let mut progress = ProofProgress::new(ReplayLimit::Legacy, ReplayMemory::capture(None));
        if byte_overflow {
            progress.bytes = usize::MAX;
        } else {
            progress.work = usize::MAX;
        }
        assert!(!progress.charge(1, 1));
        assert!(!progress.charge(0, 0));
    }
}

#[test]
fn parent_reset_cannot_resume_a_cancelled_proof_progress_owner() {
    let parent = crate::CancellationToken::new();
    let cancellation = ReplayCancellation::new(&parent.child());
    let limit = ReplayLimit::Cancellable {
        deadline: Instant::now() + Duration::from_secs(30),
        cancellation: &cancellation,
    };
    let mut progress = ProofProgress::new(limit, ReplayMemory::capture(None));
    assert!(progress.charge(1, 1));
    parent.cancel();
    assert!(!progress.charge(1, 1));
    parent.reset();
    assert!(!progress.charge(0, 0));
    let fresh = ReplayCancellation::new(&parent.child());
    let mut progress = ProofProgress::new(
        ReplayLimit::Cancellable {
            deadline: Instant::now() + Duration::from_secs(30),
            cancellation: &fresh,
        },
        ReplayMemory::capture(None),
    );
    assert!(progress.charge(1, 1));
}

#[test]
fn ordered_assumptions_keep_duplicates_out_and_preprice_the_full_vector() {
    let source = [TermId(7), TermId(3), TermId(7), TermId(2), TermId(3)];
    let bytes = std::mem::size_of_val(&source);
    let mut progress = ProofProgress::new(ReplayLimit::Legacy, ReplayMemory::capture(Some(bytes)));
    assert_eq!(
        progress.ordered_unique(&source).unwrap(),
        [TermId(7), TermId(3), TermId(2)]
    );
    assert_eq!(progress.bytes, bytes);
    assert!(progress.equal_ids(&source, &source));
    assert!(!progress.equal_ids(&source, &source[..4]));
    assert!(progress.ordered_unique(&source).is_none());
    assert!(!progress.charge(0, 0));
    let mut too_small =
        ProofProgress::new(ReplayLimit::Legacy, ReplayMemory::capture(Some(bytes - 1)));
    assert!(too_small.ordered_unique(&source).is_none());
    assert!(!too_small.charge(0, 0));
}

fn measured_native_phases() -> (usize, usize) {
    let query = parse_plain_query(UNSAT, ReplayLimit::Legacy).unwrap();
    let mut solver = Solver::try_new_with_config(query.logic, solver_config(None)).unwrap();
    solver.set_produce_proofs(true);
    solver
        .try_set_option(":check-proofs-strict", "true")
        .unwrap();
    let binding = solver
        .parse_smtlib2_with_exact_query_binding(&query.body)
        .unwrap();
    assert!(solver.check_sat().is_unsat());
    let mut progress = ProofProgress::new(ReplayLimit::Legacy, ReplayMemory::capture(None));
    let bundle = solver
        .export_last_unsat_bundle_for_exact_query_with_resource_control(&binding, &mut |w, b| {
            progress.charge(w, b)
        })
        .unwrap()
        .unwrap();
    let after_export = progress.bytes;
    let certificate =
        checked_certificate(&solver, bundle, ReplayLimit::Legacy, &mut progress).unwrap();
    assert!(ay_dpll::api::re_check_bundle_strict(&certificate.bundle)
        .unwrap()
        .quality
        .is_complete());
    assert!(progress.bytes > after_export);
    (after_export, progress.bytes)
}

#[test]
fn actual_adapter_cannot_reset_its_allowance_between_export_and_consumer_replay() {
    let (export_bytes, total_bytes) = measured_native_phases();
    for (cap, accepted) in [
        (total_bytes, true),
        (total_bytes - 1, false),
        (export_bytes, false),
    ] {
        let _scope = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(cap));
        let result = super::super::smtlib_strict_unsat_cert_via_executor(UNSAT, None);
        assert_eq!(
            result.is_some(),
            accepted,
            "cumulative cap={cap}, total={total_bytes}"
        );
    }
}
