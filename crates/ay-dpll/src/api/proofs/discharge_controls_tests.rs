// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The per-clause discharge under its envelope: the controls a nested solve
//! inherits, the one counted pool every nested solve draws from (T-a), and
//! the latch that keeps the first stop.

use super::*;
use num_bigint::BigInt;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

fn controls_with(effort: CertificationEffort) -> TrustClauseDischargeControls {
    TrustClauseDischargeControls::new(None, None, None, None, effort)
}

fn expired_backstop() -> TrustClauseDischargeControls {
    let expired = ay_core::time::Instant::now()
        .checked_sub(Duration::from_millis(1))
        .expect("one millisecond must fit before the current instant");
    TrustClauseDischargeControls::new(None, Some(expired), None, None, Default::default())
}

fn term_ceiling(limit: usize) -> TrustClauseDischargeControls {
    TrustClauseDischargeControls::new(None, None, None, Some(limit), Default::default())
}

/// Four Int pigeons in three holes `1..=3`: some pair collides or one leaves
/// the range. A tautology no specialised checker models and no structural
/// lane recognises, whose refutation needs a search: only a counted nested
/// solve can discharge it.
fn int_pigeonhole_clause(terms: &mut ay_core::TermStore) -> Vec<ay_core::TermId> {
    let pigeons: Vec<_> = (0..4)
        .map(|i| terms.mk_var(format!("effort_pigeon_{i}"), ay_core::Sort::Int))
        .collect();
    let low = terms.mk_int(BigInt::from(1));
    let high = terms.mk_int(BigInt::from(3));
    let mut clause = Vec::new();
    for (i, &left) in pigeons.iter().enumerate() {
        for &right in &pigeons[i + 1..] {
            clause.push(terms.mk_eq(left, right));
        }
    }
    for &pigeon in &pigeons {
        clause.push(terms.mk_lt(pigeon, low));
        clause.push(terms.mk_gt(pigeon, high));
    }
    clause
}

#[test]
fn nested_executor_inherits_live_publication_controls() {
    let interrupt = Arc::new(AtomicBool::new(false));
    let backstop = ay_core::time::Instant::now() + Duration::from_secs(600);
    let controls = TrustClauseDischargeControls::new(
        Some(Arc::clone(&interrupt)),
        Some(backstop),
        Some(usize::MAX),
        Some(usize::MAX),
        CertificationEffort::with_allowance(4_000, None),
    );

    let mut executor = crate::Executor::new();
    assert_eq!(
        controls.install_on(&mut executor, EffortShare::Pool),
        Some(1_000),
        "a nested solve runs on what is left of the pool"
    );
    assert_eq!(
        executor.current_solve_deadline(),
        Some(backstop),
        "the backstop is the only deadline a nested solve gets"
    );
    assert_eq!(executor.memory_limit(), Some(usize::MAX));
    assert_eq!(executor.term_memory_limit(), Some(usize::MAX));
    assert_eq!(executor.resource_limit(), Some(1_000));

    let mut guard = crate::Executor::new();
    assert_eq!(
        controls.install_on(&mut guard, EffortShare::Guard),
        Some(500)
    );
    let mut reconfirm = crate::Executor::new();
    assert_eq!(
        controls.install_on(&mut reconfirm, EffortShare::Reconfirm),
        Some(4_000)
    );

    interrupt.store(true, Ordering::Relaxed);
    assert!(executor.solve_interrupt_is_set());
}

#[test]
fn controlled_discharge_rejects_expired_or_exhausted_envelopes() {
    let mut terms = ay_core::TermStore::new();
    let tautology = terms.true_term();
    let proposition = terms.mk_var("controlled_assertion_p", ay_core::Sort::Bool);
    let not_proposition = terms.mk_not_raw(proposition);
    let expired_controls = expired_backstop();
    assert!(
        discharge_trust_clause_with_controls(&terms, &[tautology], &[], &expired_controls)
            .is_none()
    );
    assert_eq!(
        expired_controls.observed_stop(),
        Some(EnvelopeStop::Backstop),
        "an expired backstop is a stop, never a verdict about the clause"
    );

    let exhausted_controls = term_ceiling(0);
    assert!(
        discharge_trust_clause_with_controls(&terms, &[tautology], &[], &exhausted_controls,)
            .is_none()
    );
    assert_eq!(
        exhausted_controls.observed_stop(),
        Some(EnvelopeStop::TermMemory)
    );

    let live_child_controls = term_ceiling(usize::MAX);
    assert_eq!(
        check_bv_clause_with_controls(&terms, &[tautology], &live_child_controls),
        BvStepVerdict::Valid
    );
    assert_eq!(
        check_array_clause_with_controls(&terms, &[tautology], &live_child_controls),
        ArrayStepVerdict::Valid
    );
    assert_eq!(
        check_bv_assertions_unsat_with_controls(
            &terms,
            &[proposition, not_proposition],
            &live_child_controls,
            EffortShare::Pool,
        ),
        BvStepVerdict::Valid
    );

    // Directly exercise each fresh specialized Solver under a ceiling far
    // below its non-empty baseline store. This isolates child propagation
    // from the later structural replay lanes in the full discharge funnel.
    for checker in 0..3 {
        let child_exhausted_controls = term_ceiling(1);
        let reason = match checker {
            0 => {
                match check_bv_clause_with_controls(&terms, &[tautology], &child_exhausted_controls)
                {
                    BvStepVerdict::Unchecked { reason } => reason,
                    other => panic!("tiny child term limit must decline the BV checker: {other:?}"),
                }
            }
            1 => match check_array_clause_with_controls(
                &terms,
                &[tautology],
                &child_exhausted_controls,
            ) {
                ArrayStepVerdict::Unchecked { reason } => reason,
                other => panic!("tiny child term limit must decline the array checker: {other:?}"),
            },
            _ => match check_bv_assertions_unsat_with_controls(
                &terms,
                &[proposition, not_proposition],
                &child_exhausted_controls,
                EffortShare::Reconfirm,
            ) {
                BvStepVerdict::Unchecked { reason } => reason,
                other => {
                    panic!("tiny child term limit must decline the assertion checker: {other:?}")
                }
            },
        };
        assert!(reason.contains("resource envelope"), "{reason}");
        assert_eq!(
            child_exhausted_controls.observed_stop(),
            Some(EnvelopeStop::TermMemory)
        );
    }
}

#[test]
fn clone_preflight_uses_an_exact_term_store_census() {
    let mut terms = ay_core::TermStore::new();
    let baseline = terms.true_memory_bytes();
    assert!(!terms.instance_memory_exceeded(baseline));
    for index in 0..512 {
        let _ = terms.mk_var(
            format!("clone_preflight_exact_census_{index}"),
            ay_core::Sort::Bool,
        );
        if terms.true_memory_bytes() > baseline {
            break;
        }
    }
    let growth = terms.true_memory_bytes().saturating_sub(baseline);
    assert!(growth > 0, "fixture must grow the source term store");
    assert!(
        growth < 64 * 1024,
        "fixture must remain inside the hot-path cache window"
    );
    assert!(
        !terms.instance_memory_exceeded(baseline),
        "cached hot-path census must still be stale for this regression"
    );

    let controls = term_ceiling(baseline);
    assert!(!controls.clone_fits(&terms));
    assert_eq!(controls.observed_stop(), Some(EnvelopeStop::TermMemory));
}

/// T-a. The clause needs a search, so a pool of ONE conflict cannot discharge
/// it and the decline names the spent count; the full allowance does.
#[test]
fn a_clause_beyond_its_pool_declines_as_effort_exhausted_and_fits_the_allowance() {
    let mut terms = ay_core::TermStore::new();
    let clause = int_pigeonhole_clause(&mut terms);

    let full = controls_with(CertificationEffort::default());
    assert!(
        discharge_trust_clause_with_controls(&terms, &clause, &[], &full).is_some(),
        "the full allowance discharges the tautology"
    );
    assert!(full.effort.spent() > 1, "the refutation needs a search");
    assert_eq!(full.observed_stop(), None);

    let starved = controls_with(CertificationEffort::with_allowance(
        POOL_SHARE_FOR_TESTS,
        None,
    ));
    assert!(discharge_trust_clause_with_controls(&terms, &clause, &[], &starved).is_none());
    let exhausted = starved
        .effort
        .exhaustion()
        .expect("the decline is the spent pool");
    assert!(
        exhausted.starts_with("certification effort exhausted (spent "),
        "{exhausted}"
    );
    assert!(exhausted.ends_with(" of 1)"), "{exhausted}");
    assert_eq!(
        starved.decline_stop(),
        None,
        "a spent pool is a count, not a stop"
    );
}

/// T-a. The count is a function of the clause alone: two discharges spend
/// exactly the same.
#[test]
fn two_discharges_of_one_clause_spend_identically() {
    let mut terms = ay_core::TermStore::new();
    let clause = int_pigeonhole_clause(&mut terms);
    let spend = || {
        let controls = controls_with(CertificationEffort::default());
        let accepted = discharge_trust_clause_with_controls(&terms, &clause, &[], &controls);
        (accepted.is_some(), controls.effort.spent())
    };
    let first = spend();
    assert!(first.0);
    assert_eq!(first, spend());
}

/// The latch: the first stop a poll sees is kept after the signal clears,
/// so a stop that lapses can never read as a decline on evidence.
#[test]
fn the_first_stop_is_latched_after_its_signal_clears() {
    let terms = ay_core::TermStore::new();
    let controls = controls_with(CertificationEffort::default());
    assert!(!controls.stop_requested(&terms));
    ay_sys::force_process_memory_exceeded_for_testing(true);
    let stopped = controls.stop_requested(&terms);
    ay_sys::force_process_memory_exceeded_for_testing(false);
    assert!(stopped);
    assert!(controls.stop_requested(&terms), "the stop stays latched");
    assert_eq!(controls.observed_stop(), Some(EnvelopeStop::ProcessMemory));
    controls.latch(EnvelopeStop::Interrupt);
    assert_eq!(
        controls.observed_stop(),
        Some(EnvelopeStop::ProcessMemory),
        "the first stop wins"
    );
}

/// A lane-local clock is not the backstop: it ends that lane only, and turns
/// the funnel's DECLINE into a stop.
#[test]
fn a_lane_local_deadline_is_a_decline_stop_but_not_a_latch() {
    let terms = ay_core::TermStore::new();
    let controls = controls_with(CertificationEffort::default());
    controls.latch_nested(Some(crate::UnknownOrigin::SolveDeadline), false);
    assert_eq!(controls.observed_stop(), None);
    assert!(!controls.stop_requested(&terms), "later lanes still run");
    assert_eq!(controls.decline_stop(), Some(EnvelopeStop::Backstop));

    let at_backstop = expired_backstop();
    at_backstop.latch_nested(Some(crate::UnknownOrigin::SolveDeadline), false);
    assert_eq!(at_backstop.observed_stop(), Some(EnvelopeStop::Backstop));
    at_backstop.latch_nested(
        Some(crate::UnknownOrigin::DeterministicResourceBudget),
        false,
    );
    assert_eq!(at_backstop.observed_stop(), Some(EnvelopeStop::Backstop));
}

/// DR-39: a nested certification check is a `Full` child of the
/// certification's node, so its theory loops also stop for the cancels that
/// reach that node from above. The envelope reads them too, and keeps each as
/// the stop it was: never a plain decline, so never a rejection.
#[test]
fn a_cancel_above_the_certification_is_a_stop_never_a_decline() {
    use ay_core::resource::{ChildSpec, Guard, MemoryShare, NodeLabel};
    const MIB: usize = 1 << 20;
    let terms = ay_core::TermStore::new();
    let built_in = |node: &Guard| {
        let _in_node = node.enter();
        TrustClauseDischargeControls::new(
            Some(Arc::new(AtomicBool::new(false))),
            None,
            None,
            None,
            CertificationEffort::default(),
        )
    };

    // The interrupt of a check around it, which is not the envelope's own.
    let outer = Arc::new(AtomicBool::new(false));
    let check =
        Guard::root_child(ChildSpec::new(NodeLabel::Check).with_external(Arc::clone(&outer)));
    let controls = built_in(&check);
    assert!(!controls.stop_requested(&terms));
    outer.store(true, Ordering::Relaxed);
    assert!(
        controls.stop_requested(&terms),
        "the enclosing check's interrupt"
    );
    outer.store(false, Ordering::Relaxed);
    assert_eq!(
        controls.decline_stop(),
        Some(EnvelopeStop::Interrupt),
        "latched as an interrupt"
    );

    // A nested solve's plain decline while a node above it is cancelled.
    let probe = Guard::root_child(ChildSpec::new(NodeLabel::Check));
    let controls = built_in(&probe);
    controls.latch_nested(None, false);
    assert_eq!(controls.observed_stop(), None, "no cancel up: a decline");
    probe.cancel();
    controls.latch_nested(Some(crate::UnknownOrigin::IncompleteSolverLane), false);
    assert_eq!(controls.observed_stop(), Some(EnvelopeStop::Interrupt));

    // The trip of a memory share above it, read off the thread of the share.
    let shared = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_memory(MemoryShare {
        soft_bytes: MIB,
        hard_bytes: 64 * MIB,
    }));
    let controls = built_in(&shared);
    assert!(!controls.stop_requested(&terms));
    {
        let _in_share = shared.enter();
        ay_sys::charge_current_for_testing(2 * MIB);
    }
    assert!(controls.stop_requested(&terms), "through the node");
    assert_eq!(controls.observed_stop(), Some(EnvelopeStop::LaneShare));
}

const POOL_SHARE_FOR_TESTS: u64 = certification_effort::POOL_SHARE;
