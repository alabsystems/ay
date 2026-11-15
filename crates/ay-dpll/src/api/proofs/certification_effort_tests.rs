// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! T-a, the account itself: shares of the one count, the pool's draws and
//! debits, its exhaustion, and the arming of a nested executor.

use super::*;

#[test]
fn the_shares_divide_the_outer_queries_own_allowance() {
    let mut outer = Executor::new();
    let ground = Executor::DEFAULT_GROUND_CONFLICT_ALLOWANCE;
    let effort = CertificationEffort::for_query(&outer);
    assert_eq!(
        effort.reconfirm_grant(),
        ground,
        "no :rlimit: the ground allowance"
    );
    assert_eq!(effort.guard_grant(), ground / GUARD_SHARE);
    assert_eq!(effort.draw(), Some(ground / POOL_SHARE));

    outer.set_resource_limit(Some(8_000));
    let effort = CertificationEffort::for_query(&outer);
    assert_eq!(
        effort.reconfirm_grant(),
        8_000,
        "an :rlimit is the allowance"
    );
    assert_eq!(effort.guard_grant(), 1_000);
    assert_eq!(effort.draw(), Some(2_000));

    outer.set_resource_limit(Some(ground * 10));
    let effort = CertificationEffort::for_query(&outer);
    assert_eq!(
        effort.reconfirm_grant(),
        ground,
        "the tighter of the :rlimit and the ground allowance, as step (4) always took"
    );

    let starved = CertificationEffort::with_allowance(3, None);
    assert_eq!(
        starved.guard_grant(),
        1,
        "the guard always gets one conflict"
    );
}

/// The account reads the first solve from the outer query's check (step
/// (4a)'s yardstick), and no share's round-trip grant moves with it: the
/// guard's and the lanes' stay fixed and step (4)'s re-solve has none.
#[test]
fn the_account_reads_the_first_solve_and_the_share_grants_stay_fixed() {
    assert_eq!(
        CertificationEffort::default().first_solve(),
        FirstSolveWork::default()
    );
    let mut outer = Executor::new();
    let script = "(set-logic QF_LIA)
         (declare-const x Int)
         (declare-const y Int)
         (assert (< x y))
         (assert (< y x))
         (check-sat)";
    outer
        .execute_all(&ay_frontend::parse(script).expect("parse"))
        .expect("execute");
    let first_solve = CertificationEffort::for_query(&outer).first_solve();
    assert_eq!(first_solve, FirstSolveWork::of(&outer));
    assert_ne!(
        first_solve,
        FirstSolveWork::default(),
        "the query's check recorded its work"
    );
    assert_eq!(EffortShare::Guard.round_trips(), Some(GUARD_ROUND_TRIPS));
    assert_eq!(EffortShare::Pool.round_trips(), Some(LANE_ROUND_TRIPS));
    assert_eq!(
        EffortShare::Reconfirm.round_trips(),
        None,
        "step (4)'s re-solve has no round-trip grant"
    );
}

#[test]
fn the_decision_cap_follows_the_grant_and_never_widens_the_outer_cap() {
    let effort = CertificationEffort::with_allowance(400, None);
    assert_eq!(effort.decision_grant(100), 100 * DECISIONS_PER_CONFLICT);
    assert_eq!(DECISIONS_PER_CONFLICT, 60);
    let capped = CertificationEffort::with_allowance(400, Some(1_000));
    assert_eq!(capped.decision_grant(100), 1_000);
    assert_eq!(capped.decision_grant(u64::MAX), 1_000);
}

#[test]
fn the_pool_is_drawn_in_order_and_declines_once_spent() {
    let effort = CertificationEffort::with_allowance(40, None);
    assert_eq!(effort.draw(), Some(10));
    effort.debit(4);
    assert_eq!(effort.draw(), Some(6), "a draw is what is left");
    assert_eq!(effort.exhaustion(), None);
    effort.debit(9);
    assert_eq!(effort.spent(), 13, "an overshoot is charged in full");
    assert_eq!(effort.draw(), None);
    let exhausted = effort.exhaustion().expect("an empty draw is remembered");
    assert_eq!(exhausted, "certification effort exhausted (spent 13 of 10)");
}

#[test]
fn arming_installs_the_grant_and_switches_off_the_ground_default() {
    let effort = CertificationEffort::with_allowance(4_000, None);
    let interrupt = Arc::new(AtomicBool::new(false));
    let backstop = Instant::now() + std::time::Duration::from_secs(600);
    let mut nested = Executor::new();
    let certify = certify_node(
        Some(Arc::clone(&interrupt)),
        DeadlineSource::Fixed(backstop),
    );
    effort.arm(
        &mut nested,
        250,
        Some(backstop),
        Some(Arc::clone(&interrupt)),
        Some(certify),
    );
    assert_eq!(nested.resource_limit(), Some(250));
    assert_eq!(nested.decision_limit(), Some(250 * DECISIONS_PER_CONFLICT));
    assert!(!nested.ground_budget_enabled());
    assert_eq!(nested.current_solve_deadline(), Some(backstop));
    interrupt.store(true, std::sync::atomic::Ordering::Relaxed);
    assert!(nested.solve_interrupt_is_set());
}

#[test]
fn a_nested_unknown_names_its_stop_only_for_envelope_origins() {
    assert_eq!(
        EnvelopeStop::of_nested_origin(Some(UnknownOrigin::InterruptFlag), false),
        Some(NestedStop::Envelope(EnvelopeStop::Interrupt))
    );
    assert_eq!(
        EnvelopeStop::of_nested_origin(Some(UnknownOrigin::SolveDeadline), false),
        Some(NestedStop::Deadline)
    );
    assert_eq!(
        EnvelopeStop::of_nested_origin(Some(UnknownOrigin::MemoryBudget), true),
        Some(NestedStop::Envelope(EnvelopeStop::TermMemory))
    );
    for plain_decline in [
        UnknownOrigin::DeterministicResourceBudget,
        UnknownOrigin::VerdictCertification,
        UnknownOrigin::IncompleteSolverLane,
    ] {
        assert_eq!(
            EnvelopeStop::of_nested_origin(Some(plain_decline), false),
            None,
            "{plain_decline:?} is a decline, not a stop"
        );
    }
    assert_eq!(EnvelopeStop::of_nested_origin(None, false), None);
}

#[test]
fn certify_is_cancel_only_and_sized_from_the_checks_budget_alone() {
    use ay_core::resource::Inherit;
    let check = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(800)));
    let certify = {
        let _in_check = check.enter();
        certify_node(None, DeadlineSource::None)
    };
    assert_eq!(certify.label(), NodeLabel::Certify);
    assert_eq!(certify.inherit(), Inherit::CancelOnly);
    assert_eq!(
        certify.allotment(),
        Some(800 / POOL_SHARE + 800 / GUARD_SHARE + 800),
        "DR-39: P4a.1's shares of the check's budget"
    );
    assert_eq!(check.remaining(), Some(800), "deducted from nothing");
    let elsewhere = certify_node(None, DeadlineSource::None);
    assert_eq!(
        elsewhere.allotment(),
        None,
        "no budget, no count of its own"
    );
}
