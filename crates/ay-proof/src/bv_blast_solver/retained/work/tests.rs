// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn ledger(limit: u64) -> Ledger {
    let end = Instant::now() + Duration::from_secs(60);
    Ledger::new(WorkAllowance::new(limit, end), end)
}

#[test]
fn phases_receive_only_remaining_work_and_keep_their_own_ceiling() {
    let mut work = ledger(10);
    work.phase(Phase::Producer, 9, |grant| {
        assert_eq!(grant, 9);
        Ok(((), 6))
    })
    .unwrap();
    work.phase(Phase::Gates, 3, |grant| {
        assert_eq!(grant, 3);
        Ok(((), 2))
    })
    .unwrap();
    work.phase(Phase::Dag, u64::MAX, |grant| {
        assert_eq!(grant, 2);
        Ok(((), 2))
    })
    .unwrap();
    work.phase(Phase::Wire, u64::MAX, |grant| {
        assert_eq!(grant, 0);
        Ok(((), 0))
    })
    .unwrap();
    assert_eq!(work.remaining, 0);
    let result = work.finish(()).unwrap();
    assert_eq!(result.work.producer_validation, 6);
    assert_eq!(result.work.gates, 2);
    assert_eq!(result.work.dag, 2);
}

#[test]
fn refusal_and_overreported_u128_work_never_refund_or_resume() {
    for used in [1, u128::from(u64::MAX) + 1] {
        let mut work = ledger(0);
        assert!(
            matches!(work.phase(Phase::Wire, u64::MAX, |_| Ok(((), used))),
            Err(MeteredError::Work(WorkError::Exceeded { limit: 0, actual })) if actual == used)
        );
        assert!(matches!(
            work.phase::<()>(Phase::Dag, 10, |_| panic!("must not run")),
            Err(MeteredError::Work(WorkError::Refused))
        ));
    }
    let mut work = ledger(100);
    assert!(work
        .phase::<()>(Phase::Prefix, 100, |_| Err(
            malformed("opaque refusal").into()
        ))
        .is_err());
    assert!(matches!(work.check(), Err(WorkError::Refused)));
    assert!(work.finish(()).is_err());
}

#[test]
fn caught_phase_panic_is_terminal_and_success_can_never_overflow() {
    let mut work = ledger(100);
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = work.phase::<()>(Phase::Dag, 100, |_| panic!("phase panic"));
    }))
    .is_err());
    assert!(matches!(work.check(), Err(WorkError::Refused)));
    let mut work = ledger(u64::MAX);
    work.phase(Phase::Wire, u64::MAX, |_| Ok(((), u128::from(u64::MAX))))
        .unwrap();
    assert_eq!(work.remaining, 0);
    assert!(work.phase(Phase::Wire, u64::MAX, |_| Ok(((), 1))).is_err());
    assert!(work.finish(()).is_err());
}

#[test]
fn earliest_deadline_refuses_before_phase_and_latches_the_attempt() {
    let past = Instant::now().checked_sub(Duration::from_secs(1)).unwrap();
    let future = Instant::now() + Duration::from_secs(60);
    for (a, b) in [(past, future), (future, past)] {
        let mut work = Ledger::new(WorkAllowance::new(100, a), b);
        assert!(matches!(
            work.phase::<()>(Phase::Dag, 100, |_| panic!("expired")),
            Err(MeteredError::Work(WorkError::Deadline))
        ));
        assert!(matches!(work.check(), Err(WorkError::Refused)));
    }
}

#[test]
fn inspecting_allowance_deadline_neither_renews_time_nor_replaces_work() {
    let end = Instant::now() + Duration::from_secs(60);
    let allowance = WorkAllowance::new(7, end);
    assert_eq!(allowance.deadline(), end);
    assert_eq!(allowance.deadline(), end);
    let mut work = Ledger::new(allowance, end + Duration::from_secs(60));
    assert_eq!(work.deadline(), end);
    work.phase(Phase::Wire, u64::MAX, |grant| {
        assert_eq!(grant, 7);
        Ok(((), 7))
    })
    .unwrap();
    assert_eq!(work.remaining, 0);
    let past = Instant::now().checked_sub(Duration::from_secs(1)).unwrap();
    let expired = WorkAllowance::new(7, past);
    assert_eq!(expired.deadline(), past);
    assert!(matches!(
        Ledger::new(expired, end).check(),
        Err(WorkError::Deadline)
    ));
}
