// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::panic::{catch_unwind, AssertUnwindSafe};

use super::*;

#[test]
fn exact_aggregate_work_and_bytes_succeed_but_each_one_short_refuses() {
    let (proof, terms) = ordinary(1);
    let expected = plan(&proof, &terms).aggregate_charge();
    for (work, bytes, succeeds) in [
        (expected.work, expected.bytes, true),
        (expected.work - 1, expected.bytes, false),
        (expected.work, expected.bytes - 1, false),
        (0, 0, false),
    ] {
        let (mut used_work, mut used_bytes, mut calls) = (0, 0, 0);
        let result = plan(&proof, &terms).prepay(deadline(), &mut |w, b| {
            calls += 1;
            used_work += w;
            used_bytes += b;
            used_work <= work && used_bytes <= bytes
        });
        assert_eq!(result.is_ok(), succeeds);
        assert_eq!((used_work, used_bytes), (expected.work, expected.bytes));
        assert_eq!(calls, if succeeds { 2 } else { 1 });
    }
}

#[test]
fn every_census_and_prepaid_callback_is_terminal_without_repayment() {
    let (proof, terms) = ordinary(1);
    let mut census_calls = 0;
    plan_expensive_bv_credits_with_progress(&proof, &terms, &mut |_, _| {
        census_calls += 1;
        true
    })
    .unwrap();
    for stop in 1..=census_calls {
        let mut calls = 0;
        let result = plan_expensive_bv_credits_with_progress(&proof, &terms, &mut |_, _| {
            calls += 1;
            calls != stop
        });
        assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(calls, stop);
    }
    for stop in 1..=2 {
        let mut calls = 0;
        let result = plan(&proof, &terms).prepay(deadline(), &mut |_, _| {
            calls += 1;
            calls != stop
        });
        assert!(matches!(result, Err(BvCreditError::Refused)));
        assert_eq!(calls, stop);
        let mut credits = prepaid(&proof, &terms);
        calls = 0;
        assert!(matches!(
            credits.take(ProofId(0), &mut |_, _| {
                calls += 1;
                calls != stop
            }),
            Err(BvCreditError::Refused)
        ));
        assert_eq!(calls, stop);
        assert!(matches!(
            credits.take(ProofId(0), &mut |_, _| panic!("no retry")),
            Err(BvCreditError::Refused)
        ));
        assert_eq!(credits.finish(), Err(BvCreditError::Refused));
    }
}

#[test]
fn caught_callback_panics_cannot_issue_or_revive_credit() {
    let (proof, terms) = ordinary(1);
    for stop in 1..=2 {
        let mut calls = 0;
        assert!(catch_unwind(AssertUnwindSafe(|| {
            let _ = plan(&proof, &terms).prepay(deadline(), &mut |_, _| {
                calls += 1;
                assert_ne!(calls, stop, "injected prepayment panic");
                true
            });
        }))
        .is_err());
        assert_eq!(calls, stop);
        let mut credits = prepaid(&proof, &terms);
        calls = 0;
        assert!(catch_unwind(AssertUnwindSafe(|| {
            let _ = credits.take(ProofId(0), &mut |_, _| {
                calls += 1;
                assert_ne!(calls, stop, "injected issuance panic");
                true
            });
        }))
        .is_err());
        assert_eq!(calls, stop);
        assert!(matches!(
            credits.take(ProofId(0), &mut |_, _| panic!("no retry")),
            Err(BvCreditError::Refused)
        ));
        assert_eq!(credits.finish(), Err(BvCreditError::Refused));
    }
}

#[test]
fn original_deadline_is_checked_before_prepayment_issuance_and_finish() {
    let (proof, terms) = ordinary(1);
    assert!(matches!(
        plan(&proof, &terms).prepay(Instant::now(), &mut |_, _| panic!("expired")),
        Err(BvCreditError::Deadline)
    ));
    let mut credits = prepaid(&proof, &terms);
    credits.control.deadline = Instant::now();
    assert!(matches!(
        credits.take(ProofId(0), &mut |_, _| panic!("expired")),
        Err(BvCreditError::Deadline)
    ));
    credits.control.deadline = deadline();
    assert!(matches!(
        credits.take(ProofId(0), &mut |_, _| panic!("latched")),
        Err(BvCreditError::Refused)
    ));
    let mut credits = prepaid(&proof, &terms);
    drop(credits.take(ProofId(0), &mut |_, _| true).unwrap());
    credits.control.deadline = Instant::now();
    assert_eq!(credits.finish(), Err(BvCreditError::Deadline));
}

#[test]
fn deadline_is_observed_after_each_prepaid_and_issuance_callback() {
    let (proof, terms) = ordinary(1);
    for stop in 1..=2 {
        let end = Instant::now() + Duration::from_millis(50);
        let mut calls = 0;
        let result = plan(&proof, &terms).prepay(end, &mut |_, _| {
            calls += 1;
            if calls == stop {
                std::thread::sleep(end.saturating_duration_since(Instant::now()));
            }
            true
        });
        assert!(matches!(result, Err(BvCreditError::Deadline)));
        assert_eq!(calls, stop);
        let mut credits = prepaid(&proof, &terms);
        let end = Instant::now() + Duration::from_millis(50);
        credits.control.deadline = end;
        calls = 0;
        assert!(matches!(
            credits.take(ProofId(0), &mut |_, _| {
                calls += 1;
                if calls == stop {
                    std::thread::sleep(end.saturating_duration_since(Instant::now()));
                }
                true
            }),
            Err(BvCreditError::Deadline)
        ));
        assert_eq!(calls, stop);
        assert!(matches!(
            credits.take(ProofId(0), &mut |_, _| panic!("latched")),
            Err(BvCreditError::Refused)
        ));
    }
}

#[test]
#[cfg(target_pointer_width = "64")]
fn unrepresentable_source_position_refuses_before_any_debit() {
    let (proof, terms) = ordinary(1);
    let mut plan = plan(&proof, &terms);
    plan.entries[0].as_mut().unwrap().position = u32::MAX as usize + 1;
    assert!(matches!(
        plan.prepay(deadline(), &mut |_, _| panic!("not admitted")),
        Err(BvCreditError::Overflow)
    ));
}
