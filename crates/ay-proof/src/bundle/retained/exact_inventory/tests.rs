// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::bundle::retained::{control, TransportError, TransportOutcome};
use crate::ProofQuality;
use ay_core::time::Instant;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::time::Duration;

fn end() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

fn checked(ids: &[u32]) -> BundleReCheck {
    BundleReCheck {
        quality: ProofQuality::default(),
        assume_terms: ids.iter().copied().map(TermId).collect(),
    }
}

fn run(
    checked: &BundleReCheck,
    inventory: &[TermId],
    work: u64,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> TransportOutcome<Result<(), ReadError>> {
    control::run(end(), progress, |control| {
        control.constrain(work, 0)?;
        Ok(check(checked, inventory, control))
    })
}

#[test]
fn ordered_unique_comparison_preserves_actual_duplicates_without_scratch_debits() {
    let checked = checked(&[7, 7, 2, 7]);
    let mut charges = Vec::new();
    let outcome = run(&checked, &[TermId(7), TermId(2)], 12, &mut |w, b| {
        charges.push((w, b));
        true
    });
    outcome.result.unwrap().unwrap();
    // Entry/quality + four positions + four prefix probes + two first-use
    // comparisons + final inventory length. Test-owned fixtures/traces are
    // outside the comparator; zero bytes is a debit claim, not an RSS census.
    assert_eq!(outcome.usage.charged_work, 12);
    assert_eq!(outcome.usage.charged_bytes, 0);
    assert_eq!(outcome.usage.returned_owned_bytes, 0);
    assert_eq!(charges.first(), Some(&(0, 0)));
    assert_eq!(charges.last(), Some(&(0, 0)));
    assert_eq!(&charges[1..13], &[(1, 0); 12]);
    assert_eq!(charges.len(), 14);
    assert_eq!(
        checked.assume_terms,
        [TermId(7), TermId(7), TermId(2), TermId(7)]
    );
}

#[test]
fn reordered_repeated_missing_and_overbroad_inventories_are_typed_mismatches() {
    let checked = checked(&[7, 7, 2, 7]);
    for inventory in [vec![2, 7], vec![7, 2, 7], vec![7], vec![7, 2, 9], vec![]] {
        let inventory: Vec<_> = inventory.into_iter().map(TermId).collect();
        let outcome = run(&checked, &inventory, u64::MAX, &mut |_, _| true);
        assert!(matches!(
            outcome.result,
            Ok(Err(ReadError::Inventory(ExactInventoryError::Mismatch)))
        ));
        assert_eq!(outcome.usage.charged_bytes, 0);
    }
}

#[test]
fn incomplete_precedes_empty_and_no_assumption_is_not_an_exact_inventory() {
    for (trust_count, hole_count) in [(1, 0), (0, 1)] {
        let mut incomplete = checked(&[]);
        incomplete.quality.trust_count = trust_count;
        incomplete.quality.hole_count = hole_count;
        let outcome = run(&incomplete, &[], 1, &mut |_, _| true);
        assert!(matches!(
            outcome.result,
            Ok(Err(ReadError::Inventory(ExactInventoryError::Incomplete)))
        ));
        assert_eq!(outcome.usage.charged_work, 1);
    }
    let outcome = run(&checked(&[]), &[], 1, &mut |_, _| true);
    assert!(matches!(
        outcome.result,
        Ok(Err(ReadError::Inventory(ExactInventoryError::Empty)))
    ));
    assert_eq!(outcome.usage.charged_work, 1);
}

#[test]
fn exact_one_short_and_zero_work_have_precise_nonrefundable_boundaries() {
    let checked = checked(&[7, 7, 2, 7]);
    for cap in [12, 11, 0] {
        let outcome = run(&checked, &[TermId(7), TermId(2)], cap, &mut |_, _| true);
        if cap == 12 {
            outcome.result.unwrap().unwrap();
        } else {
            assert!(matches!(
                outcome.result,
                Err(TransportError::Limit { resource: "transport work", limit, actual })
                    if limit == cap as usize && actual == cap as usize + 1
            ));
        }
        assert_eq!(outcome.usage.charged_work, (cap as usize + 1).min(12));
        assert_eq!(outcome.usage.charged_bytes, 0);
    }
}

#[test]
fn every_probe_and_final_poll_can_refuse_without_reviving_control() {
    let checked = checked(&[7, 7, 2, 7]);
    for stop in 1..=14 {
        let mut calls = 0;
        let outcome = control::run(
            end(),
            &mut |_, _| {
                calls += 1;
                calls != stop
            },
            |control| {
                let result = check(&checked, &[TermId(7), TermId(2)], control);
                if result.is_err() {
                    assert!(matches!(
                        check(&checked, &[TermId(7), TermId(2)], control),
                        Err(ReadError::Transport(TransportError::Refused))
                    ));
                }
                // Deliberately swallow an inner refusal: finalization must
                // still refuse rather than accepting this apparent success.
                Ok(())
            },
        );
        assert!(matches!(outcome.result, Err(TransportError::Refused)));
        assert_eq!(calls, stop);
        assert_eq!(outcome.usage.charged_work, (stop - 1).min(12));
        assert_eq!(outcome.usage.charged_bytes, 0);
    }
}

#[test]
fn caught_callback_panics_at_each_comparison_checkpoint_remain_terminal() {
    let checked = checked(&[7, 7, 2, 7]);
    for stop in 2..=13 {
        let mut calls = 0;
        let outcome = control::run(
            end(),
            &mut |_, _| {
                calls += 1;
                assert_ne!(calls, stop, "caught comparator callback panic");
                true
            },
            |control| {
                assert!(catch_unwind(AssertUnwindSafe(|| {
                    check(&checked, &[TermId(7), TermId(2)], control)
                }))
                .is_err());
                assert!(matches!(
                    check(&checked, &[TermId(7), TermId(2)], control),
                    Err(ReadError::Transport(TransportError::Refused))
                ));
                Ok(())
            },
        );
        assert!(matches!(outcome.result, Err(TransportError::Refused)));
        assert_eq!(calls, stop);
        assert_eq!(outcome.usage.charged_work, stop - 1);
    }
}

#[test]
fn repeated_checks_share_prepaid_work_and_expired_deadline_never_calls_back() {
    let checked = checked(&[7, 7, 2, 7]);
    let outcome = control::run(end(), &mut |_, _| true, |control| {
        control.constrain(12, 0)?;
        check(&checked, &[TermId(7), TermId(2)], control).unwrap();
        assert!(matches!(
            check(&checked, &[TermId(7), TermId(2)], control),
            Err(ReadError::Transport(TransportError::Limit {
                actual: 13,
                ..
            }))
        ));
        Ok(())
    });
    assert!(matches!(
        outcome.result,
        Err(TransportError::Limit { actual: 13, .. })
    ));
    assert_eq!(outcome.usage.charged_work, 13);
    let mut calls = 0;
    let expired = control::run(
        Instant::now().checked_sub(Duration::from_secs(1)).unwrap(),
        &mut |_, _| {
            calls += 1;
            true
        },
        |control| Ok(check(&checked, &[TermId(7), TermId(2)], control)),
    );
    assert!(matches!(expired.result, Err(TransportError::Deadline)));
    assert_eq!(calls, 0);
    assert_eq!(expired.usage.charged_work, 0);
}
