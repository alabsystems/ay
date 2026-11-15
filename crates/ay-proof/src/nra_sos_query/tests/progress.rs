// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn every_callback_including_the_final_poll_can_refuse_success() {
    let fixture = Fixture::linear();
    let (mut count, mut work, mut bytes) = (0, 0, 0);
    check_nra_sos_query_with_progress(
        &fixture.terms,
        &fixture.roots[..1],
        &fixture.roots[1..],
        &fixture.candidate,
        &mut |w, b| {
            count += 1;
            work += w;
            bytes += b;
            true
        },
    )
    .unwrap();
    assert!(count > 10 && work > 0 && bytes > 0);
    for reject_at in 1..=count {
        let mut seen = 0;
        let result = check_nra_sos_query_with_progress(
            &fixture.terms,
            &fixture.roots[..1],
            &fixture.roots[1..],
            &fixture.candidate,
            &mut |_, _| {
                seen += 1;
                seen != reject_at
            },
        );
        assert!(
            matches!(result, Err(NraSosQueryCheckError::ResourceLimit)),
            "callback {reject_at}"
        );
        assert_eq!(
            seen, reject_at,
            "refused callback must never be called again"
        );
    }
}

#[test]
fn callback_refusal_is_sticky_even_when_a_callee_keeps_polling() {
    let mut external_calls = 0;
    let result = with_sticky_progress(
        &mut |_, _| {
            external_calls += 1;
            external_calls != 1
        },
        |progress| {
            assert!(!progress(0, 0));
            assert!(!progress(0, 0));
            Ok(())
        },
    );
    assert!(matches!(result, Err(NraSosQueryCheckError::ResourceLimit)));
    assert_eq!(external_calls, 1);
}

#[test]
fn zero_work_or_bytes_refuses_before_unfunded_wrapper_allocations() {
    let fixture = Fixture::linear();
    for reject_work in [true, false] {
        let result = check_nra_sos_query_with_progress(
            &fixture.terms,
            &fixture.roots,
            &[],
            &fixture.candidate,
            &mut |work, bytes| if reject_work { work == 0 } else { bytes == 0 },
        );
        assert!(matches!(result, Err(NraSosQueryCheckError::ResourceLimit)));
    }
}

#[test]
fn currentness_refuses_every_callback_and_the_final_poll() {
    let fixture = Fixture::linear();
    let checked = fixture.check(1).unwrap();
    let mut count = 0;
    assert!(checked
        .is_current_for_with_progress(
            &fixture.terms,
            &fixture.roots[..1],
            &fixture.roots[1..],
            &mut |_, _| {
                count += 1;
                true
            },
        )
        .unwrap());
    for reject_at in 1..=count {
        let mut seen = 0;
        let result = checked.is_current_for_with_progress(
            &fixture.terms,
            &fixture.roots[..1],
            &fixture.roots[1..],
            &mut |_, _| {
                seen += 1;
                seen != reject_at
            },
        );
        assert!(matches!(result, Err(NraSosQueryCheckError::ResourceLimit)));
        assert_eq!(seen, reject_at);
    }
}

#[test]
fn one_callback_retains_its_allowance_across_checking_and_currentness() {
    let fixture = Fixture::linear();
    let mut used = 0usize;
    let checked = check_nra_sos_query_with_progress(
        &fixture.terms,
        &fixture.roots,
        &[],
        &fixture.candidate,
        &mut |work, _| {
            used += work;
            true
        },
    )
    .unwrap();
    let total = used;
    assert!(matches!(
        checked.is_current_for_with_progress(
            &fixture.terms,
            &fixture.roots,
            &[],
            &mut |work, _| {
                used += work;
                used <= total
            },
        ),
        Err(NraSosQueryCheckError::ResourceLimit)
    ));
    assert!(used > total);
}
