// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Borrowed report association tests, with no solver or fabricated SAT evidence.

use super::*;

#[test]
fn report_accessors_borrow_the_same_original_sealed_obligation() {
    let obligation = obligations().remove(0);
    let source_pointer = obligation.problem().source_smtlib().as_ptr();
    let origin_pointer = obligation.id().clause_origins().as_ptr();
    let expected_id = obligation.id().clone();
    let report = QuantifiedQueryRowReport {
        obligation,
        outcome: QuantifiedQueryOutcome::Unknown(QuantifiedQueryUnknownReason::Inconclusive),
        elapsed: Duration::from_millis(3),
    };
    assert!(std::ptr::eq(report.id(), report.obligation().id()));
    assert!(std::ptr::eq(
        report.problem(),
        report.obligation().problem()
    ));
    assert_eq!(report.id(), &expected_id);
    assert_eq!(report.problem().source_smtlib().as_ptr(), source_pointer);
    assert_eq!(
        report.obligation().id().clause_origins().as_ptr(),
        origin_pointer
    );
    assert!(report
        .obligation()
        .problem()
        .source_view()
        .clauses()
        .any(|clause| !clause.premises().is_empty()));
    assert_eq!(report.elapsed(), Duration::from_millis(3));
    assert!(matches!(
        report.outcome(),
        QuantifiedQueryOutcome::Unknown(QuantifiedQueryUnknownReason::Inconclusive)
    ));
}

#[test]
fn scheduler_and_report_move_all_original_obligations_even_after_cancel_reset() {
    let obligations = obligations();
    let original: Vec<_> = obligations
        .iter()
        .map(|obligation| {
            (
                obligation.problem().source_smtlib().as_ptr(),
                obligation.id().clause_origins().as_ptr(),
                obligation.id().clone(),
            )
        })
        .collect();
    let start = Instant::now();
    let time = Cell::new(Duration::ZERO);
    let clock = || start + time.get();
    let parent = CancellationToken::new();
    let control = control::Control::new(start, Duration::from_secs(20), &parent, &clock).unwrap();
    let mut fake = Fake::new(
        &time,
        &parent,
        vec![Action {
            candidate: Candidate::CancelReset,
            ..Action::default()
        }],
    );
    let batch = schedule::run(obligations, &control, None, &mut fake);
    assert_eq!(batch.rows.len(), original.len());
    assert!(!batch.all_checked && !batch.checked_unsafe);
    assert_eq!(fake.calls.len(), 1);
    for (row, (source_pointer, origin_pointer, id)) in batch.rows.into_iter().zip(original) {
        let schedule::Outcome::Unknown(reason) = row.outcome else {
            panic!("the observed cancellation rejects both rows")
        };
        assert_eq!(reason, QuantifiedQueryUnknownReason::Cancelled);
        let report = QuantifiedQueryRowReport {
            obligation: row.obligation,
            outcome: QuantifiedQueryOutcome::Unknown(reason),
            elapsed: row.elapsed,
        };
        assert_eq!(report.id(), &id);
        assert_eq!(report.problem().source_smtlib().as_ptr(), source_pointer);
        assert_eq!(
            report.obligation().id().clause_origins().as_ptr(),
            origin_pointer
        );
        assert!(std::ptr::eq(
            report.problem(),
            report.obligation().problem()
        ));
    }
    assert!(!parent.is_cancelled());
}
