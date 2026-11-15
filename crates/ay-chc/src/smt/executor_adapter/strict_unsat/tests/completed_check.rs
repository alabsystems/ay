// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! #completed-check-accepted through the whole strict-UNSAT adapter: a stop
//! that lands right after the recheck's last admitted poll leaves the
//! certificate standing; the same stop one poll earlier still refuses it.

use super::super::resources::AFTER_CHARGE;
use super::*;
use std::cell::Cell;
use std::rc::Rc;

/// Run the adapter under a cancellable limit and cancel the caller's token
/// right after the `stop_after`-th admitted progress charge (`None`: never).
/// Returns the certificate and how many charges were admitted.
fn run_with_stop_after(
    presentation: StrictPresentation,
    stop_after: Option<usize>,
) -> (Option<StrictUnsatCert>, usize) {
    let parent = crate::CancellationToken::new();
    let cancellation = ReplayCancellation::new(&parent.child());
    let limit = ReplayLimit::Cancellable {
        deadline: live_deadline(),
        cancellation: &cancellation,
    };
    let admitted = Rc::new(Cell::new(0usize));
    let hook_admitted = Rc::clone(&admitted);
    let hook_parent = parent.clone();
    AFTER_CHARGE.with(|hook| {
        *hook.borrow_mut() = Some(Box::new(move || {
            hook_admitted.set(hook_admitted.get() + 1);
            if Some(hook_admitted.get()) == stop_after {
                hook_parent.cancel();
            }
        }));
    });
    let cert = run_strict_unsat(UNSAT, None, limit, presentation);
    AFTER_CHARGE.with(|hook| hook.borrow_mut().take());
    (cert, admitted.get())
}

#[test]
fn a_stop_after_the_last_poll_keeps_the_completed_certificate() {
    for presentation in [
        StrictPresentation::NativeOnly,
        StrictPresentation::WithAletheDiagnostic,
    ] {
        let (cert, total) = run_with_stop_after(presentation, None);
        assert!(cert.is_some(), "live run must certify");
        assert!(total > 1, "export and recheck charge progress");
        // The stop lands exactly after the check's last poll: everything after
        // it (binding result, presentation, solver destruction and the outer
        // phase exits) must not turn the finished check into a refusal.
        let (late, late_total) = run_with_stop_after(presentation, Some(total));
        assert_eq!(late_total, total, "the stop adds no admitted poll");
        let late = late.expect("a completed check is accepted after a late stop");
        assert!(matches!(
            late.strict_verdict,
            ay_dpll::api::StrictProofVerdict::Verified(quality) if quality.is_complete()
        ));
        // The late stop omits the optional text rather than refusing.
        assert!(late.alethe.is_none());
        // Negative control: the same stop one poll earlier is honoured.
        let (early, early_total) = run_with_stop_after(presentation, Some(total - 1));
        assert_eq!(early_total, total - 1);
        assert!(early.is_none(), "a stop before the last step still refuses");
    }
}

#[test]
fn a_stop_before_the_recheck_starts_still_refuses() {
    // The first admitted charge belongs to export, before the recheck.
    let (cert, admitted) = run_with_stop_after(StrictPresentation::NativeOnly, Some(1));
    assert_eq!(admitted, 1);
    assert!(cert.is_none());
}
