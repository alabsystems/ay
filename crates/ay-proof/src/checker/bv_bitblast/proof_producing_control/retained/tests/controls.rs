// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Copy, Debug)]
enum Operation {
    Capture,
    Replay,
}

fn invoke(
    operation: Operation,
    terms: &TermStore,
    clause: TermId,
    payload: &RetainedBvRefutation,
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    poll: &mut dyn FnMut() -> bool,
) -> Result<(), BridgeError> {
    let end = proof.resolution.deadline.unwrap_or_else(deadline);
    match operation {
        Operation::Capture => capture_clause(terms, &[clause], end, proof, gates, poll).map(drop),
        Operation::Replay => {
            replay_clause(terms, &[clause], Some(payload), end, proof, gates, poll)
        }
    }
}

#[test]
fn every_capture_and_replay_poll_is_terminal_including_final_cleanup() {
    let (terms, clause) = identity();
    let before = terms.entries_snapshot();
    let payload = capture(&terms, clause);
    for operation in [Operation::Capture, Operation::Replay] {
        let (proof, gates) = limits(deadline());
        let total = Cell::new(0);
        invoke(
            operation,
            &terms,
            clause,
            &payload,
            &proof,
            &gates,
            &mut || {
                total.set(total.get() + 1);
                true
            },
        )
        .unwrap();
        assert!(total.get() > 10);
        for stop_at in 1..=total.get() {
            let (proof, gates) = limits(deadline());
            let calls = Cell::new(0);
            let result = invoke(
                operation,
                &terms,
                clause,
                &payload,
                &proof,
                &gates,
                &mut || {
                    calls.set(calls.get() + 1);
                    calls.get() != stop_at // A transient refusal must stay sticky.
                },
            );
            assert_eq!(
                result,
                Err(BridgeError::Cancelled),
                "{operation:?} poll {stop_at}"
            );
            assert_eq!(calls.get(), stop_at, "no callback after stop");
        }
    }
    assert_eq!(terms.entries_snapshot(), before);
    replay(&terms, clause, Some(&payload)).unwrap();
}

#[test]
fn all_absolute_deadlines_intersect_and_missing_deadline_cannot_grant_time() {
    let (terms, clause) = identity();
    let payload = capture(&terms, clause);
    let past = Instant::now().checked_sub(Duration::from_secs(1)).unwrap();
    for operation in [Operation::Capture, Operation::Replay] {
        for expired in 0..4 {
            let end = deadline();
            let (mut proof, mut gates) = limits(end);
            let outer = if expired == 0 { past } else { end };
            match expired {
                1 => proof.resolution.deadline = Some(past),
                2 => proof.resolution.validation.deadline = Some(past),
                3 => gates.deadline = Some(past),
                _ => {}
            }
            let result = match operation {
                Operation::Capture => {
                    capture_clause(&terms, &[clause], outer, &proof, &gates, &mut || true).map(drop)
                }
                Operation::Replay => replay_clause(
                    &terms,
                    &[clause],
                    Some(&payload),
                    outer,
                    &proof,
                    &gates,
                    &mut || true,
                ),
            };
            assert_eq!(result, Err(BridgeError::Deadline));
        }
        let (mut proof, gates) = limits(deadline());
        proof.resolution.deadline = None;
        assert_eq!(
            invoke(
                operation,
                &terms,
                clause,
                &payload,
                &proof,
                &gates,
                &mut || true
            ),
            Err(BridgeError::MissingDeadline)
        );
        assert_eq!(
            invoke(
                operation,
                &terms,
                clause,
                &payload,
                &proof,
                &gates,
                &mut || false
            ),
            Err(BridgeError::Cancelled)
        );
    }
}

#[test]
fn capture_requires_finite_search_caps_without_rejecting_zero_as_unbounded() {
    let (terms, clause) = identity();
    let end = deadline();
    let (proof, gates) = limits(end);
    for absent in 0..2 {
        let mut changed = proof.clone();
        if absent == 0 {
            changed.resolution.max_conflicts = None;
        } else {
            changed.resolution.max_decisions = None;
        }
        assert_eq!(
            capture_clause(&terms, &[clause], end, &changed, &gates, &mut || true),
            Err(BridgeError::MissingSearchBounds)
        );
    }
    let mut zero = proof;
    zero.resolution.max_conflicts = Some(0);
    zero.resolution.max_decisions = Some(0);
    let result = capture_clause(&terms, &[clause], end, &zero, &gates, &mut || true);
    assert_ne!(result, Err(BridgeError::MissingSearchBounds));
}

#[test]
fn deadline_intersection_changes_no_numeric_field() {
    let end = deadline();
    let (mut proof, mut gates) = limits(end);
    proof.max_expr_nodes = 0;
    proof.resolution.max_conflicts = None;
    proof.resolution.max_decisions = Some(0);
    proof.resolution.validation.max_work = 0;
    gates.max_work = 0;
    let earliest = end.checked_sub(Duration::from_secs(10)).unwrap();
    let mut callback = || true;
    let mut control = Control::new(earliest, &mut callback);
    let (actual_proof, actual_gates) = effective_limits(&proof, &gates, &mut control).unwrap();
    proof.resolution.deadline = Some(earliest);
    proof.resolution.validation.deadline = Some(earliest);
    gates.deadline = Some(earliest);
    // Debug covers every nested numeric field, including future added fields.
    assert_eq!(format!("{actual_proof:?}"), format!("{proof:?}"));
    assert_eq!(format!("{actual_gates:?}"), format!("{gates:?}"));
}

#[test]
fn caller_zero_caps_are_not_replaced_by_private_defaults() {
    let (terms, clause) = identity();
    let payload = capture(&terms, clause);
    for cap in 0..10 {
        let (mut proof, mut gates) = limits(deadline());
        match cap {
            0 => proof.max_expr_nodes = 0,
            1 => proof.max_construction_bytes = 0,
            2 => proof.resolution.max_num_vars = 0,
            3 => proof.resolution.max_input_clauses = 0,
            4 => proof.resolution.max_codec_bytes = 0,
            5 => proof.resolution.validation.max_work = 0,
            6 => proof.resolution.validation.max_bytes = 0,
            7 => proof.resolution.max_derived_steps = 0,
            8 => gates.max_work = 0,
            9 => gates.max_vars = 0,
            _ => unreachable!(),
        }
        for operation in [Operation::Capture, Operation::Replay] {
            assert!(
                invoke(
                    operation,
                    &terms,
                    clause,
                    &payload,
                    &proof,
                    &gates,
                    &mut || true
                )
                .is_err(),
                "{operation:?}, cap {cap}"
            );
        }
    }
}

#[test]
fn caught_callback_panic_and_nested_stop_cannot_resume() {
    let calls = Cell::new(0);
    let mut callback = || {
        calls.set(calls.get() + 1);
        assert!(calls.get() != 2, "caught nested callback panic");
        true
    };
    let mut control = Control::new(deadline(), &mut callback);
    let result = control.run(|control| {
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| control.poll())).is_err());
        Ok(())
    });
    assert_eq!(result, Err(BridgeError::Cancelled));
    assert_eq!(calls.get(), 2);
    for stop in [BridgeError::Cancelled, BridgeError::Deadline] {
        let calls = Cell::new(0);
        let mut callback = || {
            calls.set(calls.get() + 1);
            true
        };
        let result: Result<(), _> =
            Control::new(deadline(), &mut callback).run(|_| Err(stop.clone()));
        assert_eq!(result, Err(stop));
        assert_eq!(calls.get(), 1);
    }
}

#[test]
fn final_admission_observes_temporary_cleanup_on_success_and_error() {
    struct Owner<'a>(&'a Cell<bool>);
    impl Drop for Owner<'_> {
        fn drop(&mut self) {
            self.0.set(true);
        }
    }
    for outcome in [Ok(()), Err(BridgeError::Source("refused".into()))] {
        let dropped = Cell::new(false);
        let calls = Cell::new(0);
        let mut callback = || {
            calls.set(calls.get() + 1);
            if calls.get() > 1 {
                assert!(dropped.get());
                return false;
            }
            true
        };
        let result = Control::new(deadline(), &mut callback).run(|_| {
            let _temporary = Owner(&dropped);
            outcome
        });
        assert_eq!(result, Err(BridgeError::Cancelled));
        assert!(dropped.get());
        assert_eq!(calls.get(), 2);
    }
}
