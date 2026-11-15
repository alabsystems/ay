// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn every_metered_callback_including_wire_and_restricted_subsetup_is_terminal() {
    let (terms, clause) = tiny();
    let before = terms.entries_snapshot();
    let bytes = bytes(&terms, clause);
    for operation in [Operation::Capture, Operation::Replay] {
        let end = deadline();
        let (proof, gates) = limits(end);
        let wire = wire_limits(end);
        let total = Cell::new(0);
        invoke(
            operation,
            &terms,
            clause,
            &bytes,
            &proof,
            &gates,
            &wire,
            WorkAllowance::new(GRANT, end),
            &mut || {
                total.set(total.get() + 1);
                true
            },
        )
        .unwrap();
        assert!(total.get() > 10);
        for stop_at in 1..=total.get() {
            let end = deadline();
            let (proof, gates) = limits(end);
            let wire = wire_limits(end);
            let calls = Cell::new(0);
            let result = invoke(
                operation,
                &terms,
                clause,
                &bytes,
                &proof,
                &gates,
                &wire,
                WorkAllowance::new(GRANT, end),
                &mut || {
                    calls.set(calls.get() + 1);
                    calls.get() != stop_at
                },
            );
            assert!(
                matches!(
                    result,
                    Err(MeteredBridgeError::Bridge(BridgeError::Cancelled))
                ),
                "{operation:?}: callback {stop_at}"
            );
            assert_eq!(calls.get(), stop_at);
        }
    }
    assert_eq!(terms.entries_snapshot(), before);
}

#[test]
fn all_five_absolute_deadlines_stop_before_lowering_or_callback() {
    let (terms, clause) = tiny();
    let past = Instant::now() - Duration::from_secs(1);
    for operation in [Operation::Capture, Operation::Replay] {
        for expired in 0..5 {
            let end = deadline();
            let (mut proof, mut gates) = limits(end);
            let mut wire = wire_limits(end);
            let credit_end = if expired == 0 { past } else { end };
            match expired {
                1 => wire.deadline = past,
                2 => proof.resolution.deadline = Some(past),
                3 => proof.resolution.validation.deadline = Some(past),
                4 => gates.deadline = Some(past),
                _ => {}
            }
            assert!(matches!(
                invoke(
                    operation,
                    &terms,
                    clause,
                    b"",
                    &proof,
                    &gates,
                    &wire,
                    WorkAllowance::new(GRANT, credit_end),
                    &mut || panic!("expired before callback")
                ),
                Err(MeteredBridgeError::Bridge(BridgeError::Deadline))
            ));
        }
        let end = deadline();
        let (mut proof, gates) = limits(end);
        proof.resolution.deadline = None;
        assert!(matches!(
            invoke(
                operation,
                &terms,
                clause,
                b"",
                &proof,
                &gates,
                &wire_limits(end),
                WorkAllowance::new(GRANT, end),
                &mut || true
            ),
            Err(MeteredBridgeError::Bridge(BridgeError::MissingDeadline))
        ));
        assert!(matches!(
            invoke(
                operation,
                &terms,
                clause,
                b"",
                &proof,
                &gates,
                &wire_limits(end),
                WorkAllowance::new(GRANT, end),
                &mut || false
            ),
            Err(MeteredBridgeError::Bridge(BridgeError::Cancelled))
        ));
    }
}

#[test]
fn invalid_wire_final_cleanup_observes_a_transient_stop() {
    let (terms, clause) = tiny();
    let end = deadline();
    let (proof, gates) = limits(end);
    let calls = Cell::new(0);
    assert!(invoke(
        Operation::Replay,
        &terms,
        clause,
        b"{",
        &proof,
        &gates,
        &wire_limits(end),
        WorkAllowance::new(GRANT, end),
        &mut || {
            calls.set(calls.get() + 1);
            true
        }
    )
    .is_err());
    let last = calls.get();
    assert!(last > 2);
    calls.set(0);
    assert!(matches!(
        invoke(
            Operation::Replay,
            &terms,
            clause,
            b"{",
            &proof,
            &gates,
            &wire_limits(end),
            WorkAllowance::new(GRANT, end),
            &mut || {
                calls.set(calls.get() + 1);
                calls.get() != last
            }
        ),
        Err(MeteredBridgeError::Bridge(BridgeError::Cancelled))
    ));
    assert_eq!(calls.get(), last);
}

#[test]
fn typed_control_keeps_nested_stops_and_caught_callback_panics_sticky() {
    let calls = Cell::new(0);
    let mut callback = || {
        calls.set(calls.get() + 1);
        if calls.get() == 2 {
            panic!("caught typed callback panic");
        }
        true
    };
    let result: Result<(), MeteredBridgeError> =
        Control::new(deadline(), &mut callback).run_typed(|control| {
            assert!(
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| control.poll())).is_err()
            );
            Ok(())
        });
    assert!(matches!(
        result,
        Err(MeteredBridgeError::Bridge(BridgeError::Cancelled))
    ));
    assert_eq!(calls.get(), 2);
    for error in [WireError::Cancelled, WireError::Deadline] {
        let calls = Cell::new(0);
        let result: Result<(), MeteredBridgeError> = Control::new(deadline(), &mut || {
            calls.set(calls.get() + 1);
            true
        })
        .run_typed(|_| Err(MeteredError::Wire(error).into()));
        match error {
            WireError::Cancelled => assert!(matches!(
                result,
                Err(MeteredBridgeError::Bridge(BridgeError::Cancelled))
            )),
            WireError::Deadline => assert!(matches!(
                result,
                Err(MeteredBridgeError::Bridge(BridgeError::Deadline))
            )),
            _ => unreachable!(),
        }
        assert_eq!(calls.get(), 1);
    }
}

#[test]
fn typed_final_boundary_drops_temporaries_and_rejected_success_owner() {
    struct Owner<'a>(&'a Cell<bool>);
    impl Drop for Owner<'_> {
        fn drop(&mut self) {
            self.0.set(true);
        }
    }
    for outcome in [
        Ok(()),
        Err(MeteredError::Wire(WireError::InvalidJson).into()),
    ] {
        let dropped = Cell::new(false);
        let calls = Cell::new(0);
        let result: Result<(), MeteredBridgeError> = Control::new(deadline(), &mut || {
            calls.set(calls.get() + 1);
            if calls.get() > 1 {
                assert!(dropped.get());
                return false;
            }
            true
        })
        .run_typed(|_| {
            let _temporary = Owner(&dropped);
            outcome
        });
        assert!(matches!(
            result,
            Err(MeteredBridgeError::Bridge(BridgeError::Cancelled))
        ));
        assert!(dropped.get());
        assert_eq!(calls.get(), 2);
    }
    let dropped = Cell::new(false);
    let calls = Cell::new(0);
    let result: Result<Owner<'_>, MeteredBridgeError> = Control::new(deadline(), &mut || {
        calls.set(calls.get() + 1);
        calls.get() == 1
    })
    .run_typed(|_| Ok(Owner(&dropped)));
    assert!(matches!(
        result,
        Err(MeteredBridgeError::Bridge(BridgeError::Cancelled))
    ));
    assert!(dropped.get());
    assert_eq!(calls.get(), 2);
}
