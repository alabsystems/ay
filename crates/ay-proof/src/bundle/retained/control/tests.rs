// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::{cell::Cell, time::Duration};

struct Owner<'a>(&'a Cell<bool>);
impl Drop for Owner<'_> {
    fn drop(&mut self) {
        self.0.set(true);
    }
}

#[test]
fn final_refusal_observes_operation_cleanup_and_drops_success_owner() {
    let end = Instant::now() + Duration::from_secs(60);
    for outcome in [Ok(()), Err(TransportError::InvalidJson)] {
        let dropped = Cell::new(false);
        let calls = Cell::new(0);
        let result = run(
            end,
            &mut |_, _| {
                calls.set(calls.get() + 1);
                if calls.get() == 2 {
                    assert!(dropped.get());
                    return false;
                }
                true
            },
            |_| {
                let _temporary = Owner(&dropped);
                outcome
            },
        );
        assert_eq!(result.result, Err(TransportError::Refused));
        assert!(dropped.get());
        assert_eq!(calls.get(), 2);
    }
    let dropped = Cell::new(false);
    let calls = Cell::new(0);
    let result = run(
        end,
        &mut |_, _| {
            calls.set(calls.get() + 1);
            calls.get() == 1
        },
        |control| {
            control.usage.returned_owned_bytes = 7;
            Ok(Owner(&dropped))
        },
    );
    assert!(matches!(result.result, Err(TransportError::Refused)));
    assert!(dropped.get());
    assert_eq!(result.usage.returned_owned_bytes, 0);
    assert_eq!(calls.get(), 2);
}

#[test]
fn caught_callback_panic_and_final_deadline_cannot_publish_or_restart() {
    let end = Instant::now() + Duration::from_secs(60);
    let calls = Cell::new(0);
    let result = run(
        end,
        &mut |_, _| {
            calls.set(calls.get() + 1);
            if calls.get() == 2 {
                panic!("caught progress panic");
            }
            true
        },
        |control| {
            assert!(std::panic::catch_unwind(
                std::panic::AssertUnwindSafe(|| control.charge(1, 0))
            )
            .is_err());
            Ok(())
        },
    );
    assert_eq!(result.result, Err(TransportError::Refused));
    assert_eq!(calls.get(), 2);
    let calls = Cell::new(0);
    let result = run(
        end,
        &mut |_, _| {
            calls.set(calls.get() + 1);
            true
        },
        |control| {
            control.deadline = Instant::now() - Duration::from_secs(1);
            Err::<(), _>(TransportError::InvalidJson)
        },
    );
    assert_eq!(result.result, Err(TransportError::Deadline));
    assert_eq!(calls.get(), 1);
}

#[test]
fn output_write_failure_drops_partial_allocation_before_final_refusal() {
    let dropped = Cell::new(false);
    let calls = Cell::new(0);
    let result = run(
        Instant::now() + Duration::from_secs(60),
        &mut |_, _| {
            calls.set(calls.get() + 1);
            if calls.get() == 4 {
                assert!(dropped.get());
                return false;
            }
            true
        },
        |control| {
            let _output_owner = Owner(&dropped);
            // Same admitted-allocation / capped-writer error shape as encode.
            let _output = control.vector::<u8>(10)?;
            control.fail::<()>(TransportError::InvalidShape("output census differs"))
        },
    );
    assert_eq!(result.result, Err(TransportError::Refused));
    assert_eq!(calls.get(), 4); // initial, requested, actual, post-drop final
    assert_eq!(result.usage.charged_bytes, 10);
    assert_eq!(result.usage.returned_owned_bytes, 0);
}
