// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn input_cap_refuses_before_lexical_scratch_or_owned_admission() {
    let json = document(SNAPSHOT_SCHEMA, None, None);
    let outcome = control::run(end(), &mut |_, _| true, |control| {
        read(json.as_bytes(), json.len() - 1, control)
    });
    assert!(matches!(
        outcome.result,
        Err(TransportError::Limit {
            resource: "outer JSON bytes",
            ..
        })
    ));
    assert_eq!(outcome.usage.charged_work, 0);
    assert_eq!(outcome.usage.charged_bytes, 0);
    assert_eq!(outcome.usage.returned_owned_bytes, 0);
}

#[test]
fn shared_work_and_scratch_exact_limits_pass_and_one_short_refuses() {
    let json = document(RETAINED_SCHEMA, Some("[]"), None);
    let baseline = checked(json.as_bytes());
    assert!(baseline.result.is_ok());
    let work = baseline.usage.charged_work;
    let bytes = baseline.usage.charged_bytes;
    assert!(work > 0 && bytes > 0);
    for (work_limit, byte_limit, accepted) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
    ] {
        let outcome = control::run(end(), &mut |_, _| true, |control| {
            control.constrain(work_limit as u64, byte_limit)?;
            read(json.as_bytes(), json.len(), control)
        });
        assert_eq!(outcome.result.is_ok(), accepted);
        if !accepted {
            assert!(matches!(outcome.result, Err(TransportError::Limit { .. })));
        }
        assert_eq!(outcome.usage.returned_owned_bytes, 0);
    }
}

#[test]
fn every_success_and_failure_cleanup_poll_refuses_terminally() {
    let valid = document(RETAINED_SCHEMA, Some("[]"), None);
    let malformed = format!("{valid} trailing");
    let shape = valid.replace("\"steps\":[]", "\"steps\":null");
    for (json, accepted) in [(&valid, true), (&malformed, false), (&shape, false)] {
        let total = Cell::new(0);
        let baseline = control::run(
            end(),
            &mut |_, _| {
                total.set(total.get() + 1);
                true
            },
            |control| read(json.as_bytes(), json.len(), control),
        );
        assert_eq!(baseline.result.is_ok(), accepted);
        assert!(total.get() > 3);
        for stop in 1..=total.get() {
            let calls = Cell::new(0);
            let outcome = control::run(
                end(),
                &mut |_, _| {
                    calls.set(calls.get() + 1);
                    calls.get() != stop
                },
                |control| read(json.as_bytes(), json.len(), control),
            );
            assert!(matches!(outcome.result, Err(TransportError::Refused)));
            assert_eq!(calls.get(), stop);
            assert_eq!(outcome.usage.returned_owned_bytes, 0);
            if stop == total.get() {
                assert_eq!(outcome.usage, baseline.usage);
            }
        }
    }
}

#[test]
fn original_deadline_precedes_callback_and_even_malformed_input() {
    let outcome = control::run(
        Instant::now() - Duration::from_secs(1),
        &mut |_, _| -> bool { panic!("expired before callback") },
        |control| read(b"{", 1, control),
    );
    assert!(matches!(outcome.result, Err(TransportError::Deadline)));
    assert_eq!(outcome.usage.charged_work, 0);
    assert_eq!(outcome.usage.returned_owned_bytes, 0);
}

#[test]
fn failed_envelope_cannot_restart_or_renew_shared_control() {
    let valid = document(SNAPSHOT_SCHEMA, None, None);
    let malformed = format!("{valid} trailing");
    let result = control::run(end(), &mut |_, _| true, |control| {
        let error = read(malformed.as_bytes(), malformed.len(), control).unwrap_err();
        let usage = control.usage;
        assert_eq!(
            read(valid.as_bytes(), valid.len(), control).unwrap_err(),
            error
        );
        assert_eq!(control.usage, usage);
        Ok(())
    });
    assert!(matches!(result.result, Err(TransportError::InvalidJson)));
}

#[test]
fn caught_progress_panic_poisoning_survives_another_read_and_final_cleanup() {
    let json = document(SNAPSHOT_SCHEMA, None, None);
    let calls = Cell::new(0);
    let outcome = control::run(
        end(),
        &mut |_, _| {
            calls.set(calls.get() + 1);
            if calls.get() == 4 {
                panic!("caught callback panic");
            }
            true
        },
        |control| {
            let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                read(json.as_bytes(), json.len(), control)
            }));
            assert!(caught.is_err());
            assert!(matches!(
                read(json.as_bytes(), json.len(), control),
                Err(TransportError::Refused)
            ));
            Ok(())
        },
    );
    assert_eq!(outcome.result, Err(TransportError::Refused));
    assert_eq!(calls.get(), 4);
}
