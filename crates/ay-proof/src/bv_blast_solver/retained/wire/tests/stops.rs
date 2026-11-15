// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn every_decode_and_encode_callback_stop_is_terminal_including_publication() {
    let fixture = Fixture::new();
    let value = payload();
    for direction in 0..2 {
        let mut total = 0;
        let mut poll = || {
            total += 1;
            true
        };
        if direction == 0 {
            decode(
                JSON,
                &fixture.wire,
                &fixture.proof,
                &fixture.gates,
                &mut poll,
            )
            .result
            .unwrap();
        } else {
            encode(
                &value,
                &fixture.wire,
                &fixture.proof,
                &fixture.gates,
                &mut poll,
            )
            .result
            .unwrap();
        }
        assert!(total > 20);
        for stop in 1..=total {
            let mut calls = 0;
            let mut poll = || {
                calls += 1;
                calls != stop
            };
            let (error, usage) = if direction == 0 {
                let out = decode(
                    JSON,
                    &fixture.wire,
                    &fixture.proof,
                    &fixture.gates,
                    &mut poll,
                );
                (out.result.unwrap_err(), out.usage)
            } else {
                let out = encode(
                    &value,
                    &fixture.wire,
                    &fixture.proof,
                    &fixture.gates,
                    &mut poll,
                );
                (out.result.unwrap_err(), out.usage)
            };
            assert_eq!(
                error,
                WireError::Cancelled,
                "direction {direction}, stop {stop}"
            );
            assert_eq!(calls, stop, "no callback after an observed stop");
            assert_eq!(usage.returned_owned_bytes, 0);
        }
    }
}

#[test]
fn all_earliest_deadlines_and_required_proof_deadline_refuse() {
    for boundary in 0..5 {
        let mut fixture = Fixture::new();
        match boundary {
            0 => fixture.wire.deadline = Instant::now(),
            1 => fixture.proof.resolution.deadline = Some(Instant::now()),
            2 => fixture.proof.resolution.validation.deadline = Some(Instant::now()),
            3 => fixture.gates.deadline = Some(Instant::now()),
            4 => fixture.proof.resolution.deadline = None,
            _ => unreachable!(),
        }
        let expected = if boundary == 4 {
            WireError::MissingDeadline
        } else {
            WireError::Deadline
        };
        assert_eq!(fixture.decode(JSON).result, Err(expected));
        assert_eq!(fixture.encode(&payload()).result, Err(expected));
    }
}

#[test]
fn usage_survives_refusal_and_caller_grant_does_not_restart_between_operations() {
    let fixture = Fixture::new();
    let mut used = 0;
    let output = encode(
        &payload(),
        &fixture.wire,
        &fixture.proof,
        &fixture.gates,
        &mut || {
            used += 1;
            true
        },
    );
    let bytes = output.result.unwrap();
    let previous = used;
    let result = decode(
        &bytes,
        &fixture.wire,
        &fixture.proof,
        &fixture.gates,
        &mut || {
            used += 1;
            used <= previous
        },
    );
    assert_eq!(result.result, Err(WireError::Cancelled));
    assert_eq!(used, previous + 1);
    let mut wire = fixture.wire;
    wire.max_work = 1;
    let refused = decode(JSON, &wire, &fixture.proof, &fixture.gates, &mut || true);
    assert!(matches!(
        refused.result,
        Err(WireError::Limit {
            resource: "work",
            ..
        })
    ));
    assert!(refused.usage.charged_work > u128::from(wire.max_work));
    assert!(refused.usage.peak_storage_bytes >= JSON.len());
    assert_eq!(refused.usage.returned_owned_bytes, 0);
    assert!(output.usage.charged_work > 0);
}

#[test]
fn caught_callback_panic_cannot_revive_a_control() {
    let fixture = Fixture::new();
    let mut calls = 0;
    let mut callback = || {
        calls += 1;
        panic!("injected callback panic")
    };
    let mut control = Control::new(fixture.wire, &mut callback);
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| control.poll()));
    assert!(panic.is_err());
    assert_eq!(control.charge(1), Err(WireError::Cancelled));
    drop(control);
    assert_eq!(calls, 1);
}
