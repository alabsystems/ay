// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Copy, Debug)]
enum Operation {
    Decode,
    Encode,
    Malformed,
    Outer,
}

fn invoke(operation: Operation, progress: Progress<'_>) -> TransportOutcome<()> {
    match operation {
        Operation::Encode => {
            let out = encode(RETAINED_SCHEMA, &field(), &limits(), end(), progress);
            TransportOutcome {
                result: out.result.map(drop),
                usage: out.usage,
            }
        }
        Operation::Decode | Operation::Malformed => {
            let bytes = match operation {
                Operation::Decode => encoded(&field()),
                _ => br#"[{"step":0,"payload":{}}}"#.to_vec(),
            };
            let out = decode(
                RETAINED_SCHEMA,
                BorrowedField::Present(&bytes),
                &limits(),
                end(),
                progress,
            );
            TransportOutcome {
                result: out.result.map(drop),
                usage: out.usage,
            }
        }
        Operation::Outer => admit_outer_json(
            br#"{"retained":[{"step":0,"payload":{}}]}"#,
            end(),
            progress,
        ),
    }
}

#[test]
fn every_progress_refusal_is_sticky_through_final_cleanup() {
    for operation in [
        Operation::Decode,
        Operation::Encode,
        Operation::Malformed,
        Operation::Outer,
    ] {
        let total = Cell::new(0);
        let baseline = invoke(operation, &mut |_, _| {
            total.set(total.get() + 1);
            true
        });
        assert_eq!(
            baseline.result.is_err(),
            matches!(operation, Operation::Malformed)
        );
        assert!(total.get() > 2);
        for stop in 1..=total.get() {
            let calls = Cell::new(0);
            let outcome = invoke(operation, &mut |_, _| {
                calls.set(calls.get() + 1);
                calls.get() != stop
            });
            assert_eq!(
                outcome.result,
                Err(TransportError::Refused),
                "{operation:?}, {stop}"
            );
            assert_eq!(calls.get(), stop);
            assert_eq!(outcome.usage.returned_owned_bytes, 0);
        }
    }
}

#[test]
fn both_original_and_wire_deadlines_refuse_before_callback() {
    let past = Instant::now().checked_sub(Duration::from_secs(1)).unwrap();
    for expiry in 0..2 {
        let mut wire = limits();
        let deadline = if expiry == 0 { past } else { end() };
        if expiry == 1 {
            wire.deadline = past;
        }
        let mut callback = |_, _| -> bool { panic!("expired before callback") };
        assert_eq!(
            decode(
                RETAINED_SCHEMA,
                BorrowedField::Present(b"[]"),
                &wire,
                deadline,
                &mut callback
            )
            .result,
            Err(TransportError::Deadline)
        );
        assert_eq!(
            encode(RETAINED_SCHEMA, &field(), &wire, deadline, &mut callback).result,
            Err(TransportError::Deadline)
        );
    }
    assert_eq!(
        admit_outer_json(b"[]", past, &mut |_, _| panic!("expired")).result,
        Err(TransportError::Deadline)
    );
}

#[test]
fn cancellation_observed_after_invalid_shape_cleanup_overrides_the_shape_error() {
    let bad = RetainedField::Present(vec![RetainedStepPayload {
        step: 1,
        payload: b"0".to_vec(),
    }]);
    let calls = Cell::new(0);
    let baseline = encode(RETAINED_SCHEMA, &bad, &limits(), end(), &mut |_, _| {
        calls.set(calls.get() + 1);
        true
    });
    assert!(matches!(
        baseline.result,
        Err(TransportError::InvalidShape(_))
    ));
    let last = calls.get();
    calls.set(0);
    let stopped = encode(RETAINED_SCHEMA, &bad, &limits(), end(), &mut |_, _| {
        calls.set(calls.get() + 1);
        calls.get() != last
    });
    assert_eq!(stopped.result, Err(TransportError::Refused));
    assert_eq!(stopped.usage, baseline.usage);
    assert_eq!(calls.get(), last);
}
