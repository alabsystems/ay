// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Copy, Debug)]
enum Operation {
    Decode,
    Encode,
}

fn invoke(operation: Operation, wire: &WireLimits, progress: Progress<'_>) -> TransportOutcome<()> {
    let result = match operation {
        Operation::Decode => {
            let bytes = encoded(&field());
            let out = decode(
                RETAINED_SCHEMA,
                BorrowedField::Present(&bytes),
                wire,
                end(),
                progress,
            );
            TransportOutcome {
                result: out.result.map(drop),
                usage: out.usage,
            }
        }
        Operation::Encode => {
            let out = encode(RETAINED_SCHEMA, &field(), wire, end(), progress);
            TransportOutcome {
                result: out.result.map(drop),
                usage: out.usage,
            }
        }
    };
    result
}

#[test]
fn exact_and_one_short_caller_work_and_byte_admission_cover_all_new_owners() {
    for operation in [Operation::Decode, Operation::Encode] {
        let wire = limits();
        let measured = invoke(operation, &wire, &mut |_, _| true);
        measured.result.unwrap();
        assert!(measured.usage.returned_owned_bytes > 0);
        for (work_limit, byte_limit, accepted) in [
            (
                measured.usage.charged_work,
                measured.usage.charged_bytes,
                true,
            ),
            (
                measured.usage.charged_work - 1,
                measured.usage.charged_bytes,
                false,
            ),
            (
                measured.usage.charged_work,
                measured.usage.charged_bytes - 1,
                false,
            ),
            (0, usize::MAX, false),
            (usize::MAX, 0, false),
        ] {
            let (mut work, mut bytes) = (0_usize, 0_usize);
            let outcome = invoke(operation, &wire, &mut |w, b| {
                work = work.checked_add(w).unwrap();
                bytes = bytes.checked_add(b).unwrap();
                work <= work_limit && bytes <= byte_limit
            });
            assert_eq!(outcome.result.is_ok(), accepted, "{operation:?}");
            assert_eq!(outcome.usage.charged_work, work);
            assert_eq!(outcome.usage.charged_bytes, bytes);
            if accepted {
                assert_eq!(outcome.usage, measured.usage);
            } else {
                assert_eq!(outcome.result, Err(TransportError::Refused));
                assert_eq!(outcome.usage.returned_owned_bytes, 0);
            }
        }
    }
}

#[test]
fn supplied_work_cap_is_an_extra_ceiling_not_a_renewed_cumulative_grant() {
    let mut wire = limits();
    wire.max_rows = 0;
    wire.max_literals = 0;
    wire.max_hints = 0;
    for operation in [Operation::Decode, Operation::Encode] {
        let baseline = invoke(operation, &limits(), &mut |_, _| true);
        let outer = invoke(operation, &wire, &mut |_, _| true);
        outer.result.unwrap();
        assert_eq!(outer.usage, baseline.usage);
        assert!(outer.usage.charged_work > 0);
        let mut exact = wire;
        exact.max_work = outer.usage.charged_work as u64;
        let admitted = invoke(operation, &exact, &mut |_, _| true);
        admitted.result.unwrap();
        assert_eq!(admitted.usage, outer.usage);
        exact.max_work -= 1;
        assert!(matches!(
            invoke(operation, &exact, &mut |_, _| true).result,
            Err(TransportError::Limit {
                resource: "transport work",
                ..
            })
        ));
        exact.max_work = 0;
        assert!(matches!(
            invoke(operation, &exact, &mut |_, _| true).result,
            Err(TransportError::Limit {
                resource: "transport work",
                ..
            })
        ));
    }
    // Not inner-proof acceptance: zero row/literal/hint limits remain for the
    // required independent inner codec/checker. Each per-call work ceiling is
    // additional to, not a substitute for, the cumulative callback above.
}

#[test]
fn payload_json_and_actual_new_storage_caps_are_not_overridden() {
    for operation in [Operation::Decode, Operation::Encode] {
        let mut wire = limits();
        wire.max_json_bytes = PAYLOAD.len();
        invoke(operation, &wire, &mut |_, _| true).result.unwrap();
        wire.max_json_bytes -= 1;
        assert!(invoke(operation, &wire, &mut |_, _| true).result.is_err());
        let mut wire = limits();
        let measured = invoke(operation, &wire, &mut |_, _| true);
        wire.max_storage_bytes = measured.usage.charged_bytes;
        invoke(operation, &wire, &mut |_, _| true).result.unwrap();
        wire.max_storage_bytes -= 1;
        assert!(matches!(
            invoke(operation, &wire, &mut |_, _| true).result,
            Err(TransportError::Limit {
                resource: "new transport bytes",
                ..
            })
        ));
    }
}

#[test]
fn shared_callback_across_calls_cannot_renew_an_allocation_allowance() {
    let bytes = encoded(&field());
    let sample = decoded(&bytes);
    sample.result.unwrap();
    let mut used = 0_usize;
    let mut progress = |_: usize, count: usize| {
        used = used.checked_add(count).unwrap();
        used <= sample.usage.charged_bytes
    };
    decode(
        RETAINED_SCHEMA,
        BorrowedField::Present(&bytes),
        &limits(),
        end(),
        &mut progress,
    )
    .result
    .unwrap();
    assert_eq!(
        decode(
            RETAINED_SCHEMA,
            BorrowedField::Present(&bytes),
            &limits(),
            end(),
            &mut progress
        )
        .result,
        Err(TransportError::Refused)
    );
}

#[test]
fn declared_lengths_overflow_without_new_allocations() {
    let mut wire = limits();
    wire.max_json_bytes = usize::MAX;
    let outcome = decode(
        RETAINED_SCHEMA,
        BorrowedField::Present(b"[]"),
        &wire,
        end(),
        &mut |_, _| true,
    );
    assert_eq!(outcome.result, Err(TransportError::Overflow));
    assert_eq!(outcome.usage.charged_bytes, 0);
    assert_eq!(outcome.usage.returned_owned_bytes, 0);
}
