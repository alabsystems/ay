// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn raw_byte_cap_is_admitted_before_lexical_or_collection_work() {
    let mut fixture = Fixture::new();
    fixture.wire.max_json_bytes = JSON.len();
    fixture.decode(JSON).result.unwrap();
    fixture.encode(&payload()).result.unwrap();
    fixture.wire.max_json_bytes -= 1;
    let failed = fixture.decode(JSON);
    assert!(matches!(
        failed.result,
        Err(WireError::Limit {
            resource: "JSON bytes",
            ..
        })
    ));
    assert_eq!(failed.usage, WireUsage::default());
    assert!(matches!(
        fixture.encode(&payload()).result,
        Err(WireError::Limit {
            resource: "JSON bytes",
            ..
        })
    ));
}

#[test]
fn exact_work_and_peak_storage_grants_and_one_short_are_enforced() {
    for direction in 0..2 {
        let mut fixture = Fixture::new();
        let usage = if direction == 0 {
            let result = fixture.decode(JSON);
            result.result.unwrap();
            result.usage
        } else {
            let result = fixture.encode(&payload());
            result.result.unwrap();
            result.usage
        };
        fixture.wire.max_work = u64::try_from(usage.charged_work).unwrap();
        fixture.wire.max_storage_bytes = usage.peak_storage_bytes;
        if direction == 0 {
            fixture.decode(JSON).result.unwrap();
        } else {
            fixture.encode(&payload()).result.unwrap();
        }
        fixture.wire.max_work -= 1;
        let failed = if direction == 0 {
            let out = fixture.decode(JSON);
            assert!(matches!(
                out.result,
                Err(WireError::Limit {
                    resource: "work",
                    ..
                })
            ));
            out.usage
        } else {
            let out = fixture.encode(&payload());
            assert!(matches!(
                out.result,
                Err(WireError::Limit {
                    resource: "work",
                    ..
                })
            ));
            out.usage
        };
        assert_eq!(failed.returned_owned_bytes, 0);
        assert!(failed.charged_work > u128::from(fixture.wire.max_work));
        fixture.wire.max_work += 1;
        fixture.wire.max_storage_bytes -= 1;
        let (error, failed) = if direction == 0 {
            let out = fixture.decode(JSON);
            (out.result.unwrap_err(), out.usage)
        } else {
            let out = fixture.encode(&payload());
            (out.result.unwrap_err(), out.usage)
        };
        assert!(matches!(
            error,
            WireError::Limit {
                resource: "storage bytes",
                ..
            }
        ));
        assert_eq!(failed.returned_owned_bytes, 0);
        assert!(failed.peak_storage_bytes > fixture.wire.max_storage_bytes);
    }
}

#[test]
fn wire_and_existing_proof_caps_intersect_without_reinterpreting_json_bytes() {
    for cap in 0..12 {
        let mut fixture = Fixture::new();
        match cap {
            0 => fixture.wire.max_rows = 1,
            1 => fixture.wire.max_literals = 0,
            2 => fixture.wire.max_hints = 3,
            3 => fixture.proof.resolution.max_derived_steps = 1,
            4 => fixture.proof.resolution.max_derived_literals = 0,
            5 => fixture.proof.resolution.max_hints = 3,
            6 => fixture.proof.resolution.validation.max_derived_steps = 1,
            7 => fixture.proof.resolution.validation.max_derived_literals = 0,
            8 => fixture.proof.resolution.validation.max_hints = 3,
            9 => fixture.proof.resolution.validation.max_work = 0,
            10 => fixture.proof.resolution.validation.max_bytes = 0,
            11 => fixture.proof.resolution.max_codec_bytes = 0,
            _ => unreachable!(),
        }
        assert!(fixture.decode(JSON).result.is_err(), "cap {cap}");
        assert!(fixture.encode(&payload()).result.is_err(), "cap {cap}");
    }
    let mut fixture = Fixture::new();
    fixture.proof.resolution.max_proof_output_bytes = 0;
    // This old field bounds logical packed proof output, not this JSON codec.
    fixture.decode(JSON).result.unwrap();
    fixture.encode(&payload()).result.unwrap();
}

#[test]
fn row_growth_accounts_for_old_new_buffers_and_honors_preallocation_refusal() {
    let fixture = Fixture::new();
    let mut poll = || true;
    let mut control = Control::new(fixture.wire, &mut poll);
    let mut rows: Vec<RetainedRupRow> = Vec::new();
    control.reserve(&mut rows, 1).unwrap();
    rows.push(payload().rows.remove(0));
    let old = rows.capacity() * size_of::<RetainedRupRow>();
    let previous_capacity = rows.capacity();
    let requested = previous_capacity + 1;
    control.limits.max_storage_bytes = old + requested * size_of::<RetainedRupRow>() - 1;
    assert!(matches!(
        control.reserve(&mut rows, requested),
        Err(WireError::Limit {
            resource: "storage bytes",
            ..
        })
    ));
    assert_eq!(rows.capacity(), previous_capacity);
    assert!(control.usage.peak_storage_bytes >= old + requested * size_of::<RetainedRupRow>());
}
