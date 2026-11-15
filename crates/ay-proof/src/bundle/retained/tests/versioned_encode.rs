// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Transport-only ownership tests; invented payloads confer no proof authority.

use super::*;
use crate::bundle::SerializableProofBundle;

fn snapshot() -> SerializableProofBundle {
    serde_json::from_str(
        r#"{"schema":"ay.proofbundle/v5","steps":[],"term_entries":[],"true_term":null,"false_term":null,"var_counter":0,"obligation_assertions":[],"datatype_declarations":[],"constructor_selectors":[],"datatype_member_signatures":[],"declared_function_identities":[]}"#,
    )
    .unwrap()
}

fn bundle_limits() -> BundleLimits {
    BundleLimits {
        max_json_bytes: 1024 * 1024,
        max_storage_bytes: 8 * 1024 * 1024,
        max_work: 10_000_000,
        deadline: end(),
    }
}

fn owning(field: RetainedField) -> RetainedBundle {
    let mut source = snapshot();
    source.schema = RETAINED_SCHEMA.to_owned();
    RetainedBundle::from_parts(source, field).unwrap()
}

fn attempt(envelope: &RetainedBundle, progress: Progress<'_>) -> TransportOutcome<Vec<u8>> {
    encode_versioned_bundle(envelope, &bundle_limits(), &limits(), end(), progress)
}

#[test]
fn owning_v6_round_trip_preserves_schema_inventory_and_raw_frames() {
    let raw = std::str::from_utf8(PAYLOAD).unwrap();
    let framed = format!("[{{\"outside_free_offset\":{raw}}},{{\"final_clause\":{raw}}}]");
    for payload in [PAYLOAD, framed.as_bytes()] {
        let field = RetainedField::Present(vec![RetainedStepPayload {
            step: 7,
            payload: payload.to_vec(),
        }]);
        let envelope = owning(field.clone());
        let payload_pointer = envelope.parts().1[0].payload.as_ptr();
        let before = envelope.parts().0.schema.as_ptr();
        let output = attempt(&envelope, &mut |_, _| true).result.unwrap();
        let expected = encode_bundle(
            &snapshot(),
            &field,
            &bundle_limits(),
            &limits(),
            end(),
            &mut |_, _| true,
        )
        .result
        .unwrap();
        assert_eq!(output, expected);
        assert_eq!(envelope.parts().0.schema, RETAINED_SCHEMA);
        assert_eq!(envelope.parts().0.schema.as_ptr(), before);
        assert_eq!(envelope.parts().1[0].payload.as_ptr(), payload_pointer);
        let decoded = decode_bundle(&output, &bundle_limits(), &limits(), end(), &mut |_, _| {
            true
        })
        .result
        .unwrap();
        drop(output);
        assert_eq!(decoded.parts().0.schema, RETAINED_SCHEMA);
        assert_eq!(decoded.parts().1, envelope.parts().1);
        assert!(crate::bundle::re_check_bundle_strict(decoded.parts().0).is_err());
    }
}

#[test]
fn owning_empty_inventory_is_emitted_and_legacy_encoder_still_refuses_v6() {
    let envelope = owning(RetainedField::Present(Vec::new()));
    let output = attempt(&envelope, &mut |_, _| true).result.unwrap();
    let value: serde_json::Value = serde_json::from_slice(&output).unwrap();
    assert_eq!(value["schema"], RETAINED_SCHEMA);
    assert_eq!(value["retained"], serde_json::json!([]));
    for field in [RetainedField::Absent, RetainedField::Present(Vec::new())] {
        assert_eq!(
            encode_bundle(
                envelope.parts().0,
                &field,
                &bundle_limits(),
                &limits(),
                end(),
                &mut |_, _| true,
            )
            .result,
            Err(TransportError::Presence(PresenceError::UnsupportedSchema)),
        );
    }
}

#[test]
fn versioned_encoding_shares_exact_work_and_byte_admission_with_legacy_writer() {
    let field = field();
    let envelope = owning(field.clone());
    let expected = encode_bundle(
        &snapshot(),
        &field,
        &bundle_limits(),
        &limits(),
        end(),
        &mut |_, _| true,
    );
    let baseline = attempt(&envelope, &mut |_, _| true);
    assert!(baseline.result.is_ok());
    assert_eq!(baseline.result, expected.result);
    assert_eq!(baseline.usage, expected.usage);
    let work = baseline.usage.charged_work;
    let bytes = baseline.usage.charged_bytes;
    assert!(work > 0 && bytes > 0);
    for (work_cap, byte_cap, accepted) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
    ] {
        let mut used = (0usize, 0usize);
        let result = attempt(&envelope, &mut |w, b| {
            used.0 += w;
            used.1 += b;
            used.0 <= work_cap && used.1 <= byte_cap
        });
        assert_eq!(result.result.is_ok(), accepted);
        if !accepted {
            assert_eq!(result.result, Err(TransportError::Refused));
            assert_eq!(result.usage.returned_owned_bytes, 0);
        }
    }
}

#[test]
fn versioned_encoding_keeps_local_json_work_and_storage_ceilings() {
    let envelope = owning(field());
    let baseline = attempt(&envelope, &mut |_, _| true);
    let length = baseline.result.as_ref().unwrap().len();
    for short in [false, true] {
        let mut bound = bundle_limits();
        bound.max_json_bytes = length - usize::from(short);
        bound.max_work = baseline.usage.charged_work as u64;
        bound.max_storage_bytes = baseline.usage.charged_bytes;
        let result = encode_versioned_bundle(&envelope, &bound, &limits(), end(), &mut |_, _| true);
        assert_eq!(result.result.is_ok(), !short);
        if short {
            assert_eq!(result.usage.returned_owned_bytes, 0);
        }
    }
    for resource in 0..2 {
        let mut bound = bundle_limits();
        if resource == 0 {
            bound.max_work = baseline.usage.charged_work as u64 - 1;
        } else {
            bound.max_storage_bytes = baseline.usage.charged_bytes - 1;
        }
        assert!(
            encode_versioned_bundle(&envelope, &bound, &limits(), end(), &mut |_, _| true,)
                .result
                .is_err()
        );
    }
}

#[test]
fn versioned_encoding_refusal_is_sticky_through_output_cleanup() {
    let envelope = owning(field());
    let total = Cell::new(0);
    assert!(attempt(&envelope, &mut |_, _| {
        total.set(total.get() + 1);
        true
    })
    .result
    .is_ok());
    assert!(total.get() > 2);
    for stop in 1..=total.get() {
        let calls = Cell::new(0);
        let outcome = attempt(&envelope, &mut |_, _| {
            calls.set(calls.get() + 1);
            calls.get() != stop
        });
        assert_eq!(outcome.result, Err(TransportError::Refused));
        assert_eq!(outcome.usage.returned_owned_bytes, 0);
        assert_eq!(calls.get(), stop);
    }
}

#[test]
fn versioned_encoding_uses_all_original_deadlines() {
    let envelope = owning(field());
    let past = Instant::now() - Duration::from_secs(1);
    for expiry in 0..3 {
        let mut bound = bundle_limits();
        let mut wire = limits();
        let mut deadline = end();
        match expiry {
            0 => bound.deadline = past,
            1 => wire.deadline = past,
            _ => deadline = past,
        }
        let result = encode_versioned_bundle(&envelope, &bound, &wire, deadline, &mut |_, _| {
            panic!("expired")
        });
        assert_eq!(result.result, Err(TransportError::Deadline));
        assert_eq!(result.usage.returned_owned_bytes, 0);
    }
}
