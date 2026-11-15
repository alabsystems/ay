// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::{cell::Cell, time::Duration};

mod fixtures;
mod framed;
mod malformed;
mod resources;
mod stops;
mod versioned_encode;

const PAYLOAD: &[u8] = br#"{"version":1,"rows":[{"id":4,"literals":[2],"hints":[1,2]},{"id":5,"literals":[],"hints":[3,4]}],"empty_clause_id":5}"#;

fn end() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

fn limits() -> WireLimits {
    WireLimits {
        max_json_bytes: 1024 * 1024,
        max_rows: 100,
        max_literals: 10000,
        max_hints: 10000,
        max_work: 1_000_000,
        max_storage_bytes: 8 * 1024 * 1024,
        deadline: end(),
    }
}

fn field() -> RetainedField {
    RetainedField::Present(vec![RetainedStepPayload {
        step: 7,
        payload: PAYLOAD.to_vec(),
    }])
}

fn encoded(field: &RetainedField) -> Vec<u8> {
    encode(RETAINED_SCHEMA, field, &limits(), end(), &mut |_, _| true)
        .result
        .unwrap()
        .unwrap()
}

fn decoded(bytes: &[u8]) -> TransportOutcome<RetainedField> {
    decode(
        RETAINED_SCHEMA,
        BorrowedField::Present(bytes),
        &limits(),
        end(),
        &mut |_, _| true,
    )
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Envelope<'a> {
    schema: &'a str,
    #[serde(default, borrow)]
    retained: BorrowedField<'a>,
}

fn borrowed(json: &[u8]) -> Result<Envelope<'_>, serde_json::Error> {
    // The eventual real outer reader must make this same call BEFORE serde.
    admit_outer_json(json, end(), &mut |_, _| true)
        .result
        .unwrap();
    serde_json::from_slice(json)
}

#[test]
fn absence_empty_inventory_and_null_have_distinct_schema_meanings() {
    let legacy = borrowed(br#"{"schema":"ay.proofbundle/v5"}"#).unwrap();
    assert!(legacy.retained.is_absent());
    assert_eq!(
        decode(
            legacy.schema,
            legacy.retained,
            &limits(),
            end(),
            &mut |_, _| true
        )
        .result
        .unwrap(),
        RetainedField::Absent
    );
    assert_eq!(
        encode(
            SNAPSHOT_SCHEMA,
            &RetainedField::Absent,
            &limits(),
            end(),
            &mut |_, _| true
        )
        .result
        .unwrap(),
        None
    );
    let current = borrowed(br#"{"schema":"ay.proofbundle/v6","retained":[]}"#).unwrap();
    let empty = decode(
        current.schema,
        current.retained,
        &limits(),
        end(),
        &mut |_, _| true,
    )
    .result
    .unwrap();
    assert_eq!(empty, RetainedField::Present(Vec::new()));
    assert_eq!(encoded(&empty), b"[]");
    assert_eq!(
        schema_presence(SNAPSHOT_SCHEMA, &empty),
        Err(PresenceError::UnexpectedRetainedField)
    );
    assert_eq!(
        schema_presence(RETAINED_SCHEMA, &RetainedField::Absent),
        Err(PresenceError::MissingRetainedField)
    );
    for old_or_unknown in [
        "ay.proofbundle/v3",
        "ay.proofbundle/v4",
        "ay.proofbundle/v999",
    ] {
        assert_eq!(
            schema_presence(old_or_unknown, &empty),
            Err(PresenceError::UnsupportedSchema)
        );
    }
    for schema in [SNAPSHOT_SCHEMA, RETAINED_SCHEMA] {
        let json = format!(r#"{{"schema":"{schema}","retained":null}}"#);
        assert!(borrowed(json.as_bytes()).is_err());
    }
}

#[test]
fn raw_payload_bytes_are_borrowed_then_preserved_without_string_escaping() {
    let payload = b"{ \"version\" : 1, \"rows\" : [], \"empty_clause_id\" : 0 }";
    let original = RetainedField::Present(vec![RetainedStepPayload {
        step: u32::MAX,
        payload: payload.to_vec(),
    }]);
    let bytes = encoded(&original);
    assert!(bytes
        .windows(b"\"payload\":{ ".len())
        .any(|w| w == b"\"payload\":{ "));
    let view: view::Inventory<'_> = serde_json::from_slice(&bytes).unwrap();
    let raw = view.entries[0].unwrap().payload.get().as_bytes();
    assert_eq!(raw, payload);
    let start = bytes.as_ptr() as usize;
    assert!((start..start + bytes.len()).contains(&(raw.as_ptr() as usize)));
    assert_eq!(decoded(&bytes).result.unwrap(), original);
}

#[test]
fn exact_eight_claimed_entries_round_trip_without_conferring_authority() {
    let entries: Vec<_> = (0..8)
        .map(|_| RetainedStepPayload {
            step: 123456,
            payload: br#"{"unrecognized":7}"#.to_vec(),
        })
        .collect();
    let original = RetainedField::Present(entries);
    assert_eq!(decoded(&encoded(&original)).result.unwrap(), original);
    // Duplicate/nonexistent source claims and malformed inner proof shapes are
    // intentionally opaque transport, not independent checker acceptance.
}

#[test]
fn escaped_metadata_keys_keep_borrowed_payloads_and_exact_u32_boundary() {
    let source =
        br#"[{"\u0073tep":4294967295,"pay\u006coad":{"rows":[],"version":1,"empty_clause_id":0}}]"#;
    let decoded = decoded(source).result.unwrap();
    let RetainedField::Present(entries) = decoded else {
        panic!("present inventory");
    };
    assert_eq!(entries[0].step, u32::MAX);
    assert_eq!(
        entries[0].payload,
        br#"{"rows":[],"version":1,"empty_clause_id":0}"#
    );
}

#[test]
fn private_wire_decoder_still_independently_checks_the_retained_payload() {
    use crate::bv_blast_solver::retained::wire;
    let restored = decoded(&encoded(&field())).result.unwrap();
    let RetainedField::Present(entries) = restored else {
        panic!("present inventory");
    };
    let deadline = end();
    let (proof, gates) = fixtures::proof_limits(deadline);
    let payload = wire::decode(&entries[0].payload, &limits(), &proof, &gates, &mut || true)
        .result
        .unwrap();
    assert_eq!(payload.empty_clause_id, 5);
    assert_eq!(payload.rows.len(), 2);
    assert!(wire::decode(
        br#"{"unrecognized":7}"#,
        &limits(),
        &proof,
        &gates,
        &mut || true
    )
    .result
    .is_err());
}
