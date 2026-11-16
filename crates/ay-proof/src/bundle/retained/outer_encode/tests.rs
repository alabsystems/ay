// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{Constant, ProofId};
use num_bigint::BigInt;
use std::{cell::Cell, time::Duration};

fn end() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

fn limits() -> BundleLimits {
    BundleLimits {
        max_json_bytes: 1024 * 1024,
        max_storage_bytes: 8 * 1024 * 1024,
        max_work: 10_000_000,
        deadline: end(),
    }
}

fn wire() -> WireLimits {
    WireLimits {
        max_json_bytes: 1024 * 1024,
        max_rows: 100,
        max_literals: 1000,
        max_hints: 1000,
        max_work: 1_000_000,
        max_storage_bytes: 8 * 1024 * 1024,
        deadline: end(),
    }
}

fn bundle() -> SerializableProofBundle {
    // Deliberately not a valid UNSAT proof: encoding must grant no authority.
    SerializableProofBundle {
        schema: SNAPSHOT_SCHEMA.to_owned(),
        steps: vec![ProofStep::Assume(TermId(0))],
        term_entries: vec![
            (
                TermData::Const(Constant::String("{\"edge\":\"\\\"}\nλ".to_owned())),
                Sort::String,
            ),
            (
                TermData::Const(Constant::Int(
                    -((BigInt::from(1) << 128usize) + BigInt::from(1)),
                )),
                Sort::Int,
            ),
        ],
        true_term: None,
        false_term: None,
        var_counter: 2,
        obligation_assertions: vec![TermId(0)],
        datatype_declarations: Vec::new(),
        constructor_selectors: Vec::new(),
        datatype_member_signatures: Vec::new(),
        declared_function_identities: Vec::new(),
    }
}

fn retained() -> RetainedField {
    RetainedField::Present(vec![RetainedStepPayload {
        step: 0,
        // Syntax-only transport: this is deliberately not a refutation.
        payload: br#"{ "unrecognized": 7 }"#.to_vec(),
    }])
}

fn encoded(bundle: &SerializableProofBundle, field: &RetainedField) -> Vec<u8> {
    encode_bundle(bundle, field, &limits(), &wire(), end(), &mut |_, _| true)
        .result
        .unwrap()
}

#[test]
fn complete_legacy_encoding_matches_existing_bytes_without_normalization() {
    let source = bundle();
    let expected = serde_json::to_vec(&source).unwrap();
    let result = encoded(&source, &RetainedField::Absent);
    assert_eq!(result, expected);
    let decoded: SerializableProofBundle = serde_json::from_slice(&result).unwrap();
    assert_eq!(serde_json::to_vec(&decoded).unwrap(), expected);
    assert_eq!(serde_json::to_vec(&source).unwrap(), expected);
}

#[test]
fn retained_encoding_keeps_raw_inventory_and_refuses_legacy_deserialization() {
    let source = bundle();
    let output = encoded(&source, &retained());
    let value: serde_json::Value = serde_json::from_slice(&output).unwrap();
    assert_eq!(value["schema"], RETAINED_SCHEMA);
    assert_eq!(value["retained"][0]["step"], 0);
    assert_eq!(value["retained"][0]["payload"]["unrecognized"], 7);
    assert!(output
        .windows(br#""payload":{ "unrecognized": 7 }"#.len())
        .any(|part| part == br#""payload":{ "unrecognized": 7 }"#));
    assert!(serde_json::from_slice::<SerializableProofBundle>(&output).is_err());
    assert_eq!(source.schema, SNAPSHOT_SCHEMA);
}

#[test]
fn complete_emission_reenters_borrowed_reader_without_losing_v6_evidence() {
    let source = bundle();
    for field in [
        RetainedField::Absent,
        RetainedField::Present(Vec::new()),
        retained(),
    ] {
        let encoded = encoded(&source, &field);
        let borrowed = borrow_bundle(&encoded, &limits(), end(), &mut |_, _| true);
        assert_eq!(borrowed.usage.returned_owned_bytes, 0);
        let view = borrowed.result.unwrap();
        assert_eq!(
            view.encoding,
            if field.is_absent() {
                BundleEncoding::SnapshotV5
            } else {
                BundleEncoding::RetainedV6
            }
        );
        assert_eq!(
            view.fields.steps.get(),
            serde_json::to_string(&source.steps).unwrap()
        );
        let schema = match view.encoding {
            BundleEncoding::SnapshotV5 => SNAPSHOT_SCHEMA,
            BundleEncoding::RetainedV6 => RETAINED_SCHEMA,
        };
        let restored = decode(schema, view.fields.retained, &wire(), end(), &mut |_, _| {
            true
        })
        .result
        .unwrap();
        assert_eq!(restored, field);
        // No legacy owner was reconstructed and no proof was checked here.
    }
}

#[test]
fn empty_retained_inventory_is_present_v6_not_omitted_v5() {
    let output = encoded(&bundle(), &RetainedField::Present(Vec::new()));
    let value: serde_json::Value = serde_json::from_slice(&output).unwrap();
    assert_eq!(value["schema"], RETAINED_SCHEMA);
    assert_eq!(value["retained"], serde_json::json!([]));
    let legacy: serde_json::Value =
        serde_json::from_slice(&encoded(&bundle(), &RetainedField::Absent)).unwrap();
    assert!(legacy.get("retained").is_none());
}

#[test]
fn unknown_or_retained_source_schema_cannot_be_downgraded() {
    for schema in [
        RETAINED_SCHEMA,
        "ay.proofbundle/v3",
        "ay.proofbundle/v4",
        "ay.proofbundle/v999",
        "",
    ] {
        let mut source = bundle();
        source.schema = schema.to_owned();
        for field in [RetainedField::Absent, retained()] {
            let outcome =
                encode_bundle(&source, &field, &limits(), &wire(), end(), &mut |_, _| true);
            assert_eq!(
                outcome.result,
                Err(TransportError::Presence(PresenceError::UnsupportedSchema))
            );
            assert_eq!(outcome.usage.returned_owned_bytes, 0);
        }
    }
}

#[test]
fn exact_output_byte_ceiling_passes_and_one_less_refuses() {
    let source = bundle();
    let field = retained();
    let expected = encoded(&source, &field);
    let mut bound = limits();
    bound.max_json_bytes = expected.len();
    let exact = encode_bundle(&source, &field, &bound, &wire(), end(), &mut |_, _| true);
    assert_eq!(exact.result.unwrap(), expected);
    bound.max_json_bytes -= 1;
    let short = encode_bundle(&source, &field, &bound, &wire(), end(), &mut |_, _| true);
    assert!(matches!(short.result, Err(TransportError::Limit { .. })));
    assert_eq!(short.usage.returned_owned_bytes, 0);
}

#[test]
fn inventory_scratch_and_output_owner_remain_cumulatively_charged() {
    let source = bundle();
    let field = retained();
    let before = serde_json::to_vec(&source).unwrap();
    let full = encode_bundle(&source, &field, &limits(), &wire(), end(), &mut |_, _| true);
    let output = full.result.unwrap();
    assert_eq!(full.usage.returned_owned_bytes, output.capacity());
    assert!(full.usage.charged_bytes > output.capacity());
    let mut bound = limits();
    bound.max_storage_bytes = full.usage.charged_bytes - 1;
    let refused = encode_bundle(&source, &field, &bound, &wire(), end(), &mut |_, _| true);
    assert!(matches!(refused.result, Err(TransportError::Limit { .. })));
    assert_eq!(refused.usage.returned_owned_bytes, 0);
    assert_eq!(serde_json::to_vec(&source).unwrap(), before);
}

#[test]
fn complete_count_and_emit_work_cannot_be_refunded_between_passes() {
    let source = bundle();
    let field = retained();
    let measured = encode_bundle(&source, &field, &limits(), &wire(), end(), &mut |_, _| true);
    assert!(measured.result.is_ok());
    let mut bound = limits();
    bound.max_work = measured.usage.charged_work as u64;
    let exact = encode_bundle(&source, &field, &bound, &wire(), end(), &mut |_, _| true);
    assert!(exact.result.is_ok());
    bound.max_work -= 1;
    let short = encode_bundle(&source, &field, &bound, &wire(), end(), &mut |_, _| true);
    assert!(matches!(short.result, Err(TransportError::Limit { .. })));
    assert_eq!(short.usage.returned_owned_bytes, 0);
}

#[test]
fn any_original_deadline_expiry_refuses_before_caller_entry() {
    let source = bundle();
    let expired = Instant::now().checked_sub(Duration::from_secs(1)).unwrap();
    for position in 0..3 {
        let mut outer = limits();
        let mut inner = wire();
        let mut deadline = end();
        match position {
            0 => deadline = expired,
            1 => outer.deadline = expired,
            _ => inner.deadline = expired,
        }
        let calls = Cell::new(0);
        let outcome = encode_bundle(
            &source,
            &retained(),
            &outer,
            &inner,
            deadline,
            &mut |_, _| {
                calls.set(calls.get() + 1);
                true
            },
        );
        assert_eq!(outcome.result, Err(TransportError::Deadline));
        assert_eq!(calls.get(), 0);
        assert_eq!(outcome.usage.returned_owned_bytes, 0);
    }
}

#[test]
fn every_callback_refusal_is_sticky_and_publishes_no_output() {
    let source = bundle();
    let field = retained();
    let mut calls = 0;
    let complete = encode_bundle(&source, &field, &limits(), &wire(), end(), &mut |_, _| {
        calls += 1;
        true
    });
    assert!(complete.result.is_ok());
    for stop in 1..=calls {
        let mut seen = 0;
        let outcome = encode_bundle(&source, &field, &limits(), &wire(), end(), &mut |_, _| {
            seen += 1;
            seen != stop
        });
        assert_eq!(outcome.result, Err(TransportError::Refused), "stop {stop}");
        assert_eq!(seen, stop, "callback reused after stop {stop}");
        assert_eq!(outcome.usage.returned_owned_bytes, 0);
    }
}

#[test]
fn excessive_sort_nesting_refuses_before_unbounded_recursion() {
    let mut source = bundle();
    let mut sort = Sort::Bool;
    for _ in 0..lexical::OUTER_DEPTH {
        sort = Sort::Seq(Box::new(sort));
    }
    source.steps = vec![ProofStep::Anchor {
        end_step: ProofId(1),
        variables: vec![("deep".to_owned(), sort)],
    }];
    let result = encode_bundle(
        &source,
        &RetainedField::Absent,
        &limits(),
        &wire(),
        end(),
        &mut |_, _| true,
    );
    assert!(matches!(
        result.result,
        Err(TransportError::Limit {
            resource: "bundle JSON depth",
            ..
        })
    ));
    assert_eq!(result.usage.returned_owned_bytes, 0);
}
