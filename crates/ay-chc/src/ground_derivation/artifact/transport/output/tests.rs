// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[derive(serde::Serialize)]
struct TextFixture {
    text: String,
    values: Vec<i128>,
}

fn fixture() -> TextFixture {
    TextFixture {
        text: format!(
            "\"\\\n\u{0000}é🦀{}",
            "x".repeat(2 * super::super::POLL_BYTES + 7)
        ),
        values: vec![i128::MIN, 0, i128::MAX],
    }
}

#[test]
fn canonical_output_preserves_serde_bytes_and_exact_cap_boundary() {
    let value = fixture();
    let expected = serde_json::to_vec(&value).unwrap();
    for limit in [expected.len(), expected.len() + 1] {
        let actual = serialize_with_limit(
            &value,
            limit,
            &mut GroundValidationControl::new(&mut || true),
        )
        .unwrap();
        assert_eq!(actual, expected);
    }
    assert_eq!(
        serialize_envelope(&value, &mut GroundValidationControl::new(&mut || true)).unwrap(),
        expected
    );
    let failure = serialize_with_limit(
        &value,
        expected.len() - 1,
        &mut GroundValidationControl::new(&mut || true),
    )
    .unwrap_err();
    assert_eq!(failure.reason, Reason::ArtifactTooLarge);
    assert_eq!(
        failure.detail,
        format!("artifact exceeds maximum of {} bytes", expected.len() - 1)
    );
}

#[test]
fn every_output_refusal_is_sticky_and_a_fresh_retry_is_byte_exact() {
    let value = fixture();
    let mut calls = 0;
    let expected = serialize_envelope(
        &value,
        &mut GroundValidationControl::new(&mut || {
            calls += 1;
            true
        }),
    )
    .unwrap();
    assert!(calls > 4);
    for refused in 1..=calls {
        let mut observed = 0;
        let failure = serialize_envelope(
            &value,
            &mut GroundValidationControl::new(&mut || {
                observed += 1;
                observed != refused
            }),
        )
        .unwrap_err();
        assert_eq!(failure.reason, Reason::Interrupted, "poll {refused}");
        assert_eq!(observed, refused);
    }
    assert_eq!(
        serialize_envelope(&value, &mut GroundValidationControl::new(&mut || true)).unwrap(),
        expected
    );
}

#[test]
fn overflow_stops_before_retaining_more_bytes_and_cannot_resume() {
    let mut callback = || true;
    let mut control = GroundValidationControl::new(&mut callback);
    let mut writer = BoundedOutput {
        bytes: Vec::new(),
        limit: 3,
        failure: None,
        control: &mut control,
    };
    assert_eq!(writer.write(b"abc").unwrap(), 3);
    assert!(writer.write(b"d").is_err());
    assert_eq!(writer.bytes, b"abc");
    assert_eq!(writer.failure, Some(Reason::ArtifactTooLarge));
    assert!(writer.write(b"later").is_err());
    assert_eq!(writer.bytes, b"abc");
}

#[test]
fn production_output_ceiling_counts_the_serialized_quotes() {
    let text = "x".repeat(CHC_GROUND_DERIVATION_ARTIFACT_MAX_BYTES - 2);
    let accepted =
        serialize_envelope(&text, &mut GroundValidationControl::new(&mut || true)).unwrap();
    assert_eq!(accepted.len(), CHC_GROUND_DERIVATION_ARTIFACT_MAX_BYTES);
    assert_eq!(accepted.first(), Some(&b'"'));
    assert_eq!(accepted.last(), Some(&b'"'));
    drop(accepted);

    let oversized = format!("{text}x");
    let failure = serialize_envelope(&oversized, &mut GroundValidationControl::new(&mut || true))
        .unwrap_err();
    assert_eq!(failure.reason, Reason::ArtifactTooLarge);
}

#[test]
fn chunked_writer_stops_at_first_refused_chunk() {
    let mut calls = 0;
    let mut callback = || {
        calls += 1;
        calls != 2
    };
    let mut control = GroundValidationControl::new(&mut callback);
    let mut writer = BoundedOutput {
        bytes: Vec::new(),
        limit: 4 * super::super::POLL_BYTES,
        failure: None,
        control: &mut control,
    };
    let input = vec![b'x'; 3 * super::super::POLL_BYTES];
    assert!(writer.write(&input).is_err());
    assert_eq!(writer.bytes.len(), super::super::POLL_BYTES);
    assert!(writer.control.is_stopped());
    assert!(writer.write(b"later").is_err());
    assert_eq!(writer.bytes.len(), super::super::POLL_BYTES);
    drop(writer);
    assert_eq!(calls, 2);
}

struct FailingSerialization;

impl Serialize for FailingSerialization {
    fn serialize<S: serde::Serializer>(&self, _: S) -> Result<S::Ok, S::Error> {
        Err(serde::ser::Error::custom("synthetic serialization failure"))
    }
}

#[test]
fn post_serialization_refusal_precedes_wrapped_output_errors() {
    let failure = serialize_envelope(
        &FailingSerialization,
        &mut GroundValidationControl::new(&mut || true),
    )
    .unwrap_err();
    assert_eq!(failure.reason, Reason::SerializationFailed);
    assert!(failure.detail.contains("synthetic serialization failure"));
    let mut polls = 0;
    let failure = serialize_envelope(
        &FailingSerialization,
        &mut GroundValidationControl::new(&mut || {
            polls += 1;
            polls != 2
        }),
    )
    .unwrap_err();
    assert_eq!(failure.reason, Reason::Interrupted);
    assert_eq!(polls, 2);

    // Entry, then the first write (which exceeds a zero-byte ceiling), then
    // the post-serde poll: a refusal there must not become ArtifactTooLarge.
    let mut polls = 0;
    let failure = serialize_with_limit(
        &true,
        0,
        &mut GroundValidationControl::new(&mut || {
            polls += 1;
            polls != 3
        }),
    )
    .unwrap_err();
    assert_eq!(failure.reason, Reason::Interrupted);
    assert_eq!(polls, 3);
}
