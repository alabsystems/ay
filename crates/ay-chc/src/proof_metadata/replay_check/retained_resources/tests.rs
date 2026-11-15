// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn controlled_artifact_and_chunked_hash_keep_legacy_bytes() {
    let value = serde_json::json!({
        "schema": "test", "quoted": "\n\"\\", "rows": [true, null, 12],
        "large": "z".repeat(CHUNK * 3 + 7),
    });
    let expected = serde_json::to_vec(&value).unwrap();
    let mut work = 0usize;
    let mut bytes = 0usize;
    let mut charge = |new_work, new_bytes| {
        work += new_work;
        bytes += new_bytes;
        true
    };
    let encoded = encode(&value, &mut charge).unwrap();
    assert_eq!(encoded, expected);
    let artifact = artifact("test", &encoded, &mut charge).unwrap();
    assert_eq!(
        artifact,
        ChcProofArtifactDigest::from_bytes("test", &expected)
    );
    assert!(work >= expected.len() * 2);
    assert!(bytes >= encoded.capacity());
}

#[test]
fn artifact_encoding_never_refunds_destroyed_backing_owners() {
    let value = serde_json::json!({ "large": "a".repeat(CHUNK * 5) });
    let mut total_bytes = 0usize;
    let mut charge = |_, bytes| {
        total_bytes += bytes;
        true
    };
    let first = encode(&value, &mut charge).unwrap();
    drop(first);
    let first_bytes = total_bytes;
    let mut charge = |_, bytes| {
        total_bytes += bytes;
        true
    };
    let second = encode(&value, &mut charge).unwrap();
    assert_eq!(total_bytes, first_bytes * 2);
    assert!(first_bytes >= second.capacity());
}

#[test]
fn one_request_credit_spans_multiple_artifact_encodings() {
    let value = serde_json::json!({ "data": "q".repeat(CHUNK + 1) });
    let mut required = 0usize;
    for _ in 0..2 {
        encode(&value, &mut |work, _| {
            required += work;
            true
        })
        .unwrap();
    }
    for credit in [required, required - 1] {
        let mut remaining = credit;
        let mut stopped = false;
        let mut charge = |work, _| {
            if stopped {
                return false;
            }
            let Some(next) = remaining.checked_sub(work) else {
                stopped = true;
                return false;
            };
            remaining = next;
            true
        };
        let first = encode(&value, &mut charge);
        assert!(first.is_ok());
        drop(first);
        let second = encode(&value, &mut charge);
        assert_eq!(second.is_ok(), credit == required);
    }
}

#[test]
fn refusal_does_not_publish_a_partial_artifact_or_digest() {
    let value = serde_json::json!({ "large": "a".repeat(CHUNK * 3) });
    let mut bytes = 0usize;
    let mut stopped = false;
    let mut charge = |_, new_bytes| {
        if stopped {
            return false;
        }
        bytes += new_bytes;
        if bytes > CHUNK * 2 {
            stopped = true;
            false
        } else {
            true
        }
    };
    assert!(encode(&value, &mut charge).is_err());
    assert!(!charge(0, 0), "later phases must keep the refusal latched");
    assert!(hash(b"source", &mut charge).is_err());
}

#[test]
fn row_reservation_overflow_refuses_before_any_callback() {
    let mut called = false;
    assert!(vector::<u64>(usize::MAX, &mut |_, _| {
        called = true;
        true
    })
    .is_err());
    assert!(!called);
}
