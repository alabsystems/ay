// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn metadata_duplicates_unknown_fields_and_wrong_payload_types_refuse() {
    for bytes in [
        br#"[{"payload":{}}]"#.as_slice(),
        br#"[{"step":0}]"#,
        br#"[{"step":0,"step":1,"payload":{}}]"#,
        br#"[{"step":0,"payload":{},"payload":{}}]"#,
        br#"[{"step":0,"payload":{},"checked":0}]"#,
        br#"[{"step":0,"payload":"{}"}]"#,
        br#"[{"step":0,"payload":null}]"#,
        br#"[{"step":0,"payload":1}]"#,
        br#"[{"step":4294967296,"payload":{}}]"#,
        br#"[{"step":-1,"payload":{}}]"#,
        br#"[{"step":1.0,"payload":{}}]"#,
        br#"[{"step":0,"payload":{}}}"#,
        br#"[] trailing"#,
    ] {
        assert!(decoded(bytes).result.is_err(), "{bytes:?}");
    }
    for json in [
        br#"{"schema":"ay.proofbundle/v6","retained":[],"retained":[]}"#.as_slice(),
        br#"{"schema":"ay.proofbundle/v6","schema":"ay.proofbundle/v5","retained":[]}"#,
        br#"{"schema":"ay.proofbundle/v6","retained":[],"checked":true}"#,
    ] {
        assert!(borrowed(json).is_err());
    }
}

#[test]
fn oversized_tokens_and_depth_fail_before_any_parser_or_owner_reservation() {
    let long = format!(r#"[{{"step":0,"payload":{{"{}":0}}}}]"#, "x".repeat(91));
    let integer = br#"[{"step":0,"payload":{"n":18446744073709551616}}]"#;
    let deep = br#"[{"step":0,"payload":{"a":[[[[[[]]]]]]}}]"#;
    for bytes in [long.as_bytes(), integer.as_slice(), deep.as_slice()] {
        let result = decoded(bytes);
        assert_eq!(result.result, Err(TransportError::InvalidJson));
        assert_eq!(result.usage.charged_bytes, 0);
        assert_eq!(result.usage.returned_owned_bytes, 0);
    }
}

#[test]
fn ninth_entry_refuses_before_any_new_inventory_owner() {
    let entry = r#"{"step":0,"payload":{}}"#;
    let json = format!("[{}]", [entry; 9].join(","));
    let outcome = decoded(json.as_bytes());
    assert_eq!(outcome.result, Err(TransportError::InvalidJson));
    assert_eq!(outcome.usage.charged_bytes, lexical::OPAQUE_BYTES);
    assert_eq!(outcome.usage.returned_owned_bytes, 0);
    let field = RetainedField::Present(
        (0..9)
            .map(|step| RetainedStepPayload {
                step,
                payload: b"{}".to_vec(),
            })
            .collect(),
    );
    assert!(matches!(
        encode(RETAINED_SCHEMA, &field, &limits(), end(), &mut |_, _| true).result,
        Err(TransportError::Limit {
            resource: "retained entries",
            ..
        })
    ));
}

#[test]
fn outer_depth_admission_ignores_brackets_in_strings_but_bounds_rawvalue_stack() {
    admit_outer_json(
        br#"{"legacy":"[[[\\\"}}}","retained":[]}"#,
        end(),
        &mut |_, _| true,
    )
    .result
    .unwrap();
    let exact = format!("{}0{}", "[".repeat(127), "]".repeat(127));
    admit_outer_json(exact.as_bytes(), end(), &mut |_, _| true)
        .result
        .unwrap();
    let over = format!("[{exact}]");
    let refused = admit_outer_json(over.as_bytes(), end(), &mut |_, _| true);
    assert_eq!(refused.result, Err(TransportError::InvalidJson));
    assert_eq!(refused.usage.charged_bytes, 0);
    // This does not claim to parse or allocate-price legacy String contents.
    let legacy = format!(r#"{{"legacy":"{}"}}"#, "x".repeat(4096));
    admit_outer_json(legacy.as_bytes(), end(), &mut |_, _| true)
        .result
        .unwrap();
}
