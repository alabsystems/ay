// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::{cell::Cell, fmt::Write as _, time::Duration};

mod controls;

const LEGACY_FIELDS: [(&str, &str); 10] = [
    ("steps", "[]"),
    ("term_entries", "[]"),
    ("true_term", "null"),
    ("false_term", "null"),
    ("var_counter", "0"),
    ("obligation_assertions", "[]"),
    ("datatype_declarations", "[]"),
    ("constructor_selectors", "[]"),
    ("datatype_member_signatures", "[]"),
    ("declared_function_identities", "[]"),
];

fn end() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

fn document(schema: &str, retained: Option<&str>, omitted: Option<&str>) -> String {
    let mut fields = Vec::new();
    if omitted != Some("schema") {
        fields.push(format!("\"schema\":\"{schema}\""));
    }
    for (name, value) in LEGACY_FIELDS {
        if omitted != Some(name) {
            fields.push(format!("\"{name}\":{value}"));
        }
    }
    if let Some(value) = retained {
        fields.push(format!("\"retained\":{value}"));
    }
    format!("{{{}}}", fields.join(","))
}

fn checked(bytes: &[u8]) -> TransportOutcome<OuterView<'_>> {
    control::run(end(), &mut |_, _| true, |control| {
        read(bytes, bytes.len(), control)
    })
}

fn escaped(value: &str) -> String {
    let mut escaped = String::new();
    for byte in value.bytes() {
        write!(escaped, "\\u{byte:04x}").expect("writing to a String cannot fail");
    }
    escaped
}

fn present(term: NullableTerm<'_>) -> &RawValue {
    match term {
        NullableTerm::Present(raw) => raw,
        NullableTerm::Absent => panic!("explicit nullable field disappeared"),
    }
}

#[test]
fn legacy_and_retained_envelopes_preserve_all_raw_borrows_and_schema_identity() {
    for (schema, retained, encoding) in [
        (SNAPSHOT_SCHEMA, None, BundleEncoding::SnapshotV5),
        (RETAINED_SCHEMA, Some("[]"), BundleEncoding::RetainedV6),
        (
            RETAINED_SCHEMA,
            Some("[ {\"step\":7,\"payload\":{\"unvalidated\":true}} ]"),
            BundleEncoding::RetainedV6,
        ),
    ] {
        let json = document(schema, retained, None);
        let outcome = checked(json.as_bytes());
        assert_eq!(outcome.usage.returned_owned_bytes, 0);
        let view = outcome.result.unwrap();
        assert_eq!(view.encoding, encoding);
        assert_eq!(view.fields.schema.get(), format!("\"{schema}\""));
        let raw = [
            view.fields.steps,
            view.fields.term_entries,
            present(view.fields.true_term),
            present(view.fields.false_term),
            view.fields.var_counter,
            view.fields.obligation_assertions,
            view.fields.datatype_declarations,
            view.fields.constructor_selectors,
            view.fields.datatype_member_signatures,
            view.fields.declared_function_identities,
        ];
        let range = json.as_ptr() as usize..json.as_ptr() as usize + json.len();
        for (field, (_, expected)) in raw.into_iter().zip(LEGACY_FIELDS) {
            assert_eq!(field.get(), expected);
            assert!(range.contains(&(field.get().as_ptr() as usize)));
        }
        match (view.fields.retained, retained) {
            (BorrowedField::Absent, None) => {}
            (BorrowedField::Present(bytes), Some(expected)) => {
                assert_eq!(bytes, expected.as_bytes());
                assert!(range.contains(&(bytes.as_ptr() as usize)));
            }
            _ => panic!("schema/presence changed"),
        }
    }
}

#[test]
fn fully_escaped_known_keys_and_schema_keep_exact_borrowed_bytes() {
    let mut json = document(RETAINED_SCHEMA, Some("[]"), None);
    for name in ["schema", "retained"]
        .into_iter()
        .chain(LEGACY_FIELDS.into_iter().map(|(name, _)| name))
    {
        json = json.replace(&format!("\"{name}\""), &format!("\"{}\"", escaped(name)));
    }
    json = json.replace(RETAINED_SCHEMA, &escaped(RETAINED_SCHEMA));
    let view = checked(json.as_bytes()).result.unwrap();
    assert_eq!(view.encoding, BundleEncoding::RetainedV6);
    assert_eq!(
        view.fields.schema.get(),
        format!("\"{}\"", escaped(RETAINED_SCHEMA))
    );
    assert_eq!(view.fields.retained, BorrowedField::Present(b"[]"));
}

#[test]
fn duplicate_escaped_equivalent_keys_and_unknown_aliases_refuse() {
    let base = document(RETAINED_SCHEMA, Some("[]"), None);
    for (name, value) in LEGACY_FIELDS
        .into_iter()
        .chain([("schema", "\"ay.proofbundle/v6\""), ("retained", "[]")])
    {
        let duplicate = base.replacen('{', &format!("{{\"{}\":{value},", escaped(name)), 1);
        assert!(checked(duplicate.as_bytes()).result.is_err(), "{name}");
    }
    for name in ["unknown", "retained_bv"] {
        let unknown = base.replacen('{', &format!("{{\"{name}\":[],"), 1);
        assert!(checked(unknown.as_bytes()).result.is_err());
    }
}

#[test]
fn schema_and_seven_nonnullable_legacy_fields_must_be_present() {
    for (schema, retained) in [(SNAPSHOT_SCHEMA, None), (RETAINED_SCHEMA, Some("[]"))] {
        for omitted in ["schema"].into_iter().chain(
            LEGACY_FIELDS
                .into_iter()
                .filter(|(_, value)| *value != "null")
                .map(|(name, _)| name),
        ) {
            let json = document(schema, retained, Some(omitted));
            assert!(checked(json.as_bytes()).result.is_err(), "{omitted}");
        }
    }
}

#[test]
fn omitted_nullable_terms_match_public_v5_and_preserve_explicit_null_presence() {
    for omitted in 0..4 {
        let make = |schema, retained| {
            let mut json = document(schema, retained, None);
            for (bit, name) in [(1, "true_term"), (2, "false_term")] {
                if omitted & bit != 0 {
                    json = json.replace(&format!("\"{name}\":null,"), "");
                }
            }
            json
        };
        let legacy = make(SNAPSHOT_SCHEMA, None);
        let original: crate::bundle::SerializableProofBundle =
            serde_json::from_str(&legacy).unwrap();
        assert_eq!(original.true_term, None);
        assert_eq!(original.false_term, None);
        for (schema, retained) in [(SNAPSHOT_SCHEMA, None), (RETAINED_SCHEMA, Some("[]"))] {
            let json = make(schema, retained);
            let view = checked(json.as_bytes()).result.unwrap();
            let range = json.as_ptr() as usize..json.as_ptr() as usize + json.len();
            for (bit, term) in [(1, view.fields.true_term), (2, view.fields.false_term)] {
                if omitted & bit != 0 {
                    assert!(matches!(term, NullableTerm::Absent));
                } else {
                    let raw = present(term);
                    assert_eq!(raw.get(), "null");
                    assert!(range.contains(&(raw.get().as_ptr() as usize)));
                }
            }
        }
    }
}

#[test]
fn schema_presence_null_and_field_type_boundaries_refuse_without_legacy_decode() {
    for (schema, retained) in [
        (SNAPSHOT_SCHEMA, Some("[]")),
        (SNAPSHOT_SCHEMA, Some("[{}]")),
        (SNAPSHOT_SCHEMA, Some("null")),
        (RETAINED_SCHEMA, None),
        (RETAINED_SCHEMA, Some("null")),
        (RETAINED_SCHEMA, Some("{}")),
        ("ay.proofbundle/v999", Some("[]")),
    ] {
        let json = document(schema, retained, None);
        assert!(checked(json.as_bytes()).result.is_err());
    }
    let base = document(SNAPSHOT_SCHEMA, None, None);
    for (name, value) in LEGACY_FIELDS {
        if value == "null" {
            continue;
        }
        for bad in ["null", "{}", "true", "\"string\""] {
            let json = base.replace(&format!("\"{name}\":{value}"), &format!("\"{name}\":{bad}"));
            assert!(checked(json.as_bytes()).result.is_err(), "{name}/{bad}");
        }
    }
    let null_schema = base.replace("\"ay.proofbundle/v5\"", "null");
    assert!(checked(null_schema.as_bytes()).result.is_err());
}

#[test]
fn u32_metadata_accepts_maximum_and_refuses_signed_float_or_overflow_values() {
    let base = document(SNAPSHOT_SCHEMA, None, None);
    for (name, original) in [
        ("var_counter", "0"),
        ("true_term", "null"),
        ("false_term", "null"),
    ] {
        let key = format!("\"{name}\":{original}");
        let maximum = base.replace(&key, &format!("\"{name}\":4294967295"));
        assert!(checked(maximum.as_bytes()).result.is_ok());
        for bad in [
            "-1",
            "1.0",
            "1e0",
            "4294967296",
            "18446744073709551615",
            "[]",
        ] {
            let json = base.replace(&key, &format!("\"{name}\":{bad}"));
            assert!(checked(json.as_bytes()).result.is_err(), "{name}/{bad}");
        }
    }
}

#[test]
fn oversized_metadata_refuses_but_nested_legacy_strings_remain_borrowed() {
    let base = document(SNAPSHOT_SCHEMA, None, None);
    let long = "a".repeat(admission::MAX_METADATA_BYTES + 1);
    let huge = "a".repeat(64 * 1024);
    for json in [
        base.replacen("schema", &long, 1),
        base.replacen(SNAPSHOT_SCHEMA, &long, 1),
        base.replacen("schema", &escaped(&long), 1),
        base.replacen("schema", &huge, 1),
        base.replacen(SNAPSHOT_SCHEMA, &huge, 1),
    ] {
        assert!(matches!(
            checked(json.as_bytes()).result,
            Err(TransportError::InvalidShape("outer metadata too long"))
        ));
    }
    let nested = base.replace("\"steps\":[]", &format!("\"steps\":[\"{long}\"]"));
    let view = checked(nested.as_bytes()).result.unwrap();
    assert_eq!(view.fields.steps.get(), format!("[\"{long}\"]"));
    // A string is not a valid ProofStep. This deliberately proves that the
    // borrowed envelope has NOT pretended to authenticate nested legacy data.
}

#[test]
fn malformed_structure_trailing_data_and_excessive_depth_refuse() {
    for json in ["null", "[]", "{}", "{", "{\"schema\":true}"] {
        assert!(checked(json.as_bytes()).result.is_err());
    }
    let base = document(SNAPSHOT_SCHEMA, None, None);
    for json in [
        format!("\"{}\"", "a".repeat(64 * 1024)),
        "[\"ay.proofbundle/v5\",[],[],null,null,0,[],[],[],[]]".to_owned(),
        format!("{base} null"),
        base.replace("\"steps\":[]", "\"steps\":[}"),
        base.replace(
            "\"steps\":[]",
            &format!("\"steps\":{}0{}", "[".repeat(128), "]".repeat(128)),
        ),
    ] {
        assert!(checked(json.as_bytes()).result.is_err());
    }
}
