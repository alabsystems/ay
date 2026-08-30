// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Strict proof-certificate schema compatibility and rejection tests.

use super::*;
use crate::proof_metadata::strict_cert::{
    CHC_OBLIGATION_STRICT_CERT_LEGACY_SCHEMA, CHC_OBLIGATION_STRICT_CERT_SCHEMA,
};

fn parse_cert(value: serde_json::Value) -> ChcObligationStrictCert {
    let wrapper = serde_json::json!({ "strict_cert": value });
    let mut reasons = Vec::new();
    let cert = ChcObligationStrictCert::from_json_value_opt(
        wrapper.as_object().expect("wrapper object"),
        "strict_cert",
        "strict_cert",
        &mut reasons,
    )
    .unwrap_or_else(|| panic!("strict cert should parse: {reasons:?}"));
    assert!(reasons.is_empty(), "strict cert parse reasons: {reasons:?}");
    cert
}

#[test]
fn strict_certificate_json_roundtrips_legacy_v1_and_bundle_v2_with_optional_alethe() {
    let alethe = "a".repeat(64);
    let bundle = "b".repeat(64);
    let legacy_json = serde_json::json!({
        "schema": CHC_OBLIGATION_STRICT_CERT_LEGACY_SCHEMA,
        "schema_version": 1,
        "alethe_sha256": alethe,
        "bundle_sha256": bundle,
        "verdict": "verified",
    });
    let legacy = parse_cert(legacy_json.clone());
    assert_eq!(legacy.to_json_value(), legacy_json);
    assert!(legacy.alethe_sha256.is_some());
    assert_eq!(
        legacy.identity_input(),
        concat!(
            "ay.chc-obligation-strict-alethe-cert/v1\n",
            "alethe_sha256=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n",
            "bundle_sha256=bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n",
            "verdict=\"verified\"\n",
        ),
        "legacy v1 identity bytes must remain exactly stable"
    );

    for alethe_sha256 in [None, Some("c".repeat(64))] {
        let current = ChcObligationStrictCert::new_bundle(
            ay_dpll::api::PROOF_BUNDLE_SCHEMA,
            alethe_sha256.clone(),
            "d".repeat(64),
            "verified",
        );
        let json = current.to_json_value();
        assert_eq!(json["schema"], CHC_OBLIGATION_STRICT_CERT_SCHEMA);
        assert_eq!(json["schema_version"], 2);
        assert_eq!(
            json.get("alethe_sha256")
                .and_then(serde_json::Value::as_str),
            alethe_sha256.as_deref()
        );
        let reparsed = parse_cert(json);
        assert_eq!(reparsed, current);
        assert_eq!(reparsed.identity_input(), current.identity_input());
    }
}

#[test]
fn strict_certificate_json_rejects_malformed_or_unknown_bundle_authority() {
    let valid = ChcObligationStrictCert::new_bundle(
        ay_dpll::api::PROOF_BUNDLE_SCHEMA,
        None,
        "d".repeat(64),
        "verified",
    )
    .to_json_value();
    for mutation in [
        (
            "bundle_sha256",
            serde_json::Value::String("short".to_string()),
        ),
        (
            "alethe_sha256",
            serde_json::Value::String("short".to_string()),
        ),
        (
            "proof_checker",
            serde_json::Value::String("unknown-checker".to_string()),
        ),
        (
            "proof_bundle_schema",
            serde_json::Value::String("unknown-bundle-schema".to_string()),
        ),
        ("verdict", serde_json::Value::String("rejected".to_string())),
        (
            "schema",
            serde_json::Value::String("unknown-strict-cert-schema".to_string()),
        ),
        ("schema_version", serde_json::Value::from(99_u64)),
    ] {
        let mut malformed = valid.clone();
        malformed[mutation.0] = mutation.1;
        let wrapper = serde_json::json!({ "strict_cert": malformed });
        let mut reasons = Vec::new();
        let parsed = ChcObligationStrictCert::from_json_value_opt(
            wrapper.as_object().expect("wrapper object"),
            "strict_cert",
            "strict_cert",
            &mut reasons,
        );
        assert!(parsed.is_none(), "malformed cert unexpectedly parsed");
        assert!(
            !reasons.is_empty(),
            "malformed cert needs a rejection reason"
        );
    }
}
