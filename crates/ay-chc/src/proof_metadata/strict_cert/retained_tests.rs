// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Wire commitment tests only: no metadata row mints source/proof authority.

use super::*;

const ALETHE: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
const BUNDLE: &str = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";

fn parse(value: &serde_json::Value) -> (Option<ChcObligationStrictCert>, Vec<String>) {
    let wrapper = serde_json::json!({ "strict_cert": value });
    let mut reasons = Vec::new();
    let parsed = ChcObligationStrictCert::from_json_value_opt(
        wrapper.as_object().unwrap(),
        "strict_cert",
        "strict_cert",
        &mut reasons,
    );
    (parsed, reasons)
}

fn assert_rejected(value: &serde_json::Value) {
    let (parsed, reasons) = parse(value);
    assert!(parsed.is_none(), "crossed metadata accepted: {value}");
    assert!(
        !reasons.is_empty(),
        "present malformed metadata needs a reason"
    );
}

fn retained(alethe: Option<String>) -> ChcObligationStrictCert {
    ChcObligationStrictCert::new_retained(alethe, BUNDLE, "verified")
}

#[test]
fn legacy_v1_and_v2_json_and_identity_bytes_remain_literal_golden_compatible() {
    let v1 = ChcObligationStrictCert::new_legacy(ALETHE, BUNDLE, "verified");
    assert_eq!(v1.to_json_value().to_string(), concat!(
        "{\"alethe_sha256\":\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\",",
        "\"bundle_sha256\":\"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\",",
        "\"schema\":\"ay.chc-obligation-strict-alethe-cert/v1\",\"schema_version\":1,\"verdict\":\"verified\"}",
    ));
    assert_eq!(
        v1.identity_input(),
        concat!(
            "ay.chc-obligation-strict-alethe-cert/v1\n",
            "alethe_sha256=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n",
            "bundle_sha256=bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n",
            "verdict=\"verified\"\n",
        )
    );
    assert!(!v1.is_current_bundle_commitment());
    assert!(!v1.is_retained_bundle_commitment());
    for diagnostic in [None, Some(ALETHE.to_string())] {
        let v2 = ChcObligationStrictCert::new_bundle(
            ay_dpll::api::PROOF_BUNDLE_SCHEMA,
            diagnostic.clone(),
            BUNDLE,
            "verified",
        );
        let fields = concat!(
            "\"bundle_sha256\":\"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\",",
            "\"proof_bundle_schema\":\"ay.proofbundle/v5\",\"proof_checker\":\"ay-proof::re_check_bundle_strict\",",
            "\"schema\":\"ay.chc-obligation-strict-proof-bundle-cert/v2\",\"schema_version\":2,\"verdict\":\"verified\"}",
        );
        let prefix = diagnostic.as_ref().map_or("{".to_string(), |digest| {
            format!("{{\"alethe_sha256\":\"{digest}\",")
        });
        assert_eq!(v2.to_json_value().to_string(), prefix + fields);
        assert_eq!(
            v2.identity_input(),
            format!(
                concat!(
            "ay.chc-obligation-strict-proof-bundle-cert/v2\n",
            "proof_checker=\"ay-proof::re_check_bundle_strict\"\n",
            "proof_bundle_schema=\"ay.proofbundle/v5\"\n",
            "bundle_sha256=bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n",
            "alethe_present={}\nalethe_sha256={}\nverdict=\"verified\"\n",
        ),
                diagnostic.is_some(),
                diagnostic.as_deref().unwrap_or("none")
            )
        );
        let (parsed, reasons) = parse(&v2.to_json_value());
        assert_eq!(reasons, [] as [std::string::String; 0]);
        assert_eq!(parsed.unwrap(), v2);
        assert!(v2.is_current_bundle_commitment());
        assert!(!v2.is_retained_bundle_commitment());
    }
    let (parsed, reasons) = parse(&v1.to_json_value());
    assert_eq!(reasons, [] as [std::string::String; 0]);
    assert_eq!(parsed.unwrap(), v1);
}

#[test]
fn retained_v3_roundtrip_binds_exact_checker_v4_and_optional_diagnostic_identity() {
    for diagnostic in [None, Some(ALETHE.to_string())] {
        let cert = retained(diagnostic.clone());
        let value = cert.to_json_value();
        assert_eq!(
            value["schema"],
            "ay.chc-obligation-strict-retained-proof-bundle-cert/v3"
        );
        assert_eq!(value["schema_version"], 3);
        assert_eq!(
            value["proof_checker"],
            "ay-proof::re_check_retained_bundle_strict_with_resource_control"
        );
        assert_eq!(
            value["proof_bundle_schema"],
            ay_dpll::api::RETAINED_PROOF_BUNDLE_SCHEMA
        );
        assert_eq!(
            value
                .get("alethe_sha256")
                .and_then(serde_json::Value::as_str),
            diagnostic.as_deref()
        );
        assert_eq!(
            cert.identity_input(),
            format!(
                concat!(
            "ay.chc-obligation-strict-retained-proof-bundle-cert/v3\n",
            "schema_version=3\n",
            "proof_checker=\"ay-proof::re_check_retained_bundle_strict_with_resource_control\"\n",
            "proof_bundle_schema=\"ay.proofbundle/v6\"\n",
            "bundle_sha256=bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n",
            "alethe_present={}\nalethe_sha256={}\nverdict=\"verified\"\n",
        ),
                diagnostic.is_some(),
                diagnostic.as_deref().unwrap_or("none")
            )
        );
        let (parsed, reasons) = parse(&value);
        assert_eq!(reasons, [] as [std::string::String; 0]);
        assert_eq!(parsed.unwrap(), cert);
        assert!(cert.is_current_bundle_commitment());
        assert!(cert.is_retained_bundle_commitment());
    }
    assert_ne!(
        retained(None).identity_input(),
        retained(Some(ALETHE.to_string())).identity_input()
    );
}

#[test]
fn all_schema_version_checker_bundle_crossings_refuse_without_any_legacy_fallback() {
    let schemas = [
        CHC_OBLIGATION_STRICT_CERT_LEGACY_SCHEMA,
        CHC_OBLIGATION_STRICT_CERT_SCHEMA,
        CHC_OBLIGATION_STRICT_CERT_RETAINED_SCHEMA,
    ];
    let checkers = [
        None,
        Some(CHC_STRICT_PROOF_BUNDLE_CHECKER),
        Some(CHC_STRICT_RETAINED_PROOF_BUNDLE_CHECKER),
    ];
    let bundles = [
        None,
        Some(ay_dpll::api::PROOF_BUNDLE_SCHEMA),
        Some(ay_dpll::api::RETAINED_PROOF_BUNDLE_SCHEMA),
    ];
    for (schema_index, schema) in schemas.into_iter().enumerate() {
        for version_index in 0..3 {
            for (checker_index, checker) in checkers.into_iter().enumerate() {
                for (bundle_index, bundle_schema) in bundles.into_iter().enumerate() {
                    let mut value = retained(Some(ALETHE.to_string())).to_json_value();
                    value["schema"] = serde_json::json!(schema);
                    value["schema_version"] = serde_json::json!(version_index + 1);
                    for (key, field) in [
                        ("proof_checker", checker),
                        ("proof_bundle_schema", bundle_schema),
                    ] {
                        if let Some(field) = field {
                            value[key] = serde_json::json!(field);
                        } else {
                            value.as_object_mut().unwrap().remove(key);
                        }
                    }
                    let matches = schema_index == version_index
                        && schema_index == checker_index
                        && schema_index == bundle_index;
                    if matches {
                        let (parsed, reasons) = parse(&value);
                        assert_eq!(reasons, [] as [std::string::String; 0]);
                        let cert = parsed.unwrap();
                        assert_eq!(cert.is_current_bundle_commitment(), schema_index != 0);
                        assert_eq!(cert.is_retained_bundle_commitment(), schema_index == 2);
                    } else {
                        assert_rejected(&value);
                    }
                }
            }
        }
    }
}

#[test]
fn retained_commitment_rejects_missing_null_unknown_and_incomplete_authority_fields() {
    let valid = retained(None).to_json_value();
    for field in [
        "schema",
        "schema_version",
        "proof_checker",
        "proof_bundle_schema",
        "bundle_sha256",
        "verdict",
    ] {
        let mut missing = valid.clone();
        missing.as_object_mut().unwrap().remove(field);
        assert_rejected(&missing);
        let mut null = valid.clone();
        null[field] = serde_json::Value::Null;
        assert_rejected(&null);
    }
    for (field, replacement) in [
        ("schema", serde_json::json!("unknown")),
        ("schema_version", serde_json::json!(0)),
        ("schema_version", serde_json::json!(4)),
        ("schema_version", serde_json::json!(99)),
        ("schema_version", serde_json::json!(-1)),
        ("schema_version", serde_json::json!("3")),
        ("schema_version", serde_json::json!(3.5)),
        ("proof_checker", serde_json::json!("unknown")),
        ("proof_bundle_schema", serde_json::json!("unknown")),
        ("verdict", serde_json::json!("incomplete")),
        ("verdict", serde_json::json!("decision-only")),
        ("verdict", serde_json::json!("rejected")),
    ] {
        let mut value = valid.clone();
        value[field] = replacement;
        assert_rejected(&value);
    }
}

#[test]
fn malformed_required_or_optional_digests_refuse_but_absent_alethe_stays_diagnostic_only() {
    let valid = retained(None).to_json_value();
    for digest in [
        serde_json::json!(""),
        serde_json::json!("short"),
        serde_json::json!("A".repeat(64)),
        serde_json::json!("x".repeat(64)),
        serde_json::json!("b".repeat(63)),
        serde_json::json!("b".repeat(65)),
        serde_json::json!(17),
    ] {
        for field in ["bundle_sha256", "alethe_sha256"] {
            let mut value = valid.clone();
            value[field] = digest.clone();
            assert_rejected(&value);
        }
    }
    let mut diagnostic_null = valid.clone();
    diagnostic_null["alethe_sha256"] = serde_json::Value::Null;
    let (parsed, reasons) = parse(&diagnostic_null);
    assert_eq!(reasons, [] as [std::string::String; 0]);
    assert_eq!(parsed.unwrap(), retained(None));
}

#[test]
fn identical_digest_diagnostics_and_verdict_never_alias_legacy_and_retained_identities() {
    let v1 = ChcObligationStrictCert::new_legacy(ALETHE, BUNDLE, "verified");
    let v2 = ChcObligationStrictCert::new_bundle(
        ay_dpll::api::PROOF_BUNDLE_SCHEMA,
        Some(ALETHE.to_string()),
        BUNDLE,
        "verified",
    );
    let v3 = retained(Some(ALETHE.to_string()));
    let identities = [
        v1.identity_input(),
        v2.identity_input(),
        v3.identity_input(),
    ];
    for (index, identity) in identities.iter().enumerate() {
        for other in &identities[..index] {
            assert_ne!(identity, other);
            assert_ne!(
                super::super::sha256_hex(identity.as_bytes()),
                super::super::sha256_hex(other.as_bytes())
            );
        }
    }
}
