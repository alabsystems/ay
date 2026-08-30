// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Versioned strict proof-bundle commitments for checked replay rows.

use super::{
    expect_json_string, json_string, optional_sha256_field, sha256_string_field, string_field,
    u64_field,
};

/// Legacy schema tag for native strict rows that required an Alethe digest.
/// Parsing remains supported so already-recorded transcripts round-trip.
pub(crate) const CHC_OBLIGATION_STRICT_CERT_LEGACY_SCHEMA: &str =
    "ay.chc-obligation-strict-alethe-cert/v1";

/// Current schema tag for an independently rechecked proof-bundle commitment.
/// Alethe is an optional diagnostic and never the authority represented here.
pub(crate) const CHC_OBLIGATION_STRICT_CERT_SCHEMA: &str =
    "ay.chc-obligation-strict-proof-bundle-cert/v2";

/// Exact checker surface whose successful complete result authorizes v2 rows.
pub(crate) const CHC_STRICT_PROOF_BUNDLE_CHECKER: &str = "ay-proof::re_check_bundle_strict";

/// Wire form retained by one strict-certificate row.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ChcObligationStrictCertWire {
    /// Historical Alethe-required row.
    LegacyV1,
    /// Bundle-authoritative row with optional Alethe diagnostics.
    BundleV2,
}

/// Strict proof-bundle commitments for one UNSAT replay obligation.
///
/// A v2 row records that AY's producer-independent bundle checker accepted the
/// exact query-bound bundle with complete quality. It retains the serialized
/// bundle's digest, not its bytes: the row is an in-process checked commitment,
/// not standalone/offline evidence. Standalone replay would require a future
/// evidence-carriage extension. Alethe is an optional presentation digest only;
/// absence is represented explicitly and never fabricated. Legacy v1
/// Alethe-required rows remain parseable without changing the surrounding
/// checked-summary/transcript v1 schemas.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcObligationStrictCert {
    /// SHA-256 over rendered Alethe text when that diagnostic surface exists.
    pub alethe_sha256: Option<String>,
    /// SHA-256 commitment to the serialized proof bundle.
    pub bundle_sha256: String,
    /// Exact serialized bundle schema checked by the v2 authority surface.
    pub proof_bundle_schema: String,
    /// Strict checker verdict — `"verified"` for any recorded cert.
    pub verdict: String,
    wire: ChcObligationStrictCertWire,
}

impl ChcObligationStrictCert {
    /// Build a v2 bundle-authoritative record from the bound digests.
    pub(crate) fn new_bundle(
        proof_bundle_schema: impl Into<String>,
        alethe_sha256: Option<String>,
        bundle_sha256: impl Into<String>,
        verdict: impl Into<String>,
    ) -> Self {
        Self {
            alethe_sha256,
            bundle_sha256: bundle_sha256.into(),
            proof_bundle_schema: proof_bundle_schema.into(),
            verdict: verdict.into(),
            wire: ChcObligationStrictCertWire::BundleV2,
        }
    }

    fn new_legacy(
        alethe_sha256: impl Into<String>,
        bundle_sha256: impl Into<String>,
        verdict: impl Into<String>,
    ) -> Self {
        Self {
            alethe_sha256: Some(alethe_sha256.into()),
            bundle_sha256: bundle_sha256.into(),
            proof_bundle_schema: String::new(),
            verdict: verdict.into(),
            wire: ChcObligationStrictCertWire::LegacyV1,
        }
    }

    /// Render the certificate record as JSON.
    pub fn to_json_value(&self) -> serde_json::Value {
        match self.wire {
            ChcObligationStrictCertWire::LegacyV1 => serde_json::json!({
                "schema": CHC_OBLIGATION_STRICT_CERT_LEGACY_SCHEMA,
                "schema_version": 1,
                "alethe_sha256": self.alethe_sha256,
                "bundle_sha256": self.bundle_sha256,
                "verdict": self.verdict,
            }),
            ChcObligationStrictCertWire::BundleV2 => {
                let mut value = serde_json::json!({
                    "schema": CHC_OBLIGATION_STRICT_CERT_SCHEMA,
                    "schema_version": 2,
                    "proof_checker": CHC_STRICT_PROOF_BUNDLE_CHECKER,
                    "proof_bundle_schema": self.proof_bundle_schema,
                    "bundle_sha256": self.bundle_sha256,
                    "verdict": self.verdict,
                });
                if let Some(alethe_sha256) = &self.alethe_sha256 {
                    value["alethe_sha256"] = serde_json::Value::String(alethe_sha256.clone());
                }
                value
            }
        }
    }

    /// Parse an OPTIONAL strict-cert record. Absence returns `None` with no
    /// reason (backward compatible); a present-but-malformed record pushes a
    /// reason and returns `None`.
    pub(super) fn from_json_value_opt(
        object: &serde_json::Map<String, serde_json::Value>,
        key: &str,
        label: &str,
        reasons: &mut Vec<String>,
    ) -> Option<Self> {
        match object.get(key) {
            None | Some(serde_json::Value::Null) => None,
            Some(value) => Self::parse_present(value, label, reasons),
        }
    }

    fn parse_present(
        value: &serde_json::Value,
        label: &str,
        reasons: &mut Vec<String>,
    ) -> Option<Self> {
        let Some(object) = value.as_object() else {
            reasons.push(format!("{label} is not an object"));
            return None;
        };
        let schema = string_field(object, "schema", &format!("{label}.schema"), reasons)?;
        let schema_version = u64_field(
            object,
            "schema_version",
            &format!("{label}.schema_version"),
            reasons,
        )?;
        let verdict = string_field(object, "verdict", &format!("{label}.verdict"), reasons)?;
        if verdict != "verified" {
            reasons.push(format!(
                "{label}.verdict={}, expected 'verified'",
                json_string(&verdict)
            ));
            return None;
        }
        match (schema.as_str(), schema_version) {
            (CHC_OBLIGATION_STRICT_CERT_LEGACY_SCHEMA, 1) => {
                Self::parse_legacy(object, label, verdict, reasons)
            }
            (CHC_OBLIGATION_STRICT_CERT_SCHEMA, 2) => {
                Self::parse_bundle(object, label, verdict, reasons)
            }
            _ => {
                reasons.push(format!(
                    "{label} has unsupported strict-cert schema/version {}/{}",
                    json_string(&schema),
                    schema_version
                ));
                None
            }
        }
    }

    fn parse_legacy(
        object: &serde_json::Map<String, serde_json::Value>,
        label: &str,
        verdict: String,
        reasons: &mut Vec<String>,
    ) -> Option<Self> {
        let alethe_sha256 = sha256_string_field(
            object,
            "alethe_sha256",
            &format!("{label}.alethe_sha256"),
            reasons,
        )?;
        let bundle_sha256 = sha256_string_field(
            object,
            "bundle_sha256",
            &format!("{label}.bundle_sha256"),
            reasons,
        )?;
        Some(Self::new_legacy(alethe_sha256, bundle_sha256, verdict))
    }

    fn parse_bundle(
        object: &serde_json::Map<String, serde_json::Value>,
        label: &str,
        verdict: String,
        reasons: &mut Vec<String>,
    ) -> Option<Self> {
        let reason_count = reasons.len();
        expect_json_string(
            object,
            "proof_checker",
            CHC_STRICT_PROOF_BUNDLE_CHECKER,
            &format!("{label}.proof_checker"),
            reasons,
        );
        expect_json_string(
            object,
            "proof_bundle_schema",
            ay_dpll::api::PROOF_BUNDLE_SCHEMA,
            &format!("{label}.proof_bundle_schema"),
            reasons,
        );
        let proof_bundle_schema = string_field(
            object,
            "proof_bundle_schema",
            &format!("{label}.proof_bundle_schema"),
            reasons,
        )?;
        let alethe_sha256 = optional_sha256_field(
            object,
            "alethe_sha256",
            &format!("{label}.alethe_sha256"),
            reasons,
        );
        let bundle_sha256 = sha256_string_field(
            object,
            "bundle_sha256",
            &format!("{label}.bundle_sha256"),
            reasons,
        )?;
        if reasons.len() != reason_count {
            return None;
        }
        Some(Self::new_bundle(
            proof_bundle_schema,
            alethe_sha256,
            bundle_sha256,
            verdict,
        ))
    }

    pub(super) fn identity_input(&self) -> String {
        match self.wire {
            ChcObligationStrictCertWire::LegacyV1 => format!(
                "{}\nalethe_sha256={}\nbundle_sha256={}\nverdict={}\n",
                CHC_OBLIGATION_STRICT_CERT_LEGACY_SCHEMA,
                self.alethe_sha256.as_deref().unwrap_or(""),
                self.bundle_sha256,
                json_string(&self.verdict),
            ),
            ChcObligationStrictCertWire::BundleV2 => {
                let (alethe_present, alethe_sha256) = self
                    .alethe_sha256
                    .as_deref()
                    .map_or((false, "none"), |digest| (true, digest));
                format!(
                    "{}\nproof_checker={}\nproof_bundle_schema={}\nbundle_sha256={}\nalethe_present={}\nalethe_sha256={}\nverdict={}\n",
                    CHC_OBLIGATION_STRICT_CERT_SCHEMA,
                    json_string(CHC_STRICT_PROOF_BUNDLE_CHECKER),
                    json_string(&self.proof_bundle_schema),
                    self.bundle_sha256,
                    alethe_present,
                    alethe_sha256,
                    json_string(&self.verdict),
                )
            }
        }
    }
}
