// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn finite_field_kinds_append_without_moving_existing_ordinals() {
    type Error = serde::de::value::Error;
    assert_eq!(VARIANTS[75], "IntCgCutChain");
    assert_eq!(VARIANTS[76], "BvMulOverflowDivision");
    assert_eq!(VARIANTS[77], "BvUremBound");
    assert_eq!(VARIANTS[78], "FiniteFieldExhaustive");
    assert!(matches!(
        VariantTagVisitor.visit_u64::<Error>(78),
        Ok(VariantTag::FiniteFieldExhaustive)
    ));
    assert!(matches!(
        VariantTagVisitor.visit_u64::<Error>(0),
        Ok(VariantTag::EufTransitive)
    ));
    assert!(matches!(
        VariantTagVisitor.visit_u64::<Error>(75),
        Ok(VariantTag::IntCgCutChain)
    ));
    assert!(matches!(
        VariantTagVisitor.visit_u64::<Error>(76),
        Ok(VariantTag::BvMulOverflowDivision)
    ));
    assert!(matches!(
        VariantTagVisitor.visit_u64::<Error>(77),
        Ok(VariantTag::BvUremBound)
    ));
    assert!(matches!(
        VariantTagVisitor.visit_u64::<Error>(80),
        Ok(VariantTag::FiniteFieldLinearWide)
    ));
    assert!(matches!(
        VariantTagVisitor.visit_u64::<Error>(81),
        Ok(VariantTag::FiniteFieldQuadratic)
    ));
    assert!(matches!(
        VariantTagVisitor.visit_u64::<Error>(82),
        Ok(VariantTag::FiniteFieldUnivariate)
    ));
    assert_eq!(VARIANTS[83], "FiniteFieldIdeal");
    assert!(matches!(
        VariantTagVisitor.visit_u64::<Error>(83),
        Ok(VariantTag::FiniteFieldIdeal)
    ));
    assert!(VariantTagVisitor.visit_u64::<Error>(u64::MAX).is_err());
    assert!(matches!(
        VariantTagVisitor.visit_bytes::<Error>(b"BvUremBound"),
        Ok(VariantTag::BvUremBound)
    ));
}

#[test]
fn finite_field_native_kinds_roundtrip_without_claiming_external_proof() {
    for kind in [
        TheoryLemmaKind::FiniteFieldQuadratic,
        TheoryLemmaKind::FiniteFieldUnivariate,
        TheoryLemmaKind::FiniteFieldIdeal,
    ] {
        let text = serde_json::to_string(&kind).unwrap();
        assert_eq!(
            serde_json::from_str::<TheoryLemmaKind>(&text).unwrap(),
            kind
        );
        assert!(serde_json::from_str::<TheoryLemmaKind>(&format!(
            r#"{{"{kind:?}":{{"roots":[2]}}}}"#
        ))
        .is_err());
        assert_eq!(kind.alethe_wire_rule(), "hole");
        assert!(!kind.is_trust());
    }
}

#[test]
fn remainder_bound_roundtrips_as_a_payload_free_theory_kind() {
    let text = serde_json::to_string(&TheoryLemmaKind::BvUremBound).unwrap();
    assert_eq!(text, "\"BvUremBound\"");
    assert_eq!(
        serde_json::from_str::<TheoryLemmaKind>(&text).unwrap(),
        TheoryLemmaKind::BvUremBound
    );
    assert_eq!(TheoryLemmaKind::BvUremBound.alethe_rule(), "bv_urem_bound");
    assert!(serde_json::from_str::<TheoryLemmaKind>(r#"{"BvUremBound":{"width":32}}"#).is_err());
}
