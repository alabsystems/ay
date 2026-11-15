// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ProofStep;

fn rational(n: i64, d: i64) -> NraSosRational {
    NraSosRational {
        numerator: n.into(),
        denominator: d.into(),
    }
}

fn certificate() -> NraSosCertificate {
    NraSosCertificate {
        basis: vec![vec![]],
        gram: vec![vec![rational(0, 1)]],
        terms: vec![],
        rhs: rational(-1, 1),
    }
}

#[test]
fn payload_round_trip_preserves_exact_structure() {
    let original = ProofStep::NraSos {
        clause: vec![TermId::new(3)],
        certificate: certificate(),
    };
    let bytes = serde_json::to_vec(&original).unwrap();
    assert_eq!(
        serde_json::from_slice::<ProofStep>(&bytes).unwrap(),
        original
    );
    assert_ne!(rational(1, 2), rational(2, 4));
}

#[test]
fn payload_denies_unknown_fields() {
    let mut value = serde_json::to_value(certificate()).unwrap();
    value["invented_source"] = serde_json::json!([]);
    assert!(serde_json::from_value::<NraSosCertificate>(value).is_err());
}

#[test]
fn integer_decoder_rejects_oversized_and_noncanonical_limbs() {
    let mut value = serde_json::to_value(rational(1, 1)).unwrap();
    value["numerator"] = serde_json::json!([1, vec![1u32; 33]]);
    assert!(serde_json::from_value::<NraSosRational>(value.clone()).is_err());
    for invalid in [
        serde_json::json!([1, [1, 0]]),
        serde_json::json!([0, [1]]),
        serde_json::json!([1, []]),
        serde_json::json!([2, [1]]),
    ] {
        value["numerator"] = invalid;
        assert!(serde_json::from_value::<NraSosRational>(value.clone()).is_err());
    }
}

#[test]
fn integer_decoder_accepts_exact_width_boundary() {
    let mut value = serde_json::to_value(rational(1, 1)).unwrap();
    value["numerator"] = serde_json::json!([1, vec![u32::MAX; 32]]);
    let decoded: NraSosRational = serde_json::from_value(value).unwrap();
    assert_eq!(decoded.numerator.bits(), NraSosRational::MAX_BITS);
}

#[test]
fn certificate_decoder_bounds_every_nested_vector() {
    let original = serde_json::to_value(certificate()).unwrap();
    let mut value = original.clone();
    value["basis"] = serde_json::json!(vec![Vec::<u32>::new(); 46]);
    assert!(serde_json::from_value::<NraSosCertificate>(value).is_err());
    let mut value = original.clone();
    value["basis"] = serde_json::json!([[], [1, 2, 3]]);
    assert!(serde_json::from_value::<NraSosCertificate>(value).is_err());
    let mut value = original.clone();
    value["gram"] = serde_json::json!(vec![vec![rational(0, 1)]; 46]);
    assert!(serde_json::from_value::<NraSosCertificate>(value).is_err());
    let mut value = original.clone();
    value["gram"] = serde_json::json!([vec![rational(0, 1); 46]]);
    assert!(serde_json::from_value::<NraSosCertificate>(value).is_err());
    let mut value = original;
    let term = NraSosTerm {
        origin: NraSosOrigin::ClauseLiteral { position: 0 },
        multiplier: rational(1, 1),
    };
    value["terms"] = serde_json::json!(vec![term; 401]);
    assert!(serde_json::from_value::<NraSosCertificate>(value).is_err());
}

#[test]
fn step_decoder_bounds_clause_slots() {
    let step = ProofStep::NraSos {
        clause: vec![TermId::new(0); 1_025],
        certificate: certificate(),
    };
    assert!(serde_json::from_value::<ProofStep>(serde_json::to_value(step).unwrap()).is_err());
}

#[test]
fn programmatic_payload_preflight_rejects_bad_dimensions_and_denominators() {
    let mut cert = certificate();
    cert.gram[0].push(rational(0, 1));
    assert_eq!(cert.validate_shape(), Err(NraSosShapeError::Malformed));
    let mut cert = certificate();
    cert.rhs.denominator = 0.into();
    assert_eq!(cert.validate_shape(), Err(NraSosShapeError::Malformed));
    cert.rhs.denominator = (-1).into();
    assert_eq!(cert.validate_shape(), Err(NraSosShapeError::Malformed));
}

#[test]
fn sequence_bound_precedes_decoding_an_excess_nested_payload() {
    let mut value = serde_json::to_value(certificate()).unwrap();
    let mut rows = vec![serde_json::json!([]); NraSosCertificate::MAX_BASIS];
    rows.push(serde_json::json!({"not_a_monomial": []}));
    value["basis"] = rows.into();
    let error = serde_json::from_value::<NraSosCertificate>(value).unwrap_err();
    assert!(error
        .to_string()
        .contains("SOS sequence exceeds its fixed bound"));
}
