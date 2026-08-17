// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unknown JSON fields must never become latent proof authority.

use ay_core::{
    AletheRule, ArraySort, BitVecSort, BvGateType, Constant, CuttingPlaneAnnotation,
    DatatypeConstructor, DatatypeField, DatatypeSort, FarkasAnnotation, FpOp, LiaAnnotation,
    ProofId, ProofStep, Sort, TermData, TermId, TheoryLemmaKind,
};
use ay_proof::{DatatypeMemberSignature, SerializableProofBundle, PROOF_BUNDLE_SCHEMA};
use serde::{de::DeserializeOwned, Serialize};
use serde_json::{json, Value};
use std::fmt::Debug;

const UNKNOWN: &str = "future_authority";

fn assert_struct_rejects_unknown<T>(value: &T, label: &str)
where
    T: Serialize + DeserializeOwned + Debug,
{
    let mut encoded = serde_json::to_value(value).expect("serialize strict authority carrier");
    encoded
        .as_object_mut()
        .expect("struct serializes as a JSON object")
        .insert(UNKNOWN.to_string(), json!("must reject"));
    assert_unknown_rejected::<T>(encoded, label);
}

fn assert_struct_variant_rejects_unknown<T>(value: &T, label: &str)
where
    T: Serialize + DeserializeOwned + Debug,
{
    let mut encoded = serde_json::to_value(value).expect("serialize strict authority variant");
    let tagged = encoded
        .as_object_mut()
        .expect("externally tagged enum serializes as a JSON object");
    assert_eq!(tagged.len(), 1, "{label}: expected one variant tag");
    tagged
        .values_mut()
        .next()
        .and_then(Value::as_object_mut)
        .expect("struct variant serializes with a named-field payload")
        .insert(UNKNOWN.to_string(), json!("must reject"));
    assert_unknown_rejected::<T>(encoded, label);
}

fn assert_unknown_rejected<T>(encoded: Value, label: &str)
where
    T: DeserializeOwned + Debug,
{
    let error = serde_json::from_value::<T>(encoded)
        .expect_err("an unknown authority field must fail closed");
    assert!(
        error.to_string().contains("unknown field"),
        "{label}: expected an unknown-field rejection, got {error}"
    );
}

fn assert_bundle_path_rejects_unknown(encoded: &Value, path: &str) {
    let mut mutated = encoded.clone();
    mutated
        .pointer_mut(path)
        .and_then(Value::as_object_mut)
        .unwrap_or_else(|| panic!("bundle fixture path {path:?} must name an object"))
        .insert(UNKNOWN.to_string(), json!("must reject"));
    assert_unknown_rejected::<SerializableProofBundle>(mutated, path);
}

#[test]
fn bundle_root_and_datatype_signature_reject_unknown_fields() {
    let bundle = SerializableProofBundle {
        schema: PROOF_BUNDLE_SCHEMA.to_string(),
        steps: Vec::new(),
        term_entries: Vec::new(),
        true_term: None,
        false_term: None,
        var_counter: 0,
        obligation_assertions: Vec::new(),
        datatype_declarations: Vec::new(),
        constructor_selectors: Vec::new(),
        datatype_member_signatures: Vec::new(),
    };
    assert_struct_rejects_unknown(&bundle, "SerializableProofBundle");

    let signature = DatatypeMemberSignature {
        identity: "Ctor#0".to_string(),
        argument_sorts: vec![Sort::Bool],
        result_sort: Sort::Uninterpreted("D".to_string()),
        nullary_term: None,
    };
    assert_struct_rejects_unknown(&signature, "DatatypeMemberSignature");
}

#[test]
fn bundle_decode_recursively_rejects_every_nested_authority_object() {
    let field = DatatypeField::new("value", Sort::Int);
    let constructor = DatatypeConstructor::new("Some", vec![field]);
    let datatype = DatatypeSort::new("OptionInt", vec![constructor]);
    let farkas = FarkasAnnotation::from_ints(&[1]);
    let bundle = SerializableProofBundle {
        schema: PROOF_BUNDLE_SCHEMA.to_string(),
        steps: vec![ProofStep::TheoryLemma {
            theory: "LIA".to_string(),
            clause: vec![TermId(0)],
            farkas: Some(farkas.clone()),
            kind: TheoryLemmaKind::ArraySelectStore { index_eq: true },
            lia: Some(LiaAnnotation::CuttingPlane(CuttingPlaneAnnotation {
                farkas,
                divisor: 2,
            })),
        }],
        term_entries: vec![
            (
                TermData::Const(Constant::BitVec {
                    value: 3.into(),
                    width: 8,
                }),
                Sort::BitVec(BitVecSort::new(8)),
            ),
            (
                TermData::Var("array".to_string(), 0),
                Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Bool))),
            ),
            (
                TermData::Var("datatype".to_string(), 1),
                Sort::Datatype(datatype),
            ),
        ],
        true_term: None,
        false_term: None,
        var_counter: 2,
        obligation_assertions: Vec::new(),
        datatype_declarations: Vec::new(),
        constructor_selectors: Vec::new(),
        datatype_member_signatures: vec![DatatypeMemberSignature {
            identity: "Some#0".to_string(),
            argument_sorts: vec![Sort::Int],
            result_sort: Sort::Uninterpreted("OptionInt".to_string()),
            nullary_term: None,
        }],
    };
    let encoded = serde_json::to_value(bundle).expect("serialize nested bundle fixture");
    for path in [
        "",
        "/steps/0/TheoryLemma",
        "/steps/0/TheoryLemma/farkas",
        "/steps/0/TheoryLemma/kind/ArraySelectStore",
        "/steps/0/TheoryLemma/lia/CuttingPlane",
        "/steps/0/TheoryLemma/lia/CuttingPlane/farkas",
        "/term_entries/0/0/Const/BitVec",
        "/term_entries/0/1/BitVec",
        "/term_entries/1/1/Array",
        "/term_entries/2/1/Datatype",
        "/term_entries/2/1/Datatype/constructors/0",
        "/term_entries/2/1/Datatype/constructors/0/fields/0",
        "/datatype_member_signatures/0",
    ] {
        assert_bundle_path_rejects_unknown(&encoded, path);
    }
}

#[test]
fn sort_authority_structs_reject_unknown_fields() {
    let bitvec = BitVecSort::new(8);
    assert_struct_rejects_unknown(&bitvec, "BitVecSort");

    let array = ArraySort::new(Sort::Int, Sort::BitVec(bitvec.clone()));
    assert_struct_rejects_unknown(&array, "ArraySort");

    let field = DatatypeField::new("value", Sort::Int);
    assert_struct_rejects_unknown(&field, "DatatypeField");

    let constructor = DatatypeConstructor::new("Some", vec![field.clone()]);
    assert_struct_rejects_unknown(&constructor, "DatatypeConstructor");

    let datatype = DatatypeSort::new("OptionInt", vec![constructor]);
    assert_struct_rejects_unknown(&datatype, "DatatypeSort");
}

#[test]
fn annotation_authority_structs_reject_unknown_fields() {
    let farkas = FarkasAnnotation::from_ints(&[1, 2]);
    assert_struct_rejects_unknown(&farkas, "FarkasAnnotation");

    let cutting_plane = CuttingPlaneAnnotation { farkas, divisor: 2 };
    assert_struct_rejects_unknown(&cutting_plane, "CuttingPlaneAnnotation");
}

#[test]
fn every_proof_step_struct_variant_rejects_unknown_fields() {
    let variants = [
        ProofStep::Resolution {
            clause: vec![TermId(0)],
            pivot: TermId(0),
            clause1: ProofId(0),
            clause2: ProofId(1),
        },
        ProofStep::TheoryLemma {
            theory: "EUF".to_string(),
            clause: vec![TermId(0)],
            farkas: None,
            kind: TheoryLemmaKind::EufReflexive,
            lia: None,
        },
        ProofStep::Step {
            rule: AletheRule::Refl,
            clause: vec![TermId(0)],
            premises: Vec::new(),
            args: vec![TermId(0)],
        },
        ProofStep::Anchor {
            end_step: ProofId(0),
            variables: vec![("x".to_string(), Sort::Int)],
        },
    ];
    for (index, variant) in variants.iter().enumerate() {
        assert_struct_variant_rejects_unknown(variant, &format!("ProofStep variant {index}"));
    }
}

#[test]
fn every_theory_kind_struct_variant_rejects_unknown_fields() {
    let variants = [
        TheoryLemmaKind::BvBitBlastGate {
            gate_type: BvGateType::And,
            width: 8,
        },
        TheoryLemmaKind::ArraySelectStore { index_eq: true },
        TheoryLemmaKind::FpToBv {
            operation: FpOp::Add,
        },
        TheoryLemmaKind::FpClassification {
            operation: FpOp::IsNaN,
        },
    ];
    for (index, variant) in variants.iter().enumerate() {
        assert_struct_variant_rejects_unknown(variant, &format!("TheoryLemmaKind variant {index}"));
    }
}

#[test]
fn bitvector_constant_struct_variant_rejects_unknown_fields() {
    let bitvector = Constant::BitVec {
        value: 3.into(),
        width: 8,
    };
    assert_struct_variant_rejects_unknown(&bitvector, "Constant::BitVec");
}
