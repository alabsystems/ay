// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::*;

#[test]
fn farkas_annotation_from_ints_preserves_values() {
    let ann = FarkasAnnotation::from_ints(&[0, 1, 2]);
    assert_eq!(
        ann.coefficients,
        vec![
            Rational64::from(0),
            Rational64::from(1),
            Rational64::from(2)
        ]
    );
}

#[test]
fn farkas_annotation_is_valid_checks_non_negative_coeffs() {
    assert!(FarkasAnnotation::from_ints(&[]).is_valid());
    assert!(FarkasAnnotation::from_ints(&[0, 1, 2]).is_valid());
    assert!(!FarkasAnnotation::from_ints(&[0, -1, 2]).is_valid());

    let bad = FarkasAnnotation::new(vec![Rational64::new(-1, 2)]);
    assert!(!bad.is_valid());
}

#[test]
fn theory_lemma_kind_alethe_rule_mapping() {
    assert_eq!(
        TheoryLemmaKind::EufTransitive.alethe_rule(),
        "eq_transitive"
    );
    assert_eq!(TheoryLemmaKind::EufCongruent.alethe_rule(), "eq_congruent");
    assert_eq!(
        TheoryLemmaKind::EufCongruentPred.alethe_rule(),
        "eq_congruent_pred"
    );
    assert_eq!(TheoryLemmaKind::LraFarkas.alethe_rule(), "la_generic");
    assert_eq!(TheoryLemmaKind::LiaGeneric.alethe_rule(), "lia_generic");
    assert_eq!(TheoryLemmaKind::BvBitBlast.alethe_rule(), "bv_bitblast");
    assert_eq!(
        TheoryLemmaKind::BvBitBlastGate {
            gate_type: BvGateType::And,
            width: 8,
        }
        .alethe_rule(),
        "bv_bitblast"
    );
    assert_eq!(
        TheoryLemmaKind::ArraySelectStore { index_eq: true }.alethe_rule(),
        "read_over_write_pos"
    );
    assert_eq!(
        TheoryLemmaKind::ArraySelectStore { index_eq: false }.alethe_rule(),
        "read_over_write_neg"
    );
    assert_eq!(
        TheoryLemmaKind::ArrayExtensionality.alethe_rule(),
        "extensionality"
    );
    assert_eq!(
        TheoryLemmaKind::FpToBv {
            operation: FpOp::Add,
        }
        .alethe_rule(),
        "fp_to_bv"
    );
    assert_eq!(
        TheoryLemmaKind::FpToBv {
            operation: FpOp::Eq,
        }
        .alethe_rule(),
        "fp_to_bv"
    );
    assert_eq!(TheoryLemmaKind::Generic.alethe_rule(), "trust");
    assert_eq!(TheoryLemmaKind::default().alethe_rule(), "trust");
}

#[test]
fn theory_lemma_kind_is_trust_excludes_array_variants() {
    // Array variants are no longer trust (#8073)
    assert!(
        !TheoryLemmaKind::ArraySelectStore { index_eq: true }.is_trust(),
        "ArraySelectStore(index_eq=true) should not be trust"
    );
    assert!(
        !TheoryLemmaKind::ArraySelectStore { index_eq: false }.is_trust(),
        "ArraySelectStore(index_eq=false) should not be trust"
    );
    assert!(
        !TheoryLemmaKind::ArrayExtensionality.is_trust(),
        "ArrayExtensionality should not be trust"
    );
    // Generic is still trust
    assert!(TheoryLemmaKind::Generic.is_trust());
    // Other non-trust variants
    assert!(!TheoryLemmaKind::EufTransitive.is_trust());
    assert!(!TheoryLemmaKind::BvBitBlast.is_trust());
}

#[test]
fn fp_op_display_and_fp_to_bv_is_not_trust() {
    // FpOp Display covers all arithmetic, comparison, conversion, and classification ops.
    assert_eq!(format!("{}", FpOp::Add), "fp.add");
    assert_eq!(format!("{}", FpOp::Sub), "fp.sub");
    assert_eq!(format!("{}", FpOp::Mul), "fp.mul");
    assert_eq!(format!("{}", FpOp::Div), "fp.div");
    assert_eq!(format!("{}", FpOp::Sqrt), "fp.sqrt");
    assert_eq!(format!("{}", FpOp::Neg), "fp.neg");
    assert_eq!(format!("{}", FpOp::Abs), "fp.abs");
    assert_eq!(format!("{}", FpOp::Fma), "fp.fma");
    assert_eq!(format!("{}", FpOp::Eq), "fp.eq");
    assert_eq!(format!("{}", FpOp::Lt), "fp.lt");
    assert_eq!(format!("{}", FpOp::Le), "fp.leq");
    assert_eq!(format!("{}", FpOp::Gt), "fp.gt");
    assert_eq!(format!("{}", FpOp::Ge), "fp.geq");
    assert_eq!(format!("{}", FpOp::ToReal), "fp.to_real");
    assert_eq!(format!("{}", FpOp::FromReal), "to_fp_real");
    assert_eq!(format!("{}", FpOp::ToSbv), "fp.to_sbv");
    assert_eq!(format!("{}", FpOp::ToUbv), "fp.to_ubv");
    assert_eq!(format!("{}", FpOp::FromSbv), "to_fp_sbv");
    assert_eq!(format!("{}", FpOp::FromUbv), "to_fp_unsigned");
    assert_eq!(format!("{}", FpOp::RoundToIntegral), "fp.roundToIntegral");
    assert_eq!(format!("{}", FpOp::Min), "fp.min");
    assert_eq!(format!("{}", FpOp::Max), "fp.max");
    assert_eq!(format!("{}", FpOp::Rem), "fp.rem");
    assert_eq!(format!("{}", FpOp::IsNaN), "fp.isNaN");
    assert_eq!(format!("{}", FpOp::IsInfinite), "fp.isInfinite");
    assert_eq!(format!("{}", FpOp::IsZero), "fp.isZero");
    assert_eq!(format!("{}", FpOp::IsNormal), "fp.isNormal");
    assert_eq!(format!("{}", FpOp::IsSubnormal), "fp.isSubnormal");
    assert_eq!(format!("{}", FpOp::IsPositive), "fp.isPositive");
    assert_eq!(format!("{}", FpOp::IsNegative), "fp.isNegative");
    assert_eq!(format!("{}", FpOp::StructuralEq), "fp_structural_eq");
    assert_eq!(format!("{}", FpOp::ToIeeeBv), "fp.to_ieee_bv");
    assert_eq!(format!("{}", FpOp::FromFp), "to_fp_fp");

    // FpToBv must NOT be trust (unlike Generic).
    let fp_to_bv_kind = TheoryLemmaKind::FpToBv {
        operation: FpOp::Add,
    };
    assert!(!fp_to_bv_kind.is_trust());

    // All FpOp variants map to "fp_to_bv" rule.
    for op in [
        FpOp::Add,
        FpOp::Sub,
        FpOp::Mul,
        FpOp::Div,
        FpOp::Sqrt,
        FpOp::Neg,
        FpOp::Abs,
        FpOp::Fma,
        FpOp::Eq,
        FpOp::Lt,
        FpOp::Le,
        FpOp::Gt,
        FpOp::Ge,
        FpOp::ToReal,
        FpOp::FromReal,
        FpOp::ToSbv,
        FpOp::ToUbv,
        FpOp::FromSbv,
        FpOp::FromUbv,
        FpOp::RoundToIntegral,
        FpOp::Min,
        FpOp::Max,
        FpOp::Rem,
        FpOp::IsNaN,
        FpOp::IsInfinite,
        FpOp::IsZero,
        FpOp::IsNormal,
        FpOp::IsSubnormal,
        FpOp::IsPositive,
        FpOp::IsNegative,
        FpOp::StructuralEq,
        FpOp::ToIeeeBv,
        FpOp::FromFp,
    ] {
        assert_eq!(
            TheoryLemmaKind::FpToBv { operation: op }.alethe_rule(),
            "fp_to_bv",
            "FpOp::{op} should map to fp_to_bv"
        );
    }
}

#[test]
fn alethe_rule_name_and_display() {
    assert_eq!(AletheRule::True.name(), "true");
    assert_eq!(AletheRule::AndPos(1).name(), "and_pos");
    assert_eq!(AletheRule::OrPos(7).name(), "or_pos");
    assert_eq!(AletheRule::ReadOverWritePos.name(), "read_over_write_pos");
    assert_eq!(AletheRule::ReadOverWriteNeg.name(), "read_over_write_neg");
    assert_eq!(AletheRule::Extensionality.name(), "extensionality");
    assert_eq!(AletheRule::BvBitblast.name(), "bv_bitblast");
    assert_eq!(AletheRule::FpToBv.name(), "fp_to_bv");
    assert_eq!(AletheRule::Custom("my_rule".to_string()).name(), "my_rule");

    assert_eq!(format!("{}", AletheRule::IteNeg2), "ite_neg2");
    assert_eq!(format!("{}", AletheRule::FpToBv), "fp_to_bv");
    assert_eq!(
        format!("{}", AletheRule::EqCongruentPred),
        "eq_congruent_pred"
    );
}

#[test]
fn proof_id_display() {
    assert_eq!(ProofId(0).to_string(), "t0");
    assert_eq!(ProofId(12).to_string(), "t12");
}

#[test]
fn proof_add_assume_without_name_does_not_add_named_steps() {
    let mut proof = Proof::new();
    let h1 = proof.add_assume(TermId::new(1), None);

    assert_eq!(h1, ProofId(0));
    assert!(proof.named_steps.is_empty());
}

#[test]
fn proof_add_and_get_steps_and_named_assumes() {
    let mut proof = Proof::new();
    assert!(proof.is_empty());
    assert_eq!(proof.len(), 0);

    let h1 = proof.add_assume(TermId::new(1), Some("h1".to_string()));
    let t1 = proof.add_rule_step(
        AletheRule::Resolution,
        vec![TermId::new(2), TermId::new(3)],
        vec![h1],
        vec![],
    );

    assert_eq!(h1, ProofId(0));
    assert_eq!(t1, ProofId(1));
    assert_eq!(proof.named_steps.get("h1"), Some(&h1));
    assert_eq!(proof.len(), 2);
    assert!(!proof.is_empty());

    match proof.get_step(h1) {
        Some(ProofStep::Assume(t)) => assert_eq!(*t, TermId::new(1)),
        other => panic!("unexpected step: {other:?}"),
    }

    match proof.get_step(t1) {
        Some(ProofStep::Step {
            rule,
            clause,
            premises,
            args,
        }) => {
            assert_eq!(rule, &AletheRule::Resolution);
            assert_eq!(clause, &vec![TermId::new(2), TermId::new(3)]);
            assert_eq!(premises, &vec![h1]);
            assert!(args.is_empty());
        }
        other => panic!("unexpected step: {other:?}"),
    }

    assert!(proof.get_step(ProofId(9999)).is_none());
}

#[test]
fn proof_add_anchor_step_roundtrips_through_get_step() {
    let mut proof = Proof::new();
    let end = proof.add_assume(TermId::new(1), None);
    let anchor = proof.add_step(ProofStep::Anchor {
        end_step: end,
        variables: vec![("x".to_string(), crate::sort::Sort::Bool)],
    });

    match proof.get_step(anchor) {
        Some(ProofStep::Anchor {
            end_step,
            variables,
        }) => {
            assert_eq!(*end_step, end);
            assert_eq!(variables, &vec![("x".to_string(), crate::sort::Sort::Bool)]);
        }
        other => panic!("unexpected step: {other:?}"),
    }
}

#[test]
fn proof_add_resolution_and_theory_lemmas() {
    let mut proof = Proof::new();
    let c1 = proof.add_assume(TermId::new(10), None);
    let c2 = proof.add_assume(TermId::new(11), None);

    let r = proof.add_resolution(vec![TermId::new(12)], TermId::new(13), c1, c2);

    match proof.get_step(r) {
        Some(ProofStep::Resolution {
            clause,
            pivot,
            clause1,
            clause2,
        }) => {
            assert_eq!(clause, &vec![TermId::new(12)]);
            assert_eq!(*pivot, TermId::new(13));
            assert_eq!(*clause1, c1);
            assert_eq!(*clause2, c2);
        }
        other => panic!("unexpected step: {other:?}"),
    }

    let tl1 = proof.add_theory_lemma("EUF", vec![TermId::new(20)]);
    match proof.get_step(tl1) {
        Some(ProofStep::TheoryLemma {
            theory,
            clause,
            farkas,
            kind,
            ..
        }) => {
            assert_eq!(theory, "EUF");
            assert_eq!(clause, &vec![TermId::new(20)]);
            assert!(farkas.is_none());
            assert_eq!(*kind, TheoryLemmaKind::Generic);
        }
        other => panic!("unexpected step: {other:?}"),
    }

    let tl2 = proof.add_theory_lemma_with_farkas(
        "LRA",
        vec![TermId::new(30)],
        FarkasAnnotation::from_ints(&[1, 0]),
    );
    match proof.get_step(tl2) {
        Some(ProofStep::TheoryLemma {
            theory,
            clause,
            farkas,
            kind,
            ..
        }) => {
            assert_eq!(theory, "LRA");
            assert_eq!(clause, &vec![TermId::new(30)]);
            assert_eq!(farkas, &Some(FarkasAnnotation::from_ints(&[1, 0])));
            assert_eq!(*kind, TheoryLemmaKind::LraFarkas);
        }
        other => panic!("unexpected step: {other:?}"),
    }

    let tl3 = proof.add_theory_lemma_with_kind(
        "EUF",
        vec![TermId::new(40)],
        TheoryLemmaKind::EufCongruentPred,
    );
    match proof.get_step(tl3) {
        Some(ProofStep::TheoryLemma { farkas, kind, .. }) => {
            assert!(farkas.is_none());
            assert_eq!(*kind, TheoryLemmaKind::EufCongruentPred);
        }
        other => panic!("unexpected step: {other:?}"),
    }

    let tl4 = proof.add_theory_lemma_with_farkas_and_kind(
        "LIA",
        vec![TermId::new(50)],
        FarkasAnnotation::from_ints(&[1]),
        TheoryLemmaKind::LiaGeneric,
    );
    match proof.get_step(tl4) {
        Some(ProofStep::TheoryLemma {
            theory,
            clause,
            farkas,
            kind,
            ..
        }) => {
            assert_eq!(theory, "LIA");
            assert_eq!(clause, &vec![TermId::new(50)]);
            assert_eq!(farkas, &Some(FarkasAnnotation::from_ints(&[1])));
            assert_eq!(*kind, TheoryLemmaKind::LiaGeneric);
        }
        other => panic!("unexpected step: {other:?}"),
    }
}

#[test]
fn theory_lemma_kind_string_variants_alethe_rule_mapping() {
    assert_eq!(
        TheoryLemmaKind::StringLengthAxiom.alethe_rule(),
        "string_length"
    );
    assert_eq!(
        TheoryLemmaKind::StringContentAxiom.alethe_rule(),
        "string_decompose"
    );
    assert_eq!(
        TheoryLemmaKind::StringNormalForm.alethe_rule(),
        "string_code_inj"
    );
}

#[test]
fn theory_lemma_kind_is_trust_excludes_string_variants() {
    // String variants are no longer trust (#8074)
    assert!(
        !TheoryLemmaKind::StringLengthAxiom.is_trust(),
        "StringLengthAxiom should not be trust"
    );
    assert!(
        !TheoryLemmaKind::StringContentAxiom.is_trust(),
        "StringContentAxiom should not be trust"
    );
    assert!(
        !TheoryLemmaKind::StringNormalForm.is_trust(),
        "StringNormalForm should not be trust"
    );
    // Generic is still trust
    assert!(TheoryLemmaKind::Generic.is_trust());
}

#[test]
fn alethe_rule_name_string_variants() {
    assert_eq!(AletheRule::StringLength.name(), "string_length");
    assert_eq!(AletheRule::StringDecompose.name(), "string_decompose");
    assert_eq!(AletheRule::StringCodeInj.name(), "string_code_inj");

    assert_eq!(format!("{}", AletheRule::StringLength), "string_length");
    assert_eq!(
        format!("{}", AletheRule::StringDecompose),
        "string_decompose"
    );
    assert_eq!(format!("{}", AletheRule::StringCodeInj), "string_code_inj");
}
