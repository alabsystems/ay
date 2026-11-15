// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn annotation_cannot_replace_actual_operation_or_missing_predicate() {
    let mut f = Fixture::new(8, 24);
    let theorem = f.theorem(FpOp::IsNaN);
    assert!(f.validate(theorem, FpOp::Add).is_err());
    assert!(f.validate(theorem, FpOp::IsZero).is_err());
    let bare = f.app("fp.isNaN", &[f.value], Sort::Bool);
    assert!(f.validate(bare, FpOp::IsNaN).is_err());
}

#[test]
fn incomplete_or_weakened_bv_conditions_are_not_certificates() {
    let mut f = Fixture::new(8, 24);
    let source = f.app("fp.isNaN", &[f.value], Sort::Bool);
    let exponent_only = f.test_field(
        f.fields.exponent,
        8,
        WordConstant::Ones,
        EqualitySense::Equal,
    );
    let incomplete = f.eq(source, exponent_only);
    assert!(f.validate(incomplete, FpOp::IsNaN).is_err());
    let fraction_zero = f.test_field(
        f.fields.fraction,
        23,
        WordConstant::Zero,
        EqualitySense::Equal,
    );
    let wrong = f.and(exponent_only, fraction_zero);
    let false_nan = f.eq(source, wrong);
    assert!(f.validate(false_nan, FpOp::IsNaN).is_err());
    let sign_only = f.test_field(f.fields.sign, 1, WordConstant::Ones, EqualitySense::Equal);
    let negative = f.app("fp.isNegative", &[f.value], Sort::Bool);
    let lacks_nan_exclusion = f.eq(negative, sign_only);
    assert!(f.validate(lacks_nan_exclusion, FpOp::IsNegative).is_err());
}

#[test]
fn changed_source_field_cannot_alias_the_original_bits() {
    let mut f = Fixture::new(8, 24);
    let theorem = f.theorem(FpOp::IsNaN);
    let TermData::App(_, args) = f.terms.get(theorem) else {
        panic!("fixture equality");
    };
    let [source, lowered] = args.as_slice() else {
        panic!("fixture equality arity");
    };
    let lowered = *lowered;
    let source = *source;
    let other = f.terms.mk_var("other_fraction", Sort::bitvec(23));
    let value = f.app(
        "fp",
        &[f.fields.sign, f.fields.exponent, other],
        Sort::FloatingPoint(8, 24),
    );
    let changed = f.app("fp.isNaN", &[value], Sort::Bool);
    let forged = f.eq(changed, lowered);
    assert!(f.validate(forged, FpOp::IsNaN).is_err());
    assert_ne!(source, changed);
}

#[test]
fn named_builtin_identity_does_not_accept_indexed_lookalike() {
    let mut f = Fixture::new(8, 24);
    let predicate = f.predicate(FpOp::IsNaN);
    let source = f.terms.mk_app(
        Symbol::indexed("fp.isNaN", vec![8, 24]),
        [f.value],
        Sort::Bool,
    );
    let forged = f.eq(source, predicate);
    assert!(f.validate(forged, FpOp::IsNaN).is_err());
}

#[test]
fn missing_nodes_wrong_sorts_and_arity_refuse_without_indexing() {
    let mut f = Fixture::new(8, 24);
    assert!(f.validate(TermId::SENTINEL, FpOp::IsNaN).is_err());
    let malformed = f.app(
        "fp",
        &[f.fields.sign, f.fields.exponent],
        Sort::FloatingPoint(8, 24),
    );
    let source = f.app("fp.isNaN", &[malformed], Sort::Bool);
    let predicate = f.predicate(FpOp::IsNaN);
    let theorem = f.eq(source, predicate);
    assert!(f.validate(theorem, FpOp::IsNaN).is_err());
    let wrong_width = f.terms.mk_var("wrong_sign", Sort::bitvec(2));
    let malformed = f.app(
        "fp",
        &[wrong_width, f.fields.exponent, f.fields.fraction],
        Sort::FloatingPoint(8, 24),
    );
    let source = f.app("fp.isNaN", &[malformed], Sort::Bool);
    let theorem = f.eq(source, predicate);
    assert!(f.validate(theorem, FpOp::IsNaN).is_err());
    let malformed = f.app(
        "fp",
        &[f.fields.sign, f.fields.exponent, TermId::SENTINEL],
        Sort::FloatingPoint(8, 24),
    );
    let source = f.app("fp.isNaN", &[malformed], Sort::Bool);
    let theorem = f.eq(source, predicate);
    assert!(f.validate(theorem, FpOp::IsNaN).is_err());
}

#[test]
fn guessed_sign_and_changed_off_sign_fields_fail_closed() {
    let mut f = Fixture::new(8, 24);
    let source = f.app("fp.neg", &[f.value], Sort::FloatingPoint(8, 24));
    let false_same_sign = f.eq(source, f.value);
    assert!(f.validate(false_same_sign, FpOp::Neg).is_err());
    let zero = f.terms.mk_bitvec(BigInt::from(0u8), 1);
    let other_exponent = f.terms.mk_var("other_exponent", Sort::bitvec(8));
    let false_abs = f.app(
        "fp",
        &[zero, other_exponent, f.fields.fraction],
        Sort::FloatingPoint(8, 24),
    );
    let abs = f.app("fp.abs", &[f.value], Sort::FloatingPoint(8, 24));
    let theorem = f.eq(abs, false_abs);
    assert!(f.validate(theorem, FpOp::Abs).is_err());
}

#[test]
fn adding_an_unrelated_clause_literal_never_completes_the_schema() {
    let mut f = Fixture::new(8, 24);
    let theorem = f.theorem(FpOp::IsNaN);
    let other = f.terms.mk_var("other", Sort::Bool);
    assert!(super::super::super::validate_fp_to_bv(
        &f.terms,
        ProofId(0),
        &[theorem, other],
        FpOp::IsNaN,
        &mut |_, _| true
    )
    .is_err());
}

#[test]
fn unsupported_arithmetic_circuit_is_not_promoted_by_a_matching_tag() {
    let mut f = Fixture::new(8, 24);
    let rm = f.app("RNE", &[], Sort::Uninterpreted("RoundingMode".into()));
    let add = f.app(
        "fp.add",
        &[rm, f.value, f.value],
        Sort::FloatingPoint(8, 24),
    );
    let alleged = f.eq(add, f.value);
    assert!(f.validate(alleged, FpOp::Add).is_err());
    // Rust remainder and its allowed raw-NaN payload set have no certificate
    // merely because a native fp.rem occurrence appears in a term.
    let rem = f.app("fp.rem", &[f.value, f.value], Sort::FloatingPoint(8, 24));
    let alleged = f.eq(rem, f.value);
    assert!(f.validate(alleged, FpOp::Rem).is_err());
}

#[test]
fn imported_noncanonical_constants_and_hidden_field_cycles_are_not_authority() {
    let mut f = Fixture::new(8, 24);
    let theorem = f.theorem(FpOp::IsNaN);
    for data in [
        TermData::Const(Constant::BitVec {
            value: BigInt::from(-1i8),
            width: 1,
        }),
        TermData::Const(Constant::BitVec {
            value: BigInt::from(2u8),
            width: 1,
        }),
        TermData::Const(Constant::BitVec {
            value: BigInt::from(0u8),
            width: 2,
        }),
        TermData::App(Symbol::named("bvnot"), vec![f.fields.sign]),
    ] {
        let mut entries = f.terms.entries_snapshot();
        entries[f.fields.sign.index()] = (data, Sort::bitvec(1));
        let imported = TermStore::from_entries(entries, None, None, f.terms.var_counter());
        assert!(super::super::super::validate_fp_to_bv(
            &imported,
            ProofId(0),
            &[theorem],
            FpOp::IsNaN,
            &mut |_, _| true
        )
        .is_err());
    }
}
