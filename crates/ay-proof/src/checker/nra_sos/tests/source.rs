// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{Constant, TermData};

/// Raw comparisons deliberately retain constant and malformed child terms so
/// the SOS checker, not a simplifying constructor, owns the refusal.
fn conflict_over(terms: &mut TermStore, expression: TermId) -> [TermId; 2] {
    let (zero, one) = if terms.sort(expression) == &Sort::Int {
        (terms.mk_int(0.into()), terms.mk_int(1.into()))
    } else {
        (real(terms, 0), real(terms, 1))
    };
    let lower = terms.mk_app(Symbol::Named(">=".into()), [expression, one], Sort::Bool);
    let upper = terms.mk_app(Symbol::Named("<=".into()), [expression, zero], Sort::Bool);
    [terms.mk_not_raw(lower), terms.mk_not_raw(upper)]
}

fn linear_certificate() -> NraSosCertificate {
    certificate(vec![vec![]], &[&[0]], vec![term(0, 1), term(1, 1)], -1)
}

#[test]
fn admits_homogeneous_integer_arithmetic_and_exact_fractional_sources() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let one = terms.mk_int(1.into());
    let expression = terms.mk_app(Symbol::Named("+".into()), [x, one], Sort::Int);
    let clause = conflict_over(&mut terms, expression);
    validate(&terms, &clause, &linear_certificate()).unwrap();

    let x = terms.mk_var("r", Sort::Real);
    let half = terms.mk_rational(BigRational::new(1.into(), 2.into()));
    let expression = terms.mk_mul(vec![half, x]);
    let clause = conflict_over(&mut terms, expression);
    let mut cert = linear_certificate();
    for factor in &mut cert.terms {
        factor.multiplier.denominator = 2.into();
    }
    cert.rhs.denominator = 2.into();
    validate(&terms, &clause, &cert).unwrap();
}

#[test]
fn rejects_unsupported_operators_even_for_an_otherwise_valid_identity() {
    for name in ["/", "to_real", "f"] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let one = real(&mut terms, 1);
        let expression = terms.mk_app(Symbol::Named(name.into()), [x, one], Sort::Real);
        let clause = conflict_over(&mut terms, expression);
        assert!(matches!(
            validate(&terms, &clause, &linear_certificate()),
            Err(ProofCheckError::InvalidTheoryLemma { .. })
        ));
    }
    for name in ["+", "-", "*"] {
        let mut terms = TermStore::new();
        let expression = terms.mk_app(Symbol::Named(name.into()), [], Sort::Real);
        let clause = conflict_over(&mut terms, expression);
        assert!(validate(&terms, &clause, &linear_certificate()).is_err());
    }
}

#[test]
fn rejects_mixed_numeric_child_sorts_before_parsing() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let one = terms.mk_int(1.into());
    let expression = terms.mk_app(Symbol::Named("+".into()), [x, one], Sort::Real);
    let clause = conflict_over(&mut terms, expression);
    assert!(validate(&terms, &clause, &linear_certificate()).is_err());
}

#[test]
fn rejects_constant_kind_and_annotated_sort_disagreement() {
    for integer_source in [false, true] {
        let mut terms = TermStore::new();
        let value = if integer_source {
            terms.mk_int(1.into())
        } else {
            real(&mut terms, 1)
        };
        let clause = conflict_over(&mut terms, value);
        let mut entries = terms.entries_snapshot();
        entries[value.index()].0 = if integer_source {
            TermData::Const(Constant::Rational(BigRational::one().into()))
        } else {
            TermData::Const(Constant::Int(1.into()))
        };
        let restored = TermStore::from_entries(entries, None, None, 0);
        assert!(matches!(
            validate(&restored, &clause, &linear_certificate()),
            Err(ProofCheckError::InvalidTheoryLemma { .. })
        ));
    }
}

#[test]
fn rejects_bv2nat_before_touching_raw_bitvector_width_or_value() {
    for width in [0, 8, u32::MAX] {
        let mut terms = TermStore::new();
        let raw = terms.mk_var("raw", Sort::bitvec(8));
        let expression = terms.mk_app(Symbol::Named("bv2nat".into()), [raw], Sort::Int);
        let clause = conflict_over(&mut terms, expression);
        let mut entries = terms.entries_snapshot();
        entries[raw.index()].0 = TermData::Const(Constant::BitVec {
            value: (-1).into(),
            width,
        });
        let restored = TermStore::from_entries(entries, None, None, 0);
        assert!(matches!(
            validate(&restored, &clause, &linear_certificate()),
            Err(ProofCheckError::InvalidTheoryLemma { .. })
        ));
    }
}

#[test]
fn rejects_raw_foreign_constant_masquerading_as_arithmetic() {
    let mut terms = TermStore::new();
    let value = real(&mut terms, 1);
    let clause = conflict_over(&mut terms, value);
    for foreign in [
        Constant::Bool(true),
        Constant::BitVec {
            value: 1.into(),
            width: u32::MAX,
        },
    ] {
        let mut entries = terms.entries_snapshot();
        entries[value.index()].0 = TermData::Const(foreign);
        let restored = TermStore::from_entries(entries, None, None, 0);
        assert!(matches!(
            validate(&restored, &clause, &linear_certificate()),
            Err(ProofCheckError::InvalidTheoryLemma { .. })
        ));
    }
}

#[test]
fn generic_expansion_cap_refusals_keep_the_resource_limit_classification() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let degree = terms.mk_app(Symbol::Named("*".into()), vec![x; 257], Sort::Real);
    let clause = conflict_over(&mut terms, degree);
    assert_eq!(
        validate(&terms, &clause, &linear_certificate()),
        Err(ProofCheckError::ResourceLimit)
    );

    let wide = terms.mk_rational(BigRational::from_integer(
        num_bigint::BigInt::one() << 1_023usize,
    ));
    let coefficient = terms.mk_app(Symbol::Named("*".into()), [wide; 5], Sort::Real);
    let clause = conflict_over(&mut terms, coefficient);
    assert_eq!(
        validate(&terms, &clause, &linear_certificate()),
        Err(ProofCheckError::ResourceLimit)
    );
}
