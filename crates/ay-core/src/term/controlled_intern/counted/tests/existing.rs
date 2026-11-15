// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

#[test]
fn mixed_existing_arena_preserves_ids_and_deduplicates_supported_data() {
    let mut store = TermStore::new();
    let rm = store.mk_var("same", Sort::Uninterpreted("RoundingMode".into()));
    let integer = store.mk_int(BigInt::from(17));
    let real = store.mk_rational(num_rational::BigRational::new(
        BigInt::from(3),
        BigInt::from(7),
    ));
    let string = store.mk_string("existing".into());
    let body = store.mk_var("body", Sort::Bool);
    let quantified =
        store.mk_forall_with_triggers(vec![("i".into(), Sort::Int)], body, vec![vec![body]]);
    let original = ample();
    let mut builder = CountedTermBuilder::new(&mut store, &original).unwrap();
    let yes = builder.boolean(true).unwrap();
    let same = builder.variable("same", &Sort::Bool).unwrap();
    assert_ne!(same, rm);
    assert_eq!(builder.variable("same", &Sort::Bool).unwrap(), same);
    assert_eq!(builder.variable("body", &Sort::Bool).unwrap(), body);
    let sign = builder.bitvector(&BigInt::from(0), 1).unwrap();
    let exp = builder.bitvector(&BigInt::from(0), 3).unwrap();
    let frac = builder.bitvector(&BigInt::from(0), 4).unwrap();
    let fp = builder.floating_point_fields(sign, exp, frac).unwrap();
    assert_eq!(builder.floating_point_fields(sign, exp, frac).unwrap(), fp);
    // Force a general existing payload into a supported candidate's bucket.
    let candidate = TermData::App(Symbol::named("and"), vec![yes, body]);
    let hash = TermStore::compute_hash(&candidate);
    builder.terms.insert(hash, quantified, &original).unwrap();
    let actual = builder.apply(CountedBuiltin::And, &[yes, body]).unwrap();
    assert_eq!(builder.store.get(actual), &candidate);
    assert_eq!(
        builder.variable("new-int", &Sort::Int),
        Err(CountedTermError::Unsupported)
    );
    builder.finish().unwrap();
    assert_eq!(store.sort(rm), &Sort::Uninterpreted("RoundingMode".into()));
    assert_eq!(store.sort(integer), &Sort::Int);
    assert_eq!(store.sort(real), &Sort::Real);
    assert_eq!(store.sort(string), &Sort::String);
    assert!(
        matches!(store.get(quantified), TermData::Forall(_, actual, triggers) if *actual == body && triggers == &[vec![body]])
    );
}

#[test]
fn existing_payload_work_refusal_is_sticky_without_source_mutation() {
    let mut store = TermStore::new();
    let id = store.mk_string("x".repeat(4096));
    let before = store.terms.len();
    let original = owner(200, 1024 * 1024);
    assert!(matches!(
        CountedTermBuilder::new(&mut store, &original),
        Err(CountedTermError::Stopped(
            CountedAdmissionError::WorkExhausted
        ))
    ));
    assert_eq!(original.check(), Err(CountedAdmissionError::WorkExhausted));
    assert_eq!(store.terms.len(), before);
    assert!(
        matches!(store.get(id), TermData::Const(Constant::String(value)) if value.len() == 4096)
    );
}

#[test]
fn too_deep_existing_sort_refuses_before_hashing_and_stays_terminal() {
    let mut sort = Sort::Int;
    for _ in 0..258 {
        sort = Sort::Seq(Box::new(sort));
    }
    let mut store = TermStore::new();
    store.mk_var("deep", sort);
    let original = ample();
    assert!(matches!(
        CountedTermBuilder::new(&mut store, &original),
        Err(CountedTermError::Stopped(
            CountedAdmissionError::WorkExhausted
        ))
    ));
    assert_eq!(original.check(), Err(CountedAdmissionError::WorkExhausted));
}

#[test]
fn malformed_existing_rational_is_accounted_raw_not_normalized_or_authorized() {
    let mut store = TermStore::new();
    let raw = TermData::Const(Constant::Rational(crate::term::RationalWrapper(
        num_rational::BigRational::new_raw(1.into(), 0.into()),
    )));
    let id = store.intern(raw, Sort::Real);
    let original = ample();
    let mut builder = CountedTermBuilder::new(&mut store, &original).unwrap();
    builder.boolean(true).unwrap();
    assert!(
        matches!(builder.store.get(id), TermData::Const(Constant::Rational(value)) if value.0.denom() == &BigInt::from(0))
    );
    builder.finish().unwrap();
}
