// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use num_bigint::BigInt;
use num_rational::BigRational;

use super::*;

mod progress;

fn entries() -> Vec<(TermData, Sort)> {
    vec![
        (TermData::Const(Constant::Bool(true)), Sort::Bool),
        (TermData::Const(Constant::Bool(false)), Sort::Bool),
        (TermData::Var("x".into(), 0), Sort::Int),
        (TermData::Var("y".into(), 1), Sort::Int),
    ]
}

fn run(entries: &[(TermData, Sort)]) -> Result<(), ProofCheckError> {
    validate_term_snapshot_with_progress(entries, &mut |_, _| true)
}

fn compare(extra: (TermData, Sort), valid: bool) {
    let mut values = entries();
    values.push(extra);
    let old = validate_term_snapshot_legacy(&values);
    let new = run(&values);
    assert_eq!(old.is_ok(), valid, "old={old:?}");
    assert_eq!(new.is_ok(), valid, "new={new:?}");
    if !valid {
        assert!(matches!(
            new,
            Err(ProofCheckError::MalformedProofBundle { .. })
        ));
    }
}

#[test]
fn positional_shapes_preserve_legacy_acceptance() {
    let shapes = [
        (TermData::Not(TermId(0)), Sort::Bool),
        (TermData::Ite(TermId(0), TermId(2), TermId(3)), Sort::Int),
        (
            TermData::Let(vec![(String::new(), TermId(2))], TermId(3)),
            Sort::Int,
        ),
        (
            TermData::App(Symbol::named("="), vec![TermId(2), TermId(3)]),
            Sort::Bool,
        ),
        (
            TermData::App(Symbol::indexed("uf", vec![7]), vec![TermId(2)]),
            Sort::String,
        ),
        (
            TermData::Forall(
                vec![(String::new(), Sort::Int)],
                TermId(0),
                vec![vec![], vec![TermId(2)]],
            ),
            Sort::Bool,
        ),
        (TermData::Exists(vec![], TermId(1), vec![]), Sort::Bool),
    ];
    for shape in shapes {
        compare(shape, true);
    }
}

#[test]
fn every_child_position_rejects_forward_and_missing_handles() {
    for bad in [TermId(4), TermId::SENTINEL] {
        for data in [
            TermData::Not(bad),
            TermData::Ite(bad, TermId(0), TermId(1)),
            TermData::Ite(TermId(0), bad, TermId(1)),
            TermData::Ite(TermId(0), TermId(1), bad),
            TermData::Let(vec![("a".into(), bad)], TermId(0)),
            TermData::Let(vec![], bad),
            TermData::App(Symbol::named("uf"), vec![bad]),
            TermData::Forall(vec![], bad, vec![]),
            TermData::Exists(vec![], TermId(0), vec![vec![bad]]),
        ] {
            compare((data, Sort::Bool), false);
        }
    }
}

#[test]
fn nonboolean_and_mismatched_shapes_remain_malformed() {
    for shape in [
        (TermData::Not(TermId(2)), Sort::Bool),
        (TermData::Not(TermId(0)), Sort::Int),
        (TermData::Ite(TermId(2), TermId(0), TermId(1)), Sort::Bool),
        (TermData::Ite(TermId(0), TermId(0), TermId(2)), Sort::Bool),
        (TermData::Ite(TermId(0), TermId(2), TermId(3)), Sort::Bool),
        (TermData::Let(vec![], TermId(2)), Sort::Bool),
        (TermData::Forall(vec![], TermId(2), vec![]), Sort::Bool),
        (TermData::Exists(vec![], TermId(0), vec![]), Sort::Int),
    ] {
        compare(shape, false);
    }
}

#[test]
fn repeated_binders_and_invalid_unused_binder_sorts_remain_malformed() {
    for data in [
        TermData::Let(
            vec![("a".into(), TermId(2)), ("a".into(), TermId(3))],
            TermId(0),
        ),
        TermData::Forall(
            vec![("a".into(), Sort::Int), ("a".into(), Sort::Bool)],
            TermId(0),
            vec![],
        ),
        TermData::Exists(vec![("unused".into(), Sort::bitvec(0))], TermId(0), vec![]),
    ] {
        compare((data, Sort::Bool), false);
    }
    compare((TermData::Var("unused".into(), 2), Sort::bitvec(0)), false);
}

#[test]
fn malformed_constant_kinds_and_values_match_legacy() {
    for (constant, sort) in [
        (Constant::Bool(false), Sort::Int),
        (Constant::Int(BigInt::from(1)), Sort::Real),
        (Constant::String("s".into()), Sort::Int),
        (
            Constant::BitVec {
                value: BigInt::from(-1),
                width: 8,
            },
            Sort::bitvec(8),
        ),
        (
            Constant::BitVec {
                value: BigInt::from(256),
                width: 8,
            },
            Sort::bitvec(8),
        ),
        (
            Constant::BitVec {
                value: BigInt::from(1),
                width: 7,
            },
            Sort::bitvec(8),
        ),
        (
            Constant::Rational(BigRational::new_raw(BigInt::from(1), BigInt::from(0)).into()),
            Sort::Real,
        ),
    ] {
        compare((TermData::Const(constant), sort), false);
    }
    compare(
        (
            TermData::Const(Constant::BitVec {
                value: BigInt::from(255),
                width: 8,
            }),
            Sort::bitvec(8),
        ),
        true,
    );
}

fn rational(numerator: i32, denominator: i32) -> (TermData, Sort) {
    (
        TermData::Const(Constant::Rational(
            BigRational::new_raw(BigInt::from(numerator), BigInt::from(denominator)).into(),
        )),
        Sort::Real,
    )
}

#[test]
fn canonical_admission_rejects_numeric_raw_rational_aliases_without_repair() {
    for pair in [[(1, 2), (2, 4)], [(1, -2), (-1, 2)], [(0, 7), (0, -3)]] {
        let mut values = entries();
        values.extend(pair.map(|(n, d)| rational(n, d)));
        let before = serde_json::to_vec(&values).unwrap();
        assert!(matches!(
            run(&values),
            Err(ProofCheckError::MalformedProofBundle { .. })
        ));
        assert_eq!(serde_json::to_vec(&values).unwrap(), before);
    }
    let values = vec![rational(2, 6), rational(1, -3)];
    let before = serde_json::to_vec(&values).unwrap();
    run(&values).unwrap();
    assert_eq!(serde_json::to_vec(&values).unwrap(), before);
}

#[test]
fn duplicate_keys_and_deep_unused_sorts_are_rejected_before_canonical_hashing() {
    compare(entries()[0].clone(), false);
    let mut sort = Sort::Int;
    for _ in 0..=MAX_BUNDLE_SORT_DEPTH {
        sort = Sort::seq(sort);
    }
    compare((TermData::Var("deep".into(), 2), sort.clone()), false);
    compare(
        (
            TermData::Forall(vec![("deep".into(), sort)], TermId(0), vec![]),
            Sort::Bool,
        ),
        false,
    );
}
