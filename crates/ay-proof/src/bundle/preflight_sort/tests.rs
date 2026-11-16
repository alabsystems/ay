// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{ArraySort, BitVecSort, DatatypeConstructor, DatatypeField, DatatypeSort};

use super::*;

fn fixture() -> Sort {
    Sort::Datatype(DatatypeSort::new(
        "Packet",
        vec![
            DatatypeConstructor::new(
                "packet",
                vec![
                    DatatypeField::new("tag", Sort::BitVec(BitVecSort::new(8))),
                    DatatypeField::new("data", Sort::Seq(Box::new(Sort::Int))),
                ],
            ),
            DatatypeConstructor::unit("empty"),
        ],
    ))
}

fn check(sort: &Sort, progress: Progress<'_>) -> Result<(), ProofCheckError> {
    validate_sort_with_progress(sort, 17, "test sort", 0, progress)
}

#[test]
fn metered_sort_preserves_valid_shapes_and_legacy_controls() {
    let sorts = [
        Sort::Bool,
        Sort::Int,
        Sort::Real,
        Sort::String,
        Sort::Char,
        Sort::RegLan,
        Sort::Uninterpreted(String::new()),
        Sort::TypeVar("T".into()),
        Sort::FiniteDomain("F".into(), 3),
        Sort::BitVec(BitVecSort::new(1 << 20)),
        Sort::FloatingPoint(64, 1 << 20),
        Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Bool))),
        fixture(),
    ];
    for sort in sorts {
        check(&sort, &mut |_, _| true).unwrap();
        validate_sort(&sort, 17, "test sort", 0).unwrap();
    }
    assert!(check(&Sort::FloatingPoint(65, 113), &mut |_, _| true).is_err());
}

#[test]
fn metered_sort_refuses_at_every_callback_including_final_poll() {
    let sort = fixture();
    let mut trace = Vec::new();
    check(&sort, &mut |work, bytes| {
        trace.push((work, bytes));
        true
    })
    .unwrap();
    assert_eq!(trace.last(), Some(&(0, 0)));
    for refused in 1..=trace.len() {
        let mut calls = 0;
        let result = check(&sort, &mut |_, _| {
            calls += 1;
            calls != refused
        });
        assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(calls, refused);
    }
}

#[test]
fn metered_sort_reuses_one_exact_work_and_allocation_envelope() {
    let sort = fixture();
    let (mut work, mut bytes) = (0, 0);
    check(&sort, &mut |w, b| {
        work += w;
        bytes += b;
        true
    })
    .unwrap();
    assert!(work > 0 && bytes > 0);
    for (work_limit, byte_limit, success) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
    ] {
        let (mut used_work, mut used_bytes) = (0, 0);
        let mut progress = |w, b| {
            used_work += w;
            used_bytes += b;
            used_work <= work_limit && used_bytes <= byte_limit
        };
        assert_eq!(check(&sort, &mut progress).is_ok(), success);
        assert!(matches!(
            check(&sort, &mut progress),
            Err(ProofCheckError::ResourceLimit)
        ));
    }
}

#[test]
fn metered_sort_preserves_the_inclusive_depth_boundary() {
    let mut sort = Sort::Bool;
    for _ in 0..256 {
        sort = Sort::Seq(Box::new(sort));
    }
    assert!(check(&sort, &mut |_, _| true).is_ok());
    let sort = Sort::Seq(Box::new(sort));
    assert!(matches!(
        check(&sort, &mut |_, _| true),
        Err(ProofCheckError::MalformedProofBundle { .. })
    ));
}

#[test]
fn metered_sort_retains_invalid_scalar_and_duplicate_namespace_refusals() {
    let mut sorts = vec![
        Sort::BitVec(BitVecSort { width: 0 }),
        Sort::BitVec(BitVecSort {
            width: (1 << 20) + 1,
        }),
        Sort::FloatingPoint(1, 24),
        Sort::FloatingPoint(8, 1),
        Sort::FiniteDomain("empty".into(), 0),
    ];
    let Sort::Datatype(mut duplicate) = fixture() else {
        panic!("datatype fixture");
    };
    duplicate
        .constructors
        .push(duplicate.constructors[0].clone());
    sorts.push(Sort::Datatype(duplicate));
    let Sort::Datatype(mut duplicate) = fixture() else {
        panic!("datatype fixture");
    };
    let field = duplicate.constructors[0].fields[0].clone();
    duplicate.constructors[0].fields.push(field);
    sorts.push(Sort::Datatype(duplicate));
    for sort in sorts {
        assert!(matches!(
            check(&sort, &mut |_, _| true),
            Err(ProofCheckError::MalformedProofBundle { .. })
        ));
    }
}

/// Datatype `||` with the nullary constructor `||` and the constructor `mk`
/// whose one field is `||`.
fn empty_names() -> DatatypeSort {
    DatatypeSort::new(
        "",
        vec![
            DatatypeConstructor::unit(""),
            DatatypeConstructor::new("mk", vec![DatatypeField::new("", Sort::Int)]),
        ],
    )
}

fn malformed(sort: DatatypeSort, expected: &str) {
    let result = check(&Sort::Datatype(sort), &mut |_, _| true);
    assert!(
        matches!(&result, Err(ProofCheckError::MalformedProofBundle { reason })
            if reason == expected),
        "expected {expected:?}, got {result:?}"
    );
}

#[test]
fn metered_sort_admits_empty_names_and_refuses_duplicates_and_empty_constructor_sets() {
    let sort = Sort::Datatype(empty_names());
    check(&sort, &mut |_, _| true).unwrap();
    validate_sort(&sort, 17, "test sort", 0).unwrap();

    let mut duplicate = empty_names();
    duplicate.constructors.push(DatatypeConstructor::unit(""));
    malformed(
        duplicate,
        "term t17 test sort has a duplicate datatype constructor",
    );
    let mut duplicate = empty_names();
    duplicate.constructors[1]
        .fields
        .push(DatatypeField::new("", Sort::Bool));
    malformed(
        duplicate,
        "term t17 test sort has a duplicate datatype field",
    );
    let mut no_constructors = empty_names();
    no_constructors.constructors.clear();
    malformed(
        no_constructors,
        "term t17 test sort has an empty constructor set",
    );
}

#[test]
fn metered_sort_charges_diagnostics_before_constructing_an_error_string() {
    let malformed = Sort::FloatingPoint(1, 1);
    assert!(matches!(
        check(&malformed, &mut |_, bytes| bytes == 0),
        Err(ProofCheckError::ResourceLimit)
    ));
}

#[test]
fn complex_bundle_sort_preserves_nested_shapes_and_resource_refusal() {
    for sort in [Sort::Complex, Sort::array(Sort::Int, Sort::Complex)] {
        check(&sort, &mut |_, _| true).unwrap();
        validate_sort(&sort, 17, "Complex certificate carrier", 0).unwrap();
        assert!(matches!(
            check(&sort, &mut |_, _| false),
            Err(ProofCheckError::ResourceLimit)
        ));
    }
}
