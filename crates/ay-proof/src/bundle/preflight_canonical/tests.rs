// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use num_bigint::BigInt;
use num_rational::BigRational;

use super::*;

mod arithmetic;

fn rational(numerator: i64, denominator: i64) -> TermData {
    TermData::Const(Constant::Rational(
        BigRational::new_raw(BigInt::from(numerator), BigInt::from(denominator)).into(),
    ))
}

fn insert_all(
    values: &[(TermData, Sort)],
    progress: Progress<'_>,
) -> Result<Vec<bool>, ProofCheckError> {
    let mut index = CanonicalEntries::new();
    let mut answers = Vec::new();
    for (data, sort) in values {
        answers.push(index.insert(data, sort, progress)?);
    }
    Ok(answers)
}

fn usage(values: &[(TermData, Sort)]) -> (usize, usize, usize) {
    let (mut work, mut bytes, mut polls) = (0usize, 0usize, 0usize);
    insert_all(values, &mut |w, b| {
        work = work.checked_add(w).expect("small fixture work");
        bytes = bytes.checked_add(b).expect("small fixture bytes");
        polls = polls.saturating_add(1);
        true
    })
    .expect("valid entries");
    (work, bytes, polls)
}

#[test]
fn canonical_entries_detect_numeric_raw_rational_duplicates_without_normalizing() {
    let values: Vec<_> = [
        (1, 2),
        (2, 4),
        (-3, -6),
        (1, -2),
        (-1, 2),
        (0, 3),
        (0, -17),
        (2, 1),
        (4, 2),
        (1, 3),
    ]
    .into_iter()
    .map(|(numerator, denominator)| (rational(numerator, denominator), Sort::Real))
    .collect();
    let original = serde_json::to_vec(&values).unwrap();
    assert_eq!(
        insert_all(&values, &mut |_, _| true).unwrap(),
        vec![true, false, false, true, false, true, false, true, false, true]
    );
    assert_eq!(serde_json::to_vec(&values).unwrap(), original);
}

#[test]
fn canonical_entries_compare_complete_term_and_sort_identity() {
    let values = vec![
        (TermData::Var("x".to_string(), 0), Sort::Int),
        (TermData::Var("x".to_string(), 1), Sort::Int),
        (TermData::Var("X".to_string(), 0), Sort::Int),
        (TermData::Var("x".to_string(), 0), Sort::Bool),
        (TermData::Var("x".to_string(), 0), Sort::Int),
        (
            TermData::App(Symbol::named("f"), vec![TermId(0)]),
            Sort::Int,
        ),
        (
            TermData::App(Symbol::named("f"), vec![TermId(1)]),
            Sort::Int,
        ),
        (
            TermData::App(Symbol::indexed("f", vec![0]), vec![TermId(0)]),
            Sort::Int,
        ),
        (
            TermData::App(Symbol::named("f"), vec![TermId(0)]),
            Sort::Int,
        ),
    ];
    assert_eq!(
        insert_all(&values, &mut |_, _| true).unwrap(),
        vec![true, true, true, true, false, true, true, true, false]
    );
}

#[test]
fn canonical_entries_price_wide_hashes_and_owning_sort_walks_before_work() {
    let name = "n".repeat(16_384);
    let data = TermData::Var(name, 0);
    let mut saw_hash = false;
    let mut index = CanonicalEntries::new();
    let result = index.insert(&data, &Sort::Int, &mut |work, _| {
        saw_hash |= work >= 16_384;
        work < 16_384
    });
    assert_eq!(result, Err(ProofCheckError::ResourceLimit));
    assert!(saw_hash);
    assert!(index.insert(&data, &Sort::Int, &mut |_, _| true).unwrap());

    let wide = Sort::Datatype(ay_core::DatatypeSort::new(
        "Wide",
        vec![ay_core::DatatypeConstructor::new(
            "wide",
            (0..1_024)
                .map(|i| ay_core::DatatypeField::new(format!("field-{i}"), Sort::Int))
                .collect(),
        )],
    ));
    let mut spent = 0usize;
    let mut index = CanonicalEntries::new();
    assert_eq!(
        index.insert(&data, &wide, &mut |work, _| {
            spent += work;
            spent <= 100
        }),
        Err(ProofCheckError::ResourceLimit)
    );
    assert_eq!(
        spent, 101,
        "metadata traversal itself is incrementally cancellable"
    );
}

#[test]
fn canonical_entries_price_wide_arguments_indices_and_quantifier_trigger_payloads() {
    let values = [
        TermData::App(Symbol::named("f"), vec![TermId(0); 4_096]),
        TermData::App(Symbol::indexed("f", vec![1; 4_096]), Vec::new()),
        TermData::Forall(
            vec![("q".to_string(), Sort::Int)],
            TermId(0),
            vec![vec![TermId(0); 4_096]],
        ),
        TermData::Exists(
            vec![("q".to_string(), Sort::Uninterpreted("Q".repeat(4_096)))],
            TermId(0),
            Vec::new(),
        ),
        TermData::Const(Constant::Int(BigInt::from_slice(
            Sign::Plus,
            &vec![u32::MAX; 4_096],
        ))),
        TermData::Const(Constant::String("text".repeat(4_096))),
    ];
    for data in &values {
        let mut index = CanonicalEntries::new();
        let mut saw_payload = false;
        assert_eq!(
            index.insert(data, &Sort::Bool, &mut |work, _| {
                saw_payload |= work >= 4_096;
                work < 4_096
            }),
            Err(ProofCheckError::ResourceLimit)
        );
        assert!(saw_payload);
    }
}

#[test]
fn canonical_duplicate_comparison_prices_the_entire_sort_before_eq() {
    let data = TermData::Var("x".to_string(), 0);
    let sort = Sort::Uninterpreted("s".repeat(8_192));
    let mut index = CanonicalEntries::new();
    assert!(index.insert(&data, &sort, &mut |_, _| true).unwrap());
    let mut saw_sort_eq = false;
    assert_eq!(
        index.insert(&data, &sort, &mut |work, _| {
            saw_sort_eq |= work >= 16_384;
            work < 16_384
        }),
        Err(ProofCheckError::ResourceLimit)
    );
    assert!(saw_sort_eq);
    assert!(!index.insert(&data, &sort, &mut |_, _| true).unwrap());
}

fn entry<'a>(data: &'a TermData, sort: &'a Sort) -> CanonicalEntry<'a> {
    let mut progress = |_, _| true;
    let mut meter = CanonicalMeter::new(&mut progress);
    CanonicalEntry {
        data,
        sort,
        data_work: payload::data(data, &mut meter).unwrap(),
        sort_work: payload::sort(sort, &mut meter, 0).unwrap(),
    }
}

#[test]
fn canonical_collision_candidates_pay_full_equality_cost_and_keep_distinct_keys() {
    let left = TermData::Var(format!("{}a", "x".repeat(8_192)), 0);
    let right = TermData::Var(format!("{}b", "x".repeat(8_192)), 0);
    let sort = Sort::Int;
    let mut bucket = vec![entry(&left, &sort)];
    let mut saw_compare = false;
    let mut progress = |work, _| {
        saw_compare |= work >= 16_384;
        work < 16_384
    };
    let mut meter = CanonicalMeter::new(&mut progress);
    assert_eq!(
        insert_bucket(&mut bucket, entry(&right, &sort), &mut meter),
        Err(ProofCheckError::ResourceLimit)
    );
    assert!(saw_compare);
    assert_eq!(bucket.len(), 1);
    let mut progress = |_, _| true;
    let mut meter = CanonicalMeter::new(&mut progress);
    assert!(insert_bucket(&mut bucket, entry(&right, &sort), &mut meter).unwrap());
    assert!(!insert_bucket(&mut bucket, entry(&right, &sort), &mut meter).unwrap());
}

#[test]
fn canonical_entries_cancel_at_every_poll_including_all_final_publication_polls() {
    let values = vec![
        (TermData::Var("x".to_string(), 0), Sort::Int),
        (rational(1, 2), Sort::Real),
        (rational(2, 4), Sort::Real),
        (rational(2, 3), Sort::Real),
        (TermData::Var("x".to_string(), 0), Sort::Int),
    ];
    let (_, _, polls) = usage(&values);
    for stop in 1..=polls {
        let mut calls = 0;
        assert_eq!(
            insert_all(&values, &mut |_, _| {
                calls += 1;
                calls != stop
            }),
            Err(ProofCheckError::ResourceLimit)
        );
        assert_eq!(calls, stop);
    }
    for (data, sort) in &values {
        let mut measured = 0;
        CanonicalEntries::new()
            .insert(data, sort, &mut |_, _| {
                measured += 1;
                true
            })
            .unwrap();
        let mut index = CanonicalEntries::new();
        let mut calls = 0;
        assert_eq!(
            index.insert(data, sort, &mut |_, _| {
                calls += 1;
                calls != measured
            }),
            Err(ProofCheckError::ResourceLimit)
        );
        assert!(index.insert(data, sort, &mut |_, _| true).unwrap());
    }
}

#[test]
fn canonical_entries_share_exact_work_and_allocation_allowances_across_insertions() {
    let values: Vec<_> = (1..=8).map(|n| (rational(n, 19), Sort::Real)).collect();
    let (work, bytes, _) = usage(&values);
    for (work_limit, byte_limit, accepted) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
    ] {
        let (mut used_work, mut used_bytes) = (0usize, 0usize);
        let result = insert_all(&values, &mut |w, b| {
            used_work = used_work.checked_add(w).unwrap();
            used_bytes = used_bytes.checked_add(b).unwrap();
            used_work <= work_limit && used_bytes <= byte_limit
        });
        assert_eq!(result.is_ok(), accepted);
        if !accepted {
            assert_eq!(result, Err(ProofCheckError::ResourceLimit));
        }
    }
}

#[test]
fn canonical_entries_refuse_allocations_before_index_mutation() {
    let values = [
        (TermData::Var("plain".to_string(), 0), Sort::Int),
        (rational(1, 2), Sort::Real),
    ];
    for (data, sort) in &values {
        let mut index = CanonicalEntries::new();
        assert_eq!(
            index.insert(data, sort, &mut |_, bytes| bytes == 0),
            Err(ProofCheckError::ResourceLimit)
        );
        assert!(index.insert(data, sort, &mut |_, _| true).unwrap());
    }
    let mut progress = |_, _| true;
    let mut meter = CanonicalMeter::new(&mut progress);
    assert_eq!(
        meter.zero_limbs(usize::MAX),
        Err(ProofCheckError::ResourceLimit)
    );
}

#[test]
fn canonical_bucket_map_nodes_and_existing_bucket_growth_are_precharged() {
    let plain = TermData::Var("plain".to_string(), 0);
    let mut index = CanonicalEntries::new();
    let mut allocations = 0;
    assert_eq!(
        index.insert(&plain, &Sort::Int, &mut |_, bytes| {
            allocations += usize::from(bytes != 0);
            allocations < 2
        }),
        Err(ProofCheckError::ResourceLimit)
    );
    assert_eq!(
        allocations, 2,
        "the node charge follows the local bucket buffer"
    );
    assert!(index.buckets.is_empty());
    assert!(index.insert(&plain, &Sort::Int, &mut |_, _| true).unwrap());

    let values: Vec<_> = (1..=5).map(|n| rational(n, 19)).collect();
    let mut index = CanonicalEntries::new();
    for data in &values[..4] {
        assert!(index.insert(data, &Sort::Real, &mut |_, _| true).unwrap());
    }
    assert_eq!(
        index.insert(&values[4], &Sort::Real, &mut |_, bytes| bytes == 0),
        Err(ProofCheckError::ResourceLimit)
    );
    assert_eq!(index.rationals.len(), 4);
    assert!(index
        .insert(&values[4], &Sort::Real, &mut |_, _| true)
        .unwrap());
}

#[test]
fn canonical_entries_fail_closed_for_zero_denominator_and_overdeep_sort() {
    let invalid = rational(1, 0);
    assert!(matches!(
        CanonicalEntries::new().insert(&invalid, &Sort::Real, &mut |_, _| true),
        Err(ProofCheckError::MalformedProofBundle { reason }) if reason.contains("zero denominator")
    ));
    let mut sort = Sort::Int;
    for _ in 0..258 {
        sort = Sort::Seq(Box::new(sort));
    }
    assert_eq!(
        CanonicalEntries::new().insert(&TermData::Not(TermId(0)), &sort, &mut |_, _| true),
        Err(ProofCheckError::ResourceLimit)
    );
}
