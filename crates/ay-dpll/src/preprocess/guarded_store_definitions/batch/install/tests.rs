// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::ProofStep;

#[path = "../tests/fixtures.rs"]
mod fixtures;
use fixtures::Fixture;

fn sources(roots: &[TermId]) -> Vec<Vec<TermId>> {
    roots.iter().map(|&root| vec![root]).collect()
}

#[test]
fn complete_units_precede_unchanged_originals_and_move_existing_proof_buffers() {
    let mut fixture = Fixture::new(129);
    fixture.roots.push(fixture.roots[0]);
    let originals = fixture.roots.clone();
    let source_sets = sources(&originals);
    let batch = fixture.discover().unwrap();
    let expected: Vec<_> = batch
        .definitions()
        .iter()
        .map(|definition| (definition.definition(), definition.proof().0.steps.as_ptr()))
        .chain(
            batch
                .activated_units()
                .iter()
                .map(|unit| (unit.unit(), unit.proof().0.steps.as_ptr())),
        )
        .collect();
    assert_eq!(expected.len(), 4);
    let prepared = prepare(
        &fixture.terms,
        &originals,
        &originals,
        &source_sets,
        batch,
        &mut |_, _| true,
    )
    .unwrap();
    let (working, prepared_sources, units) = prepared.into_parts();
    assert_eq!(&working[expected.len()..], originals);
    assert_eq!(&prepared_sources[expected.len()..], source_sets);
    assert!(prepared_sources[..expected.len()].iter().all(Vec::is_empty));
    assert_eq!(fixture.roots, originals);
    for (position, (unit, &(term, steps))) in units.iter().zip(&expected).enumerate() {
        assert_eq!(working[position], term);
        assert_eq!(unit.term(), term);
        let (proof, _) = unit
            .reauthenticate(&fixture.terms, &originals, &mut |_, _| true)
            .unwrap();
        assert_eq!(proof.steps.as_ptr(), steps, "no deep proof clone");
    }
}

#[test]
fn existing_working_order_duplicates_and_nested_source_sets_are_not_reauthored() {
    let mut fixture = Fixture::new(2);
    let batch = fixture.discover().unwrap();
    let working = vec![fixture.roots[2], fixture.roots[0], fixture.roots[2]];
    let source_sets = vec![
        vec![fixture.roots[3], fixture.roots[2], fixture.roots[3]],
        Vec::new(),
        vec![fixture.roots[2]],
    ];
    let (result, result_sources, units) = prepare(
        &fixture.terms,
        &fixture.roots,
        &working,
        &source_sets,
        batch,
        &mut |_, _| true,
    )
    .unwrap()
    .into_parts();
    assert_eq!(&result[units.len()..], working);
    assert_eq!(&result_sources[units.len()..], source_sets);
    assert_eq!(result.len(), units.len() + working.len());
    assert!(!result[units.len()..].contains(&fixture.roots[1]));
}

#[test]
fn changed_original_order_and_retagged_missing_activation_both_refuse() {
    for retagged in [false, true] {
        let mut fixture = Fixture::new(129);
        let mut batch = fixture.discover().unwrap();
        let mut originals = fixture.roots.clone();
        if retagged {
            originals[3] = fixture.terms.true_term();
            batch.original_roots = originals.clone();
        } else {
            originals.swap(0, 1);
        }
        let source_sets = sources(&originals);
        assert!(prepare(
            &fixture.terms,
            &originals,
            &originals,
            &source_sets,
            batch,
            &mut |_, _| true,
        )
        .is_none());
        assert_eq!(source_sets, sources(&originals));
    }
}

#[test]
fn final_unit_proof_mutation_never_returns_the_already_checked_prefix() {
    let mut fixture = Fixture::new(129);
    let mut batch = fixture.discover().unwrap();
    let unit = batch.activated_units.last_mut().unwrap();
    let ProofStep::Step { clause, .. } = &mut unit.proof.steps[unit.conclusion.0 as usize] else {
        panic!("derived resolution conclusion")
    };
    clause[0] = fixture.terms.false_term();
    let originals = fixture.roots.clone();
    let source_sets = sources(&originals);
    assert!(prepare(
        &fixture.terms,
        &originals,
        &originals,
        &source_sets,
        batch,
        &mut |_, _| true,
    )
    .is_none());
    assert_eq!(fixture.roots, originals);
    assert_eq!(source_sets, sources(&originals));
}

#[test]
fn malformed_working_rows_and_source_metadata_refuse_before_publication() {
    for change in 0..4 {
        let mut fixture = Fixture::new(2);
        let batch = fixture.discover().unwrap();
        let mut working = fixture.roots.clone();
        let mut source_sets = sources(&working);
        match change {
            0 => {
                source_sets.pop();
            }
            1 => working[0] = TermId(u32::MAX),
            2 => source_sets[0].push(TermId(u32::MAX)),
            3 => source_sets[0].push(fixture.variable),
            _ => unreachable!(),
        }
        assert!(prepare(
            &fixture.terms,
            &fixture.roots,
            &working,
            &source_sets,
            batch,
            &mut |_, _| true,
        )
        .is_none());
    }
}

fn pipeline(progress: Progress<'_>) -> Option<PreparedArrayUnits> {
    let mut fixture = Fixture::new(2);
    let source_sets = sources(&fixture.roots);
    let original = fixture.roots.clone();
    let batch = discover(&mut fixture.terms, &fixture.roots, progress)?;
    let result = prepare(
        &fixture.terms,
        &original,
        &fixture.roots,
        &source_sets,
        batch,
        progress,
    );
    assert_eq!(fixture.roots, original);
    assert_eq!(source_sets, sources(&original));
    result
}

#[test]
fn discovery_and_install_share_exact_work_bytes_and_final_publication_refusal() {
    let mut charges = Vec::new();
    assert!(pipeline(&mut |work, bytes| {
        charges.push((work, bytes));
        true
    })
    .is_some());
    let (work, bytes) = charges
        .iter()
        .fold((0usize, 0usize), |(w, b), &(dw, db)| (w + dw, b + db));
    for (mut work, mut bytes, success) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
    ] {
        assert_eq!(
            pipeline(&mut |dw, db| {
                let (Some(w), Some(b)) = (work.checked_sub(dw), bytes.checked_sub(db)) else {
                    return false;
                };
                (work, bytes) = (w, b);
                true
            })
            .is_some(),
            success
        );
    }
    for limit in [0, charges.len() / 2, charges.len() - 1] {
        let mut calls = 0;
        assert!(pipeline(&mut |_, _| {
            calls += 1;
            calls <= limit
        })
        .is_none());
        assert!(pipeline(&mut |_, _| true).is_some());
    }
}

#[test]
fn empty_batch_preserves_rows_and_storage_overflow_never_allocates() {
    let mut fixture = Fixture::new(2);
    fixture.roots.pop();
    let batch = fixture.discover().unwrap();
    let source_sets = sources(&fixture.roots);
    let (working, kept_sources, units) = prepare(
        &fixture.terms,
        &fixture.roots,
        &fixture.roots,
        &source_sets,
        batch,
        &mut |_, _| true,
    )
    .unwrap()
    .into_parts();
    assert!(units.is_empty());
    assert_eq!(working, fixture.roots);
    assert_eq!(kept_sources, source_sets);
    assert!(storage::allocate(
        &[fixture.roots[0]],
        &[Vec::new()],
        usize::MAX,
        &mut |_, _| { panic!("overflow must be detected before allocation charge") }
    )
    .is_none());
}
