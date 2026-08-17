// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{
    AletheRule, CuttingPlaneAnnotation, DatatypeConstructor, DatatypeField, DatatypeSort,
    FarkasAnnotation, LiaAnnotation, ProofStep, Sort, TermId, TheoryLemmaKind,
};

use super::super::lemma_dedup::{
    lemma_key_fingerprint, ExistingLemma, LemmaBucket, LemmaDedupMap, LemmaKey,
};
use super::super::{HashMap, ProofId, ProofTracker};

const RICH_PAYLOAD_LEN: usize = 2_048;

fn checkpoint_charge(tracker: &ProofTracker) -> usize {
    tracker
        .checkpoint_clone_charge_for_test()
        .expect("test payload footprint is representable")
}

fn tracker_with_step(step: ProofStep) -> ProofTracker {
    let mut tracker = ProofTracker::new();
    tracker.proof.steps.push(step);
    tracker
}

fn tracker_with_lemma_map(lemma_map: LemmaDedupMap) -> ProofTracker {
    let mut tracker = ProofTracker::new();
    tracker.lemma_map = lemma_map;
    tracker
}

fn lemma_map_with_key(key: LemmaKey) -> LemmaDedupMap {
    let mut map = LemmaDedupMap::default();
    map.insert(key, ProofId(0));
    map
}

fn assert_payload_is_charged(sparse: &ProofTracker, rich: &ProofTracker, payload: &str) {
    assert!(
        checkpoint_charge(rich) > checkpoint_charge(sparse),
        "{payload} must increase the conservative checkpoint charge"
    );
}

#[test]
fn step_and_resolution_payloads_each_increase_the_charge() {
    let sparse_step = tracker_with_step(ProofStep::Step {
        rule: AletheRule::True,
        clause: Vec::new(),
        premises: Vec::new(),
        args: Vec::new(),
    });
    let rich_string = "x".repeat(RICH_PAYLOAD_LEN * 4);
    assert_payload_is_charged(
        &sparse_step,
        &tracker_with_step(ProofStep::Step {
            rule: AletheRule::Custom(rich_string.clone()),
            clause: Vec::new(),
            premises: Vec::new(),
            args: Vec::new(),
        }),
        "custom rule name",
    );
    for (payload, clause, premises, args) in [
        (
            "step clause",
            vec![TermId(1); RICH_PAYLOAD_LEN],
            Vec::new(),
            Vec::new(),
        ),
        (
            "step premises",
            Vec::new(),
            vec![ProofId(0); RICH_PAYLOAD_LEN],
            Vec::new(),
        ),
        (
            "step args",
            Vec::new(),
            Vec::new(),
            vec![TermId(2); RICH_PAYLOAD_LEN],
        ),
    ] {
        assert_payload_is_charged(
            &sparse_step,
            &tracker_with_step(ProofStep::Step {
                rule: AletheRule::True,
                clause,
                premises,
                args,
            }),
            payload,
        );
    }

    let sparse_resolution = tracker_with_step(ProofStep::Resolution {
        clause: Vec::new(),
        pivot: TermId(0),
        clause1: ProofId(0),
        clause2: ProofId(0),
    });
    assert_payload_is_charged(
        &sparse_resolution,
        &tracker_with_step(ProofStep::Resolution {
            clause: vec![TermId(3); RICH_PAYLOAD_LEN],
            pivot: TermId(0),
            clause1: ProofId(0),
            clause2: ProofId(0),
        }),
        "resolution clause",
    );
}

#[test]
fn theory_payloads_each_increase_the_charge() {
    let rich_string = "x".repeat(RICH_PAYLOAD_LEN * 4);
    let sparse_theory = tracker_with_step(ProofStep::TheoryLemma {
        theory: String::new(),
        clause: Vec::new(),
        farkas: None,
        kind: TheoryLemmaKind::LiaGeneric,
        lia: None,
    });
    let theory_variants = [
        ProofStep::TheoryLemma {
            theory: rich_string.clone(),
            clause: Vec::new(),
            farkas: None,
            kind: TheoryLemmaKind::LiaGeneric,
            lia: None,
        },
        ProofStep::TheoryLemma {
            theory: String::new(),
            clause: vec![TermId(4); RICH_PAYLOAD_LEN],
            farkas: None,
            kind: TheoryLemmaKind::LiaGeneric,
            lia: None,
        },
        ProofStep::TheoryLemma {
            theory: String::new(),
            clause: Vec::new(),
            farkas: Some(FarkasAnnotation::from_ints(&vec![1; RICH_PAYLOAD_LEN])),
            kind: TheoryLemmaKind::LiaGeneric,
            lia: None,
        },
        ProofStep::TheoryLemma {
            theory: String::new(),
            clause: Vec::new(),
            farkas: None,
            kind: TheoryLemmaKind::LiaGeneric,
            lia: Some(LiaAnnotation::CuttingPlane(CuttingPlaneAnnotation {
                farkas: FarkasAnnotation::from_ints(&vec![1; RICH_PAYLOAD_LEN]),
                divisor: 2,
            })),
        },
    ];
    for (payload, step) in ["theory name", "theory clause", "Farkas", "cutting plane"]
        .into_iter()
        .zip(theory_variants)
    {
        assert_payload_is_charged(&sparse_theory, &tracker_with_step(step), payload);
    }
}

#[test]
fn anchor_payloads_each_increase_the_charge() {
    let rich_string = "x".repeat(RICH_PAYLOAD_LEN * 4);
    let sparse_anchor = tracker_with_step(ProofStep::Anchor {
        end_step: ProofId(0),
        variables: Vec::new(),
    });
    assert_payload_is_charged(
        &sparse_anchor,
        &tracker_with_step(ProofStep::Anchor {
            end_step: ProofId(0),
            variables: vec![(String::new(), Sort::Int); RICH_PAYLOAD_LEN],
        }),
        "anchor variables",
    );
    assert_payload_is_charged(
        &sparse_anchor,
        &tracker_with_step(ProofStep::Anchor {
            end_step: ProofId(0),
            variables: vec![(rich_string.clone(), Sort::Int)],
        }),
        "anchor variable name",
    );
    let nested_sort = Sort::Datatype(DatatypeSort::new(
        rich_string.clone(),
        vec![DatatypeConstructor::new(
            rich_string.clone(),
            vec![DatatypeField::new(
                rich_string,
                Sort::seq(Sort::array(Sort::Int, Sort::Uninterpreted("U".to_string()))),
            )],
        )],
    ));
    assert_payload_is_charged(
        &sparse_anchor,
        &tracker_with_step(ProofStep::Anchor {
            end_step: ProofId(0),
            variables: vec![(String::new(), nested_sort)],
        }),
        "nested anchor sort",
    );
}

#[test]
fn named_and_scope_maps_each_increase_the_charge() {
    let sparse = ProofTracker::new();
    let rich_name = "n".repeat(RICH_PAYLOAD_LEN * 4);
    let mut named = ProofTracker::new();
    named
        .proof
        .named_steps
        .insert(rich_name.clone(), ProofId(0));
    assert_payload_is_charged(&sparse, &named, "top-level named map");

    let mut scope_named = ProofTracker::new();
    let mut named_map = HashMap::default();
    named_map.insert(rich_name, ProofId(0));
    scope_named.scope_named_steps.push(named_map);
    assert_payload_is_charged(&sparse, &scope_named, "scoped named map");

    let mut scope_assumptions = ProofTracker::new();
    let mut assumption_map = HashMap::default();
    assumption_map.reserve(RICH_PAYLOAD_LEN);
    assumption_map.insert(TermId(1), ProofId(0));
    scope_assumptions.scope_assumption_maps.push(assumption_map);
    assert_payload_is_charged(&sparse, &scope_assumptions, "scoped assumption map");

    let mut scope_lemmas = ProofTracker::new();
    let mut lemma_map = LemmaDedupMap::default();
    lemma_map.buckets.reserve(RICH_PAYLOAD_LEN);
    lemma_map.insert(
        LemmaKey::new(TheoryLemmaKind::Generic, &[TermId(2)], None),
        ProofId(0),
    );
    scope_lemmas.scope_lemma_maps.push(lemma_map);
    assert_payload_is_charged(&sparse, &scope_lemmas, "scoped lemma map");
}

#[test]
fn lemma_dedup_bucket_shapes_each_increase_the_charge() {
    let empty = ProofTracker::new();
    let mut retained_empty = LemmaDedupMap::default();
    retained_empty.buckets.reserve(RICH_PAYLOAD_LEN);
    retained_empty.clear();
    assert_payload_is_charged(
        &empty,
        &tracker_with_lemma_map(retained_empty),
        "cleared lemma bucket table capacity",
    );

    let sparse_key = LemmaKey::new(TheoryLemmaKind::Generic, &[TermId(1)], None);
    let sparse = tracker_with_lemma_map(lemma_map_with_key(sparse_key));

    let mut bucket_table =
        lemma_map_with_key(LemmaKey::new(TheoryLemmaKind::Generic, &[TermId(1)], None));
    bucket_table.buckets.reserve(RICH_PAYLOAD_LEN);
    assert_payload_is_charged(
        &sparse,
        &tracker_with_lemma_map(bucket_table),
        "lemma fingerprint bucket table",
    );

    let collision_key = LemmaKey::new(TheoryLemmaKind::Generic, &[TermId(1)], None);
    let mut collision_entries = vec![(collision_key.clone(), ProofId(0))];
    collision_entries.reserve(RICH_PAYLOAD_LEN);
    let mut collision_bucket = LemmaDedupMap::default();
    collision_bucket.buckets.insert(
        lemma_key_fingerprint(&collision_key),
        LemmaBucket::Many(collision_entries),
    );
    collision_bucket.entries = 1;
    assert_payload_is_charged(
        &sparse,
        &tracker_with_lemma_map(collision_bucket),
        "lemma collision bucket capacity",
    );

    let clause = vec![TermId(2); RICH_PAYLOAD_LEN];
    let rich_clause = lemma_map_with_key(LemmaKey::new(TheoryLemmaKind::Generic, &clause, None));
    assert_payload_is_charged(
        &sparse,
        &tracker_with_lemma_map(rich_clause),
        "lemma key clause",
    );

    let coefficients = vec![1; RICH_PAYLOAD_LEN];
    let farkas = FarkasAnnotation::from_ints(&coefficients);
    let rich_farkas = lemma_map_with_key(LemmaKey::new(
        TheoryLemmaKind::LraFarkas,
        &[TermId(3)],
        Some(&farkas),
    ));
    assert_payload_is_charged(
        &sparse,
        &tracker_with_lemma_map(rich_farkas),
        "lemma key Farkas payload",
    );
}

#[test]
fn lemma_dedup_singleton_is_inline_and_collision_promotes() {
    let first = LemmaKey::new(TheoryLemmaKind::Generic, &[TermId(1)], None);
    let fingerprint = lemma_key_fingerprint(&first);
    let mut map = LemmaDedupMap::default();
    map.insert(first.clone(), ProofId(1));
    assert!(matches!(
        map.buckets.get(&fingerprint),
        Some(LemmaBucket::One(_))
    ));
    map.insert(first.clone(), ProofId(3));
    assert_eq!(map.entries, 1);
    assert_eq!(
        map.get(TheoryLemmaKind::Generic, &[TermId(1)], None),
        Some(ProofId(3)),
        "insert replaces an exact key"
    );
    map.or_insert(first, ProofId(4));
    assert_eq!(map.entries, 1);
    assert_eq!(
        map.get(TheoryLemmaKind::Generic, &[TermId(1)], None),
        Some(ProofId(3)),
        "or_insert preserves an exact key"
    );

    let collision = LemmaKey::new(TheoryLemmaKind::Generic, &[TermId(2)], None);
    assert!(map
        .buckets
        .get_mut(&fingerprint)
        .expect("singleton bucket exists")
        .insert(collision, ProofId(2), ExistingLemma::Preserve));
    assert!(matches!(
        map.buckets.get(&fingerprint),
        Some(LemmaBucket::Many(entries)) if entries.len() == 2
    ));
}
