// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Consumer-facing certificate APIs, without compiling the entire unit-test
//! module tree. This target also builds the normal ay-core library used by
//! downstream proof/NRA crates; no verification flags are overridden here.

use ay_core::{
    NraSosCertificate, NraSosOrigin, NraSosRational, NraSosTerm, ProofStep, Sort, TermId,
    TermSnapshotError, TermStore,
};
use num_bigint::BigInt;

fn rational(value: i64) -> NraSosRational {
    NraSosRational {
        numerator: BigInt::from(value),
        denominator: BigInt::from(1),
    }
}

#[test]
fn native_sos_dto_preserves_ordered_positions_through_public_serde() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("public_sos_x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let zero = terms.mk_int(BigInt::from(0));
    let lower = terms.mk_ge(x, one);
    let upper = terms.mk_le(x, zero);
    let clause = vec![terms.mk_not(lower), terms.mk_not(upper)];
    let certificate = NraSosCertificate {
        basis: vec![vec![], vec![x]],
        gram: vec![vec![rational(0); 2]; 2],
        terms: vec![
            NraSosTerm {
                origin: NraSosOrigin::ClauseLiteral { position: 0 },
                multiplier: rational(1),
            },
            NraSosTerm {
                origin: NraSosOrigin::ClauseLiteral { position: 1 },
                multiplier: rational(1),
            },
        ],
        rhs: rational(-1),
    };
    certificate.validate_shape().unwrap();
    let step = ProofStep::NraSos {
        clause,
        certificate,
    };
    let bytes = serde_json::to_vec(&step).unwrap();
    let decoded: ProofStep = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(decoded, step);
    // These public DTOs are evidence only; this is deliberately not an UNSAT
    // claim. The ay-proof integration tests perform independent semantics.
}

#[test]
fn public_snapshot_reconstruction_preserves_ids_and_raw_metadata() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("snapshot_x", Sort::Int);
    terms.mk_int(BigInt::from(1) << 1024usize);
    let (mut work, mut bytes) = (0, 0);
    let mut progress = |w, b| {
        work += w;
        bytes += b;
        true
    };
    let entries = terms.entries_snapshot_with_progress(&mut progress).unwrap();
    let (true_term, false_term) = terms.boolean_constant_ids();
    let restored = TermStore::from_entries_with_progress(
        &entries,
        true_term,
        false_term,
        terms.var_counter(),
        &mut progress,
    )
    .unwrap();
    assert_eq!(restored.entries_snapshot(), entries);
    assert_eq!(restored.get(x), terms.get(x));
    assert_eq!(restored.boolean_constant_ids(), (true_term, false_term));
    assert_ne!(restored.entry_stamp(x), terms.entry_stamp(x));
    assert_eq!(restored.instance_term_bytes(), 0);
    assert!(work > 0 && bytes > 0);
}

#[test]
fn public_snapshot_operations_share_the_callers_cumulative_envelope() {
    let terms = TermStore::new();
    let mut required = 0;
    terms
        .entries_snapshot_with_progress(&mut |_, bytes| {
            required += bytes;
            true
        })
        .unwrap();
    let mut spent = 0;
    let mut progress = |_, bytes| {
        spent += bytes;
        spent <= required
    };
    let entries = terms.entries_snapshot_with_progress(&mut progress).unwrap();
    let (true_term, false_term) = terms.boolean_constant_ids();
    assert!(matches!(
        TermStore::from_entries_with_progress(&entries, true_term, false_term, 0, &mut progress,),
        Err(TermSnapshotError::ResourceLimit)
    ));
}

#[test]
fn public_snapshot_cancellation_cannot_return_partial_evidence() {
    let mut terms = TermStore::new();
    terms.mk_string("unused".repeat(1024));
    let mut polls = 0;
    terms
        .entries_snapshot_with_progress(&mut |_, _| {
            polls += 1;
            true
        })
        .unwrap();
    for stop in 1..=polls {
        let mut calls = 0;
        assert!(matches!(
            terms.entries_snapshot_with_progress(&mut |_, _| {
                calls += 1;
                calls != stop
            }),
            Err(TermSnapshotError::ResourceLimit)
        ));
        assert_eq!(calls, stop);
    }
}

#[test]
fn public_snapshot_copy_does_not_authenticate_or_repair_boolean_handles() {
    let raw = TermStore::from_entries(vec![], None, Some(TermId::new(u32::MAX)), 17);
    let entries = raw
        .entries_snapshot_with_progress(&mut |_, _| true)
        .unwrap();
    let ids = raw.boolean_constant_ids();
    let copied = TermStore::from_entries_with_progress(
        &entries,
        ids.0,
        ids.1,
        raw.var_counter(),
        &mut |_, _| true,
    )
    .unwrap();
    assert_eq!(copied.boolean_constant_ids(), ids);
    assert_eq!(copied.var_counter(), 17);
}

#[test]
fn public_name_restoration_moves_authority_without_changing_the_term_snapshot() {
    let mut source = TermStore::new();
    source.mk_var("external_witness", Sort::Int);
    let entries = source.entries_snapshot();
    let ids = source.boolean_constant_ids();
    let raw = TermStore::from_entries(entries.clone(), ids.0, ids.1, source.var_counter());
    assert!(!raw.is_skolem_symbol("external_witness"));
    // Registration is a mechanism, not authentication: a real bundle reader
    // must prove freshness/substitution/dependency provenance before this call.
    let restored = raw
        .with_skolem_symbols_with_progress(
            vec!["external_witness".into(), "external_witness".into()],
            &mut |_, _| true,
        )
        .unwrap();
    assert_eq!(restored.entries_snapshot(), entries);
    assert_eq!(restored.boolean_constant_ids(), ids);
    assert_eq!(restored.checker_visible_metadata_generation(), 1);
    assert!(restored.is_skolem_symbol("external_witness"));
    assert!(!restored.is_skolem_symbol("missing"));
}

#[test]
fn public_name_restoration_refuses_every_callback_without_a_partial_store() {
    let names = || vec!["first".to_owned(), "second".to_owned()];
    let mut count = 0;
    TermStore::new()
        .with_skolem_symbols_with_progress(names(), &mut |_, _| {
            count += 1;
            true
        })
        .unwrap();
    for stop in 1..=count {
        let mut calls = 0;
        assert!(matches!(
            TermStore::new().with_skolem_symbols_with_progress(names(), &mut |_, _| {
                calls += 1;
                calls != stop
            }),
            Err(TermSnapshotError::ResourceLimit)
        ));
        assert_eq!(calls, stop);
    }
}
