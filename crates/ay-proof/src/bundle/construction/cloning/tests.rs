// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::super::cancellation_fixtures as fixtures;
use super::*;

fn usage(bundle: &SerializableProofBundle) -> (usize, usize, usize) {
    let (mut work, mut bytes, mut polls) = (0, 0, 0);
    bundle
        .try_clone_with_progress(&mut |w, b| {
            work += w;
            bytes += b;
            polls += 1;
            true
        })
        .unwrap();
    (work, bytes, polls)
}

#[test]
fn raw_bundle_clone_preserves_boolean_datatype_and_skolem_bytes_and_replay() {
    for bundle in [
        fixtures::contradiction(true),
        fixtures::datatype(),
        fixtures::skolem(),
    ] {
        let copied = bundle.try_clone_with_progress(&mut |_, _| true).unwrap();
        assert_eq!(
            serde_json::to_vec(&copied).unwrap(),
            serde_json::to_vec(&bundle).unwrap()
        );
        let old = re_check_bundle_strict(&bundle).unwrap();
        let new = re_check_bundle_strict(&copied).unwrap();
        assert!(new.quality.is_complete());
        assert_eq!(old.assume_terms, new.assume_terms);
    }
}

#[test]
fn raw_bundle_clone_preserves_malformed_metadata_without_granting_authority() {
    let mut bundle = fixtures::contradiction(false);
    bundle.schema = "foreign-schema".repeat(64);
    bundle.true_term = None;
    bundle.false_term = Some(TermId(u32::MAX));
    bundle.var_counter = u32::MAX;
    bundle.obligation_assertions.push(TermId(u32::MAX));
    let copied = bundle.try_clone_with_progress(&mut |_, _| true).unwrap();
    assert_eq!(
        serde_json::to_vec(&copied).unwrap(),
        serde_json::to_vec(&bundle).unwrap()
    );
    assert!(re_check_bundle_strict(&copied).is_err());
}

#[test]
fn raw_bundle_clone_refuses_every_checkpoint_then_allows_a_fresh_attempt() {
    let bundle = fixtures::datatype();
    let expected = serde_json::to_vec(&bundle).unwrap();
    let (_, _, polls) = usage(&bundle);
    for refused in 1..=polls {
        let mut calls = 0;
        let result = bundle.try_clone_with_progress(&mut |_, _| {
            calls += 1;
            calls != refused
        });
        assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(calls, refused);
    }
    assert_eq!(serde_json::to_vec(&bundle).unwrap(), expected);
    let fresh = bundle.try_clone_with_progress(&mut |_, _| true).unwrap();
    assert_eq!(serde_json::to_vec(&fresh).unwrap(), expected);
    assert!(re_check_bundle_strict(&fresh)
        .unwrap()
        .quality
        .is_complete());
}

#[test]
fn raw_bundle_clone_obeys_exact_and_one_short_shared_allowances() {
    let bundle = fixtures::skolem();
    let (work, bytes, _) = usage(&bundle);
    for (w_cap, b_cap, admitted) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
    ] {
        let (mut w, mut b) = (0, 0);
        assert_eq!(
            bundle
                .try_clone_with_progress(&mut |dw, db| {
                    w += dw;
                    b += db;
                    w <= w_cap && b <= b_cap
                })
                .is_ok(),
            admitted
        );
    }
    let mut spent = 0;
    let mut progress = |_: usize, delta: usize| {
        spent += delta;
        spent <= bytes
    };
    assert!(bundle.try_clone_with_progress(&mut progress).is_ok());
    assert!(matches!(
        bundle.try_clone_with_progress(&mut progress),
        Err(ProofCheckError::ResourceLimit)
    ));
}

#[test]
fn raw_clone_and_independent_replay_debit_one_combined_allowance() {
    let source = fixtures::skolem();
    let (copy_work, copy_bytes, _) = usage(&source);
    let copied = source.try_clone_with_progress(&mut |_, _| true).unwrap();
    let (mut replay_work, mut replay_bytes) = (0, 0);
    re_check_bundle_strict_with_resource_control(&copied, &mut |w, b| {
        replay_work += w;
        replay_bytes += b;
        true
    })
    .unwrap();
    let work = copy_work + replay_work;
    let bytes = copy_bytes + replay_bytes;
    for (work_cap, bytes_cap, admitted) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
        (copy_work, copy_bytes, false),
    ] {
        let (mut w, mut b) = (0, 0);
        let mut progress = |dw, db| {
            w += dw;
            b += db;
            w <= work_cap && b <= bytes_cap
        };
        let copied = source.try_clone_with_progress(&mut progress).unwrap();
        let checked = re_check_bundle_strict_with_resource_control(&copied, &mut progress);
        assert_eq!(checked.is_ok(), admitted);
        if let Ok(checked) = checked {
            assert!(checked.quality.is_complete());
            assert_eq!((w, b), (work, bytes));
        }
    }
}

#[test]
fn raw_bundle_clone_prices_unused_payload_and_full_nested_typed_context() {
    let mut bundle = fixtures::contradiction(false);
    let (_, small, _) = usage(&bundle);
    let payload = "unused-string".repeat(8192);
    bundle.term_entries.push((
        TermData::Const(Constant::String(payload.clone())),
        Sort::String,
    ));
    let mut spent = 0;
    assert!(matches!(
        bundle.try_clone_with_progress(&mut |_, delta| {
            spent += delta;
            spent <= small
        }),
        Err(ProofCheckError::ResourceLimit)
    ));
    let (_, large, _) = usage(&bundle);
    assert!(large >= small + payload.len());
    bundle
        .datatype_member_signatures
        .push(DatatypeMemberSignature {
            identity: "extra-signature".to_owned(),
            argument_sorts: vec![Sort::Seq(Box::new(Sort::Uninterpreted(payload)))],
            result_sort: Sort::Bool,
            nullary_term: None,
        });
    let (_, typed, _) = usage(&bundle);
    assert!(typed > large);
    let copied = bundle.try_clone_with_progress(&mut |_, _| true).unwrap();
    assert_eq!(
        serde_json::to_vec(&copied).unwrap(),
        serde_json::to_vec(&bundle).unwrap()
    );
    assert!(
        re_check_bundle_strict(&copied).is_err(),
        "copying cannot authorize foreign declaration metadata"
    );
}
