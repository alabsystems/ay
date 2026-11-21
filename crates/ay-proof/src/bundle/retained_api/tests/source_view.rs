// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::TermData;

#[test]
fn retained_source_view_reads_exact_typed_data_after_replay_without_new_evidence() {
    let owner = finished();
    let before = producer_test_counter::count();
    owner
        .with_checked_source_view_with_resource_control(
            end(),
            &mut |_, _| true,
            |view, checked, progress| {
                assert!(checked.quality.is_complete());
                assert_eq!(view.obligations(), owner.obligation_assertions());
                assert!(view.term_count() > view.obligations().len());
                for &root in view.obligations() {
                    assert!(progress(1, 0));
                    let (data, sort) = view.term(root).expect("checked positional root");
                    assert_eq!(sort, &Sort::Bool);
                    assert!(view.term_matches_with_resource_control(
                        root,
                        (data, sort),
                        progress
                    )?);
                }
                assert!(view.datatype_declarations().is_empty());
                assert!(view.constructor_selectors().is_empty());
                assert!(view.datatype_member_signatures().is_empty());
                assert!(view.term(TermId(u32::MAX)).is_none());
                Ok(())
            },
        )
        .unwrap();
    assert_eq!(producer_test_counter::count(), before);
    let wire = owner
        .encode_with_resource_control(transport_limits(), end(), &mut |_, _| true)
        .unwrap();
    let (_, checked) = read_retained_proof_bundle_with_resource_control(
        &wire,
        transport_limits(),
        end(),
        &mut |_, _| true,
    )
    .unwrap();
    assert!(
        checked.quality.is_complete(),
        "source inspection preserves mandatory retained payloads"
    );
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn retained_source_entry_comparison_prices_borrowed_payload_before_equality() {
    let owner = finished();
    let large = TermData::Var("large_expected_source".repeat(65_536), 0);
    let result = owner.with_checked_source_view_with_resource_control(
        end(),
        &mut |_, _| true,
        |view, _, progress| {
            let root = view.obligations()[0];
            let mut limit = |work, bytes| work < 1_024 && progress(work, bytes);
            let compared =
                view.term_matches_with_resource_control(root, (&large, &Sort::Bool), &mut limit);
            assert!(matches!(compared, Err(ProofCheckError::ResourceLimit)));
            Ok(())
        },
    );
    assert!(
        result.is_ok(),
        "independent local comparison refusal does not mint a match"
    );
}

#[test]
fn retained_source_view_preserves_previsitor_and_visitor_refusal() {
    let owner = finished();
    let mut visited = false;
    let rejected = owner.with_checked_source_view_with_resource_control(
        end(),
        &mut |_, _| false,
        |_, _, _| {
            visited = true;
            Ok(())
        },
    );
    assert!(matches!(rejected, Err(ProofCheckError::ResourceLimit)));
    assert!(!visited);
    let rejected = owner.with_checked_source_view_with_resource_control(
        end(),
        &mut |work, _| work != usize::MAX,
        |_, _, progress| {
            assert!(!progress(usize::MAX, 0));
            Ok(())
        },
    );
    assert!(
        matches!(rejected, Err(ProofCheckError::ResourceLimit)),
        "ignoring a visitor callback refusal cannot revive the owner"
    );
}
