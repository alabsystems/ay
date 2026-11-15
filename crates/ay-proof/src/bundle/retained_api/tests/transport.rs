// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn actual_v6_transport_never_downgrades_and_legacy_v5_reader_remains_compatible() {
    let snapshot = bv_snapshot();
    let legacy = crate::re_check_bundle_strict(&snapshot).unwrap();
    assert!(legacy.quality.is_complete());
    assert_eq!(snapshot.schema, crate::PROOF_BUNDLE_SCHEMA);
    let legacy_bytes = serde_json::to_vec(&snapshot).unwrap();
    let owner =
        capture_strict_retained_bundle_with_resource_control(snapshot, end(), &mut |_, _| true)
            .unwrap()
            .finish_exact_with_resource_control(&mut |_, _| true)
            .unwrap()
            .0;
    let bytes = owner
        .encode_with_resource_control(transport_limits(), end(), &mut |_, _| true)
        .unwrap();
    let doc: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(doc["schema"], RETAINED_PROOF_BUNDLE_SCHEMA);
    assert!(doc["retained"].is_array());
    assert!(serde_json::from_slice::<SerializableProofBundle>(&bytes).is_err());
    let before = producer_test_counter::count();
    assert!(read_retained_proof_bundle_with_resource_control(
        &legacy_bytes,
        transport_limits(),
        end(),
        &mut |_, _| true,
    )
    .is_err());
    assert_eq!(producer_test_counter::count(), before);
    let round_trip: SerializableProofBundle = serde_json::from_slice(&legacy_bytes).unwrap();
    assert_eq!(
        crate::re_check_bundle_strict(&round_trip)
            .unwrap()
            .assume_terms,
        legacy.assume_terms
    );
}

#[test]
fn offline_reader_rejects_missing_corrupt_extra_inventory_without_reproduction() {
    let owner = finished();
    let bytes = owner
        .encode_with_resource_control(transport_limits(), end(), &mut |_, _| true)
        .unwrap();
    let original: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    let before = producer_test_counter::count();
    for mode in 0..5 {
        let mut doc = original.clone();
        match mode {
            0 => {
                doc.as_object_mut().unwrap().remove("retained");
            }
            1 => doc["retained"] = serde_json::json!(null),
            2 => doc["retained"] = serde_json::json!([]),
            3 => {
                let duplicate = doc["retained"][0].clone();
                doc["retained"].as_array_mut().unwrap().push(duplicate);
            }
            _ => doc["schema"] = serde_json::json!(crate::PROOF_BUNDLE_SCHEMA),
        }
        let corrupt = serde_json::to_vec(&doc).unwrap();
        assert!(
            read_retained_proof_bundle_with_resource_control(
                &corrupt,
                transport_limits(),
                end(),
                &mut |_, _| true,
            )
            .is_err(),
            "mode {mode}"
        );
        assert_eq!(producer_test_counter::count(), before);
    }
}

#[test]
fn offline_exact_inventory_rejects_reordering_and_unused_or_duplicate_authorized_ids() {
    let (owner, _) = capture_strict_retained_bundle_with_resource_control(
        repeated_bool_snapshot(),
        end(),
        &mut |_, _| true,
    )
    .unwrap()
    .finish_exact_with_resource_control(&mut |_, _| true)
    .unwrap();
    let bytes = owner
        .encode_with_resource_control(transport_limits(), end(), &mut |_, _| true)
        .unwrap();
    let original: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    let before = producer_test_counter::count();
    for duplicate in [false, true] {
        let mut doc = original.clone();
        let ids = doc["obligation_assertions"].as_array_mut().unwrap();
        if duplicate {
            ids.push(ids[0].clone());
        } else {
            ids.reverse();
        }
        let corrupt = serde_json::to_vec(&doc).unwrap();
        assert!(read_retained_proof_bundle_with_resource_control(
            &corrupt,
            transport_limits(),
            end(),
            &mut |_, _| true,
        )
        .is_err());
    }
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn transport_ceilings_only_tighten_and_refusals_never_publish_partial_documents() {
    let owner = finished();
    let bytes = owner
        .encode_with_resource_control(transport_limits(), end(), &mut |_, _| true)
        .unwrap();
    let before = producer_test_counter::count();
    for mode in 0..3 {
        let mut limits = transport_limits();
        match mode {
            0 => limits.max_json_bytes = bytes.len() - 1,
            1 => limits.max_storage_bytes = 0,
            _ => limits.max_work = 0,
        }
        assert!(owner
            .encode_with_resource_control(limits, end(), &mut |_, _| true)
            .is_err());
        assert!(read_retained_proof_bundle_with_resource_control(
            &bytes,
            limits,
            end(),
            &mut |_, _| true,
        )
        .is_err());
    }
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn encoded_owner_and_report_only_reader_share_callback_credit_without_producer_fallback() {
    let owner = finished();
    let (mut work, mut bytes_used) = (0usize, 0usize);
    let mut count = |w, b| {
        work = work.checked_add(w).unwrap();
        bytes_used = bytes_used.checked_add(b).unwrap();
        true
    };
    let bytes = owner
        .encode_with_resource_control(transport_limits(), end(), &mut count)
        .unwrap();
    re_check_retained_bundle_strict_with_resource_control(
        &bytes,
        transport_limits(),
        end(),
        &mut count,
    )
    .unwrap();
    assert!(work > 0 && bytes_used > 0);
    let (mut used_work, mut used_bytes) = (0usize, 0usize);
    let mut budget = |w, b| {
        used_work = used_work.checked_add(w).unwrap();
        used_bytes = used_bytes.checked_add(b).unwrap();
        used_work <= work && used_bytes < bytes_used
    };
    let before = producer_test_counter::count();
    let same_bytes = owner
        .encode_with_resource_control(transport_limits(), end(), &mut budget)
        .unwrap();
    assert_eq!(same_bytes, bytes);
    assert!(matches!(
        re_check_retained_bundle_strict_with_resource_control(
            &same_bytes,
            transport_limits(),
            end(),
            &mut budget,
        ),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert_eq!(producer_test_counter::count(), before);
}
