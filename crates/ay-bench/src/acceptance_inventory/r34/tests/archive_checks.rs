// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn original_container_and_every_selected_member_match_independent_hashes() {
    let bundle = fixture();
    assert_eq!(bundle.files.len(), 18);
    for (name, identity) in &bundle.capture.files {
        let bytes = &bundle.files[name];
        assert_eq!(bytes.len() as u64, identity.bytes);
        assert_eq!(capture::digest(bytes), identity.sha256);
    }
    for (source, text) in [
        ("static", include_str!("../fixtures/static-source.smt2")),
        ("alloc", include_str!("../fixtures/alloc-source.smt2")),
        ("bitmask", include_str!("../fixtures/bitmask-source.smt2")),
    ] {
        let source = &bundle.capture.sources[source];
        assert_eq!(
            bundle
                .text(&format!("{}/source.smt2", source.base))
                .unwrap(),
            text
        );
    }
}

fn paths() -> (tempfile::TempDir, std::path::PathBuf, std::path::PathBuf) {
    let dir = tempfile::tempdir().unwrap();
    let inventory = dir.path().join("inventory.json");
    let archive = dir.path().join("archive.tar.gz");
    std::fs::write(
        &inventory,
        include_bytes!(
            "../../../../../../docs/integrations/model_checker_consumer_acceptance_manifest.json"
        ),
    )
    .unwrap();
    std::fs::write(&archive, archive_bytes()).unwrap();
    (dir, inventory, archive)
}

#[test]
fn public_loader_authenticates_raw_frozen_inventory_without_null_reserialization() {
    let (_dir, inventory, archive) = paths();
    let loaded = R34Archive::load(&inventory, &archive).unwrap();
    assert_eq!(loaded.files.len(), 18);
    assert_eq!(
        loaded.inventory_sha256,
        Inventory::load(&inventory).unwrap().sha256
    );
}

#[test]
fn same_length_changed_container_is_refused_before_unpacking() {
    let (_dir, inventory, archive) = paths();
    let mut bytes = archive_bytes();
    let end = bytes.len() - 1;
    bytes[end] ^= 1;
    std::fs::write(&archive, bytes).unwrap();
    assert!(R34Archive::load(&inventory, &archive).is_err());
}

#[test]
fn original_inventory_obligations_cannot_be_mutated_to_authorize_replay() {
    let (_dir, inventory, archive) = paths();
    let mut value: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&inventory).unwrap()).unwrap();
    value["request_inventory"][0]["title"] = "weakened claim".into();
    std::fs::write(&inventory, serde_json::to_vec(&value).unwrap()).unwrap();
    assert!(R34Archive::load(&inventory, &archive).is_err());
}

#[cfg(unix)]
#[test]
fn final_component_symlink_is_not_an_authenticated_archive_file() {
    let (dir, inventory, archive) = paths();
    let link = dir.path().join("link.tar.gz");
    std::os::unix::fs::symlink(&archive, &link).unwrap();
    assert!(R34Archive::load(&inventory, &link).is_err());
}

#[test]
fn captured_rows_and_witnesses_are_members_of_the_original_manifest() {
    let bundle = fixture();
    for row in &bundle.capture.rows {
        let source = &bundle.capture.sources[&row.source];
        let manifest: serde_json::Value = serde_json::from_str(
            bundle
                .text(&format!("{}/manifest.json", source.base))
                .unwrap(),
        )
        .unwrap();
        let all = manifest.to_string();
        // Exact object inclusion, not a substring/value-only identity check.
        assert!(
            contains_object(&manifest, &row.row),
            "{}: {}",
            row.label,
            all.len()
        );
    }
    for witness in &bundle.capture.witnesses {
        let source = &bundle.capture.sources[&witness.source];
        let manifest: serde_json::Value = serde_json::from_str(
            bundle
                .text(&format!("{}/manifest.json", source.base))
                .unwrap(),
        )
        .unwrap();
        assert!(contains_object(&manifest, &witness.record));
    }
}

fn contains_object(value: &serde_json::Value, needle: &serde_json::Value) -> bool {
    value == needle
        || match value {
            serde_json::Value::Array(values) => values.iter().any(|v| contains_object(v, needle)),
            serde_json::Value::Object(fields) => {
                fields.values().any(|v| contains_object(v, needle))
            }
            _ => false,
        }
}

#[test]
fn source_level_dispositions_are_never_guessed_from_unknown_or_smt_polarity() {
    let bundle = fixture();
    assert_eq!(bundle.original_dispositions().len(), 5);
    assert!(bundle
        .original_dispositions()
        .values()
        .any(|v| v.contains("uninitialized")));
    assert!(bundle
        .original_dispositions()
        .values()
        .any(|v| v.contains("OverApproximation")));
}
