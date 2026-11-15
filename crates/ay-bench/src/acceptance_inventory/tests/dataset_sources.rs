// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use serde_json::{json, Value};

use super::super::{DatasetReference, DatasetSource, Inventory, InventoryDocument};

#[test]
fn all_actual_dataset_sources_roundtrip_without_inventing_paths_or_hashes() {
    let current = super::current_schemas::current();
    let sources = current["datasets"].as_array().expect("real datasets");
    assert_eq!(sources.len(), 11);
    let mut files = 0;
    let mut cohorts = 0;
    for original in sources {
        let dataset: DatasetReference = serde_json::from_value(original.clone())
            .unwrap_or_else(|error| panic!("dataset {}: {error}", original["id"]));
        assert_eq!(
            serde_json::to_value(&dataset).expect("serialize source"),
            *original
        );
        match &dataset.source {
            DatasetSource::File { path, sha256 } => {
                files += 1;
                assert_eq!(original["path"], *path);
                assert_eq!(original["sha256"], *sha256);
            }
            DatasetSource::SourceRows { rows } => {
                cohorts += 1;
                assert_eq!(dataset.id, "bmc-oct02-budget-edge-11");
                assert_eq!(rows.len(), 11);
                assert!(original.get("path").is_none());
                assert!(original.get("sha256").is_none());
                assert_eq!(rows[4].path, rows[5].path);
                assert_ne!(rows[4].details["harness"], rows[5].details["harness"]);
            }
        }
    }
    assert_eq!((files, cohorts), (10, 1));
}

#[test]
fn complete_actual_document_deserializes_and_preserves_every_original_field() {
    let original = super::current_schemas::current();
    let document: InventoryDocument = serde_json::from_value(original.clone())
        .expect("every actual nested source record must deserialize");
    let serialized = serde_json::to_value(document).expect("serialize complete document");
    assert_original_fields(&original, &serialized, "manifest");
    let plan = Inventory::parse(&original.to_string())
        .expect("current inventory")
        .plan();
    let request = plan
        .requests
        .iter()
        .find(|r| r.contract.id == "R24")
        .expect("budget request");
    assert!(request
        .dataset_ids
        .contains(&"bmc-oct02-budget-edge-11".to_owned()));
    assert!(!plan.promotable_for_ask_closure);
}

fn assert_original_fields(original: &Value, serialized: &Value, path: &str) {
    match original {
        Value::Object(fields) => {
            let actual = serialized.as_object().expect("object preserved");
            for (name, value) in fields {
                let next = format!("{path}.{name}");
                assert_original_fields(
                    value,
                    actual.get(name).unwrap_or_else(|| panic!("missing {next}")),
                    &next,
                );
            }
        }
        Value::Array(values) => {
            let actual = serialized.as_array().expect("array preserved");
            assert_eq!(values.len(), actual.len(), "{path}");
            for (index, (value, actual)) in values.iter().zip(actual).enumerate() {
                assert_original_fields(value, actual, &format!("{path}[{index}]"));
            }
        }
        _ => assert_eq!(original, serialized, "{path}"),
    }
}

fn row() -> Value {
    json!({"path":"tests/source.rs", "sha256":"1".repeat(64), "size_bytes":42,
        "harness":"original_harness", "fullmode":33204, "definition_line":9})
}

fn fixture(source: Value) -> Value {
    let mut value = super::document();
    value["datasets"][0] = source;
    value["datasets"][0]["id"] = json!("historical-bmc");
    value["datasets"][0]["repository"] = json!("model-checker-consumer");
    value
}

#[test]
fn dataset_source_forms_are_exclusive_required_and_not_defaulted() {
    for source in [
        json!({"path":"tests/source.rs", "sha256":"1".repeat(64)}),
        json!({"rows":[row()]}),
    ] {
        Inventory::parse(&fixture(source).to_string()).expect("exact source form");
    }
    for source in [
        json!({}),
        json!({"path":"tests/source.rs"}),
        json!({"sha256":"1".repeat(64)}),
        json!({"path":null, "sha256":null}),
        json!({"rows":null}),
        json!({"path":"tests/source.rs", "sha256":"1".repeat(64), "rows":[row()]}),
        json!({"path":null, "rows":[row()]}),
        json!({"sha256":null, "rows":[row()]}),
    ] {
        assert!(
            Inventory::parse(&fixture(source.clone()).to_string()).is_err(),
            "{source}"
        );
    }
}

#[test]
fn each_source_row_requires_a_valid_bound_identity_and_nonempty_cohort() {
    assert!(Inventory::parse(&fixture(json!({"rows":[]})).to_string()).is_err());
    for (field, invalid) in [
        ("path", json!("../outside.rs")),
        ("path", json!("/outside.rs")),
        ("sha256", json!("incomplete")),
        ("size_bytes", json!(0)),
        ("size_bytes", json!("42")),
    ] {
        let mut source = row();
        source[field] = invalid;
        assert!(
            Inventory::parse(&fixture(json!({"rows":[source]})).to_string()).is_err(),
            "{field}"
        );
    }
    for field in ["path", "sha256", "size_bytes"] {
        let mut source = row();
        source.as_object_mut().expect("source").remove(field);
        assert!(
            Inventory::parse(&fixture(json!({"rows":[source]})).to_string()).is_err(),
            "missing {field}"
        );
    }
}
