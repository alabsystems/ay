// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use serde_json::{json, Value};

use super::super::{BlockerKind, Inventory, PlanBlocker, INVENTORY_SCHEMA, INVENTORY_SCHEMA_V2};

pub(super) fn document() -> Value {
    let mut value = super::document();
    value["schema"] = json!(INVENTORY_SCHEMA_V2);
    for suffix in ['a', 'b', 'c', 'd'] {
        value["request_inventory"]
            .as_array_mut()
            .expect("request array")
            .push(json!({
                "id":format!("R22{suffix}"), "title":"current array request",
                "source_requests":["the development design notes"],
                "required_routes":["chc-consumer-native-typed-pdr"],
                "harness_or_solve_budget_ms":null,
                "required_checks":["original query and private consumer evidence"],
                "stored_input_ids":[]
            }));
    }
    value["routes"]
        .as_array_mut()
        .expect("route array")
        .push(json!({"id":"chc-consumer-native-typed-pdr"}));
    value["performance_contracts"]["algorithmic_scaling_contracts"] = json!([{
        "id":"flat-array-nonquadratic-work", "request_ids":["R22d"],
        "sizes":[1024,16384,131072],
        "required_algorithmic_bound":{"allowed_growth":["O(n)","O(n log n)"]},
        "numeric_user_deadline":null,
        "status":"current operation-count and matched scaling evidence missing"
    }]);
    value["stored_inputs"]
        .as_array_mut()
        .expect("input array")
        .push(json!({
            "id":"input:current-flat-export", "repository":"model-checker-consumer",
            "revision":"1".repeat(40), "path":"producer.rs",
            "kind":"unexported-typed-expression", "request_ids":["R22d"],
            "expected_semantic_result":"oracle-bound-at-consumer",
            "availability":"missing-current-export",
            "path_is_source_recipe_not_solver_input":true,
            "source_recipe":{"parameters":{"array_length":131072}},
            "historical_input_bytes_authenticated":false
        }));
    // Original order is R01-R21,U1-U7, then R22a-R22d.
    value["request_inventory"][31]["stored_input_ids"] = json!(["input:current-flat-export"]);
    value["blockers"]
        .as_array_mut()
        .expect("blocker array")
        .push(json!({
            "id":"current-array-evidence", "request_ids":["R22a","R22b","R22c","R22d"],
            "reason":"Internal current export and same-cohort evidence required."
        }));
    value
}

fn parse(value: &Value) -> crate::Result<Inventory> {
    Inventory::parse(&value.to_string())
}

#[test]
fn historical_v1_keeps_its_exact_28_request_roster() {
    let value = super::document();
    assert_eq!(value["schema"], INVENTORY_SCHEMA);
    assert_eq!(
        parse(&value).expect("historical v1").plan().requests.len(),
        28
    );
    let mut expanded = document();
    expanded["schema"] = json!(INVENTORY_SCHEMA);
    assert!(parse(&expanded).is_err(), "v1 must not silently expand");
}

#[test]
fn v2_admits_exact_32_requests_without_promoting_evidence() {
    let inventory = parse(&document()).expect("v2 fixture");
    let plan = inventory.plan();
    assert_eq!(plan.requests.len(), 32);
    assert!(!plan.promotable_for_ask_closure);
    for request in &plan.requests {
        assert_ne!(request.blockers.as_slice(), &[] as &[PlanBlocker]);
        assert!(request.routes.iter().all(|route| !route.evidence_qualified));
    }
}

#[test]
fn v2_refuses_missing_original_and_new_requests() {
    for id in ["R01", "R21", "U1", "U7", "R22a", "R22d"] {
        let mut value = document();
        value["request_inventory"]
            .as_array_mut()
            .expect("request array")
            .retain(|row| row["id"] != id);
        assert!(parse(&value).is_err(), "missing {id} must refuse");
    }
}

#[test]
fn v2_refuses_duplicate_and_unknown_request_ids() {
    let mut duplicate = document();
    let row = duplicate["request_inventory"][28].clone();
    duplicate["request_inventory"]
        .as_array_mut()
        .expect("request array")
        .push(row);
    assert!(parse(&duplicate).is_err());
    for id in ["R22", "R23", "R26", "U8", "R00"] {
        let mut value = document();
        value["request_inventory"][28]["id"] = json!(id);
        assert!(parse(&value).is_err(), "unknown {id} must refuse");
    }
}

#[test]
fn v2_refuses_unrecognized_schema_or_old_roster() {
    let mut value = document();
    value["schema"] = json!("ay.model-checker-consumer-acceptance-inventory/v9");
    assert!(parse(&value).is_err());
    let mut old = super::document();
    old["schema"] = json!(INVENTORY_SCHEMA_V2);
    assert!(parse(&old).is_err(), "v2 requires all four additions");
}

#[test]
fn v2_preserves_original_contracts_and_algorithmic_scaling_metadata() {
    let original = parse(&super::document()).expect("v1 fixture");
    let value = document();
    let inventory = parse(&value).expect("v2 fixture");
    let plan = inventory.plan();
    assert_eq!(
        &plan.document.request_inventory[..28],
        original.document.request_inventory.as_slice()
    );
    assert_eq!(
        plan.document.performance_contracts.targets,
        original.document.performance_contracts.targets
    );
    assert_eq!(plan.document.case_defaults, original.document.case_defaults);
    assert_eq!(
        serde_json::to_value(&plan.document.performance_contracts)
            .expect("performance serialization"),
        value["performance_contracts"]
    );
}

#[test]
fn missing_current_export_keeps_identity_oracle_route_and_budget_blockers() {
    let plan = parse(&document()).expect("v2 fixture").plan();
    let request = plan
        .requests
        .iter()
        .find(|request| request.contract.id == "R22d")
        .expect("new request retained");
    for kind in [
        BlockerKind::InputIdentityMissing,
        BlockerKind::OracleUnresolved,
        BlockerKind::RouteEvidenceMissing,
        BlockerKind::PreparedConsumerExportMissing,
        BlockerKind::BudgetBindingMissing,
        BlockerKind::DeclaredInventoryBlocker,
    ] {
        assert!(request.blockers.iter().any(|blocker| blocker.kind == kind));
    }
    assert!(
        parse(&document())
            .expect("v2 fixture")
            .chc_diagnostic_cases(
                &std::collections::BTreeMap::new(),
                &["input:current-flat-export".to_owned()]
            )
            .is_err(),
        "a source recipe is not a stored HORN input"
    );
}

#[test]
fn v2_new_references_are_validated_instead_of_skipped() {
    let mut missing_route = document();
    missing_route["request_inventory"][28]["required_routes"] = json!(["undefined-native-route"]);
    assert!(parse(&missing_route).is_err());
    let mut broken_reverse_binding = document();
    let last = broken_reverse_binding["stored_inputs"]
        .as_array()
        .expect("input array")
        .len()
        - 1;
    broken_reverse_binding["stored_inputs"][last]["request_ids"] = json!(["R22c"]);
    assert!(parse(&broken_reverse_binding).is_err());
}
