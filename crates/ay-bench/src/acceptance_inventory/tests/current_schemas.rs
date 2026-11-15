// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeMap;
use std::fs;

use serde_json::{json, Value};

use super::super::{
    Inventory, INVENTORY_SCHEMA_V4, INVENTORY_SCHEMA_V5, INVENTORY_SCHEMA_V6, INVENTORY_SCHEMA_V7,
    INVENTORY_SCHEMA_V8,
};

const CURRENT: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../docs/integrations/model_checker_consumer_acceptance_manifest.json"
));

pub(super) fn current() -> Value {
    serde_json::from_str(CURRENT).expect("checked-in inventory JSON")
}

// Project only the reviewed additive cohorts. Production admission pins the
// independently computed full historical hash, not this test helper's output.
fn previous(mut value: Value, version: u32) -> Value {
    let (requests, routes, schema, groups) = match version {
        7 => (
            vec!["R36"],
            vec![
                "smt-cli-default-fp-model",
                "bmc-consumer-fp-original-counterexample",
            ],
            INVENTORY_SCHEMA_V7,
            42,
        ),
        6 => (
            vec!["R35"],
            vec![
                "smt-cli-default-posture-proof",
                "bmc-consumer-divider-proof",
            ],
            INVENTORY_SCHEMA_V6,
            41,
        ),
        5 => (
            vec!["R30", "R31", "R32", "R33", "R34"],
            vec![
                "chc-consumer-exact-acyclic-drain",
                "chc-consumer-exact-prepared-exports",
                "smt-consumer-exact-witness-exports",
            ],
            INVENTORY_SCHEMA_V5,
            36,
        ),
        4 => (
            vec!["R25", "R26", "R27", "R28", "R29"],
            vec![
                "chc-consumer-current-large-block",
                "chc-consumer-current-datatypes",
                "chc-consumer-current-per-row",
                "chc-api-current-pre-discharge-realloc",
            ],
            INVENTORY_SCHEMA_V4,
            31,
        ),
        _ => panic!("test projection supports only v4/v5/v6/v7"),
    };
    value["schema"] = json!(schema);
    for table in [
        "request_inventory",
        "routes",
        "stored_inputs",
        "consumer_units",
        "supplemental_source_inventories",
        "blockers",
    ] {
        value[table].as_array_mut().expect("table").retain(|row| {
            let id = row["id"].as_str().expect("ID");
            !requests.contains(&id)
                && !routes.contains(&id)
                && !row
                    .get("request_ids")
                    .and_then(Value::as_array)
                    .is_some_and(|ids| {
                        !ids.is_empty()
                            && ids
                                .iter()
                                .all(|id| requests.contains(&id.as_str().expect("request ID")))
                    })
        });
    }
    for row in value["blockers"].as_array_mut().expect("blockers") {
        if row["id"] == "B-runner-binding" || row["id"] == "B-qualification" {
            row["request_ids"]
                .as_array_mut()
                .expect("IDs")
                .retain(|id| !requests.contains(&id.as_str().expect("ID")));
        }
    }
    let checks = value["inventory_checks"].as_object_mut().expect("checks");
    checks.insert("expected_request_group_count".to_owned(), json!(groups));
    checks
        .get_mut("required_request_groups")
        .expect("groups")
        .as_array_mut()
        .expect("group array")
        .retain(|id| !requests.contains(&id.as_str().expect("ID")));
    checks.remove(&format!("schema_v{}_roster", version + 1));
    value
}

#[test]
fn real_v4_through_v8_documents_preserve_all_contracts_and_remain_unqualified() {
    let v8 = current();
    let v7 = previous(v8.clone(), 7);
    let v6 = previous(v7.clone(), 6);
    let v5 = previous(v6.clone(), 5);
    let v4 = previous(v5.clone(), 4);
    let mut prior: Option<super::super::InventoryDocument> = None;
    for (value, contracts, groups, inputs) in [
        (v4, 34, 31, 36),
        (v5, 39, 36, 45),
        (v6, 44, 41, 71),
        (v7, 45, 42, 78),
        (v8, 46, 43, 81),
    ] {
        let inventory = Inventory::parse(&value.to_string()).expect("frozen source contract");
        let plan = inventory.plan();
        assert_eq!(plan.requests.len(), contracts);
        assert_eq!(plan.document.stored_inputs.len(), inputs);
        assert_eq!(
            plan.document.metadata["inventory_checks"]["expected_request_group_count"],
            groups
        );
        assert!(!plan.promotable_for_ask_closure);
        assert!(plan.requests.iter().all(|r| !r.blockers.is_empty()));
        assert!(plan
            .requests
            .iter()
            .flat_map(|r| &r.routes)
            .all(|r| !r.evidence_qualified));
        if let Some(prior) = prior {
            assert_eq!(
                &plan.document.request_inventory[..prior.request_inventory.len()],
                &prior.request_inventory
            );
            assert_eq!(
                &plan.document.stored_inputs[..prior.stored_inputs.len()],
                &prior.stored_inputs
            );
            assert_eq!(plan.document.case_defaults, prior.case_defaults);
            assert_eq!(
                plan.document.performance_contracts,
                prior.performance_contracts
            );
        }
        prior = Some(plan.document);
    }
}

#[test]
fn frozen_identity_binds_historical_and_current_source_contract_fields() {
    let mutations = [
        ("/snapshots/model-checker-consumer", json!("retagged")),
        ("/request_inventory/0/required_checks", json!(["weakened"])),
        ("/stored_inputs/0/sha256", json!("0".repeat(64))),
        ("/inventory_checks/solver_or_checker_runs", json!(1)),
        (
            "/inventory_checks/schema_v6_roster/current_source_revision",
            json!("0".repeat(40)),
        ),
        ("/qualification", json!("accepted")),
        (
            "/case_defaults/tracked_solver_input_bytes_must_be_preserved",
            json!(false),
        ),
    ];
    for (pointer, replacement) in mutations {
        let mut value = current();
        if let Some(target) = value.pointer_mut(pointer) {
            *target = replacement;
        } else {
            // snapshots use repository-specific keys; an added fake receipt is
            // also a forbidden change to the frozen historical contract.
            value["snapshots"]["model-checker-consumer"] = replacement;
        }
        assert!(Inventory::parse(&value.to_string()).is_err(), "{pointer}");
    }
    for id in ["R24", "R25", "R29", "R30", "R34", "R35", "R36"] {
        let mut value = current();
        value["request_inventory"]
            .as_array_mut()
            .expect("requests")
            .retain(|r| r["id"] != id);
        assert!(
            Inventory::parse(&value.to_string()).is_err(),
            "missing {id}"
        );
    }
}

#[test]
fn whitespace_and_key_order_preserve_contract_but_not_raw_file_identity() {
    let value = current();
    let reversed = value
        .as_object()
        .expect("object")
        .iter()
        .rev()
        .map(|(key, value)| format!("{}:{value}", json!(key)))
        .collect::<Vec<_>>()
        .join(",");
    let reordered = Inventory::parse(&format!("{{{reversed}}}")).expect("canonical object order");
    let original = Inventory::parse(CURRENT).expect("current bytes");
    assert_eq!(original.document, reordered.document);
    assert_ne!(original.sha256, reordered.sha256);
}

#[test]
fn fp_logic_counterexample_and_pending_acceptance_contract_cannot_be_weakened() {
    for (table, id, key, replacement) in [
        (
            "stored_inputs",
            "input:fp-logic-test6-all",
            "smt_logic",
            json!("QF_AUFBV"),
        ),
        (
            "stored_inputs",
            "input:fp-logic-test6-all",
            "expected_semantic_result",
            json!("Unknown"),
        ),
        (
            "stored_inputs",
            "input:fp-logic-test6-source",
            "kind",
            json!("smt2"),
        ),
        (
            "request_inventory",
            "R36",
            "consumer_harness_budget_ms",
            json!(120_000),
        ),
        (
            "request_inventory",
            "R36",
            "harness_or_solve_budget_ms",
            json!(15_000),
        ),
        ("request_inventory", "R36", "status", json!("accepted")),
        (
            "consumer_units",
            "r36-fp-test6:main",
            "expected_run_verdict",
            json!("SUCCESSFUL"),
        ),
        (
            "consumer_units",
            "r36-fp-test6:main",
            "validated_original_counterexample_required",
            json!(false),
        ),
        (
            "consumer_units",
            "r36-fp-test6:main",
            "independent_source_replay_required",
            json!(false),
        ),
        (
            "routes",
            "bmc-consumer-fp-original-counterexample",
            "standalone_cli_equivalent",
            json!(true),
        ),
    ] {
        let mut value = current();
        let row = value[table]
            .as_array_mut()
            .expect("table")
            .iter_mut()
            .find(|row| row["id"] == id)
            .expect("FP source contract");
        row[key] = replacement;
        assert!(Inventory::parse(&value.to_string()).is_err(), "{id}: {key}");
    }
}

#[test]
fn current_archive_oracle_budget_and_no_solve_identities_cannot_be_retagged() {
    for (id, key, replacement) in [
        (
            "input:acyclic-drain-ref-index",
            "archive_sha256",
            json!("0".repeat(64)),
        ),
        (
            "input:acyclic-drain-ref-index",
            "archive_member",
            json!("another/source.smt2"),
        ),
        (
            "input:export-static-constructor-witness",
            "expected_semantic_result",
            json!("unsat"),
        ),
        ("input:export-test2-error-p1", "kind", json!("horn-query")),
        (
            "input:export-bitmask-u8-source",
            "kind",
            json!("horn-query"),
        ),
        (
            "input:realloc-grow-pre-discharge",
            "sha256",
            json!("1".repeat(64)),
        ),
    ] {
        let mut value = current();
        let input = value["stored_inputs"]
            .as_array_mut()
            .expect("inputs")
            .iter_mut()
            .find(|input| input["id"] == id)
            .expect("current input");
        input[key] = replacement;
        assert!(Inventory::parse(&value.to_string()).is_err(), "{id}: {key}");
    }
    for (id, key, replacement) in [
        ("R29", "harness_or_solve_budget_ms", json!(120_000)),
        ("R31", "strict_smt_control_budget_ms", json!(120_000)),
        ("R34", "exact_row_contracts", json!([])),
        ("R30", "missing_original_inputs", json!([])),
    ] {
        let mut value = current();
        let request = value["request_inventory"]
            .as_array_mut()
            .expect("requests")
            .iter_mut()
            .find(|request| request["id"] == id)
            .expect("current request");
        request[key] = replacement;
        assert!(Inventory::parse(&value.to_string()).is_err(), "{id}: {key}");
    }
}

#[test]
fn duplicate_keys_are_rejected_before_identity_or_flattened_metadata_admission() {
    let text = current().to_string();
    let duplicated = format!(
        "{{\"sch\\u0065ma\":{},{}",
        json!(INVENTORY_SCHEMA_V8),
        &text[1..]
    );
    let error = Inventory::parse(&duplicated).expect_err("escaped duplicate schema");
    assert!(error.to_string().contains("duplicate inventory JSON key"));
    let duplicated = text.replacen(
        "\"request_count\":44",
        "\"request_count\":0,\"request_count\":44",
        1,
    );
    assert_ne!(duplicated, text);
    assert!(Inventory::parse(&duplicated)
        .expect_err("nested metadata duplicate")
        .to_string()
        .contains("duplicate inventory JSON key"));
}

#[test]
fn newer_rosters_cannot_be_relabelled_or_accepted_as_future_schema() {
    for schema in [
        super::super::INVENTORY_SCHEMA_V3,
        INVENTORY_SCHEMA_V4,
        INVENTORY_SCHEMA_V5,
        INVENTORY_SCHEMA_V6,
        INVENTORY_SCHEMA_V7,
        "ay.model-checker-consumer-acceptance-inventory/v9",
    ] {
        let mut value = current();
        value["schema"] = json!(schema);
        assert!(Inventory::parse(&value.to_string()).is_err());
    }
}

#[test]
fn real_current_direct_query_retains_exact_identity_and_original_twenty_second_budget() {
    let inventory = Inventory::parse(CURRENT).expect("v6");
    let input = inventory
        .document
        .stored_inputs
        .iter()
        .find(|input| input.id == "input:realloc-grow-pre-discharge")
        .expect("original query");
    let root = tempfile::tempdir().expect("private test root");
    let path = root.path().join(&input.path);
    fs::create_dir_all(path.parent().expect("parent")).expect("test directories");
    // Planning checks regular-file size only. The real runner must hash its
    // streamed private snapshot before execution; these zero bytes are no proof.
    fs::File::create(&path)
        .expect("placeholder")
        .set_len(input.size_bytes.expect("size"))
        .expect("length");
    let roots = BTreeMap::from([("model-checker-consumer".to_owned(), root.path().to_owned())]);
    let cases = inventory
        .chc_diagnostic_cases(&roots, &[input.id.clone()])
        .expect("diagnostic plan");
    assert_eq!(cases.len(), 1);
    assert_eq!(cases[0].timeout_ms, 20_000);
    assert_eq!(
        cases[0].expected_sha256,
        "sha256:0930146db6fc0c3e308d87dff805d02e20c4959e3b40c7a3c455e1ab636412d7"
    );
    assert_eq!(
        cases[0].original_revision,
        input.revision.as_deref().expect("source revision")
    );
    assert!(!cases[0].promotable_for_ask_closure);
}
