// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeMap;
use std::fs;

use serde_json::{json, Value};
use sha2::{Digest as _, Sha256};

use super::{BlockerKind, CliStatus, InputDialect, Inventory, SemanticExpectation};

pub(crate) fn document() -> Value {
    let revision = "0".repeat(40);
    let digest = "0".repeat(64);
    let mut value = json!({
        "schema": super::INVENTORY_SCHEMA,
        "captured_date": "2026-09-27",
        "qualification": "test fixture only; no execution evidence",
        "snapshots": {},
        "resource_policies": [{"id":"serial-enforced-tree-4g","jobs":1,"child_tree_peak_bytes_max":4294967296_u64}, {"id":"store-historical-2g"}, {"id":"store-machine-default"}],
        "routes": [{"id":"chc-consumer-adaptive"}, {"id":"chc-cli-original"}, {"id":"smt-api"}, {"id":"smt-cli"}],
        "request_inventory": [],
        "stored_inputs": [],
        "consumer_units": [{"id":"expected/test2/main.rs", "repository":"kani", "request_ids":["R20"], "source_files":[{"path":"tests/expected/test2/main.rs", "sha256":digest}]}],
        "datasets": [{"id":"historical-bmc", "repository":"external-measurement", "path":"/external/results-bmc.jsonl", "sha256":digest}],
        "integration_controls": [],
        "blockers": [{"id":"prepared-export", "request_ids":["R20","R21"], "reason":"Prepared property exports unavailable."}],
        "case_defaults": {
            "resource_policy":"serial-enforced-tree-4g", "request_status":"unqualified inventory",
            "consumer_selection":"match request IDs", "stored_model_checker_consumer_input_revision":revision,
            "whole_horn_export_equivalence":"not equivalent to prepared property input",
            "tracked_solver_input_bytes_must_be_preserved":true, "prepared_consumer_exports":"missing"
        },
        "source_authority_defaults": {
            "consumer_units_repository_revision":revision,
            "request_and_dataset_repository":"model-checker-consumer", "request_and_dataset_revision":revision
        },
        "performance_contracts": {
            "authority":"test frozen engineering targets",
            "measurement": {
                "minimum_alternating_pairs":3, "pair_order":"baseline,candidate repeated",
                "match_fields":["input SHA256","route","proof policy","resource envelope"],
                "record_fields":["wall time","tree peak","checker results"],
                "timeout_treatment":"censored failure", "missing_reference_treatment":"remains open",
                "historical_binary_authority":"timing reference only"
            },
            "targets":[
                {"id":"range-certified-cost", "request_ids":["R13"], "stored_input_ids":["input:range-len"], "required_routes":["smt-api","smt-cli"], "candidate_policy":"certified", "comparison_policy":"decision-only timing control", "median_limit":{"operation":"max", "absolute_ms":1000,"decision_only_median_multiplier":5}, "every_candidate_run_deadline_ms":10000},
                {"id":"plain-exact-expansion-cost", "request_ids":["R16"], "stored_input_ids":["input:expansion-test2"], "required_routes":["chc-cli-original"], "candidate_policy":"plain timing", "comparison_policy":"healthy same-route timing", "median_limit":{"healthy_reference_median_multiplier":2}, "every_candidate_run_deadline_ms":15000, "strict_evidence_deadline_ms":15000}
            ]
        },
        "unresolved_bindings": []
    });
    value["request_inventory"] = Value::Array(
        (1..=21)
            .map(|number| format!("R{number:02}"))
            .chain((1..=7).map(|number| format!("U{number}")))
            .map(|id| {
                json!({
                    "id":id, "title":"fixture request", "source_requests":["the development design notes"],
                    "required_routes":["chc-consumer-adaptive"], "harness_or_solve_budget_ms":15000,
                    "required_checks":["original evidence required"], "stored_input_ids":[]
                })
            })
            .collect(),
    );
    populate_stored_inputs(&mut value, &digest);
    value
}

fn populate_stored_inputs(value: &mut Value, digest: &str) {
    for (id, kind, expected, requests) in [
        (
            "input:store-source",
            "rust-source",
            "SUCCESSFUL",
            vec!["R01"],
        ),
        ("input:range-len", "smt2", "unsat", vec!["R13", "R14"]),
        ("input:store-full-historical", "smt2", "unsat", vec!["R01"]),
        (
            "input:budget-test3",
            "horn-query",
            "oracle-bound-at-consumer",
            vec!["R02"],
        ),
        (
            "input:budget-bitreverse",
            "horn-query",
            "Safe",
            vec!["R03", "R04", "R11"],
        ),
        (
            "input:expansion-test2",
            "horn-query",
            "Safe",
            vec!["R16", "R17", "R18", "R19"],
        ),
    ] {
        let mut input = json!({"id":id,"repository":"model-checker-consumer","path":"case.smt2","sha256":digest,
            "size_bytes":4,"kind":kind,"request_ids":requests,"expected_semantic_result":expected,"availability":"tracked"});
        if id == "input:store-full-historical" {
            input["availability"] = json!("not committed");
            input
                .as_object_mut()
                .expect("input object")
                .remove("sha256");
            input
                .as_object_mut()
                .expect("input object")
                .remove("size_bytes");
        }
        value["stored_inputs"]
            .as_array_mut()
            .expect("input array")
            .push(input);
        for request in value["request_inventory"]
            .as_array_mut()
            .expect("request array")
        {
            if requests.iter().any(|id| request["id"] == *id) {
                request["stored_input_ids"]
                    .as_array_mut()
                    .expect("input IDs")
                    .push(json!(id));
            }
            if request["id"] == "R01" {
                request["resource_policy"] = json!([
                    "store-historical-2g",
                    "store-machine-default",
                    "serial-enforced-tree-4g"
                ]);
            }
            if request["id"] == "U6" {
                request["source_inventory_dataset"] = json!("historical-bmc");
            }
        }
    }
}

fn inventory(value: &Value) -> Inventory {
    Inventory::parse(&value.to_string()).expect("test inventory passes structural admission")
}

#[test]
fn complete_plan_preserves_every_contract_and_remains_unqualified() {
    let text = document().to_string();
    let inventory = Inventory::parse(&text).expect("all-28 fixture is valid");
    assert_eq!(
        inventory.sha256,
        format!("sha256:{:x}", Sha256::digest(text.as_bytes()))
    );
    let plan = inventory.plan();
    assert_eq!(plan.requests.len(), 28);
    assert!(!plan.promotable_for_ask_closure);
    assert_eq!(plan.document, inventory.document);
    assert!(plan
        .requests
        .iter()
        .all(|request| !request.blockers.is_empty()));
    assert!(plan
        .requests
        .iter()
        .flat_map(|request| &request.routes)
        .all(|route| !route.evidence_qualified));
    let store = plan
        .requests
        .iter()
        .find(|request| request.contract.id == "R01")
        .expect("R01 exists");
    assert!(store
        .resource_policy_ids
        .contains(&"store-historical-2g".to_owned()));
    assert!(store
        .resource_policy_ids
        .contains(&"store-machine-default".to_owned()));
    let test2 = plan
        .requests
        .iter()
        .find(|request| request.contract.id == "R20")
        .expect("R20 exists");
    assert!(test2
        .blockers
        .iter()
        .any(|blocker| blocker.kind == BlockerKind::PreparedConsumerExportMissing));
    let expansion = plan
        .requests
        .iter()
        .find(|request| request.contract.id == "R16")
        .expect("R16 exists");
    assert_eq!(
        expansion.performance_contract_ids,
        ["plain-exact-expansion-cost"]
    );
}

#[test]
fn absent_or_duplicate_request_is_refused_instead_of_skipped() {
    let mut value = document();
    value["request_inventory"]
        .as_array_mut()
        .expect("request array")
        .pop();
    assert!(Inventory::parse(&value.to_string()).is_err());
    let mut value = document();
    value["request_inventory"][1]["id"] = Value::String("R01".to_owned());
    assert!(Inventory::parse(&value.to_string()).is_err());
}

#[test]
fn undefined_route_and_weakened_input_default_are_refused() {
    let mut value = document();
    value["request_inventory"][0]["required_routes"][0] =
        Value::String("imaginary-route".to_owned());
    assert!(Inventory::parse(&value.to_string()).is_err());
    let mut value = document();
    value["case_defaults"]["tracked_solver_input_bytes_must_be_preserved"] = Value::Bool(false);
    assert!(Inventory::parse(&value.to_string()).is_err());
}

#[test]
fn frozen_performance_fields_survive_complete_plan() {
    let mut value = document();
    value["performance_contracts"]["targets"][0]["comparison_policy_exception"] =
        json!("proof policy differs deliberately; all other fields match");
    let inventory = inventory(&value);
    let plan = inventory.plan();
    assert_eq!(
        serde_json::to_value(&plan.document.performance_contracts)
            .expect("performance serialization"),
        value["performance_contracts"]
    );
    value["performance_contracts"]["targets"] = json!([]);
    assert!(Inventory::parse(&value.to_string()).is_err());
}

#[test]
fn polarity_is_explicit_and_smt_does_not_infer_safety() {
    assert_eq!(
        InputDialect::HornQuery.cli_status(SemanticExpectation::Safe),
        Some(CliStatus::Unsat)
    );
    assert_eq!(
        InputDialect::HornQuery.cli_status(SemanticExpectation::Unsafe),
        Some(CliStatus::Sat)
    );
    assert_eq!(
        InputDialect::ChcComp.cli_status(SemanticExpectation::Safe),
        Some(CliStatus::Sat)
    );
    assert_eq!(
        InputDialect::ChcComp.chc_semantics(CliStatus::Unsat),
        Some(SemanticExpectation::Unsafe)
    );
    assert_eq!(
        InputDialect::HornQuery.chc_semantics(CliStatus::Unsat),
        Some(SemanticExpectation::Safe)
    );
    assert_eq!(
        InputDialect::Smt2.cli_status(SemanticExpectation::Safe),
        None
    );
    assert_eq!(
        InputDialect::Smt2.cli_status(SemanticExpectation::Unsafe),
        None
    );
    assert_eq!(
        InputDialect::HornQuery.cli_status(SemanticExpectation::Sat),
        None
    );
    assert_eq!(
        InputDialect::HornQuery.cli_status(SemanticExpectation::Unsat),
        None
    );
    assert_eq!(
        InputDialect::ChcComp.cli_status(SemanticExpectation::Sat),
        None
    );
    assert_eq!(
        InputDialect::ChcComp.cli_status(SemanticExpectation::Unsat),
        None
    );
    assert_eq!(
        SemanticExpectation::from_inventory("oracle-bound-at-consumer"),
        None
    );
}

#[test]
fn selected_horn_contract_keeps_identity_policy_and_original_deadline() {
    let mut value = document();
    let input = value["stored_inputs"]
        .as_array_mut()
        .expect("stored inputs")
        .iter_mut()
        .find(|input| input["id"] == "input:budget-bitreverse")
        .expect("stored bitreverse");
    input["path"] = Value::String("case.smt2".to_owned());
    input["size_bytes"] = Value::from(4);
    let inventory = inventory(&value);
    let directory = tempfile::tempdir().expect("fixture directory");
    fs::write(directory.path().join("case.smt2"), b"case").expect("fixture bytes");
    let roots = BTreeMap::from([(
        "model-checker-consumer".to_owned(),
        directory.path().to_owned(),
    )]);
    let selected = vec!["input:budget-bitreverse".to_owned()];
    let cases = inventory
        .chc_diagnostic_cases(&roots, &selected)
        .expect("selected diagnostic");
    assert_eq!(cases.len(), 1);
    assert_eq!(cases[0].timeout_ms, 15000);
    assert_eq!(cases[0].solver_memory_mib, 4096);
    assert_eq!(cases[0].tree_memory_mib, 4096);
    assert_eq!(cases[0].expected_cli_status, CliStatus::Unsat);
    assert_eq!(
        cases[0].original_revision,
        inventory
            .document
            .case_defaults
            .stored_model_checker_consumer_input_revision
    );
    assert!(!cases[0].promotable_for_ask_closure);
    // The authoritative gate snapshot must still reject these deliberately
    // different bytes: selector admission is not content authentication.
    assert_ne!(
        cases[0].expected_sha256,
        format!("sha256:{:x}", Sha256::digest(b"case"))
    );
    assert!(inventory.chc_diagnostic_cases(&roots, &[]).is_err());
    assert!(inventory
        .chc_diagnostic_cases(&roots, &[selected[0].clone(), selected[0].clone()])
        .is_err());
}

#[test]
fn source_smt_missing_and_unbound_oracle_do_not_become_chc_cases() {
    let inventory = inventory(&document());
    for id in [
        "input:store-source",
        "input:range-len",
        "input:store-full-historical",
        "input:budget-test3",
        "unknown",
    ] {
        assert!(
            inventory
                .chc_diagnostic_cases(&BTreeMap::new(), &[id.to_owned()])
                .is_err(),
            "{id}"
        );
    }
}

#[test]
fn selected_diagnostic_refuses_contradictory_or_undeclared_envelope() {
    let mut value = document();
    value["resource_policies"][0]["jobs"] = json!(2);
    let error = inventory(&value)
        .chc_diagnostic_cases(&BTreeMap::new(), &["input:budget-bitreverse".to_owned()])
        .expect_err("parallel policy cannot silently become serial");
    assert!(error
        .to_string()
        .contains("contradictory or missing envelope"));
    value["resource_policies"][0]["jobs"] = json!(1);
    value["resource_policies"][0]["child_tree_peak_bytes_max"] = json!(2147483648_u64);
    assert!(inventory(&value)
        .chc_diagnostic_cases(&BTreeMap::new(), &["input:budget-bitreverse".to_owned()])
        .expect_err("2 GiB policy cannot silently become 4 GiB")
        .to_string()
        .contains("envelope"));
    let mut value = document();
    value["request_inventory"][2]["resource_policy"] = json!("store-historical-2g");
    assert!(inventory(&value)
        .chc_diagnostic_cases(&BTreeMap::new(), &["input:budget-bitreverse".to_owned()])
        .expect_err("request must declare selected diagnostic profile")
        .to_string()
        .contains("does not declare"));
}

#[test]
fn selection_rejects_path_escape_and_missing_bytes() {
    let mut value = document();
    value["stored_inputs"][4]["path"] = Value::String("../outside.smt2".to_owned());
    assert!(Inventory::parse(&value.to_string()).is_err());
    let inventory = inventory(&document());
    let directory = tempfile::tempdir().expect("empty root");
    let roots = BTreeMap::from([(
        "model-checker-consumer".to_owned(),
        directory.path().to_owned(),
    )]);
    assert!(inventory
        .chc_diagnostic_cases(&roots, &["input:budget-bitreverse".to_owned()])
        .is_err());
}

#[cfg(unix)]
#[test]
fn loader_refuses_symlink_and_oversized_inventory() {
    let directory = tempfile::tempdir().expect("fixture directory");
    let target = directory.path().join("inventory.json");
    fs::write(&target, document().to_string()).expect("inventory fixture");
    let link = directory.path().join("link.json");
    std::os::unix::fs::symlink(&target, &link).expect("fixture symlink");
    assert!(Inventory::load(&link).is_err());
    let file = fs::File::create(&target).expect("oversized fixture");
    file.set_len(super::MAX_INVENTORY_BYTES + 1)
        .expect("fixture length");
    assert!(Inventory::load(&target).is_err());
}

mod schema_v2;

mod schema_v3;

mod current_schemas;

mod input_semantics;

mod dataset_sources;
