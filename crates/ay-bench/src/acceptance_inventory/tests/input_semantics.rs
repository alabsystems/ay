// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeMap;

use serde_json::{json, Value};

use super::super::{BlockerKind, Inventory, SemanticExpectation};

fn inventory() -> Inventory {
    Inventory::parse(&super::current_schemas::current().to_string()).expect("real v6")
}

#[test]
fn archive_typed_witness_and_no_solve_controls_remain_explicit_obligations() {
    let inventory = inventory();
    let plan = inventory.plan();
    let exports = plan
        .requests
        .iter()
        .find(|r| r.contract.id == "R34")
        .expect("export request");
    for (id, kind) in [
        (
            "input:export-test2-source",
            BlockerKind::ArchiveAdapterMissing,
        ),
        (
            "input:export-test2-error-p1",
            BlockerKind::TypedInputReconstructionMissing,
        ),
        (
            "input:export-static-constructor-witness",
            BlockerKind::TypedInputReconstructionMissing,
        ),
        (
            "input:export-static-constructor-witness",
            BlockerKind::OracleUnresolved,
        ),
        (
            "input:export-bitmask-witness-0026",
            BlockerKind::OracleUnresolved,
        ),
        (
            "input:export-alloc-to-slice-source",
            BlockerKind::OracleUnresolved,
        ),
        (
            "input:export-bitmask-u8-source",
            BlockerKind::SolverInvocationAbsent,
        ),
    ] {
        assert!(
            exports
                .blockers
                .iter()
                .any(|b| b.subject == id && b.kind == kind),
            "{id}: {kind:?}"
        );
    }
    assert!(
        !exports
            .blockers
            .iter()
            .any(|b| b.kind == BlockerKind::InputIdentityMissing),
        "known archive identities are not absent bytes; the missing adapter stays explicit"
    );
    let drain = plan
        .requests
        .iter()
        .find(|r| r.contract.id == "R33")
        .expect("drain request");
    assert!(drain
        .blockers
        .iter()
        .any(|b| b.kind == BlockerKind::ArchiveAdapterMissing));
    assert!(!plan.promotable_for_ask_closure);
}

#[test]
fn archived_or_typed_inputs_are_refused_before_resolving_any_root() {
    let inventory = inventory();
    for id in [
        "input:acyclic-drain-ref-index",
        "input:export-test2-source",
        "input:export-test2-error-p1",
        "input:export-static-constructor-witness",
        "input:export-bitmask-witness-0026",
        "input:export-bitmask-u8-source",
    ] {
        let error = inventory
            .chc_diagnostic_cases(&BTreeMap::new(), &[id.to_owned()])
            .expect_err("not a standalone original HORN file");
        assert!(error
            .to_string()
            .contains("not an available stored whole-HORN diagnostic"));
        let input = inventory
            .document
            .stored_inputs
            .iter()
            .find(|input| input.id == id)
            .expect("input");
        assert!(!super::super::input::direct_solver_file(input));
    }
}

#[test]
fn source_sat_spelling_is_exact_and_unknown_is_never_a_semantic_oracle() {
    for spelling in ["unsat", "Unsat"] {
        assert_eq!(
            SemanticExpectation::from_inventory(spelling),
            Some(SemanticExpectation::Unsat)
        );
    }
    for spelling in ["sat", "Sat"] {
        assert_eq!(
            SemanticExpectation::from_inventory(spelling),
            Some(SemanticExpectation::Sat)
        );
    }
    for spelling in [
        "Unknown",
        "unknown",
        "NotEstablished",
        "SUCCESSFUL",
        "UNSAT",
        "unsat ",
    ] {
        assert_eq!(SemanticExpectation::from_inventory(spelling), None);
    }
    let plan = inventory().plan();
    let replay = plan
        .requests
        .iter()
        .find(|r| r.contract.id == "R31")
        .expect("strict replay");
    assert!(!replay
        .blockers
        .iter()
        .any(|b| b.kind == BlockerKind::OracleUnresolved));
    assert!(replay
        .blockers
        .iter()
        .any(|b| b.kind == BlockerKind::RouteEvidenceMissing));
}

#[test]
fn empty_effort_fixture_list_preserves_generator_and_both_source_oracles() {
    let plan = inventory().plan();
    let effort = plan
        .requests
        .iter()
        .find(|r| r.contract.id == "R25")
        .expect("effort ask");
    assert_eq!(
        effort.contract.stored_input_ids.as_slice(),
        &[] as &[String]
    );
    assert!(effort
        .blockers
        .iter()
        .any(|b| b.kind == BlockerKind::BudgetBindingMissing));
    assert!(effort
        .blockers
        .iter()
        .any(|b| b.kind == BlockerKind::RouteEvidenceMissing));
    let matrix = &effort.contract.metadata["acceptance_matrix"];
    assert_eq!(matrix["k"], json!([1024, 2048, 4096, 8192]));
    assert_eq!(matrix["variants"][0]["expected_consumer_verdict"], "Proved");
    assert_eq!(
        matrix["variants"][1]["expected_consumer_verdict"],
        "Refuted"
    );
    assert_eq!(
        matrix["variants"][1]["independent_original_source_replay_required"],
        true
    );
}

fn archived_legacy_fixture() -> Value {
    let mut value = super::document();
    let row = &mut value["stored_inputs"][4];
    row["availability"] = json!("tracked-archive-member");
    row["archive_member"] = json!("capture/source.smt2");
    row["archive_sha256"] = json!("1".repeat(64));
    row["archive_size_bytes"] = json!(100);
    value
}

#[test]
fn archival_identity_validation_checks_container_member_and_traversal() {
    let value = archived_legacy_fixture();
    Inventory::parse(&value.to_string()).expect("complete archive identity is plannable");
    for (key, invalid) in [
        ("availability", json!("tracked")),
        ("archive_member", json!("../source.smt2")),
        ("archive_member", json!("/source.smt2")),
        ("archive_sha256", json!("short")),
        ("archive_size_bytes", json!(0)),
        ("sha256", Value::Null),
        ("size_bytes", Value::Null),
        ("not_smtlib_parser_input", json!("true")),
    ] {
        let mut changed = value.clone();
        changed["stored_inputs"][4][key] = invalid;
        assert!(Inventory::parse(&changed.to_string()).is_err(), "{key}");
    }
    for key in ["archive_member", "archive_sha256", "archive_size_bytes"] {
        let mut changed = value.clone();
        changed["stored_inputs"][4]
            .as_object_mut()
            .expect("row")
            .remove(key);
        assert!(
            Inventory::parse(&changed.to_string()).is_err(),
            "absent {key}"
        );
    }
}

#[test]
fn normalized_input_exclusion_cannot_be_overridden_by_direct_horn_label() {
    let mut value = super::document();
    value["stored_inputs"][4]["not_smtlib_parser_input"] = json!(true);
    let inventory = Inventory::parse(&value.to_string()).expect("typed exclusion retained");
    assert!(inventory
        .chc_diagnostic_cases(&BTreeMap::new(), &["input:budget-bitreverse".to_owned()])
        .expect_err("typed normalized text is not HORN")
        .to_string()
        .contains("not an available stored whole-HORN diagnostic"));
}

#[test]
fn input_backreferences_cannot_create_an_unlisted_execution_obligation() {
    let mut value = super::document();
    value["stored_inputs"][4]["request_ids"]
        .as_array_mut()
        .expect("IDs")
        .push(json!("R01"));
    assert!(Inventory::parse(&value.to_string())
        .expect_err("one-sided reference")
        .to_string()
        .contains("no reverse binding"));
}

#[test]
fn json_admission_remains_bounded_and_rejects_duplicate_flattened_fields() {
    assert!(
        super::super::json::read(&" ".repeat(super::super::MAX_INVENTORY_BYTES as usize + 1))
            .is_err()
    );
    let nested = format!("{}0{}", "[".repeat(150), "]".repeat(150));
    assert!(super::super::json::read(&nested).is_err());
    let text = super::document().to_string();
    let duplicated = format!("{{\"metadata\":1,\"metadata\":2,{}", &text[1..]);
    assert!(Inventory::parse(&duplicated)
        .expect_err("duplicate unknown metadata")
        .to_string()
        .contains("duplicate inventory JSON key"));
}
