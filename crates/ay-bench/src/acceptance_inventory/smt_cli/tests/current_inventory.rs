// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeMap;
use std::fs;

use super::super::super::{CliStatus, InputDialect, Inventory, PlanBlocker};
use super::super::{selection, SmtMemoryVariant};

fn inventory() -> Inventory {
    Inventory::parse(include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../docs/integrations/model_checker_consumer_acceptance_manifest.json"
    )))
    .expect("real current inventory")
}

#[test]
fn current_strict_controls_bind_unsat_and_the_separate_smt_budget() {
    let inventory = inventory();
    let root = tempfile::tempdir().expect("private root");
    let roots = BTreeMap::from([("model-checker-consumer".to_owned(), root.path().to_owned())]);
    let ids = [
        "input:strict-ring",
        "input:strict-nia-consecution",
        "input:strict-clause47-replay",
    ]
    .map(str::to_owned);
    for id in &ids {
        let input = inventory
            .document
            .stored_inputs
            .iter()
            .find(|r| r.id == *id)
            .expect("control");
        let path = root.path().join(&input.path);
        fs::create_dir_all(path.parent().expect("parent")).expect("directories");
        // These placeholders test selection only, not private snapshot digest
        // admission, solver execution or independent strict proof replay.
        fs::File::create(path)
            .expect("placeholder")
            .set_len(input.size_bytes.expect("size"))
            .expect("length");
        assert_eq!(
            super::super::super::diagnostic::input_timeout(
                &inventory,
                input,
                InputDialect::HornQuery
            )
            .expect("consumer/cohort budget"),
            15_000
        );
    }
    let cases = selection::select(&inventory, &roots, &ids, &[SmtMemoryVariant::Serial4GiB])
        .expect("current strict SMT controls");
    assert_eq!(cases.len(), 3);
    for case in cases {
        assert_eq!(case.expected, CliStatus::Unsat);
        assert_eq!(case.timeout_ms, 30_000);
        assert_eq!(case.request_ids, ["R31"]);
    }
    assert!(!inventory.plan().promotable_for_ask_closure);
}

#[test]
fn original_smt_selector_refuses_archives_normalized_witnesses_and_no_solve_controls() {
    let inventory = inventory();
    for id in [
        "input:export-bitmask-witness-0026",
        "input:export-static-constructor-witness",
        "input:export-test2-error-p1",
        "input:export-bitmask-u8-source",
        "input:proof-runaway-dividers-source",
        "input:fp-logic-test6-source",
    ] {
        let error = selection::select(
            &inventory,
            &BTreeMap::new(),
            &[id.to_owned()],
            &[SmtMemoryVariant::Serial4GiB],
        )
        .expect_err("no runnable direct SMT input");
        assert!(error
            .to_string()
            .contains("SMT route requires available original SMT bytes"));
    }
}

#[test]
fn proof_runaway_smt_rows_cannot_borrow_consumer_grant_or_lose_strict_controls() {
    let inventory = inventory();
    let mut ids = Vec::new();
    for input in &inventory.document.stored_inputs {
        if input.request_ids != ["R35"] || input.kind.as_deref() != Some("smt2") {
            continue;
        }
        assert_eq!(input.expected_semantic_result, "Unsat");
        assert_eq!(
            input.revision.as_deref(),
            Some("ec3d1794fb2422890a76d38705b3c03dc4a14e70")
        );
        ids.push(input.id.clone());
    }
    assert_eq!(ids.len(), 6);
    for id in ids {
        let error = selection::select(
            &inventory,
            &BTreeMap::new(),
            &[id],
            &[SmtMemoryVariant::Serial4GiB],
        )
        .expect_err("the source supplies no standalone CLI acceptance grant");
        assert!(error.to_string().contains("route-specific timeout binding"));
    }
    let control = inventory
        .document
        .stored_inputs
        .iter()
        .find(|row| row.id == "input:proof-runaway-rem-u32-digits")
        .expect("cheap strict control");
    assert_eq!(control.metadata["required_admission"], "strict-proof");
    let plan = inventory.plan();
    let request = plan
        .requests
        .iter()
        .find(|row| row.contract.id == "R35")
        .expect("R35");
    assert_eq!(request.consumer_unit_ids.len(), 8);
    assert_eq!(
        request.contract.metadata["cohorts"]["consumer_runaway_count"],
        7
    );
    assert_eq!(
        request.contract.metadata["consumer_harness_budget_ms"],
        30_000
    );
    assert!(request.contract.harness_or_solve_budget_ms.is_none());
    assert!(
        !request.blockers.iter().any(|blocker| {
            blocker.subject == "input:proof-runaway-dividers-source"
                && blocker.kind == super::super::super::BlockerKind::OracleUnresolved
        }),
        "Rust source must not require an invented SMT oracle"
    );
    assert_ne!(request.blockers.as_slice(), &[] as &[PlanBlocker]);
    assert!(request.routes.iter().all(|route| !route.evidence_qualified));
    assert!(!plan.promotable_for_ask_closure);
}

#[test]
fn fp_original_and_old_logic_control_keep_separate_bytes_and_no_borrowed_cli_grant() {
    let inventory = inventory();
    for (id, logic, bytes, digest) in [
        (
            "input:fp-logic-test6-all",
            "ALL",
            27_012,
            "1bb78d1891042eaaf6beae33ef9d7b4f7cf18680667fc81bbc3475d0d5abe68e",
        ),
        (
            "input:fp-logic-test6-qf-aufbv",
            "QF_AUFBV",
            27_017,
            "bf10e081313e27b718cc0884792a89c3b582282959445d61b3c1d1d5ec1fa32b",
        ),
    ] {
        let input = inventory
            .document
            .stored_inputs
            .iter()
            .find(|input| input.id == id)
            .expect("original FP query");
        assert_eq!(input.smt_logic.as_deref(), Some(logic));
        assert_eq!(input.size_bytes, Some(bytes));
        assert_eq!(input.sha256.as_deref(), Some(digest));
        assert_eq!(input.expected_semantic_result, "Sat");
        assert_eq!(
            input.metadata["required_admission"],
            "validated-original-model"
        );
        let error = selection::select(
            &inventory,
            &BTreeMap::new(),
            &[id.to_owned()],
            &[SmtMemoryVariant::Serial4GiB],
        )
        .expect_err("consumer harness grant is not a standalone CLI grant");
        assert!(error.to_string().contains("route-specific timeout binding"));
    }
}

#[test]
fn fp_consumer_requires_failed_counterexample_inside_original_fifteen_second_owner() {
    let inventory = inventory();
    let plan = inventory.plan();
    let request = plan
        .requests
        .iter()
        .find(|row| row.contract.id == "R36")
        .expect("R36");
    assert_eq!(request.consumer_unit_ids, ["r36-fp-test6:main"]);
    assert_eq!(
        request.contract.metadata["consumer_harness_budget_ms"],
        15_000
    );
    assert!(request.contract.harness_or_solve_budget_ms.is_none());
    assert!(request.contract.metadata["standalone_cli_budget_ms"].is_null());
    let oracle = &request.contract.metadata["consumer_oracle"];
    assert_eq!(oracle["expected_run_verdict"], "FAILED");
    assert_eq!(oracle["expected_kani_verdict"], "FAIL");
    assert_eq!(oracle["expected_solver_result"], "Sat");
    assert_eq!(oracle["validated_original_counterexample_required"], true);
    assert_eq!(oracle["independent_source_replay_required"], true);
    assert_ne!(request.blockers.as_slice(), &[] as &[PlanBlocker]);
    assert!(request.routes.iter().all(|route| !route.evidence_qualified));
    assert!(!plan.promotable_for_ask_closure);
}

#[test]
fn strict_route_budget_rejects_invalid_and_zero_durations_without_guessing() {
    for bound in [
        serde_json::json!("30000"),
        serde_json::json!(0),
        serde_json::json!(u64::MAX),
    ] {
        let mut value = crate::acceptance_inventory::test_document();
        value["request_inventory"][12]["strict_smt_control_budget_ms"] = bound;
        let inventory = Inventory::parse(&value.to_string()).expect("legacy structural fixture");
        let input = inventory
            .document
            .stored_inputs
            .iter()
            .find(|r| r.id == "input:range-len")
            .expect("SMT input");
        assert!(super::super::super::diagnostic::input_timeout(
            &inventory,
            input,
            InputDialect::Smt2
        )
        .is_err());
    }
}
