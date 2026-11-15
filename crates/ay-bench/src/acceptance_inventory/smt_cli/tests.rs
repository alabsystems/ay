// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Synthetic contract/identity controls; these do not prove a solver theorem.
use super::super::{CliStatus, Inventory};
use super::*;
use crate::environment::SolverProvenance;
use serde_json::json;
use std::collections::BTreeMap;
use std::time::{Duration, Instant};

fn case(variant: SmtMemoryVariant) -> SmtCliCase {
    SmtCliCase {
        input_id: "input:x".into(),
        request_ids: vec!["R01".into()],
        repository: "model-checker-consumer".into(),
        revision: "a".repeat(40),
        original_path: "x.smt2".into(),
        path: "/x.smt2".into(),
        sha256: format!("sha256:{}", "b".repeat(64)),
        size_bytes: 4,
        expected: CliStatus::Sat,
        timeout_ms: 1000,
        variant,
    }
}
fn binary() -> SolverProvenance {
    SolverProvenance {
        path: "/ay".into(),
        sha256: format!("sha256:{}", "c".repeat(64)),
        size_bytes: 100,
        version_output: "test-only".into(),
        build_version: "0.1.0".into(),
        build_commit: "a".repeat(40),
        build_datetime_utc: "2026-09-29T00:00:00Z".into(),
        build_stamp: "test-stamp".into(),
    }
}
fn stats(status: &str, memory: u64) -> String {
    json!({"mode":"smt", "result":status,
    "resource.memory_limit_bytes":memory,"ay_build":{"commit":"a".repeat(40),"stamp":"test-stamp",
        "version":"0.1.0","datetime_utc":"2026-09-29T00:00:00Z"}})
    .to_string()
}
fn checked(stdout: &str, stderr: &str, exit: Option<i32>) -> super::assess::Assessment {
    super::assess::assess(
        &case(SmtMemoryVariant::Serial4GiB),
        &binary(),
        stdout,
        stderr,
        exit,
        false,
        false,
        None,
    )
}

#[test]
fn profiles_preserve_no_flag_default_and_explicit_limits() {
    for (variant, expected) in [
        (SmtMemoryVariant::Serial4GiB, Some("4096")),
        (SmtMemoryVariant::Historical2GiB, Some("2048")),
        (SmtMemoryVariant::MachineDefault, None),
    ] {
        let args = super::execution::argv(
            &case(variant),
            std::path::Path::new("/private.smt2"),
            Duration::from_millis(9),
        );
        let memory = args
            .iter()
            .position(|arg| arg == "--memory")
            .map(|index| args[index + 1].as_str());
        assert_eq!(memory, expected);
        assert!(args.iter().any(|arg| arg == "--self-check"));
        assert!(!args
            .iter()
            .any(|arg| arg == "--chc" || arg == "--no-proof" || arg == "--verify-proof"));
        assert!(args.iter().any(|arg| arg == "-t:9"));
    }
}
#[test]
fn exactly_bound_self_check_is_narrow_in_tree_evidence() {
    let result = checked("sat\n", &stats("sat", 4 * 1024 * 1024 * 1024), Some(0));
    assert!(result.checked);
    assert!(result.blockers.is_empty());
}
#[test]
fn contradictory_duplicate_or_absent_verdicts_refuse() {
    for out in ["sat\nunsat\n", "sat\nsat\n", "", "satisfiable\n"] {
        assert!(!checked(out, &stats("sat", 4 * 1024 * 1024 * 1024), Some(0)).checked);
    }
}
#[test]
fn stderr_duplicate_opposite_and_stderr_only_verdicts_refuse() {
    let stamp = stats("sat", 4 * 1024 * 1024 * 1024);
    for verdict in [
        "sat",
        "unsat",
        "unknown",
        "SAT",
        "s satisfiable",
        "satisfiable",
        "s unsatisfiable",
        "UNSATISFIABLE",
        "s unknown",
        "timeout",
    ] {
        let stderr = format!("{stamp}\n{verdict}\n");
        assert!(!checked("sat\n", &stderr, Some(0)).checked);
        assert!(!checked("", &stderr, Some(0)).checked);
    }
}
#[test]
fn crash_or_fatal_diagnostic_cannot_keep_earlier_sat() {
    for exit in [None, Some(1), Some(10)] {
        assert!(!checked("sat\n", &stats("sat", 4 * 1024 * 1024 * 1024), exit).checked);
    }
    assert!(
        !checked(
            "sat\n",
            &(stats("sat", 4 * 1024 * 1024 * 1024) + "\nfatal: stopped"),
            Some(0)
        )
        .checked
    );
}
#[test]
fn unknown_and_wrong_answer_are_typed_failures() {
    let unknown = checked(
        "unknown\n",
        &stats("unknown", 4 * 1024 * 1024 * 1024),
        Some(0),
    );
    assert!(unknown.blockers.contains(&SmtCliBlocker::Unknown));
    assert!(!unknown.checked);
    let wrong = checked("unsat\n", &stats("unsat", 4 * 1024 * 1024 * 1024), Some(0));
    assert!(wrong.blockers.contains(&SmtCliBlocker::WrongAnswer));
    assert!(!wrong.checked);
}
#[test]
fn stamp_dialect_result_and_memory_mutations_refuse() {
    let original: serde_json::Value =
        serde_json::from_str(&stats("sat", 4 * 1024 * 1024 * 1024)).unwrap();
    for pointer in [
        "/mode",
        "/result",
        "/ay_build/commit",
        "/ay_build/stamp",
        "/ay_build/version",
        "/ay_build/datetime_utc",
        "/resource.memory_limit_bytes",
    ] {
        let mut altered = original.clone();
        *altered.pointer_mut(pointer).unwrap() = json!("other");
        assert!(
            !checked("sat\n", &altered.to_string(), Some(0)).checked,
            "{pointer}"
        );
    }
}
#[test]
fn missing_duplicate_malformed_stats_refuse() {
    let valid = stats("sat", 4 * 1024 * 1024 * 1024);
    for s in [String::new(), format!("{valid}\n{valid}"), "{bad".into()] {
        assert!(!checked("sat\n", &s, Some(0)).checked);
    }
}
#[test]
fn default_observation_must_exist_and_match_actual_case() {
    for expected in [None, Some(1)] {
        let result = super::assess::assess(
            &case(SmtMemoryVariant::MachineDefault),
            &binary(),
            "sat\n",
            &stats("sat", 1024),
            Some(0),
            false,
            false,
            expected,
        );
        assert!(!result.checked);
        assert!(result.blockers.iter().any(|b| matches!(
            b,
            SmtCliBlocker::DefaultMemoryUnavailable | SmtCliBlocker::DefaultMemoryChanged
        )));
    }
    assert!(
        super::assess::assess(
            &case(SmtMemoryVariant::MachineDefault),
            &binary(),
            "sat\n",
            &stats("sat", 1024),
            Some(0),
            false,
            false,
            Some(1024)
        )
        .checked
    );
}
#[test]
fn stop_flags_dominate_matching_status() {
    for (timeout, memout, expected) in [
        (true, false, SmtCliBlocker::Deadline),
        (false, true, SmtCliBlocker::MemoryLimit),
    ] {
        let result = super::assess::assess(
            &case(SmtMemoryVariant::Serial4GiB),
            &binary(),
            "sat\n",
            &stats("sat", 4 * 1024 * 1024 * 1024),
            Some(0),
            timeout,
            memout,
            None,
        );
        assert!(!result.checked);
        assert!(result.blockers.contains(&expected));
    }
}
#[test]
fn unknown_binary_commit_is_not_qualified() {
    let mut b = binary();
    b.build_commit = "unknown".into();
    let result = super::assess::assess(
        &case(SmtMemoryVariant::Serial4GiB),
        &b,
        "sat\n",
        &stats("sat", 4 * 1024 * 1024 * 1024),
        Some(0),
        false,
        false,
        None,
    );
    assert!(result
        .blockers
        .contains(&SmtCliBlocker::BinaryStampUnqualified));
    assert!(!result.checked);
}
fn inventory(root: &std::path::Path) -> Inventory {
    let mut doc = super::super::test_document();
    let bytes = b"sat\n";
    std::fs::write(root.join("case.smt2"), bytes).unwrap();
    for input in doc["stored_inputs"].as_array_mut().unwrap() {
        if input["id"] == "input:range-len" {
            input["sha256"] = json!(super::snapshot::hash(bytes).trim_start_matches("sha256:"));
        }
    }
    for request in doc["request_inventory"].as_array_mut().unwrap() {
        if matches!(request["id"].as_str(), Some("R13" | "R14")) {
            request["required_routes"] = json!(["smt-cli", "smt-api"]);
        }
    }
    Inventory::parse(&doc.to_string()).unwrap()
}
#[test]
fn select_original_smt_preserves_all_other_routes_and_performance() {
    let temp = tempfile::tempdir().unwrap();
    let inventory = inventory(temp.path());
    let roots = BTreeMap::from([("model-checker-consumer".into(), temp.path().to_path_buf())]);
    let cases = super::selection::select(
        &inventory,
        &roots,
        &["input:range-len".into()],
        &[SmtMemoryVariant::Serial4GiB],
    )
    .unwrap();
    assert_eq!(cases.len(), 1);
    assert_eq!(cases[0].expected, CliStatus::Unsat);
    let plan = inventory.plan();
    assert_eq!(plan.requests.len(), 28);
    assert!(!plan.promotable_for_ask_closure);
    let request = plan
        .requests
        .iter()
        .find(|r| r.contract.id == "R13")
        .unwrap();
    assert_eq!(request.routes.len(), 2);
    assert!(request.routes.iter().all(|r| !r.evidence_qualified));
    assert!(!request.performance_contract_ids.is_empty());
}
#[test]
fn missing_historical_bytes_horn_and_duplicate_selection_refuse() {
    let temp = tempfile::tempdir().unwrap();
    let inventory = inventory(temp.path());
    let roots = BTreeMap::from([("model-checker-consumer".into(), temp.path().to_path_buf())]);
    for ids in [
        vec!["input:store-full-historical".into()],
        vec!["input:budget-bitreverse".into()],
        vec!["input:range-len".into(), "input:range-len".into()],
    ] {
        assert!(super::selection::select(
            &inventory,
            &roots,
            &ids,
            &[SmtMemoryVariant::Serial4GiB]
        )
        .is_err());
    }
}
#[test]
fn undeclared_or_duplicate_profiles_refuse() {
    let temp = tempfile::tempdir().unwrap();
    let inventory = inventory(temp.path());
    let roots = BTreeMap::from([("model-checker-consumer".into(), temp.path().to_path_buf())]);
    for variants in [
        vec![SmtMemoryVariant::Historical2GiB],
        vec![SmtMemoryVariant::MachineDefault],
        vec![SmtMemoryVariant::Serial4GiB, SmtMemoryVariant::Serial4GiB],
    ] {
        assert!(super::selection::select(
            &inventory,
            &roots,
            &["input:range-len".into()],
            &variants
        )
        .is_err());
    }
}
#[test]
fn exact_snapshot_and_expired_original_owner_are_checked() {
    let temp = tempfile::tempdir().unwrap();
    let src = temp.path().join("in");
    std::fs::write(&src, b"sat\n").unwrap();
    let deadline = Instant::now() + Duration::from_secs(5);
    super::snapshot::copy(
        &src,
        &temp.path().join("ok"),
        &super::snapshot::hash(b"sat\n"),
        4,
        deadline,
    )
    .unwrap();
    assert!(super::snapshot::copy(
        &src,
        &temp.path().join("bad"),
        &super::snapshot::hash(b"bad\n"),
        4,
        deadline
    )
    .is_err());
    assert!(super::snapshot::copy(
        &src,
        &temp.path().join("late"),
        &super::snapshot::hash(b"sat\n"),
        4,
        Instant::now()
    )
    .is_err());
    assert!(!temp.path().join("late").exists());
}
#[cfg(unix)]
#[test]
fn symlink_snapshot_cannot_supply_original_bytes() {
    let temp = tempfile::tempdir().unwrap();
    let src = temp.path().join("in");
    std::fs::write(&src, b"sat\n").unwrap();
    let link = temp.path().join("link");
    std::os::unix::fs::symlink(&src, &link).unwrap();
    assert!(super::snapshot::copy(
        &link,
        &temp.path().join("out"),
        &super::snapshot::hash(b"sat\n"),
        4,
        Instant::now() + Duration::from_secs(5)
    )
    .is_err());
}

#[test]
fn original_smt_unsat_polarity_is_not_the_horn_query_mapping() {
    let mut input = case(SmtMemoryVariant::Historical2GiB);
    input.expected = CliStatus::Unsat;
    let result = super::assess::assess(
        &input,
        &binary(),
        "unsat\n",
        &stats("unsat", 2 * 1024 * 1024 * 1024),
        Some(0),
        false,
        false,
        None,
    );
    assert!(result.checked);
    let wrong = super::assess::assess(
        &input,
        &binary(),
        "sat\n",
        &stats("sat", 2 * 1024 * 1024 * 1024),
        Some(0),
        false,
        false,
        None,
    );
    assert!(!wrong.checked);
    assert!(wrong.blockers.contains(&SmtCliBlocker::WrongAnswer));
}

#[cfg(unix)]
#[test]
fn guarded_synthetic_cli_binds_artifacts_without_qualifying_requests() {
    use std::os::unix::fs::PermissionsExt;
    let temp = tempfile::tempdir().unwrap();
    let inventory = inventory(temp.path());
    let inventory_bytes = serde_json::to_vec(&inventory.document).unwrap();
    let inventory_path = temp.path().join("inventory.json");
    std::fs::write(&inventory_path, &inventory_bytes).unwrap();
    let selection = temp.path().join("selection.json");
    std::fs::write(
        &selection,
        json!({
            "schema":"ay.model-checker-consumer-smt-cli-selection/v1", "inventory":"inventory.json",
            "inventory_sha256":super::snapshot::hash(&inventory_bytes),
            "repository_roots":{"model-checker-consumer":temp.path()},"stored_input_ids":["input:range-len"],
            "memory_variants":["serial-enforced-tree-4g"]
        })
        .to_string(),
    )
    .unwrap();
    // Protocol fixture only. This script is deliberately not a real solver or
    // proof checker; the assertions below concern harness identity and scope.
    let binary_path = temp.path().join("fake-ay");
    let telemetry = stats("unsat", 4 * 1024 * 1024 * 1024);
    let script = format!("#!/bin/sh\nif [ \"$1\" = --version ]; then\nprintf '%s\\n' 'ay fixture' 'build.version=0.1.0' 'build.commit={}' 'build.datetime_utc=2026-09-29T00:00:00Z' 'build.stamp=test-stamp'\nexit 0\nfi\n[ \"$1\" = --self-check ] || exit 9\nprintf '%s\\n' unsat\nprintf '%s\\n' '{}' >&2\n", "a".repeat(40), telemetry);
    std::fs::write(&binary_path, script).unwrap();
    std::fs::set_permissions(&binary_path, std::fs::Permissions::from_mode(0o700)).unwrap();
    let output = temp.path().join("run");
    let report = run_smt_cli(SmtCliArgs {
        selection,
        ay: binary_path,
        out_dir: output.clone(),
        timeout_sec: 30.0,
    })
    .unwrap();
    assert_eq!(report.records.len(), 1);
    assert!(report.records[0].in_tree_self_check_passed);
    assert!(!report.records[0].independent_replay_passed);
    assert!(!report.promotable_for_ask_closure);
    assert_eq!(report.plan.requests.len(), 28);
    assert!(report
        .plan
        .requests
        .iter()
        .all(|request| request.routes.iter().all(|route| !route.evidence_qualified)));
    assert_eq!(
        std::fs::read(output.join("case-0/input.smt2")).unwrap(),
        b"sat\n"
    );
    assert!(output.join("case-0/record.json").is_file());
    assert!(output.join("report.json").is_file());
}

#[test]
fn known_default_above_tree_cap_is_preserved_and_distinguished() {
    let observed = Some(32 * 1024 * 1024 * 1024_u64);
    let mut blockers = Vec::new();
    super::execution::default_envelope(observed, &mut blockers);
    assert_eq!(observed, Some(34_359_738_368));
    assert_eq!(blockers, [SmtCliBlocker::DefaultMemoryExceedsTreeEnvelope]);
    blockers.clear();
    super::execution::default_envelope(None, &mut blockers);
    assert_eq!(blockers, [SmtCliBlocker::DefaultMemoryUnavailable]);
}

mod capture;

mod current_inventory;
